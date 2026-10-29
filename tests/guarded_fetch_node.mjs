// The Node side of tests/test_guarded_fetch_node.py: runs examples/guarded_fetch.mjs with nothing
// leaving the machine.
//
// Reads one JSON job on stdin, {"items": [...]}, runs the items one after another and prints one
// JSON line: {"node": version, "results": [...], "strays": [...]}, one result per item, each with
// what happened on the way: "connects" (the host and port of every net.Socket connect call, as the
// example made it), "lookups" (every call of dns.lookup or dns.promises.lookup, which are refused),
// "resolves" (every call of the resolver given to guardedFetch) and "violations". "strays" lists
// any of these that came between items.
//
// * While a "fetch" item with an "origin" port (a fixture of the Python test) runs, every connect
//   call is sent to 127.0.0.1 on that port instead. In an "openSocket" item, the only connection
//   allowed is one to the driver's own listener on 127.0.0.1. Any other connection is refused and
//   reported before net connects anywhere: every one in a fetch with no "origin", one to a local
//   socket path, and one outside an item. tls.connect connects through
//   net.Socket.prototype.connect, so TLS is covered too.
// * The resolver answers from the item's "answers": host -> list of answers, one per lookup (the
//   last one repeats), each a list of addresses, {"after": ms, "addrs": [...]} (those addresses, ms
//   later), or "throw".
//
// Items: {"op": "fetch", "url", "options", "answers", "origin", "ca", "agent", "env"},
// {"op": "check", "url", "options", "abort"} ("abort": {"after": ms, "reason"}, a signal for check
// that aborts that long into the item, at once for 0), {"op": "checkAddrs", "addrs", "options"},
// {"op": "openSocket", "addr", "autoSelectFamily", "port" (the listener's if absent), "tls" (a host
// name: over TLS)}, {"op": "wait", "ms"} (nothing may connect meanwhile, so what an earlier item
// left running would be reported). "env" sets (a string) or unsets (null) environment variables
// while the item runs.
import dns from "node:dns";
import fs from "node:fs";
import http from "node:http";
import https from "node:https";
import net from "node:net";
import * as gf from "../examples/guarded_fetch.mjs";

let rec = null;
let target = null; // {redirect: port} or {only: port}
const strays = []; // what came between items, when `rec` is null

// Records `value` in the item's `field`, or `what` in `strays` between items.
function note(field, value, what) {
  if (rec) rec[field].push(value);
  else strays.push(what);
}

// A listener for "openSocket", set up before the guard (listening looks up its own address).
const accepted = [];
const listener = net.createServer((c) => {
  accepted.push(c.remoteAddress);
  c.destroy();
});
await new Promise((ok) => listener.listen(0, "127.0.0.1", ok));
const listenerPort = listener.address().port;

// ---- the guard ---------------------------------------------------------------------------------

dns.lookup = function lookup(host, ...rest) {
  note("lookups", String(host), `lookup ${host}`);
  const callback = rest[rest.length - 1];
  process.nextTick(callback, Object.assign(new Error(`guarded_fetch_node.mjs: refusing to resolve ${host}`),
    { code: "ENOTFOUND" }));
};
dns.promises.lookup = async function lookup(host) {
  note("lookups", String(host), `lookup ${host}`);
  throw new Error(`guarded_fetch_node.mjs: refusing to resolve ${host}`);
};
const realConnect = net.Socket.prototype.connect;
net.Socket.prototype.connect = function connect(...args) {
  let [o, callback] = args;
  if (Array.isArray(o)) [o, callback] = o;
  if (o === null || typeof o !== "object" || o.path || rec === null || target === null) {
    const what = o?.path ?? (typeof o === "object" ? `${o?.host}:${o?.port}` : String(o));
    note("violations", `connect ${what}`, `connect ${what}`);
    throw new Error("guarded_fetch_node.mjs: refusing a connection outside an item, or to a local socket");
  }
  rec.connects.push([o.host, o.port]);
  if (Number.isInteger(target.redirect)) {
    return realConnect.call(this, { ...o, host: "127.0.0.1", port: target.redirect }, callback);
  }
  if (o.host !== "127.0.0.1" || o.port !== target.only) {
    rec.violations.push(`connect ${o.host}:${o.port}`);
    throw new Error("guarded_fetch_node.mjs: refusing to connect anywhere but the listener or a fixture");
  }
  return realConnect.call(this, o, callback);
};

// ---- the items ---------------------------------------------------------------------------------

function resolver(answers) {
  return async (host, options) => {
    note("resolves", [host, options], `resolve ${host}`);
    const seq = answers[host];
    if (!seq || seq.length === 0) throw Object.assign(new Error("no such name here"), { code: "ENOTFOUND" });
    const a = seq.length > 1 ? seq.shift() : seq[0];
    if (a === "throw") throw new Error("this resolver answers only so often");
    if (!Array.isArray(a)) await new Promise((ok) => setTimeout(ok, a.after));
    return (Array.isArray(a) ? a : a.addrs).map((address) => ({ address, family: address.includes(":") ? 6 : 4 }));
  };
}

function failure(e) {
  return { name: e.name, type: e.constructor.name, message: e.message, hops: e.hops ?? null };
}

// The signal of a "check" item's "abort": aborted with `reason`, `after` ms from now (at once for 0).
function abortSignal({ after, reason }) {
  const c = new AbortController();
  if (after === 0) c.abort(reason);
  else setTimeout(() => c.abort(reason), after);
  return c.signal;
}

async function fetchItem(item) {
  const options = { ...item.options };
  if (item.answers !== undefined) options.resolve = resolver(item.answers);
  if (item.ca !== undefined) options.tls = { ...options.tls, ca: item.ca };
  if (item.agent) { // true, or the options of an https.Agent
    options.agent = item.agent === true ? new http.Agent() : new https.Agent(item.agent);
    const create = options.agent.createConnection;
    options.agent.createConnection = function createConnection(...a) {
      rec.agent = (rec.agent ?? 0) + 1;
      return create.apply(this, a);
    };
  }
  target = Number.isInteger(item.origin) ? { redirect: item.origin } : {}; // no origin: nothing may connect
  try {
    const { status, body, hops } = await gf.guardedFetch(item.url, options);
    return { ok: { status, body: body.toString("base64"), hops } };
  } catch (e) {
    return { error: failure(e) };
  }
}

async function openSocketItem(item) {
  if (item.autoSelectFamily !== undefined) net.setDefaultAutoSelectFamily?.(item.autoSelectFamily);
  target = { only: listenerPort };
  const before = accepted.length;
  let out;
  try {
    const s = await gf.openSocket(item.addr, item.port ?? listenerPort, { host: item.tls ?? null, timeout: 2000 });
    s.destroy();
    out = { ok: true };
  } catch (e) {
    out = { error: failure(e) };
  }
  await new Promise((ok) => setTimeout(ok, out.ok ? 50 : 0));
  return { ...out, accepted: accepted.length - before,
    autoSelectFamily: net.getDefaultAutoSelectFamily?.() ?? null };
}

async function runItem(item) {
  rec = { connects: [], lookups: [], resolves: [], violations: [] };
  const saved = {};
  for (const [k, v] of Object.entries(item.env ?? {})) {
    saved[k] = process.env[k];
    if (v === null) delete process.env[k];
    else process.env[k] = v;
  }
  let out;
  try {
    if (item.op === "fetch") out = await fetchItem(item);
    else if (item.op === "check") {
      const signal = item.abort === undefined ? undefined : abortSignal(item.abort);
      out = { ok: await gf.check(item.url, { ...item.options, signal }) };
    }
    else if (item.op === "checkAddrs") out = { ok: await gf.checkAddrs(item.addrs, item.options) };
    else if (item.op === "openSocket") out = await openSocketItem(item);
    else if (item.op === "wait") out = await new Promise((ok) => setTimeout(ok, item.ms, { ok: true }));
    else throw new Error(`unknown op ${item.op}`);
  } catch (e) {
    out = { error: failure(e) };
  } finally {
    for (const [k, v] of Object.entries(saved)) {
      if (v === undefined) delete process.env[k];
      else process.env[k] = v;
    }
  }
  const r = { ...out, ...rec };
  rec = null;
  target = null;
  return r;
}

const job = JSON.parse(fs.readFileSync(0, "utf8"));
const results = [];
for (const item of job.items) results.push(await runItem(item));
listener.close();
process.stdout.write(JSON.stringify({ node: process.version, results, strays }) + "\n");
