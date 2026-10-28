// Fetch a URL for an agent, in Node: URLFence decides on the URL and on every address its host
// resolves to, and only a checked address is connected to. The counterpart of guarded_fetch.py.
//
//     import { guardedFetch } from "./guarded_fetch.mjs";
//     const { status, body, hops } = await guardedFetch("https://docs.python.org/3/", { allow: ["docs.python.org"] });
//
// An example to adapt, not a hardened HTTP client. Node 18 or later, no dependencies.
//
// 1. `urlfence check` decides on the URL (execFile, no shell, with a timeout). Its answer is used
//    only if it is one JSON object for exactly this URL, and the exit status agrees with the
//    decision; a timeout, a missing binary, malformed output or input it cannot take (a NUL, say)
//    refuses.
// 2. Pinned (`pin: true`, the default): the host is resolved once (`dns.promises.lookup` with
//    `all: true`, or `options.resolve`), and `urlfence addr` checks every address it resolves to
//    (with `denyAddr` and `nat64` as its `--deny` and `--nat64`). If any address is denied, or the
//    answer is unusable in the same ways as above, or an answer's `addr` is not numerically the
//    address checked, the fetch is refused before any connection is opened. Otherwise the request
//    goes over a connection that guardedFetch opens itself to a checked address (`openSocket`:
//    `net.connect` or `tls.connect` with that address as `host`, for which Node does no lookup, and
//    a `lookup` that refuses in case it ever did), with no Agent. The `Host` header, the TLS server
//    name and the name the certificate must match are the URL's host. A proxy resolves the name
//    itself, so nothing could be pinned: with `pin: true`, passing `agent` is an error. Pinned
//    requests never use an Agent, so no proxy can take them over; still, so that a configured
//    proxy is not silently bypassed, a proxy set in the environment for the URL's scheme refuses
//    while Node's own proxy support is on (`NODE_USE_ENV_PROXY`, `--use-env-proxy`; Node 18 has
//    none). `NO_PROXY` is not consulted. With `pin: false`, Node's http(s).request (with `agent`,
//    or the global agent and any proxy it uses) resolves the name again, and no address is
//    checked; a proxy must then enforce its own address policy.
// 3. The request (GET) is for exactly the URL that was checked: in both modes the request target
//    is the checked URL after its host and port, without the fragment.
// 4. Redirects are never followed by Node: each `Location` is resolved against the current URL
//    (WHATWG `new URL(location, url)`) and checked again, the URL and (pinned) the addresses, before
//    the next request, at most `maxRedirects` times. A name that answered a public address on one
//    hop and a private one on the next is refused at the second.
//
// The last response is returned whatever its status, with the body cut at `maxBytes` (nothing says
// whether it was cut). `timeout` (milliseconds) bounds each urlfence run and each period without
// socket activity, not the whole fetch: a server that sends slowly can hold a fetch much longer.
// `hops` lists each check: the URL's decision and, pinned, each address's.
//
// Not covered: the port and path are not restricted, a server on an allowed address may forward
// the request, only TCP is pinned, and `fetch()` (undici) is not used or pinned. See the README.
//
// Deliberate differences from guarded_fetch.py:
// * `Location` is resolved as WHATWG does, not as urljoin, and the result is normalised before
//   it is checked: the host is percent-decoded and lowercased (`DOCS%2Eexample.com` becomes
//   `docs.example.com`), tabs and newlines are removed, backslashes become slashes, dot segments
//   (also `%2e%2e`) and a default port are dropped, IPv4 number forms are made canonical (`0x7f.1`
//   becomes `127.0.0.1`), and a space in the path becomes `%20`. guarded_fetch.py would check the
//   raw string, and URLFence refuses most of these forms. This is not a way around the check: the
//   normalised string is what is checked, address included, and requested, exactly, and a server
//   could just as well have sent that string.
// * Unpinned, the request is built from URLFence's reading and the checked string, as pinned,
//   rather than by handing the URL to the library (Node would parse it again and normalise the
//   path); `agent` takes the place of `proxies`.
// * The environment refuses only when Node's own proxy support may be on, since Node's http
//   ignores HTTP_PROXY otherwise; NO_PROXY is not consulted, and ALL_PROXY, which Node does not
//   use, is not considered.
// * `tls` (CA, client certificate, cipher and version options) takes the place of an SSLContext;
//   options that could turn verification off are refused. Certificates are verified, against the
//   URL's host, whatever NODE_TLS_REJECT_UNAUTHORIZED says. With `pin: false` the `tls` options go
//   to https.request with `rejectUnauthorized: true`, but the options of an `agent` passed in
//   override them there (an agent made with `rejectUnauthorized: false` does not verify).
// * Stricter checks: lists must be arrays of strings; `timeout` must be at least 1 ms (Node takes
//   0 as no timeout); URLFence's reading must be followed by `/`, `?`, `#` or the end, with a port
//   from 1 to 65535; an answer's `addr` must be a string; the pinned request must be on the
//   connection guardedFetch opened (in case code patches `http`).
// * `timeout` and `resolve` are options, and the result is an object.
import { execFile } from "node:child_process";
import dns from "node:dns";
import http from "node:http";
import https from "node:https";
import net from "node:net";
import tls from "node:tls";

export const URLFENCE = process.env.URLFENCE_BIN ?? "urlfence";
export const TIMEOUT = 10000;
const DECISIONS = ["allow", "deny", "reject"];
const REDIRECTS = [301, 302, 303, 307, 308];
// What `tls` may set for https. Nothing here can turn verification off; the address, port, server
// name, lookup and certificate checks are guardedFetch's.
const TLS_KEYS = ["ca", "cert", "key", "pfx", "passphrase", "ciphers", "minVersion", "maxVersion", "secureContext"];

export class Refused extends Error {
  // URLFence did not allow a URL or an address on the way (`hops` lists every check), or a request failed.
  constructor(message, hops) {
    super(message);
    this.name = "Refused";
    this.hops = hops;
  }
}

function strings(lists) {
  for (const [name, value] of Object.entries(lists)) {
    if (!Array.isArray(value) || !value.every((s) => typeof s === "string")) {
      throw new TypeError(`${name} must be an array of strings`);
    }
  }
}

// Node takes a timeout of 0 as none at all.
function millis(timeout) {
  if (!Number.isSafeInteger(timeout) || timeout < 1) throw new TypeError("timeout must be an integer, at least 1 ms");
}

// Run urlfence: {code, stdout (ASCII; any other byte becomes U+FFFD), stderr}, or {error}.
function run(args, timeout) {
  return new Promise((resolve) => {
    let child;
    try {
      child = execFile(URLFENCE, args, { encoding: "buffer", timeout, killSignal: "SIGKILL", maxBuffer: 64 << 20 },
        (err, stdout, stderr) => {
          if (err && typeof err.code !== "number") {
            resolve({ error: err.killed ? `no answer within ${timeout} ms` : err.message });
          } else {
            resolve({ code: err ? err.code : 0, stdout: stdout.toString("latin1").replace(/[\x80-\xff]/g, "\ufffd"),
              stderr: stderr.toString("utf8") });
          }
        });
    } catch (e) {
      resolve({ error: e.message }); // an argument execFile cannot pass, such as one with a NUL
      return;
    }
    child.stdin.on("error", () => {});
    child.stdin.end(); // nothing on stdin
  });
}

function parse(line) {
  try {
    const r = JSON.parse(line);
    return r !== null && typeof r === "object" && !Array.isArray(r) ? r : null;
  } catch {
    return null;
  }
}

// URLFence's answer for one URL, as an object; a `reject` whenever the answer is unusable.
export async function check(url, { allow, deny = [], schemes = ["https"], timeout = TIMEOUT } = {}) {
  strings({ allow, deny, schemes });
  millis(timeout);
  if (typeof url !== "string") return { decision: "reject", reason: "urlfence did not run: the URL is not a string" };
  const args = ["check"];
  for (const a of allow) args.push("--allow", a);
  for (const d of deny) args.push("--deny", d);
  for (const s of schemes) args.push("--scheme", s);
  const p = await run([...args, "--", url], timeout);
  if (p.error !== undefined) return { decision: "reject", reason: `urlfence did not run: ${p.error}` };
  if (p.code === 2) return { decision: "reject", reason: "urlfence: " + p.stderr.trim() }; // a usage error
  const lines = p.stdout.split("\n");
  if (lines.length !== 2 || lines[1] !== "") {
    return { decision: "reject", reason: `unexpected urlfence output (exit ${p.code})` };
  }
  const r = parse(lines[0]);
  if (r === null || r.input !== url) return { decision: "reject", reason: "urlfence answered for something else" };
  if (!DECISIONS.includes(r.decision)) return { decision: "reject", reason: "urlfence gave no decision" };
  // The exit status is 0 exactly when every URL is allowed; a mismatch means a confused answer.
  if ((r.decision === "allow") !== (p.code === 0)) {
    return { decision: "reject", reason: `urlfence exit ${p.code} disagrees with its decision` };
  }
  return r;
}

// URLFence's answers for these address strings, as {answers, reason: null}, or {answers: null,
// reason} when there is no usable answer.
export async function checkAddrs(addrs, { deny = [], nat64 = [], timeout = TIMEOUT } = {}) {
  strings({ deny, nat64 });
  millis(timeout);
  const args = ["addr"];
  for (const d of deny) args.push("--deny", d);
  for (const n of nat64) args.push("--nat64", n);
  const p = await run([...args, "--", ...addrs], timeout);
  const none = (reason) => ({ answers: null, reason });
  if (p.error !== undefined) return none(`urlfence did not run: ${p.error}`);
  if (p.code === 2) return none("urlfence: " + p.stderr.trim()); // a usage error, e.g. an invalid prefix
  const lines = p.stdout.split("\n");
  if (lines.length !== addrs.length + 1 || lines[lines.length - 1] !== "") {
    return none(`unexpected urlfence output (exit ${p.code})`);
  }
  const answers = [];
  for (let i = 0; i < addrs.length; i++) {
    const r = parse(lines[i]);
    if (r === null || r.input !== addrs[i] || !DECISIONS.includes(r.decision)) {
      return none("urlfence answered for something else");
    }
    answers.push(r);
  }
  if (answers.every((r) => r.decision === "allow") !== (p.code === 0)) {
    return none(`urlfence exit ${p.code} disagrees with its decisions`);
  }
  return { answers, reason: null };
}

// The numeric value of an IPv4 or IPv6 address in numeric form, as a string to compare, or null
// (for a name, a scoped address or anything else).
export function addrKey(s) {
  if (typeof s !== "string" || s.includes("%")) return null;
  const family = net.isIP(s);
  if (family === 4) return "4:" + s;
  if (family !== 6) return null;
  const quad = /(\d+)\.(\d+)\.(\d+)\.(\d+)$/.exec(s);
  const text = quad ? s.slice(0, quad.index) + "0:0" : s;
  const [left, right] = text.split("::").map((h) => (h ? h.split(":") : []));
  const groups = right === undefined ? left : [...left, ...Array(8 - left.length - right.length).fill("0"), ...right];
  const n = groups.map((g) => parseInt(g, 16));
  if (quad) n.splice(6, 2, quad[1] * 256 + +quad[2], quad[3] * 256 + +quad[4]);
  return "6:" + n.join(":");
}

function noLookup(host, options, callback) {
  callback(new Error(`guardedFetch: refusing to resolve ${host} on a pinned connection`));
}

// A connection to exactly this numeric address and port; with `host`, over TLS with `host` as the
// server name and the name the certificate must match. Anything that is not an IPv4 or IPv6
// address in numeric form (a name, a scoped address) is a TypeError, so nothing is resolved here.
export function openSocket(addr, port, { host = null, tlsOptions = {}, timeout = TIMEOUT } = {}) {
  if (addrKey(addr) === null) throw new TypeError(`not a numeric address: ${JSON.stringify(addr)}`);
  millis(timeout);
  const where = { host: addr, port, lookup: noLookup, timeout };
  return new Promise((resolve, reject) => {
    const s = host === null ? net.connect(where) : tls.connect({
      ...tlsOptions, ...where, path: undefined, socket: undefined, rejectUnauthorized: true,
      servername: net.isIP(host) ? undefined : host, // RFC 6066: no server name for an address
      checkServerIdentity: (_, cert) => tls.checkServerIdentity(host, cert),
    });
    s.on("timeout", () => s.destroy(new Error(`no activity for ${timeout} ms`)));
    s.on("error", () => {}); // after the connection, errors reach the request
    s.once("error", reject);
    s.once(host === null ? "connect" : "secureConnect", () => {
      s.off("error", reject);
      resolve(s);
    });
  });
}

// One GET: {status, headers, body (at most maxBytes)}. With `sock`, the request must go over it.
function exchange(mod, options, maxBytes, sock = null) {
  return new Promise((resolve, reject) => {
    let settled = false;
    let req = null;
    const finish = (err, value) => {
      if (settled) return;
      settled = true;
      req?.destroy();
      sock?.destroy();
      if (err) reject(err);
      else resolve(value);
    };
    try {
      req = mod.request(options);
    } catch (e) {
      finish(e);
      return;
    }
    if (sock) req.once("socket", (s) => s !== sock && finish(new Error("the request is not on our connection")));
    req.on("timeout", () => req.destroy(new Error(`no activity for ${options.timeout} ms`)));
    req.on("error", (e) => finish(e));
    req.on("response", (res) => {
      const chunks = [];
      let n = 0;
      const end = () => finish(null, { status: res.statusCode, headers: res.headers, body: Buffer.concat(chunks) });
      res.on("data", (d) => {
        const part = d.subarray(0, maxBytes - n);
        chunks.push(part);
        n += part.length;
        if (n >= maxBytes) end();
      });
      res.on("end", end);
      res.on("error", (e) => finish(e));
      res.on("close", () => finish(new Error("the response ended early")));
      if (maxBytes === 0) end();
    });
    req.end();
  });
}

// What the request is for: URLFence's reading `r` of `url`, which must be how `url` starts.
function reading(url, r, hops) {
  const { scheme, host, port } = r;
  const prefix = `${scheme}://${host}` + (port == null ? "" : `:${port}`);
  const rest = url.startsWith(prefix) ? url.slice(prefix.length) : null;
  const defaultPort = scheme === "https" ? 443 : 80;
  const portN = port == null ? defaultPort : Number(port);
  if (!["http", "https"].includes(scheme) || typeof host !== "string" || rest === null || !/^([/?#]|$)/.test(rest)
      || !Number.isInteger(portN) || portN < 1 || portN > 65535) {
    throw new Refused("urlfence's reading of the URL does not match it", hops);
  }
  let target = rest.split("#", 1)[0]; // path and query, as checked; empty or `?...`
  if (!target.startsWith("/")) target = "/" + target;
  const headers = { Host: portN === defaultPort ? host : `${host}:${portN}`, "Accept-Encoding": "identity",
    Connection: "close" };
  return { scheme, host, port: portN, target, headers };
}

// The proxy Node's own http(s) support would take from the environment for this scheme, if that
// support is on; null otherwise.
function envProxy(scheme) {
  const env = process.env;
  const flags = [...process.execArgv, ...(env.NODE_OPTIONS ?? "").split(/\s+/)];
  const on = !["", "0"].includes(env.NODE_USE_ENV_PROXY ?? "")
    || flags.some((f) => f === "--use-env-proxy" || f.startsWith("--use-env-proxy="))
    || (scheme === "https" ? https : http).globalAgent?.options?.proxyEnv != null;
  const proxy = scheme === "https" ? env.https_proxy || env.HTTPS_PROXY : env.http_proxy || env.HTTP_PROXY;
  return on && proxy ? proxy : null;
}

// GET `url`, which URLFence read as `r`, over a connection to a checked address of its host.
async function pinnedGet(url, r, hop, hops, o) {
  const { scheme, host, port, target, headers } = reading(url, r, hops);
  if (envProxy(scheme) !== null) {
    throw new Refused(`a proxy is set in the environment for ${scheme} and Node's proxy support is on; pinning `
      + "needs a direct connection (use pin: false to go through the proxy)", hops);
  }
  const addrs = [];
  try {
    for (const a of await o.resolve(host, { all: true })) {
      if (typeof a?.address !== "string") throw new Error("the resolver gave something other than an address");
      if (!addrs.includes(a.address)) addrs.push(a.address);
    }
  } catch (e) {
    throw new Refused(`could not resolve ${JSON.stringify(host)}: ${e.message}`, hops);
  }
  if (addrs.length === 0) throw new Refused(`${JSON.stringify(host)} has no address`, hops);
  const { answers, reason: why } = await checkAddrs(addrs, { deny: o.denyAddr, nat64: o.nat64, timeout: o.timeout });
  if (answers === null) {
    hop.addrs = addrs.map((a) => ({ addr: a, decision: "reject", reason: why }));
    throw new Refused(`reject (${why}): the addresses of ${JSON.stringify(host)}`, hops);
  }
  hop.addrs = answers.map((a) => ({ addr: a.input, decision: a.decision, reason: a.reason ?? null }));
  for (const a of answers) {
    if (a.decision !== "allow") {
      throw new Refused(`${a.decision} (${a.reason}): ${JSON.stringify(host)} resolves to ${a.input}`, hops);
    }
    // Connect only to the address that was checked: the printed form must be that address.
    if (addrKey(a.addr) === null || addrKey(a.addr) !== addrKey(a.input)) {
      throw new Refused(`urlfence printed ${JSON.stringify(a.addr)} for ${JSON.stringify(a.input)}`, hops);
    }
  }
  let failure = null;
  for (const a of answers) { // every one is allowed; connect to the first that answers
    let sock;
    try {
      sock = await openSocket(a.addr, port, { host: scheme === "https" ? host : null, tlsOptions: o.tls,
        timeout: o.timeout });
    } catch (e) {
      if (e instanceof TypeError) throw new Refused(`request failed: ${e.message}`, hops);
      failure = e; // refused, timed out, or the TLS handshake or certificate failed: try the next
      continue;
    }
    hop.connected = a.addr;
    try {
      return await exchange(http, { host: a.addr, port, method: "GET", path: target, headers,
        createConnection: () => sock }, o.maxBytes, sock);
    } catch (e) {
      throw new Refused(`request failed: ${e.message}`, hops);
    }
  }
  throw new Refused(`request failed: ${failure?.message}`, hops);
}

// GET `url` with Node's http(s).request and `o.agent` (or the global agent): Node resolves the name.
// The agent's own options override these (its `rejectUnauthorized`, say).
async function unpinnedGet(url, r, hops, o) {
  const { scheme, host, port, target, headers } = reading(url, r, hops);
  try {
    return await exchange(scheme === "https" ? https : http, { ...o.tls, host, port, method: "GET", path: target,
      headers, agent: o.agent, timeout: o.timeout, servername: net.isIP(host) ? "" : host, rejectUnauthorized: true },
    o.maxBytes);
  } catch (e) {
    throw new Refused(`request failed: ${e.message}`, hops);
  }
}

// {status, body, hops} for the last response, or a Refused rejection. `denyAddr` and `nat64` are
// prefixes for `urlfence addr --deny` and `--nat64`; `tls` holds options for https (`ca`, say);
// `resolve(host, {all: true})` answers like `dns.promises.lookup`; `agent` is for pin: false.
export async function guardedFetch(url, { allow, deny = [], schemes = ["https"], maxRedirects = 3, agent,
  maxBytes = 1 << 20, pin = true, denyAddr = [], nat64 = [], tls: tlsOptions = {}, timeout = TIMEOUT,
  resolve = (host, options) => dns.promises.lookup(host, options) } = {}) {
  if (pin && agent !== undefined) {
    throw new Error("an agent connects where it likes, so nothing can be pinned: pass pin: false to use one");
  }
  strings({ allow, deny, schemes, denyAddr, nat64 });
  for (const k of Object.keys(tlsOptions)) {
    if (!TLS_KEYS.includes(k)) throw new TypeError(`tls.${k} is not an option guardedFetch passes on`);
  }
  for (const [name, n] of Object.entries({ maxRedirects, maxBytes })) {
    if (!Number.isSafeInteger(n) || n < 0) throw new TypeError(`${name} must be a non-negative integer`);
  }
  millis(timeout);
  const o = { agent, maxBytes, denyAddr, nat64, tls: tlsOptions, timeout, resolve };
  const hops = [];
  for (let i = 0; i <= maxRedirects; i++) {
    const r = await check(url, { allow, deny, schemes, timeout });
    const hop = { url, decision: r.decision, reason: r.reason ?? null };
    hops.push(hop);
    if (r.decision !== "allow") {
      throw new Refused(`${r.decision}${r.reason ? ` (${r.reason})` : ""}: ${JSON.stringify(url)}`, hops);
    }
    const { status, headers, body } = pin ? await pinnedGet(url, r, hop, hops, o) : await unpinnedGet(url, r, hops, o);
    const location = headers.location;
    if (REDIRECTS.includes(status) && location) {
      try {
        url = new URL(location, url).href; // WHATWG, as Node and browsers resolve it
      } catch {
        throw new Refused(`cannot resolve Location ${JSON.stringify(location)} against ${JSON.stringify(url)}`, hops);
      }
      continue;
    }
    return { status, body, hops };
  }
  throw new Refused(`more than ${maxRedirects} redirects`, hops);
}
