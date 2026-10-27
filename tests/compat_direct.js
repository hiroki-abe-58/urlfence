// The `node direct` view of tests/compat.py: what Node's http and https clients do on their direct
// path (no proxy), observed without any network beyond 127.0.0.1.
//
// Reads one JSON string (a URL) per line on stdin. For each URL it calls `http.request(url)` or
// `https.request(url)`, by the scheme that Node's URL parser reads, with an Agent whose
// `createConnection` records the host and port that Node derived and then lets the Agent connect to
// a fixture on 127.0.0.1 instead. Everything else stays as Node computed it, the TLS server name
// (SNI) included. The fixture records what arrives first on each connection (an HTTP request head,
// or a TLS ClientHello), then answers 403 or a fatal TLS alert, and closes.
//
// Prints one JSON object per URL, in order: {"connect": [[host, port], ...] (one per connection),
// "recs": [base64 of what the fixture received, one per connection], "error": ...}; compat.py
// parses and compares them. A last line reports the Node version and the guard: `dns.lookup` and
// `net.Socket.prototype.connect` refuse, and list, any lookup or connection other than to the
// fixture, and the guard is checked to refuse before any URL is tried.
"use strict";
const dns = require("dns");
const fs = require("fs");
const http = require("http");
const https = require("https");
const net = require("net");

const SLOTS = 8; // URLs in flight; each slot has its own fixture port and tries its URLs one by one
const LIMIT = 65536;
const TIMEOUT = 5000;
const TLS_ALERT = Buffer.from([0x15, 0x03, 0x03, 0x00, 0x02, 0x02, 0x28]); // fatal handshake_failure
const HTTP_403 = "HTTP/1.1 403 Forbidden\r\nContent-Length: 0\r\nConnection: close\r\n\r\n";

// ---- the guard ---------------------------------------------------------------------------------

const violations = [];
const fixturePorts = new Set();
const realLookup = dns.lookup;
dns.lookup = function lookup(host, ...rest) {
  // Server.listen looks up its own address; an IP literal never reaches a resolver.
  if (host === "127.0.0.1") return realLookup.call(this, host, ...rest);
  violations.push(`lookup ${host}`);
  process.nextTick(rest[rest.length - 1], new Error(`compat_direct.js: refusing to resolve ${host}`));
  return undefined;
};
const realConnect = net.Socket.prototype.connect;
net.Socket.prototype.connect = function connect(...args) {
  const a = args[0];
  const o = Array.isArray(a) ? a[0] : a !== null && typeof a === "object" ? a : { port: a, host: args[1] };
  // As in net: a non-empty `path` means a local socket (an http Agent passes `path: null`).
  if (o.path || o.host !== "127.0.0.1" || !fixturePorts.has(Number(o.port))) {
    violations.push(`connect ${o.path ? o.path : `${o.host}:${o.port}`}`);
    throw new Error("compat_direct.js: refusing to connect anywhere but the fixture");
  }
  return realConnect.apply(this, args);
};

// ---- the fixture -------------------------------------------------------------------------------

// The same rule as message_complete() in compat.py: an HTTP head ends with an empty line; a TLS
// ClientHello is complete when its handshake records hold the whole message.
function complete(buf) {
  if (buf.length === 0) return false;
  if (buf[0] !== 0x16) return buf.includes("\r\n\r\n");
  const parts = [];
  let pos = 0;
  while (pos + 5 <= buf.length) {
    if (buf[pos] !== 0x16) return true; // not a handshake record: stop, compat.py reports it
    const n = buf.readUInt16BE(pos + 3);
    if (pos + 5 + n > buf.length) return false;
    parts.push(buf.subarray(pos + 5, pos + 5 + n));
    pos += 5 + n;
    const hs = Buffer.concat(parts);
    if (hs.length >= 4 && hs.length >= 4 + hs.readUIntBE(1, 3)) return true;
  }
  return false;
}

class Slot {
  constructor() {
    this.records = [];
    this.want = null;
    this.server = net.createServer((c) => this.accept(c));
  }

  listen() {
    return new Promise((ok) => this.server.listen(0, "127.0.0.1", () => {
      this.port = this.server.address().port;
      fixturePorts.add(this.port);
      ok();
    }));
  }

  accept(c) {
    let buf = Buffer.alloc(0);
    let done = false;
    const finish = () => {
      if (done) return;
      done = true;
      this.records.push(buf); // recorded before the answer, so the client cannot finish first
      if (this.want !== null && this.records.length >= this.want.n) this.want.resolve();
      c.end(buf[0] === 0x16 ? TLS_ALERT : HTTP_403);
    };
    c.setTimeout(TIMEOUT, () => { finish(); c.destroy(); });
    c.on("data", (d) => {
      if (done) return;
      buf = Buffer.concat([buf, d]);
      if (buf.length >= LIMIT || complete(buf)) finish();
    });
    c.on("end", finish);
    c.on("close", finish);
    c.on("error", () => {});
  }

  // Wait until this slot's fixture has recorded `n` connections (or TIMEOUT passed).
  wait(n) {
    if (this.records.length >= n) return Promise.resolve();
    return new Promise((resolve) => {
      const t = setTimeout(() => { this.want = null; resolve(); }, TIMEOUT);
      this.want = { n, resolve: () => { clearTimeout(t); this.want = null; resolve(); } };
    });
  }
}

// ---- one URL -----------------------------------------------------------------------------------

async function observe(url, slot) {
  const res = { connect: [], recs: [], error: null };
  let mod = null;
  try {
    const protocol = new URL(url).protocol;
    mod = protocol === "https:" ? https : protocol === "http:" ? http : null;
  } catch (e) {
    // refused below
  }
  if (mod === null) {
    res.error = "not an http or https URL to Node";
    return res;
  }
  const agent = new mod.Agent({ keepAlive: false });
  const create = agent.createConnection; // net.createConnection, or https.Agent's (tls.connect)
  agent.createConnection = function createConnection(options, cb) {
    const socket = create.call(this, { ...options, host: "127.0.0.1", port: slot.port }, cb);
    res.connect.push([options.host, options.port]);
    return socket;
  };
  if (slot.records.length !== 0) throw new Error("compat_direct.js: a connection was not matched to its URL");
  await new Promise((done) => {
    let req;
    try {
      req = mod.request(url, { agent, timeout: TIMEOUT });
    } catch (e) {
      res.error = String(e.code || e.message);
      done();
      return;
    }
    req.on("response", (r) => r.resume());
    req.on("timeout", () => req.destroy(new Error("timeout")));
    req.on("error", (e) => { res.error = String(e.code || e.message); });
    req.on("close", done);
    req.end();
  });
  await slot.wait(res.connect.length);
  res.recs = slot.records.splice(0).map((b) => b.toString("base64"));
  agent.destroy();
  return res;
}

async function main() {
  const urls = fs.readFileSync(0, "utf8").split("\n").filter((l) => l.length > 0).map((l) => JSON.parse(l));
  const slots = Array.from({ length: SLOTS }, () => new Slot());
  await Promise.all(slots.map((s) => s.listen()));
  // The guard must refuse a connection that is not to a fixture (here a local port that is not one).
  let guard = false;
  try {
    const s = net.connect({ host: "127.0.0.1", port: 9 });
    s.on("error", () => {});
    s.destroy();
  } catch (e) {
    guard = true;
  }
  violations.length = 0;
  const results = new Array(urls.length);
  await Promise.all(slots.map(async (slot, j) => {
    for (let i = j; i < urls.length; i += SLOTS) results[i] = await observe(urls[i], slot);
  }));
  for (const s of slots) s.server.close();
  process.stdout.write(results.map((r) => JSON.stringify(r) + "\n").join("")
                       + JSON.stringify({ node: process.version, guard, violations }) + "\n");
}

main();
