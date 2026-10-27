// WHATWG URL oracle: reads one JSON string per line on stdin, prints one JSON object per line with
// what Node's URL parser (an implementation of the WHATWG URL Standard) makes of it.
const lines = require("fs").readFileSync(0, "utf8").split("\n").filter((l) => l.length > 0);
for (const l of lines) {
  const s = JSON.parse(l);
  try {
    const u = new URL(s);
    console.log(JSON.stringify({ ok: true, protocol: u.protocol, hostname: u.hostname, port: u.port,
                                 username: u.username, password: u.password }));
  } catch (e) {
    console.log(JSON.stringify({ ok: false }));
  }
}
