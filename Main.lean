import UrlFence

/-!
# `urlfence` command-line tool

    urlfence check --allow PATTERN … [--deny PATTERN …] [--scheme http|https …] [--stdin] [-- URL …]

Each URL is checked with the proven `UrlFence.Policy.check`, and one JSON object is printed per URL:

    {"input":"https://docs.python.org/3/","decision":"allow","scheme":"https","host":"docs.python.org","port":null}
    {"input":"https://docs.python.org.evil.com/","decision":"deny","scheme":"https","host":"docs.python.org.evil.com","port":null}
    {"input":"https://docs.python.org@evil.com/","decision":"reject","reason":"userinfo"}

* A pattern is a host (`docs.python.org`, `192.0.2.1`) or `*.` and a domain (every strict
  subdomain). Patterns must be in the strict host form, or the tool exits with status 2.
* Only `https` is allowed unless `--scheme` says otherwise.
* URLs come after `--`, or one per line on stdin with `--stdin` (read to the end first). Anything
  else before `--` that is not an option is a usage error, so a URL can never be taken for an option.
* The exit status is 0 when at least one URL was checked and every URL is allowed, 1 when any is
  denied or rejected, and 2 for a usage error, including no URLs at all.
* A stdin line that is not UTF-8 is rejected with reason `encoding` and reported by its bytes
  (`input_hex`). Any other character outside printable ASCII is rejected with reason `chars`. An
  argument that is not UTF-8 is decoded lossily before this program sees it (U+FFFD for each bad
  sequence), so it is rejected as `chars`, not `encoding`.
* The output is ASCII: other characters are written as `\u` escapes.

    urlfence addr [--nat64 PREFIX/96 …] [--deny PREFIX …] [--stdin] [-- ADDRESS …]

Each resolved address is checked with the proven `UrlFence.Addr.Config.check`, and one JSON object
is printed per address, with the address family, the address as printed by RFC 5952 (or dotted
decimal), and for a denial the first rule that denies it (`UrlFence.Addr.Config.explain`):

    {"input":"8.8.8.8","decision":"allow","family":"ipv4","addr":"8.8.8.8"}
    {"input":"::ffff:127.0.0.1","decision":"deny","family":"ipv6","addr":"::ffff:7f00:1","reason":"mapped 127.0.0.1: registry 127.0.0.0/8 Loopback"}
    {"input":"fe80::1%eth0","decision":"reject","reason":"parse"}

* A prefix is `ADDRESS/LENGTH` in the strict form (`UrlFence.Addr.parsePrefix`): a length of at
  most 32 or 128 without leading zeros, and no bit set after it. `--deny` takes IPv4 and IPv6
  prefixes. `--nat64` takes a /96 that URLFence honours as a NAT64 prefix (`64:ff9b::/96`, or a /96
  inside 2000::/3 outside every registry block that is not globally reachable); any other is a
  usage error rather than a prefix that would be silently ignored.
* Addresses, stdin, the exit status and the ASCII output are as for `check`; a rejected address has
  reason `parse` (an argument that is not UTF-8 too, decoded lossily as above), or `encoding` for a
  stdin line that is not UTF-8.

This file only parses arguments and prints results; the decisions come from the library.
-/

open UrlFence

structure Args where
  allow : Array String := #[]
  deny : Array String := #[]
  schemes : Array String := #[]
  stdin : Bool := false
  urls : Array String := #[]

def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--" :: rest, a => .ok { a with urls := a.urls ++ rest.toArray }
  | "--allow" :: p :: rest, a => parseArgs rest { a with allow := a.allow.push p }
  | "--deny" :: p :: rest, a => parseArgs rest { a with deny := a.deny.push p }
  | "--scheme" :: s :: rest, a => parseArgs rest { a with schemes := a.schemes.push s }
  | "--stdin" :: rest, a => parseArgs rest { a with stdin := true }
  | opt :: _, _ =>
    if opt.startsWith "--" then .error s!"unknown or incomplete option: {opt}"
    else .error s!"URLs go after `--`: {opt}"

/-- A JSON string literal in ASCII. -/
def jsonString (s : String) : String :=
  let hex (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
  let u (n : Nat) : String :=
    String.ofList ['\\', 'u', hex (n / 4096 % 16), hex (n / 256 % 16), hex (n / 16 % 16), hex (n % 16)]
  let esc (c : Char) : String :=
    if c = '"' then "\\\"" else if c = '\\' then "\\\\"
    else if c = '\n' then "\\n" else if c = '\r' then "\\r" else if c = '\t' then "\\t"
    else if c.toNat < 0x20 || c.toNat ≥ 0x7f then
      -- Outside the BMP: a UTF-16 surrogate pair.
      if c.toNat ≥ 0x10000 then
        let v := c.toNat - 0x10000
        u (0xD800 + v / 1024) ++ u (0xDC00 + v % 1024)
      else u c.toNat
    else String.singleton c
  "\"" ++ String.join (s.toList.map esc) ++ "\""

def reasonName : Reason → String
  | .chars => "chars"
  | .scheme => "scheme"
  | .userinfo => "userinfo"
  | .percent => "percent"
  | .ipv6 => "ipv6"
  | .port => "port"
  | .host => "host"

def urlFields (u : Url) : String :=
  let port := match u.port with
    | some p => jsonString (String.ofList p)
    | none => "null"
  s!"\"scheme\":\"{u.scheme.name}\",\"host\":{jsonString u.host.toString},\"port\":{port}"

def decisionJson (input : String) : Decision → String
  | .allow u => s!"\{\"input\":{jsonString input},\"decision\":\"allow\",{urlFields u}}"
  | .deny u => s!"\{\"input\":{jsonString input},\"decision\":\"deny\",{urlFields u}}"
  | .reject r => s!"\{\"input\":{jsonString input},\"decision\":\"reject\",\"reason\":\"{reasonName r}\"}"

def usageCheck : String :=
  "usage: urlfence check --allow PATTERN ... [--deny PATTERN ...] [--scheme http|https ...] [--stdin] [-- URL ...]"

def usageAddr : String :=
  "usage: urlfence addr [--nat64 PREFIX/96 ...] [--deny PREFIX ...] [--stdin] [-- ADDRESS ...]"

def usage : String := usageCheck ++ "\n" ++ usageAddr

structure AddrArgs where
  nat64 : Array String := #[]
  deny : Array String := #[]
  stdin : Bool := false
  addrs : Array String := #[]

def parseAddrArgs : List String → AddrArgs → Except String AddrArgs
  | [], a => .ok a
  | "--" :: rest, a => .ok { a with addrs := a.addrs ++ rest.toArray }
  | "--nat64" :: p :: rest, a => parseAddrArgs rest { a with nat64 := a.nat64.push p }
  | "--deny" :: p :: rest, a => parseAddrArgs rest { a with deny := a.deny.push p }
  | "--stdin" :: rest, a => parseAddrArgs rest { a with stdin := true }
  | opt :: _, _ =>
    if opt.startsWith "--" then .error s!"unknown or incomplete option: {opt}"
    else .error s!"addresses go after `--`: {opt}"

/-- The configuration from the options, or why they are not usable. -/
def addrConfig (a : AddrArgs) : Except String Addr.Config := do
  let mut deny4 : Array (Addr.Prefix 32) := #[]
  let mut deny6 : Array (Addr.Prefix 128) := #[]
  for d in a.deny do
    match Addr.parsePrefixString d with
    | some (.v4 p) => deny4 := deny4.push p
    | some (.v6 p) => deny6 := deny6.push p
    | none => throw s!"--deny {d}: not ADDRESS/LENGTH in the strict form, with no bits set after the length"
  let mut nat64 : Array (BitVec 128) := #[]
  for n in a.nat64 do
    match Addr.parsePrefixString n with
    | some (.v6 p) =>
      if p.len != 96 then throw s!"--nat64 {n}: a NAT64 prefix must be a /96"
      if !Addr.nat64Ok p.base then
        throw (s!"--nat64 {n}: this prefix would be ignored; only 64:ff9b::/96, or a /96 inside 2000::/3 " ++
          "that meets no registry block that is not globally reachable, is used as a NAT64 prefix")
      nat64 := nat64.push p.base
    | _ => throw s!"--nat64 {n}: not an IPv6 ADDRESS/96 in the strict form, with no bits set after the length"
  pure { deny4 := deny4.toList, deny6 := deny6.toList, nat64 := nat64.toList }

def addrFields (a : Addr) : String :=
  let family := match a with
    | .v4 _ => "ipv4"
    | .v6 _ => "ipv6"
  s!"\"family\":\"{family}\",\"addr\":{jsonString a.toString}"

def verdictJson (cfg : Addr.Config) (input : String) : Addr.Verdict → String
  | .allow a => s!"\{\"input\":{jsonString input},\"decision\":\"allow\",{addrFields a}}"
  | .deny a =>
    -- `explain` is `none` exactly when the address is allowed (`explain_eq_none_iff`).
    let why := ((cfg.explain a).map Addr.Why.text).getD "denied"
    s!"\{\"input\":{jsonString input},\"decision\":\"deny\",{addrFields a},\"reason\":{jsonString why}}"
  | .reject => s!"\{\"input\":{jsonString input},\"decision\":\"reject\",\"reason\":\"parse\"}"

/-- A requested URL: decoded exactly, or a stdin line that is not UTF-8. -/
inductive Input where
  | text (s : String)
  | invalid (bytes : ByteArray)

def hexBytes (b : ByteArray) : String :=
  let hex (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
  String.ofList (b.toList.flatMap fun x => [hex (x.toNat / 16), hex (x.toNat % 16)])

partial def readAll (h : IO.FS.Stream) (acc : ByteArray) : IO ByteArray := do
  let chunk ← h.read 65536
  if chunk.isEmpty then return acc
  readAll h (acc ++ chunk)

/-- Split stdin into lines (a final newline does not start another line) and decode each. -/
def stdinInputs (b : ByteArray) : Array Input :=
  let lines := b.toList.splitOn 10
  let lines := if lines.getLast? == some [] then lines.dropLast else lines
  lines.toArray.map fun l =>
    let bytes := ByteArray.mk l.toArray
    match String.fromUTF8? bytes with
    | some s => .text s
    | none => .invalid bytes

def checkInput (pol : Policy) : Input → String × Bool
  | .text s => let d := pol.checkString s; (decisionJson s d, d matches .allow _)
  | .invalid b => (s!"\{\"input_hex\":\"{hexBytes b}\",\"decision\":\"reject\",\"reason\":\"encoding\"}", false)

def checkAddrInput (cfg : Addr.Config) : Input → String × Bool
  | .text s => let v := cfg.checkString s; (verdictJson cfg s v, v matches .allow _)
  | .invalid b => (s!"\{\"input_hex\":\"{hexBytes b}\",\"decision\":\"reject\",\"reason\":\"encoding\"}", false)

def run (argv : List String) : IO UInt32 := do
  match argv with
  | "addr" :: rest =>
    match parseAddrArgs rest {} with
    | .error e => IO.eprintln e; IO.eprintln usageAddr; return 2
    | .ok a =>
    match addrConfig a with
    | .error e => IO.eprintln e; return 2
    | .ok cfg =>
      let fromStdin ← if a.stdin then pure (stdinInputs (← readAll (← IO.getStdin) .empty)) else pure #[]
      let inputs := a.addrs.map .text ++ fromStdin
      if inputs.isEmpty then IO.eprintln "no addresses to check"; return 2
      let mut ok := true
      for i in inputs do
        let (line, allowed) := checkAddrInput cfg i
        if !allowed then ok := false
        IO.println line
      return if ok then 0 else 1
  | "check" :: rest =>
    match parseArgs rest {} with
    | .error e => IO.eprintln e; IO.eprintln usageCheck; return 2
    | .ok a =>
      if a.allow.isEmpty then IO.eprintln "at least one --allow pattern is required"; IO.eprintln usageCheck; return 2
      let schemes := if a.schemes.isEmpty then ["https"] else a.schemes.toList
      match Policy.make schemes a.allow.toList a.deny.toList with
      | none =>
        IO.eprintln "a pattern is not a strict host or *.domain, or a scheme is not http/https"; return 2
      | some pol =>
        let fromStdin ← if a.stdin then pure (stdinInputs (← readAll (← IO.getStdin) .empty)) else pure #[]
        let inputs := a.urls.map .text ++ fromStdin
        if inputs.isEmpty then IO.eprintln "no URLs to check"; return 2
        let mut ok := true
        for i in inputs do
          let (line, allowed) := checkInput pol i
          if !allowed then ok := false
          IO.println line
        return if ok then 0 else 1
  | ["--version"] => IO.println "urlfence 0.1.0"; return 0
  | _ => IO.eprintln usage; return 2

def main (argv : List String) : IO UInt32 := run argv
