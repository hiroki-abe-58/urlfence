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
  (`input_hex`). Any other character outside printable ASCII is rejected with reason `chars`.
* The output is ASCII: other characters are written as `\u` escapes.

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

def usage : String :=
  "usage: urlfence check --allow PATTERN ... [--deny PATTERN ...] [--scheme http|https ...] [--stdin] [-- URL ...]"

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

def run (argv : List String) : IO UInt32 := do
  match argv with
  | "check" :: rest =>
    match parseArgs rest {} with
    | .error e => IO.eprintln e; IO.eprintln usage; return 2
    | .ok a =>
      if a.allow.isEmpty then IO.eprintln "at least one --allow pattern is required"; IO.eprintln usage; return 2
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
