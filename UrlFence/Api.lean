import UrlFence.Policy

/-!
# String-level API

Entry points for Lean callers and the command-line tool. Patterns are written as a host
(`docs.python.org`, `192.0.2.1`) or as `*.` followed by a domain (`*.example.com`, every strict
subdomain). Both must be in the strict host form; anything else is refused (`parsePattern`).
-/

namespace UrlFence

/-- Parse a pattern: `*.<domain>` for strict subdomains, otherwise one exact host. -/
def parsePattern (s : String) : Option Pattern :=
  match s.toList with
  | '*' :: '.' :: rest =>
    match parseHost rest with
    | some (.domain ls) => some (.sub ls)
    | _ => none
  | l => (parseHost l).map .exact

def Scheme.name : Scheme → String
  | .http => "http"
  | .https => "https"

def parseScheme? : String → Option Scheme
  | "http" => some .http
  | "https" => some .https
  | _ => none

/-- Parse a list of patterns; `none` if any is not in the strict form. -/
def parsePatterns : List String → Option (List Pattern)
  | [] => some []
  | s :: ss => do
    let p ← parsePattern s
    let ps ← parsePatterns ss
    pure (p :: ps)

/-- A policy from strings; `none` if a scheme or pattern is not understood. -/
def Policy.make (schemes allow deny : List String) : Option Policy := do
  let schemes ← schemes.mapM parseScheme?
  let allow ← parsePatterns allow
  let deny ← parsePatterns deny
  pure { schemes, allow, deny }

def Policy.checkString (pol : Policy) (s : String) : Decision := pol.check s.toList

def Host.toString (h : Host) : String := String.ofList h.render

/-- A parsed subdomain pattern is a valid domain. -/
theorem parsePattern_sub_valid (s : String) (d : List (List Char)) (h : parsePattern s = some (.sub d)) :
    domainOk d = true := by
  unfold parsePattern at h
  split at h
  · rename_i rest _
    split at h
    · rename_i ls hls
      injection h with h; injection h with h; subst h
      exact parseHost_valid rest _ hls
    · exact absurd h (by simp)
  · rename_i l _
    cases parseHost l <;> simp at h

end UrlFence
