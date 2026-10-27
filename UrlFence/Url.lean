import UrlFence.Host

/-!
# URLs

`parse` accepts an absolute `http://` or `https://` URL written in a strict form and refuses anything
else with a reason:

* every character is printable ASCII other than space and backslash (`chars`). The WHATWG parser
  strips tabs and newlines anywhere and reads `\` as `/`, so those would change the meaning;
* the scheme is `http` or `https`, in lowercase, followed by `//` (`scheme`);
* the authority (up to the first `/`, `?` or `#`) contains no `@` (`userinfo`), no `%`
  (`percent`), and no `[` or `]` (`ipv6`, unsupported). It is a host (`host`), optionally followed
  by `:` and a port (`port`): 1 to 5 digits, no leading zero, at most 65535.

Nothing is normalised. An accepted string is exactly the printed form of its parse (`parse_render`),
so it has a single reading, and nothing between `//` and the first `/`, `?` or `#` is an `@`
(`parse_no_userinfo`). Whether the WHATWG parser agrees on that reading for every accepted string is
tested, not proven.
-/

namespace UrlFence

inductive Scheme where
  | http
  | https
  deriving DecidableEq, Repr

/-- The scheme with `://`. -/
def Scheme.pre : Scheme → List Char
  | .http => ['h', 't', 't', 'p', ':', '/', '/']
  | .https => ['h', 't', 't', 'p', 's', ':', '/', '/']

/-- Why a URL was refused. -/
inductive Reason where
  | chars
  | scheme
  | userinfo
  | percent
  | ipv6
  | port
  | host
  deriving DecidableEq, Repr

structure Url where
  scheme : Scheme
  host : Host
  /-- The port as written, if any. -/
  port : Option (List Char)
  /-- Path, query and fragment as written: empty, or starting with `/`, `?` or `#`. -/
  rest : List Char
  deriving DecidableEq, Repr

/-- Printable ASCII other than space and backslash. -/
def okChar (c : Char) : Bool := '!' ≤ c && c ≤ '~' && c ≠ '\\'

/-- The characters that end the authority. -/
def isDelim (c : Char) : Bool := c = '/' || c = '?' || c = '#'

def portOk (p : List Char) : Bool :=
  0 < p.length && p.length ≤ 5 && p.all isDigit && (p.length = 1 || p.head? != some '0') &&
    decValue p ≤ 65535

def parseScheme : List Char → Option (Scheme × List Char)
  | 'h' :: 't' :: 't' :: 'p' :: 's' :: ':' :: '/' :: '/' :: r => some (.https, r)
  | 'h' :: 't' :: 't' :: 'p' :: ':' :: '/' :: '/' :: r => some (.http, r)
  | _ => none

/-- Split the authority into the host and the port, if any. -/
def splitPort (a : List Char) : Option (List Char × Option (List Char)) :=
  match split ':' a with
  | [h] => some (h, none)
  | [h, p] => if portOk p then some (h, some p) else none
  | _ => none

/-- Parse a URL written in the strict form. -/
def parse (s : List Char) : Except Reason Url :=
  if !s.all okChar then .error .chars else
  match parseScheme s with
  | none => .error .scheme
  | some (sc, r) =>
    let auth := r.takeWhile (fun c => !isDelim c)
    if '@' ∈ auth then .error .userinfo
    else if '%' ∈ auth then .error .percent
    else if '[' ∈ auth ∨ ']' ∈ auth then .error .ipv6
    else match splitPort auth with
      | none => .error .port
      | some (hs, port) =>
        match parseHost hs with
        | none => .error .host
        | some h => .ok { scheme := sc, host := h, port, rest := r.dropWhile (fun c => !isDelim c) }

/-- The written port, with its `:`. -/
def portPart : Option (List Char) → List Char
  | none => []
  | some p => ':' :: p

/-- Print a URL. -/
def Url.render (u : Url) : List Char := u.scheme.pre ++ u.host.render ++ portPart u.port ++ u.rest

theorem parseScheme_spec (s r : List Char) (sc : Scheme) (h : parseScheme s = some (sc, r)) :
    s = sc.pre ++ r := by
  unfold parseScheme at h
  split at h <;> (try injection h with h; injection h with h1 h2; subst h1; subst h2; rfl)
  all_goals simp at h

theorem splitPort_spec (a h : List Char) (p : Option (List Char)) (hs : splitPort a = some (h, p)) :
    a = h ++ portPart p := by
  have hj := join_split ':' a
  unfold splitPort at hs
  split at hs
  · rename_i heq
    injection hs with hs; injection hs with h1 h2; subst h1; subst h2
    rw [heq] at hj; simpa [join, portPart] using hj.symm
  · rename_i hh pp heq
    split at hs
    · injection hs with hs; injection hs with h1 h2; subst h1; subst h2
      rw [heq] at hj; simpa [join, portPart] using hj.symm
    · exact absurd hs (by simp)
  · exact absurd hs (by simp)

/-- An accepted string is exactly the printed form of its parse. -/
theorem parse_render (s : List Char) (u : Url) (h : parse s = .ok u) : u.render = s := by
  unfold parse at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i sc r hsc
      simp only at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · rename_i hs port hsp
              split at h
              · exact absurd h (by simp)
              · rename_i host hh
                injection h with h; subst h
                rw [parseScheme_spec s r sc hsc]
                simp only [Url.render, parseHost_render hs host hh]
                rw [List.append_assoc, List.append_assoc, ← List.append_assoc hs, ← splitPort_spec _ _ _ hsp,
                  List.takeWhile_append_dropWhile]

/-- An accepted URL has a valid host. -/
theorem parse_valid (s : List Char) (u : Url) (h : parse s = .ok u) : u.host.Valid := by
  unfold parse at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · rename_i hs port hsp
              split at h
              · exact absurd h (by simp)
              · rename_i host hh
                injection h with h; subst h
                exact parseHost_valid hs host hh

/-- In an accepted URL, nothing before the first `/`, `?` or `#` after the scheme is an `@`: there is
no userinfo to mistake for the host. -/
theorem parse_no_userinfo (s : List Char) (u : Url) (h : parse s = .ok u) :
    '@' ∉ (s.drop u.scheme.pre.length).takeWhile (fun c => !isDelim c) := by
  have hr := parse_render s u h
  unfold parse at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i sc r hsc
      simp only at h
      split at h
      · exact absurd h (by simp)
      · rename_i hat
        split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · split at h
              · exact absurd h (by simp)
              · injection h with h; subst h
                show '@' ∉ (s.drop sc.pre.length).takeWhile (fun c => !isDelim c)
                rw [parseScheme_spec s r sc hsc, List.drop_left]
                exact hat

end UrlFence
