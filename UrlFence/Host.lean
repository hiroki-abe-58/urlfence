import UrlFence.Split

/-!
# Hosts

A host is accepted in only two written forms, and refused otherwise:

* a **domain**: lowercase labels of letters, digits and hyphens (1 to 63 characters, not starting
  or ending with a hyphen), separated by single dots, at most 253 characters in all, whose last
  label does not look like a number. The WHATWG URL parser reads a host whose last label is all
  digits, or `0x` followed by hex digits, as an IPv4 address, so such hosts are not domains here;
* an **IPv4 address** in dotted-decimal form: four parts `0` to `255`, without leading zeros. The
  WHATWG parser also reads `127.1`, `0x7f.0.0.1` and `017.0.0.1` (octal) as IPv4 addresses; those
  forms are refused.

IPv6 literals, uppercase letters, non-ASCII names and anything else are refused. `parseHost` keeps the
written form: printing the result gives back the input (`parseHost_render`).
-/

namespace UrlFence

def isLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isHexDigit (c : Char) : Bool := isDigit c || ('a' ≤ c && c ≤ 'f')
def isLDH (c : Char) : Bool := isLower c || isDigit c || c = '-'

/-- The value of a string of decimal digits. -/
def decValue (l : List Char) : Nat := l.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- A DNS label: 1 to 63 lowercase letters, digits and hyphens, not starting or ending with `-`. -/
def labelOk (l : List Char) : Bool :=
  0 < l.length && l.length ≤ 63 && l.all isLDH && l.head? != some '-' && l.getLast? != some '-'

/-- What the WHATWG parser takes for an IPv4 number when it is the last label. -/
def numberLike (l : List Char) : Bool :=
  l.all isDigit || (match l with | '0' :: 'x' :: rest => rest.all isHexDigit | _ => false)

def domainOk (ls : List (List Char)) : Bool :=
  !ls.isEmpty && ls.all labelOk && (join '.' ls).length ≤ 253 &&
    match ls.getLast? with
    | some l => !numberLike l
    | none => false

/-- One part of a dotted-decimal IPv4 address: `0` to `255`, no leading zero. -/
def octetOk (l : List Char) : Bool :=
  0 < l.length && l.length ≤ 3 && l.all isDigit && (l.length = 1 || l.head? != some '0') &&
    decValue l ≤ 255

def ipv4Ok (ps : List (List Char)) : Bool := ps.length = 4 && ps.all octetOk

/-- A host, as written. -/
inductive Host where
  /-- A domain name, as its labels. -/
  | domain (labels : List (List Char))
  /-- An IPv4 address, as its four dotted-decimal parts. -/
  | ipv4 (parts : List (List Char))
  deriving DecidableEq, Repr

/-- Print a host. -/
def Host.render : Host → List Char
  | .domain ls => join '.' ls
  | .ipv4 ps => join '.' ps

/-- Parse a host written in one of the accepted forms. -/
def parseHost (s : List Char) : Option Host :=
  if s.all (fun c => isDigit c || c = '.') then
    if ipv4Ok (split '.' s) then some (.ipv4 (split '.' s)) else none
  else if domainOk (split '.' s) then some (.domain (split '.' s)) else none

/-- A host is valid when it is in one of the accepted forms. -/
def Host.Valid : Host → Prop
  | .domain ls => domainOk ls = true
  | .ipv4 ps => ipv4Ok ps = true

/-- Printing a parsed host gives back exactly the input. -/
theorem parseHost_render (s : List Char) (h : Host) (hp : parseHost s = some h) : h.render = s := by
  unfold parseHost at hp
  split at hp
  · split at hp
    · injection hp with hp; subst hp; exact join_split '.' s
    · exact absurd hp (by simp)
  · split at hp
    · injection hp with hp; subst hp; exact join_split '.' s
    · exact absurd hp (by simp)

/-- A parsed host is valid. -/
theorem parseHost_valid (s : List Char) (h : Host) (hp : parseHost s = some h) : h.Valid := by
  unfold parseHost at hp
  split at hp
  · split at hp
    · rename_i hv; injection hp with hp; subst hp; exact hv
    · exact absurd hp (by simp)
  · split at hp
    · rename_i hv; injection hp with hp; subst hp; exact hv
    · exact absurd hp (by simp)

theorem labelOk_noDot (l : List Char) (h : labelOk l = true) : '.' ∉ l := by
  intro hm
  simp only [labelOk, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.1.2 '.' hm
  simp [isLDH, isLower, isDigit] at this

/-- The labels of a valid domain contain no dot. -/
theorem domainOk_noDot (ls : List (List Char)) (h : domainOk ls = true) : ∀ l ∈ ls, '.' ∉ l := by
  intro l hl
  simp only [domainOk, Bool.and_eq_true, List.all_eq_true] at h
  exact labelOk_noDot l (h.1.1.2 l hl)

theorem domainOk_ne_nil (ls : List (List Char)) (h : domainOk ls = true) : ls ≠ [] := by
  rintro rfl; simp [domainOk] at h

end UrlFence
