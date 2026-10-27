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

/-- A DNS label: 1 to 63 lowercase letters, digits and hyphens, not starting or ending with `-`, and
not an IDNA A-label (`xn--…`), which WHATWG parsers decode and may reject. -/
def labelOk (l : List Char) : Bool :=
  0 < l.length && l.length ≤ 63 && l.all isLDH && l.head? != some '-' && l.getLast? != some '-' &&
    l.take 4 != ['x', 'n', '-', '-']

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

theorem labelOk_ldh (l : List Char) (h : labelOk l = true) : ∀ c ∈ l, isLDH c = true := by
  simp only [labelOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1.1.2

theorem labelOk_noDot (l : List Char) (h : labelOk l = true) : '.' ∉ l := by
  intro hm
  have := labelOk_ldh l h '.' hm
  simp [isLDH, isLower, isDigit] at this

/-- The labels of a valid domain contain no dot. -/
theorem domainOk_noDot (ls : List (List Char)) (h : domainOk ls = true) : ∀ l ∈ ls, '.' ∉ l := by
  intro l hl
  simp only [domainOk, Bool.and_eq_true, List.all_eq_true] at h
  exact labelOk_noDot l (h.1.1.2 l hl)

theorem domainOk_ne_nil (ls : List (List Char)) (h : domainOk ls = true) : ls ≠ [] := by
  rintro rfl; simp [domainOk] at h

/-- A parsed host is made of lowercase letters, digits, `-` and `.` only, so it contains none of the
characters that end or split an authority (`/`, `?`, `#`, `:`, `@`, `[`, `]`). -/
theorem parseHost_chars (s : List Char) (h : Host) (hp : parseHost s = some h) :
    ∀ c ∈ h.render, ('a' ≤ c ∧ c ≤ 'z') ∨ ('0' ≤ c ∧ c ≤ '9') ∨ c = '-' ∨ c = '.' := by
  rw [parseHost_render s h hp]
  unfold parseHost at hp
  split at hp
  · rename_i hall
    intro c hc
    have := List.all_eq_true.mp hall c hc
    simp only [isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with ⟨h1, h2⟩ | h3
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr (Or.inr h3))
  · split at hp
    · rename_i hdom
      intro c hc
      rw [← join_split '.' s] at hc
      rcases mem_join '.' _ c hc with h | ⟨q, hq, hcq⟩
      · exact Or.inr (Or.inr (Or.inr h))
      · simp only [domainOk, Bool.and_eq_true, List.all_eq_true] at hdom
        have := labelOk_ldh q (hdom.1.1.2 q hq) c hcq
        simp only [isLDH, isLower, isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
        rcases this with (⟨h1, h2⟩ | ⟨h1, h2⟩) | h3
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr (Or.inl h3))
    · exact absurd hp (by simp)

end UrlFence
