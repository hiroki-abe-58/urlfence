import UrlFence.Url

/-!
# Policies

A pattern names one host exactly, or every strict subdomain of a domain (`*.example.com`: it matches
`docs.example.com` and `a.b.example.com`, but not `example.com`, `attacker-example.com` or
`example.com.evil.net`). Matching is label by label (`sub_matches_iff`). On the printed host it is
the same as a suffix test that includes the dot (`sub_matches_iff_render`), which is the correct form
of the string checks that failed in the advisories listed in the README. A subdomain pattern never
matches an IPv4 address (`sub_not_ipv4`).

`Policy.check` allows a URL exactly when it parses, its scheme is allowed, its host matches some
allowed pattern, and it matches no denied pattern (`check_allow_iff`).
-/

namespace UrlFence

inductive Pattern where
  /-- Exactly this host. -/
  | exact (h : Host)
  /-- Every strict subdomain of this domain. -/
  | sub (d : List (List Char))
  deriving DecidableEq, Repr

def Pattern.matches : Pattern → Host → Bool
  | .exact h', h => decide (h' = h)
  | .sub d, .domain ls => !d.isEmpty && decide (d.length < ls.length) && d.isSuffixOf ls
  | .sub _, .ipv4 _ => false

/-- An exact pattern matches exactly its own host. -/
theorem exact_matches_iff (h' h : Host) : (Pattern.exact h').matches h = true ↔ h' = h := by
  simp [Pattern.matches]

theorem sub_not_ipv4 (d ps : List (List Char)) : (Pattern.sub d).matches (.ipv4 ps) = false := rfl

/-- A subdomain pattern matches exactly the domains that add at least one label in front of a
non-empty domain. (`.sub []`, which `parsePattern` never produces, matches nothing.) -/
theorem sub_matches_iff (d ls : List (List Char)) :
    (Pattern.sub d).matches (.domain ls) = true ↔ d ≠ [] ∧ ∃ pre, pre ≠ [] ∧ ls = pre ++ d := by
  simp only [Pattern.matches, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    decide_eq_true_eq, List.isSuffixOf_iff_suffix]
  constructor
  · rintro ⟨⟨hd, hlen⟩, pre, rfl⟩
    refine ⟨hd, pre, ?_, rfl⟩
    rintro rfl; simp at hlen
  · rintro ⟨hd, pre, hpre, rfl⟩
    refine ⟨⟨hd, ?_⟩, ⟨pre, rfl⟩⟩
    have : 0 < pre.length := List.length_pos_iff.mpr hpre
    simp; omega

/-- On printed domains, a subdomain pattern for `d` matches exactly when the host ends with `.`
followed by `d`. Without the dot, `attacker-example.com` would match `example.com`. -/
theorem sub_matches_iff_render (d ls : List (List Char)) (hd : domainOk d = true) (hl : domainOk ls = true) :
    (Pattern.sub d).matches (.domain ls) = true ↔ ('.' :: join '.' d) <:+ join '.' ls := by
  have hdne := domainOk_ne_nil d hd
  rw [sub_matches_iff, and_iff_right hdne]
  constructor
  · rintro ⟨pre, hpre, rfl⟩
    refine ⟨join '.' pre, ?_⟩
    rw [join_append '.' pre d hpre hdne]
  · rintro ⟨t, ht⟩
    refine ⟨split '.' t, split_ne_nil '.' t, ?_⟩
    have := congrArg (split '.') ht
    rw [split_append_sep, split_join '.' d hdne (domainOk_noDot d hd),
      split_join '.' ls (domainOk_ne_nil ls hl) (domainOk_noDot ls hl)] at this
    exact this.symm

/-- An access policy for URLs. -/
structure Policy where
  /-- Schemes that may be used. -/
  schemes : List Scheme
  /-- Hosts that may be requested. -/
  allow : List Pattern
  /-- Hosts that may not be requested, even if allowed. -/
  deny : List Pattern

inductive Decision where
  /-- Allowed; the parsed URL. -/
  | allow (u : Url)
  /-- Parsed, but the scheme or host is not allowed. -/
  | deny (u : Url)
  /-- Refused before any pattern was consulted. -/
  | reject (r : Reason)
  deriving DecidableEq, Repr

def Policy.check (pol : Policy) (s : List Char) : Decision :=
  match parse s with
  | .error r => .reject r
  | .ok u =>
    if pol.schemes.contains u.scheme && pol.allow.any (·.matches u.host) && !pol.deny.any (·.matches u.host)
    then .allow u else .deny u

/-- `check` allows `u` exactly when `s` parses to `u`, its scheme is allowed, its host matches an
allowed pattern, and it matches no denied pattern. -/
theorem check_allow_iff (pol : Policy) (s : List Char) (u : Url) :
    pol.check s = .allow u ↔
      parse s = .ok u ∧ u.scheme ∈ pol.schemes ∧ (∃ p ∈ pol.allow, p.matches u.host = true) ∧
        ∀ p ∈ pol.deny, p.matches u.host = false := by
  unfold Policy.check
  cases hp : parse s with
  | error r => simp
  | ok v =>
    simp only [Except.ok.injEq]
    by_cases hc : pol.schemes.contains v.scheme && pol.allow.any (·.matches v.host) &&
        !pol.deny.any (·.matches v.host)
    · rw [ite_eq_left hc]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_true,
        List.any_eq_false, List.contains_iff_mem] at hc
      simp only [Decision.allow.injEq]
      constructor
      · rintro rfl
        exact ⟨rfl, hc.1.1, hc.1.2, fun p hp => by simpa using hc.2 p hp⟩
      · rintro ⟨rfl, -⟩; rfl
    · rw [ite_eq_right hc]
      simp only [reduceCtorEq, false_iff]
      rintro ⟨rfl, hs, ⟨p, hpa, hpm⟩, hd⟩
      apply hc
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_true,
        List.any_eq_false, List.contains_iff_mem]
      exact ⟨⟨hs, p, hpa, hpm⟩, fun q hq => by simp [hd q hq]⟩

/-- Adding a denied pattern never allows more. -/
theorem check_allow_of_add_deny (pol : Policy) (q : Pattern) (s : List Char) (u : Url)
    (h : ({ pol with deny := q :: pol.deny } : Policy).check s = .allow u) : pol.check s = .allow u := by
  rw [check_allow_iff] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, fun p hp => h.2.2.2 p (by simp [hp])⟩

end UrlFence
