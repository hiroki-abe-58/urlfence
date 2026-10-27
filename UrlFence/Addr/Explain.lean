import UrlFence.Addr.Check

/-!
# Why an address is denied, and prefixes as text

`Config.explain` names the first rule that denies an address, in the order in which `allows4` and
`allows6` apply them, and gives `none` exactly when the address is allowed (`explain_eq_none_iff`).
The command-line tool prints its decisions from `Config.check` and takes only the reason from here.

`parsePrefix` reads a CIDR block such as `10.0.0.0/8` or `64:ff9b::/96` strictly: an address as
`parse` reads it, `/`, and a decimal length without leading zeros, at most the address width; no bit
of the address after the length may be set (`parsePrefix_v4`, `parsePrefix_v6`).
-/

namespace UrlFence.Addr

/-- The rule that denies an address. -/
inductive Why where
  /-- In a row of the IPv4 registry that is not globally reachable. -/
  | row4 (r : Row 32)
  /-- In 224.0.0.0/4. -/
  | multicast
  /-- In an IPv4 prefix the caller denies. -/
  | deny4 (p : Prefix 32)
  /-- In an IPv6 prefix the caller denies. -/
  | deny6 (p : Prefix 128)
  /-- IPv4-mapped, and the IPv4 address is denied. -/
  | mapped (v : BitVec 32) (w : Why)
  /-- In an honoured NAT64 prefix, and the IPv4 address is denied. -/
  | nat64 (v : BitVec 32) (w : Why)
  /-- Outside 2000::/3, and it carries no IPv4 address. -/
  | outside
  /-- In a row of the IPv6 registry that is not globally reachable. -/
  | row6 (r : Row 128)
  /-- An ISATAP interface identifier, and its IPv4 address is denied. -/
  | isatap (v : BitVec 32) (w : Why)
  deriving Repr

def Config.explain4 (cfg : Config) (v : BitVec 32) : Option Why :=
  match ipv4Registry.find? (fun r => r.reachable != .yes && r.block.contains v) with
  | some r => some (.row4 r)
  | none =>
    if multicast4.contains v then some .multicast
    else (cfg.deny4.find? (·.contains v)).map .deny4

def Config.explain6 (cfg : Config) (a : BitVec 128) : Option Why :=
  match cfg.deny6.find? (·.contains a) with
  | some p => some (.deny6 p)
  | none =>
    if cfg.embeds a then
      (cfg.explain4 (low32 a)).map (if mapped96.contains a then .mapped (low32 a) else .nat64 (low32 a))
    else if !global6.contains a then some .outside
    else
      match ipv6Registry.find? (fun r => r.reachable != .yes && r.block.contains a) with
      | some r => some (.row6 r)
      | none => if isatapId a then (cfg.explain4 (low32 a)).map (.isatap (low32 a)) else none

/-- The first rule that denies the address, if any. -/
def Config.explain (cfg : Config) : Addr → Option Why
  | .v4 v => cfg.explain4 v
  | .v6 a => cfg.explain6 a

theorem find?_eq_none_iff_any {α : Type} (l : List α) (p : α → Bool) :
    l.find? p = none ↔ l.any p = false := by
  rw [List.find?_eq_none, List.any_eq_false]

theorem any_of_find?_eq_some {α : Type} {l : List α} {p : α → Bool} {x : α} (h : l.find? p = some x) :
    l.any p = true :=
  List.any_eq_true.mpr ⟨x, List.mem_of_find?_eq_some h, List.find?_some h⟩

theorem explain4_eq_none_iff (cfg : Config) (v : BitVec 32) :
    cfg.explain4 v = none ↔ cfg.allows4 v = true := by
  unfold Config.explain4 Config.allows4 unreachable4
  cases h : ipv4Registry.find? (fun r => r.reachable != .yes && r.block.contains v) with
  | some r => simp [any_of_find?_eq_some h]
  | none =>
    rw [(find?_eq_none_iff_any _ _).mp h]
    cases multicast4.contains v <;>
      simp [Option.map_eq_none_iff]

theorem explain6_eq_none_iff (cfg : Config) (a : BitVec 128) :
    cfg.explain6 a = none ↔ cfg.allows6 a = true := by
  unfold Config.explain6 Config.allows6 unreachable6
  cases h : cfg.deny6.find? (·.contains a) with
  | some p => simp [any_of_find?_eq_some h]
  | none =>
    rw [(find?_eq_none_iff_any _ _).mp h]
    simp only [Bool.not_false, Bool.true_and]
    cases cfg.embeds a
    · cases hg : global6.contains a
      · simp
      · cases hr : ipv6Registry.find? (fun r => r.reachable != .yes && r.block.contains a) with
        | some r => simp [any_of_find?_eq_some hr]
        | none =>
          rw [(find?_eq_none_iff_any _ _).mp hr]
          cases isatapId a <;> simp [Option.map_eq_none_iff, explain4_eq_none_iff]
    · simp [Option.map_eq_none_iff, explain4_eq_none_iff]

/-- `explain` names a rule exactly when the address is denied. -/
theorem explain_eq_none_iff (cfg : Config) (a : Addr) : cfg.explain a = none ↔ cfg.allows a = true := by
  cases a with
  | v4 v => exact explain4_eq_none_iff cfg v
  | v6 a => exact explain6_eq_none_iff cfg a

/-! ## Prefixes as text -/

/-- A prefix of either family. -/
inductive AnyPrefix where
  | v4 (p : Prefix 32)
  | v6 (p : Prefix 128)
  deriving DecidableEq, Repr

/-- A decimal number without leading zeros, of 1 to 3 digits. -/
def lengthOk (l : List Char) : Bool :=
  0 < l.length && l.length ≤ 3 && l.all isDigit && (l.length = 1 || l.head? != some '0')

/-- Parse a CIDR block `ADDRESS/LENGTH` in the strict form. -/
def parsePrefix (s : List Char) : Option AnyPrefix :=
  match split '/' s with
  | [a, l] =>
    if lengthOk l then
      match parse a with
      | some (.v4 b) =>
        if decValue l ≤ 32 ∧ b.toNat % 2 ^ (32 - decValue l) = 0 then some (.v4 ⟨b, decValue l⟩) else none
      | some (.v6 b) =>
        if decValue l ≤ 128 ∧ b.toNat % 2 ^ (128 - decValue l) = 0 then some (.v6 ⟨b, decValue l⟩)
        else none
      | none => none
    else none
  | _ => none

/-- A parsed IPv4 prefix is a CIDR block. -/
theorem parsePrefix_v4 (s : List Char) (p : Prefix 32) (h : parsePrefix s = some (.v4 p)) :
    p.len ≤ 32 ∧ p.base.toNat % 2 ^ (32 - p.len) = 0 := by
  unfold parsePrefix at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i hc
          injection h with h
          injection h with h
          subst h
          exact hc
        · cases h
      · split at h <;> cases h
      · cases h
    · cases h
  · cases h

/-- A parsed IPv6 prefix is a CIDR block. -/
theorem parsePrefix_v6 (s : List Char) (p : Prefix 128) (h : parsePrefix s = some (.v6 p)) :
    p.len ≤ 128 ∧ p.base.toNat % 2 ^ (128 - p.len) = 0 := by
  unfold parsePrefix at h
  split at h
  · split at h
    · split at h
      · split at h <;> cases h
      · split at h
        · rename_i hc
          injection h with h
          injection h with h
          subst h
          exact hc
        · cases h
      · cases h
    · cases h
  · cases h

def prefixText4 (p : Prefix 32) : String := (Addr.v4 p.base).toString ++ "/" ++ Nat.repr p.len

def prefixText6 (p : Prefix 128) : String := (Addr.v6 p.base).toString ++ "/" ++ Nat.repr p.len

/-- The reason as one line of text. -/
def Why.text : Why → String
  | .row4 r => "registry " ++ prefixText4 r.block ++ " " ++ r.name
  | .multicast => "multicast 224.0.0.0/4"
  | .deny4 p => "deny " ++ prefixText4 p
  | .deny6 p => "deny " ++ prefixText6 p
  | .mapped v w => "mapped " ++ (Addr.v4 v).toString ++ ": " ++ w.text
  | .nat64 v w => "nat64-embedded " ++ (Addr.v4 v).toString ++ ": " ++ w.text
  | .outside => "outside 2000::/3"
  | .row6 r => "registry " ++ prefixText6 r.block ++ " " ++ r.name
  | .isatap v w => "isatap " ++ (Addr.v4 v).toString ++ ": " ++ w.text

def parsePrefixString (s : String) : Option AnyPrefix := parsePrefix s.toList

end UrlFence.Addr
