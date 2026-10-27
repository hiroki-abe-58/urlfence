import UrlFence.Addr.Text

/-!
# Checking a resolved address

URLFence decides which host names may be requested; a name that is allowed can still resolve to an
internal address. `Config.check` decides whether a resolved address may be connected to.

* **IPv4**: denied if it is in a row of the IPv4 registry whose "Globally Reachable" value is not
  `True` (`False`, `N/A` or empty), in 224.0.0.0/4 (multicast), or in a prefix the caller denies.
  A row that is not globally reachable denies all of its block, even where a more specific row says
  `True`: all of 192.0.0.0/24 is denied, including 192.0.0.9 and 192.0.0.10. This is stricter than
  the registry, on purpose: those anycast addresses (PCP 192.0.0.9 and 2001:1::1, TURN 192.0.0.10
  and 2001:1::2, SRP 2001:1::3 in 2001::/23 below) are answered by the local gateway or border
  routers, which a request made for an agent should not reach.
* **IPv6 that carries an IPv4 address in its last 32 bits** (`Config.embeds`): IPv4-mapped
  addresses (`::ffff:0:0/96`), and the NAT64 /96 prefixes that the caller configures
  (`Config.nat64`, for example the well-known `64:ff9b::/96`). Such an address gets the decision of
  the IPv4 address it carries. A configured NAT64 prefix is honoured only if it is `64:ff9b::/96`,
  or a /96 inside 2000::/3 that has no address in common with a row that is not globally reachable
  (`nat64Ok`). Other configured prefixes are not honoured, and their addresses are denied: they are
  outside 2000::/3 or in such a row (in `::ffff:0:0/96` they are decided as IPv4-mapped). The
  command-line tool refuses such a prefix rather than ignoring it.
* **Other IPv6**: allowed only inside 2000::/3, and denied there if it is in a row of the IPv6
  registry that is not globally reachable (all of 2001::/23 including Teredo, 2001:db8::/32,
  2002::/16 for 6to4, 3fff::/20), if its interface identifier is an ISATAP one (`0000:5efe`, with
  the u and g bits of RFC 5214, section 6.1 allowed: `0100:5efe`, `0200:5efe`, `0300:5efe`; then an
  IPv4 address) whose IPv4 address is denied, or if it is in a prefix the caller denies. Everything
  outside 2000::/3 is therefore denied unless it carries an IPv4 address as above: `::/96`
  (IPv4-compatible), `64:ff9b:1::/48`, `100::/64`, `5f00::/16`, `fc00::/7`, `fe80::/10`,
  `fec0::/10`, `ff00::/8` and the rest.

A prefix the caller denies for IPv6 applies to every IPv6 address, including the mapped and NAT64
ones; one denied for IPv4 applies to every IPv4 address, including those carried in IPv6.

The decision is characterised exactly (`allows4_iff`, `allows6_iff`, `embeds_iff`, `nat64Ok_iff`,
`check_allow_iff`). Every address in a row that is not globally reachable is denied
(`registry4_denied`, `registry6_denied`; for IPv6 except `::ffff:0:0/96`, whose addresses get the
IPv4 decision). Configuring NAT64 prefixes allows nothing more than the well-known prefix with an
allowed IPv4 address in it, or what the generic IPv6 rule already allows (`allows_nat64_wellKnown`).
Denying another prefix never allows more (`allows_of_add_deny4`, `allows_of_add_deny6`).

**Which encodings of IPv4 in IPv6 are decoded.** Only these: IPv4-mapped (`mapped_denied`), the
configured /96 NAT64 prefixes (`nat64_denied`, `nat64_allows_iff`) and ISATAP interface identifiers
(`isatap_denied`); 6to4 and Teredo addresses are always denied (`sixToFour_denied`,
`teredo_denied`). Others are not decoded, and an address that uses one inside 2000::/3 is decided
as a plain global address: a network-specific NAT64 prefix that is not configured (RFC 6052,
section 3.1 forbids non-global IPv4 addresses only in the well-known prefix, so
`2a00:1450:64::a00:1`, carrying 10.0.0.1, is allowed), the RFC 6052 prefix lengths 32, 40, 48, 56
and 64 (which put the IPv4 address elsewhere and cannot be configured), 6rd, MAP-E and MAP-T, and
SIIT-EAM. A network that uses one of these must put its prefixes in `deny6`.

**What the registries do not know.** Internal services on global addresses are allowed unless the
caller denies them: a cloud provider's host endpoints (for example Azure's 168.63.129.16), an
organisation's own public IPv4 and IPv6 ranges. Put them in `deny4` and `deny6`. The tables are a
snapshot (2025-10-09): a block that IANA later adds as not globally reachable is allowed until the
tables are updated (see `data/README.md`).
-/

namespace UrlFence.Addr

/-- 224.0.0.0/4, IPv4 multicast (not in the special-purpose registry). -/
def multicast4 : Prefix 32 := ⟨ip4 224 0 0 0, 4⟩

/-- `::ffff:0:0/96`, IPv4-mapped addresses (RFC 4291). -/
def mapped96 : Prefix 128 := ⟨ip6 [0, 0, 0, 0, 0, 0xffff, 0, 0], 96⟩

/-- `64:ff9b::/96`, the well-known NAT64 prefix (RFC 6052). -/
def wellKnown96 : Prefix 128 := ⟨ip6 [0x64, 0xff9b, 0, 0, 0, 0, 0, 0], 96⟩

/-- `2000::/3`, global unicast (RFC 4291). -/
def global6 : Prefix 128 := ⟨ip6 [0x2000, 0, 0, 0, 0, 0, 0, 0], 3⟩

/-- The IPv4 address in the last 32 bits of an IPv6 address. -/
def low32 (a : BitVec 128) : BitVec 32 := a.setWidth 32

/-- An ISATAP interface identifier (RFC 5214, section 6.1): the 32 bits before the last 32 are
`0000:5efe`, except for the u and g bits (`000000ug` in the first octet), so also `0100:5efe`,
`0200:5efe` and `0300:5efe`. -/
def isatapId (a : BitVec 128) : Bool :=
  ((a >>> 32).setWidth 32 &&& 0xfcffffff#32) == 0x00005efe#32

/-- In the block of a row of the IPv4 registry that is not globally reachable. -/
def unreachable4 (v : BitVec 32) : Bool :=
  ipv4Registry.any fun r => r.reachable != .yes && r.block.contains v

/-- In the block of a row of the IPv6 registry that is not globally reachable. -/
def unreachable6 (a : BitVec 128) : Bool :=
  ipv6Registry.any fun r => r.reachable != .yes && r.block.contains a

/-- What the caller adds to the registries. -/
structure Config where
  /-- IPv4 prefixes to deny. -/
  deny4 : List (Prefix 32) := []
  /-- IPv6 prefixes to deny. -/
  deny6 : List (Prefix 128) := []
  /-- NAT64 prefixes in use (opt-in): the first 96 bits of each count. -/
  nat64 : List (BitVec 128) := []

/-- The decision for an IPv4 address. -/
def Config.allows4 (cfg : Config) (v : BitVec 32) : Bool :=
  !unreachable4 v && !multicast4.contains v && !cfg.deny4.any (·.contains v)

/-- A NAT64 prefix is honoured if it is `64:ff9b::/96`, or a /96 inside 2000::/3 that has no address
in common with a row that is not globally reachable. The addresses of a configured prefix that is
not honoured are denied (except in `::ffff:0:0/96`, decided as IPv4-mapped). -/
def nat64Ok (p : BitVec 128) : Bool :=
  wellKnown96.contains p ||
    (global6.contains p &&
      !ipv6Registry.any fun r => r.reachable != .yes && (Prefix.mk p 96).overlaps r.block)

/-- The address carries an IPv4 address in its last 32 bits: IPv4-mapped, or in an honoured NAT64
prefix. -/
def Config.embeds (cfg : Config) (a : BitVec 128) : Bool :=
  mapped96.contains a || cfg.nat64.any fun p => nat64Ok p && (Prefix.mk p 96).contains a

/-- The decision for an IPv6 address. -/
def Config.allows6 (cfg : Config) (a : BitVec 128) : Bool :=
  !cfg.deny6.any (·.contains a) &&
    (if cfg.embeds a then cfg.allows4 (low32 a)
     else global6.contains a && !unreachable6 a && !(isatapId a && !cfg.allows4 (low32 a)))

def Config.allows (cfg : Config) : Addr → Bool
  | .v4 v => cfg.allows4 v
  | .v6 a => cfg.allows6 a

/-- The decision for an address written as text. -/
inductive Verdict where
  /-- May be connected to; the parsed address. -/
  | allow (a : Addr)
  /-- Parsed, but may not be connected to. -/
  | deny (a : Addr)
  /-- Not an address in one of the accepted text forms. -/
  | reject
  deriving DecidableEq, Repr

def Config.check (cfg : Config) (s : List Char) : Verdict :=
  match parse s with
  | none => .reject
  | some a => if cfg.allows a then .allow a else .deny a

def Config.checkString (cfg : Config) (s : String) : Verdict := cfg.check s.toList

/-- The IPv4-mapped address of `v` (`::ffff:v`). -/
def mappedAddr (v : BitVec 32) : BitVec 128 := BitVec.ofNat 128 (0xffff * 2 ^ 32 + v.toNat)

/-- The address of `v` in the NAT64 prefix `p`/96 (RFC 6052): the first 96 bits of `p`, then `v`. -/
def nat64Addr (p : BitVec 128) (v : BitVec 32) : BitVec 128 :=
  BitVec.ofNat 128 (p.toNat / 2 ^ 32 * 2 ^ 32 + v.toNat)

/-- The ISATAP interface identifier with the u and g bits as given. -/
def isatapWord (u g : Bool) : Nat := (if u then 0x02000000 else 0) + (if g then 0x01000000 else 0) + 0x5efe

/-- An ISATAP address of `v` (RFC 5214): the first 64 bits of `p`, then `0000:5efe` with the u and g
bits as given, then `v`. -/
def isatapAddr (p : BitVec 128) (u g : Bool) (v : BitVec 32) : BitVec 128 :=
  BitVec.ofNat 128 (p.toNat / 2 ^ 64 * 2 ^ 64 + isatapWord u g * 2 ^ 32 + v.toNat)

/-! ## The decision, exactly -/

theorem allows4_iff (cfg : Config) (v : BitVec 32) :
    cfg.allows4 v = true ↔
      (∀ r ∈ ipv4Registry, r.reachable ≠ .yes → r.block.contains v = false) ∧
        multicast4.contains v = false ∧ ∀ p ∈ cfg.deny4, p.contains v = false := by
  simp [Config.allows4, unreachable4, and_assoc]

theorem embeds_iff (cfg : Config) (a : BitVec 128) :
    cfg.embeds a = true ↔
      mapped96.contains a = true ∨
        ∃ p ∈ cfg.nat64, nat64Ok p = true ∧ (Prefix.mk p 96).contains a = true := by
  simp [Config.embeds]

theorem nat64Ok_iff (p : BitVec 128) :
    nat64Ok p = true ↔
      wellKnown96.contains p = true ∨
        (global6.contains p = true ∧
          ∀ r ∈ ipv6Registry, r.reachable ≠ .yes → (Prefix.mk p 96).overlaps r.block = false) := by
  simp [nat64Ok]

theorem allows6_iff (cfg : Config) (a : BitVec 128) :
    cfg.allows6 a = true ↔
      (∀ p ∈ cfg.deny6, p.contains a = false) ∧
        (cfg.embeds a = true → cfg.allows4 (low32 a) = true) ∧
        (cfg.embeds a = false →
          global6.contains a = true ∧
            (∀ r ∈ ipv6Registry, r.reachable ≠ .yes → r.block.contains a = false) ∧
            (isatapId a = true → cfg.allows4 (low32 a) = true)) := by
  unfold Config.allows6
  cases cfg.embeds a <;> cases isatapId a <;> simp [unreachable6, and_assoc]

/-- `check` allows `a` exactly when the text parses to `a` and `a` is allowed. -/
theorem check_allow_iff (cfg : Config) (s : List Char) (a : Addr) :
    cfg.check s = .allow a ↔ parse s = some a ∧ cfg.allows a = true := by
  unfold Config.check
  cases parse s with
  | none => simp
  | some b =>
    simp only [Option.some.injEq]
    by_cases hb : cfg.allows b = true
    · rw [ite_eq_left hb]
      constructor
      · intro h
        cases h
        exact ⟨rfl, hb⟩
      · rintro ⟨rfl, -⟩
        rfl
    · rw [ite_eq_right hb]
      constructor
      · intro h
        cases h
      · rintro ⟨rfl, h⟩
        exact absurd h hb

/-! ## The registries -/

/-- Every address in a row of the IPv4 registry that is not globally reachable is denied. -/
theorem registry4_denied (cfg : Config) (r : Row 32) (hr : r ∈ ipv4Registry) (hg : r.reachable ≠ .yes)
    (v : BitVec 32) (hv : r.block.contains v = true) : cfg.allows (.v4 v) = false := by
  show cfg.allows4 v = false
  cases h : cfg.allows4 v
  · rfl
  · rw [((allows4_iff cfg v).mp h).1 r hr hg] at hv
    cases hv

/-- Every IPv4 multicast address is denied. -/
theorem multicast4_denied (cfg : Config) (v : BitVec 32) (hv : multicast4.contains v = true) :
    cfg.allows (.v4 v) = false := by
  show cfg.allows4 v = false
  cases h : cfg.allows4 v
  · rfl
  · rw [((allows4_iff cfg v).mp h).2.1] at hv
    cases hv

theorem unreachable6_not_mapped : ∀ r ∈ ipv6Registry, r.reachable ≠ .yes → r.block ≠ mapped96 →
    r.block.overlaps mapped96 = false := by
  decide +kernel

theorem unreachable6_not_wellKnown : ∀ r ∈ ipv6Registry, r.reachable ≠ .yes →
    wellKnown96.overlaps r.block = false := by
  decide +kernel

theorem unreachable6_long_not_global : ∀ r ∈ ipv6Registry, r.reachable ≠ .yes → 96 < r.block.len →
    global6.contains r.block.base = false := by
  decide +kernel

/-- Every address in a row of the IPv6 registry that is not globally reachable is denied, except
in `::ffff:0:0/96`, whose addresses get the decision of the IPv4 address they carry. -/
theorem registry6_denied (cfg : Config) (r : Row 128) (hr : r ∈ ipv6Registry) (hg : r.reachable ≠ .yes)
    (hm : r.block ≠ mapped96) (a : BitVec 128) (ha : r.block.contains a = true) :
    cfg.allows (.v6 a) = false := by
  show cfg.allows6 a = false
  cases h : cfg.allows6 a
  · rfl
  · exfalso
    obtain ⟨-, -, hgen⟩ := (allows6_iff cfg a).mp h
    cases he : cfg.embeds a
    · rw [(hgen he).2.1 r hr hg] at ha
      cases ha
    · rcases (embeds_iff cfg a).mp he with hmap | ⟨p, -, hok, hp⟩
      · have := Prefix.overlaps_of_contains ha hmap
        rw [unreachable6_not_mapped r hr hg hm] at this
        cases this
      · rcases (nat64Ok_iff p).mp hok with hw | ⟨-, hno⟩
        · have hwa : wellKnown96.contains a = true := by
            rw [Prefix.contains_congr hp (q := wellKnown96) (by simp [wellKnown96])]
            exact hw
          have := Prefix.overlaps_of_contains hwa ha
          rw [unreachable6_not_wellKnown r hr hg] at this
          cases this
        · have := Prefix.overlaps_of_contains hp ha
          rw [hno r hr hg] at this
          cases this

/-- Outside 2000::/3, an address that carries no IPv4 address is denied. -/
theorem outside_global_denied (cfg : Config) (a : BitVec 128) (hg : global6.contains a = false)
    (he : cfg.embeds a = false) : cfg.allows (.v6 a) = false := by
  show cfg.allows6 a = false
  cases h : cfg.allows6 a
  · rfl
  · rw [((allows6_iff cfg a).mp h).2.2 he |>.1] at hg
    cases hg

/-- `2002::/16`, 6to4 (RFC 3056). -/
def sixToFour : Prefix 128 := ⟨ip6 [0x2002, 0, 0, 0, 0, 0, 0, 0], 16⟩

/-- `2001::/32`, Teredo (RFC 4380). -/
def teredo : Prefix 128 := ⟨ip6 [0x2001, 0, 0, 0, 0, 0, 0, 0], 32⟩

/-- Every 6to4 address is denied. -/
theorem sixToFour_denied (cfg : Config) (a : BitVec 128) (ha : sixToFour.contains a = true) :
    cfg.allows (.v6 a) = false :=
  registry6_denied cfg (ipv6Registry[19]'(by decide)) (List.getElem_mem _) (by decide) (by decide) a ha

/-- Every Teredo address is denied. -/
theorem teredo_denied (cfg : Config) (a : BitVec 128) (ha : teredo.contains a = true) :
    cfg.allows (.v6 a) = false :=
  registry6_denied cfg (ipv6Registry[8]'(by decide)) (List.getElem_mem _) (by decide) (by decide) a ha

/-! ## IPv4 in IPv6 -/

theorem mappedAddr_spec (v : BitVec 32) :
    mapped96.contains (mappedAddr v) = true ∧ low32 (mappedAddr v) = v := by
  have hv := v.isLt
  have hb : mapped96.base.toNat = 0xffff * 2 ^ 32 := by decide
  constructor
  · rw [Prefix.contains_iff, hb]
    simp only [mappedAddr, BitVec.toNat_ofNat] at hv ⊢
    show (0xffff * 2 ^ 32 + v.toNat) % 2 ^ 128 / 2 ^ 32 = 0xffff * 2 ^ 32 / 2 ^ 32
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [low32, mappedAddr, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hv ⊢
    omega

theorem nat64Addr_spec (p : BitVec 128) (v : BitVec 32) :
    (Prefix.mk p 96).contains (nat64Addr p v) = true ∧ low32 (nat64Addr p v) = v := by
  have hp := p.isLt
  have hv := v.isLt
  constructor
  · rw [Prefix.contains_iff]
    simp only [nat64Addr, BitVec.toNat_ofNat] at hp hv ⊢
    show (p.toNat / 2 ^ 32 * 2 ^ 32 + v.toNat) % 2 ^ 128 / 2 ^ 32 = p.toNat / 2 ^ 32
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [low32, nat64Addr, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hp hv ⊢
    omega

theorem isatapWord_lt (u g : Bool) : isatapWord u g < 2 ^ 32 := by
  cases u <;> cases g <;> decide

theorem isatapAddr_spec (p : BitVec 128) (u g : Bool) (v : BitVec 32) :
    isatapId (isatapAddr p u g v) = true ∧ low32 (isatapAddr p u g v) = v := by
  have hp := p.isLt
  have hv := v.isLt
  have hw := isatapWord_lt u g
  generalize hwd : isatapWord u g = w at hw
  constructor
  · have : (isatapAddr p u g v >>> 32).setWidth 32 = BitVec.ofNat 32 (isatapWord u g) := by
      apply BitVec.eq_of_toNat_eq
      simp only [isatapAddr, hwd, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat] at hp hv hw ⊢
      omega
    rw [isatapId, this]
    cases u <;> cases g <;> decide
  · apply BitVec.eq_of_toNat_eq
    simp only [low32, isatapAddr, hwd, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hp hv hw ⊢
    omega

/-- An IPv4-mapped address is allowed exactly when its IPv4 address is, and no denied IPv6 prefix
contains it. -/
theorem mapped_allows_iff (cfg : Config) (v : BitVec 32) :
    cfg.allows (.v6 (mappedAddr v)) = true ↔
      cfg.allows (.v4 v) = true ∧ ∀ q ∈ cfg.deny6, q.contains (mappedAddr v) = false := by
  obtain ⟨hc, hl⟩ := mappedAddr_spec v
  have he : cfg.embeds (mappedAddr v) = true := (embeds_iff cfg _).mpr (Or.inl hc)
  show cfg.allows6 _ = true ↔ cfg.allows4 v = true ∧ _
  rw [allows6_iff, hl]
  constructor
  · rintro ⟨hd, he', -⟩
    exact ⟨he' he, hd⟩
  · rintro ⟨h4, hd⟩
    refine ⟨hd, fun _ => h4, fun hf => ?_⟩
    rw [he] at hf
    cases hf

/-- The IPv4-mapped address of a denied IPv4 address is denied. -/
theorem mapped_denied (cfg : Config) (v : BitVec 32) (hv : cfg.allows (.v4 v) = false) :
    cfg.allows (.v6 (mappedAddr v)) = false := by
  cases h : cfg.allows (.v6 (mappedAddr v))
  · rfl
  · rw [((mapped_allows_iff cfg v).mp h).1] at hv
    cases hv

/-- In an honoured configured NAT64 prefix, an address is allowed exactly when its IPv4 address is,
and no denied IPv6 prefix contains it. -/
theorem nat64_allows_iff (cfg : Config) (p : BitVec 128) (hp : p ∈ cfg.nat64) (hok : nat64Ok p = true)
    (v : BitVec 32) :
    cfg.allows (.v6 (nat64Addr p v)) = true ↔
      cfg.allows (.v4 v) = true ∧ ∀ q ∈ cfg.deny6, q.contains (nat64Addr p v) = false := by
  obtain ⟨hc, hl⟩ := nat64Addr_spec p v
  have he : cfg.embeds (nat64Addr p v) = true := (embeds_iff cfg _).mpr (Or.inr ⟨p, hp, hok, hc⟩)
  show cfg.allows6 _ = true ↔ cfg.allows4 v = true ∧ _
  rw [allows6_iff, hl]
  constructor
  · rintro ⟨hd, he', -⟩
    exact ⟨he' he, hd⟩
  · rintro ⟨h4, hd⟩
    refine ⟨hd, fun _ => h4, fun hf => ?_⟩
    rw [he] at hf
    cases hf

/-- In any configured NAT64 prefix, honoured or not, the address of a denied IPv4 address is
denied. -/
theorem nat64_denied (cfg : Config) (p : BitVec 128) (hp : p ∈ cfg.nat64) (v : BitVec 32)
    (hv : cfg.allows (.v4 v) = false) : cfg.allows (.v6 (nat64Addr p v)) = false := by
  change cfg.allows4 v = false at hv
  show cfg.allows6 _ = false
  obtain ⟨hc, hl⟩ := nat64Addr_spec p v
  cases h : cfg.allows6 (nat64Addr p v)
  · rfl
  · exfalso
    obtain ⟨-, hemb, hgen⟩ := (allows6_iff cfg _).mp h
    cases he : cfg.embeds (nat64Addr p v)
    · have hok : nat64Ok p = false := by
        cases hk : nat64Ok p
        · rfl
        · have := (embeds_iff cfg _).mpr (Or.inr ⟨p, hp, hk, hc⟩)
          rw [he] at this
          cases this
      obtain ⟨hglob, hreg, -⟩ := hgen he
      have hglobp : global6.contains p = true := by
        rw [← Prefix.contains_congr hc (q := global6) (by simp [global6])]
        exact hglob
      have hall : ∀ r ∈ ipv6Registry, r.reachable ≠ .yes → (Prefix.mk p 96).overlaps r.block = false := by
        intro r hr hg
        cases ho : (Prefix.mk p 96).overlaps r.block
        · rfl
        · exfalso
          by_cases hlen : r.block.len ≤ 96
          · have := Prefix.contains_of_overlaps ho hlen hc
            rw [hreg r hr hg] at this
            cases this
          · have hcb : (Prefix.mk p 96).contains r.block.base = true := by
              unfold Prefix.overlaps at ho
              rw [shift_beq_iff] at ho
              rw [Prefix.contains_iff]
              have hmin : min (Prefix.mk p 96).len r.block.len = 96 := Nat.min_eq_left (by simp; omega)
              rw [hmin] at ho
              exact ho.symm
            have := Prefix.contains_congr hcb (q := global6) (by simp [global6])
            rw [unreachable6_long_not_global r hr hg (by omega), hglobp] at this
            cases this
      rw [(nat64Ok_iff p).mpr (Or.inr ⟨hglobp, hall⟩)] at hok
      cases hok
    · rw [hl] at hemb
      rw [hemb he] at hv
      cases hv

/-- An ISATAP address of a denied IPv4 address is denied, under any prefix and with any u and g
bits. -/
theorem isatap_denied (cfg : Config) (p : BitVec 128) (u g : Bool) (v : BitVec 32)
    (hv : cfg.allows (.v4 v) = false) : cfg.allows (.v6 (isatapAddr p u g v)) = false := by
  change cfg.allows4 v = false at hv
  show cfg.allows6 _ = false
  obtain ⟨hi, hl⟩ := isatapAddr_spec p u g v
  cases h : cfg.allows6 (isatapAddr p u g v)
  · rfl
  · exfalso
    obtain ⟨-, hemb, hgen⟩ := (allows6_iff cfg _).mp h
    rw [hl] at hemb hgen
    cases he : cfg.embeds (isatapAddr p u g v)
    · rw [(hgen he).2.2 hi] at hv
      cases hv
    · rw [hemb he] at hv
      cases hv

/-! ## What configuring NAT64 prefixes can allow -/

/-- Configuring NAT64 prefixes allows nothing beyond what the same configuration without them
allows, except addresses in `64:ff9b::/96` whose IPv4 address is allowed. (An honoured prefix of
the caller's own is a /96 inside 2000::/3 outside every row that is not globally reachable, so its
addresses would be allowed anyway unless their ISATAP-looking identifier carries a denied IPv4
address; the IPv4 decision covers that.) -/
theorem allows_nat64_wellKnown (cfg : Config) (a : Addr) (h : cfg.allows a = true) :
    ({ cfg with nat64 := [] } : Config).allows a = true ∨
      ∃ x, a = .v6 x ∧ wellKnown96.contains x = true ∧ cfg.allows4 (low32 x) = true := by
  cases a with
  | v4 v => exact Or.inl h
  | v6 x =>
    obtain ⟨hd, hemb, hgen⟩ := (allows6_iff cfg x).mp h
    have he0 : ({ cfg with nat64 := [] } : Config).embeds x = mapped96.contains x := by
      simp [Config.embeds]
    cases he : cfg.embeds x
    · left
      have hm : mapped96.contains x = false := by
        cases hm : mapped96.contains x
        · rfl
        · have := (embeds_iff cfg x).mpr (Or.inl hm)
          rw [he] at this
          cases this
      exact (allows6_iff { cfg with nat64 := [] } x).mpr
        ⟨hd, fun h1 => (by rw [he0, hm] at h1; cases h1), fun _ => hgen he⟩
    · have h4 := hemb he
      rcases (embeds_iff cfg x).mp he with hmap | ⟨p, -, hok, hp⟩
      · left
        exact (allows6_iff { cfg with nat64 := [] } x).mpr
          ⟨hd, fun _ => h4, fun h1 => (by rw [he0, hmap] at h1; cases h1)⟩
      · rcases (nat64Ok_iff p).mp hok with hw | ⟨hgp, hno⟩
        · right
          refine ⟨x, rfl, ?_, h4⟩
          rw [Prefix.contains_congr hp (q := wellKnown96) (by simp [wellKnown96])]
          exact hw
        · left
          refine (allows6_iff { cfg with nat64 := [] } x).mpr
            ⟨hd, fun _ => h4, fun _ => ⟨?_, ?_, fun _ => h4⟩⟩
          · rw [Prefix.contains_congr hp (q := global6) (by simp [global6])]
            exact hgp
          · intro r hr hg
            cases hc : r.block.contains x
            · rfl
            · have := Prefix.overlaps_of_contains hp hc
              rw [hno r hr hg] at this
              cases this

/-! ## Denying more -/

theorem allows4_of_add_deny4 (cfg : Config) (q : Prefix 32) (v : BitVec 32)
    (h : ({ cfg with deny4 := q :: cfg.deny4 } : Config).allows4 v = true) : cfg.allows4 v = true := by
  rw [allows4_iff] at h ⊢
  exact ⟨h.1, h.2.1, fun p hp => h.2.2 p (by simp [hp])⟩

/-- Denying another IPv4 prefix never allows more. -/
theorem allows_of_add_deny4 (cfg : Config) (q : Prefix 32) (a : Addr)
    (h : ({ cfg with deny4 := q :: cfg.deny4 } : Config).allows a = true) : cfg.allows a = true := by
  cases a with
  | v4 v => exact allows4_of_add_deny4 cfg q v h
  | v6 a =>
    have h' := (allows6_iff _ a).mp h
    exact (allows6_iff cfg a).mpr ⟨h'.1, fun he => allows4_of_add_deny4 cfg q _ (h'.2.1 he),
      fun he => ⟨(h'.2.2 he).1, (h'.2.2 he).2.1,
        fun hi => allows4_of_add_deny4 cfg q _ ((h'.2.2 he).2.2 hi)⟩⟩

/-- Denying another IPv6 prefix never allows more. -/
theorem allows_of_add_deny6 (cfg : Config) (q : Prefix 128) (a : Addr)
    (h : ({ cfg with deny6 := q :: cfg.deny6 } : Config).allows a = true) : cfg.allows a = true := by
  cases a with
  | v4 v => exact h
  | v6 a =>
    have h' := (allows6_iff _ a).mp h
    exact (allows6_iff cfg a).mpr ⟨fun p hp => h'.1 p (by simp [hp]), h'.2.1, h'.2.2⟩

end UrlFence.Addr
