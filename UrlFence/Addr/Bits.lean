import UrlFence.Host

/-!
# Addresses, prefixes and digits

An IPv4 address is a `BitVec 32` and an IPv6 address a `BitVec 128`; the first bit on the wire is
the most significant one. A prefix `⟨base, len⟩` of a `w`-bit address contains `a` when the first
`len` bits of `a` are those of `base` (`Prefix.contains_iff_getMsbD`): `Prefix.contains` shifts both
right by `w - len`, which keeps exactly those bits, and compares. On the numeric values that is
equal quotients by `2 ^ (w - len)` (`Prefix.contains_iff`), and for a block whose other bits are
zero, as in the registries, the range `base ≤ a < base + 2 ^ (w - len)` (`Prefix.contains_iff_range`).

`digits b k n` are the last `k` digits of `n` in base `b`, most significant first, and `ofDigits`
reads them back (`ofDigits_digits`). Octets and 16-bit groups are digits in base 256 and 65536.
-/

namespace UrlFence

/-- An IP address. -/
inductive Addr where
  | v4 (a : BitVec 32)
  | v6 (a : BitVec 128)
  deriving DecidableEq, Repr

namespace Addr

/-- The first `len` bits of the `w`-bit address `base`. -/
structure Prefix (w : Nat) where
  base : BitVec w
  len : Nat
  deriving DecidableEq, Repr

/-- `a` is in `p` when its first `p.len` bits are those of `p.base`. -/
def Prefix.contains {w : Nat} (p : Prefix w) (a : BitVec w) : Bool :=
  a >>> (w - p.len) == p.base >>> (w - p.len)

/-- Two prefixes have an address in common: their bases agree on the first bits of the shorter one. -/
def Prefix.overlaps {w : Nat} (p q : Prefix w) : Bool :=
  p.base >>> (w - min p.len q.len) == q.base >>> (w - min p.len q.len)

theorem shift_beq_iff {w : Nat} (a b : BitVec w) (k : Nat) :
    (a >>> k == b >>> k) = true ↔ a.toNat / 2 ^ k = b.toNat / 2 ^ k := by
  simp [BitVec.toNat_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- Prefix membership on the numeric value: equal quotients by `2 ^ (w - len)`. -/
theorem Prefix.contains_iff {w : Nat} (p : Prefix w) (a : BitVec w) :
    p.contains a = true ↔ a.toNat / 2 ^ (w - p.len) = p.base.toNat / 2 ^ (w - p.len) :=
  shift_beq_iff _ _ _

/-- Prefix membership bit by bit: the first `p.len` bits of `a`, most significant first, are those of
`p.base`. -/
theorem Prefix.contains_iff_getMsbD {w : Nat} (p : Prefix w) (a : BitVec w) :
    p.contains a = true ↔ ∀ i, i < p.len → a.getMsbD i = p.base.getMsbD i := by
  unfold Prefix.contains
  rw [beq_iff_eq]
  constructor
  · intro h i hi
    by_cases hw : i < w
    · rw [BitVec.getMsbD_eq_getLsbD, BitVec.getMsbD_eq_getLsbD]
      simp only [hw, decide_true, Bool.true_and]
      have := congrArg (fun x => x.getLsbD (w - 1 - i - (w - p.len))) h
      simp only [BitVec.getLsbD_ushiftRight] at this
      rwa [show w - p.len + (w - 1 - i - (w - p.len)) = w - 1 - i by omega] at this
    · rw [BitVec.getMsbD_of_ge _ _ (by omega), BitVec.getMsbD_of_ge _ _ (by omega)]
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
    by_cases hk : w - p.len + j < w
    · have := h (w - 1 - (w - p.len + j)) (by omega)
      rw [BitVec.getMsbD_eq_getLsbD, BitVec.getMsbD_eq_getLsbD] at this
      simp only [show w - 1 - (w - p.len + j) < w by omega, decide_true, Bool.true_and] at this
      rwa [show w - 1 - (w - 1 - (w - p.len + j)) = w - p.len + j by omega] at this
    · rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

theorem div_pow_eq_of_le {x y i j : Nat} (h : x / 2 ^ i = y / 2 ^ i) (hij : i ≤ j) :
    x / 2 ^ j = y / 2 ^ j := by
  have : 2 ^ j = 2 ^ i * 2 ^ (j - i) := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

theorem div_eq_iff_range {a b k : Nat} (hk : 0 < k) (hb : b % k = 0) :
    a / k = b / k ↔ b ≤ a ∧ a < b + k := by
  have hb' : k * (b / k) = b := by have := Nat.div_add_mod b k; omega
  have ha := Nat.div_add_mod a k
  have hm := Nat.mod_lt a hk
  constructor
  · intro h
    rw [h] at ha
    omega
  · rintro ⟨h1, h2⟩
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm, hb']; exact h1
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm, hb']; exact h2

/-- For a block whose bits after the first `len` are zero, membership is a range of values. -/
theorem Prefix.contains_iff_range {w : Nat} (p : Prefix w) (a : BitVec w)
    (h : p.base.toNat % 2 ^ (w - p.len) = 0) :
    p.contains a = true ↔ p.base.toNat ≤ a.toNat ∧ a.toNat < p.base.toNat + 2 ^ (w - p.len) := by
  rw [Prefix.contains_iff]
  exact div_eq_iff_range (Nat.two_pow_pos _) h

/-- An address in two prefixes makes them overlap. -/
theorem Prefix.overlaps_of_contains {w : Nat} {p q : Prefix w} {a : BitVec w}
    (hp : p.contains a = true) (hq : q.contains a = true) : p.overlaps q = true := by
  rw [Prefix.contains_iff] at hp hq
  unfold Prefix.overlaps
  rw [shift_beq_iff]
  have h1 := div_pow_eq_of_le hp (show w - p.len ≤ w - min p.len q.len by omega)
  have h2 := div_pow_eq_of_le hq (show w - q.len ≤ w - min p.len q.len by omega)
  exact h1.symm.trans h2

/-- If `p` overlaps a shorter prefix `q`, every address of `p` is in `q`. -/
theorem Prefix.contains_of_overlaps {w : Nat} {p q : Prefix w} {a : BitVec w}
    (ho : p.overlaps q = true) (hl : q.len ≤ p.len) (hp : p.contains a = true) :
    q.contains a = true := by
  rw [Prefix.contains_iff] at hp ⊢
  unfold Prefix.overlaps at ho
  rw [shift_beq_iff, Nat.min_eq_right hl] at ho
  exact (div_pow_eq_of_le hp (show w - p.len ≤ w - q.len by omega)).trans ho

/-- Whether an address of `p` is in a shorter prefix `q` depends only on `p`. -/
theorem Prefix.contains_congr {w : Nat} {p q : Prefix w} {a : BitVec w}
    (hp : p.contains a = true) (hl : q.len ≤ p.len) : q.contains a = q.contains p.base := by
  rw [Prefix.contains_iff] at hp
  have h := div_pow_eq_of_le hp (show w - p.len ≤ w - q.len by omega)
  have : a >>> (w - q.len) = p.base >>> (w - q.len) := by
    rw [BitVec.toNat_eq]
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact h
  unfold Prefix.contains
  rw [this]

/-- The number with the digits `ds` in base `b`, most significant first. -/
def ofDigits (b : Nat) (ds : List Nat) : Nat := ds.foldl (fun n d => b * n + d) 0

/-- The last `k` digits of `n` in base `b`, most significant first. -/
def digits (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => digits b k (n / b) ++ [n % b]

theorem ofDigits_snoc (b : Nat) (ds : List Nat) (d : Nat) :
    ofDigits b (ds ++ [d]) = b * ofDigits b ds + d := by
  simp [ofDigits, List.foldl_append]

theorem ofDigits_digits (b k n : Nat) : ofDigits b (digits b k n) = n % b ^ k := by
  induction k generalizing n with
  | zero => simp [digits, ofDigits, Nat.mod_one]
  | succ k ih =>
    rw [digits, ofDigits_snoc, ih, Nat.pow_succ', Nat.mod_mul]
    omega

theorem digits_length (b k n : Nat) : (digits b k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [digits, ih]

theorem digits_lt (b k n : Nat) (hb : 0 < b) : ∀ d ∈ digits b k n, d < b := by
  induction k generalizing n with
  | zero => simp [digits]
  | succ k ih =>
    intro d hd
    simp only [digits, List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact ih _ d hd
    · exact Nat.mod_lt _ hb

end Addr
end UrlFence
