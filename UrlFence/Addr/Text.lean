import UrlFence.Addr.Registry

/-!
# Addresses as text

* **IPv4**: four dotted-decimal parts `0` to `255` without leading zeros, as in `UrlFence.parseHost`
  (`ipv4Ok`): `parse4` accepts exactly the strings that `parseHost` reads as IPv4 addresses
  (`parse4_isSome_iff`). `127.1`, `0x7f.0.0.1` and `017.0.0.1` are refused.
* **IPv6**: the text forms of RFC 4291, section 2.2: eight groups of 1 to 4 hex digits in either
  case, separated by `:`; at most one `::` standing for one or more zero groups; the last two
  groups may be written as a dotted quad in the IPv4 form above (`::ffff:192.0.2.1`). Zone IDs
  (`%eth0`), brackets, prefix lengths (`/64`), spaces and anything else are refused.

`render` prints the form of RFC 5952, section 4: lowercase hex, no leading zeros in a group
(`hex16_canonical`), and the first longest run of two or more zero groups replaced by `::`
(`render6_canonical`). It does not use the mixed form that RFC 5952, section 5 recommends for
IPv4-mapped addresses: `::ffff:192.0.2.1` prints as `::ffff:c000:201`. Parsing a printed address
gives the address back (`parse_render`).
-/

namespace UrlFence.Addr

/-! ## IPv4 -/

/-- Parse a dotted-quad IPv4 address in the strict form. -/
def parse4 (s : List Char) : Option (BitVec 32) :=
  if ipv4Ok (split '.' s) then some (BitVec.ofNat 32 (ofDigits 256 ((split '.' s).map decValue)))
  else none

/-- Print an IPv4 address in dotted-decimal form. -/
def render4 (a : BitVec 32) : List Char := join '.' ((digits 256 4 a.toNat).map (Nat.toDigits 10))

theorem dec_octet : ∀ n, n < 256 →
    decValue (Nat.toDigits 10 n) = n ∧ octetOk (Nat.toDigits 10 n) = true := by
  decide +kernel

theorem octetOk_digits (l : List Char) (h : octetOk l = true) : ∀ c ∈ l, isDigit c = true := by
  simp only [octetOk, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.1.2

theorem render4_chars (a : BitVec 32) : ∀ c ∈ render4 a, c = '.' ∨ isDigit c = true := by
  intro c hc
  rcases mem_join '.' _ c hc with h | ⟨q, hq, hcq⟩
  · exact Or.inl h
  · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hq
    exact Or.inr (octetOk_digits _ (dec_octet n (digits_lt 256 4 a.toNat (by decide) n hn)).2 c hcq)

theorem parse4_render4 (a : BitVec 32) : parse4 (render4 a) = some a := by
  have hlt := digits_lt 256 4 a.toNat (by decide)
  have hlen := digits_length 256 4 a.toNat
  have hsplit : split '.' (render4 a) = (digits 256 4 a.toNat).map (Nat.toDigits 10) := by
    apply split_join
    · intro h
      have := congrArg List.length h
      simp [hlen] at this
    · intro p hp hdot
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hp
      have := octetOk_digits _ (dec_octet n (hlt n hn)).2 '.' hdot
      simp [isDigit] at this
  have hok : ipv4Ok ((digits 256 4 a.toNat).map (Nat.toDigits 10)) = true := by
    simp only [ipv4Ok, List.length_map, hlen, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      true_and]
    intro p hp
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hp
    exact (dec_octet n (hlt n hn)).2
  unfold parse4
  rw [hsplit, ite_eq_left hok, List.map_map,
    List.map_congr_left (f := decValue ∘ Nat.toDigits 10) (g := id)
      (fun n hn => (dec_octet n (hlt n hn)).1), List.map_id, ofDigits_digits]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_ofNat] at this ⊢
  omega

/-- `parse4` accepts exactly the strings that `parseHost`, the host parser of URLs, reads as IPv4
addresses. -/
theorem parse4_isSome_iff (s : List Char) :
    (parse4 s).isSome = true ↔ ∃ ps, parseHost s = some (.ipv4 ps) := by
  unfold parse4 parseHost
  by_cases hv : ipv4Ok (split '.' s) = true
  · have hall : s.all (fun c => isDigit c || c = '.') = true := by
      rw [List.all_eq_true]
      intro c hc
      rw [← join_split '.' s] at hc
      rcases mem_join '.' _ c hc with h | ⟨q, hq, hcq⟩
      · simp [h]
      · simp only [ipv4Ok, Bool.and_eq_true, List.all_eq_true] at hv
        simp [octetOk_digits q (hv.2 q hq) c hcq]
    simp [hv, hall]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, Option.isSome_none, false_iff]
    rintro ⟨ps, hps⟩
    split at hps
    · cases hps
    · split at hps <;> cases hps

/-! ## IPv6 -/

/-- A hex digit, in either case. -/
def isHex (c : Char) : Bool := isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- The value of a hex digit. -/
def hexVal (c : Char) : Nat :=
  if isDigit c then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- One 16-bit group: 1 to 4 hex digits. -/
def group? (p : List Char) : Option Nat :=
  if 0 < p.length && p.length ≤ 4 && p.all isHex then some (ofDigits 16 (p.map hexVal)) else none

/-- The groups of pieces that are all hex groups. -/
def hexGroups : List (List Char) → Option (List Nat)
  | [] => some []
  | p :: ps =>
    match group? p, hexGroups ps with
    | some g, some gs => some (g :: gs)
    | _, _ => none

/-- The groups of colon-separated pieces that contain no `::`. With `quad`, the last piece may be a
dotted quad, which gives two groups. -/
def groups (quad : Bool) (ps : List (List Char)) : Option (List Nat) :=
  if quad && ps.any (fun p => p.contains '.') then
    match ps.getLast?, hexGroups ps.dropLast with
    | some q, some gs =>
      match parse4 q with
      | some v => some (gs ++ digits 65536 2 v.toNat)
      | none => none
    | _, _ => none
  else hexGroups ps

/-- Split at the first `::`. -/
def splitGap : List Char → Option (List Char × List Char)
  | [] => none
  | c :: r =>
    if c = ':' ∧ r.head? = some ':' then some ([], r.tail)
    else (splitGap r).map fun lr => (c :: lr.1, lr.2)

/-- The colon-separated pieces of one side of `::`; none for an empty side. -/
def pieces (s : List Char) : List (List Char) := if s.isEmpty then [] else split ':' s

/-- The characters of an IPv6 address in text form. -/
def isChar6 (c : Char) : Bool := isHex c || c = ':' || c = '.'

/-- The address with these 16-bit groups, the first being the most significant. -/
def ofGroups (gs : List Nat) : BitVec 128 := BitVec.ofNat 128 (ofDigits 65536 gs)

/-- The eight 16-bit groups of an address. -/
def toGroups (a : BitVec 128) : List Nat := digits 65536 8 a.toNat

/-- Parse an IPv6 address in one of the text forms of RFC 4291, section 2.2. -/
def parse6 (s : List Char) : Option (BitVec 128) :=
  if s.all isChar6 then
    match splitGap s with
    | none =>
      match groups true (split ':' s) with
      | some gs => if gs.length = 8 then some (ofGroups gs) else none
      | none => none
    | some (l, r) =>
      match groups false (pieces l), groups true (pieces r) with
      | some ls, some rs =>
        if ls.length + rs.length ≤ 7 then
          some (ofGroups (ls ++ List.replicate (8 - ls.length - rs.length) 0 ++ rs))
        else none
      | _, _ => none
  else none

/-- A lowercase hex digit. -/
def hexChar (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- The number of hex digits of a group, without leading zeros. -/
def hexLen (n : Nat) : Nat := if n < 16 then 1 else if n < 256 then 2 else if n < 4096 then 3 else 4

/-- A group in lowercase hex without leading zeros. -/
def hex16 (n : Nat) : List Char := (digits 16 (hexLen n) n).map hexChar

/-- Scan for runs of zero groups: `i` is the index of the next group, `cur` the length of the
current run, `best` the first longest run so far as (start, length). -/
def zeroRunAux : List Nat → Nat → Nat → Nat × Nat → Nat × Nat
  | [], i, cur, best => if best.2 < cur then (i - cur, cur) else best
  | g :: gs, i, cur, best =>
    if g = 0 then zeroRunAux gs (i + 1) (cur + 1) best
    else zeroRunAux gs (i + 1) 0 (if best.2 < cur then (i - cur, cur) else best)

/-- The first longest run of zero groups, as (start, length); length 0 if there is none. -/
def zeroRun (gs : List Nat) : Nat × Nat := zeroRunAux gs 0 0 (0, 0)

/-- Print an IPv6 address in the form of RFC 5952. (`render6` only uses `::` for a run that it has
checked to be zero groups, of length 2 or more; `parse6_render6` does not depend on `zeroRun`.) -/
def render6 (a : BitVec 128) : List Char :=
  let gs := toGroups a
  let i := (zeroRun gs).1
  let n := (zeroRun gs).2
  if 2 ≤ n ∧ i + n ≤ 8 ∧ (gs.drop i).take n = List.replicate n 0 then
    join ':' ((gs.take i).map hex16) ++ ':' :: ':' :: join ':' ((gs.drop (i + n)).map hex16)
  else join ':' (gs.map hex16)

theorem hexChar_spec : ∀ d, d < 16 →
    hexVal (hexChar d) = d ∧ isHex (hexChar d) = true ∧ hexChar d ≠ ':' ∧ hexChar d ≠ '.' := by
  decide +kernel

theorem hexLen_spec (n : Nat) (h : n < 65536) : 0 < hexLen n ∧ hexLen n ≤ 4 ∧ n < 16 ^ hexLen n := by
  unfold hexLen
  by_cases h1 : n < 16
  · simp [h1]
  · by_cases h2 : n < 256
    · simp [h1, h2]
    · by_cases h3 : n < 4096
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]
        omega

theorem hex16_spec (n : Nat) (h : n < 65536) :
    group? (hex16 n) = some n ∧ hex16 n ≠ [] ∧ ∀ c ∈ hex16 n, isHex c = true ∧ c ≠ ':' ∧ c ≠ '.' := by
  obtain ⟨h0, h4, hn⟩ := hexLen_spec n h
  have hd := digits_lt 16 (hexLen n) n (by decide)
  have hlen : (hex16 n).length = hexLen n := by simp [hex16, digits_length]
  have hchars : ∀ c ∈ hex16 n, isHex c = true ∧ c ≠ ':' ∧ c ≠ '.' := by
    intro c hc
    simp only [hex16, List.mem_map] at hc
    obtain ⟨d, hd', rfl⟩ := hc
    exact (hexChar_spec d (hd d hd')).2
  refine ⟨?_, ?_, hchars⟩
  · have hall : (hex16 n).all isHex = true := List.all_eq_true.mpr (fun c hc => (hchars c hc).1)
    unfold group?
    rw [ite_eq_left (by simp [hlen, hall, h0, h4])]
    congr 1
    simp only [hex16, List.map_map]
    rw [List.map_congr_left (f := hexVal ∘ hexChar) (g := id)
      (fun d hd' => (hexChar_spec d (hd d hd')).1), List.map_id, ofDigits_digits]
    exact Nat.mod_eq_of_lt hn
  · intro he
    have := congrArg List.length he
    simp [hlen] at this
    omega

theorem hex16_pieces (L : List Nat) (hL : ∀ g ∈ L, g < 65536) :
    ∀ p ∈ L.map hex16, p ≠ [] ∧ ':' ∉ p := by
  intro p hp
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
  have := hex16_spec g (hL g hg)
  exact ⟨this.2.1, fun h => (this.2.2 ':' h).2.1 rfl⟩

theorem hexGroups_hex (L : List Nat) (h : ∀ g ∈ L, g < 65536) : hexGroups (L.map hex16) = some L := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    simp only [List.map_cons, hexGroups]
    rw [(hex16_spec g (h g (by simp))).1, ih (fun x hx => h x (by simp [hx]))]

theorem groups_hex (quad : Bool) (L : List Nat) (h : ∀ g ∈ L, g < 65536) :
    groups quad (L.map hex16) = some L := by
  have hno : (L.map hex16).any (fun p => p.contains '.') = false := by
    rw [List.any_eq_false]
    intro p hp hc
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
    exact ((hex16_spec g (h g hg)).2.2 '.' (by simpa using hc)).2.2 rfl
  unfold groups
  simp only [hno, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  exact hexGroups_hex L h

theorem splitGap_append (x y : List Char) (hx : ':' ∉ x) :
    splitGap (x ++ y) = (splitGap y).map fun lr => (x ++ lr.1, lr.2) := by
  induction x with
  | nil =>
    simp only [List.nil_append]
    cases splitGap y <;> rfl
  | cons c x ih =>
    have hc : c ≠ ':' := fun h => hx (h ▸ List.mem_cons_self ..)
    have hx' : ':' ∉ x := fun h => hx (List.mem_cons_of_mem _ h)
    rw [List.cons_append, splitGap, ite_eq_right (by simp [hc]), ih hx', Option.map_map]
    rfl

theorem splitGap_gap (y : List Char) : splitGap (':' :: ':' :: y) = some ([], y) := by
  simp [splitGap]

theorem splitGap_colon (w : List Char) (hw : w.head? ≠ some ':') :
    splitGap (':' :: w) = (splitGap w).map fun lr => (':' :: lr.1, lr.2) := by
  rw [splitGap, ite_eq_right (by simpa using hw)]

theorem join_head? (q : List Char) (rest : List (List Char)) (z : List Char) (hq : q ≠ []) :
    (join ':' (q :: rest) ++ z).head? = q.head? := by
  obtain ⟨c, q', rfl⟩ : ∃ c q', q = c :: q' := by
    cases q with
    | nil => exact absurd rfl hq
    | cons c q' => exact ⟨c, q', rfl⟩
  cases rest with
  | nil => rfl
  | cons r rs => rfl

theorem splitGap_join (ps : List (List Char)) (hne : ps ≠ []) (hps : ∀ p ∈ ps, p ≠ [] ∧ ':' ∉ p)
    (z : List Char) :
    splitGap (join ':' ps ++ z) = (splitGap z).map fun lr => (join ':' ps ++ lr.1, lr.2) := by
  induction ps with
  | nil => exact absurd rfl hne
  | cons p t ih =>
    cases t with
    | nil => exact splitGap_append p z (hps p (by simp)).2
    | cons q rest =>
      have hp := hps p (by simp)
      have hq := hps q (by simp)
      have ih' := ih (by simp) (fun x hx => hps x (List.mem_cons_of_mem _ hx))
      have hhead : (join ':' (q :: rest) ++ z).head? ≠ some ':' := by
        rw [join_head? q rest z hq.1]
        intro h
        cases q with
        | nil => exact hq.1 rfl
        | cons c q' =>
          simp only [List.head?_cons, Option.some.injEq] at h
          exact hq.2 (h ▸ List.mem_cons_self ..)
      rw [show join ':' (p :: q :: rest) = p ++ ':' :: join ':' (q :: rest) from rfl,
        List.append_assoc, splitGap_append p _ hp.2, List.cons_append, splitGap_colon _ hhead, ih',
        Option.map_map, Option.map_map]
      congr 1
      funext lr
      simp [List.append_assoc]

theorem join_ne_nil_of (ps : List (List Char)) (hne : ps ≠ []) (hps : ∀ p ∈ ps, p ≠ []) :
    join ':' ps ≠ [] := by
  cases ps with
  | nil => exact absurd rfl hne
  | cons p t =>
    have hp := hps p (by simp)
    cases t with
    | nil => exact hp
    | cons q rest =>
      show p ++ ':' :: join ':' (q :: rest) ≠ []
      simp

theorem pieces_join (ps : List (List Char)) (hps : ∀ p ∈ ps, p ≠ [] ∧ ':' ∉ p) :
    pieces (join ':' ps) = ps := by
  cases ps with
  | nil => rfl
  | cons p t =>
    have hne := join_ne_nil_of (p :: t) (by simp) (fun q hq => (hps q hq).1)
    unfold pieces
    rw [ite_eq_right (by simpa using hne)]
    exact split_join ':' _ (by simp) (fun q hq => (hps q hq).2)

theorem all_isChar6_join (ps : List (List Char)) (hps : ∀ p ∈ ps, ∀ c ∈ p, isHex c = true) :
    (join ':' ps).all isChar6 = true := by
  rw [List.all_eq_true]
  intro c hc
  rcases mem_join ':' ps c hc with rfl | ⟨q, hq, hcq⟩
  · rfl
  · simp [isChar6, hps q hq c hcq]

theorem hex16_hex (L : List Nat) (hL : ∀ g ∈ L, g < 65536) :
    ∀ p ∈ L.map hex16, ∀ c ∈ p, isHex c = true := by
  intro p hp c hc
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
  exact ((hex16_spec g (hL g hg)).2.2 c hc).1

theorem toGroups_spec (a : BitVec 128) :
    (toGroups a).length = 8 ∧ (∀ g ∈ toGroups a, g < 65536) ∧ ofGroups (toGroups a) = a := by
  refine ⟨digits_length _ _ _, digits_lt _ _ _ (by decide), ?_⟩
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [ofGroups, toGroups, BitVec.toNat_ofNat, ofDigits_digits] at this ⊢
  omega

theorem parse6_full (G : List Nat) (hlen : G.length = 8) (hlt : ∀ g ∈ G, g < 65536) :
    parse6 (join ':' (G.map hex16)) = some (ofGroups G) := by
  have hne : G.map hex16 ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [hlen] at this
  have hgap : splitGap (join ':' (G.map hex16)) = none := by
    have := splitGap_join (G.map hex16) hne (hex16_pieces G hlt) []
    rw [List.append_nil] at this
    rw [this]
    rfl
  unfold parse6
  rw [ite_eq_left (all_isChar6_join _ (hex16_hex G hlt)), hgap]
  dsimp only
  rw [split_join ':' _ hne (fun p hp => (hex16_pieces G hlt p hp).2), groups_hex true G hlt]
  dsimp only
  rw [ite_eq_left (by simp [hlen])]

theorem parse6_gap (G : List Nat) (i n : Nat) (hlen : G.length = 8) (hlt : ∀ g ∈ G, g < 65536)
    (h2 : 2 ≤ n) (hle : i + n ≤ 8) (hz : (G.drop i).take n = List.replicate n 0) :
    parse6 (join ':' ((G.take i).map hex16) ++ ':' :: ':' :: join ':' ((G.drop (i + n)).map hex16)) =
      some (ofGroups G) := by
  have hL : ∀ g ∈ G.take i, g < 65536 := fun g hg => hlt g (List.mem_of_mem_take hg)
  have hR : ∀ g ∈ G.drop (i + n), g < 65536 := fun g hg => hlt g (List.mem_of_mem_drop hg)
  have hsplit : splitGap (join ':' ((G.take i).map hex16) ++ ':' :: ':' :: join ':' ((G.drop (i + n)).map hex16)) =
      some (join ':' ((G.take i).map hex16), join ':' ((G.drop (i + n)).map hex16)) := by
    by_cases hL0 : G.take i = []
    · rw [hL0]
      exact splitGap_gap _
    · rw [splitGap_join _ (by simpa using hL0) (hex16_pieces _ hL), splitGap_gap]
      simp
  have hall : (join ':' ((G.take i).map hex16) ++ ':' :: ':' :: join ':' ((G.drop (i + n)).map hex16)).all
      isChar6 = true := by
    simp only [List.all_append, List.all_cons, all_isChar6_join _ (hex16_hex _ hL),
      all_isChar6_join _ (hex16_hex _ hR)]
    rfl
  unfold parse6
  rw [ite_eq_left hall, hsplit]
  dsimp only
  rw [pieces_join _ (hex16_pieces _ hL), pieces_join _ (hex16_pieces _ hR), groups_hex false _ hL,
    groups_hex true _ hR]
  dsimp only
  have hLlen : (G.take i).length = i := by simp [List.length_take, hlen]; omega
  have hRlen : (G.drop (i + n)).length = 8 - (i + n) := by simp [List.length_drop, hlen]
  rw [ite_eq_left (by omega), hLlen, hRlen, show 8 - i - (8 - (i + n)) = n by omega, ← hz,
    ← List.drop_drop, List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem parse6_render6 (a : BitVec 128) : parse6 (render6 a) = some a := by
  obtain ⟨hlen, hlt, hval⟩ := toGroups_spec a
  unfold render6
  dsimp only
  split
  · rename_i hc
    rw [parse6_gap _ _ _ hlen hlt hc.1 hc.2.1 hc.2.2, hval]
  · rw [parse6_full _ hlen hlt, hval]

theorem colon_mem_render6 (a : BitVec 128) : ':' ∈ render6 a := by
  obtain ⟨hlen, -, -⟩ := toGroups_spec a
  unfold render6
  dsimp only
  split
  · simp
  · generalize toGroups a = G at hlen ⊢
    match G, hlen with
    | x :: y :: rest, _ =>
      show ':' ∈ hex16 x ++ ':' :: join ':' ((y :: rest).map hex16)
      simp

/-! ## The printed form is that of RFC 5952

RFC 5952, section 4: hex digits in lowercase, no leading zeros in a group (`hex16_canonical`), and
`::` for the longest run of zero groups, the first if there are several, never for a single group
(`render6_canonical`). `zeroRun` only looks at which groups are zero, so it is checked on the 256
patterns of zero and non-zero groups (`canonical_patterns`). -/

/-- `n` zero groups from index `i`. -/
def ZeroRun (gs : List Nat) (i n : Nat) : Prop :=
  i + n ≤ gs.length ∧ (gs.drop i).take n = List.replicate n 0

instance (gs : List Nat) (i n : Nat) : Decidable (ZeroRun gs i n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The lists of `k` zeros and ones. -/
def patterns : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (patterns k).flatMap fun l => [0 :: l, 1 :: l]

/-- 0 for a zero group, 1 otherwise. -/
def zeroOne (g : Nat) : Nat := if g = 0 then 0 else 1

theorem mem_patterns (l : List Nat) (h : ∀ x ∈ l, x = 0 ∨ x = 1) : l ∈ patterns l.length := by
  induction l with
  | nil => simp [patterns]
  | cons x l ih =>
    simp only [List.length_cons, patterns, List.mem_flatMap]
    refine ⟨l, ih (fun y hy => h y (by simp [hy])), ?_⟩
    rcases h x (by simp) with rfl | rfl <;> simp

theorem zeroRunAux_zeroOne (gs : List Nat) (i cur : Nat) (best : Nat × Nat) :
    zeroRunAux (gs.map zeroOne) i cur best = zeroRunAux gs i cur best := by
  induction gs generalizing i cur best with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, zeroRunAux, zeroOne]
    by_cases hg : g = 0 <;> simp [hg, ih]

theorem zeroRun_iff_zeroOne (gs : List Nat) (i n : Nat) :
    ZeroRun (gs.map zeroOne) i n ↔ ZeroRun gs i n := by
  unfold ZeroRun
  rw [List.length_map, ← List.map_drop, ← List.map_take, List.eq_replicate_iff, List.eq_replicate_iff,
    List.length_map]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun b hb => ?_⟩
    have := h3 (zeroOne b) (List.mem_map.mpr ⟨b, hb, rfl⟩)
    unfold zeroOne at this
    split at this <;> simp_all
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun b hb => ?_⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    simp [zeroOne, h3 g hg]

theorem canonical_patterns : ∀ l ∈ patterns 8,
    (2 ≤ (zeroRun l).2 → ZeroRun l (zeroRun l).1 (zeroRun l).2 ∧
      (∀ j, j < 9 → ∀ m, m < 9 → ZeroRun l j m → m ≤ (zeroRun l).2) ∧
      ∀ j, j < (zeroRun l).1 → ¬ZeroRun l j (zeroRun l).2) ∧
    ((zeroRun l).2 < 2 → ∀ j, j < 9 → ¬ZeroRun l j 2) := by
  decide +kernel

/-- For eight groups, `zeroRun` finds the first longest run of zero groups if it has two or more
groups, and otherwise there is no such run. -/
theorem zeroRun_canonical (gs : List Nat) (h : gs.length = 8) :
    (2 ≤ (zeroRun gs).2 → ZeroRun gs (zeroRun gs).1 (zeroRun gs).2 ∧
      (∀ j m, ZeroRun gs j m → m ≤ (zeroRun gs).2) ∧
      ∀ j, j < (zeroRun gs).1 → ¬ZeroRun gs j (zeroRun gs).2) ∧
    ((zeroRun gs).2 < 2 → ∀ j, ¬ZeroRun gs j 2) := by
  have hp : gs.map zeroOne ∈ patterns 8 := by
    have := mem_patterns (gs.map zeroOne) (by
      intro x hx
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp hx
      unfold zeroOne
      split <;> simp)
    rwa [List.length_map, h] at this
  have hc := canonical_patterns _ hp
  rw [show zeroRun (gs.map zeroOne) = zeroRun gs from zeroRunAux_zeroOne gs 0 0 (0, 0)] at hc
  simp only [zeroRun_iff_zeroOne] at hc
  obtain ⟨h1, h2⟩ := hc
  refine ⟨fun hn => ?_, fun hn j hj => h2 hn j ?_ hj⟩
  · obtain ⟨hr, hmax, hfirst⟩ := h1 hn
    refine ⟨hr, fun j m hjm => hmax j ?_ m ?_ hjm, hfirst⟩
    · have := hjm.1
      omega
    · have := hjm.1
      omega
  · have := hj.1
    omega

/-- `render6` replaces the first longest run of two or more zero groups with `::`, and prints all
eight groups if there is no such run. -/
theorem render6_canonical (a : BitVec 128) :
    (∃ i n, 2 ≤ n ∧ ZeroRun (toGroups a) i n ∧ (∀ j m, ZeroRun (toGroups a) j m → m ≤ n) ∧
      (∀ j, j < i → ¬ZeroRun (toGroups a) j n) ∧
      render6 a = join ':' (((toGroups a).take i).map hex16) ++ ':' :: ':' ::
        join ':' (((toGroups a).drop (i + n)).map hex16)) ∨
    ((∀ j, ¬ZeroRun (toGroups a) j 2) ∧ render6 a = join ':' ((toGroups a).map hex16)) := by
  obtain ⟨hlen, -, -⟩ := toGroups_spec a
  obtain ⟨h1, h2⟩ := zeroRun_canonical (toGroups a) hlen
  unfold render6
  dsimp only
  by_cases hn : 2 ≤ (zeroRun (toGroups a)).2
  · obtain ⟨hr, hmax, hfirst⟩ := h1 hn
    have hle := hr.1
    left
    refine ⟨_, _, hn, hr, hmax, hfirst, ?_⟩
    rw [ite_eq_left ⟨hn, by omega, hr.2⟩]
  · right
    refine ⟨h2 (by omega), ?_⟩
    rw [ite_eq_right (fun h => hn h.1)]

theorem digits_head? (b k n : Nat) : (digits b (k + 1) n).head? = some (n / b ^ k % b) := by
  induction k generalizing n with
  | zero => simp [digits]
  | succ k ih =>
    rw [digits, List.head?_append, ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    rfl

theorem hexChar_lower : ∀ d, d < 16 →
    (isDigit (hexChar d) = true ∨ ('a' ≤ hexChar d ∧ hexChar d ≤ 'f')) ∧ (hexChar d = '0' → d = 0) := by
  decide +kernel

/-- A printed group is in lowercase hex, has 1 to 4 digits, and starts with `0` only if it is `0`. -/
theorem hex16_canonical (n : Nat) (h : n < 65536) :
    (∀ c ∈ hex16 n, isDigit c = true ∨ ('a' ≤ c ∧ c ≤ 'f')) ∧ 0 < (hex16 n).length ∧
      (hex16 n).length ≤ 4 ∧ (hex16 n = ['0'] ∨ (hex16 n).head? ≠ some '0') := by
  obtain ⟨h0, h4, -⟩ := hexLen_spec n h
  have hd := digits_lt 16 (hexLen n) n (by decide)
  have hlen : (hex16 n).length = hexLen n := by simp [hex16, digits_length]
  refine ⟨?_, by omega, by omega, ?_⟩
  · intro c hc
    simp only [hex16, List.mem_map] at hc
    obtain ⟨d, hd', rfl⟩ := hc
    exact (hexChar_lower d (hd d hd')).1
  · by_cases hn0 : n = 0
    · subst hn0
      exact Or.inl (by decide)
    · right
      obtain ⟨k, hk⟩ : ∃ k, hexLen n = k + 1 := ⟨hexLen n - 1, by omega⟩
      have hdig : n / 16 ^ k % 16 ≠ 0 := by
        unfold hexLen at hk
        by_cases h1 : n < 16
        · simp only [h1, ↓reduceIte] at hk
          obtain rfl : k = 0 := by omega
          simp only [Nat.pow_zero, Nat.div_one]
          omega
        · by_cases h2 : n < 256
          · simp only [h1, h2, ↓reduceIte] at hk
            obtain rfl : k = 1 := by omega
            simp only [Nat.pow_one]
            omega
          · by_cases h3 : n < 4096
            · simp only [h1, h2, h3, ↓reduceIte] at hk
              obtain rfl : k = 2 := by omega
              show n / 256 % 16 ≠ 0
              omega
            · simp only [h1, h2, h3, ↓reduceIte] at hk
              obtain rfl : k = 3 := by omega
              show n / 4096 % 16 ≠ 0
              omega
      simp only [hex16, hk, List.head?_map, digits_head?, Option.map_some, ne_eq, Option.some.injEq]
      intro hz
      exact hdig ((hexChar_lower _ (Nat.mod_lt _ (by decide))).2 hz)

/-! ## Both families -/

/-- Parse an address: IPv6 if it contains `:`, IPv4 otherwise. -/
def parse (s : List Char) : Option Addr :=
  if ':' ∈ s then (parse6 s).map .v6 else (parse4 s).map .v4

/-- Print an address: dotted decimal, or the form of RFC 5952. -/
def render : Addr → List Char
  | .v4 a => render4 a
  | .v6 a => render6 a

/-- Parsing a printed address gives the address back. -/
theorem parse_render (a : Addr) : parse a.render = some a := by
  cases a with
  | v4 a =>
    have : ':' ∉ render4 a := by
      intro h
      rcases render4_chars a ':' h with h | h
      · exact absurd h (by decide)
      · simp [isDigit] at h
    simp [parse, render, this, parse4_render4]
  | v6 a => simp [parse, render, colon_mem_render6 a, parse6_render6]

def parseString (s : String) : Option Addr := parse s.toList

def toString (a : Addr) : String := String.ofList a.render

end UrlFence.Addr
