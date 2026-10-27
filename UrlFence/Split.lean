/-!
# Splitting at a separator

`split sep` cuts a list of characters at every `sep`; `join sep` puts the pieces back with `sep`
between them. The two are inverse (`join_split`, `split_join`), no piece contains `sep`
(`split_noSep`), and splitting distributes over a separator (`split_append_sep`).
-/

namespace UrlFence

/-- `splitAux sep l acc` splits `l`, where `acc` holds the current piece so far, in reverse. -/
def splitAux (sep : Char) : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | c :: cs, acc => if c = sep then acc.reverse :: splitAux sep cs [] else splitAux sep cs (c :: acc)

/-- Split at every `sep`: `"a.b"` gives `["a", "b"]`, `""` gives `[""]`. Never empty. -/
def split (sep : Char) (l : List Char) : List (List Char) := splitAux sep l []

/-- Join pieces with `sep` between them (the inverse of `split`). -/
def join (sep : Char) : List (List Char) → List Char
  | [] => []
  | [x] => x
  | x :: y :: rest => x ++ sep :: join sep (y :: rest)

theorem splitAux_ne_nil (sep : Char) (l acc : List Char) : splitAux sep l acc ≠ [] := by
  induction l generalizing acc with
  | nil => simp [splitAux]
  | cons c cs ih =>
    unfold splitAux
    split <;> simp_all

theorem split_ne_nil (sep : Char) (l : List Char) : split sep l ≠ [] := splitAux_ne_nil sep l []

theorem join_cons_of_ne_nil (sep : Char) (x : List Char) {t : List (List Char)} (h : t ≠ []) :
    join sep (x :: t) = x ++ sep :: join sep t := by
  cases t with
  | nil => exact absurd rfl h
  | cons y rest => rfl

theorem join_splitAux (sep : Char) (l acc : List Char) : join sep (splitAux sep l acc) = acc.reverse ++ l := by
  induction l generalizing acc with
  | nil => simp [splitAux, join]
  | cons c cs ih =>
    unfold splitAux
    split
    · rename_i hc
      subst hc
      rw [join_cons_of_ne_nil _ _ (splitAux_ne_nil _ cs []), ih]
      simp
    · rw [ih]
      simp

/-- Joining the pieces gives back the original list. -/
theorem join_split (sep : Char) (l : List Char) : join sep (split sep l) = l := by
  simp [split, join_splitAux]

theorem splitAux_noSep (sep : Char) (l acc : List Char) (hacc : sep ∉ acc) :
    ∀ p ∈ splitAux sep l acc, sep ∉ p := by
  induction l generalizing acc with
  | nil => simpa [splitAux] using hacc
  | cons c cs ih =>
    unfold splitAux
    split
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simpa using hacc
      · exact ih [] (by simp) p hp
    · rename_i hc
      exact ih (c :: acc) (by simp_all [eq_comm])

/-- No piece of a split contains the separator. -/
theorem split_noSep (sep : Char) (l : List Char) : ∀ p ∈ split sep l, sep ∉ p :=
  splitAux_noSep sep l [] (by simp)

theorem splitAux_append_of_noSep (sep : Char) (x rest acc : List Char) (hx : sep ∉ x) :
    splitAux sep (x ++ rest) acc = splitAux sep rest (x.reverse ++ acc) := by
  induction x generalizing acc with
  | nil => simp
  | cons c cs ih =>
    have hc : c ≠ sep := by intro h; exact hx (by simp [h])
    have hcs : sep ∉ cs := by intro h; exact hx (by simp [h])
    simp [List.cons_append, splitAux, hc, ih (c :: acc) hcs]

/-- Splitting a join gives back the pieces, when no piece contains the separator. -/
theorem split_join (sep : Char) (ps : List (List Char)) (hne : ps ≠ []) (hps : ∀ p ∈ ps, sep ∉ p) :
    split sep (join sep ps) = ps := by
  induction ps with
  | nil => exact absurd rfl hne
  | cons x t ih =>
    cases t with
    | nil =>
      have hx := hps x (by simp)
      simp only [join, split]
      rw [← List.append_nil x, splitAux_append_of_noSep sep x [] [] hx]
      simp [splitAux]
    | cons y rest =>
      have hx := hps x (by simp)
      have ht : ∀ p ∈ y :: rest, sep ∉ p := fun p hp => hps p (by simp [hp])
      have ih' := ih (by simp) ht
      simp only [join, split] at ih' ⊢
      rw [splitAux_append_of_noSep sep x _ [] hx]
      simp [splitAux, ih']

theorem splitAux_append_sep (sep : Char) (x y acc : List Char) :
    splitAux sep (x ++ sep :: y) acc = splitAux sep x acc ++ split sep y := by
  induction x generalizing acc with
  | nil => simp [splitAux, split]
  | cons c cs ih =>
    by_cases hc : c = sep
    · simp [splitAux, hc, ih]
    · simp [splitAux, hc, ih]

/-- Splitting distributes over a separator. -/
theorem split_append_sep (sep : Char) (x y : List Char) :
    split sep (x ++ sep :: y) = split sep x ++ split sep y :=
  splitAux_append_sep sep x y []

/-- Joining distributes over appending non-empty lists of pieces. -/
theorem join_append (sep : Char) (x y : List (List Char)) (hx : x ≠ []) (hy : y ≠ []) :
    join sep (x ++ y) = join sep x ++ sep :: join sep y := by
  induction x with
  | nil => exact absurd rfl hx
  | cons a t ih =>
    cases t with
    | nil => rw [List.singleton_append]; exact join_cons_of_ne_nil sep a hy
    | cons b rest =>
      have := ih (by simp)
      simp only [List.cons_append] at this ⊢
      rw [join_cons_of_ne_nil sep a (by simp), this, join_cons_of_ne_nil sep a (by simp)]
      simp

theorem mem_join (sep : Char) (ps : List (List Char)) (x : Char) (h : x ∈ join sep ps) :
    x = sep ∨ ∃ q ∈ ps, x ∈ q := by
  induction ps with
  | nil => simp [join] at h
  | cons q t ih =>
    cases t with
    | nil => exact Or.inr ⟨q, by simp, by simpa [join] using h⟩
    | cons y rest =>
      simp only [join, List.mem_append, List.mem_cons] at h
      rcases h with h | h | h
      · exact Or.inr ⟨q, by simp, h⟩
      · exact Or.inl h
      · rcases ih h with h | ⟨q', hq', hx⟩
        · exact Or.inl h
        · exact Or.inr ⟨q', by simp [hq'], hx⟩

end UrlFence
