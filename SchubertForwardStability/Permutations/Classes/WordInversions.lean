import SchubertForwardStability.Permutations.Classes.WordRoots

/-! # Adjacent value swaps and inversion pairs

## Main results

Left multiplication by a simple transposition inserts exactly one inversion pair
when its inverse-position root is positive.
-/

namespace FinitaryPerm

private theorem adjacent_values_gt (i x y : ℕ+) :
    swap i (i + 1) y < swap i (i + 1) x ↔
      (y < x ∧ ¬(y = i ∧ x = i + 1)) ∨ (y = i + 1 ∧ x = i) := by
  change Equiv.swap i (i + 1) y < Equiv.swap i (i + 1) x ↔ _
  simp only [Equiv.swap_apply_def]
  split_ifs <;>
    simp_all only [← PNat.coe_inj, ← PNat.coe_lt_coe, PNat.add_coe, PNat.val_ofNat,
      and_true, true_and, false_and, and_false, not_false_eq_true, not_true_eq_false,
      or_false, or_true, iff_false, iff_true] <;>
    omega

private theorem apply_eq_inv (w : FinitaryPerm ℕ+) (a b : ℕ+) :
    w a = b ↔ a = w⁻¹ b := by
  constructor
  · intro he
    exact (inv_apply_apply w a).symm.trans (congrArg (fun j => w⁻¹ j) he)
  · intro he
    rw [he, apply_inv_apply]

/-- A positive inverse-position root inserts exactly its pair under an adjacent value swap. -/
theorem inversionSet_simple_mul (w : FinitaryPerm ℕ+) (i : ℕ+)
    (hi : w⁻¹ i < w⁻¹ (i + 1)) :
    (simpleTransposition i * w).inversionSet =
      insert (w⁻¹ i, w⁻¹ (i + 1)) w.inversionSet := by
  ext p
  rcases p with ⟨a, b⟩
  simp only [mem_inversionSet, mul_apply, simpleTransposition, Finset.mem_insert,
    Prod.mk.injEq, adjacent_values_gt, apply_eq_inv]
  constructor
  · rintro ⟨hab, (⟨hw, hn⟩ | he)⟩
    · exact Or.inr ⟨hab, hw⟩
    · exact Or.inl ⟨he.2, he.1⟩
  · rintro (⟨ha, hb⟩ | ⟨hab, hw⟩)
    · subst a
      subst b
      exact ⟨hi, Or.inr ⟨rfl, rfl⟩⟩
    · refine ⟨hab, Or.inl ⟨hw, ?_⟩⟩
      rintro ⟨hb, ha⟩
      subst a
      subst b
      exact (not_lt_of_gt hi) hab

/-- Suffix-conjugated roots in the same order as the displayed letters. -/
def wordRoots (word : List ℕ+) : List (ℕ+ × ℕ+) := (wordCuts word).map wordCutRoot

/-- Adding the first letter adds its inverse-suffix root at the front. -/
theorem wordRoots_cons (i : ℕ+) (word : List ℕ+) :
    wordRoots (i :: word) =
      ((wordProduct word)⁻¹ i, (wordProduct word)⁻¹ (i + 1)) :: wordRoots word := by
  simp only [wordRoots, wordCuts, List.map_cons, List.map_map]
  rfl

/-- The roots of a reduced word are exactly the inversions of its product. -/
theorem mem_wordRoots {word : List ℕ+}
    (hr : IsReducedWord (wordProduct word) word) (p : ℕ+ × ℕ+) :
    p ∈ wordRoots word ↔ p ∈ (wordProduct word).inversionSet := by
  induction word with
  | nil => simp only [wordRoots, wordCuts, List.map_nil, List.not_mem_nil,
      wordProduct_nil, inversionSet_one, Finset.notMem_empty]
  | cons i word ih =>
    rw [wordRoots_cons, wordProduct_cons,
      inversionSet_simple_mul _ _ (reduced_prefix_root_lt hr)]
    simp only [List.mem_cons, Finset.mem_insert, ih (isReducedWord_tail hr)]

/-- A reduced word lists each inversion root only once. -/
theorem wordRoots_nodup {word : List ℕ+}
    (hr : IsReducedWord (wordProduct word) word) : (wordRoots word).Nodup := by
  induction word with
  | nil => exact List.nodup_nil
  | cons i word ih =>
    rw [wordRoots_cons]
    refine List.Nodup.cons ?_ (ih (isReducedWord_tail hr))
    intro hm
    have hp := (mem_wordRoots (isReducedWord_tail hr) _).mp hm
    have hv := (mem_inversionSet _ _ _).mp hp
    simp only [apply_inv_apply] at hv
    exact (not_lt_of_gt (show i < i + 1 from Nat.lt_succ_self (i : ℕ))) hv.2

/-- Every selected reduced-word root is an inversion of the full product. -/
theorem wordCutRoot_mem {word : List ℕ+} {c : List ℕ+ × ℕ+ × List ℕ+}
    (hr : IsReducedWord (wordProduct word) word) (hc : c ∈ wordCuts word) :
    wordCutRoot c ∈ (wordProduct word).inversionSet := by
  exact (mem_wordRoots hr _).mp (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- Roots distinguish selected letters of a reduced word. -/
theorem wordCutRoot_injective {word : List ℕ+} {c d : List ℕ+ × ℕ+ × List ℕ+}
    (hr : IsReducedWord (wordProduct word) word) (hc : c ∈ wordCuts word)
    (hd : d ∈ wordCuts word) (he : wordCutRoot c = wordCutRoot d) : c = d := by
  exact List.inj_on_of_nodup_map (wordRoots_nodup hr) hc hd he

/-- Each inversion has a unique selected letter with that suffix-conjugated root. -/
theorem exists_unique_wordCutRoot {word : List ℕ+} {p : ℕ+ × ℕ+}
    (hr : IsReducedWord (wordProduct word) word)
    (hp : p ∈ (wordProduct word).inversionSet) :
    ∃! c, c ∈ wordCuts word ∧ wordCutRoot c = p := by
  obtain ⟨c, hc, he⟩ := List.mem_map.mp ((mem_wordRoots hr p).mpr hp)
  refine ⟨c, ⟨hc, he⟩, ?_⟩
  intro d hd
  exact wordCutRoot_injective hr hd.1 hc (hd.2.trans he.symm)

end FinitaryPerm
