import SchubertForwardStability.Permutations.Statistics.Records
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import SchubertForwardStability.TypeA.Permutations.Basic

/-! # Inversions and length

## Main definitions

* `inversionSet`: ordered pairs of positions with decreasing values.
* `length`: the number of inversions.
* `finiteInversions`, `finiteLength`: the same definitions on `Fin n`.

## Implementation notes

All inversions lie within the forward-stability bound. The membership theorem
removes this truncation, and finite extension preserves the inversion count.
-/

namespace FinitaryPerm

open scoped Classical

/-- The finite set of inversions of a positive-index finitary permutation. -/
noncomputable def inversionSet (w : FinitaryPerm ℕ+) : Finset (ℕ+ × ℕ+) :=
  ((positions w.forwardStability) ×ˢ (positions w.forwardStability)).filter
    fun p => p.1 < p.2 ∧ w p.2 < w p.1

/-- Inversion membership is exactly an increasing position pair with decreasing values. -/
@[simp]
theorem mem_inversionSet (w : FinitaryPerm ℕ+) (i j : ℕ+) :
    (i, j) ∈ w.inversionSet ↔ i < j ∧ w j < w i := by
  simp only [inversionSet, Finset.mem_filter, Finset.mem_product, mem_positions]
  constructor
  · exact fun h => h.2
  · rintro ⟨hij, hw⟩
    have hj : (j : ℕ) ≤ w.forwardStability := by
      by_contra h
      exact (not_lt_of_gt (w.isRecord_above (lt_of_not_ge h) i hij)) hw
    have hijNat : (i : ℕ) < (j : ℕ) := hij
    exact ⟨⟨(le_of_lt hijNat).trans hj, hj⟩, hij, hw⟩

/-- The Coxeter length, defined by the number of inversions. -/
noncomputable def length (w : FinitaryPerm ℕ+) : ℕ := w.inversionSet.card

/-- The identity has no inversions. -/
@[simp]
theorem inversionSet_one : inversionSet (1 : FinitaryPerm ℕ+) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨i, j⟩ h
  obtain ⟨hij, hji⟩ := (mem_inversionSet 1 i j).mp h
  exact (not_lt_of_gt hij) hji

/-- The identity has length zero. -/
@[simp]
theorem length_one : length (1 : FinitaryPerm ℕ+) = 0 := by
  rw [length, inversionSet_one, Finset.card_empty]

/-- Inverting a permutation preserves its inversion count. -/
@[simp]
theorem length_inv (w : FinitaryPerm ℕ+) : w⁻¹.length = w.length := by
  unfold length
  symm
  refine Finset.card_bij (fun p _ => (w p.2, w p.1)) ?_ ?_ ?_
  · rintro ⟨i, j⟩ h
    obtain ⟨hij, hw⟩ := (mem_inversionSet w i j).mp h
    exact (mem_inversionSet w⁻¹ _ _).mpr
      ⟨hw, by simpa only [inv_apply_apply] using hij⟩
  · rintro ⟨i, j⟩ _ ⟨k, l⟩ _ h
    exact Prod.ext (w.injective (congrArg Prod.snd h))
      (w.injective (congrArg Prod.fst h))
  · rintro ⟨i, j⟩ h
    obtain ⟨hij, hw⟩ := (mem_inversionSet w⁻¹ i j).mp h
    refine ⟨(w⁻¹ j, w⁻¹ i), (mem_inversionSet w _ _).mpr ?_, ?_⟩
    · exact ⟨hw, by simpa only [apply_inv_apply] using hij⟩
    · simp only [apply_inv_apply]

/-- Inversions of a finite permutation, represented by pairs of finite positions. -/
abbrev finiteInversions {n : ℕ} (w : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Schubert.FinPermutation.inversionSet w

/-- Finite inversion membership has the same pair of strict inequalities. -/
theorem mem_finiteInversions {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    (i, j) ∈ finiteInversions w ↔ i < j ∧ w j < w i := by
  exact Schubert.FinPermutation.mem_inversionSet_iff w i j

/-- The inversion count of a finite permutation. -/
abbrev finiteLength {n : ℕ} (w : Equiv.Perm (Fin n)) : ℕ := Schubert.FinPermutation.length w

/-- Positive reindexing preserves strict position order. -/
theorem positiveIndex_lt_iff (n : ℕ) (i j : Fin n) :
    (positiveIndex n i).val < (positiveIndex n j).val ↔ i < j := by
  change i.val + 1 < j.val + 1 ↔ i.val < j.val
  exact Nat.add_lt_add_iff_right

/-- Finite extension preserves Coxeter length. -/
theorem length_ofFinite (n : ℕ) (w : Equiv.Perm (Fin n)) :
    (ofFinite n w).length = finiteLength w := by
  unfold length finiteLength
  symm
  refine Finset.card_bij
    (fun p _ => ((positiveIndex n p.1).val, (positiveIndex n p.2).val)) ?_ ?_ ?_
  · rintro ⟨i, j⟩ h
    rw [mem_inversionSet, ofFinite_apply_position, ofFinite_apply_position,
      positiveIndex_lt_iff, positiveIndex_lt_iff]
    exact (mem_finiteInversions w i j).mp h
  · rintro ⟨i, j⟩ _ ⟨k, l⟩ _ h
    apply Prod.ext
    · exact (positiveIndex n).injective (Subtype.ext (congrArg Prod.fst h))
    · exact (positiveIndex n).injective (Subtype.ext (congrArg Prod.snd h))
  · rintro ⟨i, j⟩ h
    obtain ⟨hij, hw⟩ := (mem_inversionSet (ofFinite n w) i j).mp h
    have hj : (j : ℕ) ≤ n := by
      by_contra hn
      exact (not_lt_of_gt ((isSupported_ofFinite n w).isRecord_above
        (lt_of_not_ge hn) i hij)) hw
    have hijNat : (i : ℕ) < (j : ℕ) := hij
    have hi : (i : ℕ) ≤ n := (le_of_lt hijNat).trans hj
    obtain ⟨a, ha⟩ := (positiveIndex n).surjective ⟨i, hi⟩
    obtain ⟨b, hb⟩ := (positiveIndex n).surjective ⟨j, hj⟩
    have hai : (positiveIndex n a).val = i := congrArg Subtype.val ha
    have hbj : (positiveIndex n b).val = j := congrArg Subtype.val hb
    refine ⟨(a, b), ?_, Prod.ext hai hbj⟩
    rw [mem_finiteInversions]
    rw [← hai, ← hbj, ofFinite_apply_position, ofFinite_apply_position] at hw
    exact ⟨(positiveIndex_lt_iff n a b).mp (by rw [hai, hbj]; exact hij),
      (positiveIndex_lt_iff n (w b) (w a)).mp hw⟩

end FinitaryPerm
