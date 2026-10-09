import SchubertForwardStability.Permutations.Finitary.Longest
import SchubertForwardStability.Permutations.Statistics.Inversions
import Mathlib.Tactic

/-! # Order reversal and inversion transport

Reversal of an initial interval reverses its strict order. Reversing both
positions and values therefore bijects inversion sets and preserves length.
-/

namespace FinitaryPerm

open scoped Classical

/-- Initial reversal reverses the strict order of two positions in its interval. -/
theorem longestElement_lt_iff {n : ℕ} {i j : ℕ+}
    (hi : (i : ℕ) ≤ n) (hj : (j : ℕ) ≤ n) :
    longestElement n i < longestElement n j ↔ j < i := by
  change (longestElement n i : ℕ) < (longestElement n j : ℕ) ↔ (j : ℕ) < i
  rw [longestElement_apply_val n i hi, longestElement_apply_val n j hj]
  have := i.pos
  have := j.pos
  omega

/-- Both positions of an inversion lie within every support bound. -/
theorem IsSupported.inversion_positions_le {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) {i j : ℕ+} (h : (i, j) ∈ w.inversionSet) :
    (i : ℕ) ≤ n ∧ (j : ℕ) ≤ n := by
  obtain ⟨hij, hji⟩ := (mem_inversionSet w i j).mp h
  have hj : (j : ℕ) ≤ n := by
    by_contra hn
    exact (not_lt_of_gt (hw.isRecord_above (lt_of_not_ge hn) i hij)) hji
  exact ⟨(le_of_lt (show (i : ℕ) < j from hij)).trans hj, hj⟩

/-- Reversing positions and values carries an inversion to the reflected inversion. -/
theorem inversion_conjugate_longest {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) {i j : ℕ+} (h : (i, j) ∈ w.inversionSet) :
    (longestElement n j, longestElement n i) ∈
      (longestElement n * w * longestElement n).inversionSet := by
  obtain ⟨hi, hj⟩ := hw.inversion_positions_le h
  obtain ⟨hij, hji⟩ := (mem_inversionSet w i j).mp h
  rw [mem_inversionSet]
  refine ⟨(longestElement_lt_iff hj hi).mpr hij, ?_⟩
  simp only [mul_apply, longestElement_apply_twice]
  exact (longestElement_lt_iff ((hw.apply_le_iff i).mpr hi)
    ((hw.apply_le_iff j).mpr hj)).mpr hji

/-- Ambient longest conjugation preserves the inversion length. -/
theorem length_conjugate_longest {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) :
    (longestElement n * w * longestElement n).length = w.length := by
  unfold length
  symm
  refine Finset.card_bij (fun p _ => (longestElement n p.2, longestElement n p.1))
    ?_ ?_ ?_
  · rintro ⟨i, j⟩ h
    exact inversion_conjugate_longest hw h
  · rintro ⟨i, j⟩ _ ⟨k, l⟩ _ h
    exact Prod.ext ((longestElement n).injective (congrArg Prod.snd h))
      ((longestElement n).injective (congrArg Prod.fst h))
  · rintro ⟨i, j⟩ h
    have he := inversion_conjugate_longest hw.conjugate_longest h
    rw [conjugate_longest_twice] at he
    refine ⟨(longestElement n j, longestElement n i), he, ?_⟩
    simp only [longestElement_apply_twice]

end FinitaryPerm
