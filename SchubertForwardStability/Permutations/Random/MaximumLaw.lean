import SchubertForwardStability.Permutations.Random.SubsetMaximum
import SchubertForwardStability.Permutations.Random.CardLaw

/-! # The law of the maximum selected position

## Main results

A bound on the selected maximum restricts a subset to an initial interval.
The exact finite event counts and probabilities include both zero and thresholds
above the ambient interval.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace FinitaryPerm

/-- A selected maximum is bounded exactly when every selected position is bounded. -/
theorem subset_maximum_le_iff (m : ℕ) (V : Finset ℕ+) :
    V.sup PNat.val ≤ m ↔ V ⊆ positions m := by
  constructor
  · intro h j hj
    rw [mem_positions]
    exact (Finset.le_sup (f := PNat.val) hj).trans h
  · exact subset_maximum_le m V

/-- The bounded-maximum fibre is the powerset of the shorter initial interval. -/
theorem subset_maximum_fiber (n m : ℕ) :
    (positions n).powerset.filter (fun V => V.sup PNat.val ≤ m) =
      (positions (min n m)).powerset := by
  ext V
  simp only [Finset.mem_filter, Finset.mem_powerset, subset_maximum_le_iff]
  constructor
  · rintro ⟨hn, hm⟩ j hj
    rw [mem_positions]
    exact Nat.le_min.mpr ⟨((mem_positions n j).mp (hn hj)),
      ((mem_positions m j).mp (hm hj))⟩
  · intro h
    constructor
    · intro j hj
      rw [mem_positions]
      exact ((mem_positions (min n m) j).mp (h hj)).trans (min_le_left _ _)
    · intro j hj
      rw [mem_positions]
      exact ((mem_positions (min n m) j).mp (h hj)).trans (min_le_right _ _)

/-- Exactly `2^(min n m)` admissible subsets have selected maximum at most `m`. -/
theorem card_subset_maximum_le (n m : ℕ) :
    ((positions n).powerset.filter fun V => V.sup PNat.val ≤ m).card =
      2 ^ min n m := by
  rw [subset_maximum_fiber, Finset.card_powerset, card_positions]

/-- The bounded-maximum event has its exact powerset fraction as probability. -/
theorem subsetLaw_maximum_le (n m : ℕ) :
    subsetLaw n {V | V.sup PNat.val ≤ m} =
      (2 : ℝ≥0∞) ^ min n m / (2 : ℝ≥0∞) ^ n := by
  rw [subsetLaw, uniformOn_finset_event]
  simp only [Set.mem_ofPred_eq, card_subset_maximum_le, Finset.card_powerset,
    card_positions, Nat.cast_pow, Nat.cast_ofNat]

/-- The real bounded-maximum probability is the exact initial-interval fraction. -/
theorem subsetLaw_maximum_le_real (n m : ℕ) :
    (subsetLaw n).real {V | V.sup PNat.val ≤ m} =
      (2 : ℝ) ^ min n m / (2 : ℝ) ^ n := by
  rw [measureReal_def, subsetLaw_maximum_le]
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat]

/-- For a threshold within the ambient interval, the probability is an inverse power. -/
theorem subsetLaw_maximum_le_of_le (n m : ℕ) (hm : m ≤ n) :
    (subsetLaw n).real {V | V.sup PNat.val ≤ m} = ((2 : ℝ) ^ (n - m))⁻¹ := by
  rw [subsetLaw_maximum_le_real, min_eq_right hm]
  have he : n = m + (n - m) := by omega
  rw [he, pow_add, Nat.add_sub_cancel_left]
  have hp : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- A threshold above the ambient interval contains every admissible subset. -/
theorem subsetLaw_maximum_le_of_ge (n m : ℕ) (hm : n ≤ m) :
    (subsetLaw n).real {V | V.sup PNat.val ≤ m} = 1 := by
  rw [subsetLaw_maximum_le_real, min_eq_left hm, div_self]
  exact pow_ne_zero _ (by norm_num)

end FinitaryPerm
