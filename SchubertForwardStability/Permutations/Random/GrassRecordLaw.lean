import SchubertForwardStability.Permutations.Random.GrassRecordCounts

/-! # Uniform Grassmannian record probabilities

## Main results

The uniform law on the Grassmannian family is evaluated by its exact record count after
collapsing the duplicate initial-segment identity encodings.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

namespace FinitaryPerm

/-- The real family cardinality is the ordinary powerset size minus the duplicates. -/
theorem card_grassmannian_real (n : ℕ) :
    ((grassmannian n).card : ℝ) = (2 : ℝ) ^ n - n := by
  have h := Finset.card_filter_le (positions n).powerset
    (fun V => subsetPermutation n V = 1)
  rw [card_subsetPermutation_one_fiber, Finset.card_powerset, card_positions] at h
  have hn : n ≤ 2 ^ n := (Nat.le_succ n).trans h
  rw [card_grassmannian, Nat.cast_sub hn, Nat.cast_pow, Nat.cast_ofNat]

/-- Uniform Grassmannian record probabilities are the exact binomial-sum fractions. -/
theorem grassmannian_record_probability (n : ℕ) (j : ℕ+) (hj : j.val ≤ n) :
    (unif (grassmannian n)).real {w | IsRecord w j} =
      ((∑ k ∈ Finset.Icc j.val n, (n.choose k : ℝ)) +
        (2 : ℝ) ^ (j.val - 1) - n) / ((2 : ℝ) ^ n - n) := by
  have h : (((grassmannian n).filter fun w => IsRecord w j).card : ℝ) + (n : ℝ) =
      (∑ k ∈ Finset.Icc j.val n, (n.choose k : ℝ)) + (2 : ℝ) ^ (j.val - 1) := by
    exact_mod_cast card_grassmannian_records n j hj
  have he : (((grassmannian n).filter fun w => IsRecord w j).card : ℝ) =
      (∑ k ∈ Finset.Icc j.val n, (n.choose k : ℝ)) + (2 : ℝ) ^ (j.val - 1) - n := by
    linarith
  rw [unif, measureReal_def, uniformOn_finset_event]
  simp only [Set.mem_ofPred_eq, ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [he, card_grassmannian_real]

end FinitaryPerm
