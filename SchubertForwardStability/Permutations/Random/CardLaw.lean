import SchubertForwardStability.Permutations.Random.SubsetCounts
import Mathlib.Probability.Distributions.Binomial

/-! # The cardinality law of uniform subsets

## Main results

Uniform sampling from the admissible powerset gives the binomial cardinality law
with parameter one half. Its singleton probabilities are the binomial
fibre counts divided by the powerset cardinality, including ambient size zero.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal unitInterval

namespace FinitaryPerm

/-- The sampled-cardinality singleton mass is its binomial fibre fraction. -/
theorem subsetLaw_card_singleton (n k : ℕ) :
    (subsetLaw n).map (Finset.card : Finset ℕ+ → ℕ) {k} =
      (n.choose k : ℝ≥0∞) / (2 : ℝ≥0∞) ^ n := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton k),
    subsetLaw, uniformOn_finset_event]
  simp only [Set.mem_preimage, Set.mem_singleton_iff, card_subset_size,
    Finset.card_powerset, card_positions, Nat.cast_pow, Nat.cast_ofNat]

/-- The real sampled-cardinality singleton mass is `choose n k / 2^n`. -/
theorem subsetLaw_card_real (n k : ℕ) :
    ((subsetLaw n).map (Finset.card : Finset ℕ+ → ℕ)).real {k} =
      (n.choose k : ℝ) / (2 : ℝ) ^ n := by
  rw [measureReal_def, subsetLaw_card_singleton]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]

/-- Uniform admissible subsets have the binomial cardinality law, including size zero. -/
theorem subsetLaw_card_binomial (n : ℕ) :
    (subsetLaw n).map (Finset.card : Finset ℕ+ → ℕ) =
      binomial n ⟨1 / 2, by constructor <;> norm_num⟩ := by
  have hm : Measurable (Finset.card : Finset ℕ+ → ℕ) := measurable_of_countable _
  let : IsProbabilityMeasure ((subsetLaw n).map (Finset.card : Finset ℕ+ → ℕ)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [subsetLaw_card_real, binomial_real_singleton]
  change (n.choose k : ℝ) / (2 : ℝ) ^ n =
    (n.choose k : ℝ) * (1 / 2 : ℝ) ^ k * (1 - 1 / 2 : ℝ) ^ (n - k)
  by_cases hk : k ≤ n
  · have he : k + (n - k) = n := Nat.add_sub_of_le hk
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, mul_assoc, ←pow_add, he]
    simp only [div_eq_mul_inv, one_mul, inv_pow]
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]
    simp only [Nat.cast_zero, zero_div, zero_mul]

end FinitaryPerm
