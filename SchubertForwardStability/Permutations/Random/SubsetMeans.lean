import SchubertForwardStability.Permutations.Random.PairWeights
import SchubertForwardStability.Permutations.Random.SubsetMaximum
import SchubertForwardStability.Permutations.ForMathlib.UniformFinite

/-! # Exact finite means of uniform subsets

## Main results

The selected maximum and the maximum of two independently sampled cardinalities
have exact finite averages, including the empty ambient interval.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace FinitaryPerm

/-- The expected maximum selected position is `n-1+2^(-n)`, also for size zero. -/
theorem subsetLaw_maximum_mean (n : ℕ) :
    (∫ V, ((V.sup PNat.val : ℕ) : ℝ) ∂subsetLaw n) =
      (n : ℝ) - 1 + ((2 : ℝ) ^ n)⁻¹ := by
  rw [subsetLaw, integral_uniform_finset, Finset.card_powerset, card_positions]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have h : (∑ V ∈ (positions n).powerset, ((V.sup PNat.val : ℕ) : ℝ)) + (2 : ℝ) ^ n =
      (n : ℝ) * (2 : ℝ) ^ n + 1 := by
    exact_mod_cast sum_subset_maximum_closed n
  have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  nlinarith

/-- The maximum of two sampled sizes has a closed central-binomial mean. -/
theorem subsetLaw_pair_card_max_mean (n : ℕ) :
    (∫ p, (max p.1.card p.2.card : ℝ) ∂(subsetLaw n).prod (subsetLaw n)) =
      (n : ℝ) / 2 + ((n : ℝ) / 2) * ((2 * n).choose n : ℝ) / (4 : ℝ) ^ n := by
  rw [subsetLaw, ←uniformOn_finset_prod, integral_uniform_product,
    Finset.card_powerset, card_positions]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have h : 2 * (∑ V ∈ (positions n).powerset, ∑ W ∈ (positions n).powerset,
      (max V.card W.card : ℝ)) =
      (n : ℝ) * (4 : ℝ) ^ n + (n : ℝ) * ((2 * n).choose n : ℝ) := by
    exact_mod_cast sum_subset_pair_max_twice n
  rw [←mul_pow, show (2 : ℝ) * 2 = 4 by norm_num]
  have hp : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  nlinarith

end FinitaryPerm
