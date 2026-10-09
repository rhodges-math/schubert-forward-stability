import SchubertForwardStability.Permutations.Random.CardLaw
import SchubertForwardStability.Permutations.ForMathlib.UniformFinite
import Mathlib.Probability.Moments.Basic
import Mathlib.Data.Nat.Choose.Sum

/-! # Exponential upper tails of sampled cardinalities

## Main results

Finite binomial averaging evaluates the cardinality moment generating function
at the logarithm of three. Chernoff's inequality gives a uniform extreme-tail
bound with a strictly positive exponential rate.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal

namespace FinitaryPerm

/-- Every real function is integrable under the finite admissible-subset law. -/
theorem integrable_subsetLaw (n : ℕ) (f : Finset ℕ+ → ℝ) :
    Integrable f (subsetLaw n) := by
  have hf : IntegrableOn f ((positions n).powerset : Set (Finset ℕ+)) Measure.count := by
    rw [←((positions n).powerset : Set (Finset ℕ+)).biUnion_of_singleton,
      integrableOn_finite_biUnion (positions n).powerset.finite_toSet]
    intro V _
    exact integrableOn_singleton (hx := by simp)
  rw [subsetLaw, uniformOn, ProbabilityTheory.cond]
  apply hf.smul_measure
  rw [Measure.count_apply_finset, Finset.card_powerset, card_positions]
  simp

/-- The cardinality MGF at `log 3` is exactly `2^n`. -/
theorem subsetLaw_card_mgf_log_three (n : ℕ) :
    mgf (fun V : Finset ℕ+ => (V.card : ℝ)) (subsetLaw n) (Real.log 3) =
      (2 : ℝ) ^ n := by
  rw [mgf, subsetLaw, integral_uniform_finset, Finset.card_powerset, card_positions]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have he (V : Finset ℕ+) : Real.exp (Real.log 3 * (V.card : ℝ)) = (3 : ℝ) ^ V.card := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  simp_rw [he]
  rw [sum_subset_sizes]
  simp only [nsmul_eq_mul]
  have hs : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (3 : ℝ) ^ k) =
      (4 : ℝ) ^ n := by
    simpa only [one_pow, mul_one, one_mul, show (3 : ℝ) + 1 = 4 by norm_num,
      mul_comm] using
      (add_pow (3 : ℝ) 1 n).symm
  rw [hs, ←div_eq_inv_mul, ←div_pow]
  norm_num

/-- The cardinality upper-tail exponential rate is strictly positive. -/
theorem card_tail_rate_pos : 0 < (3 / 4 : ℝ) * Real.log 3 - Real.log 2 := by
  have h : Real.log ((2 : ℝ) ^ 4) < Real.log ((3 : ℝ) ^ 3) := by
    apply Real.log_lt_log <;> norm_num
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

/-- Sampled size at least three quarters of the ambient size has exponential probability. -/
theorem subsetLaw_card_extreme_tail (n : ℕ) :
    (subsetLaw n).real {V | (3 : ℝ) * n / 4 ≤ V.card} ≤
      Real.exp (-((3 / 4 : ℝ) * Real.log 3 - Real.log 2) * n) := by
  have h := measure_ge_le_exp_mul_mgf
    (X := fun V : Finset ℕ+ => (V.card : ℝ)) (μ := subsetLaw n)
    ((3 : ℝ) * n / 4) (t := Real.log 3)
    (Real.log_nonneg (by norm_num))
    (integrable_subsetLaw n (fun V => Real.exp (Real.log 3 * (V.card : ℝ))))
  rw [subsetLaw_card_mgf_log_three] at h
  have he : Real.exp (-Real.log 3 * ((3 : ℝ) * n / 4)) * (2 : ℝ) ^ n =
      Real.exp (-((3 / 4 : ℝ) * Real.log 3 - Real.log 2) * n) := by
    have hp : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [hp, ←Real.exp_add]
    congr 1
    ring
  exact h.trans_eq he

end FinitaryPerm
