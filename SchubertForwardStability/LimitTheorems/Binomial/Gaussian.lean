import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! # Symmetric-binomial Gaussian limit

The centered binomial characteristic function is the nth power of the
characteristic function of a symmetric two-point law. Its mean is zero and
second moment is one, so the characteristic-function central limit theorem
gives convergence of the normalized binomial laws to the standard Gaussian.

## Main results

* `binomial_rademacher_charFun`: the characteristic-function power identity.
* `tendsto_binomial_gaussian`: convergence to the standard Gaussian law.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology BigOperators Classical

namespace LimitTheorems

/-- The symmetric Bernoulli parameter in the unit interval. -/
noncomputable def binomialHalf : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

private theorem half_weight (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) * (binomialHalf : ℝ) ^ k * (1 - (binomialHalf : ℝ)) ^ (n - k) =
      (n.choose k : ℝ) / 2 ^ n := by
  norm_num only [binomialHalf, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  rw [mul_assoc, ←pow_add, Nat.add_sub_of_le hk, one_div_pow]
  ring

private theorem half_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (n : ℕ) (f : ℕ → E) :
    (∫ k, f k ∂binomial n binomialHalf) =
      ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) / 2 ^ n) • f k := by
  rw [integral_binomial, ←Nat.range_succ_eq_Iic]
  apply Finset.sum_congr rfl
  intro k hk
  rw [half_weight n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]

private theorem rademacher_mean :
    (∫ k, (2 * (k : ℝ) - 1) ∂binomial 1 binomialHalf) = 0 := by
  rw [half_integral]
  norm_num [Finset.sum_range_succ]

private theorem rademacher_second :
    (∫ k, (2 * (k : ℝ) - 1) ^ 2 ∂binomial 1 binomialHalf) = 1 := by
  rw [half_integral]
  norm_num [Finset.sum_range_succ]

private theorem half_charFun (n : ℕ) (f : ℕ → ℝ) (t : ℝ) :
    charFun ((binomial n binomialHalf).map f) t =
      ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℂ) / 2 ^ n) *
        Complex.exp (t * f k * I) := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop), half_integral]
  apply Finset.sum_congr rfl
  intro k _
  simp [Complex.real_smul]

/-- The centered binomial characteristic function is a Rademacher power. -/
theorem binomial_rademacher_charFun (n : ℕ) (t : ℝ) :
    charFun ((binomial n binomialHalf).map (fun k : ℕ => 2 * (k : ℝ) - n)) t =
      (charFun ((binomial 1 binomialHalf).map (fun k : ℕ => 2 * (k : ℝ) - 1)) t) ^ n := by
  have hr : charFun ((binomial 1 binomialHalf).map
      (fun k : ℕ => 2 * (k : ℝ) - 1)) t =
      (1 / 2 : ℂ) * Complex.exp (-t * I) + (1 / 2) * Complex.exp (t * I) := by
    rw [half_charFun]
    norm_num [Finset.sum_range_succ]
  rw [half_charFun, hr]
  have he (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      Complex.exp (t * I) ^ k * Complex.exp (-t * I) ^ (n - k) =
        Complex.exp (t * (2 * (k : ℝ) - n) * I) := by
    rw [←Complex.exp_nat_mul, ←Complex.exp_nat_mul, ←Complex.exp_add]
    congr 1
    rw [Nat.cast_sub (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    push_cast
    ring
  rw [show (1 / (2 : ℂ)) * Complex.exp (-t * I) +
      (1 / 2) * Complex.exp (t * I) =
      (Complex.exp (t * I) + Complex.exp (-t * I)) / 2 by ring]
  rw [div_pow, add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [he k hk]
  push_cast
  ring

/-- The normalized symmetric-binomial laws converge to the standard Gaussian law. -/
theorem tendsto_binomial_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (k : ℕ) => (2 * (k : ℝ) - n) / Real.sqrt n) atTop
      (id : ℝ → ℝ) (fun n => binomial n binomialHalf) (gaussianReal 0 1) where
  forall_aemeasurable n := by fun_prop
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    have hc := tendsto_charFun_inv_sqrt_mul_pow
      (P := binomial 1 binomialHalf) (X := fun k : ℕ => 2 * (k : ℝ) - 1)
      (by fun_prop) rademacher_mean rademacher_second t
    have he (n : ℕ) :
        charFun ((binomial n binomialHalf).map
          (fun k : ℕ => (2 * (k : ℝ) - n) / Real.sqrt n)) t =
        (charFun ((binomial 1 binomialHalf).map
          (fun k : ℕ => 2 * (k : ℝ) - 1)) ((Real.sqrt n)⁻¹ * t)) ^ n := by
      rw [show (fun k : ℕ => (2 * (k : ℝ) - n) / Real.sqrt n) =
        (fun k : ℕ => (Real.sqrt n)⁻¹ * (2 * (k : ℝ) - n)) by
          funext k
          ring]
      rw [charFun_map_mul_comp (by fun_prop), binomial_rademacher_charFun]
    simpa [he, charFun_gaussianReal, neg_div] using hc

end LimitTheorems
