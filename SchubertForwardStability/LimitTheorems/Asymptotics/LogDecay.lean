import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-!
# Logarithmic Exponential Decay

This file contains general results that extend Mathlib: the function
`x*exp(-c*x/(log(x)*log(log(x))))` is eventually at most `1/x^2`, so its values at the natural
numbers form a summable series for every `c > 0`.
-/

open Filter Asymptotics
open scoped Topology

namespace LimitTheorems

/-- Logarithmic exponential decay eventually dominates an inverse-square bound. -/
theorem eventually_logDecay_le_invSq {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      x * Real.exp (-(c * x / (Real.log x * Real.log (Real.log x)))) ≤ (x ^ 2)⁻¹ := by
  have hsmall :
      ∀ᶠ x : ℝ in atTop, |Real.log x ^ 3| ≤ c / 3 * |x| := by
    simpa only [Real.rpow_ofNat, Real.rpow_one, Real.norm_eq_abs] using
      (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (s := 1) (by norm_num)).bound
        (show 0 < c / 3 by positivity)
  filter_upwards [hsmall, Real.tendsto_log_atTop.eventually_ge_atTop 2,
    eventually_gt_atTop (0 : ℝ)] with x hsmall hlog hx
  have hl : 0 < Real.log x := by linarith
  have hll : 0 < Real.log (Real.log x) := Real.log_pos (by linarith)
  have hll_le : Real.log (Real.log x) ≤ Real.log x :=
    Real.log_le_self hl.le
  rw [abs_of_nonneg (by positivity), abs_of_pos hx] at hsmall
  have hcubic : 3 * Real.log x ^ 3 ≤ c * x := by nlinarith [hsmall]
  have hfactor := mul_le_mul_of_nonneg_left hll_le (sq_nonneg (Real.log x))
  have hden : 0 < Real.log x * Real.log (Real.log x) := mul_pos hl hll
  have hdiv : 3 * Real.log x ≤ c * x / (Real.log x * Real.log (Real.log x)) := by
    apply (le_div_iff₀ hden).2
    nlinarith [hfactor, hcubic]
  have hexp :
      Real.exp (-(c * x / (Real.log x * Real.log (Real.log x)))) ≤ (x ^ 3)⁻¹ := by
    calc
      _ ≤ Real.exp (-(3 * Real.log x)) := Real.exp_le_exp.mpr (neg_le_neg hdiv)
      _ = (x ^ 3)⁻¹ := by
        have hp : Real.log (x ^ 3) = 3 * Real.log x := by
          simp
        rw [← hp, Real.exp_neg, Real.exp_log (pow_pos hx 3)]
  calc
    _ ≤ x * (x ^ 3)⁻¹ := mul_le_mul_of_nonneg_left hexp hx.le
    _ = (x ^ 2)⁻¹ := by field_simp

/-- The logarithmic-exponential tail series is summable for every positive decay rate. -/
theorem summable_nat_logDecay {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ =>
      (n : ℝ) * Real.exp (-(c * n / (Real.log n * Real.log (Real.log n))))) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  refine summable_of_isBigO_nat hs (.of_norm_eventuallyLE ?_)
  have he : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.exp (-(c * n / (Real.log n * Real.log (Real.log n)))) ≤
        ((n : ℝ) ^ 2)⁻¹ :=
    tendsto_natCast_atTop_atTop.eventually (eventually_logDecay_le_invSq hc)
  filter_upwards [he] with n hn
  rw [Real.norm_of_nonneg (by positivity)]
  exact hn

end LimitTheorems
