import SchubertForwardStability.LimitTheorems.CentralLimit.Lyapunov
import SchubertForwardStability.LimitTheorems.CentralLimit.Lindeberg
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! # Variance scaling in central limit theorems

## Main results

* `tendstoInDistribution_sum_div`: the Lyapunov theorem for sums divided by their
  standard deviation, on varying row spaces and finite index types.
* `tendstoInDistribution_lindeberg_div`: the corresponding square-integrable Lindeberg theorem.

## Implementation notes

The scale is required to be positive and to have square equal to total second
moment only eventually. Division by zero in initial rows is therefore harmless.

## References

* P. Billingsley, *Probability and Measure*, third edition, Theorem 27.3.
* P. Billingsley, *Probability and Measure*, third edition, Theorem 27.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LimitTheorems

/-- **Lyapunov's central limit theorem with exponent three and variance scaling.**
Independent centered rows, divided by an eventually positive standard deviation,
converge to the standard Gaussian when the total third absolute moment divided by
the scale cubed tends to zero. See Billingsley, *Probability and Measure*, Theorem 27.3. -/
theorem tendstoInDistribution_sum_div {Ω ι : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, Fintype (ι n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → ι n → Ω n → ℝ} {s : ℕ → ℝ}
    (hint : ∀ n i, MemLp (X n i) 3 (P n))
    (hmean : ∀ n i, (∫ ω, X n i ω ∂P n) = 0)
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hpos : ∀ᶠ n in atTop, 0 < s n)
    (hvariance : ∀ᶠ n in atTop, (s n) ^ 2 = ∑ i, ∫ ω, (X n i ω) ^ 2 ∂P n)
    (hthird : Tendsto (fun n ↦ (∑ i, ∫ ω, |X n i ω| ^ 3 ∂P n) / (s n) ^ 3)
      atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω ↦ (∑ i, X n i ω) / s n)
      atTop id P (gaussianReal 0 1) := by
  classical
  let Y (n : ℕ) (i : ι n) (ω : Ω n) : ℝ := X n i ω / s n
  have hlp (n : ℕ) (i : ι n) : MemLp (Y n i) 3 (P n) := by
    simpa only [Y, div_eq_mul_inv] using (hint n i).mul_const (s n)⁻¹
  have hcenter (n : ℕ) (i : ι n) : (∫ ω, Y n i ω ∂P n) = 0 := by
    simp only [Y, integral_div, hmean, zero_div]
  have hnormalized : ∀ᶠ n in atTop, (∑ i, ∫ ω, (Y n i ω) ^ 2 ∂P n) = 1 := by
    filter_upwards [hpos, hvariance] with n hn hv
    simp only [Y, div_pow, integral_div]
    rw [← Finset.sum_div, ← hv, div_self (pow_ne_zero 2 hn.ne')]
  have hindependent (n : ℕ) : iIndepFun (Y n) (P n) :=
    (hindep n).comp (fun _ x ↦ x / s n) (fun _ ↦ by fun_prop)
  have habsolute : Tendsto (fun n ↦ ∑ i, ∫ ω, |Y n i ω| ^ 3 ∂P n) atTop (𝓝 0) := by
    apply hthird.congr'
    filter_upwards [hpos] with n hn
    simp only [Y, abs_div, div_pow, abs_of_pos hn, integral_div, ← Finset.sum_div]
  have hlimit := tendstoInDistribution_lyapunov hlp hcenter hnormalized hindependent habsolute
  have hidentity : (fun n ω ↦ ∑ i, Y n i ω) =
      (fun n ω ↦ (∑ i, X n i ω) / s n) := by
    funext n ω
    exact (Finset.sum_div Finset.univ (fun i ↦ X n i ω) (s n)).symm
  rwa [hidentity] at hlimit

/-- **Lindeberg's central limit theorem with variance scaling.** Independent centered
square-integrable rows, divided by their eventually positive standard deviation, converge
to the standard Gaussian when the scaled tail second moment vanishes at every positive
threshold. See Billingsley, *Probability and Measure*, Theorem 27.2. -/
theorem tendstoInDistribution_lindeberg_div {Ω ι : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, Fintype (ι n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → ι n → Ω n → ℝ} {s : ℕ → ℝ}
    (hint : ∀ n i, MemLp (X n i) 2 (P n))
    (hmean : ∀ n i, (∫ ω, X n i ω ∂P n) = 0)
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hpos : ∀ᶠ n in atTop, 0 < s n)
    (hvariance : ∀ᶠ n in atTop, (s n) ^ 2 = ∑ i, ∫ ω, (X n i ω) ^ 2 ∂P n)
    (htail : ∀ ε > 0, Tendsto (fun n ↦ (∑ i, ∫ ω,
      if ε * s n < |X n i ω| then (X n i ω) ^ 2 else 0 ∂P n) / (s n) ^ 2)
      atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω ↦ (∑ i, X n i ω) / s n)
      atTop id P (gaussianReal 0 1) := by
  classical
  let Y (n : ℕ) (i : ι n) (ω : Ω n) : ℝ := X n i ω / s n
  have hlp (n : ℕ) (i : ι n) : MemLp (Y n i) 2 (P n) := by
    simpa only [Y, div_eq_mul_inv] using (hint n i).mul_const (s n)⁻¹
  have hcenter (n : ℕ) (i : ι n) : (∫ ω, Y n i ω ∂P n) = 0 := by
    simp only [Y, integral_div, hmean, zero_div]
  have hnormalized : ∀ᶠ n in atTop, (∑ i, ∫ ω, (Y n i ω) ^ 2 ∂P n) = 1 := by
    filter_upwards [hpos, hvariance] with n hn hv
    simp only [Y, div_pow, integral_div]
    rw [← Finset.sum_div, ← hv, div_self (pow_ne_zero 2 hn.ne')]
  have hindependent (n : ℕ) : iIndepFun (Y n) (P n) :=
    (hindep n).comp (fun _ x ↦ x / s n) (fun _ ↦ by fun_prop)
  have hnormalized_tail : ∀ ε > 0, Tendsto (fun n ↦ ∑ i, ∫ ω,
      if ε < |Y n i ω| then (Y n i ω) ^ 2 else 0 ∂P n) atTop (𝓝 0) := by
    intro ε hε
    apply (htail ε hε).congr'
    filter_upwards [hpos] with n hn
    have heq (i : ι n) : (fun ω ↦ if ε < |Y n i ω| then (Y n i ω) ^ 2 else 0) =
        (fun ω ↦ (if ε * s n < |X n i ω| then (X n i ω) ^ 2 else 0) / (s n) ^ 2) := by
      funext ω
      dsimp only [Y]
      simp only [abs_div, abs_of_pos hn, lt_div_iff₀ hn]
      split_ifs <;> simp only [div_pow, zero_div]
    simp only [heq, integral_div, ← Finset.sum_div]
  have hlimit := tendstoInDistribution_lindeberg hlp hcenter hnormalized
    hindependent hnormalized_tail
  have hidentity : (fun n ω ↦ ∑ i, Y n i ω) =
      (fun n ω ↦ (∑ i, X n i ω) / s n) := by
    funext n ω
    exact (Finset.sum_div Finset.univ (fun i ↦ X n i ω) (s n)).symm
  rwa [hidentity] at hlimit

end LimitTheorems
