import SchubertForwardStability.LimitTheorems.CentralLimit.Truncation
import SchubertForwardStability.LimitTheorems.CentralLimit.GaussianError

/-! # Lindeberg estimates for finite rows

## Main results

* `sum_second_sq_le_tail`: tail moments control squared row variances.
* `tendsto_second_sq_lindeberg`: Lindeberg decay forces infinitesimality.
* `norm_charFun_prod_truncated_le`: the normalized row error is controlled by tail moments.

## Implementation notes

The row index types vary with the row; variance normalization is eventual.
-/

open MeasureTheory Filter Complex
open scoped Topology

namespace LimitTheorems

/-- In a probability row with total second moment one, squared second moments sum to
at most the threshold square plus the total tail second moment. -/
theorem sum_second_sq_le_tail {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hint : ∀ i, MemLp id 2 (μ i))
    (hsecond : (∑ i, ∫ x, x ^ 2 ∂μ i) = 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ i, (∫ x, x ^ 2 ∂μ i) ^ 2) ≤ ε ^ 2 + ∑ i, tailSecond (μ i) ε := by
  classical
  have hnonneg (i : ι) : 0 ≤ ∫ x, x ^ 2 ∂μ i := integral_nonneg (fun _ ↦ sq_nonneg _)
  have htail (i : ι) : tailSecond (μ i) ε ≤ ∑ j, tailSecond (μ j) ε :=
    Finset.single_le_sum (f := fun j : ι ↦ tailSecond (μ j) ε)
      (fun j _ ↦ tailSecond_nonneg (μ j) ε) (Finset.mem_univ i)
  have hi (i : ι) : (∫ x, x ^ 2 ∂μ i) ≤ ε ^ 2 + ∑ j, tailSecond (μ j) ε :=
    (second_moment_le_tail (hint i) hε).trans (add_le_add (le_refl _) (htail i))
  calc
    _ ≤ ∑ i, (ε ^ 2 + ∑ j, tailSecond (μ j) ε) * (∫ x, x ^ 2 ∂μ i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hi i) (hnonneg i)
    _ = _ := by rw [← Finset.mul_sum, hsecond, mul_one]

/-- Lindeberg tail decay and eventual total variance one imply that the sum of squared
individual second moments tends to zero, for arbitrary varying finite rows. -/
theorem tendsto_second_sq_lindeberg {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (μ : (n : ℕ) → ι n → Measure ℝ) [∀ n i, IsProbabilityMeasure (μ n i)]
    (hint : ∀ n i, MemLp id 2 (μ n i))
    (hsecond : ∀ᶠ n in atTop, (∑ i, ∫ x, x ^ 2 ∂μ n i) = 1)
    (htail : ∀ ε > 0, Tendsto (fun n ↦ ∑ i, tailSecond (μ n i) ε) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i, (∫ x, x ^ 2 ∂μ n i) ^ 2) atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  · intro b hb
    let ε : ℝ := Real.sqrt (b / 2)
    have hε : 0 < ε := Real.sqrt_pos.mpr (half_pos hb)
    have hsquare : ε ^ 2 = b / 2 := Real.sq_sqrt (half_pos hb).le
    filter_upwards [(htail ε hε).eventually (gt_mem_nhds (half_pos hb)), hsecond]
      with n hn hv
    have hbound := sum_second_sq_le_tail (μ n) (hint n) hv hε.le
    rw [hsquare] at hbound
    linarith

/-- A normalized row of centered square-integrable laws has Gaussian comparison error
bounded by the threshold, the total tail second moment, and squared second moments. -/
theorem norm_charFun_prod_truncated_le {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hint : ∀ i, MemLp id 2 (μ i))
    (hmean : ∀ i, (∫ x, x ∂μ i) = 0)
    (hsecond : (∑ i, ∫ x, x ^ 2 ∂μ i) = 1) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    ‖(∏ i, charFun (μ i) t) - exp (-((t ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      |t| ^ 3 / 2 * ε + 3 * t ^ 2 / 2 * (∑ i, tailSecond (μ i) ε) +
        t ^ 4 / 4 * (∑ i, (∫ x, x ^ 2 ∂μ i) ^ 2) := by
  have hb := norm_charFun_prod_of_error_le μ
    (fun i ↦ |t| ^ 3 / 2 * ε * (∫ x, x ^ 2 ∂μ i) + 3 * t ^ 2 / 2 * tailSecond (μ i) ε)
    t hsecond (fun i ↦ norm_charFun_truncated_le (hint i) (hmean i) hε t)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hsecond, mul_one] using hb

end LimitTheorems
