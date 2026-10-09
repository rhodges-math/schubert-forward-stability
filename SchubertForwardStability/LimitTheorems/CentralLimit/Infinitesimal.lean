import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-! # Infinitesimality from third absolute moments

## Main results

* `second_moment_le_third`: a truncation bound for second moments.
* `sum_second_sq_le_third`: a finite-row bound when total second moment is one.
* `tendsto_sum_second_sq`: vanishing total third moment implies vanishing sum of
  squared second moments, even for varying row index types.

## Implementation notes

The bounds split at a positive real threshold; no inequalities between fractional
moments are needed.
-/

open MeasureTheory Filter
open scoped Topology

namespace LimitTheorems

/-- A positive threshold bounds the second moment by its square plus the third absolute
moment divided by the threshold. -/
theorem second_moment_le_third {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 3 μ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x, x ^ 2 ∂μ) ≤ ε ^ 2 + (∫ x, |x| ^ 3 ∂μ) / ε := by
  have hsecond : Integrable (fun x : ℝ ↦ x ^ 2) μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mp (hint.mono_exponent (by norm_num))
  have hthird : Integrable (fun x : ℝ ↦ |x| ^ 3) μ := by
    simpa only [id_eq, Real.norm_eq_abs] using hint.integrable_norm_pow'
  have hpoint (x : ℝ) : x ^ 2 ≤ ε ^ 2 + |x| ^ 3 / ε := by
    by_cases hx : |x| ≤ ε
    · have hx2 : x ^ 2 ≤ ε ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
      exact hx2.trans (le_add_of_nonneg_right (by positivity))
    · have hcube : x ^ 2 * ε ≤ |x| ^ 3 := by
        calc
          x ^ 2 * ε = |x| ^ 2 * ε := by rw [sq_abs]
          _ ≤ |x| ^ 2 * |x| := mul_le_mul_of_nonneg_left (not_le.mp hx).le (sq_nonneg _)
          _ = |x| ^ 3 := by ring
      exact ((le_div_iff₀ hε).mpr hcube).trans (le_add_of_nonneg_left (sq_nonneg ε))
  have hbound := integral_mono_ae hsecond
    ((integrable_const (ε ^ 2)).add (hthird.div_const ε))
    (Eventually.of_forall hpoint)
  rw [integral_add' (integrable_const (ε ^ 2)) (hthird.div_const ε)] at hbound
  simpa only [integral_const, probReal_univ, one_smul, integral_div] using hbound

/-- In a row with total second moment one, the sum of squared second moments is bounded
by the threshold square plus the total third absolute moment divided by the threshold. -/
theorem sum_second_sq_le_third {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hint : ∀ i, MemLp id 3 (μ i))
    (hsecond : (∑ i, ∫ x, x ^ 2 ∂μ i) = 1) {ε : ℝ} (hε : 0 < ε) :
    (∑ i, (∫ x, x ^ 2 ∂μ i) ^ 2) ≤
      ε ^ 2 + (∑ i, ∫ x, |x| ^ 3 ∂μ i) / ε := by
  classical
  have hnonneg (i : ι) : 0 ≤ ∫ x, x ^ 2 ∂μ i := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hthird (i : ι) : (∫ x, |x| ^ 3 ∂μ i) ≤ ∑ j, ∫ x, |x| ^ 3 ∂μ j :=
    Finset.single_le_sum (f := fun j : ι ↦ ∫ x : ℝ, |x| ^ 3 ∂μ j)
      (fun j _ ↦ integral_nonneg (fun x ↦ pow_nonneg (abs_nonneg x) 3)) (Finset.mem_univ i)
  have hi (i : ι) : (∫ x, x ^ 2 ∂μ i) ≤
      ε ^ 2 + (∑ j, ∫ x, |x| ^ 3 ∂μ j) / ε :=
    (second_moment_le_third (hint i) hε).trans (by gcongr; exact hthird i)
  calc
    (∑ i, (∫ x, x ^ 2 ∂μ i) ^ 2) ≤
        ∑ i, (ε ^ 2 + (∑ j, ∫ x, |x| ^ 3 ∂μ j) / ε) * (∫ x, x ^ 2 ∂μ i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hi i) (hnonneg i)
    _ = ε ^ 2 + (∑ i, ∫ x, |x| ^ 3 ∂μ i) / ε := by
      rw [← Finset.mul_sum, hsecond, mul_one]

/-- For probability rows normalized to total second moment one, vanishing total third
absolute moment forces the sum of squared second moments to vanish. -/
theorem tendsto_sum_second_sq {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (μ : (n : ℕ) → ι n → Measure ℝ) [∀ n i, IsProbabilityMeasure (μ n i)]
    (hint : ∀ n i, MemLp id 3 (μ n i))
    (hsecond : ∀ᶠ n in atTop, (∑ i, ∫ x, x ^ 2 ∂μ n i) = 1)
    (hthird : Tendsto (fun n ↦ ∑ i, ∫ x, |x| ^ 3 ∂μ n i) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i, (∫ x, x ^ 2 ∂μ n i) ^ 2) atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  · intro b hb
    let ε : ℝ := Real.sqrt (b / 2)
    have hε : 0 < ε := Real.sqrt_pos.mpr (half_pos hb)
    have hsquare : ε ^ 2 = b / 2 := Real.sq_sqrt (half_pos hb).le
    have hscaled : Tendsto (fun n ↦ (∑ i, ∫ x, |x| ^ 3 ∂μ n i) / ε) atTop (𝓝 0) := by
      simpa only [zero_div] using hthird.div_const ε
    filter_upwards [hscaled.eventually (gt_mem_nhds (half_pos hb)), hsecond] with n hn hv
    have hbound := sum_second_sq_le_third (μ n) (hint n) hv hε
    rw [hsquare] at hbound
    linarith

end LimitTheorems
