import SchubertForwardStability.LimitTheorems.CentralLimit.Truncation

/-! # Third moments imply the Lindeberg tail condition

## Main results

* `tailSecond_le_third`: the third absolute moment controls a positive-threshold tail.
* `tendsto_tailSecond_third`: third-moment Lyapunov decay implies Lindeberg decay.

## Implementation notes

These estimates require neither independence nor centering nor variance normalization.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace LimitTheorems

/-- A third absolute moment bounds the second moment above a positive threshold,
divided by that threshold. -/
theorem tailSecond_le_third {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 3 μ) {ε : ℝ} (hε : 0 < ε) :
    tailSecond μ ε ≤ (∫ x, |x| ^ 3 ∂μ) / ε := by
  have hsecond : Integrable (fun x : ℝ ↦ x ^ 2) μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mp (hint.mono_exponent (by norm_num))
  have hthird : Integrable (fun x : ℝ ↦ |x| ^ 3) μ := by
    simpa only [id_eq, Real.norm_eq_abs] using hint.integrable_norm_pow'
  have hset : MeasurableSet {x : ℝ | ε < |x|} := by measurability
  have hpoint (x : ℝ) : {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) x ≤ |x| ^ 3 / ε := by
    by_cases hx : ε < |x|
    · rw [indicator_of_mem (show x ∈ {x : ℝ | ε < |x|} from hx)]
      apply (le_div_iff₀ hε).mpr
      calc
        x ^ 2 * ε ≤ x ^ 2 * |x| := mul_le_mul_of_nonneg_left hx.le (sq_nonneg x)
        _ = |x| ^ 3 := by rw [← sq_abs x]; ring
    · rw [indicator_of_notMem (show x ∉ {x : ℝ | ε < |x|} from hx)]
      positivity
  have hb := integral_mono_ae (hsecond.indicator hset) (hthird.div_const ε)
    (Eventually.of_forall hpoint)
  simpa only [tailSecond, integral_div] using hb

/-- Vanishing total third absolute moment in varying finite probability rows implies
vanishing total tail second moment at every fixed positive threshold. -/
theorem tendsto_tailSecond_third {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (μ : (n : ℕ) → ι n → Measure ℝ) [∀ n i, IsProbabilityMeasure (μ n i)]
    (hint : ∀ n i, MemLp id 3 (μ n i))
    (hthird : Tendsto (fun n ↦ ∑ i, ∫ x, |x| ^ 3 ∂μ n i) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ ∑ i, tailSecond (μ n i) ε) atTop (𝓝 0) := by
  have hscaled : Tendsto (fun n ↦ (∑ i, ∫ x, |x| ^ 3 ∂μ n i) / ε) atTop (𝓝 0) := by
    simpa only [zero_div] using hthird.div_const ε
  refine squeeze_zero (fun n ↦ Finset.sum_nonneg (fun i _ ↦ tailSecond_nonneg (μ n i) ε))
    (fun n ↦ ?_) hscaled
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun i _ ↦ tailSecond_le_third (hint n i) hε)

end LimitTheorems
