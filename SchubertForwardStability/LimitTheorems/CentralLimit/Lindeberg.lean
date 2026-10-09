import SchubertForwardStability.LimitTheorems.CentralLimit.TruncatedRows
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction

/-! # Lindeberg convergence for varying finite rows

## Main results

* `tendsto_charFun_prod_lindeberg`: Lindeberg tail decay gives Gaussian convergence of products.
* `tendstoInDistribution_lindeberg`: the square-integrable triangular-array central limit theorem.

## Implementation notes

The row spaces and finite row index types may vary. Total variance is one only eventually.
Tail moments use strict inequalities; their decay is required at every positive threshold.

## References

* P. Billingsley, *Probability and Measure*, third edition, Theorem 27.2.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology

namespace LimitTheorems

/-- For centered square-integrable probability rows, eventual variance one and Lindeberg
tail decay force characteristic-function products to converge to the standard Gaussian. -/
theorem tendsto_charFun_prod_lindeberg {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (μ : (n : ℕ) → ι n → Measure ℝ) [∀ n i, IsProbabilityMeasure (μ n i)]
    (hint : ∀ n i, MemLp id 2 (μ n i)) (hmean : ∀ n i, (∫ x, x ∂μ n i) = 0)
    (hsecond : ∀ᶠ n in atTop, (∑ i, ∫ x, x ^ 2 ∂μ n i) = 1)
    (htail : ∀ ε > 0, Tendsto (fun n ↦ ∑ i, tailSecond (μ n i) ε) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n ↦ ∏ i, charFun (μ n i) t) atTop
      (𝓝 (exp (-((t ^ 2 / 2 : ℝ) : ℂ)))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hvariance := tendsto_second_sq_lindeberg μ hint hsecond htail
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun _ ↦ ha.trans_le (norm_nonneg _)
  · intro b hb
    let c : ℝ := |t| ^ 3 / 2
    have hc : 0 < c + 1 := by dsimp only [c]; positivity
    let ε : ℝ := b / (2 * (c + 1))
    have hε : 0 < ε := div_pos hb (mul_pos (by norm_num) hc)
    have hsmall : c * ε < b / 2 := by
      calc
        c * ε < (c + 1) * ε := mul_lt_mul_of_pos_right (lt_add_one c) hε
        _ = b / 2 := by dsimp only [ε]; field_simp
    have hscaled : Tendsto (fun n ↦ 3 * t ^ 2 / 2 * (∑ i, tailSecond (μ n i) ε) +
        t ^ 4 / 4 * (∑ i, (∫ x, x ^ 2 ∂μ n i) ^ 2)) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using
        ((htail ε hε).const_mul (3 * t ^ 2 / 2)).add (hvariance.const_mul (t ^ 4 / 4))
    filter_upwards [hscaled.eventually (gt_mem_nhds (half_pos hb)), hsecond] with n hn hv
    have hbound := norm_charFun_prod_truncated_le (μ n) (hint n) (hmean n) hv hε.le t
    change _ ≤ c * ε + _ + _ at hbound
    linarith

/-- **Lindeberg's central limit theorem.** Independent centered square-integrable finite
rows on varying probability spaces converge to the standard Gaussian when their total
variance is eventually one and every positive-threshold total tail second moment vanishes.
See Billingsley, *Probability and Measure*, Theorem 27.2. -/
theorem tendstoInDistribution_lindeberg {Ω ι : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, Fintype (ι n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → ι n → Ω n → ℝ}
    (hint : ∀ n i, MemLp (X n i) 2 (P n))
    (hmean : ∀ n i, (∫ ω, X n i ω ∂P n) = 0)
    (hsecond : ∀ᶠ n in atTop, (∑ i, ∫ ω, (X n i ω) ^ 2 ∂P n) = 1)
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (htail : ∀ ε > 0, Tendsto (fun n ↦ ∑ i, ∫ ω,
      if ε < |X n i ω| then (X n i ω) ^ 2 else 0 ∂P n) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω ↦ ∑ i, X n i ω) atTop id P (gaussianReal 0 1) := by
  classical
  have hm (n : ℕ) (i : ι n) : AEMeasurable (X n i) (P n) :=
    (hint n i).aestronglyMeasurable.aemeasurable
  let μ (n : ℕ) (i : ι n) : Measure ℝ := (P n).map (X n i)
  have hlp (n : ℕ) (i : ι n) : MemLp id 2 (μ n i) := by
    exact (memLp_map_measure_iff (by fun_prop) (hm n i)).mpr (by
      simpa only [Function.comp_def, id_eq] using hint n i)
  have hfirst (n : ℕ) (i : ι n) : (∫ x, x ∂μ n i) = ∫ ω, X n i ω ∂P n :=
    integral_map (hm n i) (by fun_prop)
  have hvariance (n : ℕ) (i : ι n) :
      (∫ x, x ^ 2 ∂μ n i) = ∫ ω, (X n i ω) ^ 2 ∂P n :=
    integral_map (hm n i) (by fun_prop)
  have htail_map (n : ℕ) (i : ι n) (ε : ℝ) : tailSecond (μ n i) ε =
      ∫ ω, if ε < |X n i ω| then (X n i ω) ^ 2 else 0 ∂P n := by
    have hset : MeasurableSet {x : ℝ | ε < |x|} := by measurability
    have hi : AEStronglyMeasurable
        ({x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2)) (μ n i) :=
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ x ^ 2) (μ n i)).indicator hset
    rw [tailSecond, integral_map (hm n i) hi]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hv : ∀ᶠ n in atTop, (∑ i, ∫ x, x ^ 2 ∂μ n i) = 1 := by
    simpa only [hvariance] using hsecond
  have ht : ∀ ε > 0, Tendsto (fun n ↦ ∑ i, tailSecond (μ n i) ε) atTop (𝓝 0) := by
    simpa only [htail_map] using htail
  refine ⟨fun n ↦ Finset.aemeasurable_fun_sum Finset.univ (fun i _ ↦ hm n i),
    aemeasurable_id, ?_⟩
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  have hprod (n : ℕ) : charFun ((P n).map (fun ω ↦ ∑ i, X n i ω)) t =
      ∏ i, charFun (μ n i) t := by
    simpa only [Finset.prod_apply] using congrFun
      ((hindep n).charFun_map_fun_sum_eq_prod (hm n)) t
  have hgauss : charFun (gaussianReal 0 1) t = exp (-((t ^ 2 / 2 : ℝ) : ℂ)) := by
    rw [charFun_gaussianReal]
    congr 1
    norm_num
  simpa only [ProbabilityMeasure.coe_mk, Measure.map_id, hprod, hgauss] using
    tendsto_charFun_prod_lindeberg μ hlp
      (fun n i ↦ (hfirst n i).trans (hmean n i)) hv ht t

end LimitTheorems
