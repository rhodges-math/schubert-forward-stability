import SchubertForwardStability.LimitTheorems.CentralLimit.RowBounds
import SchubertForwardStability.LimitTheorems.CentralLimit.Infinitesimal
import SchubertForwardStability.LimitTheorems.CentralLimit.Lindeberg
import SchubertForwardStability.LimitTheorems.CentralLimit.ThirdMomentTail
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction

/-! # Lyapunov convergence for varying finite rows

## Main results

* `tendsto_charFun_prod`: vanishing total third moment gives Gaussian convergence
  of products of characteristic functions.
* `tendstoInDistribution_lyapunov`: the third-moment Lyapunov central limit theorem
  for centered, normalized triangular arrays on varying probability spaces.

## Implementation notes

The row index types may vary and need only be finite. Total second moment equals
one eventually; initial zero-variance rows therefore cause no restriction.

## References

* P. Billingsley, *Probability and Measure*, third edition, Theorem 27.3.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology

namespace LimitTheorems

/-- Characteristic-function products of centered probability rows tend to the standard
Gaussian function under third-moment Lyapunov decay and eventual variance normalization. -/
theorem tendsto_charFun_prod {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (μ : (n : ℕ) → ι n → Measure ℝ) [∀ n i, IsProbabilityMeasure (μ n i)]
    (hint : ∀ n i, MemLp id 3 (μ n i)) (hmean : ∀ n i, (∫ x, x ∂μ n i) = 0)
    (hsecond : ∀ᶠ n in atTop, (∑ i, ∫ x, x ^ 2 ∂μ n i) = 1)
    (hthird : Tendsto (fun n ↦ ∑ i, ∫ x, |x| ^ 3 ∂μ n i) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n ↦ ∏ i, charFun (μ n i) t) atTop
      (𝓝 (exp (-((t ^ 2 / 2 : ℝ) : ℂ)))) := by
  exact tendsto_charFun_prod_lindeberg μ
    (fun n i ↦ (hint n i).mono_exponent (by norm_num)) hmean hsecond
    (fun _ hε ↦ tendsto_tailSecond_third μ hint hthird hε) t

/-- **Lyapunov's central limit theorem with exponent three.** For independent centered
finite rows, eventual total variance one and vanishing total third absolute moment imply
convergence of the row sums to the standard Gaussian law. The source spaces and row index
types may vary with the row. See Billingsley, *Probability and Measure*, Theorem 27.3. -/
theorem tendstoInDistribution_lyapunov {Ω ι : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, Fintype (ι n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → ι n → Ω n → ℝ}
    (hint : ∀ n i, MemLp (X n i) 3 (P n))
    (hmean : ∀ n i, (∫ ω, X n i ω ∂P n) = 0)
    (hsecond : ∀ᶠ n in atTop, (∑ i, ∫ ω, (X n i ω) ^ 2 ∂P n) = 1)
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hthird : Tendsto (fun n ↦ ∑ i, ∫ ω, |X n i ω| ^ 3 ∂P n) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω ↦ ∑ i, X n i ω) atTop id P (gaussianReal 0 1) := by
  classical
  have hm (n : ℕ) (i : ι n) : AEMeasurable (X n i) (P n) :=
    (hint n i).aestronglyMeasurable.aemeasurable
  let μ (n : ℕ) (i : ι n) : Measure ℝ := (P n).map (X n i)
  have hlp (n : ℕ) (i : ι n) : MemLp id 3 (μ n i) := by
    exact (memLp_map_measure_iff (by fun_prop) (hm n i)).mpr (by
      simpa only [Function.comp_def, id_eq] using hint n i)
  have hfirst (n : ℕ) (i : ι n) : (∫ x, x ∂μ n i) = ∫ ω, X n i ω ∂P n :=
    integral_map (hm n i) (by fun_prop)
  have hvariance (n : ℕ) (i : ι n) :
      (∫ x, x ^ 2 ∂μ n i) = ∫ ω, (X n i ω) ^ 2 ∂P n :=
    integral_map (hm n i) (by fun_prop)
  have habsolute (n : ℕ) (i : ι n) :
      (∫ x, |x| ^ 3 ∂μ n i) = ∫ ω, |X n i ω| ^ 3 ∂P n :=
    integral_map (hm n i) (by fun_prop)
  have hv : ∀ᶠ n in atTop, (∑ i, ∫ x, x ^ 2 ∂μ n i) = 1 := by
    simpa only [hvariance] using hsecond
  have ht : Tendsto (fun n ↦ ∑ i, ∫ x, |x| ^ 3 ∂μ n i) atTop (𝓝 0) := by
    simpa only [habsolute] using hthird
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
    tendsto_charFun_prod μ hlp (fun n i ↦ (hfirst n i).trans (hmean n i)) hv ht t

end LimitTheorems
