import SchubertForwardStability.StrongMixing.Inequalities.Laplace.BoundedLaplace
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Weighted log-Laplace combination

Finite Jensen, applied after normalizing each exponential by its expectation, gives
the weighted Hölder inequality for Laplace transforms of dependent random variables.
It is the aggregation step of the Bernstein inequality of Merlevède, Peligrad and Rio.
-/

open MeasureTheory
open scoped BigOperators

namespace StrongMixing

/-- Positive weights summing to one combine integrable individual exponential
transforms into an integrable transform of the sum, and bound its logarithm by the
weighted sum of the individual logarithms at the reciprocally scaled parameters.
The variables may be dependent. -/
theorem log_laplace_weighted_le {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (Z : ι → Ω → ℝ)
    (hZ : ∀ i ∈ s, AEMeasurable (Z i) μ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∑ i ∈ s, w i = 1) (t : ℝ)
    (hI : ∀ i ∈ s, Integrable (fun ω ↦ Real.exp (t * Z i ω / w i)) μ) :
    Integrable (fun ω ↦ Real.exp (t * ∑ i ∈ s, Z i ω)) μ ∧
      Real.log (∫ ω, Real.exp (t * ∑ i ∈ s, Z i ω) ∂μ) ≤
        ∑ i ∈ s, w i * Real.log (∫ ω, Real.exp (t * Z i ω / w i) ∂μ) := by
  classical
  let L (i : ι) := Real.log (∫ ω, Real.exp (t * Z i ω / w i) ∂μ)
  let C : ℝ := ∑ i ∈ s, w i * L i
  let H (i : ι) (ω : Ω) := w i * Real.exp (-L i) * Real.exp (t * Z i ω / w i)
  have hHi (i : ι) (hi : i ∈ s) : Integrable (H i) μ :=
    (hI i hi).const_mul (w i * Real.exp (-L i))
  have hHmean (i : ι) (hi : i ∈ s) : (∫ ω, H i ω ∂μ) = w i := by
    have hp := integral_exp_pos (hI i hi)
    dsimp [H, L]
    rw [integral_const_mul, Real.exp_neg, Real.exp_log hp]
    field_simp
  have hsum (ω : Ω) : (∑ i ∈ s, w i * (t * Z i ω / w i - L i)) =
      t * ∑ i ∈ s, Z i ω - C := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hwi := (hw i hi).ne'
    field_simp
  have hj (ω : Ω) : Real.exp (t * ∑ i ∈ s, Z i ω - C) ≤ ∑ i ∈ s, H i ω := by
    have hp := convexOn_exp.map_sum_le (t := s) (w := w)
      (p := fun i ↦ t * Z i ω / w i - L i) (fun i hi ↦ (hw i hi).le) hw1
      (fun _ _ ↦ Set.mem_univ _)
    simp only [smul_eq_mul, hsum] at hp
    convert hp using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [H]
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  let R : Ω → ℝ := fun ω ↦ Real.exp (t * ∑ i ∈ s, Z i ω)
  let D : Ω → ℝ := fun ω ↦ Real.exp C * ∑ i ∈ s, H i ω
  have hD : Integrable D μ := (integrable_finsetSum s hHi).const_mul (Real.exp C)
  have hr : AEMeasurable R μ := by
    simpa [R, Finset.sum_apply] using ((s.aemeasurable_sum hZ).const_mul t).exp
  have hb (ω : Ω) : R ω ≤ D ω := by
    calc
      R ω = Real.exp C * Real.exp (t * ∑ i ∈ s, Z i ω - C) := by
        rw [← Real.exp_add]
        dsimp [R]
        congr 1
        ring
      _ ≤ D ω := mul_le_mul_of_nonneg_left (hj ω) (Real.exp_pos _).le
  have hR : Integrable R μ := hD.mono' hr.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by
      change |Real.exp (t * ∑ i ∈ s, Z i ω)| ≤ D ω
      rw [abs_of_pos (Real.exp_pos _)]
      exact hb ω)
  have heD : (∫ ω, D ω ∂μ) = Real.exp C := by
    change (∫ ω, Real.exp C * ∑ i ∈ s, H i ω ∂μ) = _
    rw [integral_const_mul, integral_finsetSum s hHi]
    rw [Finset.sum_congr rfl hHmean]
    rw [hw1, mul_one]
  refine ⟨hR, (Real.log_le_iff_le_exp (integral_exp_pos hR)).mpr ?_⟩
  exact (integral_mono_ae hR hD (Filter.Eventually.of_forall hb)).trans heD.le

end StrongMixing
