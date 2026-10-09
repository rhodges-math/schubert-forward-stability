import SchubertForwardStability.StrongMixing.Inequalities.UnitCovariance
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Ibragimov's bounded covariance estimate

Affine normalization reduces signed bounded random variables to unit-interval-valued
variables. The event-discrepancy coefficient then bounds covariance by four times the
product of the two uniform bounds.

## References

* I. A. Ibragimov, *Some limit theorems for stationary processes*, Theory Probab. Appl. 7
  (1962), 349-382.
-/

open MeasureTheory ProbabilityTheory

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Ibragimov's covariance inequality: signed measurable variables bounded by nonnegative
constants have absolute covariance at most four times the product of these constants and
the mixing coefficient. Zero bounds are permitted. -/
theorem bounded_covariance_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : MeasurableSpace Ω) (hF : F ≤ mΩ) (hG : G ≤ mΩ)
    (f g : Ω → ℝ) (hf : @Measurable Ω ℝ F inferInstance f)
    (hg : @Measurable Ω ℝ G inferInstance g) {M N : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hfM : ∀ ω, |f ω| ≤ M) (hgN : ∀ ω, |g ω| ≤ N) :
    |(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ| ≤
      4 * M * N * strongMixingCoeff (mΩ := mΩ) μ F G := by
  have hfm : @Measurable Ω ℝ mΩ inferInstance f := hf.mono hF le_rfl
  have hgm : @Measurable Ω ℝ mΩ inferInstance g := hg.mono hG le_rfl
  have hf2 : MemLp f 2 μ := MemLp.of_bound hfm.aestronglyMeasurable M
    (Filter.Eventually.of_forall hfM)
  have hg2 : MemLp g 2 μ := MemLp.of_bound hgm.aestronglyMeasurable N
    (Filter.Eventually.of_forall hgN)
  by_cases hMz : M = 0
  · have he : f = fun _ ↦ 0 := funext fun ω ↦ abs_eq_zero.mp
      (le_antisymm (by simpa [hMz] using hfM ω) (abs_nonneg _))
    simp [he, hMz]
  by_cases hNz : N = 0
  · have he : g = fun _ ↦ 0 := funext fun ω ↦ abs_eq_zero.mp
      (le_antisymm (by simpa [hNz] using hgN ω) (abs_nonneg _))
    simp [he, hNz]
  have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hMz)
  have hNp : 0 < N := lt_of_le_of_ne hN (Ne.symm hNz)
  let u : Ω → ℝ := fun ω ↦ (f ω + M) / (2 * M)
  let v : Ω → ℝ := fun ω ↦ (g ω + N) / (2 * N)
  have hu0 : ∀ ω, 0 ≤ u ω := fun ω ↦ div_nonneg
    (by have h := (abs_le.mp (hfM ω)).1; linarith) (by positivity)
  have hu1 : ∀ ω, u ω ≤ 1 := fun ω ↦ (div_le_one (by positivity)).mpr
    (by have h := (abs_le.mp (hfM ω)).2; linarith)
  have hv0 : ∀ ω, 0 ≤ v ω := fun ω ↦ div_nonneg
    (by have h := (abs_le.mp (hgN ω)).1; linarith) (by positivity)
  have hv1 : ∀ ω, v ω ≤ 1 := fun ω ↦ (div_le_one (by positivity)).mpr
    (by have h := (abs_le.mp (hgN ω)).2; linarith)
  have hu : @Measurable Ω ℝ F inferInstance u :=
    (hf.add_const M).div_const (2 * M)
  have hv : @Measurable Ω ℝ G inferInstance v :=
    (hg.add_const N).div_const (2 * N)
  have hu2 : MemLp u 2 μ := MemLp.of_bound (hu.mono hF le_rfl).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hu0 ω)] using hu1 ω)
  have hv2 : MemLp v 2 μ := MemLp.of_bound (hv.mono hG le_rfl).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hv0 ω)] using hv1 ω)
  have hb := unit_covariance_le (mΩ := mΩ) μ F G hF hG u v hu hv hu0 hu1 hv0 hv1
  have he : covariance u v μ = covariance f g μ / (4 * M * N) := by
    dsimp [u, v]
    rw [covariance_fun_div_left, covariance_fun_div_right,
      covariance_add_const_left (hf2.integrable (by norm_num)),
      covariance_add_const_right (hg2.integrable (by norm_num))]
    field_simp; ring
  have hub := covariance_eq_sub hu2 hv2
  change covariance u v μ =
    (∫ ω, u ω * v ω ∂μ) - (∫ ω, u ω ∂μ) * ∫ ω, v ω ∂μ at hub
  rw [← hub, he, abs_div, abs_of_pos (by positivity : 0 < 4 * M * N)] at hb
  have hout := (div_le_iff₀ (by positivity : 0 < 4 * M * N)).mp hb
  have hfg := covariance_eq_sub hf2 hg2
  change covariance f g μ =
    (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ at hfg
  rw [← hfg]
  simpa only [mul_comm] using hout

end StrongMixing
