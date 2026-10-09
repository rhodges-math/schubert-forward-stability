import SchubertForwardStability.StrongMixing.Coefficients.AEEqCoefficients
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.BoundedLaplace

/-!
# Bounded measurable representatives of AEMeasurable variables

For an almost-everywhere bounded real variable, choose a measurable version and
replace values outside the bounding interval by zero. This preserves the variable
almost everywhere and satisfies the bound at every point of the sample space.
-/

open MeasureTheory

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded measurable representative is a measurable version of `X`, replaced
by zero wherever its absolute value exceeds `M`. Quantitative bounds require `M>=0`. -/
noncomputable def boundedVersion (μ : Measure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X μ) (M : ℝ) (ω : Ω) : ℝ :=
  if |hX.mk X ω| ≤ M then hX.mk X ω else 0

/-- The bounded representative is measurable for every real cutoff `M`. -/
theorem boundedVersion_measurable (μ : Measure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X μ) (M : ℝ) : Measurable (boundedVersion μ X hX M) := by
  have habs : Measurable (fun ω => |hX.mk X ω|) := by
    simpa only [Real.norm_eq_abs] using hX.measurable_mk.norm
  exact Measurable.ite (measurableSet_le habs measurable_const)
    hX.measurable_mk measurable_const

/-- For every nonnegative cutoff, the bounded representative satisfies the
absolute-value bound at every sample point. -/
theorem boundedVersion_abs_le (μ : Measure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X μ) {M : ℝ} (hM : 0 ≤ M) (ω : Ω) :
    |boundedVersion μ X hX M ω| ≤ M := by
  unfold boundedVersion
  split
  · assumption
  · simpa using hM

/-- An almost-everywhere bounded variable equals its bounded representative
almost everywhere, including cutoff zero. -/
theorem boundedVersion_aeeq (μ : Measure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X μ) {M : ℝ} (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ M) :
    X =ᵐ[μ] boundedVersion μ X hX M := by
  filter_upwards [hX.ae_eq_mk, hbound] with ω he hb
  simp only [boundedVersion, ← he, ite_eq_left hb]

/-- Replacing a real variable by its bounded representative preserves its
Bochner integral whenever its original absolute-value bound holds almost surely. -/
theorem integral_boundedVersion (μ : Measure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X μ) {M : ℝ} (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ M) :
    (∫ ω, boundedVersion μ X hX M ω ∂μ) = ∫ ω, X ω ∂μ :=
  integral_congr_ae (boundedVersion_aeeq μ X hX hbound).symm

/-- Simultaneously replacing every integer coordinate by a bounded measurable
representative preserves all mixing coefficients of an AEMeasurable sequence. -/
theorem mixingCoeff_boundedVersion (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ) {M : ℝ}
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ M) (h : ℕ) :
    mixingCoeff μ (fun i => boundedVersion μ (X i) (hX i) M) h = mixingCoeff μ X h :=
  (mixingCoeff_aeeq μ X _ hX
    (fun i => (boundedVersion_measurable μ (X i) (hX i) M).aemeasurable)
    (fun i => boundedVersion_aeeq μ (X i) (hX i) (hbound i)) h).symm

end StrongMixing
