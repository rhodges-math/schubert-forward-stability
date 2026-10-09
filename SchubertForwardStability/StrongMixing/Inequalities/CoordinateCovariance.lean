import SchubertForwardStability.StrongMixing.Inequalities.BoundedCovariance
import SchubertForwardStability.StrongMixing.Coefficients.CoefficientBounds

/-!
# Coordinate covariance and geometric mixing

Coordinate pullback sigma fields are contained in the corresponding past and future
fields at their integer cut. The bounded covariance inequality therefore
gives a direct coordinate estimate in terms of the sequence mixing coefficient.
-/

open MeasureTheory ProbabilityTheory

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Two uniformly bounded real coordinates at integer positions separated by natural
lag `h` have absolute covariance at most `4 * M ^ 2 * alpha(h)`, where `alpha` is the
past/future mixing coefficient of the sequence. Every natural lag, including zero, is
allowed. -/
theorem coordinate_covariance_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ω, |X i ω| ≤ M) (i : ℤ) (h : ℕ) :
    |(∫ ω, X i ω * X (i + h) ω ∂μ) -
      (∫ ω, X i ω ∂μ) * (∫ ω, X (i + h) ω ∂μ)| ≤
        4 * M ^ 2 * mixingCoeff μ X h := by
  let F : MeasurableSpace Ω := MeasurableSpace.comap (X i) inferInstance
  let G : MeasurableSpace Ω := MeasurableSpace.comap (X (i + h)) inferInstance
  let : MeasurableSpace Ω := mΩ
  have hf : @Measurable Ω ℝ F _ (X i) := Measurable.of_comap_le le_rfl
  have hg : @Measurable Ω ℝ G _ (X (i + h)) := Measurable.of_comap_le le_rfl
  have hc := bounded_covariance_le μ F G (hX i).comap_le (hX (i + h)).comap_le
    (X i) (X (i + h)) hf hg hM hM (hbound i) (hbound (i + h))
  have hcut : strongMixingCoeff (mΩ := mΩ) μ F G ≤ mixingCoeff μ X h := by
    have hp := strongMixingCoeff_mono μ
      (comap_le_generatedSigma X (show i ∈ {j : ℤ | j ≤ i} from by simp))
      (comap_le_generatedSigma X
        (show i + (h : ℤ) ∈ {j : ℤ | i + (h : ℤ) ≤ j} from by simp))
    exact hp.trans (cutCoeff_le_mixingCoeff μ X h i)
  calc
    _ ≤ 4 * M * M * strongMixingCoeff (mΩ := mΩ) μ F G := hc
    _ ≤ 4 * M * M * mixingCoeff μ X h :=
      mul_le_mul_of_nonneg_left hcut (by positivity)
    _ = 4 * M ^ 2 * mixingCoeff μ X h := by ring

/-- For centered uniformly bounded coordinates, the absolute expected product at
natural lag `h` is at most `4 * M ^ 2 * alpha(h)`. -/
theorem centered_coordinate_product_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ω, |X i ω| ≤ M) (i : ℤ) (h : ℕ) :
    |∫ ω, X i ω * X (i + h) ω ∂μ| ≤ 4 * M ^ 2 * mixingCoeff μ X h := by
  simpa only [hcenter, zero_mul, sub_zero] using
    coordinate_covariance_le μ X hX hM hbound i h

/-- An exponential mixing bound at lag `h` yields the corresponding
exponential expected-product bound for centered uniformly bounded coordinates.
The estimate also permits a zero uniform bound. -/
theorem geometric_coordinate_product_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ω, |X i ω| ≤ M) (i : ℤ) (h : ℕ)
    (hmix : mixingCoeff μ X h ≤ Real.exp (-2 * c * h)) :
    |∫ ω, X i ω * X (i + h) ω ∂μ| ≤ 4 * M ^ 2 * Real.exp (-2 * c * h) :=
  (centered_coordinate_product_le μ X hX hcenter hM hbound i h).trans
    (mul_le_mul_of_nonneg_left hmix (by positivity))

end StrongMixing
