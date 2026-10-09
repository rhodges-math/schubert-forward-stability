import SchubertForwardStability.StrongMixing.Bernstein.PeelingScales
import SchubertForwardStability.StrongMixing.Inequalities.FinitePeeling

/-!
# Common Bernstein row bounds for finite peeling

The denominator of every retained row is enlarged to the logarithmic size of
the original finite coordinate set. The numerator uses the geometric upper
cardinality, giving positive scales even for an empty selected piece.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Enlarge the retained Bernstein bound to a numerical cardinal upper bound
`N` and a logarithmic upper size `L`. This preserves exponential integrability
and gives a common denominator for all finite peeling pieces. -/
theorem retained_size_bernstein_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t N L : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (hN : (A.card : ℝ) ≤ N)
    (hL : Real.log (max (A.card : ℝ) 2) ≤ L) (ht : 0 ≤ t)
    (hkt : retainedRate c * M * L * t < 1) :
    Integrable (fun ω => Real.exp (t * ∑ i ∈ retainedSubset A, X i ω)) μ ∧
      Real.log (∫ ω, Real.exp (t * ∑ i ∈ retainedSubset A, X i ω) ∂μ) ≤
        N * (t * M) ^ 2 * retainedVariance c / (1 - retainedRate c * M * L * t) := by
  have hκ := mul_le_mul_of_nonneg_left hL
    (mul_nonneg (retainedRate_pos hc).le hM.le)
  have hκt := mul_le_mul_of_nonneg_right hκ ht
  have hka : retainedRate c * M * Real.log (max (A.card : ℝ) 2) * t < 1 :=
    hκt.trans_lt hkt
  have h := retained_subset_bernstein_le μ X hX hcenter hM hc hbound hmix A ht hka
  refine ⟨h.1, h.2.trans ?_⟩
  have hnum := mul_le_mul_of_nonneg_right hN
    (mul_nonneg (sq_nonneg (t * M)) (retainedVariance_pos hc).le)
  have hNp : 0 ≤ N := (Nat.cast_nonneg A.card).trans hN
  have hQ : 0 < retainedVariance c := retainedVariance_pos hc
  calc
    _ ≤ N * (t * M) ^ 2 * retainedVariance c /
        (1 - retainedRate c * M * Real.log (max (A.card : ℝ) 2) * t) :=
      div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hnum) (sub_pos.mpr hka).le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hkt)
      (by linarith only [hκt])

/-- Every retained peeling row has the common logarithmic Bernstein denominator
of the original finite set and the positive geometrically decaying scale
`peelingScale(c,M,card(A),j)`. This includes empty later pieces. -/
theorem peeling_row_bernstein_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (j : ℕ) (ht : 0 ≤ t)
    (hkt : retainedRate c * M * Real.log (max (A.card : ℝ) 2) * t < 1) :
    Integrable (fun ω => Real.exp (t * ∑ i ∈ peelingPiece A j, X i ω)) μ ∧
      Real.log (∫ ω, Real.exp (t * ∑ i ∈ peelingPiece A j, X i ω) ∂μ) ≤
        (peelingScale c M A.card j * t) ^ 2 /
          (1 - retainedRate c * M * Real.log (max (A.card : ℝ) 2) * t) := by
  have hcard := Finset.card_le_card (peelingRemainder_subset A j)
  have hL : Real.log (max ((peelingRemainder A j).card : ℝ) 2) ≤
      Real.log (max (A.card : ℝ) 2) :=
    Real.log_le_log (by positivity) (max_le_max (by exact_mod_cast hcard) le_rfl)
  have h := retained_size_bernstein_le μ X hX hcenter hM hc hbound hmix
    (peelingRemainder A j) (peelingRemainder_card_le A j) hL ht hkt
  have he : (peelingScale c M A.card j * t) ^ 2 =
      ((A.card : ℝ) / (2 : ℝ) ^ j) * (t * M) ^ 2 * retainedVariance c := by
    rw [mul_pow, peelingScale_sq hc]
    ring
  rw [he]
  exact h

end StrongMixing
