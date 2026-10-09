import SchubertForwardStability.StrongMixing.Bernstein.PeelingMPR
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.BoundedVersion

/-!
# The MPR Laplace bound under almost-everywhere hypotheses

Bounded measurable representatives preserve the countable generated-field
coefficients and the finite-sum transform. The pointwise finite peeling bound
therefore holds for AEMeasurable, essentially bounded coordinates.

## References

* F. Merlevède, M. Peligrad and E. Rio, *Bernstein inequality and moderate deviations under
  strong mixing conditions*, High dimensional probability V: the Luminy volume, Inst. Math.
  Stat. (IMS) Collect. 5 (2009), 273-292, arXiv:1202.4777, Theorem 1 and (2.1).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The logarithmic MPR Laplace bound holds for centered AEMeasurable,
almost-everywhere bounded integer sequences and every finite coordinate set of
cardinality at least four, with the same explicit c-only peeling constants. -/
theorem mpr_laplace_ae_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (hn : 4 ≤ A.card) (ht : 0 ≤ t)
    (hkt : peelingMprRate c * M * Real.log A.card * Real.log (Real.log A.card) * t < 1) :
    Integrable (fun ω => Real.exp (t * ∑ i ∈ A, X i ω)) μ ∧
      Real.log (∫ ω, Real.exp (t * ∑ i ∈ A, X i ω) ∂μ) ≤
        A.card * (t * M) ^ 2 * peelingMprVariance c /
          (1 - peelingMprRate c * M * Real.log A.card * Real.log (Real.log A.card) * t) := by
  let Y (i : ℤ) := boundedVersion μ (X i) (hX i) M
  have hY (i : ℤ) : Measurable (Y i) := boundedVersion_measurable μ (X i) (hX i) M
  have hC (i : ℤ) : ∫ ω, Y i ω ∂μ = 0 := by
    rw [integral_boundedVersion μ (X i) (hX i) (hbound i), hcenter i]
  have hB (i : ℤ) (ω : Ω) : |Y i ω| ≤ M :=
    boundedVersion_abs_le μ (X i) (hX i) hM.le ω
  have hMix (h : ℕ) (hh : 1 ≤ h) : mixingCoeff μ Y h ≤ Real.exp (-2 * c * h) := by
    rw [mixingCoeff_boundedVersion μ X hX hbound]
    exact hmix h hh
  have h := peeling_mpr_laplace_le μ Y hY hC hM hc hB hMix A hn ht hkt
  have he : (fun ω => Real.exp (t * ∑ i ∈ A, X i ω)) =ᵐ[μ]
      (fun ω => Real.exp (t * ∑ i ∈ A, Y i ω)) := by
    filter_upwards [ae_all_iff.mpr (fun i => boundedVersion_aeeq μ (X i) (hX i) (hbound i))]
      with ω hω
    exact congrArg (fun z => Real.exp (t * z)) (Finset.sum_congr rfl (fun i _ => hω i))
  refine ⟨h.1.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  exact h.2

end StrongMixing
