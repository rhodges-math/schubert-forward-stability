import SchubertForwardStability.StrongMixing.Coefficients.FiniteCompression
import SchubertForwardStability.StrongMixing.Inequalities.IntervalRemainder

/-!
# The full-interval remainder estimate on a finite coordinate subset

Sorted compression preserves the geometric coefficient bound and transports finite
sums exactly. Hence the logarithmic quadratic estimate applies
to each nonempty remaining coordinate set in the finite peeling argument.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Compressing a nonempty finite coordinate set by its sorted integer
extension cannot increase a sequence's Rosenblatt coefficient at any natural lag.
No measurability or stationarity of the sequence is required for this comparison. -/
theorem mixingCoeff_finiteSet_le {E : Type*} [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℤ → Ω → E)
    (A : Finset ℤ) (hA : A.Nonempty) (h : ℕ) :
    mixingCoeff μ (fun i => X (finiteSetExtension A hA i)) h ≤ mixingCoeff μ X h :=
  mixingCoeff_reindex_le μ X (finiteSetExtension A hA) (finiteSetExtension_strictMono A hA) h

/-- A nonempty finite set of coordinates of a centered measurable bounded
geometrically mixing sequence satisfies the full-interval remainder bound with
its cardinality in place of the interval length. The explicit coefficient is
`6*K_c+384/c^2+2+3*log(card A)/(c*log(2))`, under `0<t*M<=min(1/8,c/72)`.
No stationarity is required. -/
theorem finite_set_remainder_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (hA : A.Nonempty) (ht : 0 < t) (hsmall : t * M ≤ 1 / 8)
    (hrate : t * M ≤ c / 72) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ A, X i ω) ∂μ) ≤
      A.card * (t * M) ^ 2 *
        (6 * (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
          384 / c ^ 2 + 2 + 3 * Real.log A.card / (c * Real.log 2)) := by
  have h := interval_remainder_laplace_le μ (fun i => X (finiteSetExtension A hA i))
    (fun i => hX _) (fun i => hcenter _) hM hc (fun i ω => hbound _ ω)
    (fun h hh => (mixingCoeff_finiteSet_le μ X A hA h).trans (hmix h hh))
    A.card (by have h := Finset.card_pos.mpr hA; omega) 0 ht hsmall hrate
  have hs (ω : Ω) : (∑ i ∈ Finset.Ico 0 (A.card : ℤ),
      X (finiteSetExtension A hA i) ω) = ∑ i ∈ A, X i ω :=
    finiteSetExtension_sum A hA (fun i => X i ω)
  simpa only [zero_add, hs] using h

end StrongMixing
