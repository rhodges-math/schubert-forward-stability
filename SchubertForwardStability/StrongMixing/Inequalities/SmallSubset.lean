import SchubertForwardStability.StrongMixing.Inequalities.SubsetRemainder

/-!
# Quadratic Laplace bounds on short finite coordinate sets

Sorted compression transports the geometric interval second-moment estimate to
an arbitrary nonempty finite coordinate set. The only size restriction is the
usual bounded-sum condition.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A centered measurable sequence bounded in absolute value by `M>=0`, with
geometric coefficient bound of positive rate `c`, has finite-set log-Laplace
transform at most `t^2*card(A)*M^2*K_c` when `|t|*card(A)*M<=1`.
The nonempty selected set may contain arbitrary gaps and negative coordinates;
no stationarity is required. -/
theorem finite_set_small_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (hA : A.Nonempty) (t : ℝ) (hsize : |t| * A.card * M ≤ 1) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ A, X i ω) ∂μ) ≤
      t ^ 2 * A.card * M ^ 2 *
        (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) := by
  have h := geometric_interval_laplace_le μ (fun i => X (finiteSetExtension A hA i))
    (fun i => hX _) (fun i => hcenter _) hM hc (fun i ω => hbound _ ω)
    (fun h hh => (mixingCoeff_finiteSet_le μ X A hA h).trans (hmix h hh))
    0 A.card t hsize
  have hs (ω : Ω) : (∑ i ∈ Finset.Ico 0 (A.card : ℤ),
      X (finiteSetExtension A hA i) ω) = ∑ i ∈ A, X i ω :=
    finiteSetExtension_sum A hA (fun i => X i ω)
  simpa only [zero_add, hs] using h

end StrongMixing
