import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Convergence in distribution under equality of laws

## Main results

Distributional convergence transports across equal row laws and equal limiting laws.

## Implementation notes

The row carriers may vary with the index, and the limiting carriers may differ.
Equality is proved directly in the subtype of probability measures.
-/

open MeasureTheory Filter
open scoped Topology

namespace LimitTheorems

/-- Distributional convergence transports across equal row laws and equal limiting laws. -/
theorem tendstoInDistribution_law_congr
    {ι E Ω' Γ' : Type*} {Ω Γ : ι → Type*}
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (Γ i)]
    [MeasurableSpace Ω'] [MeasurableSpace Γ']
    {μ : ∀ i, Measure (Ω i)} {ν : ∀ i, Measure (Γ i)}
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    {μ' : Measure Ω'} {ν' : Measure Γ'}
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    {X : ∀ i, Ω i → E} {Y : ∀ i, Γ i → E} {Z : Ω' → E} {W : Γ' → E}
    {l : Filter ι} (h : TendstoInDistribution X l Z μ μ')
    (hY : ∀ i, AEMeasurable (Y i) (ν i)) (hW : AEMeasurable W ν')
    (hrow : ∀ i, (ν i).map (Y i) = (μ i).map (X i))
    (hlim : ν'.map W = μ'.map Z) :
    TendstoInDistribution Y l W ν ν' where
  forall_aemeasurable := hY
  aemeasurable_limit := hW
  tendsto := by
    have hr :
        (fun i => (⟨(ν i).map (Y i), inferInstance⟩ : ProbabilityMeasure E)) =
          (fun i => (⟨(μ i).map (X i), inferInstance⟩ : ProbabilityMeasure E)) := by
      funext i
      exact Subtype.ext (hrow i)
    have hz : (⟨ν'.map W, inferInstance⟩ : ProbabilityMeasure E) =
        (⟨μ'.map Z, inferInstance⟩ : ProbabilityMeasure E) := Subtype.ext hlim
    rw [hr, hz]
    exact h.tendsto

end LimitTheorems
