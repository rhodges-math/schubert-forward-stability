import SchubertForwardStability.LimitTheorems.Convergence.Slutsky
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Equality in law and convergence in distribution

## Main statements

* `identDistrib_iff_cdf`: equality in law is equality of real cumulative probabilities.
* `TendstoInProbability.tendstoInDistribution`: convergence in probability to a constant
  implies weak convergence to that constant on varying source spaces.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LimitTheorems

/-- Real random variables have the same law exactly when their cumulative probabilities agree. -/
theorem identDistrib_iff_cdf {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν) :
    IdentDistrib X Y μ ν ↔ ∀ t : ℝ, μ.real {ω | X ω ≤ t} = ν.real {ω | Y ω ≤ t} := by
  constructor
  · intro h t
    have hreal := congrArg (fun ρ : Measure ℝ ↦ ρ.real (Set.Iic t)) h.map_eq
    rw [map_measureReal_apply_of_aemeasurable hX measurableSet_Iic,
      map_measureReal_apply_of_aemeasurable hY measurableSet_Iic] at hreal
    change μ.real {ω | X ω ≤ t} = ν.real {ω | Y ω ≤ t} at hreal
    exact hreal
  · intro h
    refine ⟨hX, hY, Measure.ext_of_Iic _ _ fun t ↦ ?_⟩
    apply (measureReal_eq_measureReal_iff).mp
    rw [map_measureReal_apply_of_aemeasurable hX measurableSet_Iic,
      map_measureReal_apply_of_aemeasurable hY measurableSet_Iic]
    change μ.real {ω | X ω ≤ t} = ν.real {ω | Y ω ≤ t}
    exact h t

variable {ι E Ω' : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  [MeasurableSpace Ω'] {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {ν : Measure Ω'} [IsProbabilityMeasure ν] [MeasurableSpace E]
  [SeminormedAddCommGroup E] [SecondCountableTopology E] [BorelSpace E]
  {X : (i : ι) → Ω i → E} {l : Filter ι} [l.IsCountablyGenerated] {c : E}

omit [SecondCountableTopology E] [l.IsCountablyGenerated] in
/-- Constant variables on arbitrary probability spaces share a constant weak limit. -/
theorem tendstoInDistribution_const_varying :
    TendstoInDistribution (fun i (_ : Ω i) ↦ c) l (fun _ : Ω' ↦ c) μ ν := by
  refine ⟨fun _ ↦ measurable_const.aemeasurable, measurable_const.aemeasurable, ?_⟩
  have heq : (fun i ↦ (⟨(μ i).map (fun _ : Ω i ↦ c), inferInstance⟩ : ProbabilityMeasure E)) =
      (fun _ : ι ↦ (⟨ν.map (fun _ : Ω' ↦ c), inferInstance⟩ : ProbabilityMeasure E)) := by
    funext i
    apply Subtype.ext
    simp only [Measure.map_const, measure_univ, one_smul]
  rw [heq]
  exact tendsto_const_nhds

/-- Convergence in probability to a constant implies convergence in distribution to it. -/
theorem TendstoInProbability.tendstoInDistribution (h : TendstoInProbability X l c μ)
    (hX : ∀ i, AEMeasurable (X i) (μ i)) :
    TendstoInDistribution X l (fun _ : Ω' ↦ c) μ ν :=
  tendstoInDistribution_of_sub tendstoInDistribution_const_varying
    (tendstoInProbability_sub_const.mpr h) hX

end LimitTheorems
