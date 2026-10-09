import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Probability.Independence.Basic

/-! # Joint convergence of independent coordinates

## Main statements

* `tendstoInDistribution_indep`: marginal weak convergence and independence imply
  joint weak convergence, on varying source spaces and along an arbitrary filter.

## Implementation notes

Independence identifies each joint law with the product of its marginal laws.
Continuity of the product of probability measures then gives the joint limit.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LimitTheorems

variable {ι E F Ω' : Type*} {Ω : ι → Type*}
  [∀ i, MeasurableSpace (Ω i)] [MeasurableSpace Ω']
  [TopologicalSpace E] [MeasurableSpace E] [SecondCountableTopology E]
  [TopologicalSpace.PseudoMetrizableSpace E] [BorelSpace E]
  [TopologicalSpace F] [MeasurableSpace F] [SecondCountableTopology F]
  [TopologicalSpace.PseudoMetrizableSpace F] [BorelSpace F]
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {X : (i : ι) → Ω i → E} {Y : (i : ι) → Ω i → F}
  {Z : Ω' → E} {W : Ω' → F} {l : Filter ι}

/-- Independent marginal weak limits give a joint weak limit on varying source spaces. -/
theorem tendstoInDistribution_indep (hX : TendstoInDistribution X l Z μ μ')
    (hY : TendstoInDistribution Y l W μ μ') (hXY : ∀ i, IndepFun (X i) (Y i) (μ i))
    (hZW : IndepFun Z W μ') :
    TendstoInDistribution (fun i ω ↦ (X i ω, Y i ω)) l (fun ω ↦ (Z ω, W ω)) μ μ' := by
  refine ⟨fun i ↦ (hX.forall_aemeasurable i).prodMk (hY.forall_aemeasurable i),
    hX.aemeasurable_limit.prodMk hY.aemeasurable_limit, ?_⟩
  let LX (i : ι) : ProbabilityMeasure E := ⟨(μ i).map (X i), inferInstance⟩
  let LY (i : ι) : ProbabilityMeasure F := ⟨(μ i).map (Y i), inferInstance⟩
  let LZ : ProbabilityMeasure E := ⟨μ'.map Z, inferInstance⟩
  let LW : ProbabilityMeasure F := ⟨μ'.map W, inferInstance⟩
  have hprod : Tendsto (fun i ↦ (LX i).prod (LY i)) l (𝓝 (LZ.prod LW)) :=
    ProbabilityMeasure.continuous_prod.tendsto (LZ, LW) |>.comp
      (hX.tendsto.prodMk_nhds hY.tendsto)
  have hi (i : ι) : (LX i).prod (LY i) =
      (⟨(μ i).map (fun ω ↦ (X i ω, Y i ω)), inferInstance⟩ : ProbabilityMeasure (E × F)) := by
    apply Subtype.ext
    exact ((hXY i).map_prod_eq_prod_map_map
      (hX.forall_aemeasurable i) (hY.forall_aemeasurable i)).symm
  have hz : LZ.prod LW =
      (⟨μ'.map (fun ω ↦ (Z ω, W ω)), inferInstance⟩ : ProbabilityMeasure (E × F)) := by
    apply Subtype.ext
    exact (hZW.map_prod_eq_prod_map_map hX.aemeasurable_limit hY.aemeasurable_limit).symm
  simpa only [hi, hz] using hprod

end LimitTheorems
