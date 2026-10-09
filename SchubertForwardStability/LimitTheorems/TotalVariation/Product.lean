import SchubertForwardStability.LimitTheorems.TotalVariation.Coupling
import Mathlib.Probability.Independence.Basic

/-! # Independent products of maximal couplings

## Main definitions

* `productCoupling`: the product of two maximal coupling laws.

## Main statements

The two original variables and the two comparison variables each have independent
coordinates with the prescribed laws. The probability of either mismatch is at
most the sum of the two total variation distances.

## References

* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, second edition, American
  Mathematical Society, Providence, RI, 2017, Proposition 4.7.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace LimitTheorems

variable {α β : Type*} [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- The law of two independently sampled maximal couplings. -/
noncomputable def productCoupling (μ ν : Measure α) (κ η : Measure β) :
    Measure ((α × α) × (β × β)) :=
  (maximalCoupling μ ν).prod (maximalCoupling κ η)

/-- Independent products of maximal couplings are probability measures. -/
instance instIsProbabilityMeasureProdCoupling (μ ν : Measure α) (κ η : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure κ] [IsProbabilityMeasure η] :
    IsProbabilityMeasure (productCoupling μ ν κ η) := by
  unfold productCoupling
  infer_instance

variable (μ ν : Measure α) (κ η : Measure β)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [IsProbabilityMeasure κ] [IsProbabilityMeasure η]

/-- The original pair has the product of the two original laws. -/
theorem productCoupling_original :
    (productCoupling μ ν κ η).map (Prod.map Prod.fst Prod.fst) = μ.prod κ := by
  unfold productCoupling
  rw [← Measure.map_prod_map _ _ measurable_fst measurable_fst,
    maximalCoupling_fst, maximalCoupling_fst]

/-- The comparison pair has the product of the two comparison laws. -/
theorem productCoupling_comparison :
    (productCoupling μ ν κ η).map (Prod.map Prod.snd Prod.snd) = ν.prod η := by
  unfold productCoupling
  rw [← Measure.map_prod_map _ _ measurable_snd measurable_snd,
    maximalCoupling_snd, maximalCoupling_snd]

/-- The two original variables remain independent in the product coupling. -/
theorem indepFun_productCoupling_original :
    IndepFun (fun p ↦ p.1.1) (fun p ↦ p.2.1) (productCoupling μ ν κ η) :=
  indepFun_prod measurable_fst measurable_fst

/-- The two comparison variables remain independent in the product coupling. -/
theorem indepFun_productCoupling_comp :
    IndepFun (fun p ↦ p.1.2) (fun p ↦ p.2.2) (productCoupling μ ν κ η) :=
  indepFun_prod measurable_snd measurable_snd

/-- The probability of either mismatch is the complement of the product agreement probability. -/
theorem productCoupling_mismatch :
    (productCoupling μ ν κ η).real {p | p.1.1 ≠ p.1.2 ∨ p.2.1 ≠ p.2.2} =
      totalVariation μ ν + totalVariation κ η -
        totalVariation μ ν * totalVariation κ η := by
  have hset : {p : (α × α) × (β × β) | p.1.1 ≠ p.1.2 ∨ p.2.1 ≠ p.2.2} =
      ({p : α × α | p.1 = p.2} ×ˢ {p : β × β | p.1 = p.2})ᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_prod, not_and_or]
  rw [hset, probReal_compl_eq_one_sub (Set.toFinite _).measurableSet]
  change 1 - ((maximalCoupling μ ν).prod (maximalCoupling κ η)).real
    ({p : α × α | p.1 = p.2} ×ˢ {p : β × β | p.1 = p.2}) = _
  rw [measureReal_prod_prod, maximalCoupling_agreement, maximalCoupling_agreement]
  ring

/-- The probability of either mismatch is bounded by the sum of the marginal distances. -/
theorem productCoupling_mismatch_le :
    (productCoupling μ ν κ η).real {p | p.1.1 ≠ p.1.2 ∨ p.2.1 ≠ p.2.2} ≤
      totalVariation μ ν + totalVariation κ η := by
  rw [productCoupling_mismatch]
  exact sub_le_self _ (mul_nonneg (totalVariation_nonneg μ ν) (totalVariation_nonneg κ η))

end LimitTheorems
