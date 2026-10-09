import SchubertForwardStability.LimitTheorems.TotalVariation.Masses
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Prod

/-! # Maximal couplings of finite probability laws

## Main definitions

* `maximalCoupling`: the probability law with diagonal common mass and product residual mass.

## Main statements

* `maximalCoupling_fst`, `maximalCoupling_snd`: the prescribed marginal laws.
* `maximalCoupling_mismatch`: mismatch probability equals total variation.
* `totalVariation_le_mismatch`: no coupling has smaller mismatch probability.

## References

* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, second edition, American
  Mathematical Society, Providence, RI, 2017, Proposition 4.7.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal

namespace LimitTheorems

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The maximal coupling realized as a sum of weighted Dirac masses. -/
noncomputable def maximalCoupling (μ ν : Measure α) : Measure (α × α) :=
  Measure.sum fun p ↦ ENNReal.ofReal (couplingMass μ ν p) • Measure.dirac p

/-- The normalized coupling masses define a probability measure. -/
instance instIsProbabilityMeasureMaxCoupling (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (maximalCoupling μ ν) := by
  have hs : HasSum (couplingMass μ ν) 1 := by
    simpa only [sum_couplingMass] using (hasSum_fintype (couplingMass μ ν))
  exact HasSum.isProbabilityMeasure_sum_dirac (couplingMass_nonneg μ ν) hs

omit [Fintype α] in
/-- The singleton mass of the coupling measure is its nonnegative point-mass formula. -/
theorem maximalCoupling_singleton (μ ν : Measure α) (p : α × α) :
    maximalCoupling μ ν {p} = ENNReal.ofReal (couplingMass μ ν p) :=
  Measure.sum_smul_dirac_singleton

/-- The real singleton mass is the real coupling-mass formula. -/
theorem maximalCoupling_real_singleton (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (p : α × α) :
    (maximalCoupling μ ν).real {p} = couplingMass μ ν p := by
  rw [measureReal_def, maximalCoupling_singleton,
    ENNReal.toReal_ofReal (couplingMass_nonneg μ ν p)]

/-- The first coordinate of the maximal coupling has the first prescribed law. -/
theorem maximalCoupling_fst (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : (maximalCoupling μ ν).map Prod.fst = μ := by
  apply Measure.ext_of_measureReal_singleton
  intro x
  rw [map_measureReal_apply measurable_fst (measurableSet_singleton x)]
  let S := ({x} : Finset α).product (Finset.univ : Finset α)
  have hS : Prod.fst ⁻¹' ({x} : Set α) = (S : Set (α × α)) := by
    ext p
    simp only [S, Finset.product_eq_sprod, Finset.coe_product, Finset.coe_univ,
      Finset.coe_singleton, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_univ, and_true]
  rw [hS, ← sum_measureReal_singleton S]
  dsimp only [S]
  simp only [Finset.product_eq_sprod, Finset.sum_product, Finset.sum_singleton,
    maximalCoupling_real_singleton]
  exact couplingMass_sum_fst μ ν x

/-- The second coordinate of the maximal coupling has the second prescribed law. -/
theorem maximalCoupling_snd (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : (maximalCoupling μ ν).map Prod.snd = ν := by
  apply Measure.ext_of_measureReal_singleton
  intro y
  rw [map_measureReal_apply measurable_snd (measurableSet_singleton y)]
  let S := (Finset.univ : Finset α).product {y}
  have hS : Prod.snd ⁻¹' ({y} : Set α) = (S : Set (α × α)) := by
    ext p
    simp only [S, Finset.product_eq_sprod, Finset.coe_product, Finset.coe_univ,
      Finset.coe_singleton, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_univ, true_and]
  rw [hS, ← sum_measureReal_singleton S]
  dsimp only [S]
  simp only [Finset.product_eq_sprod, Finset.sum_product, Finset.sum_singleton,
    maximalCoupling_real_singleton]
  exact couplingMass_sum_snd μ ν y

/-- The first coupled variable has the same distribution as the first identity variable. -/
theorem identDistrib_maximalCoupling_fst (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IdentDistrib Prod.fst id (maximalCoupling μ ν) μ := by
  refine ⟨measurable_fst.aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [maximalCoupling_fst, Measure.map_id]

/-- The second coupled variable has the same distribution as the second identity variable. -/
theorem identDistrib_maximalCoupling_snd (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IdentDistrib Prod.snd id (maximalCoupling μ ν) ν := by
  refine ⟨measurable_snd.aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [maximalCoupling_snd, Measure.map_id]

/-- Agreement in the maximal coupling has probability one minus total variation. -/
theorem maximalCoupling_agreement (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (maximalCoupling μ ν).real {p | p.1 = p.2} = 1 - totalVariation μ ν := by
  let S := (Finset.univ : Finset α).image fun x ↦ (x, x)
  have hS : {p : α × α | p.1 = p.2} = (S : Set (α × α)) := by
    ext p
    constructor
    · intro hp
      exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, Prod.ext rfl hp⟩
    · intro hp
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
      rfl
  rw [hS, ← sum_measureReal_singleton S]
  dsimp only [S]
  rw [Finset.sum_image]
  · simp only [maximalCoupling_real_singleton, couplingMass_diagonal]
    rw [totalVariation_eq_common]
    ring
  · intro x _ y _ hxy
    exact congrArg Prod.fst hxy

/-- The mismatch probability of the maximal coupling equals total variation. -/
theorem maximalCoupling_mismatch (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (maximalCoupling μ ν).real {p | p.1 ≠ p.2} = totalVariation μ ν := by
  change (maximalCoupling μ ν).real ({p : α × α | p.1 = p.2}ᶜ) = totalVariation μ ν
  rw [probReal_compl_eq_one_sub (Set.toFinite _).measurableSet, maximalCoupling_agreement]
  ring

/-- Every finite pair of probability laws admits a coupling with optimal mismatch probability. -/
theorem exists_maximalCoupling (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : ∃ ρ : Measure (α × α), IsProbabilityMeasure ρ ∧
      ρ.map Prod.fst = μ ∧ ρ.map Prod.snd = ν ∧
      ρ.real {p | p.1 ≠ p.2} = totalVariation μ ν :=
  ⟨maximalCoupling μ ν, inferInstance, maximalCoupling_fst μ ν,
    maximalCoupling_snd μ ν, maximalCoupling_mismatch μ ν⟩

/-- The mismatch probability of any coupling bounds total variation below. -/
theorem totalVariation_le_mismatch (μ ν : Measure α)
    (ρ : Measure (α × α)) [IsProbabilityMeasure ρ]
    (hfst : ρ.map Prod.fst = μ) (hsnd : ρ.map Prod.snd = ν) :
    totalVariation μ ν ≤ ρ.real {p | p.1 ≠ p.2} := by
  unfold totalVariation
  apply ciSup_le
  intro A
  rw [← hfst, ← hsnd, map_measureReal_apply measurable_fst (Set.toFinite A).measurableSet,
    map_measureReal_apply measurable_snd (Set.toFinite A).measurableSet]
  refine (abs_measureReal_sub_le_measureReal_symmDiff
    (measurable_fst (Set.toFinite A).measurableSet).nullMeasurableSet
    (measurable_snd (Set.toFinite A).measurableSet).nullMeasurableSet).trans ?_
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro p hp h
  simp [Set.mem_symmDiff, h] at hp

end LimitTheorems
