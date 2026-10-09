import SchubertForwardStability.LimitTheorems.TotalVariation.Coupling
import Mathlib.MeasureTheory.Measure.Restrict

/-! # Total variation and couplings on finite supports

## Main definitions

* `finiteRestriction`: the law on a finite subtype obtained by pullback.
* `supportedCoupling`: a finite maximal coupling mapped into the ambient carrier.

## Main statements

Injective maps from finite carriers preserve total variation in a discrete ambient space.
Finite restriction preserves supported laws, their total variation and their point masses.
The transported maximal coupling has the prescribed ambient marginals and optimal mismatch.

## References

* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, second edition, American
  Mathematical Society, Providence, RI, 2017, Propositions 4.2 and 4.7.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace LimitTheorems

/-- Injective maps from finite spaces into discrete spaces preserve total variation. -/
theorem totalVariation_map_injective {α β : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → β} (hf : Measurable f) (hfi : Function.Injective f) :
    totalVariation (μ.map f) (ν.map f) = totalVariation μ ν := by
  have hbound (B : Set β) : |(μ.map f).real B - (ν.map f).real B| ≤
      totalVariation μ ν := by
    rw [map_measureReal_apply hf .of_discrete, map_measureReal_apply hf .of_discrete]
    exact event_diff_le_totalVariation μ ν (f ⁻¹' B)
  have hbdd : BddAbove (Set.range fun B : Set β ↦
      |(μ.map f).real B - (ν.map f).real B|) :=
    ⟨totalVariation μ ν, by rintro _ ⟨B, rfl⟩; exact hbound B⟩
  apply le_antisymm
  · exact ciSup_le hbound
  · apply ciSup_le
    intro A
    have h := le_ciSup hbdd (f '' A)
    rw [map_measureReal_apply hf .of_discrete, map_measureReal_apply hf .of_discrete,
      Set.preimage_image_eq A hfi] at h
    exact h

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- The pullback of a measure to a finite subtype. -/
noncomputable def finiteRestriction (s : Finset α) (μ : Measure α) : Measure s :=
  μ.comap Subtype.val

/-- A law concentrated on a finite set is recovered by mapping its finite restriction. -/
theorem map_finiteRestriction (s : Finset α) (μ : Measure α)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) : (finiteRestriction s μ).map Subtype.val = μ := by
  exact (map_comap_subtype_coe (s := (s : Set α)) .of_discrete μ).trans
    (Measure.restrict_eq_self_of_ae_mem hμ)

/-- The finite restriction of a supported probability law is a probability law. -/
theorem isProbabilityMeasure_finiteRestriction (s : Finset α) (μ : Measure α)
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ s) :
    IsProbabilityMeasure (finiteRestriction s μ) := by
  have hm : IsProbabilityMeasure ((finiteRestriction s μ).map ((↑) : s → α)) := by
    rw [map_finiteRestriction s μ hμ]
    infer_instance
  exact (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mp hm

/-- Pullback to a finite subtype preserves each point probability. -/
theorem finiteRestriction_real_singleton (s : Finset α) (μ : Measure α) (x : s) :
    (finiteRestriction s μ).real {x} = μ.real {x.val} := by
  rw [measureReal_def, finiteRestriction, comap_subtype_coe_apply .of_discrete]
  simp only [Set.image_singleton]
  rfl

/-- Finite restriction preserves total variation for laws on the same finite support. -/
theorem totalVariation_finiteRestriction (s : Finset α) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ s) (hν : ∀ᵐ x ∂ν, x ∈ s) :
    totalVariation (finiteRestriction s μ) (finiteRestriction s ν) = totalVariation μ ν := by
  let := isProbabilityMeasure_finiteRestriction s μ hμ
  let := isProbabilityMeasure_finiteRestriction s ν hν
  have h := totalVariation_map_injective (finiteRestriction s μ) (finiteRestriction s ν)
    measurable_subtype_coe Subtype.val_injective
  rw [map_finiteRestriction s μ hμ, map_finiteRestriction s ν hν] at h
  exact h.symm

/-- The half-sum formula over a common finite support of ambient probability laws. -/
theorem totalVariation_eq_half_sum_support (s : Finset α) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ s) (hν : ∀ᵐ x ∂ν, x ∈ s) :
    totalVariation μ ν = (1 / 2 : ℝ) * ∑ x ∈ s, |μ.real {x} - ν.real {x}| := by
  let := isProbabilityMeasure_finiteRestriction s μ hμ
  let := isProbabilityMeasure_finiteRestriction s ν hν
  rw [← totalVariation_finiteRestriction s μ ν hμ hν, totalVariation_eq_half_sum]
  simp only [finiteRestriction_real_singleton]
  congr 1
  exact Finset.sum_coe_sort s (fun x ↦ |μ.real {x} - ν.real {x}|)

/-- A maximal coupling on a common finite support, transported to the ambient carrier. -/
noncomputable def supportedCoupling (s : Finset α) (μ ν : Measure α) : Measure (α × α) :=
  (maximalCoupling (finiteRestriction s μ) (finiteRestriction s ν)).map
    (Prod.map Subtype.val Subtype.val)

/-- The transported coupling is a probability law for supported probability marginals. -/
theorem isProbabilityMeasure_supportedCoupling (s : Finset α) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ s) (hν : ∀ᵐ x ∂ν, x ∈ s) :
    IsProbabilityMeasure (supportedCoupling s μ ν) := by
  let := isProbabilityMeasure_finiteRestriction s μ hμ
  let := isProbabilityMeasure_finiteRestriction s ν hν
  unfold supportedCoupling
  infer_instance

/-- The transported maximal coupling has the first prescribed ambient marginal. -/
theorem supportedCoupling_fst (s : Finset α) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ s) (hν : ∀ᵐ x ∂ν, x ∈ s) :
    (supportedCoupling s μ ν).map Prod.fst = μ := by
  let := isProbabilityMeasure_finiteRestriction s μ hμ
  let := isProbabilityMeasure_finiteRestriction s ν hν
  rw [supportedCoupling, Measure.map_map measurable_fst
    (measurable_subtype_coe.prodMap measurable_subtype_coe)]
  change (maximalCoupling (finiteRestriction s μ) (finiteRestriction s ν)).map
    (Subtype.val ∘ Prod.fst) = μ
  rw [← Measure.map_map measurable_subtype_coe measurable_fst,
    maximalCoupling_fst, map_finiteRestriction s μ hμ]

/-- The transported maximal coupling has the second prescribed ambient marginal. -/
theorem supportedCoupling_snd (s : Finset α) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ s) (hν : ∀ᵐ x ∂ν, x ∈ s) :
    (supportedCoupling s μ ν).map Prod.snd = ν := by
  let := isProbabilityMeasure_finiteRestriction s μ hμ
  let := isProbabilityMeasure_finiteRestriction s ν hν
  rw [supportedCoupling, Measure.map_map measurable_snd
    (measurable_subtype_coe.prodMap measurable_subtype_coe)]
  change (maximalCoupling (finiteRestriction s μ) (finiteRestriction s ν)).map
    (Subtype.val ∘ Prod.snd) = ν
  rw [← Measure.map_map measurable_subtype_coe measurable_snd,
    maximalCoupling_snd, map_finiteRestriction s ν hν]

/-- On countable ambient carriers, the transported coupling retains optimal mismatch. -/
theorem supportedCoupling_mismatch [Countable α] (s : Finset α) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ s) (hν : ∀ᵐ x ∂ν, x ∈ s) :
    (supportedCoupling s μ ν).real {p | p.1 ≠ p.2} = totalVariation μ ν := by
  let := isProbabilityMeasure_finiteRestriction s μ hμ
  let := isProbabilityMeasure_finiteRestriction s ν hν
  rw [supportedCoupling, map_measureReal_apply
    (measurable_subtype_coe.prodMap measurable_subtype_coe) .of_discrete]
  have hset : (Prod.map Subtype.val Subtype.val) ⁻¹' {p : α × α | p.1 ≠ p.2} =
      {p : s × s | p.1 ≠ p.2} := by
    ext p
    change p.1.val ≠ p.2.val ↔ p.1 ≠ p.2
    constructor
    · intro h hxy
      exact h (congrArg Subtype.val hxy)
    · intro h hxy
      exact h (Subtype.ext hxy)
  rw [hset, maximalCoupling_mismatch, totalVariation_finiteRestriction s μ ν hμ hν]

end LimitTheorems
