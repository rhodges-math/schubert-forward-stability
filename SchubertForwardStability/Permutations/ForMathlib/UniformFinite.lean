import Mathlib.Probability.UniformOn
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Uniform measures supported on finite sets

This file contains general results that extend Mathlib.

## Main statements

* `integral_uniform_finset`: integration is a finite average.
* `uniformOn_finset_prod`: independent finite uniform laws form a uniform product law.

## Implementation notes

The integral formula includes the empty set, whose uniform measure is zero.
Product-law extensionality uses countability of the ambient carriers.
-/

open MeasureTheory
open scoped Classical ENNReal

namespace ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- A finite uniform law assigns the reciprocal cardinality to each supported point. -/
theorem uniformOn_finset_singleton (s : Finset α) (x : α) :
    uniformOn (s : Set α) {x} = if x ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  have h := uniformOn_apply_finset (s := s) (t := {x})
  by_cases hx : x ∈ s <;>
    simpa [Finset.inter_singleton, hx, div_eq_mul_inv] using h

/-- The integral against a finite uniform law is the finite average. -/
theorem integral_uniform_finset (s : Finset α) (f : α → ℝ) :
    ∫ x, f x ∂uniformOn (s : Set α) = (s.card : ℝ)⁻¹ * ∑ x ∈ s, f x := by
  have hf : IntegrableOn f (s : Set α) Measure.count := by
    rw [← (s : Set α).biUnion_of_singleton,
      integrableOn_finite_biUnion s.finite_toSet]
    intro x _
    exact integrableOn_singleton (hx := by simp)
  rw [uniformOn, cond, integral_smul_measure, Measure.count_apply_finset,
    setIntegral_finset s hf]
  simp [measureReal_def]

/-- Uniform sampling from a finite Cartesian product equals the product of uniform laws. -/
theorem uniformOn_finset_prod [Countable α] [Countable β] (s : Finset α) (t : Finset β) :
    uniformOn (s.product t : Set (α × β)) =
      (uniformOn (s : Set α)).prod (uniformOn (t : Set β)) := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨x, y⟩
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [Set.singleton_prod_singleton, uniformOn_finset_singleton,
    uniformOn_finset_singleton, uniformOn_finset_singleton]
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ t <;>
    simp [hx, hy, Finset.card_product, ENNReal.mul_inv]

/-- Integration over a finite uniform product is a double finite average. -/
theorem integral_uniform_product (s : Finset α) (t : Finset β) (f : α × β → ℝ) :
    ∫ x, f x ∂uniformOn (s.product t : Set (α × β)) =
      ((s.card : ℝ) * (t.card : ℝ))⁻¹ * ∑ x ∈ s, ∑ y ∈ t, f (x, y) := by
  rw [integral_uniform_finset, Finset.product_eq_sprod, Finset.card_product,
    Nat.cast_mul, Finset.sum_product]

end ProbabilityTheory
