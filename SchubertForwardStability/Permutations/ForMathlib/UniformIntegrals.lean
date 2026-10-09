import SchubertForwardStability.Permutations.ForMathlib.UniformFinite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Finite uniform integral identities

This file contains general results that extend Mathlib.

## Main results

Finite uniform integrals commute with finite sums and addition, preserve inequalities,
and depend only on values in the sampling set. No integrability premise is necessary.

## Implementation notes

The empty sampling set has zero measure, and is included in every identity.
-/

namespace ProbabilityTheory

open MeasureTheory
open scoped Classical BigOperators

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Only the values on a finite sampling set determine its uniform integral. -/
theorem integral_uniform_finset_congr (s : Finset α) (f g : α → ℝ)
    (h : ∀ x ∈ s, f x = g x) :
    (∫ x, f x ∂uniformOn (s : Set α)) = ∫ x, g x ∂uniformOn (s : Set α) := by
  rw [integral_uniform_finset, integral_uniform_finset]
  exact congrArg _ (Finset.sum_congr rfl h)

/-- Inequalities on a finite sampling set pass to its uniform integrals. -/
theorem integral_uniform_finset_mono (s : Finset α) (f g : α → ℝ)
    (h : ∀ x ∈ s, f x ≤ g x) :
    (∫ x, f x ∂uniformOn (s : Set α)) ≤ ∫ x, g x ∂uniformOn (s : Set α) := by
  rw [integral_uniform_finset, integral_uniform_finset]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum h)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- A finite uniform integral is additive on arbitrary real functions. -/
theorem integral_uniform_finset_add (s : Finset α) (f g : α → ℝ) :
    (∫ x, f x + g x ∂uniformOn (s : Set α)) =
      (∫ x, f x ∂uniformOn (s : Set α)) + ∫ x, g x ∂uniformOn (s : Set α) := by
  simp only [integral_uniform_finset, Finset.sum_add_distrib, mul_add]

/-- A finite uniform integral commutes with subtraction of arbitrary real functions. -/
theorem integral_uniform_finset_sub (s : Finset α) (f g : α → ℝ) :
    (∫ x, f x - g x ∂uniformOn (s : Set α)) =
      (∫ x, f x ∂uniformOn (s : Set α)) - ∫ x, g x ∂uniformOn (s : Set α) := by
  simp only [integral_uniform_finset, Finset.sum_sub_distrib, mul_sub]

/-- A finite uniform integral commutes with every finite sum of real functions. -/
theorem integral_uniform_finsetSum {ι : Type*} (s : Finset α) (t : Finset ι)
    (f : ι → α → ℝ) :
    (∫ x, ∑ i ∈ t, f i x ∂uniformOn (s : Set α)) =
      ∑ i ∈ t, ∫ x, f i x ∂uniformOn (s : Set α) := by
  simp only [integral_uniform_finset, Finset.mul_sum]
  rw [Finset.sum_comm]

end ProbabilityTheory
