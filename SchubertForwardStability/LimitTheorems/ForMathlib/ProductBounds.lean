import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

/-! # Perturbation bounds for finite products

This file extends Mathlib with a telescoping bound for products in the closed unit ball.

## Main results

* `Finset.norm_prod_sub_prod_le_sum`: the distance between two products in the unit ball is
  bounded by the sum of the distances between their factors.
-/

namespace Finset

variable {ι R : Type*} [NormedCommRing R] [NormOneClass R]

/-- A finite product of factors with norm at most one has norm at most one. -/
theorem norm_prod_le_one (s : Finset ι) (f : ι → R) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∏ i ∈ s, f i‖ ≤ 1 :=
  (norm_prod_le s f).trans (prod_le_one₀ (fun _ _ ↦ norm_nonneg _) hf)

/-- For factors in the unit ball, the norm of the product difference is bounded by the sum
of the norms of the factor differences. -/
theorem norm_prod_sub_prod_le_sum (s : Finset ι) (f g : ι → R)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [prod_empty, sub_self, norm_zero, sum_empty, le_refl]
  | @insert a s ha ih =>
      have hfs : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi ↦ hf i (mem_insert_of_mem hi)
      have hgs : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi ↦ hg i (mem_insert_of_mem hi)
      rw [prod_insert ha, prod_insert ha, sum_insert ha]
      calc
        ‖f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i‖ =
            ‖(f a - g a) * (∏ i ∈ s, f i) +
              g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := by congr 1; ring
        _ ≤ ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ +
            ‖g a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ ‖f a - g a‖ * 1 + 1 * ∑ i ∈ s, ‖f i - g i‖ := by
          gcongr
          · exact norm_prod_le_one s f hfs
          · exact hg a (mem_insert_self a s)
          · exact ih hfs hgs
        _ = ‖f a - g a‖ + ∑ i ∈ s, ‖f i - g i‖ := by rw [mul_one, one_mul]

end Finset
