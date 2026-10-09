import SchubertForwardStability.LimitTheorems.TotalVariation.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field

/-! # Point masses of a maximal coupling

## Main definitions

* `commonMass`: the smaller of the two point probabilities.
* `residualMass`: the mass left after removing the common part.
* `couplingMass`: diagonal common mass plus the normalized product of the residuals.

## Main statements

The coupling masses are nonnegative, have the prescribed row and column sums,
sum to one, and have diagonal masses equal to the common point probabilities.

## References

* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, second edition, American
  Mathematical Society, Providence, RI, 2017, Propositions 4.2 and 4.7.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace LimitTheorems

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The common mass of two measures at a point. -/
def commonMass (μ ν : Measure α) (x : α) : ℝ := min (μ.real {x}) (ν.real {x})

/-- The residual mass of the first measure after removing its common part with the second. -/
def residualMass (μ ν : Measure α) (x : α) : ℝ := μ.real {x} - commonMass μ ν x

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Exchanging the measures preserves common point mass. -/
theorem commonMass_comm (μ ν : Measure α) (x : α) : commonMass μ ν x = commonMass ν μ x :=
  min_comm _ _

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Common point masses are nonnegative. -/
theorem commonMass_nonneg (μ ν : Measure α) (x : α) : 0 ≤ commonMass μ ν x :=
  le_min measureReal_nonneg measureReal_nonneg

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Residual point masses are nonnegative. -/
theorem residualMass_nonneg (μ ν : Measure α) (x : α) : 0 ≤ residualMass μ ν x :=
  sub_nonneg.mpr (min_le_left _ _)

private theorem sum_point_mass (μ : Measure α) [IsProbabilityMeasure μ] :
    ∑ x, μ.real {x} = 1 :=
  (sum_measureReal_singleton (μ := μ) Finset.univ).trans (by simp)

/-- Total variation is one minus the total common point mass. -/
theorem totalVariation_eq_common (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : totalVariation μ ν = 1 - ∑ x, commonMass μ ν x := by
  have hpoint x : |μ.real {x} - ν.real {x}| =
      μ.real {x} + ν.real {x} - 2 * commonMass μ ν x := by
    rcases le_total (μ.real {x}) (ν.real {x}) with hx | hx
    · rw [commonMass, min_eq_left hx, abs_of_nonpos (sub_nonpos.mpr hx)]
      ring
    · rw [commonMass, min_eq_right hx, abs_of_nonneg (sub_nonneg.mpr hx)]
      ring
  rw [totalVariation_eq_half_sum]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_point_mass μ, sum_point_mass ν]
  ring

/-- Each residual law has total mass equal to the total variation distance. -/
theorem sum_residualMass (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : ∑ x, residualMass μ ν x = totalVariation μ ν := by
  simp only [residualMass, Finset.sum_sub_distrib]
  rw [sum_point_mass μ, totalVariation_eq_common]

/-- At zero total variation all residual point masses vanish. -/
theorem residualMass_eq_zero (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : totalVariation μ ν = 0) (x : α) :
    residualMass μ ν x = 0 := by
  have hx := Finset.single_le_sum (fun y _ ↦ residualMass_nonneg μ ν y) (Finset.mem_univ x)
  rw [sum_residualMass, h] at hx
  exact le_antisymm hx (residualMass_nonneg μ ν x)

omit [Fintype α] [MeasurableSingletonClass α] in
/-- The two residual laws have disjoint pointwise supports. -/
theorem residualMass_mul_zero (μ ν : Measure α) (x : α) :
    residualMass μ ν x * residualMass ν μ x = 0 := by
  rcases le_total (μ.real {x}) (ν.real {x}) with hx | hx
  · simp [residualMass, commonMass, min_eq_left hx]
  · simp [residualMass, commonMass, min_eq_left hx, min_eq_right hx]

/-- The point-mass formula of the diagonal-plus-residual maximal coupling. -/
noncomputable def couplingMass (μ ν : Measure α) (p : α × α) : ℝ :=
  (if p.1 = p.2 then commonMass μ ν p.1 else 0) +
    residualMass μ ν p.1 * residualMass ν μ p.2 / totalVariation μ ν

/-- Coupling point masses are nonnegative. -/
theorem couplingMass_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (p : α × α) : 0 ≤ couplingMass μ ν p := by
  unfold couplingMass
  apply add_nonneg
  · split_ifs
    · exact commonMass_nonneg μ ν p.1
    · exact le_rfl
  · exact div_nonneg (mul_nonneg (residualMass_nonneg μ ν p.1)
      (residualMass_nonneg ν μ p.2)) (totalVariation_nonneg μ ν)

/-- Row sums of the coupling masses are the first law's point probabilities. -/
theorem couplingMass_sum_fst (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (x : α) : ∑ y, couplingMass μ ν (x, y) = μ.real {x} := by
  have hs : ∑ y, residualMass ν μ y = totalVariation μ ν := by
    rw [sum_residualMass, totalVariation_comm ν μ]
  dsimp only [couplingMass]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, hs]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases h : totalVariation μ ν = 0
  · rw [h, residualMass_eq_zero μ ν h x]
    simp only [zero_mul, zero_div, add_zero]
    have hx := residualMass_eq_zero μ ν h x
    unfold residualMass at hx
    linarith
  · rw [mul_div_cancel_right₀ _ h]
    simp only [residualMass]
    ring

/-- Swapping both coordinates and measures preserves the coupling mass. -/
theorem couplingMass_swap (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (x y : α) :
    couplingMass μ ν (x, y) = couplingMass ν μ (y, x) := by
  by_cases h : x = y
  · subst y
    simp only [couplingMass, ite_true, commonMass_comm μ ν x,
      totalVariation_comm μ ν, mul_comm]
  · simp only [couplingMass, h, Ne.symm h, ite_false, totalVariation_comm μ ν, mul_comm]

/-- Column sums of the coupling masses are the second law's point probabilities. -/
theorem couplingMass_sum_snd (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (y : α) : ∑ x, couplingMass μ ν (x, y) = ν.real {y} := by
  calc
    ∑ x, couplingMass μ ν (x, y) = ∑ x, couplingMass ν μ (y, x) :=
      Finset.sum_congr rfl fun x _ ↦ couplingMass_swap μ ν x y
    _ = ν.real {y} := couplingMass_sum_fst ν μ y

/-- The total coupling mass equals one. -/
theorem sum_couplingMass (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : ∑ p, couplingMass μ ν p = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [couplingMass_sum_fst]
  exact sum_point_mass μ

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Diagonal coupling mass is exactly the common point probability. -/
theorem couplingMass_diagonal (μ ν : Measure α) (x : α) :
    couplingMass μ ν (x, x) = commonMass μ ν x := by
  simp only [couplingMass, ite_true, residualMass_mul_zero, zero_div, add_zero]

end LimitTheorems
