import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Total variation on finite spaces

## Main definitions

* `totalVariation`: the supremum of absolute differences of event probabilities.
* `positiveEvent`: the event on which the first measure has at least the second's point mass.

## Main statements

* `totalVariation_eq_half_sum`: the finite half-sum formula.
* `totalVariation_positiveEvent`: the supremum is attained at the positive-mass event.

## References

* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, second edition, American
  Mathematical Society, Providence, RI, 2017, Proposition 4.2.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace LimitTheorems

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The total variation distance is the supremum of absolute event-probability differences. -/
noncomputable def totalVariation (μ ν : Measure α) : ℝ :=
  ⨆ A : Set α, |μ.real A - ν.real A|

/-- The event where the first measure has at least as much point mass as the second. -/
def positiveEvent (μ ν : Measure α) : Set α := {x | ν.real {x} ≤ μ.real {x}}

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
private theorem sum_max_half (d : α → ℝ) (hd : ∑ x, d x = 0) :
    ∑ x, max (d x) 0 = (1 / 2 : ℝ) * ∑ x, |d x| := by
  have hpoint x : 2 * max (d x) 0 = |d x| + d x := by
    by_cases hx : 0 ≤ d x
    · rw [max_eq_left hx, abs_of_nonneg hx]
      ring
    · rw [max_eq_right (le_of_not_ge hx), abs_of_neg (lt_of_not_ge hx)]
      ring
  have hsum : 2 * ∑ x, max (d x) 0 = (∑ x, |d x|) + ∑ x, d x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ hpoint x
  rw [hd] at hsum
  linarith

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
private theorem abs_sum_le_half (d : α → ℝ) (hd : ∑ x, d x = 0) (s : Finset α) :
    |∑ x ∈ s, d x| ≤ (1 / 2 : ℝ) * ∑ x, |d x| := by
  have upper (f : α → ℝ) : (∑ x ∈ s, f x) ≤ ∑ x, max (f x) 0 := by
    refine (Finset.sum_le_sum fun x _ ↦ le_max_left (f x) 0).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun x _ _ ↦ le_max_right (f x) 0)
  have hp := upper d
  rw [sum_max_half d hd] at hp
  have hn : ∑ x, -d x = 0 := by simp [Finset.sum_neg_distrib, hd]
  have hm := upper (fun x ↦ -d x)
  rw [sum_max_half _ hn] at hm
  simp only [Finset.sum_neg_distrib, abs_neg] at hm
  exact abs_le.mpr ⟨by linarith, hp⟩

private theorem sum_mass_one (μ : Measure α) [IsProbabilityMeasure μ] :
    ∑ x, μ.real {x} = 1 := by
  exact (sum_measureReal_singleton (μ := μ) Finset.univ).trans (by simp)

private theorem sum_mass_diff (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : ∑ x, (μ.real {x} - ν.real {x}) = 0 := by
  rw [Finset.sum_sub_distrib, sum_mass_one μ, sum_mass_one ν, sub_self]

/-- Every event difference is bounded by half the sum of point-mass differences. -/
theorem event_diff_le_half_sum (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (A : Set α) :
    |μ.real A - ν.real A| ≤ (1 / 2 : ℝ) * ∑ x, |μ.real {x} - ν.real {x}| := by
  have hμ := sum_measureReal_singleton (μ := μ) A.toFinset
  have hν := sum_measureReal_singleton (μ := ν) A.toFinset
  simp only [Set.coe_toFinset] at hμ hν
  rw [← hμ, ← hν, ← Finset.sum_sub_distrib]
  exact abs_sum_le_half _ (sum_mass_diff μ ν) A.toFinset

/-- The event where point masses increase realizes the half-sum distance. -/
theorem positiveEvent_diff (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    μ.real (positiveEvent μ ν) - ν.real (positiveEvent μ ν) =
      (1 / 2 : ℝ) * ∑ x, |μ.real {x} - ν.real {x}| := by
  let P := (Finset.univ : Finset α).filter fun x ↦ ν.real {x} ≤ μ.real {x}
  have hP : (P : Set α) = positiveEvent μ ν := by ext x; simp [P, positiveEvent]
  rw [← hP, ← sum_measureReal_singleton P, ← sum_measureReal_singleton P,
    ← Finset.sum_sub_distrib]
  calc
    ∑ x ∈ P, (μ.real {x} - ν.real {x}) = ∑ x, max (μ.real {x} - ν.real {x}) 0 := by
      dsimp only [P]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : ν.real {x} ≤ μ.real {x}
      · simp [hx]
      · simp [hx, max_eq_right (sub_nonpos.mpr (le_of_not_ge hx))]
    _ = (1 / 2 : ℝ) * ∑ x, |μ.real {x} - ν.real {x}| :=
      sum_max_half _ (sum_mass_diff μ ν)

/-- On a finite space the total variation supremum equals the half-sum formula. -/
theorem totalVariation_eq_half_sum (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    totalVariation μ ν = (1 / 2 : ℝ) * ∑ x, |μ.real {x} - ν.real {x}| := by
  have hbound : BddAbove (Set.range fun A : Set α ↦ |μ.real A - ν.real A|) :=
    ⟨(1 / 2 : ℝ) * ∑ x, |μ.real {x} - ν.real {x}|,
      by rintro _ ⟨A, rfl⟩; exact event_diff_le_half_sum μ ν A⟩
  apply le_antisymm
  · exact ciSup_le (event_diff_le_half_sum μ ν)
  · have h := le_ciSup hbound (positiveEvent μ ν)
    rw [positiveEvent_diff, abs_of_nonneg (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))] at h
    exact h

/-- The positive-mass event attains the total variation supremum. -/
theorem totalVariation_positiveEvent (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    totalVariation μ ν = μ.real (positiveEvent μ ν) - ν.real (positiveEvent μ ν) := by
  rw [totalVariation_eq_half_sum, positiveEvent_diff]

/-- Total variation is nonnegative. -/
theorem totalVariation_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : 0 ≤ totalVariation μ ν := by
  rw [totalVariation_eq_half_sum]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

/-- Exchanging the two laws preserves total variation. -/
theorem totalVariation_comm (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : totalVariation μ ν = totalVariation ν μ := by
  simp only [totalVariation_eq_half_sum, abs_sub_comm]

/-- Total variation bounds the absolute probability discrepancy of every event. -/
theorem event_diff_le_totalVariation (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (A : Set α) : |μ.real A - ν.real A| ≤ totalVariation μ ν := by
  rw [totalVariation_eq_half_sum]
  exact event_diff_le_half_sum μ ν A

/-- Total variation between probability measures is at most one. -/
theorem totalVariation_le_one (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : totalVariation μ ν ≤ 1 := by
  rw [totalVariation_positiveEvent]
  have hμ := measureReal_le_one (μ := μ) (s := positiveEvent μ ν)
  have hν := measureReal_nonneg (μ := ν) (s := positiveEvent μ ν)
  linarith

/-- Total variation satisfies the triangle inequality. -/
theorem totalVariation_triangle (μ ν ρ : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    totalVariation μ ρ ≤ totalVariation μ ν + totalVariation ν ρ := by
  simp only [totalVariation_eq_half_sum]
  rw [← mul_add, ← Finset.sum_add_distrib]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun x _ ↦ abs_sub_le (μ.real {x}) (ν.real {x}) (ρ.real {x}))
    (by positivity)

omit [Fintype α] [MeasurableSingletonClass α] in
/-- A law has zero total variation distance from itself. -/
@[simp]
theorem totalVariation_self (μ : Measure α) : totalVariation μ μ = 0 := by
  simp [totalVariation]

end LimitTheorems
