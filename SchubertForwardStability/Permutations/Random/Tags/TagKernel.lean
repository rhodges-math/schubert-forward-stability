import SchubertForwardStability.Permutations.Classes.Tags.TagCounts
import SchubertForwardStability.Permutations.Random.Tags.BlockTags
import Mathlib.Tactic

/-! # Completion-count bounds and two-state transition coefficients

The two-state kernel has nonnegative normalized rows. Its difference between the
two first-column entries is nonnegative and bounded by one sixth.
-/

namespace FinitaryPerm

open scoped Classical BigOperators

/-- A present boundary state has at least as many valid suffixes as an absent one. -/
theorem extensionCount_false_le_true (m : ℕ) :
    extensionCount m false ≤ extensionCount m true := by
  cases m with
  | zero => simp only [extensionCount_zero, le_refl]
  | succ m =>
    rw [extensionCount_false_succ, extensionCount_true_succ]
    omega

/-- Every entry of the completion-weighted two-state kernel is nonnegative. -/
theorem tagKernel_nonneg (m : ℕ) (a b : Bool) : 0 ≤ tagKernel m a b := by
  cases a <;> cases b <;> simp only [tagKernel, Bool.false_eq_true, ite_false, ite_true]
  all_goals positivity

/-- Each row of the completion-weighted kernel has total mass one. -/
theorem tagKernel_row_sum (m : ℕ) (a : Bool) : ∑ b : Bool, tagKernel m a b = 1 := by
  have h0 : 0 < (extensionCount m false : ℝ) := by
    exact_mod_cast extensionCount_pos m false
  have h1 : 0 < (extensionCount m true : ℝ) := by
    exact_mod_cast extensionCount_pos m true
  cases a <;> simp only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton, tagKernel,
    Bool.false_eq_true, ite_false, ite_true]
  all_goals (field_simp; ring)

/-- The absent-state first-column entry is at least the present-state entry. -/
theorem tagKernel_false_diff_nonneg (m : ℕ) :
    0 ≤ tagKernel m false false - tagKernel m true false := by
  have h0 : 0 < (extensionCount m false : ℝ) := by
    exact_mod_cast extensionCount_pos m false
  have h1 : 0 < (extensionCount m true : ℝ) := by
    exact_mod_cast extensionCount_pos m true
  simp only [tagKernel, Bool.false_eq_true, ite_false, ite_true]
  have hd0 : 0 < (extensionCount m false : ℝ) + extensionCount m true := by positivity
  have hd1 : 0 < (extensionCount m false : ℝ) + 2 * extensionCount m true := by positivity
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ hd1 hd0).mpr
  nlinarith

/-- The absolute first-column difference of the two rows is at most one sixth. -/
theorem tagKernel_false_diff_le (m : ℕ) :
    |tagKernel m false false - tagKernel m true false| ≤ (1 / 6 : ℝ) := by
  rw [abs_of_nonneg (tagKernel_false_diff_nonneg m)]
  have h0 : 0 < (extensionCount m false : ℝ) := by
    exact_mod_cast extensionCount_pos m false
  have h1 : 0 < (extensionCount m true : ℝ) := by
    exact_mod_cast extensionCount_pos m true
  have h01 : (extensionCount m false : ℝ) ≤ extensionCount m true := by
    exact_mod_cast extensionCount_false_le_true m
  simp only [tagKernel, Bool.false_eq_true, ite_false, ite_true]
  have hd0 : 0 < (extensionCount m false : ℝ) + extensionCount m true := by positivity
  have hd1 : 0 < (extensionCount m false : ℝ) + 2 * extensionCount m true := by positivity
  rw [div_sub_div _ _ hd0.ne' hd1.ne']
  apply (div_le_div_iff₀ (mul_pos hd0 hd1) (by norm_num : (0 : ℝ) < 6)).mpr
  have hp : 0 ≤ (extensionCount m true : ℝ) *
      ((extensionCount m true : ℝ) - extensionCount m false) :=
    mul_nonneg h1.le (sub_nonneg.mpr h01)
  nlinarith [sq_nonneg ((extensionCount m true : ℝ) - extensionCount m false)]

/-- Every finite-time supremum of the transition differences is at most one sixth. -/
theorem tagDobrushin_le (n : ℕ) : tagDobrushin n ≤ (1 / 6 : ℝ) := by
  unfold tagDobrushin
  by_cases hn : (Finset.range (n - 1)).Nonempty
  · apply csSup_le (hn.image _)
    intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    exact tagKernel_false_diff_le _
  · have hz : n - 1 = 0 := by
      by_contra h
      exact hn ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero h)⟩
    simp only [hz, Finset.range_zero, Finset.image_empty, Finset.coe_empty,
      Real.sSup_empty]
    norm_num

end FinitaryPerm
