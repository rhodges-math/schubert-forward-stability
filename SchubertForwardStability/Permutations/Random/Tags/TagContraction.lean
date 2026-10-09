import SchubertForwardStability.Permutations.Random.Tags.TagKernel

/-! # Iterated contraction of the completion-weighted kernels

Each transition preserves two-state probability vectors. The difference of their
first coordinates contracts by the absolute first-column difference of the rows.
-/

namespace FinitaryPerm

open scoped Classical BigOperators

/-- Applying one tag transition preserves a two-state probability vector. -/
theorem tagKernel_isProbability (m : ℕ) (p : Bool → ℝ) (hp : IsTwoStateProbability p) :
    IsTwoStateProbability (fun b => ∑ a : Bool, p a * tagKernel m a b) := by
  constructor
  · intro b
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hp.1 a) (tagKernel_nonneg m a b)
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, tagKernel_row_sum, mul_one]
    exact hp.2

/-- The exact one-step distance formula for two normalized probability vectors. -/
theorem tagKernel_contraction (m : ℕ) (p q : Bool → ℝ)
    (hp : IsTwoStateProbability p) (hq : IsTwoStateProbability q) :
    |(∑ a : Bool, p a * tagKernel m a false) -
      (∑ a : Bool, q a * tagKernel m a false)| =
      |tagKernel m false false - tagKernel m true false| * |p false - q false| := by
  have hp' : p true = 1 - p false := by
    have := hp.2
    simp only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
      Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton] at this
    linarith
  have hq' : q true = 1 - q false := by
    have := hq.2
    simp only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
      Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton] at this
    linarith
  have hid : (∑ a : Bool, p a * tagKernel m a false) -
      (∑ a : Bool, q a * tagKernel m a false) =
      (p false - q false) * (tagKernel m false false - tagKernel m true false) := by
    simp only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
      Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton, hp', hq']
    ring
  rw [hid, abs_mul, mul_comm]

/-- Any kernel within the finite time range is bounded by its supremum coefficient. -/
theorem tagKernel_diff_le_dobrushin (n t : ℕ) (ht : t < n - 1) :
    |tagKernel (n - t - 2) false false - tagKernel (n - t - 2) true false| ≤
      tagDobrushin n := by
  apply le_csSup (Finset.finite_toSet _).bddAbove
  exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩

/-- The finite supremum transition coefficient is nonnegative, including empty ranges. -/
theorem tagDobrushin_nonneg (n : ℕ) : 0 ≤ tagDobrushin n := by
  by_cases hn : n - 1 = 0
  · simp only [tagDobrushin, hn, Finset.range_zero, Finset.image_empty,
      Finset.coe_empty, Real.sSup_empty, le_refl]
  · exact le_trans (abs_nonneg _) (tagKernel_diff_le_dobrushin n 0 (by omega))

/-- Every nonempty transition range has supremum coefficient exactly one sixth. -/
theorem tagDobrushin_eq (n : ℕ) (hn : 2 ≤ n) : tagDobrushin n = (1 / 6 : ℝ) := by
  apply le_antisymm (tagDobrushin_le n)
  have h := tagKernel_diff_le_dobrushin n (n - 2) (by omega)
  have harg : n - (n - 2) - 2 = 0 := by omega
  rw [harg] at h
  norm_num [tagKernel, extensionCount_zero] at h ⊢
  exact h

/-- Every finite iteration preserves a two-state probability vector. -/
theorem applyTagKernels_isProbability (n r h : ℕ) (p : Bool → ℝ)
    (hp : IsTwoStateProbability p) : IsTwoStateProbability (applyTagKernels n r h p) := by
  induction h with
  | zero => exact hp
  | succ h ih => exact tagKernel_isProbability _ _ ih

/-- The iterated first-coordinate distance is bounded by the supremum coefficient power. -/
theorem applyTagKernels_contract (n r h : ℕ) (p q : Bool → ℝ)
    (hp : IsTwoStateProbability p) (hq : IsTwoStateProbability q) (hbound : r + h ≤ n - 1) :
    |applyTagKernels n r h p false - applyTagKernels n r h q false| ≤
      tagDobrushin n ^ h * |p false - q false| := by
  induction h with
  | zero => simp only [applyTagKernels, pow_zero, one_mul, le_refl]
  | succ h ih =>
    have hi : r + h ≤ n - 1 := by omega
    have ht : r + h < n - 1 := by omega
    have hcoef := tagKernel_diff_le_dobrushin n (r + h) ht
    have harg : n - r - h - 2 = n - (r + h) - 2 := by omega
    rw [← harg] at hcoef
    change |(∑ a : Bool, applyTagKernels n r h p a * tagKernel (n - r - h - 2) a false) -
      (∑ a : Bool, applyTagKernels n r h q a * tagKernel (n - r - h - 2) a false)| ≤ _
    rw [tagKernel_contraction _ _ _ (applyTagKernels_isProbability n r h p hp)
      (applyTagKernels_isProbability n r h q hq)]
    calc
      _ ≤ tagDobrushin n *
          |applyTagKernels n r h p false - applyTagKernels n r h q false| :=
        mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
      _ ≤ tagDobrushin n * (tagDobrushin n ^ h * |p false - q false|) :=
        mul_le_mul_of_nonneg_left (ih hi) (tagDobrushin_nonneg n)
      _ = tagDobrushin n ^ (h + 1) * |p false - q false| := by rw [pow_succ]; ring

end FinitaryPerm
