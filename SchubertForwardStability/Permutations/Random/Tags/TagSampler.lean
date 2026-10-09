import SchubertForwardStability.Permutations.Classes.Tags.TagLists
import SchubertForwardStability.Permutations.Random.Tags.BlockTags
import Mathlib.Tactic

/-! # Uniformity of the completion-weighted suffix sampler

Every valid list has the reciprocal of the completion count as mass, and every other
list has mass zero. Thus the sequential sampler equals the finite uniform law.
-/

namespace FinitaryPerm

open scoped Classical BigOperators

/-- The total weight of next symbols is the next-length completion count. -/
theorem tagChoiceTotal_eq (m : ℕ) (present : Bool) :
    tagChoiceTotal m present = extensionCount (m + 1) present := by
  have hU : (Finset.univ : Finset BlockTag) = {.zero, .start, .cont} := rfl
  cases present <;> simp [tagChoiceTotal, hU, tagChoiceCount,
    extensionCount_false_succ, extensionCount_true_succ]
  all_goals omega

/-- The next-symbol mass is its completion weight divided by the total weight. -/
theorem tagChoicePMF_apply (m : ℕ) (present : Bool) (a : BlockTag) :
    tagChoicePMF m present a = (tagChoiceCount m present a : ENNReal) /
      (tagChoiceTotal m present : ENNReal) := rfl

private theorem choiceCount_eq (m : ℕ) (present : Bool) (a : BlockTag)
    (ha : a = .cont → present = true) :
    tagChoiceCount m present a = extensionCount m (decide (a ≠ .zero)) := by
  cases a <;> cases present <;> simp_all [tagChoiceCount]

private theorem map_cons_apply (p : PMF (List BlockTag)) (a b : BlockTag) (T : List BlockTag) :
    (p.map (List.cons b)) (a :: T) = if a = b then p T else 0 := by
  by_cases h : a = b
  · subst b
    simp [PMF.map_apply]
  · simp [PMF.map_apply, List.cons.injEq, h]

/-- A nonempty-length sampler never outputs the empty list. -/
theorem tagSuffixSampler_nil (m : ℕ) (present : Bool) :
    tagSuffixSampler m present [] = if m = 0 then 1 else 0 := by
  cases m with
  | zero => simp [tagSuffixSampler]
  | succ m => simp [tagSuffixSampler, PMF.bind_apply, PMF.map_apply]

/-- The mass of a nonempty list factors into its next-symbol mass and tail mass. -/
theorem tagSuffixSampler_cons (m : ℕ) (present : Bool) (a : BlockTag) (T : List BlockTag) :
    tagSuffixSampler (m + 1) present (a :: T) =
      tagChoicePMF m present a * tagSuffixSampler m (decide (a ≠ .zero)) T := by
  simp only [tagSuffixSampler, PMF.bind_apply, map_cons_apply]
  rw [tsum_eq_single a]
  · simp
  · intro b hb
    simp [Ne.symm hb]

/-- A sampled list has the reciprocal completion-count mass exactly on the valid support. -/
theorem tagSuffixSampler_apply (m : ℕ) (present : Bool) (T : List BlockTag) :
    tagSuffixSampler m present T =
      if T.length = m ∧ ValidTagList present T then (extensionCount m present : ENNReal)⁻¹
      else 0 := by
  induction m generalizing present T with
  | zero =>
    cases T <;> simp [tagSuffixSampler, extensionCount_zero, ValidTagList]
  | succ m ih =>
    cases T with
    | nil => simp [tagSuffixSampler_nil]
    | cons a T =>
      rw [tagSuffixSampler_cons, ih, tagChoicePMF_apply, tagChoiceTotal_eq]
      by_cases ht : T.length = m ∧ ValidTagList (decide (a ≠ .zero)) T
      · rw [ite_eq_left ht]
        by_cases ha : a = .cont → present = true
        · have hfull : (a :: T).length = m + 1 ∧ ValidTagList present (a :: T) := by
            exact ⟨by simp only [List.length_cons, ht.1], ha, ht.2⟩
          rw [ite_eq_left hfull, choiceCount_eq m present a ha, div_eq_mul_inv,
            mul_right_comm]
          have h0 : (extensionCount m (decide (a ≠ .zero)) : ENNReal) ≠ 0 := by
            exact_mod_cast (extensionCount_pos m _).ne'
          rw [ENNReal.mul_inv_cancel h0 (by simp), one_mul]
        · have hc : a = .cont ∧ present = false := by
            cases a <;> cases present <;> simp_all
          obtain ⟨rfl, rfl⟩ := hc
          simp [tagChoiceCount, ValidTagList]
      · rw [ite_eq_right ht]
        have hfull : ¬ ((a :: T).length = m + 1 ∧ ValidTagList present (a :: T)) := by
          simp only [List.length_cons, Nat.succ.injEq, ValidTagList]
          tauto
        rw [ite_eq_right hfull, mul_zero]

/-- The sequential suffix sampler is the uniform PMF on the valid lists. -/
theorem tagSuffixSampler_uniform (m : ℕ) (present : Bool) :
    tagSuffixSampler m present =
      PMF.uniformOfFinset (tagSuffixLists m present) (tagSuffixLists_nonempty m present) := by
  ext T
  rw [tagSuffixSampler_apply, PMF.uniformOfFinset_apply, card_tagSuffixLists]
  simp only [mem_tagSuffixLists]

end FinitaryPerm
