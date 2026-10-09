import SchubertForwardStability.Permutations.Random.Tags.TagPartial
import Mathlib.Algebra.BigOperators.Fin

/-! # Conditional next-state laws of uniform tag histories

Extending a prescribed presence path adds one coordinate alphabet. Prefix/suffix
counts then give the completion-weighted transition kernel on positive histories.
-/

namespace FinitaryPerm

open scoped Classical BigOperators

/-- Replace the next position of a presence path by the indicated state. -/
def presenceExtend (y : ℕ → Bool) (t : ℕ) (b : Bool) (s : ℕ) : Bool :=
  if s = t + 1 then b else y s

/-- Extending the next state leaves every preceding path coordinate unchanged. -/
theorem presenceExtend_le (y : ℕ → Bool) (t : ℕ) (b : Bool) (s : ℕ) (hs : s ≤ t) :
    presenceExtend y t b s = y s := by
  simp only [presenceExtend, ite_eq_right (by omega : s ≠ t + 1)]

/-- The extended next coordinate has its prescribed state. -/
theorem presenceExtend_succ (y : ℕ → Bool) (t : ℕ) (b : Bool) :
    presenceExtend y t b (t + 1) = b := by simp [presenceExtend]

private theorem fullCount_product (m : ℕ) (y : ℕ → Bool) (hy0 : y 0 = false) :
    (tagHistoryWords m y).card =
      ∏ i : Fin m, (tagAlphabet (y i.val) (y (i.val + 1))).card := by
  rw [← Fintype.card_coe, Fintype.card_congr (tagHistoryEquiv m y hy0), Fintype.card_pi]
  simp only [Fintype.card_coe]

/-- One-step full-history counts are prefix counts times the final-coordinate alphabet size. -/
theorem card_tagHistoryWords_extend (t : ℕ) (y : ℕ → Bool) (b : Bool) (hy0 : y 0 = false) :
    (tagHistoryWords (t + 1) (presenceExtend y t b)).card =
      (tagHistoryWords t y).card * (tagAlphabet (y t) b).card := by
  have hz : presenceExtend y t b 0 = false := by
    rw [presenceExtend_le y t b 0 (Nat.zero_le _), hy0]
  rw [fullCount_product _ _ hz, Fin.prod_univ_castSucc, fullCount_product _ _ hy0]
  simp only [Fin.val_castSucc, Fin.val_last]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [presenceExtend_le y t b i.val (by omega),
      presenceExtend_le y t b (i.val + 1) (by omega)]
  · rw [presenceExtend_le y t b t (le_refl _), presenceExtend_succ]

/-- The extended-history event is the old history intersected with the prescribed next state. -/
theorem presenceHistory_extend {N : ℕ} (t : ℕ) (y : ℕ → Bool) (b : Bool) :
    presenceHistory (m := N) (t + 1) (presenceExtend y t b) =
      presenceHistory t y ∩ {T | tagPresence T (t + 1) = b} := by
  ext T
  change (∀ s ≤ t + 1, tagPresence T s = presenceExtend y t b s) ↔
    (∀ s ≤ t, tagPresence T s = y s) ∧ tagPresence T (t + 1) = b
  constructor
  · intro h
    refine ⟨fun s hs => ?_, ?_⟩
    · have h' := h s (by omega)
      rw [presenceExtend_le y t b s hs] at h'
      exact h'
    · simpa only [presenceExtend_succ] using h (t + 1) (le_refl _)
  · rintro ⟨h, hb⟩ s hs
    by_cases heq : s = t + 1
    · subst s
      simpa only [presenceExtend_succ] using hb
    · have hs' : s ≤ t := by omega
      rw [presenceExtend_le y t b s hs']
      exact h s hs'

/-- On every positive history, the next presence state follows the completion kernel. -/
theorem tagLaw_conditional_next (t m : ℕ) (y : ℕ → Bool)
    (hp : 0 < (tagLaw (t + (m + 1))).real (presenceHistory t y)) (b : Bool) :
    (tagLaw (t + (m + 1))).real
      (presenceHistory t y ∩ {T | tagPresence T (t + 1) = b}) /
      (tagLaw (t + (m + 1))).real (presenceHistory t y) = tagKernel m (y t) b := by
  have hy0 := (tagLaw_prefix_history_pos t (m + 1) y).mp hp
  have hnew : (tagLaw (t + (m + 1))).real (presenceHistory (t + 1) (presenceExtend y t b)) =
      ((tagHistoryWords t y).card : ℝ) * (tagAlphabet (y t) b).card * extensionCount m b /
        (tagWords (t + (m + 1))).card := by
    have h := tagLaw_prefix_history (t + 1) m (presenceExtend y t b)
    have hn : t + 1 + m = t + (m + 1) := by omega
    rw [hn, card_tagHistoryWords_extend t y b hy0, presenceExtend_succ] at h
    simpa only [Nat.cast_mul] using h
  rw [← presenceHistory_extend, hnew, tagLaw_prefix_history]
  have hP : ((tagHistoryWords t y).card : ℝ) ≠ 0 := by
    rw [card_tagHistoryWords_of_zero t y hy0]
    positivity
  have hW : ((tagWords (t + (m + 1))).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (tagWords_nonempty _)).ne'
  have hU : (extensionCount (m + 1) (y t) : ℝ) ≠ 0 := by
    exact_mod_cast (extensionCount_pos _ _).ne'
  have hratio :
      (((tagHistoryWords t y).card : ℝ) * (tagAlphabet (y t) b).card * extensionCount m b /
        (tagWords (t + (m + 1))).card) /
      (((tagHistoryWords t y).card : ℝ) * extensionCount (m + 1) (y t) /
        (tagWords (t + (m + 1))).card) =
      ((tagAlphabet (y t) b).card : ℝ) * extensionCount m b /
        extensionCount (m + 1) (y t) := by field_simp
  rw [hratio]
  cases y t <;> cases b <;> simp [tagKernel, card_tagAlphabet,
    extensionCount_false_succ, extensionCount_true_succ]

end FinitaryPerm
