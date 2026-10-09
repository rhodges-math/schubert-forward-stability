import SchubertForwardStability.Permutations.Classes.Patterns.PatternRecords
import Mathlib.Tactic

/-! # Size bounds and small boundaries of pattern avoidance

A pattern cannot occur in a smaller interval, so every permutation of size `n` avoids each
pattern of larger size. The file also treats size zero, and shows that `132` and `231` have
the Catalan counts in sizes zero, one and two.
-/

open FinitaryPerm
open scoped Classical

namespace PermutationPattern

/-- An increasing occurrence has no more entries than its ambient interval. -/
theorem Contains.size_le {k n : ℕ} {π : PermutationPattern k}
    {w : FinitaryPerm ℕ+} (h : Contains n π w) : k ≤ n := by
  obtain ⟨f, hf, hn, _⟩ := h
  let g : Fin k → Fin n := fun i => (positiveIndex n).symm ⟨f i, hn i⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply hf.injective
    exact congrArg Subtype.val ((positiveIndex n).symm.injective hij)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective g hg

/-- A pattern cannot occur in an interval smaller than its rank. -/
theorem not_contains_of_lt_size {k : ℕ} (n : ℕ) (π : PermutationPattern k)
    (w : FinitaryPerm ℕ+) (h : n < k) : ¬Contains n π w :=
  fun ho => (not_le_of_gt h) ho.size_le

/-- Every bounded permutation avoids each pattern larger than the ambient size. -/
theorem avoiding_of_lt_size {k : ℕ} (n : ℕ) (π : PermutationPattern k)
    (h : n < k) : avoiding n π = symmetricGroup n := by
  ext w
  simp only [mem_avoiding, mem_symmetricGroup, not_contains_of_lt_size n π w h,
    not_false_eq_true, and_true]

/-- Avoiding a larger pattern leaves the full factorial number of permutations. -/
theorem card_avoiding_of_lt_size {k : ℕ} (n : ℕ) (π : PermutationPattern k)
    (h : n < k) : (avoiding n π).card = n.factorial := by
  rw [avoiding_of_lt_size n π h, card_symmetricGroup]

/-- A finite pattern occurs in its own positive-index permutation. -/
theorem contains_ofFinite {k : ℕ} (π : PermutationPattern k) :
    Contains k π (ofFinite k π) := by
  refine ⟨fun i => (positiveIndex k i).val, ?_, fun i => (positiveIndex k i).property, ?_⟩
  · intro i j hij
    change i.val + 1 < j.val + 1
    exact Nat.add_lt_add_right hij 1
  · intro i j
    rw [ofFinite_apply_position, ofFinite_apply_position]
    change (π i).val < (π j).val ↔ (π i).val + 1 < (π j).val + 1
    omega

/-- A nonempty forbidden pattern leaves exactly identity in the empty group. -/
theorem avoiding_zero {k : ℕ} (π : PermutationPattern k) (hk : 0 < k) :
    avoiding 0 π = {1} := by
  rw [avoiding_of_lt_size 0 π hk, symmetricGroup_zero]

/-- Empty-size record fibers contain identity precisely for the empty record set. -/
theorem recordFiberCard_zero {k : ℕ} (π : PermutationPattern k) (hk : 0 < k)
    (R : Finset ℕ+) : recordFiberCard 0 π R = if R = ∅ then 1 else 0 := by
  unfold recordFiberCard recordFiber
  rw [avoiding_zero π hk]
  by_cases hR : R = ∅
  · subst R
    simp only [recordSet_zero, Finset.filter_true, Finset.card_singleton,
      ↓reduceIte]
  · have hne : ∅ ≠ R := Ne.symm hR
    simp only [recordSet_zero, hne, Finset.filter_false, Finset.card_empty,
      ite_eq_right hR]

/-- Both three-entry Catalan patterns have the Catalan counts at sizes zero, one and two. -/
theorem card_catalan_small (n : ℕ) (hn : n ≤ 2) :
    (avoiding n p231).card = catalan n ∧ (avoiding n p132).card = catalan n := by
  have hk : n < 3 := by omega
  rw [card_avoiding_of_lt_size n p231 hk, card_avoiding_of_lt_size n p132 hk]
  interval_cases n <;> norm_num [catalan]

end PermutationPattern
