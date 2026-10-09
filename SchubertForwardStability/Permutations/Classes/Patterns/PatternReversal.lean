import SchubertForwardStability.Permutations.Classes.PatternFamilies
import SchubertForwardStability.Permutations.Statistics.LongestOrder
import Mathlib.Tactic

/-! # Reversal of pattern occurrences and avoidance families

Reversing the positions of a permutation and of a pattern preserves occurrences. Reversal
is therefore a bijection between the avoiders of a pattern and those of its reverse; it maps
the `231`-avoiders onto the `132`-avoiders of every size.
-/

open FinitaryPerm
open scoped Classical

namespace PermutationPattern

/-- Reverse the positions of a pattern while retaining its values. -/
def reversePattern {k : ℕ} (π : PermutationPattern k) : PermutationPattern k :=
  π * Fin.revPerm

/-- Reversing a pattern evaluates it at the reflected finite position. -/
@[simp]
theorem reversePattern_apply {k : ℕ} (π : PermutationPattern k) (i : Fin k) :
    reversePattern π i = π i.rev := rfl

/-- Reversing pattern positions twice restores the original pattern. -/
@[simp]
theorem reversePattern_twice {k : ℕ} (π : PermutationPattern k) :
    reversePattern (reversePattern π) = π := by
  ext i
  simp only [reversePattern_apply, Fin.rev_rev]

/-- An occurrence reverses along with the ambient one-line notation. -/
theorem contains_reverse {k n : ℕ} {π : PermutationPattern k}
    {w : FinitaryPerm ℕ+} (h : Contains n π w) :
    Contains n (reversePattern π) (w * longestElement n) := by
  obtain ⟨f, hf, hn, ho⟩ := h
  refine ⟨fun i => longestElement n (f i.rev), ?_, ?_, ?_⟩
  · intro i j hij
    exact (longestElement_lt_iff (hn i.rev) (hn j.rev)).mpr
      (hf (Fin.rev_lt_rev.mpr hij))
  · intro i
    exact ((isSupported_longestElement n).apply_le_iff _).mpr (hn i.rev)
  · intro i j
    simpa only [reversePattern_apply, mul_apply, longestElement_apply_twice] using
      ho i.rev j.rev

/-- Pattern occurrence is equivalent to occurrence in the reversed notation. -/
theorem contains_reverse_iff {k : ℕ} (n : ℕ) (π : PermutationPattern k)
    (w : FinitaryPerm ℕ+) :
    Contains n (reversePattern π) (w * longestElement n) ↔ Contains n π w := by
  constructor
  · intro h
    simpa only [reversePattern_twice, mul_assoc, longestElement_mul_self, mul_one] using
      contains_reverse h
  · exact contains_reverse

/-- Bounded avoidance is unchanged when positions and the forbidden pattern reverse. -/
theorem mem_reverse_avoiding {k : ℕ} (n : ℕ) (π : PermutationPattern k)
    (w : FinitaryPerm ℕ+) :
    w * longestElement n ∈ avoiding n (reversePattern π) ↔ w ∈ avoiding n π := by
  rw [mem_avoiding, mem_avoiding, contains_reverse_iff]
  constructor
  · rintro ⟨hw, hp⟩
    have hs := hw.mul (isSupported_longestElement n)
    exact ⟨by simpa only [mul_assoc, longestElement_mul_self, mul_one] using hs, hp⟩
  · rintro ⟨hw, hp⟩
    exact ⟨hw.mul (isSupported_longestElement n), hp⟩

/-- Reversal bijects an avoidance family with the reversed-pattern family. -/
theorem reverse_avoiding_bij {k : ℕ} (n : ℕ) (π : PermutationPattern k) :
    Set.BijOn (fun w : FinitaryPerm ℕ+ => w * longestElement n)
      (avoiding n π : Set _) (avoiding n (reversePattern π) : Set _) := by
  have hi : Function.Involutive (fun w : FinitaryPerm ℕ+ => w * longestElement n) := by
    intro w
    simp only [mul_assoc, longestElement_mul_self, mul_one]
  refine ⟨fun w hw => (mem_reverse_avoiding n π w).mpr hw, hi.injective.injOn, ?_⟩
  intro w hw
  change w ∈ avoiding n (reversePattern π) at hw
  refine ⟨w * longestElement n, ?_, hi w⟩
  exact (mem_reverse_avoiding n π (w * longestElement n)).mp
    (by simpa only [mul_assoc, longestElement_mul_self, mul_one] using hw)

/-- Reversing the three entries of the `231` pattern gives `132`. -/
@[simp]
theorem reversePattern_p231 : reversePattern p231 = p132 := by
  ext i
  fin_cases i <;> decide

/-- Reversal maps `231`-avoiders bijectively onto `132`-avoiders at every size. -/
theorem avoiding231_reverse_bij (n : ℕ) :
    Set.BijOn (fun w : FinitaryPerm ℕ+ => w * longestElement n)
      (avoiding n p231 : Set _) (avoiding n p132 : Set _) := by
  simpa only [reversePattern_p231] using reverse_avoiding_bij n p231

/-- The two reversed Catalan avoidance families have equal cardinalities. -/
theorem card_avoiding231_eq_132 (n : ℕ) :
    (avoiding n p231).card = (avoiding n p132).card := by
  have h := avoiding231_reverse_bij n
  exact Finset.card_nbij _ h.1 h.2.1 h.2.2

end PermutationPattern
