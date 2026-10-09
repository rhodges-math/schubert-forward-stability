import SchubertForwardStability.Permutations.Classes.Patterns.PatternSplit
import Mathlib.Tactic

/-! # Value intervals on either side of a Catalan maximum

If the maximum of a permutation of size `n` is at position `r`, and every value to its left
is smaller than every value to its right, then the values to its left lie in
`{1, ..., r-1}`. This applies to every `231`-avoider.
-/

open FinitaryPerm
open scoped Classical

namespace PermutationPattern

/-- A split at the maximum with the lower values on the left bounds that left block. -/
theorem split_left_values (n : ℕ) (w : FinitaryPerm ℕ+) (r : ℕ+)
    (hw : IsSupported n w) (hr : (r : ℕ) ≤ n) (hm : (w r : ℕ) = n)
    (hs : ∀ i j : ℕ+, i < r → r < j → (j : ℕ) ≤ n → w i < w j)
    (i : ℕ+) (hi : i < r) : w i < r := by
  by_contra hnot
  have hHigh : (r : ℕ) ≤ w i := le_of_not_gt hnot
  have hrPos := r.pos
  let I := positions ((r : ℕ) - 1)
  have hiI : i ∈ I := by
    apply (mem_positions _ i).mpr
    change (i : ℕ) < (r : ℕ) at hi
    omega
  have hSmall (k : ℕ+) (hk : k ∈ I) : (k : ℕ) < r := by
    have hb := (mem_positions _ k).mp hk
    omega
  have hInv (k : ℕ+) (hk : k ∈ I) : w⁻¹ k < r := by
    have hkSmall := hSmall k hk
    have hkN : (k : ℕ) ≤ n := hkSmall.le.trans hr
    have hjN := (hw.inv.apply_le_iff k).mpr hkN
    by_contra hnotSmall
    have hrj : r ≤ w⁻¹ k := le_of_not_gt hnotSmall
    by_cases he : w⁻¹ k = r
    · have hx := congrArg (fun x : ℕ+ => (w x : ℕ)) he
      simp only [apply_inv_apply, hm] at hx
      omega
    · have hs' := hs i (w⁻¹ k) hi (lt_of_le_of_ne hrj (Ne.symm he)) hjN
      rw [apply_inv_apply] at hs'
      change (w i : ℕ) < (k : ℕ) at hs'
      omega
  have hSub : I.image (fun k => w⁻¹ k) ⊆ I.erase i := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    refine Finset.mem_erase.mpr ⟨?_, (mem_positions _ _).mpr ?_⟩
    · intro he
      have hx := congrArg (fun x : ℕ+ => (w x : ℕ)) he
      simp only [apply_inv_apply] at hx
      have hkSmall := hSmall k hk
      omega
    · have hj := hInv k hk
      change (w⁻¹ k : ℕ) < (r : ℕ) at hj
      omega
  have hc := Finset.card_le_card hSub
  rw [Finset.card_image_of_injective _ w⁻¹.injective,
    Finset.card_erase_of_mem hiI, card_positions] at hc
  have hipos := i.pos
  change (i : ℕ) < (r : ℕ) at hi
  omega

/-- Values before the maximum of a `231`-avoider lie in the first r-1 values. -/
theorem avoiding231_left_values (n : ℕ) (w : FinitaryPerm ℕ+)
    (hw : w ∈ avoiding n p231) (r : ℕ+) (hr : (r : ℕ) ≤ n)
    (hm : (w r : ℕ) = n) (i : ℕ+) (hi : i < r) : w i < r :=
  split_left_values n w r ((mem_avoiding n p231 w).mp hw).1 hr hm
    (avoiding231_split n w hw r hr hm) i hi

end PermutationPattern
