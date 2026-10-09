import SchubertForwardStability.Permutations.Classes.PatternFamilies
import Mathlib.Tactic

/-! # Value separation at the maximum of Catalan pattern avoiders

In a `231`-avoider every value to the left of the maximum is smaller than every value to its
right; in a `132`-avoider every such value is larger.
-/

open FinitaryPerm
open scoped Classical

namespace PermutationPattern

private theorem value_lt_max {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) {r i : ℕ+} (hr : (w r : ℕ) = n)
    (hi : (i : ℕ) ≤ n) (hne : i ≠ r) : w i < w r := by
  have hb := (hw.apply_le_iff i).mpr hi
  have hn : (w i : ℕ) ≠ n := by
    intro he
    exact hne (w.injective (PNat.eq (he.trans hr.symm)))
  change (w i : ℕ) < (w r : ℕ)
  rw [hr]
  exact lt_of_le_of_ne hb hn

private theorem contains231_of_split {n : ℕ} {w : FinitaryPerm ℕ+}
    {i r j : ℕ+} (hi : (i : ℕ) ≤ n) (hr : (r : ℕ) ≤ n)
    (hj : (j : ℕ) ≤ n) (hir : i < r) (hrj : r < j)
    (hji : w j < w i) (him : w i < w r) : Contains n p231 w := by
  refine ⟨![i, r, j], ?_, ?_, ?_⟩
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro a
    fin_cases a <;> simpa
  · intro a
    fin_cases a <;> simpa
  · intro a b
    fin_cases a <;> fin_cases b <;>
      norm_num [p231, Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
        simp only [← PNat.coe_lt_coe, ← PNat.coe_le_coe] at * <;> omega

private theorem contains132_of_split {n : ℕ} {w : FinitaryPerm ℕ+}
    {i r j : ℕ+} (hi : (i : ℕ) ≤ n) (hr : (r : ℕ) ≤ n)
    (hj : (j : ℕ) ≤ n) (hir : i < r) (hrj : r < j)
    (hij : w i < w j) (hjm : w j < w r) : Contains n p132 w := by
  refine ⟨![i, r, j], ?_, ?_, ?_⟩
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro a
    fin_cases a <;> simpa
  · intro a
    fin_cases a <;> simpa
  · intro a b
    fin_cases a <;> fin_cases b <;>
      norm_num [p132, Equiv.swap_apply_def] <;>
        simp only [← PNat.coe_lt_coe, ← PNat.coe_le_coe] at * <;> omega

/-- Values to the left of the maximum in a `231`-avoider are below those to its right. -/
theorem avoiding231_split (n : ℕ) (w : FinitaryPerm ℕ+)
    (hw : w ∈ avoiding n p231) (r : ℕ+) (hr : (r : ℕ) ≤ n) (hm : (w r : ℕ) = n)
    (i j : ℕ+) (hir : i < r) (hrj : r < j) (hj : (j : ℕ) ≤ n) : w i < w j := by
  have h := (mem_avoiding n p231 w).mp hw
  have hi : (i : ℕ) ≤ n := le_trans (show (i : ℕ) ≤ r from hir.le) hr
  have hmax := value_lt_max h.1 hm hi (ne_of_lt hir)
  by_contra hnot
  have hne : w j ≠ w i := fun he => (ne_of_gt (hir.trans hrj)) (w.injective he)
  have hji : w j < w i := lt_of_le_of_ne (le_of_not_gt hnot) hne
  exact h.2 (contains231_of_split hi hr hj hir hrj hji hmax)

/-- Values to the left of the maximum in a `132`-avoider are above those to its right. -/
theorem avoiding132_split (n : ℕ) (w : FinitaryPerm ℕ+)
    (hw : w ∈ avoiding n p132) (r : ℕ+) (hr : (r : ℕ) ≤ n) (hm : (w r : ℕ) = n)
    (i j : ℕ+) (hir : i < r) (hrj : r < j) (hj : (j : ℕ) ≤ n) : w j < w i := by
  have h := (mem_avoiding n p132 w).mp hw
  have hi : (i : ℕ) ≤ n := le_trans (show (i : ℕ) ≤ r from hir.le) hr
  have hmax := value_lt_max h.1 hm hj (ne_of_gt hrj)
  by_contra hnot
  have hne : w i ≠ w j := fun he => (ne_of_lt (hir.trans hrj)) (w.injective he)
  have hij : w i < w j := lt_of_le_of_ne (le_of_not_gt hnot) hne
  exact h.2 (contains132_of_split hi hr hj hir hrj hij hmax)

end PermutationPattern
