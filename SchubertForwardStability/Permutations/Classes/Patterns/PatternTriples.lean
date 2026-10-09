import SchubertForwardStability.Permutations.Classes.PatternFamilies
import Mathlib.Tactic

/-! # Triple comparisons for the two Catalan patterns

An occurrence of `231` is a triple of positions `i < j < k` with `w k < w i < w j`, and an
occurrence of `132` is one with `w i < w k < w j`.
-/

namespace PermutationPattern

open FinitaryPerm

/-- A `231` occurrence is an increasing triple with its last value smallest. -/
theorem contains231_iff (n : ℕ) (w : FinitaryPerm ℕ+) :
    Contains n p231 w ↔ ∃ i j k : ℕ+, i < j ∧ j < k ∧ (k : ℕ) ≤ n ∧
      w k < w i ∧ w i < w j := by
  constructor
  · rintro ⟨f, hf, hn, ho⟩
    exact ⟨f 0, f 1, f 2, hf (by decide), hf (by decide), hn 2,
      (ho 2 0).mp (by decide), (ho 0 1).mp (by decide)⟩
  · rintro ⟨i, j, k, hij, hjk, hk, hki, hijv⟩
    refine ⟨![i, j, k], ?_, ?_, ?_⟩
    · apply Fin.strictMono_iff_lt_succ.mpr
      intro a
      fin_cases a <;> simpa
    · intro a
      fin_cases a <;> simp <;>
        simp only [← PNat.coe_lt_coe] at * <;> omega
    · intro a b
      fin_cases a <;> fin_cases b <;>
        norm_num [p231, Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
        simp only [← PNat.coe_lt_coe, ← PNat.coe_le_coe] at * <;> omega

/-- A `132` occurrence is an increasing triple with its middle value largest. -/
theorem contains132_iff (n : ℕ) (w : FinitaryPerm ℕ+) :
    Contains n p132 w ↔ ∃ i j k : ℕ+, i < j ∧ j < k ∧ (k : ℕ) ≤ n ∧
      w i < w k ∧ w k < w j := by
  constructor
  · rintro ⟨f, hf, hn, ho⟩
    exact ⟨f 0, f 1, f 2, hf (by decide), hf (by decide), hn 2,
      (ho 0 2).mp (by decide), (ho 2 1).mp (by decide)⟩
  · rintro ⟨i, j, k, hij, hjk, hk, hikv, hkjv⟩
    refine ⟨![i, j, k], ?_, ?_, ?_⟩
    · apply Fin.strictMono_iff_lt_succ.mpr
      intro a
      fin_cases a <;> simpa
    · intro a
      fin_cases a <;> simp <;>
        simp only [← PNat.coe_lt_coe] at * <;> omega
    · intro a b
      fin_cases a <;> fin_cases b <;>
        norm_num [p132, Equiv.swap_apply_def] <;>
        simp only [← PNat.coe_lt_coe, ← PNat.coe_le_coe] at * <;> omega

end PermutationPattern
