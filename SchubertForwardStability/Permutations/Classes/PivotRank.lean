import SchubertForwardStability.Permutations.Statistics.PivotCovers
import SchubertForwardStability.Permutations.Statistics.SuffixChoice
import Mathlib.Order.RelClasses

/-! # Lexicographic descent rank for pivot transitions

## Main definitions

* `lastDescent`: the greatest adjacent descent, with value zero at identity.
* `pivotRank`: the last descent and its permutation value, with pair zero at identity.
* `PivotRankLt`: the inverse image of the lexicographic natural-pair order.

## Main results

The rank order is well founded. Both the pivot exchange and every finite left-cover
output strictly decrease it.
-/

namespace FinitaryPerm

open scoped Classical

/-- The greatest positive descent position, or zero if the descent set is empty. -/
noncomputable def lastDescent (w : FinitaryPerm ℕ+) : ℕ := w.descentSet.sup PNat.val

/-- The last-descent statistic vanishes precisely at identity. -/
theorem lastDescent_eq_zero (w : FinitaryPerm ℕ+) : w.lastDescent = 0 ↔ w = 1 := by
  constructor
  · intro hz
    by_contra hn
    obtain ⟨j, hj⟩ := exists_descent_of_ne_one w hn
    have hb := Finset.le_sup (f := PNat.val) ((mem_descentSet w j).mpr hj)
    change (j : ℕ) ≤ w.lastDescent at hb
    rw [hz] at hb
    exact (Nat.not_le.mpr (show 0 < (j : ℕ) from j.2)) hb
  · rintro rfl
    simp only [lastDescent, descentSet_one, Finset.sup_empty]
    rfl

/-- A strictly increasing tail bounds all adjacent descents by its starting position. -/
theorem lastDescent_le_of_tail {w : FinitaryPerm ℕ+} {r : ℕ+}
    (ht : StrictMonoOn w {j : ℕ+ | r < j}) : w.lastDescent ≤ (r : ℕ) := by
  apply Finset.sup_le
  intro j hj
  by_contra hn
  have hrj : r < j := lt_of_not_ge hn
  have hnext : j < j + 1 := Nat.lt_succ_self (j : ℕ)
  have hv := ht hrj (hrj.trans hnext) hnext
  exact (not_lt_of_gt hv) ((mem_descentSet w j).mp hj)

/-- The starting position of an increasing-tail pivot is itself a descent. -/
theorem IncreasingTailPivot.hasDescent {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) : HasDescent w r := by
  have hrs : r + 1 ≤ s := Nat.succ_le_of_lt h.start_lt
  by_cases he : r + 1 = s
  · simpa only [HasDescent, he] using h.value_lt
  · exact (h.tail_strictMono (Nat.lt_succ_self (r : ℕ)) h.start_lt
      (lt_of_le_of_ne hrs he)).trans h.value_lt

/-- The start of an increasing-tail pivot is exactly its last descent. -/
theorem IncreasingTailPivot.lastDescent_eq {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) : w.lastDescent = (r : ℕ) := by
  apply le_antisymm (lastDescent_le_of_tail h.tail_strictMono)
  exact Finset.le_sup (f := PNat.val) ((mem_descentSet w r).mpr h.hasDescent)

/-- Last descent and its value, with pair zero for the empty descent set. -/
noncomputable def pivotRank (w : FinitaryPerm ℕ+) : ℕ × ℕ :=
  if hz : w.lastDescent = 0 then (0, 0)
  else (w.lastDescent, ((w ⟨w.lastDescent, Nat.pos_of_ne_zero hz⟩ : ℕ+) : ℕ))

/-- The first rank coordinate is the last-descent statistic. -/
theorem pivotRank_fst (w : FinitaryPerm ℕ+) : w.pivotRank.1 = w.lastDescent := by
  unfold pivotRank
  split_ifs with hz
  · exact hz.symm
  · rfl

/-- Identity has the zero lexicographic rank. -/
theorem pivotRank_one : pivotRank (1 : FinitaryPerm ℕ+) = (0, 0) := by
  simp only [pivotRank, (lastDescent_eq_zero 1).mpr rfl, dite_true]

/-- A specified positive last descent determines the two rank coordinates. -/
theorem pivotRank_eq_of_last {w : FinitaryPerm ℕ+} {r : ℕ+}
    (he : w.lastDescent = (r : ℕ)) : w.pivotRank = ((r : ℕ), (w r : ℕ)) := by
  unfold pivotRank
  have hn : w.lastDescent ≠ 0 := by rw [he]; exact Nat.ne_of_gt r.2
  rw [dite_eq_right hn]
  exact Prod.ext he (congrArg (fun j : ℕ+ => (w j : ℕ)) (PNat.eq he))

/-- An increasing-tail pivot determines the lexicographic rank. -/
theorem IncreasingTailPivot.pivotRank_eq {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) : w.pivotRank = ((r : ℕ), (w r : ℕ)) :=
  pivotRank_eq_of_last h.lastDescent_eq

/-- Strict lexicographic comparison of the descent ranks. -/
def PivotRankLt (v w : FinitaryPerm ℕ+) : Prop :=
  Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b) v.pivotRank w.pivotRank

/-- Pulling back the natural-pair lexicographic order gives a well-founded relation. -/
theorem pivotRankLt_wellFounded : WellFounded PivotRankLt :=
  InvImage.wf pivotRank (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

/-- A tail-bounded permutation with a smaller value at the pivot has lower rank. -/
theorem IncreasingTailPivot.rank_lt_of_tail {w v : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) (ht : StrictMonoOn v {j : ℕ+ | r < j})
    (hv : v r < w r) : PivotRankLt v w := by
  rw [PivotRankLt, h.pivotRank_eq, Prod.lex_def]
  have hb := lastDescent_le_of_tail ht
  rcases lt_or_eq_of_le hb with hl | he
  · exact Or.inl (by simpa only [pivotRank_fst] using hl)
  · rw [pivotRank_eq_of_last he]
    exact Or.inr ⟨rfl, hv⟩

/-- A swap entirely before or at a tail boundary leaves its strict increase intact. -/
theorem strictMono_tail_swap {v : FinitaryPerm ℕ+} {q r : ℕ+}
    (ht : StrictMonoOn v {j : ℕ+ | r < j}) (hqr : q < r) :
    StrictMonoOn (v * swap q r) {j : ℕ+ | r < j} := by
  intro i hi j hj hij
  rw [mul_apply, swap_apply_of_ne (ne_of_gt (hqr.trans hi)) (ne_of_gt hi),
    mul_apply, swap_apply_of_ne (ne_of_gt (hqr.trans hj)) (ne_of_gt hj)]
  exact ht hi hj hij

/-- The pivot exchange strictly decreases lexicographic descent rank. -/
theorem IncreasingTailPivot.swapped_rank_lt {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) : PivotRankLt (w * swap r s) w := by
  apply h.rank_lt_of_tail h.swapped_tail
  simpa only [mul_apply, swap_apply_left] using h.value_lt

/-- Every finite left-cover output strictly decreases the original pivot rank. -/
theorem IncreasingTailPivot.transition_rank_lt {w : FinitaryPerm ℕ+} {q r s : ℕ+}
    (h : IncreasingTailPivot w r s) (hq : q ∈ transitionPositions (w * swap r s) r) :
    PivotRankLt ((w * swap r s) * swap q r) w := by
  have hq' := (mem_transitionPositions _ _ _).mp hq
  apply h.rank_lt_of_tail (strictMono_tail_swap h.swapped_tail hq'.left_lt)
  rw [mul_apply, swap_apply_right]
  exact hq'.value_lt.trans (by simpa only [mul_apply, swap_apply_left] using h.value_lt)

end FinitaryPerm
