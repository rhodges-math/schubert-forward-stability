import SchubertForwardStability.Paper.Walk.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Telescoping record-walk increments

Every finite increment block telescopes to its endpoint difference. The absolute
endpoint difference is bounded by the block length, for every pair of permutations.
-/

namespace RecordStability

open FinitaryPerm
open scoped BigOperators

/-- A finite record-walk increment block sums to its endpoint difference. -/
theorem recordWalkStep_sum (u v : FinitaryPerm ℕ+) (r k : ℕ) :
    ∑ t ∈ Finset.range k, recordWalkStep u v (r + t).succPNat =
      recordWalk u v (r + k).succPNat - recordWalk u v r.succPNat := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [Finset.sum_range_succ, hk, recordWalkStep]
    have hIndex : (r + k).succPNat + 1 = (r + (k + 1)).succPNat := by
      apply PNat.eq
      change r + k + 1 + 1 = r + (k + 1) + 1
      omega
    rw [hIndex]
    ring

/-- A record-walk endpoint difference is bounded in absolute value by its distance. -/
theorem abs_recordWalk_sub_le (u v : FinitaryPerm ℕ+) (r k : ℕ) :
    |recordWalk u v (r + k).succPNat - recordWalk u v r.succPNat| ≤ (k : ℤ) := by
  rw [← recordWalkStep_sum]
  calc
    _ ≤ ∑ t ∈ Finset.range k, |recordWalkStep u v (r + t).succPNat| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.range k, (1 : ℤ) :=
      Finset.sum_le_sum (fun t _ => abs_recordWalkStep_le u v (r + t).succPNat)
    _ = _ := by simp

/-- Real-cast increments telescope to the real-cast endpoint difference. -/
theorem recordWalkStep_sum_real (u v : FinitaryPerm ℕ+) (r k : ℕ) :
    ∑ t ∈ Finset.range k, (recordWalkStep u v (r + t).succPNat : ℝ) =
      (recordWalk u v (r + k).succPNat : ℝ) - (recordWalk u v r.succPNat : ℝ) := by
  exact_mod_cast recordWalkStep_sum u v r k

/-- The absolute real walk difference is bounded by the number of increments. -/
theorem abs_recordWalk_sub_le_real (u v : FinitaryPerm ℕ+) (r k : ℕ) :
    |(recordWalk u v (r + k).succPNat : ℝ) - (recordWalk u v r.succPNat : ℝ)| ≤
      (k : ℝ) := by
  exact_mod_cast abs_recordWalk_sub_le u v r k

end RecordStability
