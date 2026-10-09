import SchubertForwardStability.Paper.Boolean.BlockTail
import Mathlib.Analysis.Asymptotics.Lemmas

/-! # Summable bounds for Boolean backwards excess

The first three distances use their deterministic amplitude bounds. Later
distances use the logarithmic MPR tail, giving one summable bound
independent of the ambient Boolean family.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory StrongMixing Filter Asymptotics

/-- The uniform backwards-excess bound, with deterministic treatment of the small distances. -/
noncomputable def booleanBacktrackBound (k : ℕ) : ℝ :=
  if k < 4 then (k : ℝ) else (k : ℝ) * Real.exp
    (-(positiveDriftTailRate (mprTailConstant (Real.log 6 / 12)) (1 / 27) * k /
      (Real.log k * Real.log (Real.log k))))

/-- Every term of the Boolean backwards-excess bound is nonnegative. -/
theorem booleanBacktrackBound_nonneg (k : ℕ) : 0 ≤ booleanBacktrackBound k := by
  unfold booleanBacktrackBound
  split_ifs <;> positivity

/-- The backwards-excess bound is summable, including its finitely many small distances. -/
theorem summable_booleanBacktrackBound : Summable booleanBacktrackBound := by
  have hC : 0 < mprTailConstant (Real.log 6 / 12) :=
    mprTailConstant_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num))
  have hs := summable_positiveDriftTail (eta := (1 / 27 : ℝ)) hC (by norm_num)
  apply summable_of_isBigO_nat hs (.of_norm_eventuallyLE ?_)
  filter_upwards [eventually_ge_atTop 4] with k hk
  rw [booleanBacktrackBound, ite_eq_right (not_lt.mpr hk)]
  rw [Real.norm_of_nonneg (by positivity)]

/-- Every preterminal backwards block has expected positive excess bounded by the summable term. -/
theorem integral_boolean_backtrack_bound (N a k : ℕ) (ha : a + k ≤ N) :
    (∫ p, max ((recordWalk p.1 p.2 a.succPNat : ℝ) -
        recordWalk p.1 p.2 (a + k).succPNat) 0 ∂pairLaw (boolean (N + 1))) ≤
      booleanBacktrackBound k := by
  by_cases hk : k < 4
  · rw [booleanBacktrackBound, ite_eq_left hk]
    calc
      _ ≤ ∫ _p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+, (k : ℝ)
          ∂pairLaw (boolean (N + 1)) := by
        apply ProbabilityTheory.integral_uniform_finset_mono
        intro p _
        have h := (abs_le.mp (abs_recordWalk_sub_le_real p.1 p.2 a k)).1
        apply max_le _ (Nat.cast_nonneg k)
        linarith
      _ = _ := by
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  · rw [booleanBacktrackBound, ite_eq_right hk]
    exact integral_boolean_backtrack_le N a k (by omega) ha

end RecordStability
