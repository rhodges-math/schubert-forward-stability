import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

/-! # Effective error bounds for the Stirling sequence

## Main results

Robbins' bound on successive logarithmic differences gives a telescoping tail
estimate and an effective relative error for the Stirling sequence.

## References

Stirling's formula and Robbins' sharp stepwise estimate, as proved in Mathlib's
`Analysis.SpecialFunctions.Stirling`.
-/

open Filter
open scoped Topology

namespace LimitTheorems

private theorem log_stirling_segment_le (n : ℕ) (hn : 0 < n) (m : ℕ) :
    Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq (n + m)) ≤
      1 / (12 * (n : ℝ)) - 1 / (12 * ((n + m : ℕ) : ℝ)) := by
  induction m with
  | zero => simp only [Nat.add_zero, sub_self, le_refl]
  | succ m ih =>
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hm : 0 < ((n + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + m)
    have hs := Stirling.log_stirlingSeq_sdiff_le (n + m)
    calc
      _ = (Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + m))) +
          (Real.log (Stirling.stirlingSeq (n + m)) -
            Real.log (Stirling.stirlingSeq ((n + m) + 1))) := by
        rw [Nat.add_succ]
        ring
      _ ≤ (1 / (12 * (n : ℝ)) - 1 / (12 * ((n + m : ℕ) : ℝ))) +
          1 / (12 * ((n + m : ℕ) : ℝ) * (((n + m : ℕ) : ℝ) + 1)) :=
        add_le_add ih hs
      _ = _ := by
        rw [Nat.add_succ, Nat.cast_succ]
        field_simp [hn', hm.ne', ne_of_gt (by linarith :
          0 < ((n + m : ℕ) : ℝ) + 1)]
        ring

/-- Robbins' logarithmic Stirling remainder is bounded by `1/(12n)`. -/
theorem log_stirling_error_le (n : ℕ) (hn : 0 < n) :
    Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) ≤
      1 / (12 * (n : ℝ)) := by
  have hshift : Tendsto (fun m : ℕ => n + m) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat n
  have ht := (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hshift).log
    (ne_of_gt (by positivity : 0 < Real.sqrt Real.pi))
  apply le_of_tendsto (tendsto_const_nhds.sub ht)
  exact Eventually.of_forall fun m => (log_stirling_segment_le n hn m).trans
    (sub_le_self _ (by positivity))

/-- The logarithmic Stirling remainder is nonnegative at every positive index. -/
theorem log_stirling_error_nonneg (n : ℕ) (hn : 0 < n) :
    0 ≤ Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) := by
  apply sub_nonneg.mpr
  exact Real.log_le_log (by positivity)
    (Stirling.sqrt_pi_le_stirlingSeq (Nat.ne_of_gt hn))

/-- Robbins' bound gives an effective relative Stirling error of at most `1/(6n)`. -/
theorem stirling_relative_error_le (n : ℕ) (hn : 0 < n) :
    |Stirling.stirlingSeq n / Real.sqrt Real.pi - 1| ≤ 1 / (6 * (n : ℝ)) := by
  let d := Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi)
  have hd0 : 0 ≤ d := log_stirling_error_nonneg n hn
  have hd : d ≤ 1 / (12 * (n : ℝ)) := log_stirling_error_le n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hd1 : d ≤ 1 := hd.trans ((div_le_one (by positivity)).mpr (by linarith))
  have h := Real.abs_exp_sub_one_le (x := d) (by rwa [abs_of_nonneg hd0])
  have hp : 0 < Stirling.stirlingSeq n :=
    (by positivity : 0 < Real.sqrt Real.pi).trans_le
      (Stirling.sqrt_pi_le_stirlingSeq (Nat.ne_of_gt hn))
  have he : Real.exp d = Stirling.stirlingSeq n / Real.sqrt Real.pi := by
    dsimp only [d]
    rw [Real.exp_sub, Real.exp_log hp, Real.exp_log (by positivity)]
  rw [he, abs_of_nonneg hd0] at h
  calc
    _ ≤ 2 * d := h
    _ ≤ 2 * (1 / (12 * (n : ℝ))) := mul_le_mul_of_nonneg_left hd (by norm_num)
    _ = _ := by field_simp; ring

end LimitTheorems
