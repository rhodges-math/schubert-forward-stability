import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Powers of six and lag-loss absorption

The quarter event bound absorbs small lags. For larger lags, the exponent `1/3`
absorbs the loss of two lag positions, `(1/6)^(h-2) <= 6^(-h/3)`, and the exponent `1/6`
absorbs the factor two from independent pairing, `2*6^(-h/3) <= 6^(-h/6)`. The bound
`6^(-h/6)` equals `exp(-2*c*h)` with `c = log(6)/12`.
-/

namespace RecordStability

/-- The quarter bound is smaller than the six-power bound for exponents through two thirds. -/
private theorem quarter_le_six_rpow (a : ℝ) (ha : a ≤ 2 / 3) :
    (1 / 4 : ℝ) ≤ Real.rpow 6 (-a) := by
  simp only [Real.rpow_eq_pow]
  have h6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hlog : Real.log ((6 : ℝ) ^ 2) ≤ Real.log ((4 : ℝ) ^ 3) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  have he : (1 / 4 : ℝ) = Real.exp (-Real.log 4) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  rw [he, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6)]
  apply Real.exp_le_exp.mpr
  have hp := mul_le_mul_of_nonneg_left ha h6.le
  nlinarith

/-- The loss of two integer lag positions is absorbed by the one-third exponent
at every lag at least three. -/
theorem six_gap_decay_le (h : ℕ) (hh : 3 ≤ h) :
    (1 / 6 : ℝ) ^ (h - 2) ≤ Real.rpow 6 (-(h : ℝ) / 3) := by
  simp only [Real.rpow_eq_pow]
  have h6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have he : Real.exp (-Real.log 6) = (1 / 6 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 6)]
    norm_num
  rw [← he, ← Real.exp_nat_mul, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6)]
  have hd : ((h - 2 : ℕ) : ℝ) = (h : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ h)]
    norm_num
  rw [hd]
  apply Real.exp_le_exp.mpr
  have hh' : (3 : ℝ) ≤ h := by exact_mod_cast hh
  have hp := mul_nonneg h6.le (sub_nonneg.mpr hh')
  nlinarith

/-- The quarter coefficient bound is at most `6^(-h/3)` for the lags `h <= 2`. -/
theorem six_small_record_bound (h : ℕ) (hh : h ≤ 2) :
    (1 / 4 : ℝ) ≤ Real.rpow 6 (-(h : ℝ) / 3) := by
  have hh' : (h : ℝ) ≤ 2 := by exact_mod_cast hh
  have he : -(h : ℝ) / 3 = -((h : ℝ) / 3) := by ring
  rw [he]
  exact quarter_le_six_rpow _ (by linarith)

/-- The quarter coefficient bound is at most `6^(-h/6)` for the lags `h <= 4`. -/
theorem six_small_pair_bound (h : ℕ) (hh : h ≤ 4) :
    (1 / 4 : ℝ) ≤ Real.rpow 6 (-(h : ℝ) / 6) := by
  have hh' : (h : ℝ) ≤ 4 := by exact_mod_cast hh
  have he : -(h : ℝ) / 6 = -((h : ℝ) / 6) := by ring
  rw [he]
  exact quarter_le_six_rpow _ (by linarith)

/-- The factor two from independent row pairing is absorbed by the one-sixth
exponent at every lag at least five. -/
theorem six_pair_decay_le (h : ℕ) (hh : 5 ≤ h) :
    2 * Real.rpow 6 (-(h : ℝ) / 3) ≤ Real.rpow 6 (-(h : ℝ) / 6) := by
  simp only [Real.rpow_eq_pow]
  have h6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hlog : Real.log ((2 : ℝ) ^ 2) ≤ Real.log 6 :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at hlog
  norm_num at hlog
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6),
    ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh' : (3 : ℝ) ≤ h := by exact_mod_cast (show 3 ≤ h by omega)
  have hp := mul_nonneg h6.le (sub_nonneg.mpr hh')
  nlinarith

/-- The bound `6^(-h/6)` equals `exp(-2*c*h)` with `c=log(6)/12` at every integer
lag `h`. -/
theorem six_mixing_rate_eq (h : ℕ) :
    Real.rpow 6 (-(h : ℝ) / 6) = Real.exp (-2 * (Real.log 6 / 12) * (h : ℝ)) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6)]
  congr 1
  ring

end RecordStability
