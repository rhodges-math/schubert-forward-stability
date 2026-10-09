import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.Ring

/-! # Remainder estimates for the complex exponential

## Main results

* `iteratedDeriv_exp_mul`: derivatives of a complex exponential on the real line.
* `norm_exp_I_remainder_le`: a global cubic bound for the quadratic remainder.
* `norm_exp_neg_remainder_le`: a quadratic bound for the exponential on the negative axis.
* `norm_exp_I_linear_le`: a quadratic bound for the linear imaginary-axis remainder.
* `norm_exp_I_second_le`: a global quadratic bound for the second-order remainder.

## Implementation notes

Taylor's theorem is applied to the segment parameter in the interval `[0,1]`.
The exponential has norm one along the imaginary axis.
-/

open Complex Set

namespace LimitTheorems

/-- Every real derivative of `s ↦ exp(s z)` multiplies the exponential by `z`. -/
theorem iteratedDeriv_exp_mul (n : ℕ) (z : ℂ) (s : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ exp ((y : ℂ) * z)) s =
      z ^ n * exp ((s : ℂ) * z) := by
  induction n generalizing s with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
      rw [iteratedDeriv_succ, show iteratedDeriv n
        (fun y : ℝ ↦ exp ((y : ℂ) * z)) =
          (fun y : ℝ ↦ z ^ n * exp ((y : ℂ) * z)) from funext ih]
      have hderiv := (((hasDerivAt_id s).ofReal_comp.mul_const z).cexp).const_mul (z ^ n)
      calc
        deriv (fun y : ℝ ↦ z ^ n * exp ((y : ℂ) * z)) s =
            z ^ n * (exp ((s : ℂ) * z) * z) := by simpa only [id_eq,
              ofReal_one, one_mul] using hderiv.deriv
        _ = z ^ (n + 1) * exp ((s : ℂ) * z) := by rw [pow_succ]; ring

/-- The quadratic remainder of `exp(i x)` has norm at most `|x|³ / 2` for every real `x`. -/
theorem norm_exp_I_remainder_le (x : ℝ) :
    ‖exp ((x : ℂ) * I) - (1 + (x : ℂ) * I - (x : ℂ) ^ 2 / 2)‖ ≤
      |x| ^ 3 / 2 := by
  let z : ℂ := (x : ℂ) * I
  let f : ℝ → ℂ := fun s ↦ exp ((s : ℂ) * z)
  have hf (k : ℕ) : ContDiff ℝ k f := by
    have hof : ContDiff ℝ k (fun y : ℝ ↦ (y : ℂ)) := Complex.ofRealCLM.contDiff
    exact Complex.contDiff_exp.comp (hof.mul contDiff_const)
  have hwithin (k : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin k f (Icc (0 : ℝ) 1) s = iteratedDeriv k f s := by
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hf k).contDiffAt hs
  have hnorm (s : ℝ) : ‖iteratedDeriv 3 f s‖ = |x| ^ 3 := by
    rw [show f = (fun s : ℝ ↦ exp ((s : ℂ) * z)) from rfl,
      iteratedDeriv_exp_mul, norm_mul, norm_pow]
    have hexp : ‖exp ((s : ℂ) * z)‖ = 1 := by
      convert norm_exp_ofReal_mul_I (s * x) using 1
      congr 1
      simp only [z, ofReal_mul]
      ring
    rw [hexp, mul_one]
    simp only [z, norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs]
  have htaylor : taylorWithinEval f 2 (Icc (0 : ℝ) 1) 0 1 =
      1 + (x : ℂ) * I - (x : ℂ) ^ 2 / 2 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hwithin 0 0 (by norm_num), hwithin 1 0 (by norm_num), hwithin 2 0 (by norm_num)]
    simp only [f, iteratedDeriv_exp_mul]
    norm_num [z, RCLike.real_smul_eq_coe_mul, mul_pow]
    ring_nf
  have hbound := taylor_mean_remainder_bound (n := 2) (f := f) (C := |x| ^ 3)
    (a := 0) (b := 1) (x := 1) (by norm_num) (hf 3).contDiffOn (by norm_num)
    (fun s hs ↦ by rw [hwithin 3 s hs, hnorm])
  simpa only [f, htaylor, z, ofReal_one, one_mul, sub_zero, one_pow, mul_one,
    Nat.factorial_two, Nat.cast_ofNat] using hbound

/-- The linear remainder of `exp(i x)` has norm at most `x²` for every real `x`. -/
theorem norm_exp_I_linear_le (x : ℝ) :
    ‖exp ((x : ℂ) * I) - (1 + (x : ℂ) * I)‖ ≤ x ^ 2 := by
  let z : ℂ := (x : ℂ) * I
  let f : ℝ → ℂ := fun s ↦ exp ((s : ℂ) * z)
  have hf (k : ℕ) : ContDiff ℝ k f := by
    have hof : ContDiff ℝ k (fun y : ℝ ↦ (y : ℂ)) := Complex.ofRealCLM.contDiff
    exact Complex.contDiff_exp.comp (hof.mul contDiff_const)
  have hwithin (k : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin k f (Icc (0 : ℝ) 1) s = iteratedDeriv k f s :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hf k).contDiffAt hs
  have hnorm (s : ℝ) : ‖iteratedDeriv 2 f s‖ = x ^ 2 := by
    rw [show f = (fun s : ℝ ↦ exp ((s : ℂ) * z)) from rfl,
      iteratedDeriv_exp_mul, norm_mul, norm_pow]
    have hexp : ‖exp ((s : ℂ) * z)‖ = 1 := by
      convert norm_exp_ofReal_mul_I (s * x) using 1
      congr 1
      simp only [z, ofReal_mul]
      ring
    rw [hexp, mul_one]
    simp only [z, norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs, sq_abs]
  have htaylor : taylorWithinEval f 1 (Icc (0 : ℝ) 1) 0 1 = 1 + (x : ℂ) * I := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hwithin 0 0 (by norm_num), hwithin 1 0 (by norm_num)]
    simp only [f, iteratedDeriv_exp_mul]
    norm_num [z, RCLike.real_smul_eq_coe_mul]
  have hbound := taylor_mean_remainder_bound (n := 1) (f := f) (C := x ^ 2)
    (a := 0) (b := 1) (x := 1) (by norm_num) (hf 2).contDiffOn (by norm_num)
    (fun s hs ↦ by rw [hwithin 2 s hs, hnorm])
  simpa only [f, htaylor, z, ofReal_one, one_mul, sub_zero, one_pow, mul_one,
    Nat.factorial_one, Nat.cast_one, div_one] using hbound

/-- The quadratic remainder of `exp(i x)` also has the global bound `3 x² / 2`. -/
theorem norm_exp_I_second_le (x : ℝ) :
    ‖exp ((x : ℂ) * I) - (1 + (x : ℂ) * I - (x : ℂ) ^ 2 / 2)‖ ≤
      3 * x ^ 2 / 2 := by
  have hnorm : ‖(x : ℂ) ^ 2 / 2‖ = x ^ 2 / 2 := by
    simp [norm_pow, sq_abs]
  calc
    _ = ‖(exp ((x : ℂ) * I) - (1 + (x : ℂ) * I)) + (x : ℂ) ^ 2 / 2‖ := by
      congr 1
      ring
    _ ≤ ‖exp ((x : ℂ) * I) - (1 + (x : ℂ) * I)‖ + ‖(x : ℂ) ^ 2 / 2‖ :=
      norm_add_le _ _
    _ ≤ x ^ 2 + x ^ 2 / 2 := add_le_add (norm_exp_I_linear_le x) hnorm.le
    _ = _ := by ring

/-- Along the negative real axis, the linear exponential remainder has norm at most `a²`. -/
theorem norm_exp_neg_remainder_le {a : ℝ} (ha : 0 ≤ a) :
    ‖exp (-(a : ℂ)) - (1 - (a : ℂ))‖ ≤ a ^ 2 := by
  let z : ℂ := -(a : ℂ)
  let f : ℝ → ℂ := fun s ↦ exp ((s : ℂ) * z)
  have hf (k : ℕ) : ContDiff ℝ k f := by
    have hof : ContDiff ℝ k (fun y : ℝ ↦ (y : ℂ)) := Complex.ofRealCLM.contDiff
    exact Complex.contDiff_exp.comp (hof.mul contDiff_const)
  have hwithin (k : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin k f (Icc (0 : ℝ) 1) s = iteratedDeriv k f s :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hf k).contDiffAt hs
  have hnorm (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDeriv 2 f s‖ ≤ a ^ 2 := by
    rw [show f = (fun s : ℝ ↦ exp ((s : ℂ) * z)) from rfl,
      iteratedDeriv_exp_mul, norm_mul, norm_pow]
    have hz : ‖z‖ = a := by simp only [z, norm_neg, norm_real, Real.norm_eq_abs,
      abs_of_nonneg ha]
    rw [hz]
    have hexp : ‖exp ((s : ℂ) * z)‖ ≤ 1 := by
      rw [norm_exp]
      simp only [z, mul_neg, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs.1 ha))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (sq_nonneg a)
  have htaylor : taylorWithinEval f 1 (Icc (0 : ℝ) 1) 0 1 = 1 - (a : ℂ) := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hwithin 0 0 (by norm_num), hwithin 1 0 (by norm_num)]
    simp only [f, iteratedDeriv_exp_mul]
    norm_num [z, RCLike.real_smul_eq_coe_mul]
    ring
  have hbound := taylor_mean_remainder_bound (n := 1) (f := f) (C := a ^ 2)
    (a := 0) (b := 1) (x := 1) (by norm_num) (hf 2).contDiffOn (by norm_num)
    (fun s hs ↦ by rw [hwithin 2 s hs]; exact hnorm s hs)
  simpa only [f, htaylor, z, ofReal_one, one_mul, sub_zero, one_pow, mul_one,
    Nat.factorial_one, Nat.cast_one, div_one] using hbound

end LimitTheorems
