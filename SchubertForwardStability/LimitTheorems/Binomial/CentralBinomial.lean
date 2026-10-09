import SchubertForwardStability.LimitTheorems.Binomial.StirlingRate

/-! # Central-binomial error from Stirling's formula

Writing `C(2n,n)*sqrt(pi*n)/4^n` as a ratio of Stirling sequences and bounding the
logarithmic Stirling remainder shows that its distance from `1` is at most `1/n` for every
`n >= 1`.

## Main results

* `LimitTheorems.centralBinomial_error_le`: `|C(2n,n)*sqrt(pi*n)/4^n - 1| <= 1/n`.
* `LimitTheorems.centralBinomial_error_isBigO`: the relative error is `O(1/n)`.
-/

open Filter Asymptotics
open scoped Topology

namespace LimitTheorems

/-- The central-binomial normalization is the ratio of three Stirling factors. -/
theorem centralBinomial_stirling (n : ℕ) (hn : 0 < n) :
    ((2 * n).choose n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n =
      Real.sqrt Real.pi * Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hnp : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hf : ((2 * n).choose n : ℝ) * (n.factorial : ℝ) ^ 2 =
      ((2 * n).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ 2 * n)
    rw [show 2 * n - n = n by omega] at h
    have h' : ((2 * n).choose n : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ) =
        ((2 * n).factorial : ℝ) := by exact_mod_cast h
    simpa only [pow_two, mul_assoc] using h'
  have hp : ((((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n)) =
      (4 : ℝ) ^ n * (((n : ℝ) / Real.exp 1) ^ n) ^ 2 := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [show 2 * (n : ℝ) / Real.exp 1 = 2 * ((n : ℝ) / Real.exp 1) by ring]
    calc
      _ = ((2 * ((n : ℝ) / Real.exp 1)) ^ 2) ^ n := by rw [pow_mul]
      _ = (4 * ((n : ℝ) / Real.exp 1) ^ 2) ^ n := by congr 1; ring
      _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm 2 n, pow_mul]
  have hs : Real.sqrt (2 * ((2 * n : ℕ) : ℝ)) = 2 * Real.sqrt n := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [show (2 : ℝ) * (2 * n) = 4 * n by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hsq : Real.sqrt (2 * (n : ℝ)) ^ 2 = 2 * n :=
    Real.sq_sqrt (by positivity)
  have hsqn : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hnp.le
  have hs0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnp).ne'
  have hf0 : (n.factorial : ℝ) ≠ 0 := by positivity
  have he0 : ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := by positivity
  rw [Real.sqrt_mul Real.pi_pos.le]
  unfold Stirling.stirlingSeq
  rw [hp, hs]
  conv_rhs => arg 2; rw [div_pow, mul_pow, hsq]
  field_simp [hf0, he0, hs0, hn0]
  rw [← hf, ← hsqn, Real.sq_sqrt (sq_nonneg (Real.sqrt (n : ℝ)))]
  ring

/-- Stirling's logarithmic remainder bounds the normalized central-binomial error. -/
theorem centralBinomial_error_le (n : ℕ) (hn : 0 < n) :
    |((2 * n).choose n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n - 1| ≤
      (n : ℝ)⁻¹ := by
  let p := Real.sqrt Real.pi
  let d₁ := Real.log (Stirling.stirlingSeq n) - Real.log p
  let d₂ := Real.log (Stirling.stirlingSeq (2 * n)) - Real.log p
  let B : ℝ := 1 / (12 * n)
  have hnp : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have h2n : 0 < 2 * n := by omega
  have hd₁0 : 0 ≤ d₁ := log_stirling_error_nonneg n hn
  have hd₂0 : 0 ≤ d₂ := log_stirling_error_nonneg (2 * n) h2n
  have hd₁ : d₁ ≤ B := log_stirling_error_le n hn
  have hd₂ : d₂ ≤ B := by
    refine (log_stirling_error_le (2 * n) h2n).trans ?_
    dsimp only [B]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : n ≤ 2 * n))
      (by norm_num)
  have hab : |d₂ - 2 * d₁| ≤ 2 * B := abs_le.mpr ⟨by linarith, by linarith⟩
  have hB : 2 * B = 1 / (6 * (n : ℝ)) := by dsimp only [B]; ring
  have hsmall : |d₂ - 2 * d₁| ≤ 1 := by
    refine hab.trans ?_
    rw [hB]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hp : 0 < p := by dsimp only [p]; positivity
  have hs₁ : 0 < Stirling.stirlingSeq n :=
    hp.trans_le (Stirling.sqrt_pi_le_stirlingSeq hn.ne')
  have hs₂ : 0 < Stirling.stirlingSeq (2 * n) :=
    hp.trans_le (Stirling.sqrt_pi_le_stirlingSeq h2n.ne')
  have he₁ : Real.exp d₁ = Stirling.stirlingSeq n / p := by
    dsimp only [d₁]
    rw [Real.exp_sub, Real.exp_log hs₁, Real.exp_log hp]
  have he₂ : Real.exp d₂ = Stirling.stirlingSeq (2 * n) / p := by
    dsimp only [d₂]
    rw [Real.exp_sub, Real.exp_log hs₂, Real.exp_log hp]
  have he : Real.exp (d₂ - 2 * d₁) =
      ((2 * n).choose n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n := by
    rw [centralBinomial_stirling n hn, Real.exp_sub,
      show 2 * d₁ = d₁ + d₁ by ring, Real.exp_add, he₁, he₂]
    dsimp only [p]
    field_simp
  have h := Real.abs_exp_sub_one_le hsmall
  rw [he] at h
  calc
    _ ≤ 2 * |d₂ - 2 * d₁| := h
    _ ≤ 2 * (2 * B) := mul_le_mul_of_nonneg_left hab (by norm_num)
    _ = (1 / 3 : ℝ) / n := by dsimp only [B]; ring
    _ ≤ 1 / n := div_le_div_of_nonneg_right (by norm_num) hnp.le
    _ = _ := one_div _

/-- The central-binomial normalization has relative error of order `1/n`. -/
theorem centralBinomial_error_isBigO :
    (fun n : ℕ => ((2 * n).choose n : ℝ) * Real.sqrt (Real.pi * n) /
      (4 : ℝ) ^ n - 1) =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity), one_mul]
  exact centralBinomial_error_le n (by omega)

end LimitTheorems
