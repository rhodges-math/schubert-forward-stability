import SchubertForwardStability.StrongMixing.Inequalities.FinitePeeling
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The logarithmic cutoff for finite Cantor peeling

After at most `floor(log(log(n))/log(2))+1` half-retention stages, the residual
has cardinality at most `n/log(n)`. All quantitative statements cover `n>=4`.
-/

namespace StrongMixing

/-- The deterministic logarithmic peeling depth is
`floor(log(log(max(n,4)))/log(2))+1`. The maximum makes this a total definition. -/
noncomputable def peelingLogDepth (n : ℕ) : ℕ :=
  ⌊Real.log (Real.log (max (n : ℝ) 4)) / Real.log 2⌋₊ + 1

/-- The numerical logarithm of four is strictly greater than one, as needed
to make the logarithmic peeling cutoff and its log-log bounds positive. -/
theorem log_four_gt_one : 1 < Real.log (4 : ℝ) := by
  have h := Real.log_two_gt_d9
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num
  linarith

/-- For every natural `n>=4`, both `log(n)>1` and `log(log(n))>0`. -/
theorem peeling_logs_pos (n : ℕ) (hn : 4 ≤ n) :
    1 < Real.log n ∧ 0 < Real.log (Real.log n) := by
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (show (4 : ℝ) ≤ n by exact_mod_cast hn)
  have hp := log_four_gt_one.trans_le hl
  exact ⟨hp, Real.log_pos hp⟩

/-- The rounded peeling depth has `2^depth>log(n)` for all `n>=4`. -/
theorem peelingLogDepth_pow_gt (n : ℕ) (hn : 4 ≤ n) :
    Real.log n < (2 : ℝ) ^ peelingLogDepth n := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := peeling_logs_pos n hn
  have hf := Nat.lt_floor_add_one (Real.log (Real.log n) / Real.log 2)
  have hd : peelingLogDepth n = ⌊Real.log (Real.log n) / Real.log 2⌋₊ + 1 := by
    unfold peelingLogDepth
    rw [max_eq_left (by exact_mod_cast hn : (4 : ℝ) ≤ n)]
  have hm := mul_lt_mul_of_pos_right hf h2
  have hrel : Real.log (Real.log n) < (peelingLogDepth n : ℝ) * Real.log 2 := by
    rw [div_mul_cancel₀ _ h2.ne'] at hm
    simpa only [hd, Nat.cast_add, Nat.cast_one] using hm
  apply (Real.log_lt_log_iff (by linarith : 0 < Real.log n) (by positivity)).mp
  rw [Real.log_pow]
  exact hrel

/-- The rounded logarithmic peeling depth is at most
`log(log(n))/log(2)+1` for every `n>=4`. -/
theorem peelingLogDepth_le (n : ℕ) (hn : 4 ≤ n) :
    (peelingLogDepth n : ℝ) ≤ Real.log (Real.log n) / Real.log 2 + 1 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := (peeling_logs_pos n hn).2
  have hf := Nat.floor_le (div_nonneg hp.le h2.le)
  unfold peelingLogDepth
  rw [max_eq_left (by exact_mod_cast hn : (4 : ℝ) ≤ n), Nat.cast_add, Nat.cast_one]
  linarith

/-- At the logarithmic cutoff, the residual cardinality is at most
`card(A)/log(card(A))`, whenever the original set has at least four coordinates. -/
theorem peelingRemainder_log_card (A : Finset ℤ) (hn : 4 ≤ A.card) :
    ((peelingRemainder A (peelingLogDepth A.card)).card : ℝ) ≤
      (A.card : ℝ) / Real.log A.card := by
  have hp := peelingLogDepth_pow_gt A.card hn
  have hl : 0 < Real.log A.card := by linarith [(peeling_logs_pos A.card hn).1]
  exact (peelingRemainder_card_le A _).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg A.card) hl hp.le)

/-- The number of all retained pieces and the final residual is bounded by
`(1/log(2)+2/log(log(4)))*log(log(n))`, with a fixed positive numerical constant. -/
theorem peelingLogDepth_count_le (n : ℕ) (hn : 4 ≤ n) :
    (peelingLogDepth n : ℝ) + 1 ≤
      (1 / Real.log 2 + 2 / Real.log (Real.log 4)) * Real.log (Real.log n) := by
  have h4 : 0 < Real.log (Real.log 4) := Real.log_pos log_four_gt_one
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (show (4 : ℝ) ≤ n by exact_mod_cast hn)
  have hll := Real.log_le_log (by linarith [log_four_gt_one] : 0 < Real.log 4) hl
  have hm := mul_le_mul_of_nonneg_left hll (by positivity : 0 ≤ 2 / Real.log (Real.log 4))
  have he : 2 / Real.log (Real.log 4) * Real.log (Real.log 4) = (2 : ℝ) := by
    field_simp
  have hd := peelingLogDepth_le n hn
  rw [show (1 / Real.log 2 + 2 / Real.log (Real.log 4)) * Real.log (Real.log n) =
    Real.log (Real.log n) / Real.log 2 +
      2 / Real.log (Real.log 4) * Real.log (Real.log n) by ring]
  nlinarith only [hd, hm, he]

end StrongMixing
