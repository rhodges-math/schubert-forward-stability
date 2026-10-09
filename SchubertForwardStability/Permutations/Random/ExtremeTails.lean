import SchubertForwardStability.Permutations.Random.MaximumLaw
import SchubertForwardStability.Permutations.Random.CardTail
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Extreme tails of uniform subset statistics

## Main results

The exact prefix-maximum law and the binomial Chernoff estimate give simultaneous
exponential bounds on the two three-quarter threshold events.
-/

open MeasureTheory Filter
open scoped Classical

namespace FinitaryPerm

/-- A nonnegative real maximum threshold is evaluated by its natural floor. -/
theorem subsetLaw_maximum_real_le (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (subsetLaw n).real {V | ((V.sup PNat.val : ℕ) : ℝ) ≤ t} =
      (2 : ℝ) ^ min n ⌊t⌋₊ / (2 : ℝ) ^ n := by
  have he : {V : Finset ℕ+ | ((V.sup PNat.val : ℕ) : ℝ) ≤ t} =
      {V | V.sup PNat.val ≤ ⌊t⌋₊} := by
    ext V
    exact (Nat.le_floor_iff ht).symm
  rw [he, subsetLaw_maximum_le_real]

/-- A selected maximum at most three quarters of the ambient size is exponentially rare. -/
theorem subsetLaw_maximum_extreme_tail (n : ℕ) :
    (subsetLaw n).real {V | ((V.sup PNat.val : ℕ) : ℝ) ≤ (3 : ℝ) * n / 4} ≤
      Real.exp (-(Real.log 2 / 4) * n) := by
  have hn : (0 : ℝ) ≤ (3 : ℝ) * n / 4 := by positivity
  have hm : ⌊(3 : ℝ) * n / 4⌋₊ ≤ n := by
    apply Nat.floor_le_of_le
    have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [subsetLaw_maximum_real_le n _ hn, min_eq_right hm]
  have hp (k : ℕ) : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hp, hp, ←Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hf := Nat.floor_le hn
  have hl : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hf hl]

/-- One positive rate bounds both extreme events for every ambient size. -/
theorem subsetLaw_extreme_tails :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      (subsetLaw n).real {V | (3 : ℝ) * n / 4 ≤ V.card} ≤ Real.exp (-c * n) ∧
        (subsetLaw n).real {V | ((V.sup PNat.val : ℕ) : ℝ) ≤ (3 : ℝ) * n / 4} ≤
          Real.exp (-c * n) := by
  let a : ℝ := (3 / 4 : ℝ) * Real.log 3 - Real.log 2
  let b : ℝ := Real.log 2 / 4
  have ha : 0 < a := card_tail_rate_pos
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  refine ⟨min a b, lt_min ha hb, fun n => ?_⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · refine (subsetLaw_card_extreme_tail n).trans (Real.exp_le_exp.mpr ?_)
    change -a * (n : ℝ) ≤ -min a b * n
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) hn
  · refine (subsetLaw_maximum_extreme_tail n).trans (Real.exp_le_exp.mpr ?_)
    change -b * (n : ℝ) ≤ -min a b * n
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) hn

/-- The common extreme-tail bounds in eventual form. -/
theorem subsetLaw_extreme_tails_eventually :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (subsetLaw n).real {V | (3 : ℝ) * n / 4 ≤ V.card} ≤ Real.exp (-c * n) ∧
        (subsetLaw n).real {V | ((V.sup PNat.val : ℕ) : ℝ) ≤ (3 : ℝ) * n / 4} ≤
          Real.exp (-c * n) := by
  obtain ⟨c, hc, h⟩ := subsetLaw_extreme_tails
  exact ⟨c, hc, Eventually.of_forall h⟩

end FinitaryPerm
