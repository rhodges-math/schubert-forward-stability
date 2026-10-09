import SchubertForwardStability.Permutations.Classes.Boolean.BooleanRestrictions
import SchubertForwardStability.Permutations.ForMathlib.FibBounds
import SchubertForwardStability.Permutations.Random.FiniteEvents
import SchubertForwardStability.Permutations.Random.FamilyInstances

/-! # Uniform Boolean forward-support tails

Support sublevels are smaller Boolean families. Their finite
uniform probabilities and positive odd Fibonacci growth give a geometric
bound for the deficit of the maximum support of two independent permutations.
-/

namespace FinitaryPerm

open MeasureTheory ProbabilityTheory
open scoped Classical

private theorem card_real_fib (n : ℕ) :
    ((boolean n).card : ℝ) = (Int.fib (2 * (n : ℤ) - 1) : ℝ) := by
  exact_mod_cast card_boolean_int_fib_all n

/-- A positive Boolean forward-support sublevel has the smaller-family Fibonacci mass. -/
theorem boolean_forward_probability (n m : ℕ) (hm : m ≤ n) (hPositive : 1 ≤ m) :
    (unif (boolean n)).real {w | w.forwardStability ≤ m} =
      (Int.fib (2 * (m : ℤ) - 1) : ℝ) / (Int.fib (2 * (n : ℤ) - 1) : ℝ) := by
  rw [unif_real_event]
  simp only [Set.mem_ofPred_eq]
  rw [filter_forwardStability_le_boolean n m hm hPositive, card_real_fib, card_real_fib]

/-- Independent Boolean pair support sublevels have the square of the marginal Fibonacci mass. -/
theorem boolean_pair_forward_probability (n m : ℕ) (hm : m ≤ n) (hPositive : 1 ≤ m) :
    (pairLaw (boolean n)).real {p | max p.1.forwardStability p.2.forwardStability ≤ m} =
      ((Int.fib (2 * (m : ℤ) - 1) : ℝ) / (Int.fib (2 * (n : ℤ) - 1) : ℝ)) ^ 2 := by
  have hSet : {p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ |
      max p.1.forwardStability p.2.forwardStability ≤ m} =
      {w : FinitaryPerm ℕ+ | w.forwardStability ≤ m} ×ˢ
        {w : FinitaryPerm ℕ+ | w.forwardStability ≤ m} := by
    ext p
    change max p.1.forwardStability p.2.forwardStability ≤ m ↔
      p.1.forwardStability ≤ m ∧ p.2.forwardStability ≤ m
    exact max_le_iff
  rw [hSet, pairLaw_eq_prod, measureReal_prod_prod,
    boolean_forward_probability n m hm hPositive, pow_two]

/-- Positive deficits of the maximum independent Boolean support have factor-four tails. -/
theorem boolean_pair_deficit_le (n t : ℕ) (htPositive : 1 ≤ t) (ht : t < n) :
    (pairLaw (boolean n)).real {p | t ≤ n - max p.1.forwardStability p.2.forwardStability} ≤
      (1 / 4 : ℝ) ^ t := by
  have hSet : {p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ |
      t ≤ n - max p.1.forwardStability p.2.forwardStability} =
      {p | max p.1.forwardStability p.2.forwardStability ≤ n - t} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    omega
  rw [hSet, boolean_pair_forward_probability n (n - t) (Nat.sub_le _ _) (by omega)]
  have hGrowth := Int.fib_odd_stride_le n t ht
  have hIndex : 2 * (((n - t : ℕ) : ℤ)) - 1 = 2 * ((n : ℤ) - (t : ℤ)) - 1 := by
    rw [Nat.cast_sub ht.le]
  rw [← hIndex] at hGrowth
  have hDen : (0 : ℝ) < (Int.fib (2 * (n : ℤ) - 1) : ℝ) := by
    have h := Int.fib_two_mul_add_one_pos (n := (n : ℤ) - 1)
    rw [show 2 * ((n : ℤ) - 1) + 1 = 2 * (n : ℤ) - 1 by ring] at h
    exact_mod_cast h
  have hNum : (0 : ℝ) ≤ (Int.fib (2 * ((n - t : ℕ) : ℤ) - 1) : ℝ) := by
    have h := Int.fib_two_mul_add_one_pos (n := ((n - t : ℕ) : ℤ) - 1)
    rw [show 2 * (((n - t : ℕ) : ℤ) - 1) + 1 =
      2 * ((n - t : ℕ) : ℤ) - 1 by ring] at h
    exact_mod_cast h.le
  have hPow : (0 : ℝ) < 2 ^ t := by positivity
  have hCast : (2 : ℝ) ^ t * (Int.fib (2 * ((n - t : ℕ) : ℤ) - 1) : ℝ) ≤
      (Int.fib (2 * (n : ℤ) - 1) : ℝ) := by exact_mod_cast hGrowth
  have hRatio : (Int.fib (2 * ((n - t : ℕ) : ℤ) - 1) : ℝ) /
      (Int.fib (2 * (n : ℤ) - 1) : ℝ) ≤ (1 / 2 : ℝ) ^ t := by
    apply (div_le_iff₀ hDen).mpr
    calc
      _ ≤ (Int.fib (2 * (n : ℤ) - 1) : ℝ) / (2 : ℝ) ^ t :=
        (le_div_iff₀ hPow).mpr (by nlinarith)
      _ = _ := by rw [one_div, inv_pow]; ring
  calc
    _ ≤ ((1 / 2 : ℝ) ^ t) ^ 2 := by gcongr
    _ = (1 / 4 : ℝ) ^ t := by
      rw [← pow_mul, Nat.mul_comm t 2, pow_mul]
      norm_num

end FinitaryPerm
