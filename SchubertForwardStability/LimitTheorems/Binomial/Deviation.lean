import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! # Even-binomial absolute deviation

The two-step Pascal recurrence gives De Moivre's central-binomial expression for
the mean absolute deviation of the symmetric binomial law.

## Main results

* `binomial_deviation_sum`: the unnormalized weighted-sum identity.
* `binomial_deviation_mean`: the normalized mean absolute deviation.

## References

* P. Diaconis and S. Zabell, *Closed form summation for classical distributions: variations
  on a theme of de Moivre*, Statist. Sci. 6 (1991), 284-302, Equation (1.1).
-/

open scoped BigOperators Classical

namespace LimitTheorems

private theorem choose_step (n : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℝ) * f k =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (f k + f (k + 1)) := by
  simpa only [mul_add, Finset.sum_add_distrib] using
    (Finset.sum_choose_succ_mul (R := ℝ) (fun k _ => f k) n)

private theorem choose_two_step (n : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 3), ((n + 2).choose k : ℝ) * f k =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
        (f k + 2 * f (k + 1) + f (k + 2)) := by
  rw [show n + 3 = (n + 1) + 2 by omega,
    show n + 2 = (n + 1) + 1 by omega, choose_step]
  rw [show n + 1 + 1 = n + 2 by omega, choose_step]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [show k + 1 + 1 = k + 2 by omega]
  ring

private theorem abs_four_step (k n : ℕ) :
    |(k : ℝ) - (n + 1)| + 2 * |(k + 1 : ℕ) - (n + 1 : ℝ)| +
      |(k + 2 : ℕ) - (n + 1 : ℝ)| =
      4 * |(k : ℝ) - n| + if k = n then 2 else 0 := by
  by_cases he : k = n
  · subst k
    norm_num
  · rcases lt_or_gt_of_ne he with h | h
    · have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast h
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
        ite_eq_right he, abs_of_nonpos (by linarith : (k : ℝ) - (n + 1) ≤ 0),
        abs_of_nonpos (by linarith : (k : ℝ) + 1 - (n + 1) ≤ 0),
        abs_of_nonpos (by linarith : (k : ℝ) + 2 - (n + 1) ≤ 0),
        abs_of_nonpos (by linarith : (k : ℝ) - n ≤ 0)]
      ring
    · have hnk : (n : ℝ) + 1 ≤ k := by exact_mod_cast h
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
        ite_eq_right he, abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) - (n + 1)),
        abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) + 1 - (n + 1)),
        abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) + 2 - (n + 1)),
        abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) - n)]
      ring

/-- The unnormalized even-binomial absolute deviation has a central-binomial form. -/
theorem binomial_deviation_sum (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 1), |(k : ℝ) - n| *
      ((2 * n).choose k : ℝ)) = n * (Nat.centralBinom n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := choose_two_step (2 * n) (fun k => |(k : ℝ) - (n + 1)|)
    simp only [abs_four_step] at hs
    have hd : (∑ k ∈ Finset.range (2 * n + 1), ((2 * n).choose k : ℝ) *
        (if k = n then 2 else 0)) = 2 * (Nat.centralBinom n : ℝ) := by
      rw [Finset.sum_eq_single n]
      · simp [Nat.centralBinom, mul_comm]
      · intro b _ hb
        simp [hb]
      · intro hn
        exact (hn (Finset.mem_range.mpr (by omega))).elim
    have ht : (∑ k ∈ Finset.range (2 * n + 1), ((2 * n).choose k : ℝ) *
        |(k : ℝ) - n|) = n * (Nat.centralBinom n : ℝ) := by
      simpa only [mul_comm] using ih
    simp only [mul_add, Finset.sum_add_distrib] at hs
    have he : (∑ k ∈ Finset.range (2 * n + 1), ((2 * n).choose k : ℝ) *
        (4 * |(k : ℝ) - n|)) = 4 * n * (Nat.centralBinom n : ℝ) := by
      simp_rw [show ∀ k, ((2 * n).choose k : ℝ) * (4 * |(k : ℝ) - n|) =
        4 * (((2 * n).choose k : ℝ) * |(k : ℝ) - n|) by
          intro k
          ring]
      rw [←Finset.mul_sum, ht]
      ring
    rw [he, hd] at hs
    have hc : (n + 1 : ℝ) * Nat.centralBinom (n + 1) =
        2 * (2 * n + 1) * Nat.centralBinom n := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    simpa only [Nat.cast_add, Nat.cast_one,
      show 2 * (n + 1) = 2 * n + 2 by omega,
      show 2 * n + 2 + 1 = 2 * n + 3 by omega, mul_comm] using hs.trans (by
        nlinarith [hc])

/-- De Moivre's normalized even-binomial absolute deviation identity. -/
theorem binomial_deviation_mean (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 1), |(k : ℝ) - n| *
      ((2 * n).choose k : ℝ) / 2 ^ (2 * n)) =
      n * ((2 * n).choose n : ℝ) / 2 ^ (2 * n) := by
  rw [←Finset.sum_div, binomial_deviation_sum]
  rfl

end LimitTheorems
