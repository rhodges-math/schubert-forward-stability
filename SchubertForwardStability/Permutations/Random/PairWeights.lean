import SchubertForwardStability.Permutations.Random.SubsetCounts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde

/-! # Binomially weighted maxima

## Main results

The finite weighted maximum of two independent subset sizes satisfies a Pascal
recurrence. The diagonal correction is the central binomial coefficient.
-/

open scoped BigOperators Classical

namespace FinitaryPerm

/-- The binomially weighted maximum of two sizes. -/
def pairSizeMaxWeight (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
    n.choose k * n.choose l * max k l

private theorem choose_weight_step (n : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.range (n + 2), (n + 1).choose k * f k =
      ∑ k ∈ Finset.range (n + 1), n.choose k * (f k + f (k + 1)) := by
  simpa only [Nat.cast_id, mul_add, Finset.sum_add_distrib] using
    (Finset.sum_choose_succ_mul (R := ℕ) (fun k _ => f k) n)

private theorem choose_pair_step (n : ℕ) (f : ℕ → ℕ → ℕ) :
    ∑ k ∈ Finset.range (n + 2), ∑ l ∈ Finset.range (n + 2),
      (n + 1).choose k * (n + 1).choose l * f k l =
    ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
      n.choose k * n.choose l *
        (f k l + f (k + 1) l + f k (l + 1) + f (k + 1) (l + 1)) := by
  calc
    _ = ∑ k ∈ Finset.range (n + 2), (n + 1).choose k *
        (∑ l ∈ Finset.range (n + 2), (n + 1).choose l * f k l) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ k ∈ Finset.range (n + 1), n.choose k *
        ((∑ l ∈ Finset.range (n + 2), (n + 1).choose l * f k l) +
          ∑ l ∈ Finset.range (n + 2), (n + 1).choose l * f (k + 1) l) :=
      choose_weight_step n (fun k => ∑ l ∈ Finset.range (n + 2),
        (n + 1).choose l * f k l)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [choose_weight_step, choose_weight_step, ←Finset.sum_add_distrib,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

private theorem max_four_step (k l : ℕ) :
    max k l + max (k + 1) l + max k (l + 1) + max (k + 1) (l + 1) =
      4 * max k l + 2 + if k = l then 1 else 0 := by
  split_ifs <;> omega

private theorem choose_pair_total (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
      n.choose k * n.choose l = 4 ^ n := by
  rw [←Finset.sum_mul_sum, Nat.sum_range_choose, ←mul_pow]
  norm_num

private theorem choose_pair_diagonal (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
      n.choose k * n.choose l * (if k = l then 1 else 0) = Nat.centralBinom n := by
  unfold Nat.centralBinom
  rw [←Nat.sum_range_choose_sq]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single k]
  · simp only [ite_true, mul_one, pow_two]
  · intro l _ hl
    simp only [ite_eq_right (Ne.symm hl), mul_zero]
  · exact fun hn => (hn hk).elim

/-- The weighted maximum recurrence has the central-binomial diagonal correction. -/
theorem pairSizeMaxWeight_succ (n : ℕ) :
    pairSizeMaxWeight (n + 1) =
      4 * pairSizeMaxWeight n + 2 * 4 ^ n + Nat.centralBinom n := by
  unfold pairSizeMaxWeight
  rw [show n + 1 + 1 = n + 2 by omega, choose_pair_step]
  simp_rw [max_four_step]
  have he (k l : ℕ) : n.choose k * n.choose l *
      (4 * max k l + 2 + if k = l then 1 else 0) =
      4 * (n.choose k * n.choose l * max k l) +
        2 * (n.choose k * n.choose l) +
        n.choose k * n.choose l * (if k = l then 1 else 0) := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ←Finset.mul_sum]
  have ht : (∑ k ∈ Finset.range (n + 1), n.choose k *
      (∑ l ∈ Finset.range (n + 1), n.choose l)) = 4 ^ n := by
    simpa only [Finset.mul_sum] using choose_pair_total n
  rw [ht, choose_pair_diagonal]

/-- Twice the finite weighted maximum has a closed central-binomial expression. -/
theorem pairSizeMaxWeight_twice (n : ℕ) :
    2 * pairSizeMaxWeight n = n * 4 ^ n + n * Nat.centralBinom n := by
  induction n with
  | zero => simp [pairSizeMaxWeight]
  | succ n ih =>
    rw [pairSizeMaxWeight_succ, pow_succ]
    have hc := Nat.succ_mul_centralBinom_succ n
    nlinarith

/-- Twice the summed size maximum over pairs of subsets has the same closed expression. -/
theorem sum_subset_pair_max_twice (n : ℕ) :
    2 * (∑ V ∈ (positions n).powerset, ∑ W ∈ (positions n).powerset,
      max V.card W.card) = n * 4 ^ n + n * (2 * n).choose n := by
  rw [sum_subset_pair_sizes]
  simp only [nsmul_eq_mul]
  exact pairSizeMaxWeight_twice n

end FinitaryPerm
