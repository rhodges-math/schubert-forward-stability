import SchubertForwardStability.Permutations.Random.SubsetCounts
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # Sums of subset maxima

## Main results

The sum of the maximum selected position satisfies the last-position recurrence.
Its closed finite expression retains the empty ambient set.
-/

open scoped BigOperators Classical

namespace FinitaryPerm

/-- Adding the last positive position extends the initial interval by one point. -/
theorem positions_succ_insert (n : ℕ) :
    positions (n + 1) = insert (Nat.succPNat n) (positions n) := by
  ext j
  simp only [Finset.mem_insert, mem_positions]
  constructor
  · intro hj
    by_cases h : j.val ≤ n
    · exact Or.inr h
    · left
      apply PNat.eq
      change j.val = n + 1
      omega
  · intro hj
    rcases hj with rfl | hj
    · exact le_rfl
    · omega

/-- Every admissible subset has selected maximum at most the ambient size. -/
theorem subset_maximum_le (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) :
    V.sup PNat.val ≤ n := by
  apply Finset.sup_le
  intro j hj
  exact (mem_positions n j).mp (hV hj)

private theorem subset_max_insert (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) :
    (insert (Nat.succPNat n) V).sup PNat.val = n + 1 := by
  rw [Finset.sup_insert]
  change max (n + 1) (V.sup PNat.val) = n + 1
  exact max_eq_left (by have h := subset_maximum_le n V hV; omega)

/-- The total selected maximum increases by the new last position in half the subsets. -/
theorem sum_subset_maximum_succ (n : ℕ) :
    (∑ V ∈ (positions (n + 1)).powerset, V.sup PNat.val) =
      (∑ V ∈ (positions n).powerset, V.sup PNat.val) + (n + 1) * 2 ^ n := by
  have hn : Nat.succPNat n ∉ positions n := by
    rw [mem_positions]
    change ¬n + 1 ≤ n
    omega
  rw [positions_succ_insert, Finset.sum_powerset_insert hn]
  have he : (∑ V ∈ (positions n).powerset,
      (insert (Nat.succPNat n) V).sup PNat.val) =
      ∑ _V ∈ (positions n).powerset, (n + 1) := by
    apply Finset.sum_congr rfl
    intro V hV
    exact subset_max_insert n V (Finset.mem_powerset.mp hV)
  rw [he, Finset.sum_const, Finset.card_powerset, card_positions, nsmul_eq_mul]
  simp only [Nat.cast_id]
  ring

/-- The exact total selected maximum, expressed without truncated subtraction. -/
theorem sum_subset_maximum_closed (n : ℕ) :
    (∑ V ∈ (positions n).powerset, V.sup PNat.val) + 2 ^ n = n * 2 ^ n + 1 := by
  induction n with
  | zero => simp [positions_zero]
  | succ n ih =>
    rw [sum_subset_maximum_succ, pow_succ]
    nlinarith

end FinitaryPerm
