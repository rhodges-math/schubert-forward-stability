import SchubertForwardStability.Paper.Boolean.Means
import SchubertForwardStability.Paper.Walk.Differences

/-! # Centered Boolean record increments

Finite uniform integration shows that the centered increments have zero
mean and absolute value at most two.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

/-- The expected Boolean walk increment lies between minus one and one. -/
theorem integral_boolean_step_bounds (n : ℕ) (i : ℕ+) :
    -1 ≤ (∫ p, (recordWalkStep p.1 p.2 i : ℝ) ∂pairLaw (boolean n)) ∧
      (∫ p, (recordWalkStep p.1 p.2 i : ℝ) ∂pairLaw (boolean n)) ≤ 1 := by
  have hLower : (∫ _p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+, (-1 : ℝ)
      ∂pairLaw (boolean n)) ≤
      ∫ p, (recordWalkStep p.1 p.2 i : ℝ) ∂pairLaw (boolean n) := by
    apply integral_uniform_finset_mono
    intro p _
    exact_mod_cast (recordWalkStep_bounds p.1 p.2 i).1
  have hUpper : (∫ p, (recordWalkStep p.1 p.2 i : ℝ) ∂pairLaw (boolean n)) ≤
      ∫ _p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+, (1 : ℝ) ∂pairLaw (boolean n) := by
    apply integral_uniform_finset_mono
    intro p _
    exact_mod_cast (recordWalkStep_bounds p.1 p.2 i).2
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
    And.intro hLower hUpper

/-- The centered Boolean walk increment has zero expectation. -/
theorem integral_centeredBooleanStep (n : ℕ) (i : ℕ+) :
    (∫ p, centeredBooleanStep n i p ∂pairLaw (boolean n)) = 0 := by
  unfold centeredBooleanStep
  have h := integral_uniform_finset_sub ((boolean n).product (boolean n))
    (fun p => (recordWalkStep p.1 p.2 i : ℝ))
    (fun _p => ∫ q, (recordWalkStep q.1 q.2 i : ℝ) ∂pairLaw (boolean n))
  change (∫ p, _ ∂pairLaw (boolean n)) =
    (∫ p, (recordWalkStep p.1 p.2 i : ℝ) ∂pairLaw (boolean n)) -
      ∫ _p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+,
        (∫ q, (recordWalkStep q.1 q.2 i : ℝ) ∂pairLaw (boolean n))
          ∂pairLaw (boolean n) at h
  rw [h]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self]

/-- Every centered Boolean increment has absolute value at most two. -/
theorem abs_centeredBooleanStep_le (n : ℕ) (i : ℕ+)
    (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) : |centeredBooleanStep n i p| ≤ 2 := by
  have hStep := recordWalkStep_bounds p.1 p.2 i
  have hMean := integral_boolean_step_bounds n i
  have hLower : (-1 : ℝ) ≤ (recordWalkStep p.1 p.2 i : ℝ) := by
    exact_mod_cast hStep.1
  have hUpper : (recordWalkStep p.1 p.2 i : ℝ) ≤ 1 := by
    exact_mod_cast hStep.2
  unfold centeredBooleanStep
  apply abs_le.mpr
  constructor <;> linarith [hMean.1, hMean.2]

/-- Expected increments over a finite block telescope to the difference of walk means. -/
theorem booleanMeanWalk_step_sum (n r k : ℕ) :
    ∑ t ∈ Finset.range k, (∫ p, (recordWalkStep p.1 p.2 (r + t).succPNat : ℝ)
      ∂pairLaw (boolean n)) =
      booleanMeanWalk n (r + k).succPNat - booleanMeanWalk n r.succPNat := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [Finset.sum_range_succ, hk, ← booleanMeanWalk_step]
    have hIndex : (r + k).succPNat + 1 = (r + (k + 1)).succPNat := by
      apply PNat.eq
      change r + k + 1 + 1 = r + (k + 1) + 1
      omega
    rw [hIndex]
    ring

/-- A centered Boolean block sums to the endpoint difference minus its mean difference. -/
theorem centeredBooleanStep_sum (n r k : ℕ)
    (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) :
    ∑ t ∈ Finset.range k, centeredBooleanStep n (r + t).succPNat p =
      (recordWalk p.1 p.2 (r + k).succPNat : ℝ) -
        (recordWalk p.1 p.2 r.succPNat : ℝ) -
      (booleanMeanWalk n (r + k).succPNat - booleanMeanWalk n r.succPNat) := by
  unfold centeredBooleanStep
  rw [Finset.sum_sub_distrib, recordWalkStep_sum_real, booleanMeanWalk_step_sum]

end RecordStability
