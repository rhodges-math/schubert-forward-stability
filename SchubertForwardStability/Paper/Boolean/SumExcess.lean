import SchubertForwardStability.Paper.Boolean.BoundSeries

/-! # A uniform bound for the sum of Boolean walk excesses

Positive earlier excesses are bounded by the distance-dependent terms.
Distinct earlier positions give distinct backwards distances, so their finite
sum is bounded by the same convergent series at every ambient size.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory
open scoped Classical BigOperators

/-- The sum of all preterminal positive Boolean walk excess means has a uniform finite bound. -/
theorem sum_boolean_excess_le (r : ℕ+) :
    (∑ i ∈ positions ((r : ℕ) - 1),
      ∫ p, max ((recordWalk p.1 p.2 i : ℝ) - recordWalk p.1 p.2 r) 0
        ∂pairLaw (boolean (r : ℕ))) ≤ ∑' k, booleanBacktrackBound k := by
  have hr := r.pos
  calc
    _ ≤ ∑ i ∈ positions ((r : ℕ) - 1), booleanBacktrackBound ((r : ℕ) - (i : ℕ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := (mem_positions _ _).mp hi
      have hip := i.pos
      have hSize : (r : ℕ) - 1 + 1 = (r : ℕ) := by omega
      have hStart : ((i : ℕ) - 1).succPNat = i := by
        apply PNat.eq
        change (i : ℕ) - 1 + 1 = (i : ℕ)
        omega
      have hEnd : ((i : ℕ) - 1 + ((r : ℕ) - (i : ℕ))).succPNat = r := by
        apply PNat.eq
        change (i : ℕ) - 1 + ((r : ℕ) - (i : ℕ)) + 1 = (r : ℕ)
        omega
      have h := integral_boolean_backtrack_bound ((r : ℕ) - 1) ((i : ℕ) - 1)
        ((r : ℕ) - (i : ℕ)) (by omega)
      simpa only [hSize, hStart, hEnd] using h
    _ ≤ _ := by
      have hInject : Set.InjOn (fun i : ℕ+ => (r : ℕ) - (i : ℕ))
          (positions ((r : ℕ) - 1) : Set ℕ+) := by
        intro i hi j hj he
        change (r : ℕ) - (i : ℕ) = (r : ℕ) - (j : ℕ) at he
        have hi' := (mem_positions _ _).mp hi
        have hj' := (mem_positions _ _).mp hj
        apply PNat.eq
        omega
      have hImage :
          (∑ k ∈ (positions ((r : ℕ) - 1)).image (fun i : ℕ+ => (r : ℕ) - (i : ℕ)),
            booleanBacktrackBound k) =
          ∑ i ∈ positions ((r : ℕ) - 1), booleanBacktrackBound ((r : ℕ) - (i : ℕ)) := by
        rw [Finset.sum_image hInject]
      rw [← hImage]
      exact Summable.sum_le_tsum _ (fun k _ => booleanBacktrackBound_nonneg k)
        summable_booleanBacktrackBound

end RecordStability
