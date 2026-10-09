import SchubertForwardStability.Paper.Walk.Overshoot
import SchubertForwardStability.Permutations.Random.Records
import SchubertForwardStability.Permutations.ForMathlib.UniformIntegrals
import Mathlib.Algebra.BigOperators.Intervals

/-! # Uniform upward-step probabilities and overshoot bounds

## Main results

Simultaneous records have reciprocal-square probability, which bounds the expected
tail-maximum overshoot through the number of upward steps.

## Implementation notes

Positions are positive integers, walk values are integers, and expectations are real.
The uniform law is on independent pairs of permutations supported in the ambient size.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Corollary 3.4 and Lemma 3.5.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

/-- A walk step is upward exactly at a simultaneous pair of records. -/
theorem recordWalkStep_eq_one_iff (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    recordWalkStep u v i = 1 ↔ IsRecord u i ∧ IsRecord v i := by
  by_cases hu : IsRecord u i <;> by_cases hv : IsRecord v i <;>
    simp [recordWalkStep_eq, nonRecordIndicator, hu, hv]

/-- A uniform independent pair has reciprocal-square upward probability. -/
theorem uniform_upward_probability (n : ℕ) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    (pairLaw (symmetricGroup n)).real {p | recordWalkStep p.1 p.2 i = 1} =
      1 / (((i : ℕ) : ℝ) ^ 2) := by
  have he : {p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ | recordWalkStep p.1 p.2 i = 1} =
      {w : FinitaryPerm ℕ+ | IsRecord w i} ×ˢ {w | IsRecord w i} := by
    ext p
    exact recordWalkStep_eq_one_iff p.1 p.2 i
  rw [he, pairLaw_eq_prod, measureReal_prod_prod,
    uniform_record_probability n i hi]
  simp only [one_div, pow_two, mul_inv_rev]

/-- The expected upward indicator is the reciprocal square of its position. -/
theorem integral_uniform_upward (n : ℕ) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    (∫ p, (upwardIndicator p.1 p.2 i : ℝ) ∂pairLaw (symmetricGroup n)) =
      1 / (((i : ℕ) : ℝ) ^ 2) := by
  have he : (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
      (upwardIndicator p.1 p.2 i : ℝ)) =
      {p | recordWalkStep p.1 p.2 i = 1}.indicator (fun _ => (1 : ℝ)) := by
    funext p
    by_cases hp : recordWalkStep p.1 p.2 i = 1 <;> simp [upwardIndicator, hp]
  rw [he, integral_indicator_const (1 : ℝ) (by measurability), smul_eq_mul, mul_one]
  exact uniform_upward_probability n i hi

private theorem integral_pair_sum {α : Type*} (W : Finset (FinitaryPerm ℕ+))
    (s : Finset α) (f : α → FinitaryPerm ℕ+ × FinitaryPerm ℕ+ → ℝ) :
    (∫ p, ∑ k ∈ s, f k p ∂pairLaw W) = ∑ k ∈ s, ∫ p, f k p ∂pairLaw W := by
  exact integral_uniform_finsetSum _ _ _

private theorem integral_pair_mono (W : Finset (FinitaryPerm ℕ+))
    (f g : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ → ℝ) (h : ∀ p, f p ≤ g p) :
    (∫ p, f p ∂pairLaw W) ≤ ∫ p, g p ∂pairLaw W := by
  exact integral_uniform_finset_mono _ _ _ (fun p _ => h p)

/-- A uniform expected tail overshoot is bounded by a finite reciprocal-square sum. -/
theorem integral_uniform_overshoot (n : ℕ) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    (∫ p, ((recordWalkMaxFrom n i p.1 p.2 - recordWalk p.1 p.2 i : ℤ) : ℝ)
      ∂pairLaw (symmetricGroup n)) ≤
        ∑ j ∈ Finset.Icc (i : ℕ) n, 1 / ((j : ℝ) ^ 2) := by
  calc
    _ ≤ ∫ p, ∑ k ∈ Finset.range (n + 1 - (i : ℕ)),
        (upwardIndicator p.1 p.2 ((i : ℕ) - 1 + k).succPNat : ℝ)
          ∂pairLaw (symmetricGroup n) := by
      apply integral_pair_mono
      intro p
      have hb := recordWalkMaxFrom_le_upward i p.1 p.2 (by omega : (i : ℕ) ≤ n + 1)
      exact_mod_cast hb
    _ = ∑ j ∈ Finset.Icc (i : ℕ) n, 1 / ((j : ℝ) ^ 2) := by
      rw [integral_pair_sum]
      apply Finset.sum_bij (fun k _ => (i : ℕ) + k)
      · intro k hk
        have hr := Finset.mem_range.mp hk
        have hp := PNat.pos i
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro a ha b hb he
        omega
      · intro j hj
        obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hj
        exact ⟨j - (i : ℕ), Finset.mem_range.mpr (by omega), by omega⟩
      · intro k hk
        have hr := Finset.mem_range.mp hk
        have hp := PNat.pos i
        have hj : (((i : ℕ) - 1 + k).succPNat : ℕ) = (i : ℕ) + k := by
          change (i : ℕ) - 1 + k + 1 = (i : ℕ) + k
          omega
        rw [integral_uniform_upward n _ (by rw [hj]; omega), hj]

end RecordStability
