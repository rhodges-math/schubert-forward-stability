import SchubertForwardStability.Permutations.Random.BooleanMoments
import SchubertForwardStability.Paper.Walk.Basic
import SchubertForwardStability.Permutations.ForMathlib.UniformIntegrals

/-! # Mean Boolean record walks

The mean walk and its finite maximum use the independent uniform pair
law. Indicator expectations give exact pair-step means and the walk recurrence.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Section 5.4.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory
open scoped Classical

private theorem integral_pair_sub (n : ℕ)
    (f g : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ → ℝ) :
    (∫ p, f p - g p ∂pairLaw (boolean n)) =
      (∫ p, f p ∂pairLaw (boolean n)) - ∫ p, g p ∂pairLaw (boolean n) :=
  integral_uniform_finset_sub _ _ _

/-- The expected record walk under the independent uniform Boolean pair law. -/
noncomputable def booleanMeanWalk (n : ℕ) (i : ℕ+) : ℝ :=
  ∫ p, (recordWalk p.1 p.2 i : ℝ) ∂pairLaw (boolean n)

/-- The finite maximum of Boolean record-walk means through the ambient terminal position. -/
noncomputable def booleanMeanMax (n : ℕ) : ℝ :=
  (positions (n + 1)).sup'
    ⟨1, (mem_positions (n + 1) 1).mpr (Nat.succ_pos n)⟩ (booleanMeanWalk n)

/-- The centered increment of the independent uniform Boolean record walk. -/
noncomputable def centeredBooleanStep (n : ℕ) (i : ℕ+)
    (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) : ℝ :=
  (recordWalkStep p.1 p.2 i : ℝ) -
    ∫ q, (recordWalkStep q.1 q.2 i : ℝ) ∂pairLaw (boolean n)

/-- The two independent Boolean pair coordinates have the same non-record mean. -/
theorem integral_boolean_pair_nonRecord (n : ℕ) (i : ℕ+) :
    (∫ p, (p.1.nonRecordIndicator i : ℝ) ∂pairLaw (boolean n)) =
        1 - (booleanRecordCount n i : ℝ) / (Int.fib (2 * (n : ℤ) - 1) : ℝ) ∧
      (∫ p, (p.2.nonRecordIndicator i : ℝ) ∂pairLaw (boolean n)) =
        1 - (booleanRecordCount n i : ℝ) / (Int.fib (2 * (n : ℤ) - 1) : ℝ) := by
  constructor
  · calc
      _ = ∫ w, (w.nonRecordIndicator i : ℝ) ∂unif (boolean n) :=
        ((identDistrib_pairLaw_fst ⟨1, one_mem_boolean n⟩).comp
          (measurable_of_countable (fun w : FinitaryPerm ℕ+ =>
            (w.nonRecordIndicator i : ℝ)))).integral_eq
      _ = _ := integral_boolean_nonRecord n i
  · calc
      _ = ∫ w, (w.nonRecordIndicator i : ℝ) ∂unif (boolean n) :=
        ((identDistrib_pairLaw_snd ⟨1, one_mem_boolean n⟩).comp
          (measurable_of_countable (fun w : FinitaryPerm ℕ+ =>
            (w.nonRecordIndicator i : ℝ)))).integral_eq
      _ = _ := integral_boolean_nonRecord n i

/-- The Boolean mean increment is twice its record probability minus one. -/
theorem integral_boolean_step (n : ℕ) (i : ℕ+) :
    (∫ p, (recordWalkStep p.1 p.2 i : ℝ) ∂pairLaw (boolean n)) =
      2 * ((booleanRecordCount n i : ℝ) / (Int.fib (2 * (n : ℤ) - 1) : ℝ)) - 1 := by
  have he : (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
      (recordWalkStep p.1 p.2 i : ℝ)) =
      (fun p => (1 - (p.1.nonRecordIndicator i : ℝ)) - (p.2.nonRecordIndicator i : ℝ)) := by
    funext p
    rw [recordWalkStep_eq]
    push_cast
    ring
  rw [he, integral_pair_sub, integral_pair_sub]
  obtain ⟨hu, hv⟩ := integral_boolean_pair_nonRecord n i
  rw [hu, hv]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- Differences of consecutive Boolean walk means equal the expected increment. -/
theorem booleanMeanWalk_step (n : ℕ) (i : ℕ+) :
    booleanMeanWalk n (i + 1) - booleanMeanWalk n i =
      ∫ p, (recordWalkStep p.1 p.2 i : ℝ) ∂pairLaw (boolean n) := by
  unfold booleanMeanWalk recordWalkStep
  simp only [Int.cast_sub]
  exact (integral_uniform_finset_sub _ _ _).symm

end RecordStability
