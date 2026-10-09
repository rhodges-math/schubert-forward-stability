import SchubertForwardStability.Permutations.Classes.Patterns.CatalanEquidistribution
import SchubertForwardStability.Permutations.Random.FiberLaw
import SchubertForwardStability.Permutations.Random.FiniteEvents

/-! # Record-set laws in the two Catalan avoidance classes

Equal finite record fibers give the same uniform record-set distribution and,
by measurable composition, the same record and non-record indicator vectors.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Section 8.
-/

namespace RecordStability

open FinitaryPerm PermutationPattern MeasureTheory ProbabilityTheory
open scoped Classical

/-- The bounded record-indicator vector of a permutation. -/
noncomputable def recordVector (n : ℕ) (w : FinitaryPerm ℕ+) : Fin n → ℕ :=
  fun i => if IsRecord w i.val.succPNat then 1 else 0

/-- The bounded complementary non-record vector of a permutation. -/
noncomputable def complementVector (n : ℕ) (w : FinitaryPerm ℕ+) : Fin n → ℕ :=
  fun i => w.nonRecordIndicator i.val.succPNat

/-- The uniform Catalan avoidance classes have the same bounded record-set law. -/
theorem catalan_recordSet_identDistrib (n : ℕ) :
    IdentDistrib (recordSet n) (recordSet n) (unif (avoiding n p132))
      (unif (avoiding n p231)) := by
  refine ⟨(measurable_of_countable _).aemeasurable,
    (measurable_of_countable _).aemeasurable, ?_⟩
  apply map_unif_eq_of_fibers _ _ _ _
  intro R
  convert card_recordSet_catalan_eq n R using 1 <;> congr 1 <;> ext w <;> simp

/-- Every record-set event has the same probability in the two Catalan classes. -/
theorem catalan_record_probability (n : ℕ) (R : Finset ℕ+) :
    (unif (avoiding n p132)).real {w | recordSet n w = R} =
      (unif (avoiding n p231)).real {w | recordSet n w = R} := by
  have h := (catalan_recordSet_identDistrib n).measure_mem_eq (measurableSet_singleton R)
  simpa only [measureReal_def, Set.preimage, Set.mem_singleton_iff] using
    congrArg ENNReal.toReal h

/-- The record-indicator vectors have the same law in the two Catalan classes. -/
theorem catalan_recordVector_identDistrib (n : ℕ) :
    IdentDistrib (recordVector n) (recordVector n) (unif (avoiding n p132))
      (unif (avoiding n p231)) := by
  let F (R : Finset ℕ+) : Fin n → ℕ := fun i => if i.val.succPNat ∈ R then 1 else 0
  have he (w : FinitaryPerm ℕ+) : F (recordSet n w) = recordVector n w := by
    funext i
    have hi : (i.val.succPNat : ℕ) ≤ n := Nat.succ_le_of_lt i.isLt
    simp only [F, recordVector, mem_recordSet, hi, true_and]
  simpa only [Function.comp_def, he] using
    (catalan_recordSet_identDistrib n).comp (measurable_of_countable F)

/-- The complementary non-record vectors have the same law in the two Catalan classes. -/
theorem catalan_complement_identDistrib (n : ℕ) :
    IdentDistrib (complementVector n) (complementVector n) (unif (avoiding n p132))
      (unif (avoiding n p231)) := by
  let F (R : Finset ℕ+) : Fin n → ℕ := fun i => if i.val.succPNat ∈ R then 0 else 1
  have he (w : FinitaryPerm ℕ+) : F (recordSet n w) = complementVector n w := by
    funext i
    have hi : (i.val.succPNat : ℕ) ≤ n := Nat.succ_le_of_lt i.isLt
    simp only [F, complementVector, nonRecordIndicator, mem_recordSet, hi, true_and]
  simpa only [Function.comp_def, he] using
    (catalan_recordSet_identDistrib n).comp (measurable_of_countable F)

/-- Record-set probabilities and both indicator-vector laws agree for the Catalan classes. -/
theorem catalan_record_law (n : ℕ) :
    (∀ R : Finset ℕ+, (unif (avoiding n p132)).real {w | recordSet n w = R} =
      (unif (avoiding n p231)).real {w | recordSet n w = R}) ∧
    IdentDistrib (recordVector n) (recordVector n) (unif (avoiding n p132))
      (unif (avoiding n p231)) ∧
    IdentDistrib (complementVector n) (complementVector n) (unif (avoiding n p132))
      (unif (avoiding n p231)) :=
  ⟨catalan_record_probability n, catalan_recordVector_identDistrib n,
    catalan_complement_identDistrib n⟩

end RecordStability
