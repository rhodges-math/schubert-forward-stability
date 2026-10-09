import SchubertForwardStability.Permutations.Classes.Patterns.CatalanFibers

/-! # Equality of Catalan record fibers at every finite record set

The gap product agrees for the two three-entry patterns on admissible nonempty
record sets. All other fibers are empty, except for the common empty-size identity
fiber, so the equality holds for every ambient size and every finite record set.
-/

namespace PermutationPattern

open FinitaryPerm
open scoped Classical

/-- A record fiber is empty when its specified record set is not ambient-bounded. -/
theorem recordFiberCard_unbounded {k n : ℕ} (π : PermutationPattern k) (R : Finset ℕ+)
    (hR : ¬R ⊆ positions n) : recordFiberCard n π R = 0 := by
  unfold recordFiberCard
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have he := ((mem_recordFiber n π R w).mp hw).2
  apply hR
  rw [← he]
  exact Finset.filter_subset _ _

/-- In positive ambient size, no record fiber can omit the first position. -/
theorem recordFiberCard_missing_first {k n : ℕ} (π : PermutationPattern k)
    (hn : 0 < n) (R : Finset ℕ+) (hOne : (1 : ℕ+) ∉ R) : recordFiberCard n π R = 0 := by
  unfold recordFiberCard
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have he := ((mem_recordFiber n π R w).mp hw).2
  apply hOne
  rw [← he]
  exact (mem_recordSet n w 1).mpr ⟨by change 1 ≤ n; omega, isRecord_first w⟩

/-- The two Catalan avoidance classes have the same record fibers, including all boundaries. -/
theorem recordFiberCard_catalan_eq (n : ℕ) (R : Finset ℕ+) :
    recordFiberCard n p132 R = recordFiberCard n p231 R := by
  by_cases hn : n = 0
  · subst n
    rw [recordFiberCard_zero p132 (by decide), recordFiberCard_zero p231 (by decide)]
  by_cases hR : R ⊆ positions n
  · by_cases hOne : (1 : ℕ+) ∈ R
    · rw [recordFiberCard_gapProduct n p132 (Or.inl rfl) R hR hOne,
        recordFiberCard_gapProduct n p231 (Or.inr rfl) R hR hOne]
    · rw [recordFiberCard_missing_first p132 (by omega) R hOne,
        recordFiberCard_missing_first p231 (by omega) R hOne]
  · rw [recordFiberCard_unbounded p132 R hR, recordFiberCard_unbounded p231 R hR]

/-- The full record-set filters of the two Catalan classes have equal cardinalities. -/
theorem card_recordSet_catalan_eq (n : ℕ) (R : Finset ℕ+) :
    ((avoiding n p132).filter fun w => recordSet n w = R).card =
      ((avoiding n p231).filter fun w => recordSet n w = R).card := by
  simpa only [recordFiberCard, recordFiber] using recordFiberCard_catalan_eq n R

end PermutationPattern
