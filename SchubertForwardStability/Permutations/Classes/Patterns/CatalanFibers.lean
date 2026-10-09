import SchubertForwardStability.Permutations.Classes.Patterns.RecordFiberRecursion
import SchubertForwardStability.Permutations.Classes.Patterns.CatalanCounts
import SchubertForwardStability.Permutations.Classes.Patterns.CatalanGaps

/-! # Catalan products for prescribed record gaps

For `π = 132` or `π = 231`, the number of `π`-avoiders of size `n` with a prescribed record
set `R` containing `1` is the product of the Catalan numbers `Cat(r' - r - 1)` over `r ∈ R`,
where `r'` is the next record after `r`, or `n+1`. The proof deletes the final record and
uses strong induction on `n`.

## Main results

* `PermutationPattern.recordFiberCard_gapProduct`: the record-fiber count is the Catalan gap
  product.
-/

namespace PermutationPattern

open FinitaryPerm
open scoped Classical

/-- Either three-entry Catalan avoidance family has the Catalan cardinality. -/
theorem card_avoiding_catalan (n : ℕ) (π : PermutationPattern 3)
    (hπ : π = p132 ∨ π = p231) : (avoiding n π).card = catalan n := by
  rcases hπ with hπ | hπ <;> subst π
  · exact card_avoiding132_catalan n
  · exact card_avoiding231_catalan n

/-- A bounded record fiber of either Catalan pattern is the product over its record gaps. -/
theorem recordFiberCard_gapProduct (n : ℕ) (π : PermutationPattern 3)
    (hπ : π = p132 ∨ π = p231) (R : Finset ℕ+) (hR : R ⊆ positions n)
    (hOne : 1 ∈ R) : recordFiberCard n π R = recordGapProduct n R := by
  induction n using Nat.strong_induction_on generalizing R with
  | h n ih =>
    let r := R.max' ⟨1, hOne⟩
    have hr : r ∈ R := Finset.max'_mem R _
    have hLast : ∀ s ∈ R, s ≤ r := fun s hs => Finset.le_max' R s hs
    have hrBound := (mem_positions n r).mp (hR hr)
    have hrPos := r.pos
    have hErase := erase_max_positions R r hLast
    have hSmall : (r : ℕ) - 1 < n := by omega
    rw [recordFiber_recursion n π hπ R hR r hr hLast,
      card_avoiding_catalan (n - (r : ℕ)) π hπ,
      recordGapProduct_erase_max n R r hr hLast hrBound]
    congr 1
    by_cases hFirst : r = 1
    · have hZero : (r : ℕ) - 1 = 0 := by rw [hFirst]; rfl
      have hEmpty : R.erase r = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro s hs
        have h := (mem_positions ((r : ℕ) - 1) s).mp (hErase hs)
        have := s.pos
        omega
      rw [hZero, hEmpty, recordFiberCard_zero π (by decide), ite_eq_left rfl,
        recordGapProduct_empty]
    · have hOneErase : (1 : ℕ+) ∈ R.erase r := Finset.mem_erase.mpr ⟨Ne.symm hFirst, hOne⟩
      exact ih ((r : ℕ) - 1) hSmall (R.erase r) hErase hOneErase

end PermutationPattern
