import SchubertForwardStability.Permutations.Classes.LexWord

/-! # Boolean permutations

## Main definitions

* `IsBoolean`: existence of a reduced expression with no repeated letter.
* `boolean`: Boolean permutations supported in an initial positive interval.

## Implementation notes

Booleanity is defined through reduced expressions, not through pattern avoidance.
-/

namespace FinitaryPerm

open scoped Classical

/-- A permutation is Boolean if some reduced expression uses no letter twice. -/
def IsBoolean (w : FinitaryPerm ℕ+) : Prop :=
  ∃ word : List ℕ+, IsReducedWord w word ∧ word.Nodup

/-- Boolean permutations in the symmetric group supported on the first `n` positions. -/
noncomputable def boolean (n : ℕ) : Finset (FinitaryPerm ℕ+) :=
  (symmetricGroup n).filter IsBoolean

/-- Boolean-family membership is support containment together with Booleanity. -/
@[simp]
theorem mem_boolean (n : ℕ) (w : FinitaryPerm ℕ+) :
    w ∈ boolean n ↔ IsSupported n w ∧ IsBoolean w := by
  simp only [boolean, Finset.mem_filter, mem_symmetricGroup]

/-- Identity is Boolean, represented by the empty reduced word. -/
theorem isBoolean_one : IsBoolean (1 : FinitaryPerm ℕ+) :=
  ⟨[], (isReducedWordIn_one 0).1, List.nodup_nil⟩

/-- Every ambient Boolean family contains identity, including at size zero. -/
theorem one_mem_boolean (n : ℕ) : (1 : FinitaryPerm ℕ+) ∈ boolean n :=
  (mem_boolean n 1).mpr ⟨isSupported_one n, isBoolean_one⟩

end FinitaryPerm
