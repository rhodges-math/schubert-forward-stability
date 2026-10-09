import SchubertForwardStability.Permutations.Classes.Boolean.BooleanSupport

/-! # Length bounds for Boolean permutations

Distinct reduced-expression generators identify the Coxeter length with support
cardinality and bound it by the ambient generator interval.
-/

namespace FinitaryPerm

/-- The selected generator support of a Boolean permutation has size equal to its length. -/
theorem IsBoolean.lexFirst_card {w : FinitaryPerm ℕ+} (hw : IsBoolean w) :
    w.lexFirstReducedWord.toFinset.card = w.length :=
  (List.toFinset_card_of_nodup hw.lexFirst_nodup).trans (isReducedWordIn_lexFirst w).1.2

/-- A Boolean permutation supported on the first `n` positions has length at most `n-1`. -/
theorem IsBoolean.length_le {w : FinitaryPerm ℕ+} {n : ℕ} (hw : IsBoolean w)
    (hs : IsSupported n w) : w.length ≤ n - 1 := by
  obtain ⟨word, hword⟩ := exists_reducedWordIn w hs
  have hnodup := hw.reducedWord_nodup hword.1
  have hsub : word.toFinset ⊆ positions (n - 1) := by
    intro i hi
    apply (mem_positions _ _).mpr
    exact Nat.le_sub_one_of_lt (hword.2 i (List.mem_toFinset.mp hi))
  calc
    w.length = word.length := hword.1.2.symm
    _ = word.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ (positions (n - 1)).card := Finset.card_le_card hsub
    _ = n - 1 := by simp

end FinitaryPerm
