import SchubertForwardStability.Permutations.Classes.NormalWords
import SchubertForwardStability.Permutations.Classes.Boolean.BooleanCommutations

/-! # Lexicographic normal forms of Boolean reduced words

Distinctness and the commutation-only connectivity of Boolean reduced expressions
turn neighboring-generator orders into a characterization of the least word.

## References

Patricia Hersh, *On optimizing discrete Morse functions*, Advances in Applied
Mathematics 35(3), 294-322 (2005).
-/

namespace FinitaryPerm

/-- A Boolean reduced word is the selected least word exactly when it has no distant inversion. -/
theorem IsBoolean.eq_lexFirst_iff {w : FinitaryPerm ℕ+} (hw : IsBoolean w)
    (word : List ℕ+) (hword : IsReducedWord w word) :
    word = w.lexFirstReducedWord ↔ ¬HasCommutingInversion word := by
  constructor
  · rintro rfl
    exact not_hasCommutingInversion_lexFirst w
  · intro hNo
    apply normalWord_eq_of_projections word w.lexFirstReducedWord
      (hw.reducedWord_nodup hword) hw.lexFirst_nodup hNo
      (not_hasCommutingInversion_lexFirst w)
      (reducedWord_toFinset_eq w word _ hword (isReducedWordIn_lexFirst w).1)
    intro a b hab
    exact commutations_neighborProjection_eq (hw.reducedWord_commutations word _
      hword (isReducedWordIn_lexFirst w).1) a b hab

end FinitaryPerm
