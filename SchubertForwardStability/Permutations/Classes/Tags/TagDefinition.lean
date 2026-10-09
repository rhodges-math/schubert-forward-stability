import SchubertForwardStability.Permutations.Classes.Tags.TagValidity
import SchubertForwardStability.Permutations.Classes.Tags.TagReadout
import SchubertForwardStability.Permutations.Classes.Tags.TagInjective

/-! # Local validity and external indices for boundary tags

A boundary tag word is valid exactly when its first symbol is not a continuation and no
continuation follows an absent symbol. A permutation supported in `[1, n]` has the tag zero
at the external indices `0` and `t >= n`.
-/

namespace FinitaryPerm

/-- A tag word is valid exactly when its first symbol is not a continuation and no
continuation follows an absent symbol. -/
theorem isTagWord_local_iff {m : ℕ} (T : Fin m → BlockTag) :
    IsTagWord T ↔
      (∀ i : Fin m, i.val = 0 → T i ≠ .cont) ∧
        ∀ i j : Fin m, j.val + 1 = i.val → T i = .cont → T j ≠ .zero := by
  constructor
  · intro h
    constructor
    · intro i hi hc
      rcases h i hc with ⟨_, hFalse⟩ | ⟨j, hj, _⟩
      · cases hFalse
      · omega
    · intro i j hji hc
      rcases h i hc with ⟨hi, _⟩ | ⟨k, hki, hk⟩
      · omega
      · have he : k = j := Fin.ext (by omega)
        rwa [he] at hk
  · rintro ⟨hFirst, hPrevious⟩ i hc
    by_cases hi : i.val = 0
    · exact False.elim ((hFirst i hi) hc)
    · right
      have hp : 0 < i.val := by omega
      let j : Fin m := ⟨i.val - 1, by have hb := i.isLt; omega⟩
      have hji : j.val + 1 = i.val := by dsimp [j]; omega
      exact ⟨j, hji, hPrevious i j hji hc⟩

/-- A generator that continues a decreasing block is present in the selected word. -/
theorem generatorContinues_present (w : FinitaryPerm ℕ+) (t : ℕ)
    (h : GeneratorContinues w t) : GeneratorPresent w t := by
  obtain ⟨i, j, hi, _, hInfix⟩ := h
  exact ⟨i, hi, hInfix.sublist.subset (by simp)⟩

/-- A supported permutation has no generator or continuation at external tag indices. -/
theorem blockTag_outside (n : ℕ) (w : FinitaryPerm ℕ+) (hw : IsSupported n w)
    (t : ℕ) (ht : t = 0 ∨ n ≤ t) :
    ¬GeneratorPresent w t ∧ ¬GeneratorContinues w t ∧ blockTag n w t = .zero := by
  have hPresent : ¬GeneratorPresent w t := by
    rintro ⟨i, hi, hWord⟩
    have hp := i.pos
    have hb := lexFirst_letter_bound w hw i hWord
    rcases ht with ht | ht <;> omega
  refine ⟨hPresent, fun hc => hPresent (generatorContinues_present w t hc), ?_⟩
  rcases ht with rfl | ht
  · exact blockTag_zero n w
  · exact blockTag_above w ht

end FinitaryPerm
