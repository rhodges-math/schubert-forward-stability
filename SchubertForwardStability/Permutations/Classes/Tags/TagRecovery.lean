import SchubertForwardStability.Permutations.Classes.Tags.TagProjection
import SchubertForwardStability.Permutations.Classes.Tags.TagReadout
import SchubertForwardStability.Permutations.Classes.Tags.TagInjective

/-! # Recovery of valid Boolean boundary vectors

The tags of the selected word are recovered using transported neighboring
projections of a distinct representative. This gives the bijection for finite families.
-/

namespace FinitaryPerm

/-- No positive predecessor can continue into the first generator index. -/
theorem not_generatorContinues_first (w : FinitaryPerm ℕ+) : ¬GeneratorContinues w 1 := by
  rintro ⟨i, j, hi, hji, _⟩
  have he := congrArg PNat.val hji
  change (j : ℕ) + 1 = (i : ℕ) at he
  have hp := j.pos
  omega

/-- The generator-presence predicate recovers the nonzero input coordinates. -/
theorem tagRepresentative_generator {m : ℕ} (T : Fin m → BlockTag) (i : Fin m) :
    GeneratorPresent (wordProduct (tagRepresentative T)) (i.val + 1) ↔ T i ≠ .zero :=
  (generatorPresent_iff_reduced _ _ (tagRepresentative_reduced T) i.val.succPNat).trans
    (tagRepresentative_present T i)

/-- Every valid input continuation agrees with the selector's continuation test. -/
theorem tagRepresentative_continues {m : ℕ} (T : Fin m → BlockTag) (hT : IsTagWord T)
    (i : Fin m) : GeneratorContinues (wordProduct (tagRepresentative T)) (i.val + 1) ↔
      T i = .cont := by
  by_cases hi : 0 < i.val
  · let j : ℕ+ := ⟨i.val, hi⟩
    have hRead := (tagRepresentative_boolean T).continues_iff_reduced
      _ (tagRepresentative_reduced T) j
    exact hRead.trans (tagRepresentative_cont_iff T hT j i.isLt)
  · have hZero : i.val = 0 := Nat.eq_zero_of_not_pos hi
    have hNc : T i ≠ .cont := by
      intro hc
      rcases hT i hc with ⟨_, hp⟩ | ⟨j, hj, _⟩
      · cases hp
      · rw [hZero] at hj
        omega
    have hNw : ¬GeneratorContinues (wordProduct (tagRepresentative T)) (i.val + 1) := by
      simpa only [hZero, Nat.zero_add] using not_generatorContinues_first
        (wordProduct (tagRepresentative T))
    exact iff_of_false hNw hNc

/-- The three selector tags recover each coordinate of a valid boundary vector. -/
theorem tagRepresentative_tag {m : ℕ} (T : Fin m → BlockTag) (hT : IsTagWord T)
    (i : Fin m) : blockTag (m + 1) (wordProduct (tagRepresentative T)) (i.val + 1) = T i := by
  have hPres := tagRepresentative_generator T i
  have hContinue := tagRepresentative_continues T hT i
  have hp : 0 < i.val + 1 := by omega
  have hn : i.val + 1 < m + 1 := by have hb := i.isLt; omega
  cases ht : T i
  · have hAbsent : ¬GeneratorPresent (wordProduct (tagRepresentative T)) (i.val + 1) :=
      fun h => hPres.mp h ht
    simp [blockTag, hAbsent]
  · have hPresent := hPres.mpr (by rw [ht]; decide)
    have hNc := hContinue.not.mpr (by rw [ht]; decide)
    simp [blockTag, hp, hn, hPresent, hNc]
  · have hPresent := hPres.mpr (by rw [ht]; decide)
    have hContinuous := hContinue.mpr ht
    simp [blockTag, hp, hn, hPresent, hContinuous]

/-- The boundary vector of a valid representative is precisely its input vector. -/
theorem booleanTags_tagRepresentative {m : ℕ} (T : Fin m → BlockTag) (hT : IsTagWord T) :
    booleanTags (m + 1) (wordProduct (tagRepresentative T)) = T := by
  funext i
  exact tagRepresentative_tag T hT i

/-- Every valid boundary vector is realized in the finite Boolean family, including size zero. -/
theorem booleanTags_surjOn (n : ℕ) : Set.SurjOn (booleanTags n)
    (boolean n : Set (FinitaryPerm ℕ+)) (tagWords (n - 1) : Set (Fin (n - 1) → BlockTag)) := by
  by_cases hn : 1 ≤ n
  · intro T ht
    have hSize : n - 1 + 1 = n := Nat.sub_add_cancel hn
    refine ⟨wordProduct (tagRepresentative T), ?_, ?_⟩
    · change wordProduct (tagRepresentative T) ∈ boolean n
      simpa only [hSize] using tagRepresentative_mem_boolean T
    · funext i
      change blockTag n (wordProduct (tagRepresentative T)) (i.val + 1) = T i
      have he := tagRepresentative_tag T ((mem_tagWords T).mp ht) i
      rw [hSize] at he
      exact he
  · have hZero : n = 0 := by omega
    subst n
    intro T _
    exact ⟨1, one_mem_boolean 0, by funext i; exact Fin.elim0 i⟩

/-- The Boolean boundary map is a bijection onto all valid finite boundary vectors. -/
theorem booleanTags_bijOn (n : ℕ) : Set.BijOn (booleanTags n)
    (boolean n : Set (FinitaryPerm ℕ+)) (tagWords (n - 1) : Set (Fin (n - 1) → BlockTag)) :=
  ⟨fun w _ => booleanTags_mem n w, booleanTags_injOn n, booleanTags_surjOn n⟩

/-- Decoding the tags recovers every Boolean permutation at positive ambient size. -/
theorem tagRepresentative_booleanTags (n : ℕ) (hn : 1 ≤ n) (w : FinitaryPerm ℕ+)
    (hw : w ∈ boolean n) : wordProduct (tagRepresentative (booleanTags n w)) = w := by
  have hSize : n - 1 + 1 = n := Nat.sub_add_cancel hn
  apply booleanTags_injective n _ w
  · simpa only [hSize] using tagRepresentative_mem_boolean (booleanTags n w)
  · exact hw
  · funext i
    change blockTag n (wordProduct (tagRepresentative (booleanTags n w))) (i.val + 1) =
      blockTag n w (i.val + 1)
    have he := tagRepresentative_tag (booleanTags n w) (valid_booleanTags n w) i
    rw [hSize] at he
    exact he

end FinitaryPerm
