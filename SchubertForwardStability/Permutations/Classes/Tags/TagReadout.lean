import SchubertForwardStability.Permutations.Classes.NormalNeighbors
import SchubertForwardStability.Permutations.Classes.Boolean.BooleanNormal
import SchubertForwardStability.Permutations.Classes.Tags.TagValidity

/-! # Boundary symbols from arbitrary Boolean reduced expressions

Occurrence and reversed-neighbor order can be transported from any reduced
expression to the least word before reading its continuation symbols.
-/

namespace FinitaryPerm

/-- A positive-index generator is present exactly when it occurs in the selected word. -/
theorem generatorPresent_iff_mem (w : FinitaryPerm ℕ+) (i : ℕ+) :
    GeneratorPresent w (i : ℕ) ↔ i ∈ w.lexFirstReducedWord := by
  constructor
  · rintro ⟨k, hk, hm⟩
    have hki : k = i := PNat.eq hk
    simpa only [hki] using hm
  · intro hi
    exact ⟨i, rfl, hi⟩

/-- Generator occurrence is independent of the chosen reduced expression. -/
theorem generatorPresent_iff_reduced (w : FinitaryPerm ℕ+) (word : List ℕ+)
    (hword : IsReducedWord w word) (i : ℕ+) :
    GeneratorPresent w (i : ℕ) ↔ i ∈ word := by
  rw [generatorPresent_iff_mem]
  have he := reducedWord_toFinset_eq w word _ hword (isReducedWordIn_lexFirst w).1
  simpa only [List.mem_toFinset] using
    (iff_of_eq (congrArg (fun s : Finset ℕ+ => i ∈ s) he.symm))

/-- A Boolean continuation is exactly a reversed neighboring projection of the least word. -/
theorem IsBoolean.continues_iff_projection {w : FinitaryPerm ℕ+} (hw : IsBoolean w)
    (j : ℕ+) : GeneratorContinues w ((j + 1 : ℕ+) : ℕ) ↔
      neighborProjection (j + 1) j w.lexFirstReducedWord = [j + 1, j] := by
  rw [normal_neighbors_projection_iff _ hw.lexFirst_nodup
    (not_hasCommutingInversion_lexFirst w) (j + 1) j rfl]
  constructor
  · rintro ⟨i, k, hi, hk, hPair⟩
    have hij : i = j + 1 := PNat.eq hi
    have hkN := congrArg PNat.val hk
    change (k : ℕ) + 1 = (i : ℕ) at hkN
    have hiN : (i : ℕ) = (j : ℕ) + 1 := hi
    have hkj : k = j := PNat.eq (by omega)
    simpa only [hij, hkj] using hPair
  · intro hPair
    exact ⟨j + 1, j, rfl, rfl, hPair⟩

/-- Boolean continuations can be read from any reduced word by neighboring projection. -/
theorem IsBoolean.continues_iff_reduced {w : FinitaryPerm ℕ+} (hw : IsBoolean w)
    (word : List ℕ+) (hword : IsReducedWord w word) (j : ℕ+) :
    GeneratorContinues w ((j + 1 : ℕ+) : ℕ) ↔
      neighborProjection (j + 1) j word = [j + 1, j] := by
  rw [hw.continues_iff_projection]
  have he := commutations_neighborProjection_eq (hw.reducedWord_commutations
    w.lexFirstReducedWord word (isReducedWordIn_lexFirst w).1 hword)
      (j + 1) j (Or.inr rfl)
  rw [he]

end FinitaryPerm
