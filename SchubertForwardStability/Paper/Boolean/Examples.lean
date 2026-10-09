import SchubertForwardStability.Permutations.Classes.Intervals.IntervalCounts
import SchubertForwardStability.Permutations.Classes.Intervals.BoundaryCounts
import SchubertForwardStability.Permutations.Classes.Tags.TagReadout
import SchubertForwardStability.Permutations.Finitary.Longest

/-! # Explicit record-boundary fibers at size five

The Boolean permutations of size five with a record at position three split into the
boundary fiber `booleanBoundaryOne 5 3`, in which the generator `s_2` does not occur, and
its complement `booleanBoundaryTwo 5 3`. Both fibers are listed by reduced words; they have
ten and nine elements.
-/

namespace RecordStability

open FinitaryPerm

open scoped Classical

private def boundaryOneWords : List (List ℕ+) :=
  [[], [3], [4], [3, 4], [4, 3], [1], [1, 3], [1, 4], [1, 3, 4], [1, 4, 3]]

private def boundaryTwoWords : List (List ℕ+) :=
  [[2, 3], [2, 3, 4], [2, 4, 3], [1, 2, 3], [1, 2, 3, 4], [1, 2, 4, 3],
    [2, 1, 3], [2, 1, 3, 4], [2, 1, 4, 3]]

private theorem boundaryWords_nodup (word : List ℕ+)
    (hw : word ∈ boundaryOneWords ++ boundaryTwoWords) : word.Nodup := by
  have h : (boundaryOneWords ++ boundaryTwoWords).all (fun w => decide w.Nodup) = true := by
    decide
  exact of_decide_eq_true ((List.all_eq_true.mp h) word hw)

private theorem boundaryWords_bound (word : List ℕ+)
    (hw : word ∈ boundaryOneWords ++ boundaryTwoWords) : ∀ i ∈ word, (i : ℕ) < 5 := by
  have h : (boundaryOneWords ++ boundaryTwoWords).all
      (fun w => w.all (fun i => decide ((i : ℕ) < 5))) = true := by decide
  intro i hi
  exact of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp h) word hw)) i hi)

private theorem boundaryWords_record (word : List ℕ+)
    (hw : word ∈ boundaryOneWords ++ boundaryTwoWords) : IsRecord (wordProduct word) 3 := by
  have h : (boundaryOneWords ++ boundaryTwoWords).all (fun w =>
      decide (wordProduct w 1 < wordProduct w 3 ∧ wordProduct w 2 < wordProduct w 3)) =
      true := by decide
  have hValues := of_decide_eq_true ((List.all_eq_true.mp h) word hw)
  intro j hj
  have hCases : j = 1 ∨ j = 2 := by
    have hp := j.pos
    change (j : ℕ) < 3 at hj
    have hNat : (j : ℕ) = 1 ∨ (j : ℕ) = 2 := by omega
    exact hNat.elim (fun h => Or.inl (PNat.eq h)) (fun h => Or.inr (PNat.eq h))
  rcases hCases with rfl | rfl
  · exact hValues.1
  · exact hValues.2

private theorem boundaryOneWords_absent (word : List ℕ+) (hw : word ∈ boundaryOneWords) :
    (2 : ℕ+) ∉ word := by
  have h : boundaryOneWords.all (fun w => decide ((2 : ℕ+) ∉ w)) = true := by decide
  exact of_decide_eq_true ((List.all_eq_true.mp h) word hw)

private theorem boundaryTwoWords_present (word : List ℕ+) (hw : word ∈ boundaryTwoWords) :
    (2 : ℕ+) ∈ word := by
  have h : boundaryTwoWords.all (fun w => decide ((2 : ℕ+) ∈ w)) = true := by decide
  exact of_decide_eq_true ((List.all_eq_true.mp h) word hw)

private theorem boundaryOneWords_subset :
    (boundaryOneWords.map wordProduct).toFinset ⊆ booleanBoundaryOne 5 3 := by
  intro w hw
  obtain ⟨word, hWord, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  have hAll : word ∈ boundaryOneWords ++ boundaryTwoWords := List.mem_append.mpr (Or.inl hWord)
  have hN := boundaryWords_nodup word hAll
  refine (mem_booleanBoundaryOne 5 3 _).mpr
    ⟨wordProduct_mem_boolean 5 word hN (boundaryWords_bound word hAll),
      boundaryWords_record word hAll, ?_⟩
  have hAbsent : ¬GeneratorPresent (wordProduct word) 2 := by
    intro h
    have hMem := (generatorPresent_iff_reduced _ word (isReducedWord_of_nodup word hN) 2).mp h
    exact boundaryOneWords_absent word hWord hMem
  change blockTag 5 (wordProduct word) 2 = .zero
  simp only [blockTag, hAbsent, and_false, ↓reduceIte]

private theorem boundaryTwoWords_subset :
    (boundaryTwoWords.map wordProduct).toFinset ⊆ booleanBoundaryTwo 5 3 := by
  intro w hw
  obtain ⟨word, hWord, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  have hAll : word ∈ boundaryOneWords ++ boundaryTwoWords := List.mem_append.mpr (Or.inr hWord)
  have hN := boundaryWords_nodup word hAll
  refine (mem_booleanBoundaryTwo 5 3 _).mpr
    ⟨wordProduct_mem_boolean 5 word hN (boundaryWords_bound word hAll),
      boundaryWords_record word hAll, ?_⟩
  apply (blockTag_ne_zero_iff 5 _ 2).mpr
  refine ⟨by decide, by decide, ?_⟩
  exact (generatorPresent_iff_reduced _ word (isReducedWord_of_nodup word hN) 2).mpr
    (boundaryTwoWords_present word hWord)

private theorem boundaryOneWords_card : (boundaryOneWords.map wordProduct).toFinset.card = 10 := by
  have hValues : (boundaryOneWords.map (fun word => oneLine 5 (wordProduct word))).Nodup := by
    decide
  have hWords : (boundaryOneWords.map wordProduct).Nodup := by
    apply List.Nodup.of_map (oneLine 5)
    simpa only [List.map_map, Function.comp_def] using hValues
  rw [List.toFinset_card_of_nodup hWords, List.length_map]
  rfl

private theorem boundaryTwoWords_card : (boundaryTwoWords.map wordProduct).toFinset.card = 9 := by
  have hValues : (boundaryTwoWords.map (fun word => oneLine 5 (wordProduct word))).Nodup := by
    decide
  have hWords : (boundaryTwoWords.map wordProduct).Nodup := by
    apply List.Nodup.of_map (oneLine 5)
    simpa only [List.map_map, Function.comp_def] using hValues
  rw [List.toFinset_card_of_nodup hWords, List.length_map]
  rfl

private theorem boundaryOne_five_card : (booleanBoundaryOne 5 3).card = 10 := by
  have hL := card_booleanOn_initial_int 5 2 (by decide)
  have hR := card_booleanOn_interval_int 5 3 (by decide)
  norm_num [Int.fib, Nat.fib] at hL hR
  have h : ((booleanBoundaryOne 5 3).card : ℤ) = 10 := by
    rw [card_booleanBoundaryOne, Nat.cast_mul]
    change ((booleanOn 5 (positions 2)).card : ℤ) *
      ((booleanOn 5 (positionInterval 3 5)).card : ℤ) = 10
    rw [hL, hR]
    norm_num
  exact_mod_cast h

private theorem boundaryTwo_five_card : (booleanBoundaryTwo 5 3).card = 9 := by
  have hInitial : positions 2 ⊆ positions 3 := by
    intro i hi
    rw [mem_positions] at hi ⊢
    omega
  have hFinal : positionInterval 4 5 ⊆ positionInterval 3 5 := by
    intro i hi
    rw [mem_positionInterval] at hi ⊢
    exact ⟨hi.1, by omega⟩
  have hL := card_booleanOn_sdiff_cast 5 hInitial
  have hR := card_booleanOn_sdiff_cast 5 hFinal
  rw [card_booleanOn_initial_int 5 3 (by decide),
    card_booleanOn_initial_int 5 2 (by decide)] at hL
  have hRLarge : ((booleanOn 5 (positionInterval 3 5)).card : ℤ) = 5 := by
    have h := card_booleanOn_interval_int 5 3 (by decide)
    norm_num [Int.fib, Nat.fib] at h
    exact_mod_cast h
  have hRSmall : ((booleanOn 5 (positionInterval 4 5)).card : ℤ) = 2 := by
    have h := card_booleanOn_interval_int 5 4 (by decide)
    norm_num [Int.fib, Nat.fib] at h
    exact_mod_cast h
  rw [hRLarge, hRSmall] at hR
  norm_num [Int.fib, Nat.fib] at hL hR
  have h : ((booleanBoundaryTwo 5 3).card : ℤ) = 9 := by
    rw [card_booleanBoundaryTwo, Nat.cast_mul]
    change ((booleanOn 5 (positions 3) \ booleanOn 5 (positions 2)).card : ℤ) *
      ((booleanOn 5 (positionInterval 3 5) \ booleanOn 5 (positionInterval 4 5)).card : ℤ) = 9
    rw [hL, hR]
    norm_num
  exact_mod_cast h

/-- The first size-five record-three boundary fiber is the displayed ten-word set. -/
theorem booleanBoundaryOne_five :
    booleanBoundaryOne 5 3 =
      ([[], [3], [4], [3, 4], [4, 3], [1], [1, 3], [1, 4], [1, 3, 4], [1, 4, 3]].map
        wordProduct).toFinset := by
  exact (Finset.eq_of_subset_of_card_le boundaryOneWords_subset
    (by rw [boundaryOne_five_card, boundaryOneWords_card])).symm

/-- The second size-five record-three boundary fiber is the displayed nine-word set. -/
theorem booleanBoundaryTwo_five :
    booleanBoundaryTwo 5 3 =
      ([[2, 3], [2, 3, 4], [2, 4, 3], [1, 2, 3], [1, 2, 3, 4], [1, 2, 4, 3],
        [2, 1, 3], [2, 1, 3, 4], [2, 1, 4, 3]].map wordProduct).toFinset := by
  exact (Finset.eq_of_subset_of_card_le boundaryTwoWords_subset
    (by rw [boundaryTwo_five_card, boundaryTwoWords_card])).symm

end RecordStability
