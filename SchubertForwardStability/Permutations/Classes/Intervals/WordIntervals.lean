import SchubertForwardStability.Permutations.Classes.Boolean.BooleanDistinct
import SchubertForwardStability.Permutations.Classes.Intervals.BooleanIntervals
import SchubertForwardStability.Permutations.Classes.FiniteWords
import SchubertForwardStability.Permutations.Classes.Intervals.RecordSwaps

/-! # Position supports of bounded adjacent words

Upper generator bounds give initial support bounds. Lower generator bounds fix
all preceding positions, so distinct bounded words realize restricted Boolean families.
-/

namespace FinitaryPerm

/-- A word using only generators below n represents a permutation supported at size n. -/
theorem wordProduct_supported (n : ℕ) (word : List ℕ+)
    (hBound : ∀ i ∈ word, (i : ℕ) < n) : IsSupported n (wordProduct word) := by
  obtain ⟨finiteWord, he⟩ := exists_finiteAdjacentWord word hBound
  rw [← he, ← ofFinite_wordProduct]
  exact isSupported_ofFinite n _

/-- A word whose generators are at least j fixes every position below j. -/
theorem wordProduct_fixed_below (word : List ℕ+) (j : ℕ+)
    (hBound : ∀ i ∈ word, j ≤ i) (k : ℕ+) (hk : k < j) : wordProduct word k = k := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    rw [wordProduct_cons, mul_apply, ih (fun a ha => hBound a (List.mem_cons_of_mem i ha))]
    exact simpleTransposition_apply_below i k (hk.trans_le (hBound i List.mem_cons_self))

/-- A distinct word bounded by n represents a member of the finite Boolean family. -/
theorem wordProduct_mem_boolean (n : ℕ) (word : List ℕ+) (hN : word.Nodup)
    (hBound : ∀ i ∈ word, (i : ℕ) < n) : wordProduct word ∈ boolean n :=
  (mem_boolean n _).mpr ⟨wordProduct_supported n word hBound,
    isBoolean_wordProduct_of_nodup word hN⟩

/-- A distinct word with interval bounds fixes the complement of that position interval. -/
theorem wordProduct_mem_booleanOn_interval (n : ℕ) (j : ℕ+) (word : List ℕ+)
    (hN : word.Nodup) (hLower : ∀ i ∈ word, j ≤ i)
    (hUpper : ∀ i ∈ word, (i : ℕ) < n) :
    wordProduct word ∈ booleanOn n (positionInterval (j : ℕ) n) := by
  apply (mem_booleanOn _ _ _).mpr
  refine ⟨wordProduct_mem_boolean n word hN hUpper, ?_⟩
  intro k hk
  by_cases hLast : n < (k : ℕ)
  · exact wordProduct_supported n word hUpper k hLast
  · have hkn : (k : ℕ) ≤ n := le_of_not_gt hLast
    have hkj : k < j := by
      by_contra h
      apply hk
      rw [mem_positionInterval]
      exact ⟨hkn, le_of_not_gt h⟩
    exact wordProduct_fixed_below word j hLower k hkj

/-- Distinct words with an additional small bound lie in the corresponding initial family. -/
theorem wordProduct_mem_booleanOn_initial (n m : ℕ) (word : List ℕ+) (hN : word.Nodup)
    (hAmbient : ∀ i ∈ word, (i : ℕ) < n) (hSmall : ∀ i ∈ word, (i : ℕ) < m) :
    wordProduct word ∈ booleanOn n (positions m) := by
  apply (mem_booleanOn _ _ _).mpr
  refine ⟨wordProduct_mem_boolean n word hN hAmbient, ?_⟩
  intro k hk
  exact wordProduct_supported m word hSmall k
    (lt_of_not_ge (by simpa only [mem_positions] using hk))

end FinitaryPerm
