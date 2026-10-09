import SchubertForwardStability.Permutations.Classes.Tags.BlockTags

/-! # Local validity of boundary symbols extracted from words

A continuation occurrence includes its preceding positive generator. Consequently,
the boundary vectors extracted from reduced words satisfy the local suffix condition.
-/

namespace FinitaryPerm

open scoped Classical

/-- A boundary symbol is present exactly at an in-range occurring positive generator. -/
theorem blockTag_ne_zero_iff (n : ℕ) (w : FinitaryPerm ℕ+) (t : ℕ) :
    blockTag n w t ≠ .zero ↔ 0 < t ∧ t < n ∧ GeneratorPresent w t := by
  by_cases h : 0 < t ∧ t < n ∧ GeneratorPresent w t
  · by_cases hc : GeneratorContinues w t
    · simp [blockTag, h, hc]
    · simp [blockTag, h, hc]
  · simp [blockTag, h]

/-- A continuation boundary symbol is exactly an in-range continuing occurrence. -/
theorem blockTag_eq_cont_iff (n : ℕ) (w : FinitaryPerm ℕ+) (t : ℕ) :
    blockTag n w t = .cont ↔
      (0 < t ∧ t < n ∧ GeneratorPresent w t) ∧ GeneratorContinues w t := by
  by_cases h : 0 < t ∧ t < n ∧ GeneratorPresent w t
  · by_cases hc : GeneratorContinues w t
    · simp [blockTag, h, hc]
    · simp [blockTag, h, hc]
  · simp [blockTag, h]

/-- A continuing generator has its positive predecessor among the occurring generators. -/
theorem generatorContinues_predecessor (w : FinitaryPerm ℕ+) (t : ℕ)
    (hc : GeneratorContinues w t) :
    ∃ j : ℕ+, (j : ℕ) + 1 = t ∧ GeneratorPresent w (j : ℕ) := by
  obtain ⟨i, j, hi, hj, hinfix⟩ := hc
  refine ⟨j, ?_, j, rfl, ?_⟩
  · have h := congrArg PNat.val hj
    change (j : ℕ) + 1 = (i : ℕ) at h
    exact h.trans hi
  · exact hinfix.sublist.subset (by simp)

/-- Every extracted finite boundary vector satisfies the local continuation condition. -/
theorem valid_booleanTags (n : ℕ) (w : FinitaryPerm ℕ+) : IsTagWord (booleanTags n w) := by
  intro i hc
  change blockTag n w (i.val + 1) = .cont at hc
  obtain ⟨hb, hcontinue⟩ := (blockTag_eq_cont_iff n w (i.val + 1)).mp hc
  obtain ⟨j, hji, hpres⟩ := generatorContinues_predecessor w (i.val + 1) hcontinue
  have hjp := PNat.pos j
  have hi : 0 < i.val := by omega
  right
  refine ⟨⟨i.val - 1, by omega⟩, ?_, ?_⟩
  · change i.val - 1 + 1 = i.val
    omega
  · change blockTag n w (i.val - 1 + 1) ≠ .zero
    rw [blockTag_ne_zero_iff, Nat.sub_add_cancel (by omega : 1 ≤ i.val)]
    refine ⟨hi, by omega, ?_⟩
    have hj : (j : ℕ) = i.val := by omega
    simpa only [hj] using hpres

/-- Extracted boundary vectors belong to the finite set of valid tag words. -/
theorem booleanTags_mem (n : ℕ) (w : FinitaryPerm ℕ+) : booleanTags n w ∈ tagWords (n - 1) :=
  (mem_tagWords _).mpr (valid_booleanTags n w)

end FinitaryPerm
