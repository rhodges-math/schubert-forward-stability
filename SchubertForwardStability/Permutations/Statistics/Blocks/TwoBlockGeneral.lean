import SchubertForwardStability.Permutations.Statistics.Blocks.TwoBlockMaximum

/-! # Paired block maxima without overlap

## Main results

For two block endpoints bounded by their own maxima, the finite maximum is the
greater of the support endpoint and the sum of maxima minus the greater block size.
-/

namespace FinitaryPerm

/-- The general paired profile is bounded by its endpoint or its interior peak. -/
theorem twoBlock_pairValue_le_max {k l M N i : ℕ} (hk : k ≤ M) (hl : l ≤ N)
    (hi : i ≤ max M N + 1) :
    (if i ≤ k then M - k else if i ≤ M then M - i + 1 else 0) +
      (if i ≤ l then N - l else if i ≤ N then N - i + 1 else 0) + i - 1 ≤
        max (max M N) (M + N - max k l) := by
  split_ifs <;> omega

/-- At one greater than both maxima, both tail profiles vanish. -/
theorem twoBlock_pairValue_endpoint {k l M N : ℕ} (hk : k ≤ M) (hl : l ≤ N) :
    (if max M N + 1 ≤ k then M - k
      else if max M N + 1 ≤ M then M - (max M N + 1) + 1 else 0) +
      (if max M N + 1 ≤ l then N - l
        else if max M N + 1 ≤ N then N - (max M N + 1) + 1 else 0) +
          (max M N + 1) - 1 = max M N := by
  split_ifs <;> omega

/-- The paired finite maximum is the greater endpoint-or-interior value. -/
theorem twoBlock_pairMax_general {k l M N : ℕ} (hk : k ≤ M) (hl : l ≤ N) :
    (positions (max M N + 1)).sup (fun i : ℕ+ =>
      (if (i : ℕ) ≤ k then M - k else if (i : ℕ) ≤ M then M - (i : ℕ) + 1 else 0) +
        (if (i : ℕ) ≤ l then N - l else if (i : ℕ) ≤ N then N - (i : ℕ) + 1 else 0) +
          (i : ℕ) - 1) = max (max M N) (M + N - max k l) := by
  let f : ℕ+ → ℕ := fun i =>
    (if (i : ℕ) ≤ k then M - k else if (i : ℕ) ≤ M then M - (i : ℕ) + 1 else 0) +
      (if (i : ℕ) ≤ l then N - l else if (i : ℕ) ≤ N then N - (i : ℕ) + 1 else 0) +
        (i : ℕ) - 1
  change (positions (max M N + 1)).sup f = max (max M N) (M + N - max k l)
  have hend : max M N ≤ (positions (max M N + 1)).sup f := by
    let i : ℕ+ := ⟨max M N + 1, Nat.succ_pos _⟩
    have hi : i ∈ positions (max M N + 1) := (mem_positions _ _).mpr le_rfl
    have he : f i = max M N := twoBlock_pairValue_endpoint hk hl
    calc
      max M N = f i := he.symm
      _ ≤ _ := Finset.le_sup (f := f) hi
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    exact twoBlock_pairValue_le_max hk hl ((mem_positions _ _).mp hi)
  · apply max_le hend
    by_cases hsep : max k l < min M N
    · exact (twoBlock_pairMax_eq hsep).ge
    · exact le_trans (by omega : M + N - max k l ≤ max M N) hend

end FinitaryPerm
