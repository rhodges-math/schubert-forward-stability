import SchubertForwardStability.Permutations.Statistics.Blocks.TwoBlocks

/-! # Finite maxima of two block tails

## Main results

When both block endpoints lie below both maxima, the sum of the two tail profiles
plus the position minus one is maximized at the smaller endpoint plus one.
-/

namespace FinitaryPerm

/-- Two three-piece tail profiles are bounded by the sum of their maxima minus
the larger block endpoint throughout the support interval. -/
theorem twoBlock_pairValue_le {k l M N i : ℕ} (hsep : max k l < min M N)
    (hi : i ≤ max M N + 1) :
    (if i ≤ k then M - k else if i ≤ M then M - i + 1 else 0) +
      (if i ≤ l then N - l else if i ≤ N then N - i + 1 else 0) + i - 1 ≤
        M + N - max k l := by
  split_ifs <;> omega

/-- The smaller endpoint plus one attains the upper bound of the paired profiles. -/
theorem twoBlock_pairValue_peak {k l M N : ℕ} (hsep : max k l < min M N) :
    (if min k l + 1 ≤ k then M - k
      else if min k l + 1 ≤ M then M - (min k l + 1) + 1 else 0) +
      (if min k l + 1 ≤ l then N - l
        else if min k l + 1 ≤ N then N - (min k l + 1) + 1 else 0) +
          (min k l + 1) - 1 = M + N - max k l := by
  split_ifs <;> omega

/-- The positive-position finite maximum of two block profiles has its exact value. -/
theorem twoBlock_pairMax_eq {k l M N : ℕ} (hsep : max k l < min M N) :
    (positions (max M N + 1)).sup (fun i : ℕ+ =>
      (if (i : ℕ) ≤ k then M - k else if (i : ℕ) ≤ M then M - (i : ℕ) + 1 else 0) +
        (if (i : ℕ) ≤ l then N - l else if (i : ℕ) ≤ N then N - (i : ℕ) + 1 else 0) +
          (i : ℕ) - 1) = M + N - max k l := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    exact twoBlock_pairValue_le hsep ((mem_positions _ _).mp hi)
  · let i : ℕ+ := ⟨min k l + 1, Nat.succ_pos _⟩
    have hi : i ∈ positions (max M N + 1) := (mem_positions _ _).mpr (by
      change min k l + 1 ≤ max M N + 1
      omega)
    calc
      M + N - max k l =
          (if (i : ℕ) ≤ k then M - k else if (i : ℕ) ≤ M then M - (i : ℕ) + 1 else 0) +
            (if (i : ℕ) ≤ l then N - l else if (i : ℕ) ≤ N then N - (i : ℕ) + 1 else 0) +
              (i : ℕ) - 1 := (twoBlock_pairValue_peak hsep).symm
      _ ≤ _ := Finset.le_sup (f := fun j : ℕ+ =>
        (if (j : ℕ) ≤ k then M - k else if (j : ℕ) ≤ M then M - (j : ℕ) + 1 else 0) +
          (if (j : ℕ) ≤ l then N - l else if (j : ℕ) ≤ N then N - (j : ℕ) + 1 else 0) +
            (j : ℕ) - 1) hi

end FinitaryPerm
