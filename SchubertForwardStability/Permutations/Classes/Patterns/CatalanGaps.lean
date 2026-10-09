import SchubertForwardStability.Permutations.Classes.Patterns.PatternRecords
import Mathlib.Tactic

/-! # Removing the final record from a Catalan gap product

Deleting the largest record `r` from a record set and shortening the ambient size to `r-1`
preserves all earlier gaps. The Catalan gap product therefore factors as the product for the
shortened set times `Cat(n-r)`.
-/

namespace PermutationPattern

open scoped Classical BigOperators

/-- The next position after the largest record is the ambient terminal position. -/
theorem nextRecord_max (n : ℕ) (R : Finset ℕ+) (r : ℕ+)
    (hMax : ∀ j ∈ R, j ≤ r) : nextRecord n R r = n + 1 := by
  have hEmpty : ((R.image PNat.val).filter fun s => (r : ℕ) < s) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨hImage, hAbove⟩ := Finset.mem_filter.mp hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hImage
    have h := hMax j hj
    change (j : ℕ) ≤ (r : ℕ) at h
    omega
  unfold nextRecord
  simp [hEmpty]

/-- Removing the final record and shortening the ambient interval preserves earlier gaps. -/
theorem nextRecord_erase_max (n : ℕ) (R : Finset ℕ+) (r : ℕ+)
    (hr : r ∈ R) (hMax : ∀ j ∈ R, j ≤ r) (hn : (r : ℕ) ≤ n)
    (i : ℕ+) (hi : i ∈ R.erase r) :
    nextRecord ((r : ℕ) - 1) (R.erase r) i = nextRecord n R i := by
  obtain ⟨hir, hiR⟩ := Finset.mem_erase.mp hi
  have hiLt' : i < r := lt_of_le_of_ne (hMax i hiR) hir
  have hiLt : (i : ℕ) < (r : ℕ) := hiLt'
  let S := insert (n + 1) ((R.image PNat.val).filter fun s => (i : ℕ) < s)
  let T := insert (r : ℕ) (((R.erase r).image PNat.val).filter fun s => (i : ℕ) < s)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  have hrS : (r : ℕ) ∈ S := Finset.mem_insert.mpr (Or.inr
    (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨r, hr, rfl⟩, hiLt⟩))
  have hSub : ∀ x ∈ T, x ∈ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with he | hFilter
    · rw [he]
      exact hrS
    · obtain ⟨hImage, hAbove⟩ := Finset.mem_filter.mp hFilter
      obtain ⟨j, hj, hValue⟩ := Finset.mem_image.mp hImage
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨j, (Finset.mem_erase.mp hj).2, hValue⟩, hAbove⟩))
  have hBound : S.min' hS ≤ (r : ℕ) := Finset.min'_le S _ hrS
  have hMin : S.min' hS ∈ T := by
    rcases Finset.mem_insert.mp (Finset.min'_mem S hS) with he | hFilter
    · omega
    · obtain ⟨hImage, hAbove⟩ := Finset.mem_filter.mp hFilter
      obtain ⟨j, hj, hValue⟩ := Finset.mem_image.mp hImage
      by_cases he : j = r
      · subst j
        exact Finset.mem_insert.mpr (Or.inl hValue.symm)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨he, hj⟩, hValue⟩, hAbove⟩))
  unfold nextRecord
  simp only [Nat.sub_add_cancel (Nat.succ_le_of_lt r.pos)]
  change T.min' hT = S.min' hS
  apply le_antisymm
  · exact Finset.min'_le T _ hMin
  · exact Finset.min'_le S _ (hSub _ (Finset.min'_mem T hT))

/-- The Catalan gap product factors into the shortened prefix and its final gap. -/
theorem recordGapProduct_erase_max (n : ℕ) (R : Finset ℕ+) (r : ℕ+)
    (hr : r ∈ R) (hMax : ∀ j ∈ R, j ≤ r) (hn : (r : ℕ) ≤ n) :
    recordGapProduct n R =
      recordGapProduct ((r : ℕ) - 1) (R.erase r) * catalan (n - (r : ℕ)) := by
  unfold recordGapProduct
  calc
    _ = (∏ i ∈ R.erase r, catalan (nextRecord n R i - (i : ℕ) - 1)) *
        catalan (nextRecord n R r - (r : ℕ) - 1) :=
      (Finset.prod_erase_mul R _ hr).symm
    _ = _ := by
      rw [nextRecord_max n R r hMax,
        show n + 1 - (r : ℕ) - 1 = n - (r : ℕ) by omega]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      rw [nextRecord_erase_max n R r hr hMax hn i hi]

end PermutationPattern
