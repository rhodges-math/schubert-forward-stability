import SchubertForwardStability.SchubertPolynomials.Stability.ShiftConstants
import SchubertForwardStability.SchubertPolynomials.Products.RecordBound

/-! # Suffix counts after an initial fixed position

Translation preserves the suffix non-record relation on successor positions.
The new first value is the smallest value and supplies no inversion witness.
Consequently the first suffix count is unchanged, and every later suffix count
is the translated original count.
-/

namespace FinitaryPerm

open scoped Classical

/-- The suffix non-record relation translates with both successor positions. -/
theorem suffixNonRecord_shiftRight_iff (w : FinitaryPerm ℕ+) (i j : ℕ+) :
    IsSuffixNonRecord (shiftRight w) (i + 1) (j + 1) ↔ IsSuffixNonRecord w i j := by
  constructor
  · rintro ⟨k, hik, hkj, hv⟩
    have hp : 0 < (k : ℕ) - 1 := by have hi := i.pos; change (i : ℕ) + 1 ≤ k at hik; omega
    let l : ℕ+ := ⟨(k : ℕ) - 1, hp⟩
    have he : l + 1 = k := by
      apply PNat.eq
      change (k : ℕ) - 1 + 1 = (k : ℕ)
      omega
    rw [←he] at hik hkj hv
    rw [shiftRight_apply_add_one, shiftRight_apply_add_one] at hv
    refine ⟨l, ?_, ?_, ?_⟩
    · change (i : ℕ) ≤ l
      change (i : ℕ) + 1 ≤ (l : ℕ) + 1 at hik
      omega
    · change (l : ℕ) < j
      change (l : ℕ) + 1 < (j : ℕ) + 1 at hkj
      omega
    · change (w j : ℕ) < w l
      change (w j : ℕ) + 1 < (w l : ℕ) + 1 at hv
      omega
  · rintro ⟨k, hik, hkj, hv⟩
    refine ⟨k + 1, ?_, ?_, ?_⟩
    · exact Nat.add_le_add_right hik 1
    · exact Nat.add_lt_add_right hkj 1
    · rw [shiftRight_apply_add_one, shiftRight_apply_add_one]
      exact Nat.add_lt_add_right hv 1

/-- The inserted first value cannot witness a suffix non-record. -/
theorem suffixNonRecord_shiftRight_first (w : FinitaryPerm ℕ+) (j : ℕ+) :
    IsSuffixNonRecord (shiftRight w) 1 j ↔ IsSuffixNonRecord (shiftRight w) 2 j := by
  constructor
  · rintro ⟨k, _, hkj, hv⟩
    have hk : k ≠ 1 := by
      intro he
      rw [he, shiftRight_apply_one] at hv
      exact (not_lt_of_ge (one_le : 1 ≤ shiftRight w j)) hv
    refine ⟨k, ?_, hkj, hv⟩
    have hp := k.pos
    have hn : (k : ℕ) ≠ 1 := fun he => hk (PNat.eq he)
    change 2 ≤ (k : ℕ)
    omega
  · rintro ⟨k, hk, hkj, hv⟩
    exact ⟨k, (show (1 : ℕ+) ≤ 2 by decide).trans hk, hkj, hv⟩

/-- The suffix count at each successor position is its original suffix count. -/
theorem suffixNonRecordCount_shiftRight_succ (w : FinitaryPerm ℕ+) (i : ℕ+) :
    (shiftRight w).suffixNonRecordCount (i + 1) = w.suffixNonRecordCount i := by
  rw [suffixNonRecordCount, suffixNonRecordCount]
  symm
  apply Finset.card_nbij (fun j : ℕ+ => j + 1)
  · intro j hj
    exact (mem_suffixNonRecords _ _ _).mpr
      ((suffixNonRecord_shiftRight_iff w i j).mpr ((mem_suffixNonRecords _ _ _).mp hj))
  · intro j _ k _ he
    apply PNat.eq
    have h := congrArg PNat.val he
    change (j : ℕ) + 1 = (k : ℕ) + 1 at h
    omega
  · intro j hj
    have hs := (mem_suffixNonRecords _ _ _).mp hj
    have hp : 0 < (j : ℕ) - 1 := by
      have hi := i.pos
      have hlt := hs.start_lt
      change (i : ℕ) + 1 < (j : ℕ) at hlt
      omega
    let k : ℕ+ := ⟨(j : ℕ) - 1, hp⟩
    have he : k + 1 = j := by
      apply PNat.eq
      change (j : ℕ) - 1 + 1 = (j : ℕ)
      omega
    refine ⟨k, ?_, he⟩
    rw [←he] at hs
    exact (mem_suffixNonRecords _ _ _).mpr ((suffixNonRecord_shiftRight_iff w i k).mp hs)

/-- The first suffix count is unchanged by insertion of an initial fixed position. -/
theorem suffixNonRecordCount_shiftRight_first (w : FinitaryPerm ℕ+) :
    (shiftRight w).suffixNonRecordCount 1 = w.suffixNonRecordCount 1 := by
  have he : (shiftRight w).suffixNonRecords 1 = (shiftRight w).suffixNonRecords 2 := by
    ext j
    simp only [mem_suffixNonRecords, suffixNonRecord_shiftRight_first]
  change ((shiftRight w).suffixNonRecords 1).card = _
  rw [he]
  exact suffixNonRecordCount_shiftRight_succ w 1

end FinitaryPerm
