import SchubertForwardStability.Permutations.Statistics.SuffixRecords

/-! # Finite models of suffix non-record counts

## Main results

Extension from a finite symmetric group preserves suffix non-record witnesses and their
counts. The comparison uses the increasing one-based index equivalence.

## Implementation notes

Finite positions are zero-based. The extension maps them to the positive positions one
greater than their values.
-/

namespace FinitaryPerm

open scoped Classical

/-- Extending a finite permutation preserves the earlier-larger-value condition in a suffix. -/
theorem ofFinite_suffixNonRecord_iff {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    IsSuffixNonRecord (ofFinite n w) (positiveIndex n i).val (positiveIndex n j).val ↔
      ∃ k : Fin n, i ≤ k ∧ k < j ∧ w j < w k := by
  constructor
  · rintro ⟨k, hik, hkj, hvalue⟩
    have hkn : (k : ℕ) ≤ n := by
      have hjn := (positiveIndex n j).property
      have hkj' : (k : ℕ) < ((positiveIndex n j).val : ℕ) := hkj
      omega
    let l := (positiveIndex n).symm ⟨k, hkn⟩
    have hl : (positiveIndex n l).val = k :=
      congrArg Subtype.val ((positiveIndex n).apply_symm_apply ⟨k, hkn⟩)
    rw [← hl] at hik hkj hvalue
    rw [ofFinite_apply_position, ofFinite_apply_position] at hvalue
    refine ⟨l, ?_, ?_, ?_⟩
    · change i.val + 1 ≤ l.val + 1 at hik
      change i.val ≤ l.val
      omega
    · change l.val + 1 < j.val + 1 at hkj
      change l.val < j.val
      omega
    · change (w j).val + 1 < (w l).val + 1 at hvalue
      change (w j).val < (w l).val
      omega
  · rintro ⟨k, hik, hkj, hvalue⟩
    refine ⟨(positiveIndex n k).val, ?_, ?_, ?_⟩
    · change i.val + 1 ≤ k.val + 1
      exact Nat.add_le_add_right hik 1
    · change k.val + 1 < j.val + 1
      exact Nat.add_lt_add_right hkj 1
    · rw [ofFinite_apply_position, ofFinite_apply_position]
      change (w j).val + 1 < (w k).val + 1
      exact Nat.add_lt_add_right hvalue 1

/-- A suffix count of an extended permutation is its finite witness-set cardinality. -/
theorem ofFinite_suffixNonRecordCount {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) :
    (ofFinite n w).suffixNonRecordCount (positiveIndex n i).val =
      (Finset.univ.filter fun j : Fin n =>
        ∃ k : Fin n, i ≤ k ∧ k < j ∧ w j < w k).card := by
  rw [suffixNonRecordCount_eq_card (isSupported_ofFinite n w), positions,
    Finset.filter_image, Finset.card_image_of_injective]
  · apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ofFinite_suffixNonRecord_iff]
  · intro j k h
    exact (positiveIndex n).injective (Subtype.ext h)

end FinitaryPerm
