import SchubertForwardStability.Permutations.Finitary.PositiveShift
import SchubertForwardStability.Permutations.Classes.Intervals.IntervalWords

/-! # Translation bijections for final Boolean intervals

The index-shift homomorphism maps a finite initial Boolean family onto the
corresponding final interval. Subtracting the offset from the bounded selected
word constructs the inverse image, including the empty-size case.
-/

namespace FinitaryPerm

/-- Subtract an offset from a positive position, using one below the valid range. -/
def unshiftPosition (m : ℕ) (i : ℕ+) : ℕ+ := ((i : ℕ) - m).toPNat'

/-- Above the offset, subtracting and translating recovers the original position. -/
theorem shiftPosition_unshift (m : ℕ) (i : ℕ+) (hi : m < (i : ℕ)) :
    shiftPosition m (unshiftPosition m i) = i := by
  apply PNat.eq
  rw [shiftPosition_val]
  have hSub : (unshiftPosition m i : ℕ) = (i : ℕ) - m :=
    PNat.toPNat'_coe (Nat.sub_pos_of_lt hi)
  rw [hSub]
  omega

/-- Subtracting an offset from a translated position recovers the original position. -/
theorem unshiftPosition_shift (m : ℕ) (i : ℕ+) :
    unshiftPosition m (shiftPosition m i) = i := by
  apply PNat.eq
  have hPositive : 0 < (shiftPosition m i : ℕ) - m := by
    rw [shiftPosition_val]
    have hp := i.pos
    omega
  change (((shiftPosition m i : ℕ) - m).toPNat' : ℕ) = (i : ℕ)
  rw [PNat.toPNat'_coe hPositive, shiftPosition_val]
  omega

/-- Translating an initial Boolean family realizes the corresponding final interval family. -/
theorem shiftPermHom_boolean_mem (m n : ℕ) (w : FinitaryPerm ℕ+) (hw : w ∈ boolean n) :
    shiftPermHom m w ∈ booleanOn (m + n) (positionInterval (m + 1) (m + n)) := by
  have h := (mem_boolean _ _).mp hw
  have hN : (w.lexFirstReducedWord.map (shiftPosition m)).Nodup :=
    List.Nodup.map (shiftPosition m).injective h.2.lexFirst_nodup
  have hLower : ∀ i ∈ w.lexFirstReducedWord.map (shiftPosition m), m.succPNat ≤ i := by
    intro i hi
    obtain ⟨j, _hj, rfl⟩ := List.mem_map.mp hi
    change m + 1 ≤ m + (j : ℕ)
    have hp := j.pos
    omega
  have hUpper : ∀ i ∈ w.lexFirstReducedWord.map (shiftPosition m), (i : ℕ) < m + n := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    rw [shiftPosition_val]
    have hOld := lexFirst_letter_bound w h.1 j hj
    omega
  have hMem := wordProduct_mem_booleanOn_interval (m + n) m.succPNat _ hN hLower hUpper
  rw [wordProduct_map_shift, (isReducedWordIn_lexFirst w).1.1] at hMem
  simpa only [Nat.succPNat_coe, Nat.succ_eq_add_one] using hMem

/-- Every final-interval Boolean permutation has an initial inverse image under translation. -/
theorem shiftPermHom_boolean_surj (m n : ℕ) :
    Set.SurjOn (shiftPermHom m) (boolean n : Set (FinitaryPerm ℕ+))
      (booleanOn (m + n) (positionInterval (m + 1) (m + n)) : Set _) := by
  intro v hv
  change v ∈ booleanOn (m + n) (positionInterval (m + 1) (m + n)) at hv
  have hV := (mem_booleanOn_interval_word (m + n) m.succPNat v).mp (by
    simpa only [Nat.succPNat_coe, Nat.succ_eq_add_one] using hv)
  have h := (mem_boolean _ _).mp hV.1
  have hAbove : ∀ i ∈ v.lexFirstReducedWord, m < (i : ℕ) := by
    intro i hi
    have hLow := hV.2 i hi
    change m + 1 ≤ (i : ℕ) at hLow
    omega
  let word := v.lexFirstReducedWord.map (unshiftPosition m)
  have hN : word.Nodup := by
    apply List.Nodup.map_on _ h.2.lexFirst_nodup
    intro i hi j hj he
    have heShift := congrArg (shiftPosition m) he
    simpa only [shiftPosition_unshift m i (hAbove i hi),
      shiftPosition_unshift m j (hAbove j hj)] using heShift
  have hUpper : ∀ i ∈ word, (i : ℕ) < n := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hSmall : (unshiftPosition m j : ℕ) = (j : ℕ) - m :=
      PNat.toPNat'_coe (Nat.sub_pos_of_lt (hAbove j hj))
    rw [hSmall]
    have hOld := lexFirst_letter_bound v h.1 j hj
    have hLow := hAbove j hj
    omega
  have hRecover : word.map (shiftPosition m) = v.lexFirstReducedWord := by
    change (v.lexFirstReducedWord.map (unshiftPosition m)).map (shiftPosition m) = _
    rw [List.map_map]
    calc
      _ = v.lexFirstReducedWord.map id := List.map_congr_left fun i hi =>
        shiftPosition_unshift m i (hAbove i hi)
      _ = _ := List.map_id v.lexFirstReducedWord
  refine ⟨wordProduct word, wordProduct_mem_boolean n word hN hUpper, ?_⟩
  rw [← wordProduct_map_shift, hRecover, (isReducedWordIn_lexFirst v).1.1]

/-- Translation is a bijection between an initial and the corresponding final Boolean family. -/
theorem shiftPermHom_boolean_bijOn (m n : ℕ) :
    Set.BijOn (shiftPermHom m) (boolean n : Set (FinitaryPerm ℕ+))
      (booleanOn (m + n) (positionInterval (m + 1) (m + n)) : Set _) :=
  ⟨fun w hw => shiftPermHom_boolean_mem m n w hw,
    (shiftPermHom_injective m).injOn, shiftPermHom_boolean_surj m n⟩

/-- A translated final-interval Boolean family has the same cardinality as its initial family. -/
theorem card_booleanOn_shifted (m n : ℕ) :
    (booleanOn (m + n) (positionInterval (m + 1) (m + n))).card = (boolean n).card :=
  (Finset.card_nbij (shiftPermHom m) (shiftPermHom_boolean_bijOn m n).1
    (shiftPermHom_boolean_bijOn m n).2.1 (shiftPermHom_boolean_bijOn m n).2.2).symm

end FinitaryPerm
