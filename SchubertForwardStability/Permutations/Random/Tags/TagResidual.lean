import SchubertForwardStability.Permutations.Random.Tags.TagHistories

/-! # Prescribed-symbol counts inside full presence paths

Fixing any subset of free start/continuation positions leaves one choice there and
two at every other free position. The conditional probabilities are reciprocal powers.
-/

namespace FinitaryPerm

open scoped Classical BigOperators

/-- A compatible presence path forces absent symbols and fresh starts. -/
theorem tagHistory_forced {m : ℕ} (T : Fin m → BlockTag) (y : ℕ → Bool)
    (hT : T ∈ tagWords m) (hh : T ∈ presenceHistory m y) (i : Fin m) :
    (y (i.val + 1) = false → T i = .zero) ∧
      (y i.val = false → y (i.val + 1) = true → T i = .start) := by
  have hA := ((mem_tagHistoryWords T y).mp (Finset.mem_filter.mpr ⟨hT, hh⟩)).2 i
  constructor
  · intro hb
    simpa [tagAlphabet, hb] using hA
  · intro ha hb
    simpa [tagAlphabet, ha, hb] using hA

/-- A coordinate alphabet after additionally fixing the indicated set of symbols. -/
noncomputable def tagFixedAlphabet {m : ℕ} (y : ℕ → Bool) (J : Finset (Fin m))
    (a : Fin m → BlockTag) (i : Fin m) : Finset BlockTag :=
  if i ∈ J then (tagAlphabet (y i.val) (y (i.val + 1))).filter fun t => t = a i
  else tagAlphabet (y i.val) (y (i.val + 1))

/-- Full-history tag vectors satisfying the additional prescribed-symbol coordinates. -/
noncomputable def tagHistoryAssignments {m : ℕ} (y : ℕ → Bool) (J : Finset (Fin m))
    (a : Fin m → BlockTag) : Finset (Fin m → BlockTag) :=
  (tagHistoryWords m y).filter fun T => ∀ i ∈ J, T i = a i

/-- Constrained full-history membership is the product of the constrained alphabets. -/
theorem mem_tagHistoryAssignments {m : ℕ} (y : ℕ → Bool) (J : Finset (Fin m))
    (a T : Fin m → BlockTag) : T ∈ tagHistoryAssignments y J a ↔
      y 0 = false ∧ ∀ i : Fin m, T i ∈ tagFixedAlphabet y J a i := by
  rw [tagHistoryAssignments, Finset.mem_filter, mem_tagHistoryWords]
  constructor
  · rintro ⟨⟨hy0, hA⟩, hJ⟩
    refine ⟨hy0, fun i => ?_⟩
    by_cases hi : i ∈ J
    · simp only [tagFixedAlphabet, ite_eq_left hi, Finset.mem_filter]
      exact ⟨hA i, hJ i hi⟩
    · simp only [tagFixedAlphabet, ite_eq_right hi]
      exact hA i
  · rintro ⟨hy0, hA⟩
    refine ⟨⟨hy0, fun i => ?_⟩, ?_⟩
    · have h := hA i
      by_cases hi : i ∈ J
      · simp only [tagFixedAlphabet, ite_eq_left hi, Finset.mem_filter] at h
        exact h.1
      · simpa only [tagFixedAlphabet, ite_eq_right hi] using h
    · intro i hi
      have h := hA i
      simp only [tagFixedAlphabet, ite_eq_left hi, Finset.mem_filter] at h
      exact h.2

/-- Free coordinates fixed to an allowed symbol have one remaining choice. -/
theorem card_tagFixedAlphabet {m : ℕ} (y : ℕ → Bool) (J : Finset (Fin m))
    (a : Fin m → BlockTag) (hJ : J ⊆ freeTagPositions m y)
    (ha : ∀ i ∈ J, a i = .start ∨ a i = .cont) (i : Fin m) :
    (tagFixedAlphabet y J a i).card = if i ∈ freeTagPositions m y \ J then 2 else 1 := by
  by_cases hi : i ∈ J
  · have hf := (Finset.mem_filter.mp (hJ hi)).2
    rcases ha i hi with hs | hc
    · simp [tagFixedAlphabet, hi, tagAlphabet, hf.1, hf.2, hs, Finset.filter_insert]
    · simp [tagFixedAlphabet, hi, tagAlphabet, hf.1, hf.2, hc, Finset.filter_insert,
        Finset.filter_singleton]
  · simp [tagFixedAlphabet, hi, card_tagAlphabet, freeTagPositions]

/-- Prescribed full-history vectors are equivalent to their constrained coordinate choices. -/
noncomputable def tagAssignmentEquiv {m : ℕ} (y : ℕ → Bool) (J : Finset (Fin m))
    (a : Fin m → BlockTag) (hy0 : y 0 = false) :
    {T : Fin m → BlockTag // T ∈ tagHistoryAssignments y J a} ≃
      ((i : Fin m) → {t : BlockTag // t ∈ tagFixedAlphabet y J a i}) where
  toFun T i := ⟨T.val i, ((mem_tagHistoryAssignments _ _ _ _).mp T.property).2 i⟩
  invFun Q := ⟨fun i => (Q i).val,
    (mem_tagHistoryAssignments _ _ _ _).mpr ⟨hy0, fun i => (Q i).property⟩⟩
  left_inv T := by apply Subtype.ext; rfl
  right_inv Q := by funext i; apply Subtype.ext; rfl

/-- Prescribing allowed free symbols leaves two choices at every other free coordinate. -/
theorem card_tagHistoryAssignments {m : ℕ} (y : ℕ → Bool) (J : Finset (Fin m))
    (a : Fin m → BlockTag) (hy0 : y 0 = false) (hJ : J ⊆ freeTagPositions m y)
    (ha : ∀ i ∈ J, a i = .start ∨ a i = .cont) :
    (tagHistoryAssignments y J a).card = 2 ^ ((freeTagPositions m y).card - J.card) := by
  rw [← Fintype.card_coe, Fintype.card_congr (tagAssignmentEquiv y J a hy0), Fintype.card_pi]
  simp only [Fintype.card_coe]
  simp_rw [card_tagFixedAlphabet y J a hJ ha]
  have hf : (Finset.univ.filter fun i : Fin m => i ∈ freeTagPositions m y ∧ i ∉ J) =
      freeTagPositions m y \ J := by ext i; simp
  simp [Finset.prod_ite, hf, Finset.card_sdiff_of_subset hJ]

/-- A full-history assignment has as mass its count divided by the number of valid
words. -/
theorem tagLaw_history_assignment {m : ℕ} (y : ℕ → Bool) (J : Finset (Fin m))
    (a : Fin m → BlockTag) :
    (tagLaw m).real (presenceHistory m y ∩ {T | ∀ i ∈ J, T i = a i}) =
      ((tagHistoryAssignments y J a).card : ℝ) / (tagWords m).card := by
  rw [tagLaw_real_set]
  congr 2
  congr 1
  ext T
  simp [tagHistoryAssignments, tagHistoryWords, and_assoc]

/-- Free start/continuation symbols are independent fair choices given any positive full path. -/
theorem tagLaw_conditional_choices {m : ℕ} (y : ℕ → Bool)
    (hp : 0 < (tagLaw m).real (presenceHistory m y)) (J : Finset (Fin m))
    (hJ : J ⊆ freeTagPositions m y) (a : Fin m → BlockTag)
    (ha : ∀ i ∈ J, a i = .start ∨ a i = .cont) :
    (tagLaw m).real (presenceHistory m y ∩ {T | ∀ i ∈ J, T i = a i}) /
      (tagLaw m).real (presenceHistory m y) = ((2 : ℝ) ^ J.card)⁻¹ := by
  have hy0 := (tagLaw_full_history_pos m y).mp hp
  rw [tagLaw_history_assignment, tagLaw_full_history,
    card_tagHistoryAssignments y J a hy0 hJ ha, card_tagHistoryWords_of_zero m y hy0]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have ht : ((tagWords m).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (tagWords_nonempty m)).ne'
  have hpow : (2 : ℝ) ^ ((freeTagPositions m y).card - J.card) * 2 ^ J.card =
      2 ^ (freeTagPositions m y).card := by
    rw [← pow_add, Nat.sub_add_cancel (Finset.card_le_card hJ)]
  have hc : (2 : ℝ) ^ (freeTagPositions m y).card ≠ 0 := by positivity
  calc
    _ = (2 : ℝ) ^ ((freeTagPositions m y).card - J.card) /
        2 ^ (freeTagPositions m y).card := by field_simp
    _ = _ := by
      apply (div_eq_iff hc).mpr
      rw [← hpow]
      simp [mul_comm]

end FinitaryPerm
