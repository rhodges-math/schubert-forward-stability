import SchubertForwardStability.Permutations.Random.Tags.TagSampler

/-! # Coordinate alphabets for prescribed presence paths

A full presence path determines an allowed alphabet at each position. Valid words
with this path are exactly the Cartesian product of those coordinate alphabets.
-/

namespace FinitaryPerm

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- The external zero position has absent presence state. -/
theorem tagPresence_zero {m : ℕ} (T : Fin m → BlockTag) : tagPresence T 0 = false := by
  simp [tagPresence]

/-- At a finite coordinate, presence is exactly the nonzero-symbol indicator. -/
theorem tagPresence_fin {m : ℕ} (T : Fin m → BlockTag) (i : Fin m) :
    tagPresence T (i.val + 1) = decide (T i ≠ .zero) := by
  simp [tagPresence, i.isLt]

/-- A full presence history is its absent external state and the finite coordinate states. -/
theorem presenceHistory_full_iff {m : ℕ} (T : Fin m → BlockTag) (y : ℕ → Bool) :
    T ∈ presenceHistory m y ↔ y 0 = false ∧
      ∀ i : Fin m, decide (T i ≠ .zero) = y (i.val + 1) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [tagPresence_zero, eq_comm] using h 0 (Nat.zero_le _)
    · intro i
      simpa only [tagPresence_fin] using h (i.val + 1) (by omega)
  · rintro ⟨hy0, hcoords⟩ s hs
    cases s with
    | zero => simp only [tagPresence_zero, hy0]
    | succ s =>
      have hs' : s < m := by omega
      rw [tagPresence_fin T ⟨s, hs'⟩]
      exact hcoords ⟨s, hs'⟩

/-- The allowed symbol alphabet for prescribed preceding and current presence states. -/
def tagAlphabet (a b : Bool) : Finset BlockTag :=
  if b then if a then {.start, .cont} else {.start} else {.zero}

/-- Membership in a coordinate alphabet is the prescribed presence and continuation condition. -/
theorem mem_tagAlphabet (a b : Bool) (t : BlockTag) :
    t ∈ tagAlphabet a b ↔ decide (t ≠ .zero) = b ∧ (t = .cont → a = true) := by
  cases a <;> cases b <;> cases t <;> simp [tagAlphabet]

/-- Valid finite tag vectors with the prescribed full presence history. -/
noncomputable def tagHistoryWords (m : ℕ) (y : ℕ → Bool) : Finset (Fin m → BlockTag) :=
  (tagWords m).filter fun T => T ∈ presenceHistory m y

/-- A full-history tag-word fiber is the product of its prescribed coordinate alphabets. -/
theorem mem_tagHistoryWords {m : ℕ} (T : Fin m → BlockTag) (y : ℕ → Bool) :
    T ∈ tagHistoryWords m y ↔ y 0 = false ∧
      ∀ i : Fin m, T i ∈ tagAlphabet (y i.val) (y (i.val + 1)) := by
  rw [tagHistoryWords, Finset.mem_filter, mem_tagWords, presenceHistory_full_iff]
  constructor
  · rintro ⟨hv, hy0, hcoords⟩
    refine ⟨hy0, fun i => ?_⟩
    rw [mem_tagAlphabet]
    refine ⟨hcoords i, fun hc => ?_⟩
    rcases hv i hc with ⟨_, hfalse⟩ | ⟨j, hji, hj⟩
    · cases hfalse
    · have htrue : decide (T j ≠ .zero) = true := decide_eq_true hj
      rw [hcoords j, hji] at htrue
      exact htrue
  · rintro ⟨hy0, halphabet⟩
    have hcoords : ∀ i : Fin m, decide (T i ≠ .zero) = y (i.val + 1) :=
      fun i => ((mem_tagAlphabet _ _ _).mp (halphabet i)).1
    refine ⟨?_, hy0, hcoords⟩
    intro i hc
    have hp : y i.val = true := ((mem_tagAlphabet _ _ _).mp (halphabet i)).2 hc
    by_cases hi : i.val = 0
    · rw [hi, hy0] at hp
      cases hp
    · right
      let j : Fin m := ⟨i.val - 1, by omega⟩
      have hji : j.val + 1 = i.val := by dsimp [j]; omega
      refine ⟨j, hji, ?_⟩
      have hj : decide (T j ≠ .zero) = true := by rw [hcoords j, hji, hp]
      by_contra hzero
      simp only [hzero, ne_eq, not_true_eq_false, decide_false] at hj
      cases hj

/-- A coordinate alphabet has two symbols exactly when both presence states are true. -/
theorem card_tagAlphabet (a b : Bool) :
    (tagAlphabet a b).card = if a = true ∧ b = true then 2 else 1 := by
  cases a <;> cases b <;> simp [tagAlphabet]

/-- Full-history vectors are equivalent to independent choices in their coordinate alphabets. -/
noncomputable def tagHistoryEquiv (m : ℕ) (y : ℕ → Bool) (hy0 : y 0 = false) :
    {T : Fin m → BlockTag // T ∈ tagHistoryWords m y} ≃
      ((i : Fin m) → {a : BlockTag // a ∈ tagAlphabet (y i.val) (y (i.val + 1))}) where
  toFun T i := ⟨T.val i, ((mem_tagHistoryWords _ _).mp T.property).2 i⟩
  invFun Q := ⟨fun i => (Q i).val, (mem_tagHistoryWords _ _).mpr ⟨hy0, fun i => (Q i).property⟩⟩
  left_inv T := by apply Subtype.ext; rfl
  right_inv Q := by funext i; apply Subtype.ext; rfl

/-- With absent external state, a full path has two choices at each free position. -/
theorem card_tagHistoryWords_of_zero (m : ℕ) (y : ℕ → Bool) (hy0 : y 0 = false) :
    (tagHistoryWords m y).card = 2 ^ (freeTagPositions m y).card := by
  rw [← Fintype.card_coe, Fintype.card_congr (tagHistoryEquiv m y hy0), Fintype.card_pi]
  simp only [Fintype.card_coe, card_tagAlphabet]
  simp [Finset.prod_ite, freeTagPositions]

/-- Full-path fibers have the free-choice count, and inconsistent external paths are empty. -/
theorem card_tagHistoryWords (m : ℕ) (y : ℕ → Bool) :
    (tagHistoryWords m y).card =
      if y 0 = false then 2 ^ (freeTagPositions m y).card else 0 := by
  by_cases hy0 : y 0 = false
  · rw [ite_eq_left hy0]
    exact card_tagHistoryWords_of_zero m y hy0
  · rw [ite_eq_right hy0]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro T hT
    exact hy0 ((mem_tagHistoryWords T y).mp hT).1

/-- Every event under the finite tag law is its valid-vector count divided by the total. -/
theorem tagLaw_real_set (m : ℕ) (E : Set (Fin m → BlockTag)) :
    (tagLaw m).real E =
      (((tagWords m).filter fun T => T ∈ E).card : ℝ) / (tagWords m).card := by
  let s : Finset (Fin m → BlockTag) := Finset.univ.filter fun T => T ∈ E
  have hs : (s : Set (Fin m → BlockTag)) = E := by ext T; simp [s]
  have hi : tagWords m ∩ s = (tagWords m).filter fun T => T ∈ E := by
    ext T
    simp [s]
  have hμ : tagLaw m E =
      (((tagWords m).filter fun T => T ∈ E).card : ENNReal) / (tagWords m).card := by
    calc
      _ = tagLaw m (s : Set (Fin m → BlockTag)) := congrArg (tagLaw m) hs.symm
      _ = ((tagWords m ∩ s).card : ENNReal) / (tagWords m).card := uniformOn_apply_finset
      _ = _ := by rw [hi]
  simp only [measureReal_def, hμ, ENNReal.toReal_div, ENNReal.toReal_natCast]

/-- The probability of a full history is its fiber count divided by the number of all
words. -/
theorem tagLaw_full_history (m : ℕ) (y : ℕ → Bool) :
    (tagLaw m).real (presenceHistory m y) =
      ((tagHistoryWords m y).card : ℝ) / (tagWords m).card :=
  tagLaw_real_set m _

/-- A full prescribed path has positive probability exactly when its external state is absent. -/
theorem tagLaw_full_history_pos (m : ℕ) (y : ℕ → Bool) :
    0 < (tagLaw m).real (presenceHistory m y) ↔ y 0 = false := by
  rw [tagLaw_full_history, card_tagHistoryWords]
  have ht : 0 < ((tagWords m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (tagWords_nonempty m)
  by_cases hy0 : y 0 = false
  · rw [ite_eq_left hy0]
    simpa only [hy0, iff_true] using div_pos (by positivity :
      0 < ((2 ^ (freeTagPositions m y).card : ℕ) : ℝ)) ht
  · rw [ite_eq_right hy0]
    simp only [Nat.cast_zero, zero_div, lt_self_iff_false, false_iff]
    exact hy0

end FinitaryPerm
