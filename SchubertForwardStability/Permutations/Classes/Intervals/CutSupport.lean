import SchubertForwardStability.Permutations.Classes.Intervals.WordIntervals

/-! # Initial-interval preservation by distinct adjacent words

An adjacent generator is the only generator crossing its own initial cut.
In a distinct word its occurrence cannot be cancelled by the other generators.
This gives lower generator bounds from fixed-prefix conditions.
-/

namespace FinitaryPerm

/-- A permutation preserves the positive initial interval ending at i. -/
def PreservesInitial (w : FinitaryPerm ℕ+) (i : ℕ+) : Prop :=
  ∀ k : ℕ+, w k ≤ i ↔ k ≤ i

/-- Identity preserves every positive initial interval. -/
theorem preservesInitial_one (i : ℕ+) : PreservesInitial 1 i := fun _ => Iff.rfl

/-- Products preserve a common initial interval. -/
theorem PreservesInitial.mul {u v : FinitaryPerm ℕ+} {i : ℕ+}
    (hu : PreservesInitial u i) (hv : PreservesInitial v i) :
    PreservesInitial (u * v) i := fun k => by
  rw [mul_apply, hu, hv]

/-- Inversion preserves initial-interval preservation. -/
theorem PreservesInitial.inv {w : FinitaryPerm ℕ+} {i : ℕ+}
    (hw : PreservesInitial w i) : PreservesInitial w⁻¹ i := fun k => by
  simpa only [apply_inv_apply] using (hw (w⁻¹ k)).symm

/-- An adjacent transposition preserves precisely the initial cuts at other generators. -/
theorem simple_preservesInitial_iff (j i : ℕ+) :
    PreservesInitial (simpleTransposition j) i ↔ j ≠ i := by
  constructor
  · intro h he
    subst j
    have hi := h i
    rw [simpleTransposition_apply_left] at hi
    change (i : ℕ) + 1 ≤ (i : ℕ) ↔ (i : ℕ) ≤ (i : ℕ) at hi
    omega
  · intro h k
    have hNat : (j : ℕ) ≠ (i : ℕ) := fun he => h (PNat.eq he)
    by_cases hk : k = j
    · subst k
      rw [simpleTransposition_apply_left]
      change (j : ℕ) + 1 ≤ (i : ℕ) ↔ (j : ℕ) ≤ (i : ℕ)
      omega
    · by_cases hNext : k = j + 1
      · subst k
        rw [simpleTransposition_apply_right]
        change (j : ℕ) ≤ (i : ℕ) ↔ (j : ℕ) + 1 ≤ (i : ℕ)
        omega
      · change swap j (j + 1) k ≤ i ↔ k ≤ i
        rw [swap_apply_of_ne hk hNext]

/-- Avoiding a generator suffices to preserve its initial cut. -/
theorem word_preservesInitial (word : List ℕ+) (i : ℕ+) (h : i ∉ word) :
    PreservesInitial (wordProduct word) i := by
  induction word with
  | nil => exact preservesInitial_one i
  | cons j word ih =>
    rw [List.mem_cons, not_or] at h
    rw [wordProduct_cons]
    exact ((simple_preservesInitial_iff j i).mpr (fun he => h.1 he.symm)).mul (ih h.2)

/-- A distinct adjacent word preserves a cut exactly when its generator is absent. -/
theorem preservesInitial_word_iff (word : List ℕ+) (hN : word.Nodup) (i : ℕ+) :
    PreservesInitial (wordProduct word) i ↔ i ∉ word := by
  refine ⟨?_, word_preservesInitial word i⟩
  intro h hi
  obtain ⟨pre, suf, he⟩ := List.mem_iff_append.mp hi
  rw [he] at hN h
  have hSplit := List.nodup_append'.mp hN
  have hPre : i ∉ pre := fun hi =>
    (List.disjoint_left.mp hSplit.2.2 hi) List.mem_cons_self
  have hSuf : i ∉ suf := (List.nodup_cons.mp hSplit.2.1).1
  have hp := word_preservesInitial pre i hPre
  have hs := word_preservesInitial suf i hSuf
  have hSimple := hp.inv.mul (h.mul hs.inv)
  have hEq : (wordProduct pre)⁻¹ *
      (wordProduct (pre ++ i :: suf) * (wordProduct suf)⁻¹) = simpleTransposition i := by
    simp only [wordProduct_append, wordProduct_cons, mul_assoc, mul_inv_cancel,
      mul_one, inv_mul_cancel_left]
  rw [hEq] at hSimple
  exact ((simple_preservesInitial_iff i i).mp hSimple) rfl

/-- Fixing a prefix preserves every initial interval within that prefix. -/
theorem preservesInitial_of_fixed_below (w : FinitaryPerm ℕ+) (r i : ℕ+)
    (hFix : ∀ k : ℕ+, k < r → w k = k) (hi : i < r) : PreservesInitial w i := by
  intro k
  constructor
  · intro hk
    have he : w (w k) = w k := hFix (w k) (hk.trans_lt hi)
    have hFixed : w k = k := w.injective he
    simpa only [hFixed] using hk
  · intro hk
    rw [hFix k (hk.trans_lt hi)]
    exact hk

/-- The selected word of a Boolean permutation fixing a prefix has the matching lower bound. -/
theorem IsBoolean.lexFirst_lower {w : FinitaryPerm ℕ+} (hw : IsBoolean w) (r : ℕ+)
    (hFix : ∀ k : ℕ+, k < r → w k = k) : ∀ i ∈ w.lexFirstReducedWord, r ≤ i := by
  intro i hi
  by_contra hBound
  have hPreserve := preservesInitial_of_fixed_below w r i hFix (lt_of_not_ge hBound)
  have hWord := (isReducedWordIn_lexFirst w).1.1
  rw [← hWord] at hPreserve
  exact (preservesInitial_word_iff _ hw.lexFirst_nodup i).mp hPreserve hi

end FinitaryPerm
