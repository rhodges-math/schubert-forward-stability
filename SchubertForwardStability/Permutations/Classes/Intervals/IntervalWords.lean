import SchubertForwardStability.Permutations.Classes.Intervals.CutSupport
import SchubertForwardStability.Permutations.Classes.Tags.TagInjective

/-! # Selected words of restricted Boolean families

Fixed-complement conditions are equivalent to upper or lower bounds
on the distinct selected adjacent word.
-/

namespace FinitaryPerm

/-- Restricting a Boolean permutation to an initial interval bounds its selected generators. -/
theorem mem_booleanOn_initial_word (n m : ℕ) (w : FinitaryPerm ℕ+) :
    w ∈ booleanOn n (positions m) ↔
      w ∈ boolean n ∧ ∀ i ∈ w.lexFirstReducedWord, (i : ℕ) < m := by
  constructor
  · intro h
    have hw := (mem_booleanOn _ _ _).mp h
    have hSupport : IsSupported m w := fun k hk =>
      hw.2 k (by rw [mem_positions]; exact not_le_of_gt hk)
    exact ⟨hw.1, fun i hi => lexFirst_letter_bound w hSupport i hi⟩
  · rintro ⟨hw, hSmall⟩
    have h := (mem_boolean _ _).mp hw
    have hMem := wordProduct_mem_booleanOn_initial n m w.lexFirstReducedWord
      h.2.lexFirst_nodup (fun i hi => lexFirst_letter_bound w h.1 i hi) hSmall
    simpa only [(isReducedWordIn_lexFirst w).1.1] using hMem

/-- Restricting a Boolean permutation to a final interval bounds its selected generators below. -/
theorem mem_booleanOn_interval_word (n : ℕ) (r : ℕ+) (w : FinitaryPerm ℕ+) :
    w ∈ booleanOn n (positionInterval (r : ℕ) n) ↔
      w ∈ boolean n ∧ ∀ i ∈ w.lexFirstReducedWord, r ≤ i := by
  constructor
  · intro h
    have hw := (mem_booleanOn _ _ _).mp h
    have hFix : ∀ k : ℕ+, k < r → w k = k := by
      intro k hk
      exact hw.2 k (by rw [mem_positionInterval]; exact fun h => (not_le_of_gt hk) h.2)
    exact ⟨hw.1, ((mem_boolean _ _).mp hw.1).2.lexFirst_lower r hFix⟩
  · rintro ⟨hw, hLower⟩
    have h := (mem_boolean _ _).mp hw
    have hMem := wordProduct_mem_booleanOn_interval n r w.lexFirstReducedWord
      h.2.lexFirst_nodup hLower (fun i hi => lexFirst_letter_bound w h.1 i hi)
    simpa only [(isReducedWordIn_lexFirst w).1.1] using hMem

end FinitaryPerm
