import SchubertForwardStability.Permutations.Classes.Intervals.WordIntervals
import SchubertForwardStability.Permutations.Classes.Intervals.BlockPartition

/-! # Constructive interval factors at Boolean records

Splitting the selected word constructs the small and large interval factors.
Their one-position overlap gives uniqueness.
-/

namespace FinitaryPerm

/-- Every Boolean record has two initial/final interval factors. -/
theorem boolean_record_factor_exists (n : ℕ) (w : FinitaryPerm ℕ+) (hw : w ∈ boolean n)
    (r : ℕ+) (hr : IsRecord w r) : ∃ p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+,
      p.1 ∈ booleanOn n (positions (r : ℕ)) ∧
      p.2 ∈ booleanOn n (positionInterval (r : ℕ) n) ∧ p.1 * p.2 = w := by
  obtain ⟨hSupport, hBool⟩ := (mem_boolean n w).mp hw
  have hWord := (isReducedWordIn_lexFirst w).1
  have hN := hBool.lexFirst_nodup
  have hUpper : ∀ i ∈ w.lexFirstReducedWord, (i : ℕ) < n :=
    fun i hi => lexFirst_letter_bound w hSupport i hi
  by_cases hFirst : r = 1
  · subst r
    refine ⟨(1, w), one_mem_booleanOn n _, ?_, one_mul w⟩
    have h := wordProduct_mem_booleanOn_interval n 1 w.lexFirstReducedWord hN
      (fun _ _ => one_le) hUpper
    simpa only [hWord.1] using h
  · let j : ℕ+ := ⟨(r : ℕ) - 1, by
      have hp := r.pos
      have hNe : (r : ℕ) ≠ 1 := fun h => hFirst (PNat.eq h)
      omega⟩
    have hR : r = j + 1 := by
      apply PNat.eq
      change (r : ℕ) = (r : ℕ) - 1 + 1
      have hp := r.pos
      omega
    have hCut := hBool.word_cut_eq j (by rw [← hR]; exact hr)
    let L := w.lexFirstReducedWord.filter fun i => decide (i ≤ j)
    let H := w.lexFirstReducedWord.filter fun i => decide (j < i)
    have hLUpper : ∀ i ∈ L, (i : ℕ) < n :=
      fun i hi => hUpper i (List.mem_filter.mp hi).1
    have hHUpper : ∀ i ∈ H, (i : ℕ) < n :=
      fun i hi => hUpper i (List.mem_filter.mp hi).1
    have hSmall : ∀ i ∈ L, (i : ℕ) < (r : ℕ) := by
      intro i hi
      have hLow : i ≤ j := of_decide_eq_true (List.mem_filter.mp hi).2
      rw [hR]
      change (i : ℕ) < (j : ℕ) + 1
      exact Nat.lt_succ_of_le hLow
    have hLarge : ∀ i ∈ H, r ≤ i := by
      intro i hi
      have hHigh : j < i := of_decide_eq_true (List.mem_filter.mp hi).2
      rw [hR]
      change (j : ℕ) + 1 ≤ (i : ℕ)
      exact Nat.succ_le_of_lt hHigh
    refine ⟨(wordProduct L, wordProduct H),
      wordProduct_mem_booleanOn_initial n r L (hN.filter _) hLUpper hSmall,
      wordProduct_mem_booleanOn_interval n r H (hN.filter _) hLarge hHUpper, ?_⟩
    rw [← wordProduct_append]
    change wordProduct (w.lexFirstReducedWord.filter (fun i => decide (i ≤ j)) ++
      w.lexFirstReducedWord.filter (fun i => decide (j < i))) = w
    rw [hCut, hWord.1]

/-- The two initial/final interval factors of a Boolean record are unique. -/
theorem boolean_record_factor_unique (n : ℕ) (w : FinitaryPerm ℕ+) (hw : w ∈ boolean n)
    (r : ℕ+) (hr : IsRecord w r) : ∃! p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+,
      p.1 ∈ booleanOn n (positions (r : ℕ)) ∧
      p.2 ∈ booleanOn n (positionInterval (r : ℕ) n) ∧ p.1 * p.2 = w := by
  obtain ⟨p, hp1, hp2, he⟩ := boolean_record_factor_exists n w hw r hr
  refine ⟨p, ⟨hp1, hp2, he⟩, ?_⟩
  rintro q ⟨hq1, hq2, hq⟩
  exact booleanInterval_product_injOn n r (Finset.mem_product.mpr ⟨hq1, hq2⟩)
    (Finset.mem_product.mpr ⟨hp1, hp2⟩) (hq.trans he.symm)

end FinitaryPerm
