import SchubertForwardStability.Permutations.Classes.Intervals.BlockRuns
import SchubertForwardStability.Permutations.Classes.Boolean.BooleanLex

/-! # Ascending intervals of distinct decreasing runs

Disjoint interval supports and a noninverted maximal boundary force all letters
of the first block to be smaller than every letter of the next block.
-/

namespace FinitaryPerm

private theorem interval_separation (a0 a1 b0 b1 : ℕ+) (ha : a0 ≤ a1) (hb : b0 ≤ b1)
    (hd : ∀ k : ℕ+, ¬(a0 ≤ k ∧ k ≤ a1 ∧ b0 ≤ k ∧ k ≤ b1))
    (hl : a0 < b1) : a1 < b0 := by
  by_contra hn
  exact hd (max a0 b0)
    ⟨le_max_left _ _, max_le ha (le_of_not_gt hn), le_max_right _ _, max_le hl.le hb⟩

/-- Distinct-generator words with no commuting inversion have ascending decreasing runs. -/
theorem isAscendingBlocks_decreasingBlocks (word : List ℕ+) (hN : word.Nodup)
    (hNo : ¬HasCommutingInversion word) : IsAscendingBlocks (decreasingBlocks word) := by
  intro pre suf a b heq x hx y hy
  have haMem : a ∈ decreasingBlocks word := by rw [heq]; simp
  have hbMem : b ∈ decreasingBlocks word := by rw [heq]; simp
  obtain ⟨a0, a1, ha, haWord⟩ := decreasingBlocks_interval word a haMem
  obtain ⟨b0, b1, hb, hbWord⟩ := decreasingBlocks_interval word b hbMem
  have hword : word = pre.flatten ++ a ++ b ++ suf.flatten := by
    rw [← decreasingBlocks_flatten word, heq]
    simp only [List.flatten_append, List.flatten_cons, List.append_assoc]
  have hN' := hN
  rw [hword] at hN'
  have hNR : (pre.flatten ++ ((a ++ b) ++ suf.flatten)).Nodup := by
    simpa only [List.append_assoc] using hN'
  have hNab : (a ++ b).Nodup := hNR.of_append_right.of_append_left
  have hD : ∀ k : ℕ+, k ∈ a → k ∉ b := List.disjoint_left.mp hNab.disjoint
  obtain ⟨ap, haSnoc⟩ := decreasingBlockWord_snoc a0 a1 ha
  obtain ⟨bs, hbHead⟩ := decreasingBlockWord_head b0 b1 hb
  have hBoundary : word = (pre.flatten ++ ap) ++ a0 :: b1 :: (bs ++ suf.flatten) := by
    rw [hword, haWord, haSnoc, hbWord, hbHead]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hLow : a0 ≤ b1 + 1 := by
    by_contra hn
    exact hNo ⟨pre.flatten ++ ap, bs ++ suf.flatten, a0, b1, hBoundary, lt_of_not_ge hn⟩
  have hNotMerge : b1 + 1 ≠ a0 := by
    intro hj
    apply (isMaximalBlocks_decreasingBlocks word).2.2 pre suf a b heq
    refine ⟨a0, b1, ?_, ?_, hj⟩
    · rw [haWord, haSnoc]
      simp
    · rw [hbWord, hbHead]
      rfl
  have ha0 : a0 ∈ a := by
    rw [haWord, mem_decreasingBlockWord]
    exact ⟨le_rfl, ha⟩
  have hb1 : b1 ∈ b := by
    rw [hbWord, mem_decreasingBlockWord]
    exact ⟨hb, le_rfl⟩
  have hNe : a0 ≠ b1 := fun h => hD a0 ha0 (h.symm ▸ hb1)
  have hStrict : a0 < b1 := by
    have hL : (a0 : ℕ) ≤ (b1 : ℕ) + 1 := hLow
    have hE : (a0 : ℕ) ≠ (b1 : ℕ) := fun h => hNe (PNat.eq h)
    have hM : (b1 : ℕ) + 1 ≠ (a0 : ℕ) := fun h => hNotMerge (PNat.eq h)
    change (a0 : ℕ) < (b1 : ℕ)
    omega
  have hSep : a1 < b0 := interval_separation a0 a1 b0 b1 ha hb (by
    intro k hk
    exact hD k (haWord.symm ▸ (mem_decreasingBlockWord a0 a1 k).mpr ⟨hk.1, hk.2.1⟩)
      (hbWord.symm ▸ (mem_decreasingBlockWord b0 b1 k).mpr ⟨hk.2.2.1, hk.2.2.2⟩)) hStrict
  have hxI := (mem_decreasingBlockWord a0 a1 x).mp (haWord ▸ hx)
  have hyI := (mem_decreasingBlockWord b0 b1 y).mp (hbWord ▸ hy)
  exact lt_of_le_of_lt hxI.2 (lt_of_lt_of_le hSep hyI.1)

/-- The selected reduced word of a Boolean permutation has an ascending maximal block form. -/
theorem IsBoolean.blockNormalForm {w : FinitaryPerm ℕ+} (hw : IsBoolean w) :
    IsMaximalBlocks w.lexFirstReducedWord (decreasingBlocks w.lexFirstReducedWord) ∧
      IsAscendingBlocks (decreasingBlocks w.lexFirstReducedWord) :=
  ⟨isMaximalBlocks_decreasingBlocks _, isAscendingBlocks_decreasingBlocks _
    hw.lexFirst_nodup (not_hasCommutingInversion_lexFirst w)⟩

end FinitaryPerm
