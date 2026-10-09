import SchubertForwardStability.Permutations.Classes.Intervals.BlockCut
import Mathlib.Data.List.Chain

/-! # Ordered word partitions at record boundaries

Blocks lie wholly on one side of a record boundary. Their ascending order yields
a monotone threshold chain, and the word is the concatenation of its two generator
subwords.
-/

namespace FinitaryPerm

open scoped Classical

/-- Every selected decreasing block lies wholly below or wholly above a record boundary. -/
theorem IsBoolean.blocks_side {w : FinitaryPerm ℕ+} (hw : IsBoolean w) (j : ℕ+)
    (hr : IsRecord w (j + 1)) (b : List ℕ+)
    (hb : b ∈ decreasingBlocks w.lexFirstReducedWord) :
    (∀ x ∈ b, x ≤ j) ∨ ∀ x ∈ b, j < x := by
  obtain ⟨i, k, _, he⟩ := decreasingBlocks_interval _ b hb
  by_cases hk : k ≤ j
  · left
    intro x hx
    exact ((mem_decreasingBlockWord i k x).mp (he ▸ hx)).2.trans hk
  · have hUpper : j + 1 ≤ k := by
      have h : (j : ℕ) < (k : ℕ) := lt_of_not_ge hk
      change (j : ℕ) + 1 ≤ (k : ℕ)
      omega
    have hLower : j < i := lt_of_not_ge fun hi =>
      hw.blocks_no_cross j hr b hb ⟨i, k, hi, hUpper, he⟩
    right
    intro x hx
    exact hLower.trans_le ((mem_decreasingBlockWord i k x).mp (he ▸ hx)).1

/-- Once a selected generator exceeds a record cut, every following generator also exceeds it. -/
theorem IsBoolean.word_cut_chain {w : FinitaryPerm ℕ+} (hw : IsBoolean w) (j : ℕ+)
    (hr : IsRecord w (j + 1)) :
    w.lexFirstReducedWord.IsChain (fun a b => j < a → j < b) := by
  rw [← decreasingBlocks_flatten w.lexFirstReducedWord]
  have hNon : [] ∉ decreasingBlocks w.lexFirstReducedWord := by
    intro h
    exact List.ne_nil_of_mem_splitBy h rfl
  apply (List.isChain_flatten hNon).mpr
  constructor
  · intro b hb
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro a c pre suf he hHigh
    have ha : a ∈ b := by rw [he]; simp
    have hc : c ∈ b := by rw [he]; simp
    rcases hw.blocks_side j hr b hb with hLow | hLarge
    · exact ((not_lt_of_ge (hLow a ha)) hHigh).elim
    · exact hLarge c hc
  · apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro a b pre suf he x hx y hy hHigh
    exact hHigh.trans (hw.blockNormalForm.2 pre suf a b he x
      (List.mem_of_mem_getLast? hx) y (List.mem_of_mem_head? hy))

private theorem cut_pairwise_split (j : ℕ+) (word : List ℕ+)
    (h : word.Pairwise (fun a b => j < a → j < b)) :
    word.filter (fun x => decide (x ≤ j)) ++ word.filter (fun x => decide (j < x)) = word := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    obtain ⟨hHead, hTail⟩ := List.pairwise_cons.mp h
    by_cases ha : a ≤ j
    · simp [ha, not_lt_of_ge ha, ih hTail]
    · have hHigh : j < a := lt_of_not_ge ha
      have hAll : ∀ b ∈ word, j < b := fun b hb => hHead b hb hHigh
      have hLowFilter : word.filter (fun x => decide (x ≤ j)) = [] :=
        List.filter_eq_nil_iff.mpr fun b hb => by simp [not_le_of_gt (hAll b hb)]
      have hHighFilter : word.filter (fun x => decide (j < x)) = word :=
        List.filter_eq_self.mpr fun b hb => by simp [hAll b hb]
      simp [ha, hHigh, hLowFilter, hHighFilter]

/-- A selected Boolean word is its small-generator subword followed by its large one. -/
theorem IsBoolean.word_cut_eq {w : FinitaryPerm ℕ+} (hw : IsBoolean w) (j : ℕ+)
    (hr : IsRecord w (j + 1)) :
    w.lexFirstReducedWord.filter (fun x => decide (x ≤ j)) ++
      w.lexFirstReducedWord.filter (fun x => decide (j < x)) = w.lexFirstReducedWord := by
  let : Trans (fun a b : ℕ+ => j < a → j < b)
      (fun a b : ℕ+ => j < a → j < b) (fun a b : ℕ+ => j < a → j < b) :=
    ⟨fun h₁ h₂ ha => h₂ (h₁ ha)⟩
  exact cut_pairwise_split j _ (hw.word_cut_chain j hr).pairwise

end FinitaryPerm
