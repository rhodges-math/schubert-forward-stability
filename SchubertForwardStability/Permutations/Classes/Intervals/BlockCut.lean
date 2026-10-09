import SchubertForwardStability.Permutations.Classes.Tags.TagRecords
import SchubertForwardStability.Permutations.Classes.Intervals.BlockAscending
import SchubertForwardStability.Permutations.Classes.Tags.TagReadout

/-! # Record boundaries separate decreasing blocks

Every neighboring descending pair in an interval block is a contiguous subword.
A record boundary rules out precisely the pair that would cross that boundary.
-/

namespace FinitaryPerm

open scoped Classical

/-- A neighboring descending pair inside a block is a contiguous subword of that block. -/
theorem pair_infix_decreasingBlock (i j k : ℕ+) (hij : i ≤ j) (hjk : j + 1 ≤ k) :
    [j + 1, j].IsInfix (decreasingBlockWord i k) := by
  induction k using PNat.recOn with
  | one =>
    change (j : ℕ) + 1 ≤ 1 at hjk
    have hp := j.pos
    omega
  | succ k ih =>
    have hkj : j ≤ k := by
      have h : (j : ℕ) + 1 ≤ (k : ℕ) + 1 := hjk
      change (j : ℕ) ≤ (k : ℕ)
      omega
    rw [decreasingBlockWord_succ i k (hij.trans hkj)]
    by_cases he : k = j
    · subst k
      obtain ⟨tail, hTail⟩ := decreasingBlockWord_head i j hij
      exact ⟨[], tail, by simp [hTail]⟩
    · have hInside : j + 1 ≤ k := by
        have h : (j : ℕ) ≤ (k : ℕ) := hkj
        have hNe : (k : ℕ) ≠ (j : ℕ) := fun h => he (PNat.eq h)
        change (j : ℕ) + 1 ≤ (k : ℕ)
        omega
      obtain ⟨pre, suf, hWord⟩ := ih hInside
      exact ⟨(k + 1) :: pre, suf, by
        simpa only [List.cons_append] using congrArg (List.cons (k + 1)) hWord⟩

/-- A Boolean record position cannot be a continuing generator index. -/
theorem IsBoolean.record_not_continues {w : FinitaryPerm ℕ+} (hw : IsBoolean w)
    (j : ℕ+) (hr : IsRecord w j) : ¬GeneratorContinues w j := by
  intro hc
  let n := max w.forwardStability (j : ℕ)
  have hs : IsSupported n w := w.isSupported_forwardStability.mono (le_max_left _ _)
  have hMem := (mem_boolean n w).mpr ⟨hs, hw⟩
  obtain ⟨a, b, ha, hba, hPair⟩ := hc
  have hA : a ∈ w.lexFirstReducedWord := hPair.sublist.subset (by simp)
  have hBound := lexFirst_letter_bound w hs a hA
  rw [ha] at hBound
  have hc' : GeneratorContinues w j := ⟨a, b, ha, hba, hPair⟩
  obtain ⟨p, hp, hPres⟩ := generatorContinues_predecessor w j hc'
  have hPred : (p : ℕ) = (j : ℕ) - 1 := by omega
  have hPrev : blockTag n w ((j : ℕ) - 1) ≠ .zero := by
    rw [blockTag_ne_zero_iff]
    exact ⟨by rw [← hPred]; exact p.pos, by omega,
      by simpa only [hPred] using hPres⟩
  have hCurrent : blockTag n w j = .cont := (blockTag_eq_cont_iff n w j).mpr
    ⟨⟨j.pos, hBound, a, ha, hA⟩, hc'⟩
  have hNotStart : blockTag n w j ≠ .start := by rw [hCurrent]; decide
  have hLocal := boolean_nonRecord_local n w hMem j (le_max_right _ _)
  rw [nonRecordIndicator_eq_zero hr, ite_eq_left ⟨hPrev, hNotStart⟩] at hLocal
  exact Nat.zero_ne_one hLocal

/-- A decreasing block of a Boolean selected word cannot cross a record boundary. -/
theorem IsBoolean.blocks_no_cross {w : FinitaryPerm ℕ+} (hw : IsBoolean w) (j : ℕ+)
    (hr : IsRecord w (j + 1)) (b : List ℕ+)
    (hb : b ∈ decreasingBlocks w.lexFirstReducedWord) :
    ¬∃ i k : ℕ+, i ≤ j ∧ j + 1 ≤ k ∧ b = decreasingBlockWord i k := by
  rintro ⟨i, k, hij, hjk, hBlock⟩
  have hPair := pair_infix_decreasingBlock i j k hij hjk
  rw [← hBlock] at hPair
  obtain ⟨pre, suf, hBlocks⟩ := List.mem_iff_append.mp hb
  have hWord : w.lexFirstReducedWord = pre.flatten ++ b ++ suf.flatten := by
    rw [← decreasingBlocks_flatten w.lexFirstReducedWord, hBlocks]
    simp only [List.flatten_append, List.flatten_cons, List.append_assoc]
  have hInfix : b.IsInfix w.lexFirstReducedWord := ⟨pre.flatten, suf.flatten, hWord.symm⟩
  exact hw.record_not_continues (j + 1) hr ⟨j + 1, j, rfl, rfl, hPair.trans hInfix⟩

end FinitaryPerm
