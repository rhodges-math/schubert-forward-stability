import SchubertForwardStability.Permutations.Classes.Intervals.BlockWords
import Mathlib.Data.List.SplitBy

/-! # Maximal decreasing blocks from adjacent runs

The standard list run splitter yields nonempty consecutive-decreasing intervals.
Its terminal-to-initial boundary condition is exactly maximality of the blocks.
-/

namespace FinitaryPerm

/-- The maximal runs of consecutive decreasing positive generators in a word. -/
def decreasingBlocks (word : List ℕ+) : List (List ℕ+) :=
  word.splitBy fun x y => decide (y + 1 = x)

private theorem chain_cons_block (j : ℕ+) (tail : List ℕ+)
    (hc : (j :: tail).IsChain fun x y => y + 1 = x) :
    ∃ i : ℕ+, i ≤ j ∧ j :: tail = decreasingBlockWord i j := by
  induction tail generalizing j with
  | nil => exact ⟨j, le_rfl, (decreasingBlockWord_self j).symm⟩
  | cons k tail ih =>
    have hjk : k + 1 = j := (List.isChain_cons_cons.mp hc).1
    obtain ⟨i, hik, heq⟩ := ih k hc.tail
    refine ⟨i, ?_, ?_⟩
    · rw [← hjk]
      have hN : (i : ℕ) ≤ (k : ℕ) := hik
      change (i : ℕ) ≤ (k : ℕ) + 1
      omega
    · rw [← hjk, heq]
      exact (decreasingBlockWord_succ i k hik).symm

/-- The maximal decreasing runs concatenate to the original word. -/
@[simp]
theorem decreasingBlocks_flatten (word : List ℕ+) : (decreasingBlocks word).flatten = word :=
  List.flatten_splitBy _ _

/-- Every standard decreasing run is a nonempty closed decreasing interval. -/
theorem decreasingBlocks_interval (word : List ℕ+) (b : List ℕ+)
    (hb : b ∈ decreasingBlocks word) :
    ∃ i j : ℕ+, i ≤ j ∧ b = decreasingBlockWord i j := by
  have hn : b ≠ [] := List.ne_nil_of_mem_splitBy hb
  have hc : b.IsChain fun x y => y + 1 = x := by
    simpa only [decide_eq_true_eq] using List.isChain_of_mem_splitBy hb
  cases b with
  | nil => exact (hn rfl).elim
  | cons j tail =>
    obtain ⟨i, hij, heq⟩ := chain_cons_block j tail hc
    exact ⟨i, j, hij, heq⟩

/-- The standard decreasing runs satisfy the maximal-block factorization predicate. -/
theorem isMaximalBlocks_decreasingBlocks (word : List ℕ+) :
    IsMaximalBlocks word (decreasingBlocks word) := by
  refine ⟨decreasingBlocks_flatten word, decreasingBlocks_interval word, ?_⟩
  intro pre suf a b heq
  have hc := List.isChain_getLast_head_splitBy
    (fun x y : ℕ+ => decide (y + 1 = x)) word
  change (decreasingBlocks word).IsChain _ at hc
  rw [heq] at hc
  have hpair := (List.isChain_cons_cons.mp (List.isChain_append.mp hc).2.1).1
  obtain ⟨ha, hb, hfalse⟩ := hpair
  rintro ⟨i, j, hi, hj, hji⟩
  have hilast : a.getLast ha = i := List.getLast_of_mem_getLast? (by rw [hi]; simp)
  have hjhead : b.head hb = j := List.head_of_mem_head? (by rw [hj]; simp)
  simp only [hilast, hjhead, hji, decide_true] at hfalse
  cases hfalse

end FinitaryPerm
