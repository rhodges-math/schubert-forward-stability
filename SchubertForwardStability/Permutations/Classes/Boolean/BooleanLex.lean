import SchubertForwardStability.Permutations.Classes.Boolean.BooleanSupport
import SchubertForwardStability.Permutations.Classes.Boolean.BooleanRecords

/-! # Adjacent order in lexicographically selected reduced words

Separated adjacent transpositions commute. Swapping an inverted separated pair
preserves the represented permutation and creates a lexicographically smaller word.
-/

namespace FinitaryPerm

/-- Adjacent transpositions commute when their positive indices are separated by a gap. -/
theorem simpleTransposition_comm_gap (i j : ℕ+) (h : (j : ℕ) + 1 < (i : ℕ)) :
    simpleTransposition i * simpleTransposition j =
      simpleTransposition j * simpleTransposition i := by
  have hj0 : j ≠ i := by
    intro he
    have hn := congrArg PNat.val he
    omega
  have hj1 : j ≠ i + 1 := by
    intro he
    have hn := congrArg PNat.val he
    change (j : ℕ) = (i : ℕ) + 1 at hn
    omega
  have hs0 : j + 1 ≠ i := by
    intro he
    have hn := congrArg PNat.val he
    change (j : ℕ) + 1 = (i : ℕ) at hn
    omega
  have hs1 : j + 1 ≠ i + 1 := by
    intro he
    have hn := congrArg PNat.val he
    change (j : ℕ) + 1 = (i : ℕ) + 1 at hn
    omega
  apply Subtype.ext
  change Equiv.swap i (i + 1) * Equiv.swap j (j + 1) =
    Equiv.swap j (j + 1) * Equiv.swap i (i + 1)
  rw [Equiv.mul_swap_eq_swap_mul,
    Equiv.swap_apply_of_ne_of_ne hj0 hj1, Equiv.swap_apply_of_ne_of_ne hs0 hs1]

/-- Consecutive letters in the selected reduced word cannot have a separated downward gap. -/
theorem lexFirst_adjacent_order (w : FinitaryPerm ℕ+) (pre suf : List ℕ+) (i j : ℕ+)
    (heq : w.lexFirstReducedWord = pre ++ i :: j :: suf) : i ≤ j + 1 := by
  by_contra hn
  change ¬ (i : ℕ) ≤ (j : ℕ) + 1 at hn
  have hgap : (j : ℕ) + 1 < (i : ℕ) := Nat.lt_of_not_ge hn
  have hj : j < i := by
    change (j : ℕ) < (i : ℕ)
    omega
  have hc := simpleTransposition_comm_gap i j hgap
  have hprod : wordProduct (pre ++ j :: i :: suf) = wordProduct (pre ++ i :: j :: suf) := by
    simpa only [wordProduct_append, wordProduct_cons, mul_assoc] using
      congrArg (fun a => wordProduct pre * (a * wordProduct suf)) hc.symm
  have ho := isReducedWordIn_lexFirst w
  have hv : IsReducedWordIn w.forwardStability w (pre ++ j :: i :: suf) := by
    refine ⟨⟨hprod.trans ((congrArg wordProduct heq).symm.trans ho.1.1), ?_⟩, ?_⟩
    · calc
        (pre ++ j :: i :: suf).length = (pre ++ i :: j :: suf).length := by simp
        _ = w.lexFirstReducedWord.length := congrArg List.length heq.symm
        _ = w.length := ho.1.2
    · intro k hk
      apply ho.2 k
      rw [heq]
      simpa only [List.mem_append, List.mem_cons, or_comm, or_left_comm, or_assoc] using hk
  have hlt : (pre ++ j :: i :: suf) < w.lexFirstReducedWord := by
    rw [heq]
    exact List.Lex.append_left _ (List.Lex.rel hj) pre
  exact (not_lt_of_ge (lexFirstReducedWord_le w _ hv)) hlt

/-- The selected reduced word has no contiguous separated pair in decreasing order. -/
theorem not_hasCommutingInversion_lexFirst (w : FinitaryPerm ℕ+) :
    ¬ HasCommutingInversion w.lexFirstReducedWord := by
  rintro ⟨pre, suf, i, j, heq, hgap⟩
  exact (not_lt_of_ge (lexFirst_adjacent_order w pre suf i j heq)) hgap

/-- Exchanging a separated adjacent pair preserves its represented permutation. -/
theorem WordCommutation.wordProduct_eq {a b : List ℕ+} (h : WordCommutation a b) :
    wordProduct a = wordProduct b := by
  obtain ⟨pre, suf, i, j, rfl, rfl, hgap⟩ := h
  have hc : simpleTransposition i * simpleTransposition j =
      simpleTransposition j * simpleTransposition i := by
    rcases hgap with hgap | hgap
    · exact (simpleTransposition_comm_gap j i hgap).symm
    · exact simpleTransposition_comm_gap i j hgap
  simpa only [wordProduct_append, wordProduct_cons, mul_assoc] using
    congrArg (fun a => wordProduct pre * (a * wordProduct suf)) hc

/-- Exchanging a separated adjacent pair preserves word length. -/
theorem WordCommutation.length_eq {a b : List ℕ+} (h : WordCommutation a b) :
    a.length = b.length := by
  obtain ⟨pre, suf, i, j, rfl, rfl, _⟩ := h
  simp

/-- Exchanging a separated adjacent pair preserves its finite generator support. -/
theorem WordCommutation.toFinset_eq {a b : List ℕ+} (h : WordCommutation a b) :
    a.toFinset = b.toFinset := by
  obtain ⟨pre, suf, i, j, rfl, rfl, _⟩ := h
  simp [Finset.insert_comm]

end FinitaryPerm
