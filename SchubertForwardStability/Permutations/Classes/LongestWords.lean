import SchubertForwardStability.Permutations.Statistics.LongestOrder
import SchubertForwardStability.Permutations.Classes.Boolean.BooleanSupport
import Mathlib.Tactic

/-! # Longest conjugation on adjacent words

Reversal relabels the adjacent letters by the reflected Coxeter diagram. It
carries bounded reduced words to bounded reduced words and preserves Booleanity.
-/

namespace FinitaryPerm

private theorem conjugate_swap {α : Type*} [DecidableEq α]
    (w : FinitaryPerm α) (a b : α) : w * swap a b * w⁻¹ = swap (w a) (w b) := by
  apply Subtype.ext
  change w.val * Equiv.swap a b * w.val⁻¹ = Equiv.swap (w a) (w b)
  rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right]

/-- Reversing the right endpoint gives the reflected adjacent letter. -/
theorem longestElement_next_letter {n : ℕ} {i : ℕ+} (hi : (i : ℕ) < n) :
    longestElement n (i + 1) = longestElement (n - 1) i := by
  apply PNat.eq
  rw [longestElement_apply_val n (i + 1) (by change (i : ℕ) + 1 ≤ n; omega),
    longestElement_apply_val (n - 1) i (by omega)]
  change n + 1 - ((i : ℕ) + 1) = n - 1 + 1 - (i : ℕ)
  have := i.pos
  omega

/-- Reversing the left endpoint gives the successor of the reflected letter. -/
theorem longestElement_left_letter {n : ℕ} {i : ℕ+} (hi : (i : ℕ) < n) :
    longestElement n i = longestElement (n - 1) i + 1 := by
  apply PNat.eq
  rw [longestElement_apply_val n i (by omega)]
  change n + 1 - (i : ℕ) = (longestElement (n - 1) i : ℕ) + 1
  rw [longestElement_apply_val (n - 1) i (by omega)]
  have := i.pos
  omega

/-- Longest conjugation reflects an adjacent transposition within its diagram. -/
theorem conjugate_simple_longest {n : ℕ} {i : ℕ+} (hi : (i : ℕ) < n) :
    longestElement n * simpleTransposition i * longestElement n =
      simpleTransposition (longestElement (n - 1) i) := by
  have hc := conjugate_swap (longestElement n) i (i + 1)
  rw [longestElement_inv, longestElement_next_letter hi, longestElement_left_letter hi] at hc
  exact hc.trans (Subtype.ext (Equiv.swap_comm _ _))

/-- Relabeling a bounded adjacent word represents its longest conjugate. -/
theorem wordProduct_conjugate_longest (n : ℕ) (word : List ℕ+)
    (hword : ∀ i ∈ word, (i : ℕ) < n) :
    wordProduct (word.map (longestElement (n - 1))) =
      longestElement n * wordProduct word * longestElement n := by
  induction word with
  | nil => simp
  | cons i word ih =>
    rw [List.map_cons, wordProduct_cons, wordProduct_cons,
      ←conjugate_simple_longest (hword i List.mem_cons_self),
      ih (fun j hj => hword j (List.mem_cons_of_mem i hj))]
    apply ext
    intro j
    simp only [mul_apply, longestElement_apply_twice]

/-- Longest conjugation transports every bounded reduced expression. -/
theorem IsReducedWordIn.conjugate_longest {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) {word : List ℕ+} (hword : IsReducedWordIn n w word) :
    IsReducedWordIn n (longestElement n * w * longestElement n)
      (word.map (longestElement (n - 1))) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [wordProduct_conjugate_longest n word hword.2, hword.1.1]
  · rw [List.length_map, hword.1.2, length_conjugate_longest hw]
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hb : (longestElement (n - 1) j : ℕ) ≤ n - 1 :=
      ((isSupported_longestElement (n - 1)).apply_le_iff j).mpr
      (Nat.le_sub_one_of_lt (hword.2 j hj))
    have hn : 0 < n := lt_trans j.pos (hword.2 j hj)
    change (longestElement (n - 1) j : ℕ) < n
    omega

private theorem boolean_conjugate {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (hb : IsBoolean w) :
    IsBoolean (longestElement n * w * longestElement n) := by
  obtain ⟨word, hword⟩ := exists_reducedWordIn w hw
  refine ⟨word.map (longestElement (n - 1)), (hword.conjugate_longest hw).1, ?_⟩
  exact (hb.reducedWord_nodup hword.1).map (longestElement (n - 1)).injective

/-- Ambient longest conjugation preserves the Boolean property. -/
theorem isBoolean_conjugate_longest {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) :
    IsBoolean (longestElement n * w * longestElement n) ↔ IsBoolean w := by
  constructor
  · intro h
    simpa only [conjugate_longest_twice] using boolean_conjugate hw.conjugate_longest h
  · exact boolean_conjugate hw

end FinitaryPerm
