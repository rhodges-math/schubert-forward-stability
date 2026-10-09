import SchubertForwardStability.Permutations.Classes.Intervals.WordCuts
import SchubertForwardStability.Permutations.Statistics.AdjacentLength

/-! # Suffix-conjugated roots of adjacent words

## Main definitions

* `wordCutRoot`: the two inverse suffix positions of a selected adjacent letter.

## Main results

The deleted product differs by the transposition of these positions. For a reduced
word, each suffix root is positive and the tail is itself reduced.
-/

namespace FinitaryPerm

/-- Inverse-suffix positions of the two adjacent values at a selected word letter. -/
def wordCutRoot (c : List ℕ+ × ℕ+ × List ℕ+) : ℕ+ × ℕ+ :=
  ((wordProduct c.2.2)⁻¹ c.2.1, (wordProduct c.2.2)⁻¹ (c.2.1 + 1))

/-- Conjugating a transposition pulls its two positions back through the permutation. -/
theorem inv_mul_swap_mul (w : FinitaryPerm ℕ+) (a b : ℕ+) :
    w⁻¹ * swap a b * w = swap (w⁻¹ a) (w⁻¹ b) := by
  apply Subtype.ext
  exact Equiv.symm_trans_swap_trans a b w.val.symm

/-- Restoring a selected letter multiplies its deleted product by the suffix root swap. -/
theorem wordCuts_product {word pre : List ℕ+} {i : ℕ+} {suf : List ℕ+}
    (hc : (pre, i, suf) ∈ wordCuts word) :
    wordProduct word = wordProduct (pre ++ suf) *
      swap (wordCutRoot (pre, i, suf)).1 (wordCutRoot (pre, i, suf)).2 := by
  rw [← (mem_wordCuts word pre i suf).mp hc, wordProduct_append, wordProduct_cons,
    wordProduct_append]
  change wordProduct pre * (simpleTransposition i * wordProduct suf) =
    (wordProduct pre * wordProduct suf) *
      swap ((wordProduct suf)⁻¹ i) ((wordProduct suf)⁻¹ (i + 1))
  rw [← inv_mul_swap_mul]
  change wordProduct pre * (swap i (i + 1) * wordProduct suf) = _
  simp only [mul_assoc, mul_inv_cancel_left]

/-- Deleting the selected letter multiplies the full product by the same root swap. -/
theorem wordCuts_deleted_product {word pre : List ℕ+} {i : ℕ+} {suf : List ℕ+}
    (hc : (pre, i, suf) ∈ wordCuts word) :
    wordProduct (pre ++ suf) = wordProduct word *
      swap (wordCutRoot (pre, i, suf)).1 (wordCutRoot (pre, i, suf)).2 := by
  let t := swap (wordCutRoot (pre, i, suf)).1 (wordCutRoot (pre, i, suf)).2
  have ht : t * t = 1 := by
    exact (congrArg (fun s => t * s) (swap_inv _ _).symm).trans (mul_inv_cancel t)
  rw [wordCuts_product hc, mul_assoc, ht, mul_one]

private theorem length_inverse_simple (w : FinitaryPerm ℕ+) (i : ℕ+) :
    (w⁻¹ * simpleTransposition i).length = (simpleTransposition i * w).length := by
  calc
    (w⁻¹ * simpleTransposition i).length = ((simpleTransposition i * w)⁻¹).length := by
      simp only [mul_inv_rev, simpleTransposition, swap_inv]
    _ = (simpleTransposition i * w).length := length_inv _

/-- Left multiplication by an adjacent transposition increases length by at most one. -/
theorem length_simple_mul_le (w : FinitaryPerm ℕ+) (i : ℕ+) :
    (simpleTransposition i * w).length ≤ w.length + 1 := by
  have hn : i ≠ i + 1 := (show i < i + 1 from Nat.lt_succ_self (i : ℕ)).ne
  rcases lt_or_gt_of_ne ((w⁻¹).injective.ne hn) with ha | hd
  · have h := length_mul_simple_of_ascent w⁻¹ i ha
    rw [length_inverse_simple, length_inv] at h
    omega
  · have h := length_mul_simple_of_descent w⁻¹ i hd
    rw [length_inverse_simple, length_inv] at h
    omega

/-- The inversion length of a displayed adjacent word is at most its displayed length. -/
theorem wordProduct_length_le (word : List ℕ+) : (wordProduct word).length ≤ word.length := by
  induction word with
  | nil => simp only [wordProduct_nil, length_one, List.length_nil, le_refl]
  | cons i word ih =>
    rw [wordProduct_cons, List.length_cons]
    exact (length_simple_mul_le _ _).trans (Nat.add_le_add_right ih 1)

/-- The tail of any reduced adjacent expression is itself reduced. -/
theorem isReducedWord_tail {w : FinitaryPerm ℕ+} {i : ℕ+} {word : List ℕ+}
    (h : IsReducedWord w (i :: word)) : IsReducedWord (wordProduct word) word := by
  refine ⟨rfl, ?_⟩
  have hf : (simpleTransposition i * wordProduct word).length = word.length + 1 := by
    rw [← wordProduct_cons, h.1]
    exact h.2.symm
  have hb := length_simple_mul_le (wordProduct word) i
  have ht := wordProduct_length_le word
  omega

/-- The leftmost root of a reduced expression has its two suffix positions in increasing order. -/
theorem reduced_prefix_root_lt {w : FinitaryPerm ℕ+} {i : ℕ+} {word : List ℕ+}
    (h : IsReducedWord w (i :: word)) :
    (wordProduct word)⁻¹ i < (wordProduct word)⁻¹ (i + 1) := by
  have hn : i ≠ i + 1 := (show i < i + 1 from Nat.lt_succ_self (i : ℕ)).ne
  rcases lt_or_gt_of_ne (((wordProduct word)⁻¹).injective.ne hn) with ha | hd
  · exact ha
  · have hl := length_mul_simple_of_descent (wordProduct word)⁻¹ i hd
    rw [length_inverse_simple, length_inv, ← wordProduct_cons, h.1] at hl
    have ht := (isReducedWord_tail h).2
    have hf := h.2
    simp only [List.length_cons] at hf
    omega

/-- Every suffix-conjugated root of a reduced word is positive. -/
theorem wordCutRoot_lt {word : List ℕ+} {c : List ℕ+ × ℕ+ × List ℕ+}
    (hr : IsReducedWord (wordProduct word) word) (hc : c ∈ wordCuts word) :
    (wordCutRoot c).1 < (wordCutRoot c).2 := by
  induction word generalizing c with
  | nil => exact False.elim (List.not_mem_nil hc)
  | cons i word ih =>
    rcases List.mem_cons.mp hc with he | hm
    · cases he
      exact reduced_prefix_root_lt hr
    · obtain ⟨d, hd, he⟩ := List.mem_map.mp hm
      subst c
      exact ih (c := d) (isReducedWord_tail hr) hd

end FinitaryPerm
