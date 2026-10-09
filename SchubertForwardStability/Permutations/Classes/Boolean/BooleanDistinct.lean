import SchubertForwardStability.Permutations.Classes.Boolean.BooleanSupport
import SchubertForwardStability.Permutations.Statistics.AdjacentLength

/-! # Reducedness of words with distinct generators

A new generator cannot lower length: a shorter reduced expression, prepended with
the new generator, would give a reduced expression of the old permutation with
a different generator support. Thus every distinct-generator word is reduced.
-/

namespace FinitaryPerm

/-- Left multiplication by a positive adjacent transposition changes length by one. -/
theorem length_simple_mul_cases (w : FinitaryPerm ℕ+) (i : ℕ+) :
    w.length + 1 = (simpleTransposition i * w).length ∨
      (simpleTransposition i * w).length + 1 = w.length := by
  have hinv : (w⁻¹ * simpleTransposition i).length =
      (simpleTransposition i * w).length := by
    calc
      _ = ((simpleTransposition i * w)⁻¹).length := by
        simp only [mul_inv_rev, simpleTransposition, swap_inv]
      _ = _ := length_inv _
  have hne : i ≠ i + 1 := (show i < i + 1 from Nat.lt_succ_self (i : ℕ)).ne
  rcases lt_or_gt_of_ne ((w⁻¹).injective.ne hne) with ha | hd
  · have h := length_mul_simple_of_ascent w⁻¹ i ha
    rw [hinv, length_inv] at h
    exact Or.inl h
  · have h := length_mul_simple_of_descent w⁻¹ i hd
    rw [hinv, length_inv] at h
    exact Or.inr h

/-- A positive adjacent word with no repeated generator is a reduced expression. -/
theorem isReducedWord_of_nodup (word : List ℕ+) (hN : word.Nodup) :
    IsReducedWord (wordProduct word) word := by
  induction word with
  | nil => exact (isReducedWordIn_one 0).1
  | cons i word ih =>
    obtain ⟨hi, ht⟩ := List.nodup_cons.mp hN
    have hr := ih ht
    rcases length_simple_mul_cases (wordProduct word) i with ha | hd
    · refine ⟨rfl, ?_⟩
      rw [wordProduct_cons, List.length_cons]
      exact (congrArg (fun n => n + 1) hr.2).trans ha
    · let v := simpleTransposition i * wordProduct word
      obtain ⟨red, hred⟩ := exists_reducedWordIn v v.isSupported_forwardStability
      have hii : simpleTransposition i * simpleTransposition i = 1 := by
        simpa only [simpleTransposition, swap_inv] using inv_mul_cancel (simpleTransposition i)
      have hnew : IsReducedWord (wordProduct word) (i :: red) := by
        constructor
        · rw [wordProduct_cons, hred.1.1]
          change simpleTransposition i * (simpleTransposition i * wordProduct word) = _
          rw [← mul_assoc, hii, one_mul]
        · calc
            (i :: red).length = red.length + 1 := rfl
            _ = v.length + 1 := congrArg (fun n => n + 1) hred.1.2
            _ = (wordProduct word).length := hd
      have hs := reducedWord_toFinset_eq (wordProduct word) word (i :: red) hr hnew
      have hm : i ∈ word.toFinset := by rw [hs]; simp
      exact (hi (List.mem_toFinset.mp hm)).elim

/-- The permutation represented by a distinct-generator word is Boolean. -/
theorem isBoolean_wordProduct_of_nodup (word : List ℕ+) (hN : word.Nodup) :
    IsBoolean (wordProduct word) := ⟨word, isReducedWord_of_nodup word hN, hN⟩

end FinitaryPerm
