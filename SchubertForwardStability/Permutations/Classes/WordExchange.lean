import SchubertForwardStability.Permutations.Classes.WordInversions
import SchubertForwardStability.Permutations.Statistics.ExchangeLength

/-! # Covers and deletion in reduced adjacent words

## Main results

An inversion-length cover obtained by a right transposition is the product of one
and only one reduced single-letter deletion of a displayed reduced expression.
-/

namespace FinitaryPerm

/-- A length-decreasing right transposition exchanges an inversion pair. -/
theorem exchange_cover_inversion {w : FinitaryPerm ℕ+} {q r : ℕ+}
    (hqr : q < r) (hl : (w * swap q r).length + 1 = w.length) :
    (q, r) ∈ w.inversionSet := by
  refine (mem_inversionSet _ _ _).mpr ⟨hqr, ?_⟩
  rcases lt_or_gt_of_ne (w.injective.ne hqr.ne) with ha | hd
  · have hb := length_exchange_ge hqr ha
    omega
  · exact hd

/-- Increasingly ordered transposition endpoints are determined by the permutation. -/
theorem swap_ordered_injective {a b q r : ℕ+} (hab : a < b) (hqr : q < r)
    (he : swap a b = swap q r) : a = q ∧ b = r := by
  have hm : Equiv.swap q r a ≠ a := by
    change swap q r a ≠ a
    rw [← he, swap_apply_left]
    exact hab.ne'
  rcases Equiv.eq_or_eq_of_swap_apply_ne_self hm with ha | ha
  · refine ⟨ha, ?_⟩
    have hv := congrArg (fun w : FinitaryPerm ℕ+ => w a) he
    simpa only [ha, swap_apply_left] using hv
  · have hv := congrArg (fun w : FinitaryPerm ℕ+ => w a) he
    simp only [ha, swap_apply_left, swap_apply_right] at hv
    exact False.elim ((not_lt_of_gt hqr) (by simpa only [ha, hv] using hab))

/-- Every decreasing transposition cover deletes a unique letter of a reduced word. -/
theorem exists_unique_cover_deletion {w : FinitaryPerm ℕ+} {word : List ℕ+}
    {q r : ℕ+} (hr : IsReducedWord w word) (hqr : q < r)
    (hl : (w * swap q r).length + 1 = w.length) :
    ∃! c : List ℕ+ × ℕ+ × List ℕ+,
      c ∈ wordCuts word ∧ IsReducedWord (w * swap q r) (c.1 ++ c.2.2) := by
  have hr' : IsReducedWord (wordProduct word) word := by
    rw [hr.1]
    exact hr
  have hp := exchange_cover_inversion hqr hl
  rw [← hr.1] at hp
  obtain ⟨c, ⟨hc, he⟩, hu⟩ := exists_unique_wordCutRoot hr' hp
  have hprod : wordProduct (c.1 ++ c.2.2) = w * swap q r := by
    have hd := wordCuts_deleted_product hc
    simpa only [hr.1, he] using hd
  refine ⟨c, ⟨hc, hprod, ?_⟩, ?_⟩
  · have hc' : (c.1 ++ c.2.2).length + 1 = word.length := wordCuts_deleted_length hc
    have hw := hr.2
    omega
  · intro d hd
    have hs : swap (wordCutRoot d).1 (wordCutRoot d).2 = swap q r := by
      apply mul_left_cancel (a := w)
      rw [← hr.1, ← wordCuts_deleted_product hd.1]
      simpa only [hr.1] using hd.2.1
    have he' : wordCutRoot d = (q, r) := by
      exact Prod.ext (swap_ordered_injective (wordCutRoot_lt hr' hd.1) hqr hs).1
        (swap_ordered_injective (wordCutRoot_lt hr' hd.1) hqr hs).2
    exact hu d ⟨hd.1, he'⟩

end FinitaryPerm
