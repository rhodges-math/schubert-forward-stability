import SchubertForwardStability.Permutations.Classes.ReducedWords
import SchubertForwardStability.Permutations.Statistics.Descents

/-! # Length changes at adjacent positions

## Main results

Right multiplication by an adjacent transposition lowers inversion length by one
at a descent and raises it by one at an ascent.

## Implementation notes

The finite inversion-count theorem is transported through positive reindexing.
The ambient bound includes both the permutation support and the adjacent pair.
-/

namespace FinitaryPerm

open Schubert.FinPermutation

/-- Finite extension intertwines a right adjacent swap with its positive transposition. -/
theorem ofFinite_rightAdjacentSwap {n : ℕ} (g : Schubert.FinPermutation n)
    (a : AdjacentPosition n) :
    ofFinite n (g.rightAdjacentSwap a) = ofFinite n g * simpleTransposition (adjacentLetter a) :=
  (ofFinite_mul n g (adjacentTransposition a)).trans
    (congrArg (fun v => ofFinite n g * v) (ofFinite_adjacent a))

/-- A finite adjacent descent is its positive-index extension's adjacent descent. -/
theorem hasDescent_ofFinite_adjacent {n : ℕ} (g : Schubert.FinPermutation n)
    (a : AdjacentPosition n) :
    FinitaryPerm.HasDescent (ofFinite n g) (adjacentLetter a) ↔ g.HasDescent a.left := by
  rw [hasDescent_left_iff]
  change ofFinite n g (positiveIndex n a.right).val <
    ofFinite n g (positiveIndex n a.left).val ↔ _
  rw [ofFinite_apply_position, ofFinite_apply_position, positiveIndex_lt_iff]

private theorem finite_simple_pair (w : FinitaryPerm ℕ+) (i : ℕ+) :
    ∃ (n : ℕ) (g : Schubert.FinPermutation n) (a : AdjacentPosition n),
      ofFinite n g = w ∧ adjacentLetter a = i := by
  let n := max w.forwardStability ((i : ℕ) + 1)
  have hw : IsSupported n w := w.isSupported_forwardStability.mono (le_max_left _ _)
  have hi : (i : ℕ) < n := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  let a := AdjacentPosition.endingAt ⟨(i : ℕ), hi⟩ i.pos
  refine ⟨n, toFinite n w hw, a, ofFinite_toFinite n w hw, ?_⟩
  apply PNat.eq
  change (i : ℕ) - 1 + 1 = (i : ℕ)
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt i.pos)

/-- An adjacent right descent decreases inversion length by exactly one. -/
theorem length_mul_simple_of_descent (w : FinitaryPerm ℕ+) (i : ℕ+)
    (hi : FinitaryPerm.HasDescent w i) :
    (w * simpleTransposition i).length + 1 = w.length := by
  obtain ⟨n, g, a, hg, ha⟩ := finite_simple_pair w i
  have hd : g.HasDescent a.left := (hasDescent_ofFinite_adjacent g a).mp (by
    simpa only [hg, ha] using hi)
  have h := Schubert.FinPermutation.length_rightAdjacentSwap_of_descent g a hd
  change finiteLength (g.rightAdjacentSwap a) + 1 = finiteLength g at h
  rw [← length_ofFinite n (g.rightAdjacentSwap a), ofFinite_rightAdjacentSwap, hg, ha] at h
  simpa only [← length_ofFinite n, hg] using h

/-- An adjacent right ascent increases inversion length by exactly one. -/
theorem length_mul_simple_of_ascent (w : FinitaryPerm ℕ+) (i : ℕ+)
    (hi : w i < w (i + 1)) : w.length + 1 = (w * simpleTransposition i).length := by
  obtain ⟨n, g, a, hg, ha⟩ := finite_simple_pair w i
  have hv : g a.left < g a.right := by
    apply (positiveIndex_lt_iff n _ _).mp
    rw [← ofFinite_apply_position, ← ofFinite_apply_position]
    change ofFinite n g (adjacentLetter a) < ofFinite n g (adjacentLetter a + 1)
    simpa only [hg, ha] using hi
  have h := Schubert.FinPermutation.length_rightAdjacentSwap_of_ascent g a hv
  change finiteLength g + 1 = finiteLength (g.rightAdjacentSwap a) at h
  rw [← length_ofFinite n (g.rightAdjacentSwap a), ofFinite_rightAdjacentSwap, hg, ha] at h
  simpa only [← length_ofFinite n, hg] using h

/-- An adjacent transposition has exactly one inversion. -/
@[simp] theorem length_simpleTransposition (i : ℕ+) : (simpleTransposition i).length = 1 := by
  have h := length_mul_simple_of_ascent 1 i (Nat.lt_succ_self (i : ℕ))
  simpa only [length_one, one_mul, zero_add] using h.symm

end FinitaryPerm
