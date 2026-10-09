import SchubertForwardStability.Permutations.Statistics.SuffixPivot
import SchubertForwardStability.Permutations.Statistics.ExchangeLength
import SchubertForwardStability.Permutations.Classes.WordExchange

/-! # Right covers at an increasing-tail pivot

## Main definitions

* `transitionPositions`: the finite set of gap-free left endpoints before a fixed endpoint.

## Main results

The pivot exchange lowers inversion length by one. In the exchanged permutation,
the pivot is the unique right endpoint of a cover starting at the last-descent position.
-/

namespace FinitaryPerm

open scoped Classical

/-- Gap-free ascent starts in the finite initial interval before a fixed right endpoint. -/
noncomputable def transitionPositions (v : FinitaryPerm ℕ+) (r : ℕ+) : Finset ℕ+ :=
  (positions (r : ℕ)).filter fun q => GapFreeAscent v q r

/-- Membership in the finite left-endpoint set is exactly the gap-free ascent condition. -/
theorem mem_transitionPositions (v : FinitaryPerm ℕ+) (q r : ℕ+) :
    q ∈ transitionPositions v r ↔ GapFreeAscent v q r := by
  simp only [transitionPositions, Finset.mem_filter, mem_positions]
  exact ⟨And.right, fun h => ⟨le_of_lt h.left_lt, h⟩⟩

/-- Each finite left-endpoint term is an inversion-length cover. -/
theorem transitionPositions_length {v : FinitaryPerm ℕ+} {q r : ℕ+}
    (hq : q ∈ transitionPositions v r) : (v * swap q r).length = v.length + 1 :=
  ((mem_transitionPositions _ _ _).mp hq).length_exchange

/-- The finite left endpoints produce pairwise distinct transposition outputs. -/
theorem transitionOutput_injective {v : FinitaryPerm ℕ+} {q t r : ℕ+}
    (hq : q ∈ transitionPositions v r) (ht : t ∈ transitionPositions v r)
    (he : v * swap q r = v * swap t r) : q = t := by
  exact (swap_ordered_injective ((mem_transitionPositions _ _ _).mp hq).left_lt
    ((mem_transitionPositions _ _ _).mp ht).left_lt (mul_left_cancel he)).1

/-- The pivot exchange creates a gap-free ascent between its exchanged endpoints. -/
theorem IncreasingTailPivot.swapped_gap {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) : GapFreeAscent (w * swap r s) r s := by
  refine ⟨h.start_lt, ?_, ?_⟩
  · simpa only [mul_apply, swap_apply_left, swap_apply_right] using h.value_lt
  · intro k hrk hks hv
    have hk := h.tail_strictMono hrk h.start_lt hks
    rw [mul_apply, swap_apply_left, mul_apply,
      swap_apply_of_ne (ne_of_gt hrk) (ne_of_lt hks)] at hv
    exact (not_lt_of_gt hk) hv.1

/-- In the exchanged permutation, only the pivot is a gap-free right ascent endpoint. -/
theorem IncreasingTailPivot.swapped_gap_iff {w : FinitaryPerm ℕ+} {r s k : ℕ+}
    (h : IncreasingTailPivot w r s) (hrk : r < k) :
    GapFreeAscent (w * swap r s) r k ↔ k = s := by
  constructor
  · intro hg
    rcases lt_trichotomy k s with hks | he | hsk
    · have hv := hg.value_lt
      rw [mul_apply, swap_apply_left, mul_apply,
        swap_apply_of_ne (ne_of_gt hrk) (ne_of_lt hks)] at hv
      exact False.elim ((not_lt_of_gt (h.tail_strictMono hrk h.start_lt hks)) hv)
    · exact he
    · apply False.elim
      apply hg.gap s h.start_lt hsk
      simp only [mul_apply, swap_apply_left, swap_apply_right,
        swap_apply_of_ne (ne_of_gt hrk) (ne_of_gt hsk)]
      exact ⟨h.value_lt, h.above_lt k hsk⟩
  · intro he
    subst k
    exact h.swapped_gap

/-- Exchanging an increasing-tail pivot lowers the inversion length by one. -/
theorem IncreasingTailPivot.swapped_length {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) : w.length = (w * swap r s).length + 1 := by
  have hs : (swap r s : FinitaryPerm ℕ+) * swap r s = 1 := by
    simpa only [swap_inv] using mul_inv_cancel (swap r s)
  simpa only [mul_assoc, hs, mul_one] using h.swapped_gap.length_exchange

/-- The pivot is the unique right endpoint of an inversion-length cover at the start. -/
theorem IncreasingTailPivot.swapped_cover_iff {w : FinitaryPerm ℕ+} {r s k : ℕ+}
    (h : IncreasingTailPivot w r s) (hrk : r < k) :
    ((w * swap r s) * swap r k).length = (w * swap r s).length + 1 ↔ k = s := by
  exact (length_exchange_cover_iff hrk).trans (h.swapped_gap_iff hrk)

end FinitaryPerm
