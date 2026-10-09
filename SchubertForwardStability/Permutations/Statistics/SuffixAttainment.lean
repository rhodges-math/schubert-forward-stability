import SchubertForwardStability.Permutations.Statistics.SuffixAscent
import Mathlib.Data.Finset.Max

/-! # Attainment of a suffix count under ascent exchange

## Main results

A maximum-value position in a nonempty prefix is a record of that suffix. If the
prefix is below the next value, exchanging that maximum with the next value raises
the suffix count by one. This gives exact attainment for an increasing-tail pivot.

## Implementation notes

The maximum is selected in a finite set of positive positions. Injectivity makes
every comparison with a different maximum position strict.
-/

namespace FinitaryPerm

open scoped Classical

/-- A nonempty prefix has a position attaining its largest value. -/
theorem exists_prefix_max {w : FinitaryPerm ℕ+} {i r : ℕ+} (hi : i < r) :
    ∃ q : ℕ+, i ≤ q ∧ q < r ∧
      ∀ k : ℕ+, i ≤ k → k < r → w k ≤ w q := by
  let t := (positions (r : ℕ)).filter fun k => i ≤ k ∧ k < r
  have hmem : ∀ k : ℕ+, k ∈ t ↔ i ≤ k ∧ k < r := by
    intro k
    simp only [t, Finset.mem_filter, mem_positions]
    exact ⟨fun hk => hk.2, fun hk => ⟨le_of_lt hk.2, hk⟩⟩
  have ht : t.Nonempty := ⟨i, (hmem i).mpr ⟨le_rfl, hi⟩⟩
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image t w ht
  exact ⟨q, (hmem q).mp hq |>.1, (hmem q).mp hq |>.2,
    fun k hik hkr => hmax k ((hmem k).mpr ⟨hik, hkr⟩)⟩

/-- A smaller prefix has a maximum position giving a gap-free ascent and a suffix record. -/
theorem exists_max_prefix_ascent {w : FinitaryPerm ℕ+} {i r : ℕ+}
    (hi : i < r) (hp : ∀ k : ℕ+, i ≤ k → k < r → w k < w r) :
    ∃ q : ℕ+, i ≤ q ∧ GapFreeAscent w q r ∧ ¬IsSuffixNonRecord w i q := by
  obtain ⟨q, hiq, hqr, hmax⟩ := exists_prefix_max (w := w) hi
  refine ⟨q, hiq, ⟨hqr, hp q hiq hqr, ?_⟩, ?_⟩
  · intro j hqj hjr hj
    exact (not_lt_of_ge (hmax j (hiq.trans (le_of_lt hqj)) hjr)) hj.1
  · rintro ⟨k, hik, hkq, hv⟩
    exact (not_lt_of_ge (hmax k hik (hkq.trans hqr))) hv

/-- Exchanging the smaller prefix maximum attains a one-count increase. -/
theorem exists_ascent_count_attain {w : FinitaryPerm ℕ+} {i r : ℕ+}
    (hi : i < r) (hp : ∀ k : ℕ+, i ≤ k → k < r → w k < w r) :
    ∃ q : ℕ+, i ≤ q ∧ GapFreeAscent w q r ∧
      (w * swap q r).suffixNonRecordCount i = w.suffixNonRecordCount i + 1 := by
  obtain ⟨q, hiq, hq, hrecord⟩ := exists_max_prefix_ascent hi hp
  refine ⟨q, hiq, hq, ?_⟩
  rw [hq.count_eq_prefix_low hiq hp, ite_eq_right hrecord]

/-- The prefix below an exchanged start is exactly the prefix below the original pivot value. -/
theorem IncreasingTailPivot.prefix_below_iff {w : FinitaryPerm ℕ+} {i r s : ℕ+}
    (h : IncreasingTailPivot w r s) :
    (∀ k : ℕ+, i ≤ k → k < r → (w * swap r s) k < (w * swap r s) r) ↔
      ∀ k : ℕ+, i ≤ k → k < r → w k < w s := by
  constructor <;> intro hp k hik hkr
  · have hk := hp k hik hkr
    simpa only [mul_apply, swap_apply_left, swap_apply_of_ne (ne_of_lt hkr)
      (ne_of_lt (hkr.trans h.start_lt))] using hk
  · simpa only [mul_apply, swap_apply_left, swap_apply_of_ne (ne_of_lt hkr)
      (ne_of_lt (hkr.trans h.start_lt))] using hp k hik hkr

/-- Every gap-free exchange before a pivot is bounded by the original earlier suffix count. -/
theorem IncreasingTailPivot.exchange_count_le {w : FinitaryPerm ℕ+} {i q r s : ℕ+}
    (h : IncreasingTailPivot w r s) (hi : i < r)
    (hq : GapFreeAscent (w * swap r s) q r) :
    ((w * swap r s) * swap q r).suffixNonRecordCount i ≤ w.suffixNonRecordCount i := by
  have hbound := hq.count_le_prefix (i := i)
  rw [h.prefix_below_iff, ←h.count_before hi] at hbound
  exact hbound

/-- A smaller earlier prefix attains the original pivot suffix count after two exchanges. -/
theorem IncreasingTailPivot.exists_exchange_attain {w : FinitaryPerm ℕ+} {i r s : ℕ+}
    (h : IncreasingTailPivot w r s) (hi : i < r)
    (hp : ∀ k : ℕ+, i ≤ k → k < r → w k < w s) :
    ∃ q : ℕ+, i ≤ q ∧ GapFreeAscent (w * swap r s) q r ∧
      ((w * swap r s) * swap q r).suffixNonRecordCount i = w.suffixNonRecordCount i := by
  obtain ⟨q, hiq, hq, heq⟩ := exists_ascent_count_attain hi (h.prefix_below_iff.mpr hp)
  refine ⟨q, hiq, hq, ?_⟩
  rw [heq, h.count_before hi, ite_eq_left hp]

end FinitaryPerm
