import SchubertForwardStability.Permutations.Statistics.SuffixExchange

/-! # Suffix counts under a gap-free ascent exchange

## Main definitions

* `GapFreeAscent`: an ascent with no intervening value strictly between its endpoint values.

## Main results

Exchanging a gap-free ascent does not increase any suffix count beginning after its
left position. For an earlier suffix, the count can increase by one only when its
entire prefix before the right position is below the right endpoint value.

## Implementation notes

Membership away from the exchanged positions is compared directly. The two exceptional
membership contributions are then restored to the common twice-erased finite set.
-/

namespace FinitaryPerm

open scoped Classical

/-- An ascent whose open position interval contains no value between its endpoint values. -/
structure GapFreeAscent (w : FinitaryPerm ℕ+) (q r : ℕ+) : Prop where
  /-- The left endpoint occurs before the right endpoint. -/
  left_lt : q < r
  /-- The endpoint values form an ascent. -/
  value_lt : w q < w r
  /-- No intervening position has a value strictly between the endpoint values. -/
  gap : ∀ j : ℕ+, q < j → j < r → ¬(w q < w j ∧ w j < w r)

/-- A suffix non-record is exactly a failure of strict increase from its earlier prefix. -/
theorem suffixNonRecord_iff_not_prefix {w : FinitaryPerm ℕ+} {i j : ℕ+} :
    IsSuffixNonRecord w i j ↔ ¬∀ k : ℕ+, i ≤ k → k < j → w k < w j := by
  constructor
  · rintro ⟨k, hik, hkj, hv⟩ hall
    exact (not_lt_of_gt (hall k hik hkj)) hv
  · intro hn
    push Not at hn
    obtain ⟨k, hik, hkj, hv⟩ := hn
    have hne : w k ≠ w j := fun he => (ne_of_lt hkj) (w.injective he)
    exact ⟨k, hik, hkj, lt_of_le_of_ne hv (Ne.symm hne)⟩

/-- A suffix beginning after the left endpoint can only lose non-records under the exchange. -/
theorem GapFreeAscent.suffix_subset_earlier {w : FinitaryPerm ℕ+} {i q r : ℕ+}
    (h : GapFreeAscent w q r) (hqi : q < i) :
    (w * swap q r).suffixNonRecords i ⊆ w.suffixNonRecords i := by
  intro j hj
  obtain ⟨k, hik, hkj, hv⟩ := (mem_suffixNonRecords _ i j).mp hj
  have hqk : q < k := lt_of_lt_of_le hqi hik
  have hqj : q < j := hqk.trans hkj
  apply (mem_suffixNonRecords w i j).mpr
  by_cases hjr : j = r
  · subst j
    rw [mul_apply, swap_apply_right, mul_apply,
      swap_apply_of_ne (ne_of_gt hqk) (ne_of_lt hkj)] at hv
    have hn : ¬w k < w r := fun hk => h.gap k hqk hkj ⟨hv, hk⟩
    have hne : w r ≠ w k := fun he => (ne_of_gt hkj) (w.injective he)
    exact ⟨k, hik, hkj, lt_of_le_of_ne (le_of_not_gt hn) hne⟩
  · rw [mul_apply, swap_apply_of_ne (ne_of_gt hqj) hjr] at hv
    by_cases hkr : k = r
    · subst k
      rw [mul_apply, swap_apply_right] at hv
      exact ⟨r, hik, hkj, hv.trans h.value_lt⟩
    · rw [mul_apply, swap_apply_of_ne (ne_of_gt hqk) hkr] at hv
      exact ⟨k, hik, hkj, hv⟩

/-- The count cannot increase when the suffix begins after the left endpoint. -/
theorem GapFreeAscent.count_le_earlier {w : FinitaryPerm ℕ+} {i q r : ℕ+}
    (h : GapFreeAscent w q r) (hqi : q < i) :
    (w * swap q r).suffixNonRecordCount i ≤ w.suffixNonRecordCount i :=
  Finset.card_le_card (h.suffix_subset_earlier hqi)

/-- Suffix membership between gap-free endpoints is unchanged for an earlier suffix. -/
theorem GapFreeAscent.suffix_between {w : FinitaryPerm ℕ+} {i j q r : ℕ+}
    (h : GapFreeAscent w q r) (hiq : i ≤ q) (hqj : q < j) (hjr : j < r) :
    IsSuffixNonRecord (w * swap q r) i j ↔ IsSuffixNonRecord w i j := by
  constructor
  · rintro ⟨k, hik, hkj, hv⟩
    rw [mul_apply, swap_apply_of_ne (ne_of_gt hqj) (ne_of_lt hjr)] at hv
    by_cases hkq : k = q
    · subst k
      rw [mul_apply, swap_apply_left] at hv
      have hn : ¬w q < w j := fun hj => h.gap j hqj hjr ⟨hj, hv⟩
      have hne : w j ≠ w q := fun he => (ne_of_gt hqj) (w.injective he)
      exact ⟨q, hiq, hqj, lt_of_le_of_ne (le_of_not_gt hn) hne⟩
    · rw [mul_apply, swap_apply_of_ne hkq (ne_of_lt (hkj.trans hjr))] at hv
      exact ⟨k, hik, hkj, hv⟩
  · rintro ⟨k, hik, hkj, hv⟩
    refine ⟨k, hik, hkj, ?_⟩
    rw [mul_apply, swap_apply_of_ne (ne_of_gt hqj) (ne_of_lt hjr)]
    by_cases hkq : k = q
    · subst k
      rw [mul_apply, swap_apply_left]
      exact hv.trans h.value_lt
    · simpa only [mul_apply, swap_apply_of_ne hkq (ne_of_lt (hkj.trans hjr))] using hv

/-- Suffix membership is unchanged away from the two gap-free endpoints. -/
theorem GapFreeAscent.suffix_away {w : FinitaryPerm ℕ+} {i j q r : ℕ+}
    (h : GapFreeAscent w q r) (hiq : i ≤ q) (hjq : j ≠ q) (hjr : j ≠ r) :
    IsSuffixNonRecord (w * swap q r) i j ↔ IsSuffixNonRecord w i j := by
  rcases lt_or_gt_of_ne hjq with hjq | hqj
  · exact suffixNonRecord_swap_after hjq (hjq.trans h.left_lt)
  · rcases lt_or_gt_of_ne hjr with hjr | hrj
    · exact h.suffix_between hiq hqj hjr
    · exact suffixNonRecord_swap_before hiq (hiq.trans (le_of_lt h.left_lt))
        hqj hrj

/-- The exchanged right endpoint is a non-record for every suffix containing both endpoints. -/
theorem GapFreeAscent.exchanged_right {w : FinitaryPerm ℕ+} {i q r : ℕ+}
    (h : GapFreeAscent w q r) (hiq : i ≤ q) :
    IsSuffixNonRecord (w * swap q r) i r := by
  refine ⟨q, hiq, h.left_lt, ?_⟩
  simpa only [mul_apply, swap_apply_right, swap_apply_left] using h.value_lt

/-- Any non-record at the exchanged left endpoint was already a non-record there. -/
theorem GapFreeAscent.exchanged_left_imp {w : FinitaryPerm ℕ+} {i q r : ℕ+}
    (h : GapFreeAscent w q r) :
    IsSuffixNonRecord (w * swap q r) i q → IsSuffixNonRecord w i q := by
  rintro ⟨k, hik, hkq, hv⟩
  rw [mul_apply, swap_apply_left, mul_apply,
    swap_apply_of_ne (ne_of_lt hkq) (ne_of_lt (hkq.trans h.left_lt))] at hv
  exact ⟨k, hik, hkq, h.value_lt.trans hv⟩

/-- The suffix sets agree after removing the gap-free endpoints. -/
theorem GapFreeAscent.erased_suffix_sets {w : FinitaryPerm ℕ+} {i q r : ℕ+}
    (h : GapFreeAscent w q r) (hiq : i ≤ q) :
    (((w * swap q r).suffixNonRecords i).erase q).erase r =
      ((w.suffixNonRecords i).erase q).erase r := by
  ext j
  simp only [Finset.mem_erase, mem_suffixNonRecords]
  constructor
  · rintro ⟨hjr, hjq, hj⟩
    exact ⟨hjr, hjq, (h.suffix_away hiq hjq hjr).mp hj⟩
  · rintro ⟨hjr, hjq, hj⟩
    exact ⟨hjr, hjq, (h.suffix_away hiq hjq hjr).mpr hj⟩

private theorem card_erase_indicator (t : Finset ℕ+) (a : ℕ+) :
    (t.erase a).card + (if a ∈ t then 1 else 0) = t.card := by
  by_cases ha : a ∈ t
  · simpa only [ha, ite_true] using Finset.card_erase_add_one ha
  · simp only [Finset.erase_eq_of_notMem ha, ha, ite_false, Nat.add_zero]

private theorem card_two_erase (t : Finset ℕ+) {q r : ℕ+} (hqr : q ≠ r) :
    ((t.erase q).erase r).card + (if q ∈ t then 1 else 0) +
      (if r ∈ t then 1 else 0) = t.card := by
  have hq := card_erase_indicator t q
  have hr := card_erase_indicator (t.erase q) r
  have hrq : r ≠ q := Ne.symm hqr
  have hmem : r ∈ t.erase q ↔ r ∈ t :=
    ⟨fun hj => (Finset.mem_erase.mp hj).2, fun hj => Finset.mem_erase.mpr ⟨hrq, hj⟩⟩
  simp only [hmem] at hr
  omega

/-- Counts differ only by the membership contributions at the two exchanged endpoints. -/
theorem GapFreeAscent.count_balance {w : FinitaryPerm ℕ+} {i q r : ℕ+}
    (h : GapFreeAscent w q r) (hiq : i ≤ q) :
    (w * swap q r).suffixNonRecordCount i +
        (if IsSuffixNonRecord w i q then 1 else 0) +
        (if IsSuffixNonRecord w i r then 1 else 0) =
      w.suffixNonRecordCount i +
        (if IsSuffixNonRecord (w * swap q r) i q then 1 else 0) + 1 := by
  have hw := card_two_erase (w.suffixNonRecords i) (ne_of_lt h.left_lt)
  have hz := card_two_erase ((w * swap q r).suffixNonRecords i) (ne_of_lt h.left_lt)
  rw [h.erased_suffix_sets hiq] at hz
  have hr : r ∈ (w * swap q r).suffixNonRecords i :=
    (mem_suffixNonRecords _ i r).mpr (h.exchanged_right hiq)
  simp only [hr, ite_true, mem_suffixNonRecords] at hw hz
  rw [suffixNonRecordCount, suffixNonRecordCount]
  omega

/-- A larger prefix value prevents any increase of the suffix count under the exchange. -/
theorem GapFreeAscent.count_le_prefix_high {w : FinitaryPerm ℕ+} {i q r : ℕ+}
    (h : GapFreeAscent w q r) (hiq : i ≤ q)
    (hp : ∃ k : ℕ+, i ≤ k ∧ k < r ∧ w r < w k) :
    (w * swap q r).suffixNonRecordCount i ≤ w.suffixNonRecordCount i := by
  have hr : IsSuffixNonRecord w i r := hp
  have hleft : (if IsSuffixNonRecord (w * swap q r) i q then 1 else 0 : ℕ) ≤
      if IsSuffixNonRecord w i q then 1 else 0 := by
    by_cases hz : IsSuffixNonRecord (w * swap q r) i q
    · rw [ite_eq_left hz, ite_eq_left (h.exchanged_left_imp hz)]
    · rw [ite_eq_right hz]
      exact Nat.zero_le _
  have hb := h.count_balance hiq
  rw [ite_eq_left hr] at hb
  omega

/-- A wholly smaller prefix gives the exact increase determined by the left record status. -/
theorem GapFreeAscent.count_eq_prefix_low {w : FinitaryPerm ℕ+} {i q r : ℕ+}
    (h : GapFreeAscent w q r) (hiq : i ≤ q)
    (hp : ∀ k : ℕ+, i ≤ k → k < r → w k < w r) :
    (w * swap q r).suffixNonRecordCount i = w.suffixNonRecordCount i +
      if IsSuffixNonRecord w i q then 0 else 1 := by
  have hr : ¬IsSuffixNonRecord w i r := by
    rw [suffixNonRecord_iff_not_prefix]
    exact not_not_intro hp
  have hq : ¬IsSuffixNonRecord (w * swap q r) i q := by
    rintro ⟨k, hik, hkq, hv⟩
    rw [mul_apply, swap_apply_left, mul_apply,
      swap_apply_of_ne (ne_of_lt hkq) (ne_of_lt (hkq.trans h.left_lt))] at hv
    exact (not_lt_of_gt (hp k hik (hkq.trans h.left_lt))) hv
  have hb := h.count_balance hiq
  rw [ite_eq_right hr, ite_eq_right hq] at hb
  by_cases hleft : IsSuffixNonRecord w i q
  · rw [ite_eq_left hleft] at hb ⊢
    omega
  · rw [ite_eq_right hleft] at hb ⊢
    omega

/-- A gap-free ascent increases the count by at most the smaller-prefix indicator. -/
theorem GapFreeAscent.count_le_prefix {w : FinitaryPerm ℕ+} {i q r : ℕ+}
    (h : GapFreeAscent w q r) :
    (w * swap q r).suffixNonRecordCount i ≤ w.suffixNonRecordCount i +
      if (∀ k : ℕ+, i ≤ k → k < r → w k < w r) then 1 else 0 := by
  by_cases hqi : q < i
  · exact (h.count_le_earlier hqi).trans (Nat.le_add_right _ _)
  · have hiq : i ≤ q := le_of_not_gt hqi
    by_cases hp : ∀ k : ℕ+, i ≤ k → k < r → w k < w r
    · rw [ite_eq_left hp, h.count_eq_prefix_low hiq hp]
      by_cases hleft : IsSuffixNonRecord w i q
      · rw [ite_eq_left hleft]
        omega
      · rw [ite_eq_right hleft]
    · rw [ite_eq_right hp, Nat.add_zero]
      exact h.count_le_prefix_high hiq (suffixNonRecord_iff_not_prefix.mpr hp)

end FinitaryPerm
