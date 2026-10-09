import SchubertForwardStability.Permutations.Statistics.SuffixExtrema

/-! # Earlier larger values in two increasing blocks

## Main results

For two increasing blocks, an earlier larger value exists precisely when the position
lies in the second block and its value is below the maximum of the first block.
The non-record interval gives exact cardinality and intrinsic tail formulas. The first
block's maximum bounds support, with equality when it exceeds the block boundary.
-/

namespace FinitaryPerm

open scoped Classical

/-- In two increasing blocks, the first block's final value determines every non-record. -/
theorem twoBlock_nonRecord_iff {w : ℕ+ → ℕ+} {k j : ℕ+}
    (hl : StrictMonoOn w {i : ℕ+ | i ≤ k})
    (hr : StrictMonoOn w {i : ℕ+ | k < i}) :
    (∃ i : ℕ+, i < j ∧ w j < w i) ↔ k < j ∧ w j < w k := by
  constructor
  · rintro ⟨i, hij, hv⟩
    have hkj : k < j := by
      by_contra hn
      have hjk : j ≤ k := le_of_not_gt hn
      exact (not_lt_of_gt (hl (hij.le.trans hjk) hjk hij)) hv
    refine ⟨hkj, ?_⟩
    by_cases hik : i ≤ k
    · have hwik : w i ≤ w k := by
        rcases lt_or_eq_of_le hik with hik | rfl
        · exact (hl hik.le (show k ≤ k from le_rfl) hik).le
        · exact le_rfl
      exact hv.trans_le hwik
    · exact False.elim ((not_lt_of_gt (hr (lt_of_not_ge hik) hkj hij)) hv)
  · rintro ⟨hkj, hv⟩
    exact ⟨k, hkj, hv⟩

/-- A fixed tail makes the non-record positions the interval after the first block. -/
theorem twoBlock_nonRecord_interval_iff {w : ℕ+ → ℕ+} {k M j : ℕ+}
    (hl : StrictMonoOn w {i : ℕ+ | i ≤ k})
    (hr : StrictMonoOn w {i : ℕ+ | k < i}) (hinj : Function.Injective w)
    (hkM : k ≤ M) (hmax : w k = M) (hfix : ∀ i : ℕ+, M < i → w i = i) :
    (∃ i : ℕ+, i < j ∧ w j < w i) ↔ k < j ∧ j ≤ M := by
  rw [twoBlock_nonRecord_iff hl hr]
  constructor
  · rintro ⟨hkj, hv⟩
    refine ⟨hkj, ?_⟩
    by_contra hn
    have hMj := lt_of_not_ge hn
    rw [hfix j hMj, hmax] at hv
    exact (not_lt_of_gt hMj) hv
  · rintro ⟨hkj, hjM⟩
    refine ⟨hkj, ?_⟩
    have hnext : M < M + 1 := Nat.lt_succ_self (M : ℕ)
    have hwj := hr hkj (hkM.trans_lt hnext) (hjM.trans_lt hnext)
    rw [hfix (M + 1) hnext] at hwj
    have hle : w j ≤ M := Nat.le_of_lt_succ hwj
    have hne : w j ≠ M := by
      intro he
      exact (ne_of_gt hkj) (hinj (he.trans hmax.symm))
    rw [hmax]
    exact lt_of_le_of_ne hle hne

private theorem card_positions_difference (m n : ℕ) :
    (positions m \ positions n).card = m - n := by
  by_cases hnm : n ≤ m
  · have hs : positions n ⊆ positions m := by
      intro j hj
      exact (mem_positions _ _).mpr (((mem_positions _ _).mp hj).trans hnm)
    rw [Finset.card_sdiff_of_subset hs, card_positions, card_positions]
  · have hmn : m ≤ n := le_of_lt (lt_of_not_ge hnm)
    have he : positions m \ positions n = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hmem := Finset.mem_sdiff.mp hj
      exact hmem.2 ((mem_positions _ _).mpr (((mem_positions _ _).mp hmem.1).trans hmn))
    rw [he, Finset.card_empty, Nat.sub_eq_zero_of_le hmn]

/-- The non-record tail counts of two increasing blocks have three interval pieces. -/
theorem twoBlock_tailCard_eq {w : ℕ+ → ℕ+} {k M : ℕ+}
    (hl : StrictMonoOn w {i : ℕ+ | i ≤ k})
    (hr : StrictMonoOn w {i : ℕ+ | k < i}) (hinj : Function.Injective w)
    (hkM : k ≤ M) (hmax : w k = M) (hfix : ∀ i : ℕ+, M < i → w i = i) (i : ℕ+) :
    ((positions (M : ℕ)).filter fun j => i ≤ j ∧
      ∃ t : ℕ+, t < j ∧ w j < w t).card =
      if i ≤ k then (M : ℕ) - (k : ℕ)
      else if i ≤ M then (M : ℕ) - (i : ℕ) + 1 else 0 := by
  have he : (positions (M : ℕ)).filter (fun j => i ≤ j ∧
      ∃ t : ℕ+, t < j ∧ w j < w t) =
      positions (M : ℕ) \ positions (max (k : ℕ) ((i : ℕ) - 1)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff, mem_positions,
      twoBlock_nonRecord_interval_iff hl hr hinj hkM hmax hfix]
    have hi : 0 < (i : ℕ) := i.2
    change ((j : ℕ) ≤ (M : ℕ) ∧ (i : ℕ) ≤ (j : ℕ) ∧
        (k : ℕ) < (j : ℕ) ∧ (j : ℕ) ≤ (M : ℕ)) ↔
      (j : ℕ) ≤ (M : ℕ) ∧ ¬(j : ℕ) ≤ max (k : ℕ) ((i : ℕ) - 1)
    omega
  rw [he, card_positions_difference]
  have hi : 0 < (i : ℕ) := i.2
  have hk : (k : ℕ) ≤ (M : ℕ) := hkM
  change (M : ℕ) - max (k : ℕ) ((i : ℕ) - 1) =
    if (i : ℕ) ≤ (k : ℕ) then (M : ℕ) - (k : ℕ)
    else if (i : ℕ) ≤ (M : ℕ) then (M : ℕ) - (i : ℕ) + 1 else 0
  split_ifs <;> omega

/-- A permutation fails to be a record exactly when an earlier value is larger. -/
theorem not_isRecord_iff_earlier_larger (w : FinitaryPerm ℕ+) (j : ℕ+) :
    ¬IsRecord w j ↔ ∃ i : ℕ+, i < j ∧ w j < w i := by
  constructor
  · intro hn
    unfold IsRecord at hn
    push Not at hn
    obtain ⟨i, hij, hv⟩ := hn
    have hne : w i ≠ w j := fun he => (ne_of_lt hij) (w.injective he)
    exact ⟨i, hij, lt_of_le_of_ne hv (Ne.symm hne)⟩
  · rintro ⟨i, hij, hv⟩ hrecord
    exact (not_lt_of_gt hv) (hrecord i hij)

/-- A support-containing finite interval counts all non-records in any positive tail. -/
theorem nonRecordsFrom_card_supported {w : FinitaryPerm ℕ+} {n : ℕ}
    (hw : IsSupported n w) (i : ℕ+) :
    w.nonRecordsFrom i = ((positions n).filter fun j => i ≤ j ∧ ¬IsRecord w j).card := by
  rw [nonRecordsFrom_eq_card]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, mem_tailPositions, mem_positions]
  constructor
  · rintro ⟨⟨hj, hij⟩, hnr⟩
    refine ⟨?_, hij, hnr⟩
    by_contra hn
    exact hnr (hw.isRecord_above (lt_of_not_ge hn))
  · rintro ⟨_, hij, hnr⟩
    refine ⟨⟨?_, hij⟩, hnr⟩
    by_contra hn
    exact hnr (w.isRecord_above (lt_of_not_ge hn))

/-- A two-block permutation's intrinsic non-record tail has the three interval pieces. -/
theorem twoBlock_nonRecordsFrom {w : FinitaryPerm ℕ+} {k M : ℕ+}
    (hl : StrictMonoOn w {i : ℕ+ | i ≤ k})
    (hr : StrictMonoOn w {i : ℕ+ | k < i}) (hkM : k ≤ M)
    (hmax : w k = M) (hfix : ∀ i : ℕ+, M < i → w i = i) (i : ℕ+) :
    w.nonRecordsFrom i = if i ≤ k then (M : ℕ) - (k : ℕ)
      else if i ≤ M then (M : ℕ) - (i : ℕ) + 1 else 0 := by
  have hs : IsSupported (M : ℕ) w := hfix
  rw [nonRecordsFrom_card_supported hs]
  simpa only [not_isRecord_iff_earlier_larger] using
    twoBlock_tailCard_eq hl hr w.injective hkM hmax hfix i

/-- The first block's maximum bounds the support of a two-block permutation. -/
theorem twoBlock_forward_le {w : FinitaryPerm ℕ+} {k M : ℕ+}
    (hl : StrictMonoOn w {i : ℕ+ | i ≤ k})
    (hr : StrictMonoOn w {i : ℕ+ | k < i}) (hmax : w k = M) :
    w.forwardStability ≤ (M : ℕ) := by
  by_contra hn
  have hMf : (M : ℕ) < w.forwardStability := lt_of_not_ge hn
  have hf : 1 < w.forwardStability := lt_of_le_of_lt (Nat.succ_le_of_lt M.pos) hMf
  let m : ℕ+ := ⟨w.forwardStability, w.one_le_forwardStability⟩
  let p := w⁻¹ m
  have hp : w p = m := apply_inv_apply w m
  have hpm : p ≤ m := (w.isSupported_forwardStability.apply_le_iff p).mp (by rw [hp]; rfl)
  have hne : p ≠ m := by
    intro he
    exact forwardStability_moved hf (by simpa only [he] using hp)
  have hpm' : p < m := lt_of_le_of_ne hpm hne
  have hkp : k < p := by
    by_contra hn'
    have hpk : p ≤ k := le_of_not_gt hn'
    have hvalue := hl.monotoneOn hpk (show k ≤ k from le_rfl) hpk
    rw [hp, hmax] at hvalue
    exact (not_le_of_gt hMf) hvalue
  have hinc := hr hkp (hkp.trans hpm') hpm'
  rw [hp] at hinc
  have hwm : w m ≤ m := (w.isSupported_forwardStability.apply_le_iff m).mpr le_rfl
  exact (not_lt_of_ge hwm) hinc

/-- A strictly later first-block maximum is the exact support bound. -/
theorem twoBlock_forward_eq {w : FinitaryPerm ℕ+} {k M : ℕ+}
    (hl : StrictMonoOn w {i : ℕ+ | i ≤ k})
    (hr : StrictMonoOn w {i : ℕ+ | k < i}) (hmax : w k = M) (hkM : k < M) :
    w.forwardStability = (M : ℕ) := by
  apply le_antisymm (twoBlock_forward_le hl hr hmax)
  by_contra hn
  have hfixed := w.isSupported_forwardStability M (lt_of_not_ge hn)
  have he : k = M := w.injective (hmax.trans hfixed.symm)
  exact (ne_of_lt hkM) he

/-- The first-block maximum alone yields the intrinsic three-piece non-record tail. -/
theorem twoBlock_tail_of_max {w : FinitaryPerm ℕ+} {k M : ℕ+}
    (hl : StrictMonoOn w {i : ℕ+ | i ≤ k})
    (hr : StrictMonoOn w {i : ℕ+ | k < i}) (hkM : k ≤ M) (hmax : w k = M) (i : ℕ+) :
    w.nonRecordsFrom i = if i ≤ k then (M : ℕ) - (k : ℕ)
      else if i ≤ M then (M : ℕ) - (i : ℕ) + 1 else 0 := by
  apply twoBlock_nonRecordsFrom hl hr hkM hmax
  intro j hj
  exact w.isSupported_forwardStability j ((twoBlock_forward_le hl hr hmax).trans_lt hj)

end FinitaryPerm
