import SchubertForwardStability.Permutations.Statistics.SuffixExtrema

/-! # Maximum formulas for pairs of suffix counts

## Main definitions

* `pairSuffixBound`: the positive maximum of positions plus positive paired suffix counts.
* `pairRecordBound`: the maximum of paired global non-record tail counts plus position minus one.

## Main results

`pairSuffixBound_eq_recordBound` identifies these two purely combinatorial maxima.

## Implementation notes

The maxima are finite, with cutoff the greater positive forward-stability bound. Suffix
candidates with zero paired count are omitted. The lower bound one includes the identity pair.
-/

namespace FinitaryPerm

open scoped Classical

/-- The positive maximum of positions plus nonzero paired suffix non-record counts. -/
noncomputable def pairSuffixBound (u v : FinitaryPerm ℕ+) : ℕ :=
  max 1 ((positions (max u.forwardStability v.forwardStability)).sup fun i =>
    if u.suffixNonRecordCount i + v.suffixNonRecordCount i = 0 then 0
    else (i : ℕ) + u.suffixNonRecordCount i + v.suffixNonRecordCount i)

/-- The maximum of paired global non-record tail counts plus the position minus one. -/
noncomputable def pairRecordBound (u v : FinitaryPerm ℕ+) : ℕ :=
  (positions (max u.forwardStability v.forwardStability + 1)).sup fun i =>
    u.nonRecordsFrom i + v.nonRecordsFrom i + (i : ℕ) - 1

/-- Interchanging the permutations preserves the paired suffix bound. -/
theorem pairSuffixBound_comm (u v : FinitaryPerm ℕ+) :
    pairSuffixBound u v = pairSuffixBound v u := by
  simp only [pairSuffixBound, max_comm u.forwardStability v.forwardStability,
    Nat.add_comm (u.suffixNonRecordCount _) (v.suffixNonRecordCount _), Nat.add_assoc]

/-- The paired suffix bound is always at least one. -/
theorem one_le_pairSuffixBound (u v : FinitaryPerm ℕ+) : 1 ≤ pairSuffixBound u v :=
  le_max_left _ _

/-- Every positive paired suffix candidate is bounded by the paired suffix maximum. -/
theorem suffix_candidate_le {u v : FinitaryPerm ℕ+} {i : ℕ+}
    (hi : (i : ℕ) ≤ max u.forwardStability v.forwardStability)
    (hpositive : 0 < u.suffixNonRecordCount i + v.suffixNonRecordCount i) :
    (i : ℕ) + u.suffixNonRecordCount i + v.suffixNonRecordCount i ≤ pairSuffixBound u v := by
  have hmem := (mem_positions _ i).mpr hi
  have hsup := Finset.le_sup (f := fun k : ℕ+ =>
    if u.suffixNonRecordCount k + v.suffixNonRecordCount k = 0 then 0
    else (k : ℕ) + u.suffixNonRecordCount k + v.suffixNonRecordCount k) hmem
  rw [ite_eq_right (ne_of_gt hpositive)] at hsup
  exact hsup.trans (le_max_right _ _)

/-- The paired suffix bound contains the positive support bound of the first permutation. -/
theorem forward_le_pairSuffixBound_left (u v : FinitaryPerm ℕ+) :
    u.forwardStability ≤ pairSuffixBound u v := by
  by_cases hu : u.forwardStability ≤ 1
  · exact hu.trans (one_le_pairSuffixBound u v)
  · obtain ⟨i, hi, he⟩ := exists_suffix_count_extreme (lt_of_not_ge hu)
    have hpositive : 0 < u.suffixNonRecordCount i + v.suffixNonRecordCount i := by
      omega
    have hcandidate := suffix_candidate_le
      ((le_of_lt hi).trans (le_max_left _ _)) hpositive
    omega

/-- The paired suffix bound contains the positive support bound of the second permutation. -/
theorem forward_le_pairSuffixBound_right (u v : FinitaryPerm ℕ+) :
    v.forwardStability ≤ pairSuffixBound u v := by
  rw [pairSuffixBound_comm]
  exact forward_le_pairSuffixBound_left v u

/-- The greater support bound is a lower bound for the paired suffix maximum. -/
theorem max_forward_le_pairSuffixBound (u v : FinitaryPerm ℕ+) :
    max u.forwardStability v.forwardStability ≤ pairSuffixBound u v :=
  max_le (forward_le_pairSuffixBound_left u v) (forward_le_pairSuffixBound_right u v)

/-- Every global tail candidate is bounded by the global tail maximum. -/
theorem record_candidate_le {u v : FinitaryPerm ℕ+} {i : ℕ+}
    (hi : (i : ℕ) ≤ max u.forwardStability v.forwardStability + 1) :
    u.nonRecordsFrom i + v.nonRecordsFrom i + (i : ℕ) - 1 ≤ pairRecordBound u v :=
  Finset.le_sup (f := fun k : ℕ+ =>
    u.nonRecordsFrom k + v.nonRecordsFrom k + (k : ℕ) - 1) ((mem_positions _ i).mpr hi)

/-- The global tail maximum is at least one, as seen at the second position. -/
theorem one_le_pairRecordBound (u v : FinitaryPerm ℕ+) : 1 ≤ pairRecordBound u v := by
  have hm : 1 ≤ max u.forwardStability v.forwardStability :=
    u.one_le_forwardStability.trans (le_max_left _ _)
  have hcandidate := record_candidate_le (u := u) (v := v) (i := 2) (by
    change 2 ≤ max u.forwardStability v.forwardStability + 1
    omega)
  change u.nonRecordsFrom 2 + v.nonRecordsFrom 2 + 2 - 1 ≤ _ at hcandidate
  omega

/-- Global non-record tail counts bound all positive paired suffix candidates. -/
theorem pairSuffixBound_le_recordBound (u v : FinitaryPerm ℕ+) :
    pairSuffixBound u v ≤ pairRecordBound u v := by
  apply max_le (one_le_pairRecordBound u v)
  apply Finset.sup_le
  intro i hi
  by_cases hzero : u.suffixNonRecordCount i + v.suffixNonRecordCount i = 0
  · rw [ite_eq_left hzero]
    exact Nat.zero_le _
  · rw [ite_eq_right hzero]
    have hu := suffixNonRecordCount_le u i
    have hv := suffixNonRecordCount_le v i
    have hin := (mem_positions _ i).mp hi
    have hnext := record_candidate_le (u := u) (v := v) (i := i + 1) (by
      change (i : ℕ) + 1 ≤ max u.forwardStability v.forwardStability + 1
      omega)
    change u.nonRecordsFrom (i + 1) + v.nonRecordsFrom (i + 1) +
      ((i : ℕ) + 1) - 1 ≤ _ at hnext
    omega

private theorem tail_step_le (u v : FinitaryPerm ℕ+) (i : ℕ+)
    (hnot : ¬IsRecord u i ∨ ¬IsRecord v i) :
    u.nonRecordsFrom (i + 1) + v.nonRecordsFrom (i + 1) + ((i + 1 : ℕ+) : ℕ) - 1 ≤
      u.nonRecordsFrom i + v.nonRecordsFrom i + (i : ℕ) - 1 := by
  have hu := nonRecordsFrom_succ u i
  have hv := nonRecordsFrom_succ v i
  have hipos := PNat.pos i
  change u.nonRecordsFrom (i + 1) + v.nonRecordsFrom (i + 1) +
    ((i : ℕ) + 1) - 1 ≤ _
  rcases hnot with hu' | hv'
  · rw [nonRecordIndicator_eq_one hu'] at hu
    omega
  · rw [nonRecordIndicator_eq_one hv'] at hv
    omega

private theorem tail_at_records_le (u v : FinitaryPerm ℕ+) (i : ℕ+)
    (hi : (i : ℕ) ≤ max u.forwardStability v.forwardStability)
    (hu : IsRecord u i) (hv : IsRecord v i) :
    u.nonRecordsFrom (i + 1) + v.nonRecordsFrom (i + 1) + ((i + 1 : ℕ+) : ℕ) - 1 ≤
      pairSuffixBound u v := by
  rw [← suffixNonRecordCount_eq_of_record hu, ← suffixNonRecordCount_eq_of_record hv]
  change u.suffixNonRecordCount i + v.suffixNonRecordCount i +
    ((i : ℕ) + 1) - 1 ≤ _
  by_cases hzero : u.suffixNonRecordCount i + v.suffixNonRecordCount i = 0
  · have hm := max_forward_le_pairSuffixBound u v
    omega
  · have hc := suffix_candidate_le hi (by omega :
      0 < u.suffixNonRecordCount i + v.suffixNonRecordCount i)
    omega

private theorem tail_first_le (u v : FinitaryPerm ℕ+) :
    u.nonRecordsFrom 1 + v.nonRecordsFrom 1 + 1 - 1 ≤ pairSuffixBound u v := by
  have hu := nonRecordsFrom_succ u 1
  have hv := nonRecordsFrom_succ v 1
  rw [nonRecordIndicator_eq_zero (isRecord_first u)] at hu
  rw [nonRecordIndicator_eq_zero (isRecord_first v)] at hv
  have hsecond := tail_at_records_le u v 1
    (u.one_le_forwardStability.trans (le_max_left _ _))
    (isRecord_first u) (isRecord_first v)
  change u.nonRecordsFrom (1 + 1) + v.nonRecordsFrom (1 + 1) + 2 - 1 ≤ _ at hsecond
  omega

private theorem tail_candidates_le (u v : FinitaryPerm ℕ+) (n : ℕ) :
    ∀ i : ℕ+, (i : ℕ) ≤ n → (i : ℕ) ≤ max u.forwardStability v.forwardStability + 1 →
      u.nonRecordsFrom i + v.nonRecordsFrom i + (i : ℕ) - 1 ≤ pairSuffixBound u v := by
  induction n with
  | zero =>
      intro i hi _
      have hipos := PNat.pos i
      omega
  | succ n ih =>
      intro i hi hin
      by_cases hprev : (i : ℕ) ≤ n
      · exact ih i hprev hin
      have hie : (i : ℕ) = n + 1 := by omega
      by_cases hn : n = 0
      · have hi1 : i = 1 := PNat.eq (by change (i : ℕ) = 1; omega)
        rw [hi1]
        change u.nonRecordsFrom 1 + v.nonRecordsFrom 1 + 1 - 1 ≤ pairSuffixBound u v
        exact tail_first_le u v
      · let k : ℕ+ := ⟨n, by omega⟩
        have hik : i = k + 1 := PNat.eq hie
        rw [hik]
        have hk : (k : ℕ) ≤ max u.forwardStability v.forwardStability := by
          change n ≤ max u.forwardStability v.forwardStability
          omega
        by_cases hu : IsRecord u k
        · by_cases hv : IsRecord v k
          · exact tail_at_records_le u v k hk hu hv
          · exact (tail_step_le u v k (Or.inr hv)).trans
              (ih k le_rfl (hk.trans (Nat.le_succ _)))
        · exact (tail_step_le u v k (Or.inl hu)).trans
            (ih k le_rfl (hk.trans (Nat.le_succ _)))

/-- Every paired global non-record tail candidate is bounded by the paired suffix maximum. -/
theorem pairRecordBound_le_suffixBound (u v : FinitaryPerm ℕ+) :
    pairRecordBound u v ≤ pairSuffixBound u v := by
  apply Finset.sup_le
  intro i hi
  exact tail_candidates_le u v (max u.forwardStability v.forwardStability + 1) i
    ((mem_positions _ i).mp hi) ((mem_positions _ i).mp hi)

/-- The positive suffix-count maximum equals the global non-record tail maximum. -/
theorem pairSuffixBound_eq_recordBound (u v : FinitaryPerm ℕ+) :
    pairSuffixBound u v = pairRecordBound u v :=
  le_antisymm (pairSuffixBound_le_recordBound u v) (pairRecordBound_le_suffixBound u v)

end FinitaryPerm
