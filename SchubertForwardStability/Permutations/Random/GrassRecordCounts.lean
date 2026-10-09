import SchubertForwardStability.Permutations.Random.MaximumLaw
import SchubertForwardStability.Permutations.Classes.GrassRecordStructure
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Counts of records in subset encodings

## Main results

A record occurs in the selected block or beyond its selected maximum. The disjoint
encoding events have binomial and powerset counts. Unique nonidentity encodings
remove the duplicate initial-segment representations of the identity.
-/

open scoped Classical BigOperators

namespace FinitaryPerm

/-- A record of an admissible encoding occurs in its selected block or after its maximum. -/
theorem subset_record_iff (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) (j : ℕ+) :
    IsRecord (subsetPermutation n V) j ↔ j.val ≤ V.card ∨ V.sup PNat.val < j.val := by
  rw [subsetPermutation_eq n V hV]
  have h := not_congr (grassmannian_notRecord_iff n V hV j)
  simpa only [not_not, not_and_or, Nat.not_lt, Nat.not_le] using h

/-- Admissible subsets of size at least a threshold are counted by a binomial tail. -/
theorem card_subset_size_ge (n j : ℕ) :
    ((positions n).powerset.filter fun V => j ≤ V.card).card =
      ∑ k ∈ Finset.Icc j n, n.choose k := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (positions n).powerset (Finset.Icc j n) (Finset.card : Finset ℕ+ → ℕ)
  simp only [card_subset_size] at h
  have he : (positions n).powerset.filter (fun V => V.card ∈ Finset.Icc j n) =
      (positions n).powerset.filter (fun V => j ≤ V.card) := by
    ext V
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hV, hj, _⟩
      exact ⟨hV, hj⟩
    · rintro ⟨hV, hj⟩
      refine ⟨hV, hj, ?_⟩
      simpa only [card_positions] using Finset.card_le_card (Finset.mem_powerset.mp hV)
  rw [he] at h
  exact h.symm

private theorem card_le_selected_max (V : Finset ℕ+) : V.card ≤ V.sup PNat.val := by
  have hs := (subset_maximum_le_iff (V.sup PNat.val) V).mp le_rfl
  simpa only [card_positions] using Finset.card_le_card hs

/-- The encoding record fibre is the disjoint union of its size and maximum events. -/
theorem subset_record_fiber (n : ℕ) (j : ℕ+) :
    (positions n).powerset.filter (fun V => IsRecord (subsetPermutation n V) j) =
      ((positions n).powerset.filter (fun V => j.val ≤ V.card)) ∪
        ((positions n).powerset.filter (fun V => V.sup PNat.val < j.val)) := by
  ext V
  by_cases hV : V ⊆ positions n
  · simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_powerset, hV,
      true_and, subset_record_iff n V hV j]
  · simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_powerset, hV,
      false_and, or_self]

/-- The encoding record count is the binomial tail plus the shorter powerset. -/
theorem card_subset_records (n : ℕ) (j : ℕ+) (hj : j.val ≤ n) :
    ((positions n).powerset.filter fun V => IsRecord (subsetPermutation n V) j).card =
      (∑ k ∈ Finset.Icc j.val n, n.choose k) + 2 ^ (j.val - 1) := by
  have hd : Disjoint
      ((positions n).powerset.filter fun V => j.val ≤ V.card)
      ((positions n).powerset.filter fun V => V.sup PNat.val < j.val) := by
    apply Finset.disjoint_left.mpr
    intro V hV hW
    have hc := card_le_selected_max V
    have h₁ := (Finset.mem_filter.mp hV).2
    have h₂ := (Finset.mem_filter.mp hW).2
    omega
  rw [subset_record_fiber, Finset.card_union_of_disjoint hd, card_subset_size_ge]
  have he : (positions n).powerset.filter (fun V => V.sup PNat.val < j.val) =
      (positions n).powerset.filter (fun V => V.sup PNat.val ≤ j.val - 1) := by
    apply Finset.filter_congr
    intro V _
    have hp := PNat.pos j
    omega
  rw [he, card_subset_maximum_le, min_eq_right (by omega : j.val - 1 ≤ n)]

/-- Nonidentity record encodings are bijective with the nonidentity record family. -/
theorem card_nonid_record_encodings (n : ℕ) (j : ℕ+) :
    (((positions n).powerset.filter fun V => IsRecord (subsetPermutation n V) j).filter
      fun V => subsetPermutation n V ≠ 1).card =
      (((grassmannian n).filter fun w => IsRecord w j).erase 1).card := by
  apply Finset.card_bij (fun V _ => subsetPermutation n V)
  · intro V hV
    obtain ⟨hVr, hne⟩ := Finset.mem_filter.mp hV
    obtain ⟨_, hr⟩ := Finset.mem_filter.mp hVr
    exact Finset.mem_erase.mpr ⟨hne,
      Finset.mem_filter.mpr ⟨subsetPermutation_mem_grassmannian n V, hr⟩⟩
  · intro V hV W hW he
    obtain ⟨hVr, hne⟩ := Finset.mem_filter.mp hV
    have hv := Finset.mem_powerset.mp (Finset.mem_filter.mp hVr).1
    have hw := Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hW).1).1
    rw [subsetPermutation_eq n V hv] at hne
    rw [subsetPermutation_eq n V hv, subsetPermutation_eq n W hw] at he
    exact grassmannianOfSubset_inj_nonid n V W hv hw hne he
  · intro w hw
    obtain ⟨hne, hwr⟩ := Finset.mem_erase.mp hw
    obtain ⟨hg, hr⟩ := Finset.mem_filter.mp hwr
    obtain ⟨V, hV, he⟩ := exists_grassmannianOfSubset hg
    have hs : subsetPermutation n V = w := (subsetPermutation_eq n V hV).trans he.symm
    refine ⟨V, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hV, ?_⟩, ?_⟩, hs⟩ <;> rw [hs]
    · exact hr
    · exact hne

/-- Removing the duplicate identity encodings subtracts `n` from the record count. -/
theorem card_grassmannian_records (n : ℕ) (j : ℕ+) (hj : j.val ≤ n) :
    ((grassmannian n).filter fun w => IsRecord w j).card + n =
      (∑ k ∈ Finset.Icc j.val n, n.choose k) + 2 ^ (j.val - 1) := by
  have he :
      (((positions n).powerset.filter fun V => IsRecord (subsetPermutation n V) j).filter
        fun V => subsetPermutation n V = 1) =
      (positions n).powerset.filter (fun V => subsetPermutation n V = 1) := by
    ext V
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hV, _⟩, hi⟩
      exact ⟨hV, hi⟩
    · rintro ⟨hV, hi⟩
      refine ⟨⟨hV, ?_⟩, hi⟩
      rw [hi]
      exact isRecord_one j
  have h := Finset.card_filter_add_card_filter_not
    (s := (positions n).powerset.filter fun V => IsRecord (subsetPermutation n V) j)
    (fun V => subsetPermutation n V = 1)
  rw [he, card_subsetPermutation_one_fiber, card_nonid_record_encodings,
    card_subset_records n j hj] at h
  have hm : 1 ∈ (grassmannian n).filter fun w => IsRecord w j :=
    Finset.mem_filter.mpr ⟨one_mem_grassmannian n, isRecord_one j⟩
  have hc := Finset.card_erase_of_mem hm
  have hp := Finset.card_pos.mpr ⟨1, hm⟩
  omega

end FinitaryPerm
