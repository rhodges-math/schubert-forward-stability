import SchubertForwardStability.Permutations.Random.PointMasses
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Counts of admissible subset encodings

## Main results

Cardinality fibres have binomial size. Deleting identity encodings gives a bijection
with the nonidentity Grassmannian family, and the full family has powerset size less
the duplicate initial segments. Weighted finite sums group by sampled cardinality.
-/

namespace FinitaryPerm

open scoped Classical BigOperators

/-- The cardinality fibre in the admissible powerset is its fixed-size powerset. -/
theorem subset_card_fiber (n k : ℕ) :
    (positions n).powerset.filter (fun V => V.card = k) = (positions n).powersetCard k := by
  ext V
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]

/-- There are exactly `choose n k` admissible subsets of sampled size `k`. -/
theorem card_subset_size (n k : ℕ) :
    ((positions n).powerset.filter fun V => V.card = k).card = n.choose k := by
  rw [subset_card_fiber, Finset.card_powersetCard, card_positions]

/-- Nonidentity admissible encodings are in bijection with nonidentity Grassmannians. -/
theorem card_nonid_subset_grass (n : ℕ) :
    ((positions n).powerset.filter fun V => subsetPermutation n V ≠ 1).card =
      ((grassmannian n).erase 1).card := by
  apply Finset.card_bij (fun V _ => subsetPermutation n V)
  · intro V hV
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_filter.mp hV).2, subsetPermutation_mem_grassmannian n V⟩
  · intro V hV W hW he
    have hv := Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1
    have hw := Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1
    have hne := (Finset.mem_filter.mp hV).2
    rw [subsetPermutation_eq n V hv] at hne
    rw [subsetPermutation_eq n V hv, subsetPermutation_eq n W hw] at he
    exact grassmannianOfSubset_inj_nonid n V W hv hw hne he
  · intro w hw
    obtain ⟨hne, hg⟩ := Finset.mem_erase.mp hw
    obtain ⟨V, hV, he⟩ := exists_grassmannianOfSubset hg
    have hm : V ∈ (positions n).powerset.filter fun U => subsetPermutation n U ≠ 1 := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hV, ?_⟩
      rw [subsetPermutation_eq n V hV, ←he]
      exact hne
    exact ⟨V, hm, (subsetPermutation_eq n V hV).trans he.symm⟩

/-- Removing the initial-segment identity fibres leaves `2^n-(n+1)` encodings. -/
theorem card_nonid_subset_encodings (n : ℕ) :
    ((positions n).powerset.filter fun V => subsetPermutation n V ≠ 1).card =
      2 ^ n - (n + 1) := by
  have h := Finset.card_filter_add_card_filter_not (s := (positions n).powerset)
    (fun V => subsetPermutation n V = 1)
  rw [card_subsetPermutation_one_fiber, Finset.card_powerset, card_positions] at h
  simpa only [Nat.add_sub_cancel_left] using congrArg (fun x : ℕ => x - (n + 1)) h

/-- The ambient Grassmannian family has cardinality `2^n-n`, including size zero. -/
theorem card_grassmannian (n : ℕ) : (grassmannian n).card = 2 ^ n - n := by
  have h := Finset.card_filter_add_card_filter_not (s := (positions n).powerset)
    (fun V => subsetPermutation n V = 1)
  rw [card_subsetPermutation_one_fiber, card_nonid_subset_grass,
    Finset.card_erase_of_mem (one_mem_grassmannian n), Finset.card_powerset,
    card_positions] at h
  have hp : 0 < (grassmannian n).card := Finset.card_pos.mpr ⟨1, one_mem_grassmannian n⟩
  omega

/-- A statistic of sampled size sums by its binomially counted fibres. -/
theorem sum_subset_sizes {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    ∑ V ∈ (positions n).powerset, f V.card =
      ∑ k ∈ Finset.range (n + 1), n.choose k • f k := by
  have hm : ∀ V ∈ (positions n).powerset, V.card ∈ Finset.range (n + 1) := by
    intro V hV
    have hc := Finset.card_le_card (Finset.mem_powerset.mp hV)
    rw [card_positions] at hc
    exact Finset.mem_range.mpr (by omega)
  rw [←Finset.sum_fiberwise_of_maps_to' hm f]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_const, card_subset_size]

/-- A pair-size statistic sums by the product of its two binomial fibre counts. -/
theorem sum_subset_pair_sizes {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → ℕ → R) :
    ∑ V ∈ (positions n).powerset, ∑ W ∈ (positions n).powerset, f V.card W.card =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        (n.choose k * n.choose l) • f k l := by
  calc
    _ = ∑ V ∈ (positions n).powerset, ∑ l ∈ Finset.range (n + 1),
        n.choose l • f V.card l := by
      apply Finset.sum_congr rfl
      intro V _
      exact sum_subset_sizes n (f V.card)
    _ = ∑ k ∈ Finset.range (n + 1), n.choose k •
        (∑ l ∈ Finset.range (n + 1), n.choose l • f k l) :=
      sum_subset_sizes n (fun k => ∑ l ∈ Finset.range (n + 1), n.choose l • f k l)
    _ = _ := by simp only [Finset.smul_sum, smul_smul]

end FinitaryPerm
