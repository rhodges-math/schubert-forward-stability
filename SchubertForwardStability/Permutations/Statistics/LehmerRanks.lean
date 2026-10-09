import SchubertForwardStability.Permutations.Statistics.LehmerCode

/-!
# Remaining-value ranks for right Lehmer counts

## Main definitions

* `remainingValues n w i` removes the values in the prefix strictly before `i`.

## Main results

* `rightInversionCount_eq_rank` identifies a right inversion count with the rank
  of its value among the remaining values.

## Implementation notes

The rank is computed directly from the values at the prefix positions.
-/

namespace FinitaryPerm

noncomputable section

open scoped Classical

/-- The values in the supported interval not used at any earlier position. -/
def remainingValues (n : ℕ) (w : FinitaryPerm ℕ+) (i : ℕ+) : Finset ℕ+ :=
  positions n \ (positions ((i : ℕ) - 1)).image w

/-- Remaining values are precisely bounded values absent from the strict prefix. -/
@[simp] theorem mem_remainingValues (n : ℕ) (w : FinitaryPerm ℕ+) (i a : ℕ+) :
    a ∈ remainingValues n w i ↔ (a : ℕ) ≤ n ∧ ∀ k : ℕ+, k < i → w k ≠ a := by
  rw [remainingValues, Finset.mem_sdiff, mem_positions, Finset.mem_image]
  constructor
  · rintro ⟨ha, hprefix⟩
    refine ⟨ha, ?_⟩
    intro k hki he
    apply hprefix
    refine ⟨k, (mem_positions _ _).mpr ?_, he⟩
    change (k : ℕ) < (i : ℕ) at hki
    omega
  · rintro ⟨ha, hprefix⟩
    refine ⟨ha, ?_⟩
    rintro ⟨k, hk, he⟩
    have hkn := (mem_positions ((i : ℕ) - 1) k).mp hk
    have hipos := PNat.pos i
    exact hprefix k (by change (k : ℕ) < (i : ℕ); omega) he

/-- A supported value at the current position has not occurred in its strict prefix. -/
theorem apply_mem_remainingValues {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    w i ∈ remainingValues n w i := by
  rw [mem_remainingValues]
  refine ⟨(hw.apply_le_iff i).mpr hi, ?_⟩
  intro k hki he
  exact (ne_of_lt hki) (w.injective he)

/-- The image of a right inversion set is the set of lower remaining values. -/
theorem image_rightInversionSet {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (i : ℕ+) :
    (w.rightInversionSet i).image w = (remainingValues n w i).filter (· < w i) := by
  ext a
  rw [Finset.mem_image, Finset.mem_filter, mem_remainingValues]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hjn : (j : ℕ) ≤ n := by
      rw [rightInversionSet_eq_filter hw i] at hj
      exact (mem_positions _ _).mp (Finset.mem_filter.mp hj).1
    obtain ⟨hij, hvalue⟩ := (mem_rightInversionSet w i j).mp hj
    refine ⟨⟨(hw.apply_le_iff j).mpr hjn, ?_⟩, hvalue⟩
    intro k hki he
    have hkj := w.injective he
    subst k
    exact (not_lt_of_gt hij) hki
  · rintro ⟨⟨_, hprefix⟩, hvalue⟩
    let j := w⁻¹ a
    have he : w j = a := apply_inv_apply w a
    have hij : i < j := by
      rcases lt_trichotomy j i with hji | hji | hij
      · exact False.elim (hprefix j hji he)
      · have : w i = a := by simpa only [hji] using he
        rw [this] at hvalue
        exact False.elim (lt_irrefl a hvalue)
      · exact hij
    refine ⟨j, (mem_rightInversionSet w i j).mpr ⟨hij, ?_⟩, he⟩
    simpa only [he] using hvalue

/-- A right inversion count is the lower-value rank among values remaining after
the strict prefix. -/
theorem rightInversionCount_eq_rank {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (i : ℕ+) :
    w.rightInversionCount i = ((remainingValues n w i).filter (· < w i)).card := by
  rw [← image_rightInversionSet hw i, Finset.card_image_of_injective _ w.injective]
  rfl

/-- Agreeing strict prefixes leave exactly the same finite set of values available. -/
theorem remainingValues_congr {n : ℕ} {w v : FinitaryPerm ℕ+} (i : ℕ+)
    (h : ∀ k : ℕ+, k < i → w k = v k) :
    remainingValues n w i = remainingValues n v i := by
  unfold remainingValues
  congr 1
  apply Finset.image_congr
  intro k hk
  have hkn := (mem_positions ((i : ℕ) - 1) k).mp hk
  have hipos := PNat.pos i
  apply h
  change (k : ℕ) < (i : ℕ)
  omega

end

end FinitaryPerm
