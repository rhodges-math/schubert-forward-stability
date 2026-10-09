import SchubertForwardStability.Permutations.Statistics.LehmerCode
import SchubertForwardStability.Permutations.Statistics.Records
import SchubertForwardStability.Permutations.Finitary.Longest
import SchubertForwardStability.Permutations.Statistics.LehmerInjective
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Left inversion codes

## Main definitions

* `leftCoordinates` counts preceding larger values in each bounded position.
* `leftCodeEquiv` identifies supported permutations with increasing-bound coordinates.

## Main results

Reversal exchanges left and right inversion counts. The left-coordinate map is
injective by the right Lehmer theorem and bijective by factorial cardinality.

## Implementation notes

Positive positions correspond to zero-based finite coordinates. Size zero is included.
-/

namespace FinitaryPerm

open scoped Classical
open scoped BigOperators

noncomputable section

private theorem reversal_lt {n : ℕ} {i j : ℕ+} (hi : (i : ℕ) ≤ n)
    (hj : (j : ℕ) ≤ n) : longestElement n i < longestElement n j ↔ j < i := by
  change (longestElement n i : ℕ) < (longestElement n j : ℕ) ↔ (j : ℕ) < (i : ℕ)
  rw [longestElement_apply_val n i hi, longestElement_apply_val n j hj]
  have hpi := PNat.pos i
  have hpj := PNat.pos j
  omega

private theorem left_to_conjugate {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (i : ℕ+) (hi : (i : ℕ) ≤ n) (j : ℕ+)
    (hj : j ∈ w.leftInversions i) :
    longestElement n j ∈ (longestElement n * w * longestElement n).rightInversionSet
      (longestElement n i) := by
  obtain ⟨hji, hv⟩ := (mem_leftInversions w i j).mp hj
  have hjn : (j : ℕ) ≤ n := le_trans hji.le hi
  apply (mem_rightInversionSet _ _ _).mpr
  refine ⟨(reversal_lt hi hjn).mpr hji, ?_⟩
  simpa only [mul_apply, longestElement_apply_twice] using
    (reversal_lt ((hw.apply_le_iff j).mpr hjn) ((hw.apply_le_iff i).mpr hi)).mpr hv

private theorem conjugate_to_left {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (i : ℕ+) (hi : (i : ℕ) ≤ n) (k : ℕ+)
    (hk : k ∈ (longestElement n * w * longestElement n).rightInversionSet
      (longestElement n i)) : longestElement n k ∈ w.leftInversions i := by
  have hkn : (k : ℕ) ≤ n := by
    rw [rightInversionSet_eq_filter hw.conjugate_longest (longestElement n i),
      Finset.mem_filter,
      mem_positions] at hk
    exact hk.1
  have hkr : (longestElement n k : ℕ) ≤ n :=
    ((isSupported_longestElement n).apply_le_iff k).mpr hkn
  obtain ⟨hpos, hval⟩ := (mem_rightInversionSet _ _ _).mp hk
  apply (mem_leftInversions w i _).mpr
  refine ⟨(reversal_lt hi hkr).mp (by simpa only [longestElement_apply_twice] using hpos), ?_⟩
  apply (reversal_lt ((hw.apply_le_iff _).mpr hkr) ((hw.apply_le_iff i).mpr hi)).mp
  simpa only [mul_apply, longestElement_apply_twice] using hval

/-- Reversal of positions and values exchanges left and right inversion counts. -/
theorem leftCount_eq_reversedRight {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    w.leftInversionCount i =
      (longestElement n * w * longestElement n).rightInversionCount (longestElement n i) := by
  have hset : ((longestElement n * w * longestElement n).rightInversionSet
      (longestElement n i)).image (longestElement n) = w.leftInversions i := by
    ext j
    constructor
    · intro hj
      obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp hj
      rw [← hkj]
      exact conjugate_to_left hw i hi k hk
    · intro hj
      exact Finset.mem_image.mpr
        ⟨longestElement n j, left_to_conjugate hw i hi j hj,
          longestElement_apply_twice n j⟩
  have hcard := congrArg Finset.card hset
  rw [Finset.card_image_of_injective _ (longestElement n).injective] at hcard
  exact hcard.symm

/-- Left inversion coordinates have bounds increasing with their positive positions. -/
abbrev LeftCoordinates (n : ℕ) := (i : Fin n) → Fin (i.val + 1)

/-- The bounded left inversion coordinates of any finitary permutation. -/
def leftCoordinates (n : ℕ) (w : FinitaryPerm ℕ+) : LeftCoordinates n := fun i =>
  ⟨w.leftInversionCount i.val.succPNat, by
    have h := leftInversionCount_le w i.val.succPNat
    change w.leftInversionCount i.val.succPNat ≤ i.val + 1 - 1 at h
    omega⟩

/-- Left inversion coordinates distinguish permutations supported in the same interval. -/
theorem leftCoordinates_injective (n : ℕ) : Function.Injective
    (fun w : {w : FinitaryPerm ℕ+ // IsSupported n w} => leftCoordinates n w.val) := by
  intro w v h
  have hc : longestElement n * w.val * longestElement n =
      longestElement n * v.val * longestElement n := by
    apply lehmerCode_injective
    ext j
    rw [lehmerCode_apply, lehmerCode_apply]
    by_cases hj : (j : ℕ) ≤ n
    · have hr : (longestElement n j : ℕ) ≤ n :=
        ((isSupported_longestElement n).apply_le_iff j).mpr hj
      let i : Fin n := ⟨(longestElement n j : ℕ) - 1, by
        have := PNat.pos (longestElement n j)
        omega⟩
      have hi : i.val.succPNat = longestElement n j := by
        apply PNat.eq
        change (longestElement n j : ℕ) - 1 + 1 = (longestElement n j : ℕ)
        have := PNat.pos (longestElement n j)
        omega
      have hv := congrArg (fun a : LeftCoordinates n => (a i).val) h
      change w.val.leftInversionCount i.val.succPNat =
        v.val.leftInversionCount i.val.succPNat at hv
      rw [hi, leftCount_eq_reversedRight w.property _ hr,
        leftCount_eq_reversedRight v.property _ hr, longestElement_apply_twice] at hv
      exact hv
    · rw [rightInversionCount_eq_zero w.property.conjugate_longest j (by omega),
        rightInversionCount_eq_zero v.property.conjugate_longest j (by omega)]
  apply Subtype.ext
  have ht := congrArg (fun x => longestElement n * x * longestElement n) hc
  simpa only [conjugate_longest_twice] using ht

/-- Increasing-bound finite coordinates have factorial cardinality. -/
theorem card_leftCoordinates (n : ℕ) : Fintype.card (LeftCoordinates n) = n.factorial := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Finset.prod_fin_eq_prod_range, Nat.factorial_eq_prod_range_add_one]
  apply Finset.prod_congr rfl
  intro i hi
  rw [dite_eq_left (Finset.mem_range.mp hi)]

/-- The left inversion map is bijective by injectivity and equal finite cardinalities. -/
theorem leftCoordinates_bijective (n : ℕ) : Function.Bijective
    (fun w : {w : FinitaryPerm ℕ+ // IsSupported n w} => leftCoordinates n w.val) := by
  let : Fintype {w : FinitaryPerm ℕ+ // IsSupported n w} :=
    Fintype.ofEquiv (Equiv.Perm (Fin n)) (finiteEquiv n)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨leftCoordinates_injective n, ?_⟩
  calc
    _ = Fintype.card (Equiv.Perm (Fin n)) := (Fintype.card_congr (finiteEquiv n)).symm
    _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]
    _ = _ := (card_leftCoordinates n).symm

/-- Supported permutations are equivalent to their increasing-bound left inversion codes. -/
def leftCodeEquiv (n : ℕ) :
    {w : FinitaryPerm ℕ+ // IsSupported n w} ≃ LeftCoordinates n :=
  Equiv.ofBijective (fun w => leftCoordinates n w.val) (leftCoordinates_bijective n)

/-- A left-code coordinate is the number of preceding larger values. -/
theorem leftCodeEquiv_apply (n : ℕ) (w : {w : FinitaryPerm ℕ+ // IsSupported n w})
    (i : Fin n) : (leftCodeEquiv n w i).val = w.val.leftInversionCount i.val.succPNat := rfl

/-- A record is exactly the zero entry of the increasing-bound inversion code. -/
theorem isRecord_iff_leftCode (n : ℕ) (w : {w : FinitaryPerm ℕ+ // IsSupported n w})
    (i : Fin n) : IsRecord w.val i.val.succPNat ↔ leftCodeEquiv n w i = 0 := by
  rw [isRecord_iff_leftInversionCount, ← leftCodeEquiv_apply n w i]
  exact Fin.val_eq_zero_iff

end

end FinitaryPerm
