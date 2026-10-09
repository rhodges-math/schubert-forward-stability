import SchubertForwardStability.SchubertPolynomials.Stability.ShiftRelation
import SchubertForwardStability.SchubertPolynomials.Products.Constants

/-! # Signed back-stability witnesses

## Main definitions

* `BackShiftWitness`: a signed shift of both factors whose Schubert product has an output moving
  the first position.

## Main results

Witnesses are symmetric in the two factors, a witness at shift zero is an output of the
unshifted product moving the first position, the identity pair has no witnesses, and a
witness shift cannot remove a moved position. For shifts `k ≥ 0` the witnesses are the
boundary hits of `SchubertPolynomial.BoundaryHit`, which define backward stability.
-/

namespace SchubertPolynomial

open FinitaryPerm
open scoped Classical

/-- An admissible signed shift whose Schubert product has an output moving the first position. -/
def BackShiftWitness (u v : FinitaryPerm ℕ+) (k : ℤ) : Prop :=
  ∃ u' v' w : FinitaryPerm ℕ+, SignedShift k u u' ∧ SignedShift k v v' ∧
    structureConst u' v' w ≠ 0 ∧ w 1 ≠ 1

/-- Exchanging the input permutations preserves every signed back-stability witness. -/
theorem backShiftWitness_comm (u v : FinitaryPerm ℕ+) (k : ℤ) :
    BackShiftWitness u v k ↔ BackShiftWitness v u k := by
  constructor
  · rintro ⟨u', v', w, hu, hv, hc, hw⟩
    refine ⟨v', u', w, hv, hu, ?_, hw⟩
    simpa only [structureConst_comm v' u' w] using hc
  · rintro ⟨v', u', w, hv, hu, hc, hw⟩
    refine ⟨u', v', w, hu, hv, ?_, hw⟩
    simpa only [structureConst_comm u' v' w] using hc

/-- Zero-shift witnesses are exactly unshifted product outputs moving the first position. -/
theorem backShiftWitness_zero_iff (u v : FinitaryPerm ℕ+) :
    BackShiftWitness u v 0 ↔ ∃ w : FinitaryPerm ℕ+, structureConst u v w ≠ 0 ∧ w 1 ≠ 1 := by
  constructor
  · rintro ⟨u', v', w, hu, hv, hc, hw⟩
    have he : u = u' := (signedShift_zero_iff u u').mp hu
    have he' : v = v' := (signedShift_zero_iff v v').mp hv
    subst u'
    subst v'
    exact ⟨w, hc, hw⟩
  · rintro ⟨w, hc, hw⟩
    exact ⟨u, v, w, SignedShift.zero u, SignedShift.zero v, hc, hw⟩

/-- Identity products never supply a back-stability witness at any signed shift. -/
theorem not_backShiftWitness_one (k : ℤ) : ¬BackShiftWitness 1 1 k := by
  rintro ⟨u', v', w, hu, hv, hc, hw⟩
  have he : u' = 1 := hu.eq_one
  have he' : v' = 1 := hv.eq_one
  subst u'
  subst v'
  rw [structureConst_one_left] at hc
  by_cases hew : w = 1
  · subst w
    exact hw (one_apply 1)
  · rw [ite_eq_right (Ne.symm hew)] at hc
    exact hc rfl

/-- A moved original position cannot be removed by an admissible witness shift. -/
theorem backShiftWitness_shift_lower {u v : FinitaryPerm ℕ+} {k : ℤ}
    (h : BackShiftWitness u v k) {i : ℕ+} (hi : u i ≠ i ∨ v i ≠ i) :
    1 - ((i : ℕ) : ℤ) ≤ k := by
  obtain ⟨u', v', w, hu, hv, _, _⟩ := h
  have hp : 0 < ((i : ℕ) : ℤ) + k := by
    by_contra hn
    have hle : ((i : ℕ) : ℤ) + k ≤ 0 := le_of_not_gt hn
    exact hi.elim (fun hm => hm (hu.removed_fixed i hle))
      (fun hm => hm (hv.removed_fixed i hle))
  omega

end SchubertPolynomial
