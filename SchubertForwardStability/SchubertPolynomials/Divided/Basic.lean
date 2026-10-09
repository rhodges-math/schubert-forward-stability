import SchubertForwardStability.SchubertPolynomials.Divided.Monomials
import SchubertForwardStability.SchubertPolynomials.ForMathlib.RootRegular
import Mathlib.Tactic.Ring

/-! # Divided-difference quotient identities

## Main results

* `root_mul_variableDividedDifference`: the polynomial quotient identity.
* `variableDividedDifference_eq_iff`: uniqueness of the quotient.
* `variableDividedDifference_mul`: the twisted Leibniz rule.
* `variableDividedDifference_sq`: the nilpotent square relation.

## Implementation notes

Cancellation uses regular variable differences, not a domain hypothesis.
The coefficient ring remains an arbitrary commutative ring.
-/

namespace SchubertPolynomial

variable {σ R : Type*} [CommRing R]

/-- The root times the divided difference of a monomial is its alternating numerator. -/
theorem root_mul_divided_monomial {i j : σ} (hij : i ≠ j) (a : σ →₀ ℕ) (c : R) :
    (MvPolynomial.X i - MvPolynomial.X j) *
        variableDividedDifference R i j (MvPolynomial.monomial a c) =
      MvPolynomial.monomial a c - variableSwap R i j (MvPolynomial.monomial a c) := by
  rw [variableDividedDifference_monomial]
  have he : MvPolynomial.monomial a c = c • MvPolynomial.monomial a (1 : R) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [he, map_smul, mul_smul_comm, root_mul_monomialQuotient hij, smul_sub]

/-- Divided difference is the polynomial quotient of the alternating difference by the root. -/
theorem root_mul_variableDividedDifference {i j : σ} (hij : i ≠ j)
    (p : MvPolynomial σ R) :
    (MvPolynomial.X i - MvPolynomial.X j) * variableDividedDifference R i j p =
      p - variableSwap R i j p := by
  induction p using MvPolynomial.monomial_add_induction_on with
  | C c =>
    simpa only [MvPolynomial.C_apply] using root_mul_divided_monomial hij 0 c
  | monomial_add a c p _ _ hp =>
    rw [map_add, map_add, mul_add, hp, root_mul_divided_monomial hij]
    abel

/-- A divided difference is uniquely determined by its alternating quotient identity. -/
theorem variableDividedDifference_eq_iff {i j : σ} (hij : i ≠ j)
    (p q : MvPolynomial σ R) :
    variableDividedDifference R i j p = q ↔
      (MvPolynomial.X i - MvPolynomial.X j) * q = p - variableSwap R i j p := by
  constructor
  · intro he
    rw [← he, root_mul_variableDividedDifference hij]
  · intro he
    apply (MvPolynomial.isRegular_X_sub_X hij).left
    exact (root_mul_variableDividedDifference hij p).trans he.symm

/-- Divided differences satisfy the twisted product rule over any commutative ring. -/
theorem variableDividedDifference_mul {i j : σ} (hij : i ≠ j)
    (p q : MvPolynomial σ R) :
    variableDividedDifference R i j (p * q) =
      variableDividedDifference R i j p * q +
        variableSwap R i j p * variableDividedDifference R i j q := by
  apply (variableDividedDifference_eq_iff hij _ _).mpr
  calc
    (MvPolynomial.X i - MvPolynomial.X j) *
        (variableDividedDifference R i j p * q +
          variableSwap R i j p * variableDividedDifference R i j q) =
      ((MvPolynomial.X i - MvPolynomial.X j) * variableDividedDifference R i j p) * q +
        variableSwap R i j p *
          ((MvPolynomial.X i - MvPolynomial.X j) * variableDividedDifference R i j q) := by
      ring
    _ = (p - variableSwap R i j p) * q +
        variableSwap R i j p * (q - variableSwap R i j q) := by
      rw [root_mul_variableDividedDifference hij, root_mul_variableDividedDifference hij]
    _ = p * q - variableSwap R i j (p * q) := by
      rw [map_mul]
      ring

/-- Every divided difference is invariant under its variable swap. -/
theorem variableSwap_dividedDifference {i j : σ} (hij : i ≠ j)
    (p : MvPolynomial σ R) :
    variableSwap R i j (variableDividedDifference R i j p) =
      variableDividedDifference R i j p := by
  apply (MvPolynomial.isRegular_X_sub_X hij).left
  have hm := congrArg (variableSwap R i j) (root_mul_variableDividedDifference hij p)
  simp only [map_mul, map_sub, variableSwap_X_left, variableSwap_X_right,
    variableSwap_involutive] at hm
  calc
    (MvPolynomial.X i - MvPolynomial.X j) *
        variableSwap R i j (variableDividedDifference R i j p) =
      -((MvPolynomial.X j - MvPolynomial.X i) *
        variableSwap R i j (variableDividedDifference R i j p)) := by ring
    _ = -(variableSwap R i j p - p) := by rw [hm]
    _ = p - variableSwap R i j p := by ring
    _ = (MvPolynomial.X i - MvPolynomial.X j) * variableDividedDifference R i j p :=
      (root_mul_variableDividedDifference hij p).symm

/-- Applying the same divided difference twice gives zero. -/
@[simp]
theorem variableDividedDifference_sq {i j : σ} (hij : i ≠ j) (p : MvPolynomial σ R) :
    variableDividedDifference R i j (variableDividedDifference R i j p) = 0 := by
  apply (variableDividedDifference_eq_iff hij _ _).mpr
  rw [variableSwap_dividedDifference hij, sub_self, mul_zero]

/-- Constants have zero divided difference. -/
@[simp]
theorem variableDividedDifference_C {i j : σ} (hij : i ≠ j) (c : R) :
    variableDividedDifference R i j (MvPolynomial.C c) = 0 := by
  apply (variableDividedDifference_eq_iff hij _ _).mpr
  simp only [variableSwap, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C,
    sub_self, mul_zero]

/-- The first indexed variable has divided difference one. -/
@[simp]
theorem variableDividedDifference_X_left {i j : σ} (hij : i ≠ j) :
    variableDividedDifference R i j (MvPolynomial.X i) = 1 := by
  apply (variableDividedDifference_eq_iff hij _ _).mpr
  simp only [variableSwap_X_left, mul_one]

/-- The second indexed variable has divided difference negative one. -/
@[simp]
theorem variableDividedDifference_X_right {i j : σ} (hij : i ≠ j) :
    variableDividedDifference R i j (MvPolynomial.X j) = -1 := by
  apply (variableDividedDifference_eq_iff hij _ _).mpr
  rw [variableSwap_X_right]
  ring

/-- A variable outside the indexed pair has zero divided difference. -/
@[simp]
theorem variableDividedDifference_X_other {i j : σ} (hij : i ≠ j) (k : σ)
    (hki : k ≠ i) (hkj : k ≠ j) :
    variableDividedDifference R i j (MvPolynomial.X k) = 0 := by
  apply (variableDividedDifference_eq_iff hij _ _).mpr
  rw [variableSwap_X_other i j k hki hkj, sub_self, mul_zero]

/-- Zero divided difference is equivalent to invariance under the indexed variable swap. -/
theorem variableDividedDifference_eq_zero {i j : σ} (hij : i ≠ j)
    (p : MvPolynomial σ R) :
    variableDividedDifference R i j p = 0 ↔ variableSwap R i j p = p := by
  rw [variableDividedDifference_eq_iff hij, mul_zero, eq_comm, sub_eq_zero, eq_comm]

end SchubertPolynomial
