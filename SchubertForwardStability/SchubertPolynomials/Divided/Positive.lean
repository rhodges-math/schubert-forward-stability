import SchubertForwardStability.SchubertPolynomials.Divided.Basic
import Mathlib.Data.PNat.Basic

/-! # Adjacent divided differences on positive indices

## Main definitions

* `dividedDifference`: the adjacent operator on `MvPolynomial ℕ+ R`.

## Main results

The alternating quotient, twisted product rule, invariant image and nilpotent
square hold over any commutative coefficient ring. Constants and individual
variables have the usual divided differences.

## Implementation notes

The positive index `i` exchanges `i` and `i+1`. Multiplication conventions do not
enter this polynomial definition.
-/

namespace SchubertPolynomial

variable {R : Type*} [CommRing R]

/-- The adjacent type-A divided difference on polynomials with positive-indexed variables. -/
noncomputable abbrev dividedDifference (R : Type*) [CommRing R] (i : ℕ+) :
    MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R := variableDividedDifference R i (i + 1)

private theorem ne_next (i : ℕ+) : i ≠ i + 1 :=
  (show i < i + 1 from Nat.lt_succ_self (i : ℕ)).ne

/-- The adjacent root times the divided difference is its alternating numerator. -/
theorem root_mul_dividedDifference (i : ℕ+) (p : MvPolynomial ℕ+ R) :
    (MvPolynomial.X i - MvPolynomial.X (i + 1)) * dividedDifference R i p =
      p - variableSwap R i (i + 1) p := root_mul_variableDividedDifference (ne_next i) p

/-- Adjacent divided differences obey the twisted Leibniz rule. -/
theorem dividedDifference_mul (i : ℕ+) (p q : MvPolynomial ℕ+ R) :
    dividedDifference R i (p * q) = dividedDifference R i p * q +
      variableSwap R i (i + 1) p * dividedDifference R i q :=
  variableDividedDifference_mul (ne_next i) p q

/-- The image of an adjacent divided difference is fixed by its adjacent variable swap. -/
theorem variableSwap_dividedDifference_adj (i : ℕ+) (p : MvPolynomial ℕ+ R) :
    variableSwap R i (i + 1) (dividedDifference R i p) = dividedDifference R i p :=
  variableSwap_dividedDifference (ne_next i) p

/-- Adjacent divided differences have square zero. -/
theorem dividedDifference_sq (i : ℕ+) (p : MvPolynomial ℕ+ R) :
    dividedDifference R i (dividedDifference R i p) = 0 :=
  variableDividedDifference_sq (ne_next i) p

/-- Adjacent divided differences annihilate constants. -/
theorem dividedDifference_C (i : ℕ+) (c : R) :
    dividedDifference R i (MvPolynomial.C c) = 0 := variableDividedDifference_C (ne_next i) c

/-- The variable at the adjacent operator's index has divided difference one. -/
theorem dividedDifference_X (i : ℕ+) : dividedDifference R i (MvPolynomial.X i) = 1 :=
  variableDividedDifference_X_left (ne_next i)

/-- The next variable has divided difference negative one. -/
theorem dividedDifference_X_next (i : ℕ+) :
    dividedDifference R i (MvPolynomial.X (i + 1)) = -1 :=
  variableDividedDifference_X_right (ne_next i)

/-- Other variables have zero divided difference under the adjacent operator. -/
theorem dividedDifference_X_other (i j : ℕ+) (hji : j ≠ i) (hjn : j ≠ i + 1) :
    dividedDifference R i (MvPolynomial.X j) = 0 :=
  variableDividedDifference_X_other (ne_next i) j hji hjn

end SchubertPolynomial
