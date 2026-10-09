import SchubertForwardStability.SchubertPolynomials.Divided.Exponents
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Polynomial divided differences on monomials

## Main definitions

* `monomialQuotient`: the finite geometric-series quotient of a swapped monomial difference.
* `variableDividedDifference`: its linear extension to the multivariate polynomial ring.

## Main results

* `root_mul_monomialQuotient`: the finite formula has the alternating-difference numerator.
* `variableDividedDifference_monomial`: arbitrary coefficients factor out linearly.

## Implementation notes

The construction is valid over any commutative ring and any variable carrier.
Distinctness of the indexed variables is required for the quotient identity.
-/

namespace SchubertPolynomial

open scoped Classical

variable {σ R : Type*} [CommRing R]

/-- The polynomial quotient of a coefficient-one monomial's swapped difference. -/
noncomputable def monomialQuotient (R : Type*) [CommRing R] (i j : σ) (a : σ →₀ ℕ) :
    MvPolynomial σ R :=
  if a j < a i then
    ∑ k ∈ Finset.range (a i - a j),
      MvPolynomial.monomial (replaceExponents a i j (a i - 1 - k) (a j + k)) 1
  else if a i < a j then
    -∑ k ∈ Finset.range (a j - a i),
      MvPolynomial.monomial (replaceExponents a i j (a i + k) (a j - 1 - k)) 1
  else 0

/-- The linear divided-difference operator at an ordered pair of variables. -/
noncomputable def variableDividedDifference (R : Type*) [CommRing R] (i j : σ) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (MvPolynomial.basisMonomials σ R).constr R (monomialQuotient R i j)

/-- The linear operator takes a coefficient-one monomial to its finite quotient formula. -/
@[simp]
theorem variableDividedDifference_monomial_one (i j : σ) (a : σ →₀ ℕ) :
    variableDividedDifference R i j (MvPolynomial.monomial a 1) =
      monomialQuotient R i j a :=
  Module.Basis.constr_basis (MvPolynomial.basisMonomials σ R) R (monomialQuotient R i j) a

/-- An arbitrary monomial coefficient factors out of the divided difference. -/
theorem variableDividedDifference_monomial (i j : σ) (a : σ →₀ ℕ) (c : R) :
    variableDividedDifference R i j (MvPolynomial.monomial a c) =
      c • monomialQuotient R i j a := by
  have he : MvPolynomial.monomial a c = c • MvPolynomial.monomial a (1 : R) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [he, map_smul, variableDividedDifference_monomial_one]

/-- Equal exponents at the two variables give zero divided difference. -/
@[simp]
theorem monomialQuotient_eq_zero (i j : σ) (a : σ →₀ ℕ) (ha : a i = a j) :
    monomialQuotient R i j a = 0 := by
  simp only [monomialQuotient, ha, lt_self_iff_false, ite_false]

private theorem positive_quotient (a : σ →₀ ℕ) {i j : σ} (hij : i ≠ j) (ha : a j < a i) :
    (MvPolynomial.X i - MvPolynomial.X j) *
        (∑ k ∈ Finset.range (a i - a j),
          MvPolynomial.monomial (replaceExponents a i j (a i - 1 - k) (a j + k)) (1 : R)) =
      MvPolynomial.monomial a 1 -
        MvPolynomial.monomial (replaceExponents a i j (a j) (a i)) 1 := by
  let term : ℕ → MvPolynomial σ R := fun k ↦
    MvPolynomial.monomial (replaceExponents a i j (a i - k) (a j + k)) 1
  rw [sub_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have ht : ∀ k ∈ Finset.range (a i - a j),
      MvPolynomial.X i *
          MvPolynomial.monomial (replaceExponents a i j (a i - 1 - k) (a j + k)) (1 : R) -
        MvPolynomial.X j *
          MvPolynomial.monomial (replaceExponents a i j (a i - 1 - k) (a j + k)) 1 =
      term k - term (k + 1) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [X_mul_replace_left a hij, X_mul_replace_right a hij]
    have he : a i - 1 - k + 1 = a i - k := by omega
    have he' : a i - 1 - k = a i - (k + 1) := by omega
    rw [he]
    simp only [term, he', Nat.add_assoc]
  rw [Finset.sum_congr rfl ht, Finset.sum_range_sub']
  have he : a i - (a i - a j) = a j := by omega
  have he' : a j + (a i - a j) = a i := by omega
  simp only [term, Nat.sub_zero, Nat.add_zero, he, he', replaceExponents_self]

private theorem negative_quotient (a : σ →₀ ℕ) {i j : σ} (hij : i ≠ j) (ha : a i < a j) :
    (MvPolynomial.X i - MvPolynomial.X j) *
        (-∑ k ∈ Finset.range (a j - a i),
          MvPolynomial.monomial (replaceExponents a i j (a i + k) (a j - 1 - k)) (1 : R)) =
      MvPolynomial.monomial a 1 -
        MvPolynomial.monomial (replaceExponents a i j (a j) (a i)) 1 := by
  let term : ℕ → MvPolynomial σ R := fun k ↦
    MvPolynomial.monomial (replaceExponents a i j (a i + k) (a j - k)) 1
  rw [mul_neg, sub_mul, neg_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have ht : ∀ k ∈ Finset.range (a j - a i),
      MvPolynomial.X j *
          MvPolynomial.monomial (replaceExponents a i j (a i + k) (a j - 1 - k)) (1 : R) -
        MvPolynomial.X i *
          MvPolynomial.monomial (replaceExponents a i j (a i + k) (a j - 1 - k)) 1 =
      term k - term (k + 1) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [X_mul_replace_right a hij, X_mul_replace_left a hij]
    have he : a j - 1 - k + 1 = a j - k := by omega
    have he' : a j - 1 - k = a j - (k + 1) := by omega
    rw [he]
    simp only [term, he', Nat.add_assoc]
  rw [Finset.sum_congr rfl ht, Finset.sum_range_sub']
  have he : a i + (a j - a i) = a j := by omega
  have he' : a j - (a j - a i) = a i := by omega
  simp only [term, Nat.sub_zero, Nat.add_zero, he, he', replaceExponents_self]

/-- Multiplying the finite quotient formula by its root recovers the monomial difference. -/
theorem root_mul_monomialQuotient {i j : σ} (hij : i ≠ j) (a : σ →₀ ℕ) :
    (MvPolynomial.X i - MvPolynomial.X j) * monomialQuotient R i j a =
      MvPolynomial.monomial a 1 - variableSwap R i j (MvPolynomial.monomial a 1) := by
  rw [variableSwap_monomial]
  by_cases ha : a j < a i
  · rw [monomialQuotient, ite_eq_left ha]
    exact positive_quotient a hij ha
  · rw [monomialQuotient, ite_eq_right ha]
    by_cases hb : a i < a j
    · rw [ite_eq_left hb]
      exact negative_quotient a hij hb
    · have he : a i = a j := by omega
      rw [ite_eq_right hb, mul_zero]
      have hs : replaceExponents a i j (a j) (a i) = a := by
        simpa only [he] using replaceExponents_self a i j
      rw [hs, sub_self]

end SchubertPolynomial
