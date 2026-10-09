import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

/-! # Degrees of nonnegative integer polynomial sums

This file contains general results that extend Mathlib.

## Main results

Nonnegative integer coefficients are preserved by addition, multiplication and
finite sums. They prevent support cancellation, so additive and finite-sum variable
degrees equal the maximum or finite supremum of their summand degrees.

## Implementation notes

Zero polynomials and empty index sets are included. The integer coefficient order
is essential for the support-union equality.
-/

namespace MvPolynomial

open scoped Classical BigOperators

variable {σ ι : Type*}

/-- Multiplication preserves nonnegative integer coefficients. -/
theorem coeff_mul_nonneg {p q : MvPolynomial σ ℤ}
    (hp : ∀ m, 0 ≤ p.coeff m) (hq : ∀ m, 0 ≤ q.coeff m) (m : σ →₀ ℕ) :
    0 ≤ (p * q).coeff m := by
  classical
  rw [coeff_mul]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hp j.1) (hq j.2)

/-- Addition preserves nonnegative integer coefficients. -/
theorem coeff_add_nonneg {p q : MvPolynomial σ ℤ}
    (hp : ∀ m, 0 ≤ p.coeff m) (hq : ∀ m, 0 ≤ q.coeff m) (m : σ →₀ ℕ) :
    0 ≤ (p + q).coeff m := by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact add_nonneg (hp m) (hq m)

/-- A finite sum of polynomials with nonnegative integer coefficients is nonnegative. -/
theorem coeff_finsetSum_nonneg (s : Finset ι) (f : ι → MvPolynomial σ ℤ)
    (hf : ∀ j ∈ s, ∀ m, 0 ≤ (f j).coeff m) (m : σ →₀ ℕ) :
    0 ≤ (∑ j ∈ s, f j).coeff m := by
  change 0 ≤ (lcoeff ℤ m) (∑ j ∈ s, f j)
  rw [map_sum]
  exact Finset.sum_nonneg fun j hj => hf j hj m

/-- Nonnegative integer coefficients prevent cancellation of either summand's support. -/
theorem support_add_eq_union_of_nonneg {p q : MvPolynomial σ ℤ}
    (hp : ∀ m, 0 ≤ p.coeff m) (hq : ∀ m, 0 ≤ q.coeff m) :
    (p + q).support = p.support ∪ q.support := by
  classical
  ext m
  simp only [mem_support_iff, Finset.mem_union, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply]
  have hp0 := hp m
  have hq0 := hq m
  omega

/-- The degree of a sum with nonnegative integer coefficients is the summand maximum. -/
theorem degreeOf_add_eq_max_of_nonneg (i : σ) {p q : MvPolynomial σ ℤ}
    (hp : ∀ m, 0 ≤ p.coeff m) (hq : ∀ m, 0 ≤ q.coeff m) :
    (p + q).degreeOf i = max (p.degreeOf i) (q.degreeOf i) := by
  classical
  simp only [degreeOf_eq_sup, support_add_eq_union_of_nonneg hp hq, Finset.sup_union]

/-- A finite sum of nonnegative integer polynomials has the supremum of their degrees. -/
theorem degreeOf_sum_eq_sup_of_nonneg (i : σ) (s : Finset ι)
    (f : ι → MvPolynomial σ ℤ) (hf : ∀ j ∈ s, ∀ m, 0 ≤ (f j).coeff m) :
    (∑ j ∈ s, f j).degreeOf i = s.sup fun j => (f j).degreeOf i := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro hf; simp
  | @insert j s hj ih =>
    intro hf
    have hs : ∀ k ∈ s, ∀ m, 0 ≤ (f k).coeff m :=
      fun k hk => hf k (Finset.mem_insert_of_mem hk)
    rw [Finset.sum_insert hj,
      degreeOf_add_eq_max_of_nonneg i (hf j (Finset.mem_insert_self _ _))
        (coeff_finsetSum_nonneg s f hs), ih hs, Finset.sup_insert]

end MvPolynomial
