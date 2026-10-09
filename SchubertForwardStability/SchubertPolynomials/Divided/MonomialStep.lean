import SchubertForwardStability.SchubertPolynomials.Divided.Basic

/-! # A one-step divided difference on monomials

## Main results

When the first exponent exceeds the second by one, the divided difference
lowers that first exponent to the second and leaves all other exponents unchanged.

## Implementation notes

The variable carrier and commutative coefficient ring are arbitrary. The geometric
sum consists of one term, so no nonvanishing or domain assumption is needed.
-/

namespace SchubertPolynomial

variable {σ R : Type*} [CommRing R]

/-- A monomial with adjacent exponent gap one loses one at the first variable. -/
theorem variableDividedDifference_monomial_step {i j : σ} (hij : i ≠ j)
    (a : σ →₀ ℕ) (hstep : a i = a j + 1) :
    variableDividedDifference R i j (MvPolynomial.monomial a 1) =
      MvPolynomial.monomial (a.update i (a j)) 1 := by
  classical
  have hlt : a j < a i := by omega
  have hdiff : a i - a j = 1 := by omega
  rw [variableDividedDifference_monomial_one, monomialQuotient, ite_eq_left hlt, hdiff]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.sub_zero, Nat.add_zero]
  have he : replaceExponents a i j (a i - 1) (a j) = a.update i (a j) := by
    rw [hstep, Nat.add_sub_cancel, replaceExponents]
    apply Finsupp.ext
    intro k
    by_cases hki : k = i
    · subst k
      simp only [Finsupp.update_apply, hij, ite_false, ite_true]
    · by_cases hkj : k = j
      · subst k
        simp only [Finsupp.update_apply, hki, ite_false, ite_true]
      · simp only [Finsupp.update_apply, hki, hkj, ite_false]
  rw [he]

end SchubertPolynomial
