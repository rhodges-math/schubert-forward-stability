import Mathlib.Data.Finsupp.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename

/-! # Two-variable exponent replacements

## Main definitions

* `replaceExponents`: replace two entries of a finite monomial exponent function.
* `variableSwap`: exchange the two indexed polynomial variables.

## Main results

The replacement evaluations, multiplication shifts and swapped-monomial formula
provide the exponent API for polynomial divided differences.

## Implementation notes

The variable carrier is arbitrary. Distinctness of the two variables is explicit
where a replacement at the second position could overwrite the first.
-/

namespace SchubertPolynomial

open scoped Classical

variable {σ R : Type*} [CommRing R]

/-- Replace the exponents at two indexed variables. -/
noncomputable def replaceExponents (a : σ →₀ ℕ) (i j : σ) (p q : ℕ) : σ →₀ ℕ :=
  (a.update i p).update j q

/-- Replacing two distinct exponents gives the first specified value at the first variable. -/
@[simp]
theorem replaceExponents_left (a : σ →₀ ℕ) {i j : σ} (hij : i ≠ j) (p q : ℕ) :
    replaceExponents a i j p q i = p := by
  simp [replaceExponents, Finsupp.update_apply, hij]

/-- The second replacement value is the exponent at the second variable. -/
@[simp]
theorem replaceExponents_right (a : σ →₀ ℕ) (i j : σ) (p q : ℕ) :
    replaceExponents a i j p q j = q := by
  simp [replaceExponents, Finsupp.update_apply]

/-- Exponents away from the two indexed variables are unchanged. -/
theorem replaceExponents_other (a : σ →₀ ℕ) (i j : σ) (p q : ℕ) {k : σ}
    (hki : k ≠ i) (hkj : k ≠ j) : replaceExponents a i j p q k = a k := by
  simp [replaceExponents, Finsupp.update_apply, hki, hkj]

/-- Restoring both initial exponents recovers the initial exponent function. -/
@[simp]
theorem replaceExponents_self (a : σ →₀ ℕ) (i j : σ) :
    replaceExponents a i j (a i) (a j) = a := by
  simp only [replaceExponents, Finsupp.update_self]

/-- Adding one at the first variable increments the first replacement exponent. -/
theorem single_add_replace_left (a : σ →₀ ℕ) {i j : σ} (hij : i ≠ j) (p q : ℕ) :
    Finsupp.single i 1 + replaceExponents a i j p q =
      replaceExponents a i j (p + 1) q := by
  ext k
  by_cases hki : k = i
  · subst k
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, replaceExponents_left a hij]
    omega
  · by_cases hkj : k = j
    · subst k
      simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hij.symm,
        replaceExponents_right, zero_add]
    · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hki,
        replaceExponents_other a i j _ _ hki hkj, zero_add]

/-- Adding one at the second variable increments the second replacement exponent. -/
theorem single_add_replace_right (a : σ →₀ ℕ) {i j : σ} (hij : i ≠ j) (p q : ℕ) :
    Finsupp.single j 1 + replaceExponents a i j p q =
      replaceExponents a i j p (q + 1) := by
  ext k
  by_cases hki : k = i
  · subst k
    simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hij,
      replaceExponents_left a hij, zero_add]
  · by_cases hkj : k = j
    · subst k
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, replaceExponents_right]
      omega
    · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hkj,
        replaceExponents_other a i j _ _ hki hkj, zero_add]

/-- Multiplying a coefficient-one replacement monomial by the first variable shifts its exponent. -/
theorem X_mul_replace_left (a : σ →₀ ℕ) {i j : σ} (hij : i ≠ j) (p q : ℕ) :
    MvPolynomial.X i * MvPolynomial.monomial (replaceExponents a i j p q) (1 : R) =
      MvPolynomial.monomial (replaceExponents a i j (p + 1) q) 1 := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial,
    single_add_replace_left a hij, one_mul]

/-- Multiplying a coefficient-one replacement monomial by the second variable
shifts its exponent. -/
theorem X_mul_replace_right (a : σ →₀ ℕ) {i j : σ} (hij : i ≠ j) (p q : ℕ) :
    MvPolynomial.X j * MvPolynomial.monomial (replaceExponents a i j p q) (1 : R) =
      MvPolynomial.monomial (replaceExponents a i j p (q + 1)) 1 := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial,
    single_add_replace_right a hij, one_mul]

/-- The algebra automorphism exchanging two indexed variables. -/
noncomputable def variableSwap (R : Type*) [CommRing R] (i j : σ) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R := MvPolynomial.renameEquiv R (Equiv.swap i j)

/-- Swapping variables exchanges the first variable with the second. -/
@[simp]
theorem variableSwap_X_left (i j : σ) : variableSwap R i j (MvPolynomial.X i) =
    MvPolynomial.X j := by
  simp only [variableSwap, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    Equiv.swap_apply_left]

/-- Swapping variables exchanges the second variable with the first. -/
@[simp]
theorem variableSwap_X_right (i j : σ) : variableSwap R i j (MvPolynomial.X j) =
    MvPolynomial.X i := by
  simp only [variableSwap, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    Equiv.swap_apply_right]

/-- Swapping variables fixes every other variable. -/
@[simp]
theorem variableSwap_X_other (i j k : σ) (hki : k ≠ i) (hkj : k ≠ j) :
    variableSwap R i j (MvPolynomial.X k) = MvPolynomial.X k := by
  simp only [variableSwap, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- Applying the same variable swap twice is the identity. -/
@[simp]
theorem variableSwap_involutive (i j : σ) (p : MvPolynomial σ R) :
    variableSwap R i j (variableSwap R i j p) = p := by
  simp only [variableSwap, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]
  have he : (Equiv.swap i j : σ → σ) ∘ Equiv.swap i j = id := by
    funext k
    exact Equiv.swap_apply_self i j k
  rw [he, MvPolynomial.rename_id_apply]

/-- Renaming by a swap exchanges the two monomial exponents. -/
theorem mapDomain_swap (a : σ →₀ ℕ) (i j : σ) :
    Finsupp.mapDomain (Equiv.swap i j) a = replaceExponents a i j (a j) (a i) := by
  by_cases hij : i = j
  · subst j
    rw [Equiv.swap_self, replaceExponents_self]
    exact Finsupp.mapDomain_id
  · ext k
    rw [Finsupp.mapDomain_equiv_apply]
    by_cases hki : k = i
    · subst k
      simp only [Equiv.symm_swap, Equiv.swap_apply_left, replaceExponents_left a hij]
    · by_cases hkj : k = j
      · subst k
        simp only [Equiv.symm_swap, Equiv.swap_apply_right, replaceExponents_right]
      · simp only [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hki hkj,
          replaceExponents_other a i j _ _ hki hkj]

/-- Variable swaps act on a monomial by exchanging its indexed exponents. -/
@[simp]
theorem variableSwap_monomial (i j : σ) (a : σ →₀ ℕ) (c : R) :
    variableSwap R i j (MvPolynomial.monomial a c) =
      MvPolynomial.monomial (replaceExponents a i j (a j) (a i)) c := by
  rw [variableSwap, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_monomial,
    mapDomain_swap]

end SchubertPolynomial
