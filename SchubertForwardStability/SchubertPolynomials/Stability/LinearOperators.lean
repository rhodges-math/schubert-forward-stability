import SchubertForwardStability.SchubertPolynomials.Stability.Simple
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import SchubertForwardStability.Permutations.Classes.Intervals.WordCuts

/-! # Linear forms through divided-difference words

## Main definitions

* `linearForm`: a finite linear combination of polynomial variables.

## Main results

Adjacent divided differences differentiate a linear form by the difference of its
two adjacent coefficients. The twisted product rule transports those coefficients.

## Implementation notes

Coefficients are finitely supported over an arbitrary commutative ring.
-/

namespace SchubertPolynomial

open FinitaryPerm
open scoped Classical BigOperators

variable {R : Type*} [CommRing R]

/-- The linear map sending a finite coefficient vector to its linear polynomial. -/
noncomputable def linearForm (R : Type*) [CommRing R] :
    (ℕ+ →₀ R) →ₗ[R] MvPolynomial ℕ+ R :=
  Finsupp.linearCombination R (fun j => MvPolynomial.X j)

/-- A linear form is the finite sum of its coefficients times the variables. -/
theorem linearForm_apply (a : ℕ+ →₀ R) :
    linearForm R a = ∑ j ∈ a.support, MvPolynomial.C (a j) * MvPolynomial.X j := by
  simp only [linearForm, Finsupp.linearCombination_apply, Finsupp.sum,
    MvPolynomial.smul_eq_C_mul]

/-- A singleton coefficient vector produces its one-variable linear monomial. -/
theorem linearForm_single (j : ℕ+) (r : R) :
    linearForm R (Finsupp.single j r) = r • MvPolynomial.X j :=
  Finsupp.linearCombination_single R r j

/-- Adjacent divided differences of a linear form are adjacent coefficient differences. -/
theorem dividedDifference_linearForm (i : ℕ+) (a : ℕ+ →₀ R) :
    dividedDifference R i (linearForm R a) = MvPolynomial.C (a i - a (i + 1)) := by
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply, sub_self]
  | add a b ha hb =>
    simp only [map_add, ha, hb, Finsupp.add_apply]
    rw [← MvPolynomial.C_add]
    congr 1
    ring
  | single j r =>
    rw [linearForm_single, map_smul]
    have hn : i ≠ i + 1 := (show i < i + 1 from Nat.lt_succ_self (i : ℕ)).ne
    by_cases hj : j = i
    · subst j
      simp only [dividedDifference_X, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne hn.symm, sub_zero, MvPolynomial.smul_eq_C_mul, mul_one]
    · by_cases hj' : j = i + 1
      · subst j
        simp only [dividedDifference_X_next, Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne hn, zero_sub, MvPolynomial.C_neg,
          MvPolynomial.smul_eq_C_mul, mul_neg, mul_one]
      · simp only [dividedDifference_X_other i j hj hj', Finsupp.single_eq_of_ne (Ne.symm hj),
          Finsupp.single_eq_of_ne (Ne.symm hj'), sub_self, MvPolynomial.C_0, smul_zero]

/-- Variable swapping transports the finite coefficient vector by the same transposition. -/
theorem linearForm_swap (i : ℕ+) (a : ℕ+ →₀ R) :
    linearForm R (a.equivMapDomain (Equiv.swap i (i + 1))) =
      variableSwap R i (i + 1) (linearForm R a) := by
  simp only [linearForm, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_equivMapDomain]
  simp only [Finsupp.sum, map_sum, map_smul, variableSwap, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X]
  have hd : (fun a b : ℕ+ => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq ℕ+) := Subsingleton.elim _ _
  rw [hd]

/-- The adjacent product rule with a finite linear form and transported coefficients. -/
theorem dividedDifference_linear_mul (i : ℕ+) (a : ℕ+ →₀ R)
    (p : MvPolynomial ℕ+ R) :
    dividedDifference R i (linearForm R a * p) =
      linearForm R (a.equivMapDomain (Equiv.swap i (i + 1))) * dividedDifference R i p +
        (a i - a (i + 1)) • p := by
  rw [dividedDifference_mul, dividedDifference_linearForm, ← linearForm_swap,
    MvPolynomial.smul_eq_C_mul, add_comm]

/-- Coefficients transported by the variable action of a displayed word. -/
def wordCoefficients : List ℕ+ → (ℕ+ →₀ R) → ℕ+ →₀ R
  | [], a => a
  | i :: word, a => (wordCoefficients word a).equivMapDomain (Equiv.swap i (i + 1))

/-- Transported coefficients are original coefficients at inverse-permuted positions. -/
theorem wordCoefficients_apply (word : List ℕ+) (a : ℕ+ →₀ R) (j : ℕ+) :
    wordCoefficients word a j = a ((wordProduct word)⁻¹ j) := by
  induction word generalizing j with
  | nil => simp only [wordCoefficients, wordProduct_nil, inv_one, one_apply]
  | cons i word ih =>
    simp only [wordCoefficients, Finsupp.equivMapDomain_apply, Equiv.symm_swap, ih,
      wordProduct_cons, mul_inv_rev, mul_apply, simpleTransposition, swap_inv]
    rfl

/-- A selected letter contributes its suffix-transported coefficient and deleted operator. -/
noncomputable def wordDeletionTerm (a : ℕ+ →₀ R) (c : List ℕ+ × ℕ+ × List ℕ+)
    (p : MvPolynomial ℕ+ R) : MvPolynomial ℕ+ R :=
  (wordCoefficients c.2.2 a c.2.1 - wordCoefficients c.2.2 a (c.2.1 + 1)) •
    wordDividedDifference R (c.1 ++ c.2.2) p

/-- Iterated twisted Leibniz gives the exact deleted-letter expansion for a linear factor. -/
theorem wordDivided_linearForm (word : List ℕ+) (a : ℕ+ →₀ R)
    (p : MvPolynomial ℕ+ R) :
    wordDividedDifference R word (linearForm R a * p) =
      linearForm R (wordCoefficients word a) * wordDividedDifference R word p +
        ((wordCuts word).map (fun c => wordDeletionTerm a c p)).sum := by
  induction word with
  | nil => simp only [wordDividedDifference_nil, LinearMap.id_apply, wordCoefficients,
      wordCuts, List.map_nil, List.sum_nil, add_zero]
  | cons i word ih =>
    rw [wordDividedDifference_cons, LinearMap.comp_apply, ih, map_add,
      dividedDifference_linear_mul]
    simp only [wordCoefficients, wordCuts, List.map_cons, List.sum_cons, List.map_map,
      wordDeletionTerm, List.nil_append, map_list_sum, Function.comp_def, map_smul,
      List.cons_append,
      wordDividedDifference_cons, LinearMap.comp_apply]
    rw [add_assoc]

end SchubertPolynomial
