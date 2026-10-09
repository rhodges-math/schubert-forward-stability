import SchubertForwardStability.SchubertPolynomials.Divided.Independence
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Homogeneous degrees of divided differences

## Main results

Replacing two distinct exponents preserves their total-degree balance. Every
monomial term in a divided difference has degree one less than its input.
Adjacent, word and permutation operators consequently lower homogeneous degrees
by their respective numbers of letters.

## Implementation notes

Degrees use natural subtraction. The zero polynomial is homogeneous in every
degree, so the statements include inputs below the operator length and arbitrary
commutative coefficient rings.
-/

namespace SchubertPolynomial

variable {σ R : Type*} [CommRing R]

private theorem degree_update_balance (a : σ →₀ ℕ) (i : σ) (p : ℕ) :
    (a.update i p).degree + a i = a.degree + p := by
  exact Finsupp.sum_update_add a i p (fun _ m => m) (fun _ => rfl)
    (fun _ _ _ => rfl)

/-- Replacing two distinct exponents balances their old and new total degrees. -/
theorem replaceExponents_degree (a : σ →₀ ℕ) {i j : σ} (hij : i ≠ j) (p q : ℕ) :
    (replaceExponents a i j p q).degree + a i + a j = a.degree + p + q := by
  classical
  have hi := degree_update_balance a i p
  have hj := degree_update_balance (a.update i p) j q
  rw [Finsupp.update_apply, ite_eq_right hij.symm] at hj
  change (replaceExponents a i j p q).degree + a j = (a.update i p).degree + q at hj
  omega

/-- The coefficient-one monomial quotient has homogeneous degree one below its exponent. -/
theorem monomialQuotient_isHomogeneous {i j : σ} (hij : i ≠ j) (a : σ →₀ ℕ) :
    (monomialQuotient R i j a).IsHomogeneous (a.degree - 1) := by
  classical
  unfold monomialQuotient
  split_ifs with hpos hneg
  · apply MvPolynomial.IsHomogeneous.sum
    intro k hk
    apply MvPolynomial.isHomogeneous_monomial
    have hbalance := replaceExponents_degree a hij (a i - 1 - k) (a j + k)
    have hbound := Finset.mem_range.mp hk
    omega
  · apply MvPolynomial.IsHomogeneous.neg
    apply MvPolynomial.IsHomogeneous.sum
    intro k hk
    apply MvPolynomial.isHomogeneous_monomial
    have hbalance := replaceExponents_degree a hij (a i + k) (a j - 1 - k)
    have hbound := Finset.mem_range.mp hk
    omega
  · exact (MvPolynomial.homogeneousSubmodule σ R (a.degree - 1)).zero_mem

/-- A two-variable divided difference lowers homogeneous degree by one. -/
theorem variableDivided_isHomogeneous {i j : σ} (hij : i ≠ j)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    (variableDividedDifference R i j p).IsHomogeneous (d - 1) := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply MvPolynomial.IsHomogeneous.sum
  intro a ha
  rw [variableDividedDifference_monomial]
  have hdegree : a.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp ha)
  have hq := monomialQuotient_isHomogeneous (R := R) hij a
  rw [hdegree] at hq
  exact (MvPolynomial.homogeneousSubmodule σ R (d - 1)).smul_mem (p.coeff a) hq

/-- An adjacent divided difference lowers homogeneous degree by one. -/
theorem dividedDifference_isHomogeneous (i : ℕ+) {p : MvPolynomial ℕ+ R} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    (dividedDifference R i p).IsHomogeneous (d - 1) := by
  have hij : i ≠ i + 1 := by
    intro h
    have hv := congrArg PNat.val h
    change (i : ℕ) = (i : ℕ) + 1 at hv
    omega
  exact variableDivided_isHomogeneous hij hp

/-- A word of adjacent divided differences lowers homogeneous degree by its length. -/
theorem wordDivided_isHomogeneous (word : List ℕ+) {p : MvPolynomial ℕ+ R} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    (wordDividedDifference R word p).IsHomogeneous (d - word.length) := by
  induction word with
  | nil => simpa only [wordDividedDifference_nil, LinearMap.id_apply, List.length_nil,
      Nat.sub_zero] using hp
  | cons i word ih =>
    rw [wordDividedDifference_cons, LinearMap.comp_apply]
    simpa only [List.length_cons, Nat.sub_sub, Nat.add_comm] using
      dividedDifference_isHomogeneous i ih

/-- A permutation divided difference lowers homogeneous degree by inversion length. -/
theorem permutationDivided_isHomogeneous (w : FinitaryPerm ℕ+)
    {p : MvPolynomial ℕ+ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    (permutationDividedDifference R w p).IsHomogeneous (d - w.length) := by
  have h := wordDivided_isHomogeneous w.lexFirstReducedWord hp
  rw [w.isReducedWordIn_lexFirst.1.2] at h
  exact h

/-- A two-variable divided difference annihilates a polynomial homogeneous of degree zero. -/
theorem variableDivided_homogeneous_zero {i j : σ} (hij : i ≠ j)
    {p : MvPolynomial σ R} (hp : p.IsHomogeneous 0) :
    variableDividedDifference R i j p = 0 := by
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    (Nat.eq_zero_of_le_zero hp.totalDegree_le)
  rw [hc, variableDividedDifference_C hij]

/-- An adjacent divided difference annihilates a polynomial homogeneous of degree zero. -/
theorem dividedDifference_homogeneous_zero (i : ℕ+) {p : MvPolynomial ℕ+ R}
    (hp : p.IsHomogeneous 0) : dividedDifference R i p = 0 := by
  have hij : i ≠ i + 1 := by
    intro h
    have hv := congrArg PNat.val h
    change (i : ℕ) = (i : ℕ) + 1 at hv
    omega
  exact variableDivided_homogeneous_zero hij hp

/-- A word longer than a homogeneous degree annihilates that polynomial. -/
theorem wordDivided_zero_of_degree_lt (word : List ℕ+) {p : MvPolynomial ℕ+ R}
    {d : ℕ} (hp : p.IsHomogeneous d) (hd : d < word.length) :
    wordDividedDifference R word p = 0 := by
  induction word with
  | nil => simp only [List.length_nil] at hd; omega
  | cons i word ih =>
    rw [wordDividedDifference_cons, LinearMap.comp_apply]
    by_cases ht : d < word.length
    · rw [ih ht, map_zero]
    · have he : word.length = d := by
        rw [List.length_cons] at hd
        omega
      have hh := wordDivided_isHomogeneous word hp
      rw [he, Nat.sub_self] at hh
      exact dividedDifference_homogeneous_zero i hh

/-- A permutation operator annihilates homogeneous degrees below its inversion length. -/
theorem permutationDivided_zero_of_degree_lt (w : FinitaryPerm ℕ+)
    {p : MvPolynomial ℕ+ R} {d : ℕ} (hp : p.IsHomogeneous d) (hd : d < w.length) :
    permutationDividedDifference R w p = 0 := by
  apply wordDivided_zero_of_degree_lt w.lexFirstReducedWord hp
  rw [w.isReducedWordIn_lexFirst.1.2]
  exact hd

end SchubertPolynomial
