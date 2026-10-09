import SchubertForwardStability.SchubertPolynomials.Stability.Extraction
import SchubertForwardStability.Permutations.Statistics.AdjacentLength

/-! # Adjacent divided differences of Schubert polynomials

## Main results

An adjacent divided difference sends a Schubert polynomial to the polynomial of
its right adjacent swap at a descent, and to zero at an ascent.

## Implementation notes

Complementary relative lengths and the nil-Coxeter composition rule prove both
cases directly from the inverse-relative-longest construction over any commutative ring.
-/

namespace SchubertPolynomial

open scoped Classical

variable {R : Type*} [CommRing R]

/-- The permutation operator of an adjacent transposition is its adjacent divided difference. -/
theorem permutationDivided_simple (i : ℕ+) :
    permutationDividedDifference R (FinitaryPerm.simpleTransposition i) =
      dividedDifference R i := by
  have hword : FinitaryPerm.IsReducedWord (FinitaryPerm.simpleTransposition i) [i] := by
    constructor
    · rw [FinitaryPerm.wordProduct_cons, FinitaryPerm.wordProduct_nil, mul_one]
    · simp only [List.length_singleton, FinitaryPerm.length_simpleTransposition]
  rw [permutationDividedDifference_eq [i] hword, wordDividedDifference_cons,
    wordDividedDifference_nil, LinearMap.comp_id]

private theorem simple_relative (w : FinitaryPerm ℕ+) (i : ℕ+) (n : ℕ) :
    FinitaryPerm.simpleTransposition i * (w⁻¹ * FinitaryPerm.longestElement n) =
      (w * FinitaryPerm.simpleTransposition i)⁻¹ * FinitaryPerm.longestElement n := by
  simp only [mul_inv_rev, FinitaryPerm.simpleTransposition, FinitaryPerm.swap_inv, mul_assoc]

/-- An adjacent right descent gives the Schubert polynomial after its adjacent swap. -/
theorem divided_schubert_of_descent (w : FinitaryPerm ℕ+) (i : ℕ+)
    (hi : FinitaryPerm.HasDescent w i) :
    dividedDifference R i (schubert R w) =
      schubert R (w * FinitaryPerm.simpleTransposition i) := by
  let v := w * FinitaryPerm.simpleTransposition i
  let n := max w.forwardStability v.forwardStability
  have hw : FinitaryPerm.IsSupported n w :=
    w.isSupported_forwardStability.mono (le_max_left _ _)
  have hv : FinitaryPerm.IsSupported n v :=
    v.isSupported_forwardStability.mono (le_max_right _ _)
  have hadd : (FinitaryPerm.simpleTransposition i *
      (w⁻¹ * FinitaryPerm.longestElement n)).length =
      (FinitaryPerm.simpleTransposition i).length +
        (w⁻¹ * FinitaryPerm.longestElement n).length := by
    rw [simple_relative, FinitaryPerm.length_simpleTransposition]
    change (v⁻¹ * FinitaryPerm.longestElement n).length =
      1 + (w⁻¹ * FinitaryPerm.longestElement n).length
    have hdrop := FinitaryPerm.length_mul_simple_of_descent w i hi
    have hrelw := FinitaryPerm.length_inv_mul_longest w hw
    have hrelv := FinitaryPerm.length_inv_mul_longest v hv
    change v.length + 1 = w.length at hdrop
    omega
  rw [← permutationDivided_simple, schubert_eq_ambient w n (le_max_left _ _),
    ambientSchubert, ← LinearMap.comp_apply, ← permutationDividedDifference_mul _ _ hadd,
    simple_relative]
  exact ambientSchubert_eq_schubert v hv

/-- An adjacent right ascent annihilates a Schubert polynomial. -/
theorem divided_schubert_of_ascent (w : FinitaryPerm ℕ+) (i : ℕ+)
    (hi : w i < w (i + 1)) : dividedDifference R i (schubert R w) = 0 := by
  let v := w * FinitaryPerm.simpleTransposition i
  let n := max w.forwardStability v.forwardStability
  have hw : FinitaryPerm.IsSupported n w :=
    w.isSupported_forwardStability.mono (le_max_left _ _)
  have hv : FinitaryPerm.IsSupported n v :=
    v.isSupported_forwardStability.mono (le_max_right _ _)
  have hnot : (FinitaryPerm.simpleTransposition i *
      (w⁻¹ * FinitaryPerm.longestElement n)).length ≠
      (FinitaryPerm.simpleTransposition i).length +
        (w⁻¹ * FinitaryPerm.longestElement n).length := by
    rw [simple_relative, FinitaryPerm.length_simpleTransposition]
    change (v⁻¹ * FinitaryPerm.longestElement n).length ≠
      1 + (w⁻¹ * FinitaryPerm.longestElement n).length
    have hrise := FinitaryPerm.length_mul_simple_of_ascent w i hi
    have hrelw := FinitaryPerm.length_inv_mul_longest w hw
    have hrelv := FinitaryPerm.length_inv_mul_longest v hv
    change w.length + 1 = v.length at hrise
    omega
  rw [← permutationDivided_simple, schubert_eq_ambient w n (le_max_left _ _),
    ambientSchubert, ← LinearMap.comp_apply, permutationDividedDifference_mul_zero _ _ hnot,
    LinearMap.zero_apply]

/-- The adjacent divided-difference action is the right-swap polynomial at a descent
and zero otherwise. -/
theorem divided_schubert (w : FinitaryPerm ℕ+) (i : ℕ+) :
    dividedDifference R i (schubert R w) =
      if FinitaryPerm.HasDescent w i then
        schubert R (w * FinitaryPerm.simpleTransposition i) else 0 := by
  classical
  by_cases hi : FinitaryPerm.HasDescent w i
  · rw [ite_eq_left hi]
    exact divided_schubert_of_descent w i hi
  · rw [ite_eq_right hi]
    apply divided_schubert_of_ascent
    have hij : i < i + 1 := Nat.lt_succ_self (i : ℕ)
    have hne : w i ≠ w (i + 1) := fun he => hij.ne (w.injective he)
    exact lt_of_le_of_ne (not_lt.mp hi) hne

end SchubertPolynomial
