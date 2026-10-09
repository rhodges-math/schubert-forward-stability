import SchubertForwardStability.SchubertPolynomials.Stability.Construction
import SchubertForwardStability.SchubertPolynomials.Stability.Cycle

/-! # Ambient stability of Schubert polynomials

## Main results

Appending a fixed point does not change a supported permutation's Schubert polynomial.
The construction therefore agrees in every ambient size at least its support bound.

## Implementation notes

The successive-longest factor has additive relative length. Its action
lowers the next staircase, including the empty-interval boundary case.

## References

L. Manivel, *Symmetric functions, Schubert polynomials and degeneracy loci*, Sections 2.3--2.5.
-/

namespace SchubertPolynomial

variable {R : Type*} [CommRing R]

/-- Appending one fixed point preserves the ambient polynomial, as in Manivel, Sections 2.3--2.5. -/
theorem ambientSchubert_succ (n : ℕ) (w : FinitaryPerm ℕ+) (hw : FinitaryPerm.IsSupported n w) :
    ambientSchubert R (n + 1) w = ambientSchubert R n w := by
  have hm : (w⁻¹ * FinitaryPerm.longestElement n) *
      (FinitaryPerm.longestElement n * FinitaryPerm.longestElement (n + 1)) =
        w⁻¹ * FinitaryPerm.longestElement (n + 1) := by
    calc (w⁻¹ * FinitaryPerm.longestElement n) *
        (FinitaryPerm.longestElement n * FinitaryPerm.longestElement (n + 1)) =
          w⁻¹ * (FinitaryPerm.longestElement n * FinitaryPerm.longestElement n) *
            FinitaryPerm.longestElement (n + 1) := by simp only [mul_assoc]
      _ = w⁻¹ * FinitaryPerm.longestElement (n + 1) := by
        rw [FinitaryPerm.longestElement_mul_self, mul_one]
  have hadd : ((w⁻¹ * FinitaryPerm.longestElement n) *
      (FinitaryPerm.longestElement n * FinitaryPerm.longestElement (n + 1))).length =
        (w⁻¹ * FinitaryPerm.longestElement n).length +
          (FinitaryPerm.longestElement n * FinitaryPerm.longestElement (n + 1)).length := by
    rw [hm]
    exact FinitaryPerm.length_relative_succ_add w hw
  have hop := permutationDividedDifference_mul (R := R)
    (w⁻¹ * FinitaryPerm.longestElement n)
    (FinitaryPerm.longestElement n * FinitaryPerm.longestElement (n + 1)) hadd
  rw [hm] at hop
  rw [ambientSchubert, ambientSchubert, hop, LinearMap.comp_apply,
    permutationDividedDifference_staircase]

/-- Increasing an ambient support bound preserves the constructed polynomial. -/
theorem ambientSchubert_eq {m n : ℕ} (w : FinitaryPerm ℕ+)
    (hw : FinitaryPerm.IsSupported m w) (hmn : m ≤ n) :
    ambientSchubert R n w = ambientSchubert R m w := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => rw [Nat.add_zero]
  | succ k ih =>
    rw [Nat.add_succ, ambientSchubert_succ (m + k) w (hw.mono (by omega)), ih (by omega)]

/-- The Schubert polynomial equals its formula at every sufficiently large ambient size. -/
theorem schubert_eq_ambient (w : FinitaryPerm ℕ+) (n : ℕ) (hn : w.forwardStability ≤ n) :
    schubert R w = ambientSchubert R n w := by
  exact (ambientSchubert_eq w w.isSupported_forwardStability hn).symm

/-- A supported permutation's Schubert polynomial has its ambient divided-difference formula. -/
theorem schubert_eq_word {n : ℕ} (w : FinitaryPerm ℕ+) (hn : w.forwardStability ≤ n)
    (word : List ℕ+)
    (hword : FinitaryPerm.IsReducedWord (w⁻¹ * FinitaryPerm.longestElement n) word) :
    schubert R w = wordDividedDifference R word (staircaseMonomial R n) := by
  rw [schubert_eq_ambient w n hn, ambientSchubert_eq_word n w word hword]

/-- Identity has ambient Schubert polynomial one at every size. -/
theorem ambientSchubert_one (n : ℕ) : ambientSchubert R n (1 : FinitaryPerm ℕ+) = 1 := by
  rw [ambientSchubert_eq 1 (FinitaryPerm.isSupported_one 0) (Nat.zero_le n), ambientSchubert_zero]

/-- The Schubert polynomial of every longest element is its staircase monomial. -/
theorem schubert_longestElement (n : ℕ) :
    schubert R (FinitaryPerm.longestElement n) = staircaseMonomial R n := by
  by_cases hn : n = 0
  · subst n
    rw [FinitaryPerm.longestElement_zero, schubert_one, staircaseMonomial_zero]
  · have hpos : 1 ≤ n := by omega
    rw [schubert_eq_ambient (FinitaryPerm.longestElement n) n
      ((FinitaryPerm.forwardStability_le_iff _ hpos).mpr
        (FinitaryPerm.isSupported_longestElement n)), ambientSchubert_longest]

end SchubertPolynomial
