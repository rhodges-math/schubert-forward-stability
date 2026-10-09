import SchubertForwardStability.SchubertPolynomials.Stability.Ambient

/-! # Extraction of Schubert polynomials by permutation operators

## Main results

The longest operator sends its staircase to one. The operator of a permutation
sends its own Schubert polynomial to one. These polynomials are therefore nonzero
over every nontrivial commutative coefficient ring.

## Implementation notes

The proof uses ambient stability and complementary relative lengths. It does not
use a Schubert basis or positivity theorem.
-/

namespace SchubertPolynomial

variable {R : Type*} [CommRing R]

/-- For every ambient size bounding the support, the ambient formula equals the Schubert
polynomial, including size zero. -/
theorem ambientSchubert_eq_schubert {n : ℕ} (w : FinitaryPerm ℕ+)
    (hw : FinitaryPerm.IsSupported n w) : ambientSchubert R n w = schubert R w := by
  calc ambientSchubert R n w = ambientSchubert R (max n w.forwardStability) w :=
      (ambientSchubert_eq w hw (le_max_left _ _)).symm
    _ = schubert R w := (schubert_eq_ambient w _ (le_max_right _ _)).symm

/-- The longest permutation operator extracts one from its staircase monomial. -/
theorem permutationDividedDifference_top (n : ℕ) :
    permutationDividedDifference R (FinitaryPerm.longestElement n)
      (staircaseMonomial R n) = 1 := by
  simpa only [ambientSchubert, inv_one, one_mul] using ambientSchubert_one (R := R) n

/-- A supported permutation's operator extracts one from its ambient Schubert polynomial. -/
theorem permutationDivided_ambient_self {n : ℕ} (w : FinitaryPerm ℕ+)
    (hw : FinitaryPerm.IsSupported n w) :
    permutationDividedDifference R w (ambientSchubert R n w) = 1 := by
  have hm : w * (w⁻¹ * FinitaryPerm.longestElement n) =
      FinitaryPerm.longestElement n := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hadd : (w * (w⁻¹ * FinitaryPerm.longestElement n)).length =
      w.length + (w⁻¹ * FinitaryPerm.longestElement n).length := by
    rw [hm]
    have h := FinitaryPerm.length_inv_mul_longest w hw
    omega
  have hop := permutationDividedDifference_mul (R := R) w
    (w⁻¹ * FinitaryPerm.longestElement n) hadd
  rw [hm] at hop
  rw [ambientSchubert, ← LinearMap.comp_apply, ← hop, permutationDividedDifference_top]

/-- The divided-difference operator of a permutation sends its Schubert polynomial to
one. -/
theorem permutationDivided_schubert_self (w : FinitaryPerm ℕ+) :
    permutationDividedDifference R w (schubert R w) = 1 :=
  permutationDivided_ambient_self w w.isSupported_forwardStability

/-- Schubert polynomials are nonzero over any nontrivial commutative ring. -/
theorem schubert_ne_zero [Nontrivial R] (w : FinitaryPerm ℕ+) : schubert R w ≠ 0 := by
  intro hz
  have h := permutationDivided_schubert_self (R := R) w
  rw [hz, map_zero] at h
  exact zero_ne_one h

end SchubertPolynomial
