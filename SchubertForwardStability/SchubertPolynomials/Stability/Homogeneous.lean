import SchubertForwardStability.SchubertPolynomials.Divided.Homogeneous
import SchubertForwardStability.SchubertPolynomials.Stability.Extraction

/-! # Homogeneous degrees of Schubert polynomials

## Main results

The staircase exponent has the inversion length of its ambient longest element.
The Schubert polynomial of a supported permutation is homogeneous in its own
inversion length, independently of the ambient size.

## Implementation notes

Successive lowering balances total exponent degrees. The descending-cycle length
gives the identical recursion for longest-element inversion lengths. Natural
subtraction then uses the complementary relative length.
-/

namespace SchubertPolynomial

private theorem lowered_degree (n k : ℕ) (hk : k ≤ n) :
    (loweredStaircase n k).degree + k = (staircaseExponent (n + 1)).degree := by
  induction k with
  | zero => rw [Nat.add_zero, loweredStaircase_zero]
  | succ k ih =>
    have hprev := ih (by omega)
    have hleft : loweredStaircase n k (Nat.succPNat k) = n - k := by
      rw [loweredStaircase_apply]
      change (if k + 1 ≤ k then n - (k + 1) else n + 1 - (k + 1)) = n - k
      split_ifs <;> omega
    have hb := Finsupp.sum_update_add (loweredStaircase n k) (Nat.succPNat k)
      (n - (k + 1)) (fun _ m => m) (fun _ => rfl) (fun _ _ _ => rfl)
    change ((loweredStaircase n k).update (Nat.succPNat k) (n - (k + 1))).degree +
      loweredStaircase n k (Nat.succPNat k) =
        (loweredStaircase n k).degree + (n - (k + 1)) at hb
    rw [← loweredStaircase_succ, hleft] at hb
    omega

private theorem staircase_degree_succ (n : ℕ) :
    (staircaseExponent (n + 1)).degree = (staircaseExponent n).degree + n := by
  have h := lowered_degree n n le_rfl
  rw [loweredStaircase_last] at h
  exact h.symm

private theorem longest_length_succ (n : ℕ) :
    (FinitaryPerm.longestElement (n + 1)).length =
      (FinitaryPerm.longestElement n).length + n := by
  have h := FinitaryPerm.length_relative_succ_add (1 : FinitaryPerm ℕ+)
    (FinitaryPerm.isSupported_one n)
  simp only [inv_one, one_mul] at h
  rw [← FinitaryPerm.initialDescendingWord_product, FinitaryPerm.length_initialDescendingWord] at h
  exact h

/-- The staircase exponent degree equals the inversion length of its ambient longest element. -/
theorem staircaseExponent_degree (n : ℕ) :
    (staircaseExponent n).degree = (FinitaryPerm.longestElement n).length := by
  induction n with
  | zero => rw [staircaseExponent_zero, map_zero, FinitaryPerm.longestElement_zero,
      FinitaryPerm.length_one]
  | succ n ih => rw [staircase_degree_succ, longest_length_succ, ih]

/-- The staircase monomial is homogeneous of its longest permutation's inversion length. -/
theorem staircaseMonomial_isHomogeneous (R : Type*) [CommSemiring R] (n : ℕ) :
    (staircaseMonomial R n).IsHomogeneous (FinitaryPerm.longestElement n).length := by
  exact MvPolynomial.isHomogeneous_monomial 1 (staircaseExponent_degree n)

variable {R : Type*} [CommRing R]

/-- A supported ambient Schubert polynomial is homogeneous of the permutation's length. -/
theorem ambientSchubert_isHomogeneous {n : ℕ} (w : FinitaryPerm ℕ+)
    (hw : FinitaryPerm.IsSupported n w) : (ambientSchubert R n w).IsHomogeneous w.length := by
  have h := permutationDivided_isHomogeneous (w⁻¹ * FinitaryPerm.longestElement n)
    (staircaseMonomial_isHomogeneous R n)
  have hc := FinitaryPerm.length_inv_mul_longest w hw
  have hd : (FinitaryPerm.longestElement n).length -
      (w⁻¹ * FinitaryPerm.longestElement n).length = w.length := by omega
  rw [hd] at h
  exact h

/-- Every Schubert polynomial is homogeneous of its permutation's inversion length. -/
theorem schubert_isHomogeneous (w : FinitaryPerm ℕ+) :
    (schubert R w).IsHomogeneous w.length :=
  ambientSchubert_isHomogeneous w w.isSupported_forwardStability

end SchubertPolynomial
