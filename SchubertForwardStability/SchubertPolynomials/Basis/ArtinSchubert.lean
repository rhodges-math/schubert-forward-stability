import SchubertForwardStability.SchubertPolynomials.Basis.ArtinOperators
import SchubertForwardStability.SchubertPolynomials.Stability.Ambient

/-!
# Artin bounds for Schubert polynomials

## Main results

* `ambientSchubert_mem_artinSpan` gives the Artin bounds in every ambient size.
* `schubert_mem_artinSpan` gives the Artin bounds for every supported permutation.
* `schubert_degreeOf_le` gives the corresponding separate variable degree bounds.

## Implementation notes

The ambient size may be zero. At size zero, the only supported permutation is identity,
whose polynomial is the constant one.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-- The staircase exponent satisfies every Artin exponent bound. -/
theorem isArtinExponent_staircase (n : ℕ) : IsArtinExponent n (staircaseExponent n) := by
  intro i
  rw [staircaseExponent_apply]

/-- The staircase monomial lies in the Artin span of its ambient size. -/
theorem staircaseMonomial_mem_artinSpan (n : ℕ) :
    staircaseMonomial R n ∈ artinSpan R n :=
  monomial_mem_artinSpan (isArtinExponent_staircase n) 1

/-- Every ambient Schubert polynomial belongs to its ambient Artin span. -/
theorem ambientSchubert_mem_artinSpan (n : ℕ) (w : FinitaryPerm ℕ+) :
    ambientSchubert R n w ∈ artinSpan R n :=
  permutationDivided_mem_artinSpan (staircaseMonomial_mem_artinSpan n) _

/-- A Schubert polynomial belongs to every Artin span supporting its permutation. -/
theorem schubert_mem_artinSpan {n : ℕ} (w : FinitaryPerm ℕ+)
    (hw : FinitaryPerm.IsSupported n w) : schubert R w ∈ artinSpan R n := by
  by_cases hn : n = 0
  · subst n
    rw [FinitaryPerm.isSupported_zero_iff] at hw
    subst w
    rw [schubert_one]
    exact monomial_mem_artinSpan (isArtinExponent_zero 0) 1
  · rw [schubert_eq_ambient w n
      ((FinitaryPerm.forwardStability_le_iff w (by omega)).mpr hw)]
    exact ambientSchubert_mem_artinSpan n w

/-- The degree in the variable at `i` is bounded by the supported size minus `i`. -/
theorem schubert_degreeOf_le {n : ℕ} (w : FinitaryPerm ℕ+)
    (hw : FinitaryPerm.IsSupported n w) (i : ℕ+) :
    (schubert R w).degreeOf i ≤ n - (i : ℕ) :=
  (mem_artinSpan_iff_degree n _).mp (schubert_mem_artinSpan w hw) i

end

end SchubertPolynomial
