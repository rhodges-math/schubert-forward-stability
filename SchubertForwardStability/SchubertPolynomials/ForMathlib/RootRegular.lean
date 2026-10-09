import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Regular variable differences

This file extends Mathlib with cancellation by `X i - X j` over any commutative
coefficient ring. A triangular change of variables sends this difference to `X i`.

## Main results

* `isRegular_X_sub_X`: differences of distinct variables are non-zero-divisors.

## Implementation notes

No domain or nontriviality assumption is imposed on the coefficient ring.
-/

namespace MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- The difference of two distinct variables is regular over any commutative ring. -/
theorem isRegular_X_sub_X {i j : σ} (hij : i ≠ j) :
    IsRegular (X i - X j : MvPolynomial σ R) := by
  classical
  let f : σ → MvPolynomial σ R := fun k ↦ if k = i then X i + X j else X k
  let g : σ → MvPolynomial σ R := fun k ↦ if k = i then X i - X j else X k
  have hcomp : (aeval g).comp (aeval f) = AlgHom.id R (MvPolynomial σ R) := by
    ext k
    by_cases hk : k = i
    · subst k
      simp [f, g, hij.symm]
    · simp [f, g, hk]
  have hinv (p : MvPolynomial σ R) : aeval g (aeval f p) = p :=
    AlgHom.congr_fun hcomp p
  have hroot : aeval f (X i - X j : MvPolynomial σ R) = X i := by
    simp [f, hij.symm]
  suffices h : IsLeftRegular (X i - X j : MvPolynomial σ R) from
    ⟨h, h.right_of_commute (Commute.all _)⟩
  intro p q hpq
  have he := congrArg (aeval f) hpq
  rw [map_mul, map_mul, hroot] at he
  have hc := (isRegular_X (R := R) (n := i)).left he
  have hc' := congrArg (aeval g) hc
  simpa only [hinv] using hc'

end MvPolynomial
