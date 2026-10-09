import SchubertForwardStability.SchubertPolynomials.Stability.Homogeneous
import SchubertForwardStability.Permutations.Finitary.LengthBounds

/-! # Dual divided-difference functionals

## Main definitions

* `schubertFunctional`: constant coefficient after a permutation divided difference.

## Main results

Each functional evaluates to one on its indexed Schubert polynomial and zero on
every other Schubert polynomial, over any commutative coefficient ring.

## Implementation notes

Equal lengths use the unique maximum-length element and nil-Coxeter vanishing.
Unequal lengths use homogeneous degrees and overlong-operator annihilation.
No Schubert basis or leading-monomial theorem is used.
-/

namespace SchubertPolynomial

open scoped Classical

variable {R : Type*} [CommRing R]

/-- Distinct permutations of equal length give zero Schubert extraction. -/
theorem permutationDivided_schubert_of_eq_length (u v : FinitaryPerm ℕ+)
    (hlen : u.length = v.length) (hne : u ≠ v) :
    permutationDividedDifference R u (schubert R v) = 0 := by
  let n := max u.forwardStability v.forwardStability
  have hu : FinitaryPerm.IsSupported n u := u.isSupported_forwardStability.mono (le_max_left _ _)
  have hv : FinitaryPerm.IsSupported n v := v.isSupported_forwardStability.mono (le_max_right _ _)
  have hr : FinitaryPerm.IsSupported n (v⁻¹ * FinitaryPerm.longestElement n) :=
    hv.inv.mul (FinitaryPerm.isSupported_longestElement n)
  have hc := FinitaryPerm.length_inv_mul_longest v hv
  have hnot : (u * (v⁻¹ * FinitaryPerm.longestElement n)).length ≠
      u.length + (v⁻¹ * FinitaryPerm.longestElement n).length := by
    intro hadd
    have hmax : (u * (v⁻¹ * FinitaryPerm.longestElement n)).length =
        (FinitaryPerm.longestElement n).length := by omega
    have he := (FinitaryPerm.length_eq_longest_iff _ (hu.mul hr)).mp hmax
    have he' := congrArg (fun g : FinitaryPerm ℕ+ => g * FinitaryPerm.longestElement n) he
    simp only [mul_assoc, FinitaryPerm.longestElement_mul_self, mul_one] at he'
    exact hne (mul_inv_eq_one.mp he')
  rw [schubert_eq_ambient v n (le_max_right _ _), ambientSchubert,
    ← LinearMap.comp_apply, permutationDividedDifference_mul_zero u _ hnot,
    LinearMap.zero_apply]

/-- The constant coefficient after applying a permutation divided difference. -/
noncomputable def schubertFunctional (R : Type*) [CommRing R] (w : FinitaryPerm ℕ+) :
    MvPolynomial ℕ+ R →ₗ[R] R :=
  (MvPolynomial.lcoeff R 0).comp (permutationDividedDifference R w)

/-- The divided-difference functional is its displayed constant-coefficient formula. -/
theorem schubertFunctional_apply (w : FinitaryPerm ℕ+) (p : MvPolynomial ℕ+ R) :
    schubertFunctional R w p = (permutationDividedDifference R w p).coeff 0 := rfl

/-- Divided-difference functionals are dual to the Schubert family. -/
theorem schubertFunctional_schubert (u v : FinitaryPerm ℕ+) :
    schubertFunctional R u (schubert R v) = if u = v then 1 else 0 := by
  classical
  by_cases he : u = v
  · subst u
    simp only [ite_true, schubertFunctional_apply, permutationDivided_schubert_self,
      MvPolynomial.coeff_one]
  · rw [ite_eq_right he, schubertFunctional_apply]
    rcases lt_trichotomy u.length v.length with hlt | heq | hgt
    · have hh := permutationDivided_isHomogeneous u (schubert_isHomogeneous (R := R) v)
      apply hh.coeff_eq_zero
      rw [map_zero]
      omega
    · rw [permutationDivided_schubert_of_eq_length u v heq he,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    · rw [permutationDivided_zero_of_degree_lt u (schubert_isHomogeneous v) hgt,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- The same delta functional evaluates every supported ambient Schubert formula. -/
theorem schubertFunctional_ambient {n : ℕ} (u v : FinitaryPerm ℕ+)
    (hv : FinitaryPerm.IsSupported n v) :
    schubertFunctional R u (ambientSchubert R n v) = if u = v then 1 else 0 := by
  rw [ambientSchubert_eq_schubert v hv, schubertFunctional_schubert]

end SchubertPolynomial
