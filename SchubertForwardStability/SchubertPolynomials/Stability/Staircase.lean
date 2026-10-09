import SchubertForwardStability.SchubertPolynomials.Divided.MonomialStep
import SchubertForwardStability.Permutations.Finitary.Finite

/-! # Staircase monomials on positive variables

## Main definitions

* `staircaseExponent`: the finite exponent function i ↦ n-i.
* `staircaseMonomial`: the coefficient-one monomial of that exponent function.
* `loweredStaircase`: the (n+1)-staircase with its first k exponents lowered by one.

## Main results

The partial lowering starts at the (n+1)-staircase and ends at the n-staircase.
Each intermediate adjacent divided difference performs exactly one lowering.

## Implementation notes

Variables are positive integers, while ambient sizes and cutoffs are natural numbers.
The staircase monomial itself is defined over every commutative semiring.
-/

namespace SchubertPolynomial

/-- The staircase exponent at positive variable i is n-i, truncated naturally at zero. -/
noncomputable def staircaseExponent (n : ℕ) : ℕ+ →₀ ℕ :=
  Finsupp.onFinset (FinitaryPerm.positions n) (fun i => n - (i : ℕ)) (by
    intro i hi
    apply (FinitaryPerm.mem_positions n i).mpr
    omega)

/-- The staircase exponent evaluates to the natural truncated difference. -/
@[simp]
theorem staircaseExponent_apply (n : ℕ) (i : ℕ+) :
    staircaseExponent n i = n - (i : ℕ) := rfl

/-- The staircase monomial in ambient size n has coefficient one. -/
noncomputable def staircaseMonomial (R : Type*) [CommSemiring R] (n : ℕ) :
    MvPolynomial ℕ+ R := MvPolynomial.monomial (staircaseExponent n) 1

/-- The empty staircase has zero exponent at every variable. -/
@[simp]
theorem staircaseExponent_zero : staircaseExponent 0 = 0 := by
  ext i
  simp only [staircaseExponent_apply, Finsupp.zero_apply, Nat.zero_sub]

/-- The size-one staircase has zero exponent at every positive variable. -/
@[simp]
theorem staircaseExponent_one : staircaseExponent 1 = 0 := by
  ext i
  simp only [staircaseExponent_apply, Finsupp.zero_apply]
  have := i.pos
  omega

/-- The staircase monomial at size zero is one. -/
@[simp]
theorem staircaseMonomial_zero (R : Type*) [CommSemiring R] : staircaseMonomial R 0 = 1 := by
  rw [staircaseMonomial, staircaseExponent_zero, MvPolynomial.monomial_zero', map_one]

/-- The staircase monomial at size one is one. -/
@[simp]
theorem staircaseMonomial_one (R : Type*) [CommSemiring R] : staircaseMonomial R 1 = 1 := by
  rw [staircaseMonomial, staircaseExponent_one, MvPolynomial.monomial_zero', map_one]

/-- The staircase monomial is the product of its displayed variable powers. -/
theorem staircaseMonomial_eq_prod (R : Type*) [CommSemiring R] (n : ℕ) :
    staircaseMonomial R n =
      ∏ i ∈ FinitaryPerm.positions n, (MvPolynomial.X i : MvPolynomial ℕ+ R) ^ (n - (i : ℕ)) := by
  classical
  have he : Finsupp.indicator (FinitaryPerm.positions n) (fun i _ => n - (i : ℕ)) =
      staircaseExponent n := by
    ext i
    rw [staircaseExponent_apply]
    by_cases hi : i ∈ FinitaryPerm.positions n
    · rw [Finsupp.indicator_of_mem hi]
    · rw [Finsupp.indicator_of_notMem hi]
      have hbound : n < (i : ℕ) := by
        simpa only [FinitaryPerm.mem_positions, not_le] using hi
      omega
  rw [staircaseMonomial, ← he, ← MvPolynomial.prod_X_pow]

/-- Coefficient homomorphisms preserve staircase monomials. -/
theorem staircaseMonomial_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (n : ℕ) :
    MvPolynomial.map f (staircaseMonomial R n) = staircaseMonomial S n := by
  rw [staircaseMonomial, MvPolynomial.map_monomial, map_one, staircaseMonomial]

/-- Lower the first k exponents of the next staircase by one. -/
noncomputable def loweredStaircase (n k : ℕ) : ℕ+ →₀ ℕ :=
  Finsupp.onFinset (FinitaryPerm.positions (n + 1))
    (fun i => if (i : ℕ) ≤ k then n - (i : ℕ) else n + 1 - (i : ℕ)) (by
      intro i hi
      apply (FinitaryPerm.mem_positions (n + 1) i).mpr
      split_ifs at hi <;> omega)

/-- The partially lowered staircase is given by its explicit cutoff formula. -/
@[simp]
theorem loweredStaircase_apply (n k : ℕ) (i : ℕ+) :
    loweredStaircase n k i = if (i : ℕ) ≤ k then n - (i : ℕ) else n + 1 - (i : ℕ) := rfl

/-- Before any lowering, the exponent function is the next staircase. -/
theorem loweredStaircase_zero (n : ℕ) : loweredStaircase n 0 = staircaseExponent (n + 1) := by
  ext i
  rw [loweredStaircase_apply, staircaseExponent_apply, ite_eq_right (not_le_of_gt i.pos)]

/-- After lowering the first n positions, the exponent function is the n-staircase. -/
theorem loweredStaircase_last (n : ℕ) : loweredStaircase n n = staircaseExponent n := by
  ext i
  rw [loweredStaircase_apply, staircaseExponent_apply]
  split_ifs <;> omega

/-- Increasing the lowering cutoff changes exactly its newly included positive position. -/
theorem loweredStaircase_succ (n k : ℕ) :
    loweredStaircase n (k + 1) =
      (loweredStaircase n k).update (Nat.succPNat k) (n - (k + 1)) := by
  classical
  ext i
  rw [loweredStaircase_apply, Finsupp.update_apply, loweredStaircase_apply]
  by_cases hi : i = Nat.succPNat k
  · subst i
    simp only [Nat.succPNat_coe, Nat.succ_eq_add_one, le_refl, ite_true]
  · have hne : (i : ℕ) ≠ k + 1 := fun h => hi (PNat.eq h)
    simp only [hi, ite_false]
    split_ifs <;> omega

/-- The next adjacent operator lowers exactly the next unprocessed staircase exponent. -/
theorem loweredStaircase_step {R : Type*} [CommRing R] (n k : ℕ) (hk : k < n) :
    variableDividedDifference R (Nat.succPNat k) (Nat.succPNat k + 1)
      (MvPolynomial.monomial (loweredStaircase n k) 1) =
        MvPolynomial.monomial (loweredStaircase n (k + 1)) 1 := by
  let i : ℕ+ := Nat.succPNat k
  change variableDividedDifference R i (i + 1)
    (MvPolynomial.monomial (loweredStaircase n k) 1) =
      MvPolynomial.monomial (loweredStaircase n (k + 1)) 1
  have hij : i ≠ i + 1 := by
    intro h
    have hnat := congrArg PNat.val h
    change k + 1 = k + 2 at hnat
    omega
  have hleft : loweredStaircase n k i = n - k := by
    rw [loweredStaircase_apply]
    change (if k + 1 ≤ k then n - (k + 1) else n + 1 - (k + 1)) = n - k
    split_ifs <;> omega
  have hright : loweredStaircase n k (i + 1) = n - (k + 1) := by
    rw [loweredStaircase_apply]
    change (if k + 2 ≤ k then n - (k + 2) else n + 1 - (k + 2)) = n - (k + 1)
    split_ifs <;> omega
  have hgap : loweredStaircase n k i = loweredStaircase n k (i + 1) + 1 := by
    rw [hleft, hright]
    omega
  rw [variableDividedDifference_monomial_step hij _ hgap, hright, loweredStaircase_succ]

end SchubertPolynomial
