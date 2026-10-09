import SchubertForwardStability.SchubertPolynomials.Divided.Unreduced

/-! # Multiplication of permutation divided differences

## Main results

Length-additive permutation products compose their divided-difference operators.
A non-length-additive product of these operators is zero. Coefficient homomorphisms
commute with every permutation operator.

## Implementation notes

The displayed reduced-word order agrees with multiplication of linear endomorphisms.
All coefficient rings are arbitrary commutative rings.
-/

namespace SchubertPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A length-additive permutation product composes its divided-difference operators. -/
theorem permutationDividedDifference_mul (u v : FinitaryPerm ℕ+)
    (hadd : (u * v).length = u.length + v.length) :
    permutationDividedDifference R (u * v) =
      (permutationDividedDifference R u).comp (permutationDividedDifference R v) := by
  have hu := (FinitaryPerm.isReducedWordIn_lexFirst u).1
  have hv := (FinitaryPerm.isReducedWordIn_lexFirst v).1
  have hword : FinitaryPerm.IsReducedWord (u * v)
      (u.lexFirstReducedWord ++ v.lexFirstReducedWord) := by
    constructor
    · rw [FinitaryPerm.wordProduct_append, hu.1, hv.1]
    · rw [List.length_append, hu.2, hv.2, hadd]
  rw [permutationDividedDifference_eq _ hword, wordDividedDifference_append]
  rfl

/-- A non-length-additive product of permutation divided-difference operators is zero. -/
theorem permutationDividedDifference_mul_zero (u v : FinitaryPerm ℕ+)
    (hne : (u * v).length ≠ u.length + v.length) :
    (permutationDividedDifference R u).comp (permutationDividedDifference R v) = 0 := by
  have hu := (FinitaryPerm.isReducedWordIn_lexFirst u).1
  have hv := (FinitaryPerm.isReducedWordIn_lexFirst v).1
  change (wordDividedDifference R u.lexFirstReducedWord).comp
    (wordDividedDifference R v.lexFirstReducedWord) = 0
  rw [← wordDividedDifference_append]
  apply wordDividedDifference_zero
  rintro ⟨_, hlen⟩
  apply hne
  rw [FinitaryPerm.wordProduct_append, hu.1, hv.1, List.length_append, hu.2, hv.2] at hlen
  exact hlen.symm

/-- Coefficient homomorphisms commute with every permutation divided difference. -/
theorem permutationDividedDifference_map (f : R →+* S) (w : FinitaryPerm ℕ+)
    (p : MvPolynomial ℕ+ R) :
    permutationDividedDifference S w (MvPolynomial.map f p) =
      MvPolynomial.map f (permutationDividedDifference R w p) :=
  wordDividedDifference_map f w.lexFirstReducedWord p

end SchubertPolynomial
