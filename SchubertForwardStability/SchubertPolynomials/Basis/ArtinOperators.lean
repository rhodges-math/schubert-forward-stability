import SchubertForwardStability.SchubertPolynomials.Basis.ArtinSpan
import SchubertForwardStability.SchubertPolynomials.Divided.Independence

/-!
# Divided differences preserve the Artin span

## Main results

* `dividedDifference_mem_artinSpan` proves stability under adjacent divided differences.
* `wordDividedDifference_mem_artinSpan` extends this to every positive-indexed word.
* `permutationDivided_mem_artinSpan` extends this to permutation divided differences.

## Implementation notes

The bounds are checked separately on the two geometric-series cases of each monomial quotient.
The result applies to every commutative coefficient ring, including rings with zero divisors.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-- Replacing two exponents within their Artin bounds preserves all Artin bounds. -/
theorem IsArtinExponent.replace {n : ℕ} {a : ℕ+ →₀ ℕ}
    (ha : IsArtinExponent n a) (i j : ℕ+) (p q : ℕ)
    (hp : p ≤ n - (i : ℕ)) (hq : q ≤ n - (j : ℕ)) :
    IsArtinExponent n (replaceExponents a i j p q) := by
  classical
  intro k
  by_cases hkj : k = j
  · subst k
    simpa only [replaceExponents_right] using hq
  · by_cases hki : k = i
    · subst k
      have hij : i ≠ j := hkj
      simpa only [replaceExponents_left a hij] using hp
    · simpa only [replaceExponents_other a i j p q hki hkj] using ha k

private theorem positive_term {n : ℕ} {a : ℕ+ →₀ ℕ}
    (ha : IsArtinExponent n a) (i : ℕ+) (k : ℕ) (hk : k < a i - a (i + 1)) :
    IsArtinExponent n
      (replaceExponents a i (i + 1) (a i - 1 - k) (a (i + 1) + k)) := by
  have hleft := ha i
  have hright := ha (i + 1)
  have hcoe : ((i + 1 : ℕ+) : ℕ) = (i : ℕ) + 1 := rfl
  apply ha.replace
  · omega
  · rw [hcoe]
    omega

private theorem negative_term {n : ℕ} {a : ℕ+ →₀ ℕ}
    (ha : IsArtinExponent n a) (i : ℕ+) (k : ℕ) (hk : k < a (i + 1) - a i) :
    IsArtinExponent n
      (replaceExponents a i (i + 1) (a i + k) (a (i + 1) - 1 - k)) := by
  have hleft := ha i
  have hright := ha (i + 1)
  have hcoe : ((i + 1 : ℕ+) : ℕ) = (i : ℕ) + 1 := rfl
  rw [hcoe] at hright
  apply ha.replace
  · omega
  · rw [hcoe]
    omega

/-- The adjacent monomial quotient of an Artin-bounded monomial lies in its Artin span. -/
theorem monomialQuotient_mem_artinSpan {n : ℕ} {a : ℕ+ →₀ ℕ}
    (ha : IsArtinExponent n a) (i : ℕ+) :
    monomialQuotient R i (i + 1) a ∈ artinSpan R n := by
  classical
  unfold monomialQuotient
  split_ifs
  · exact Submodule.sum_mem _ fun k hk =>
      monomial_mem_artinSpan (positive_term ha i k (Finset.mem_range.mp hk)) 1
  · exact Submodule.neg_mem _ (Submodule.sum_mem _ fun k hk =>
      monomial_mem_artinSpan (negative_term ha i k (Finset.mem_range.mp hk)) 1)
  · exact Submodule.zero_mem _

/-- Adjacent divided differences preserve the Artin span over every commutative ring. -/
theorem dividedDifference_mem_artinSpan {n : ℕ} {p : MvPolynomial ℕ+ R}
    (hp : p ∈ artinSpan R n) (i : ℕ+) : dividedDifference R i p ∈ artinSpan R n := by
  rw [artinSpan_eq_span (R := R)] at hp
  have hle : Submodule.span R
      ((fun a : ℕ+ →₀ ℕ => MvPolynomial.monomial a (1 : R)) ''
        {a | IsArtinExponent n a}) ≤
      (artinSpan R n).comap (dividedDifference R i) := by
    refine Submodule.span_le.mpr ?_
    rintro p ⟨a, ha, rfl⟩
    change variableDividedDifference R i (i + 1) (MvPolynomial.monomial a 1) ∈
      artinSpan R n
    rw [variableDividedDifference_monomial_one]
    exact monomialQuotient_mem_artinSpan (R := R) ha i
  exact hle hp

/-- Every word of adjacent divided differences preserves the Artin span. -/
theorem wordDividedDifference_mem_artinSpan {n : ℕ} {p : MvPolynomial ℕ+ R}
    (hp : p ∈ artinSpan R n) (word : List ℕ+) :
    wordDividedDifference R word p ∈ artinSpan R n := by
  induction word with
  | nil => simpa only [wordDividedDifference_nil, LinearMap.id_apply] using hp
  | cons i word ih =>
    rw [wordDividedDifference_cons, LinearMap.comp_apply]
    exact dividedDifference_mem_artinSpan ih i

/-- Permutation divided differences preserve the Artin span. -/
theorem permutationDivided_mem_artinSpan {n : ℕ} {p : MvPolynomial ℕ+ R}
    (hp : p ∈ artinSpan R n) (w : FinitaryPerm ℕ+) :
    permutationDividedDifference R w p ∈ artinSpan R n :=
  wordDividedDifference_mem_artinSpan hp w.lexFirstReducedWord

end

end SchubertPolynomial
