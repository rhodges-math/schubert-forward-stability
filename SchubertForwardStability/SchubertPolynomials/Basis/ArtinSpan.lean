import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.PNat.Basic

/-!
# Artin-bounded monomials

## Main definitions

* `IsArtinExponent n a` bounds each exponent by `n - i` at positive index `i`.
* `artinSpan R n` is the submodule spanned by these monomials over a commutative semiring.

## Main results

* `artinSpan_eq_span` identifies the support submodule with the bounded monomial span.
* `mem_artinSpan_iff_degree` characterizes membership by separate variable degrees.
* `exists_mem_artinSpan` places every polynomial in some Artin span.

## Implementation notes

Variables have positive integer indices. Natural subtraction makes exponents zero beyond `n`.
The support definition and monomial-span characterization remain valid for trivial coefficients.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

variable {R : Type*} [CommSemiring R]

/-- An exponent is Artin-bounded at size `n` when its exponent at `i` is at most `n - i`. -/
def IsArtinExponent (n : ℕ) (a : ℕ+ →₀ ℕ) : Prop :=
  ∀ i : ℕ+, a i ≤ n - (i : ℕ)

/-- Zero exponents are Artin-bounded at every size. -/
@[simp] theorem isArtinExponent_zero (n : ℕ) : IsArtinExponent n 0 := by
  intro i
  exact Nat.zero_le _

/-- An exponent remains Artin-bounded when the size increases. -/
theorem IsArtinExponent.mono {m n : ℕ} {a : ℕ+ →₀ ℕ}
    (ha : IsArtinExponent m a) (hmn : m ≤ n) : IsArtinExponent n a := by
  intro i
  exact (ha i).trans (Nat.sub_le_sub_right hmn _)

/-- Decreasing every exponent preserves the Artin bounds. -/
theorem IsArtinExponent.of_le {n : ℕ} {a b : ℕ+ →₀ ℕ}
    (ha : IsArtinExponent n a) (hba : b ≤ a) : IsArtinExponent n b := by
  intro i
  exact (hba i).trans (ha i)

/-- The Artin span consists of polynomials supported on Artin-bounded exponents. -/
def artinSpan (R : Type*) [CommSemiring R] (n : ℕ) : Submodule R (MvPolynomial ℕ+ R) :=
  AddMonoidAlgebra.supported R R {a | IsArtinExponent n a}

/-- The Artin span is the span of its coefficient-one bounded monomials. -/
theorem artinSpan_eq_span (n : ℕ) :
    artinSpan R n = Submodule.span R
      ((fun a : ℕ+ →₀ ℕ => MvPolynomial.monomial a (1 : R)) ''
        {a | IsArtinExponent n a}) := by
  exact AddMonoidAlgebra.supported_eq_span_single R _

/-- Artin-span membership is precisely the bound on every supported exponent. -/
theorem mem_artinSpan_iff (n : ℕ) (p : MvPolynomial ℕ+ R) :
    p ∈ artinSpan R n ↔ ∀ a ∈ p.support, IsArtinExponent n a := by
  rfl

/-- Every coefficient outside the Artin exponent bounds vanishes in the Artin span. -/
theorem mem_artinSpan_iff_coeff (n : ℕ) (p : MvPolynomial ℕ+ R) :
    p ∈ artinSpan R n ↔ ∀ a, ¬IsArtinExponent n a → p.coeff a = 0 := by
  exact Finsupp.mem_supported' R p.coeff

/-- Artin-span membership is equivalent to the separate bounds on variable degrees. -/
theorem mem_artinSpan_iff_degree (n : ℕ) (p : MvPolynomial ℕ+ R) :
    p ∈ artinSpan R n ↔ ∀ i : ℕ+, p.degreeOf i ≤ n - (i : ℕ) := by
  rw [mem_artinSpan_iff]
  constructor
  · intro hp i
    exact MvPolynomial.degreeOf_le_iff.mpr fun a ha => hp a ha i
  · intro hp a ha i
    exact MvPolynomial.degreeOf_le_iff.mp (hp i) a ha

/-- Positive variable degrees satisfy the equivalent index-plus-degree Artin bound. -/
theorem mem_artinSpan_iff_degree_pos (n : ℕ) (p : MvPolynomial ℕ+ R) :
    p ∈ artinSpan R n ↔
      ∀ i : ℕ+, 0 < p.degreeOf i → (i : ℕ) + p.degreeOf i ≤ n := by
  rw [mem_artinSpan_iff_degree]
  constructor
  · intro hp i hi
    have := hp i
    omega
  · intro hp i
    by_cases hi : p.degreeOf i = 0
    · rw [hi]
      exact Nat.zero_le _
    · have := hp i (Nat.pos_of_ne_zero hi)
      omega

/-- A bounded monomial with any coefficient lies in the Artin span. -/
theorem monomial_mem_artinSpan {n : ℕ} {a : ℕ+ →₀ ℕ}
    (ha : IsArtinExponent n a) (r : R) :
    MvPolynomial.monomial a r ∈ artinSpan R n := by
  change Finsupp.single a r ∈ Finsupp.supported R R {a | IsArtinExponent n a}
  exact Finsupp.single_mem_supported R r ha

/-- A coefficient-one monomial over a nontrivial semiring lies in exactly its Artin spans. -/
theorem monomial_one_mem_artinSpan [Nontrivial R] (n : ℕ) (a : ℕ+ →₀ ℕ) :
    MvPolynomial.monomial a (1 : R) ∈ artinSpan R n ↔ IsArtinExponent n a := by
  change Finsupp.single a (1 : R) ∈ Finsupp.supported R R {a | IsArtinExponent n a} ↔ _
  rw [Finsupp.supported_eq_span_single]
  exact Finsupp.single_mem_span_single R

/-- Increasing the size enlarges the Artin span. -/
theorem artinSpan_mono {m n : ℕ} (hmn : m ≤ n) : artinSpan R m ≤ artinSpan R n := by
  intro p hp
  exact (mem_artinSpan_iff n p).mpr fun a ha =>
    ((mem_artinSpan_iff m p).mp hp a ha).mono hmn

private theorem exponent_bound (a : ℕ+ →₀ ℕ) :
    IsArtinExponent (a.support.sup fun i => (i : ℕ) + a i) a := by
  classical
  intro i
  by_cases hi : a i = 0
  · rw [hi]
    exact Nat.zero_le _
  · have hle := Finset.le_sup (f := fun i : ℕ+ => (i : ℕ) + a i)
      (Finsupp.mem_support_iff.mpr hi)
    omega

/-- Every finite polynomial belongs to the Artin span of some size. -/
theorem exists_mem_artinSpan (p : MvPolynomial ℕ+ R) : ∃ n, p ∈ artinSpan R n := by
  classical
  refine ⟨p.support.sup fun a => a.support.sup fun i => (i : ℕ) + a i, ?_⟩
  rw [mem_artinSpan_iff]
  intro a ha
  exact (exponent_bound a).mono
    (Finset.le_sup (f := fun a : ℕ+ →₀ ℕ => a.support.sup fun i => (i : ℕ) + a i) ha)

end

end SchubertPolynomial
