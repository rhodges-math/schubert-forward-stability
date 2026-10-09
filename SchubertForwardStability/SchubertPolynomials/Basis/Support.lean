import SchubertForwardStability.SchubertPolynomials.Basis.Global

/-!
# Artin membership and Schubert coordinate support

## Main results

* `mem_artinSpan_iff_repr_support` identifies Artin membership with support containment
  of the Schubert coordinate vector.
* `mem_artinSpan_iff_schubert` states the same condition using nonzero coordinates.
* `schubert_repr_eq_zero` gives vanishing coordinates outside an ambient support bound.

## Implementation notes

The criterion holds for every commutative coefficient ring and every ambient size,
including size zero. No nontriviality assumption on the coefficient ring is needed.
-/

namespace SchubertPolynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-- A polynomial lies in the Artin span precisely when its Schubert coordinate
support consists of permutations supported in the ambient size. -/
theorem mem_artinSpan_iff_repr_support (n : ℕ) (p : MvPolynomial ℕ+ R) :
    p ∈ artinSpan R n ↔
      ↑((schubertBasis R).repr p).support ⊆
        {w : FinitaryPerm ℕ+ | FinitaryPerm.IsSupported n w} := by
  rw [artinSpan_eq_span_schubert]
  have he : (schubertBasis R : FinitaryPerm ℕ+ → MvPolynomial ℕ+ R) = schubert R := by
    funext w
    exact schubertBasis_apply w
  rw [← he]
  exact (schubertBasis R).mem_span_image

/-- A polynomial lies in the Artin span precisely when every nonzero Schubert
coordinate is indexed by a permutation supported in the ambient size. -/
theorem mem_artinSpan_iff_schubert (n : ℕ) (p : MvPolynomial ℕ+ R) :
    p ∈ artinSpan R n ↔ ∀ w : FinitaryPerm ℕ+,
      (schubertBasis R).repr p w ≠ 0 → FinitaryPerm.IsSupported n w := by
  rw [mem_artinSpan_iff_repr_support]
  constructor
  · intro h w hw
    exact h (Finsupp.mem_support_iff.mpr hw)
  · intro h w hw
    exact h w (Finsupp.mem_support_iff.mp hw)

/-- Schubert coordinates outside an Artin span's ambient support bound vanish. -/
theorem schubert_repr_eq_zero {n : ℕ} {p : MvPolynomial ℕ+ R}
    (hp : p ∈ artinSpan R n) (w : FinitaryPerm ℕ+)
    (hw : ¬FinitaryPerm.IsSupported n w) : (schubertBasis R).repr p w = 0 := by
  by_contra hcoeff
  exact hw ((mem_artinSpan_iff_schubert n p).mp hp w hcoeff)

end

end SchubertPolynomial
