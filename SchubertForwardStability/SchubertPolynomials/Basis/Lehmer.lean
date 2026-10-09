import SchubertForwardStability.Permutations.Statistics.LehmerInjective
import SchubertForwardStability.SchubertPolynomials.Basis.ArtinCoordinates

/-!
# The right Lehmer bijection

## Main definitions

* `finiteLehmerEquiv` identifies size-`n` permutations with Artin-bounded exponents.
* `FinitaryPerm.lehmerEquiv` identifies finitary permutations with finite exponent vectors.

## Main results

* `finiteLehmerCode_bijective` uses code injectivity and equal factorial cardinalities.
* `FinitaryPerm.lehmerCode_surjective` covers every finitely supported exponent vector.

## Implementation notes

The equivalences are given by the right inversion counts.
-/

noncomputable section

namespace SchubertPolynomial

/-- The right Lehmer vector of a supported permutation satisfies the Artin bounds. -/
theorem isArtinExponent_lehmer {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : FinitaryPerm.IsSupported n w) : IsArtinExponent n w.lehmerCode :=
  FinitaryPerm.lehmerCode_le hw

/-- The finite right Lehmer map sends a permutation to its bounded exponent vector. -/
def finiteLehmerCode (n : ℕ) (w : Equiv.Perm (Fin n)) :
    {a : ℕ+ →₀ ℕ // IsArtinExponent n a} :=
  ⟨(FinitaryPerm.ofFinite n w).lehmerCode,
    isArtinExponent_lehmer (FinitaryPerm.isSupported_ofFinite n w)⟩

/-- The finite right Lehmer map is injective. -/
theorem finiteLehmerCode_injective (n : ℕ) : Function.Injective (finiteLehmerCode n) := by
  intro w v h
  apply FinitaryPerm.ofFinite_injective n
  exact FinitaryPerm.lehmerCode_injective (congrArg Subtype.val h)

/-- The finite right Lehmer map is bijective because both index types have size `n!`. -/
theorem finiteLehmerCode_bijective (n : ℕ) : Function.Bijective (finiteLehmerCode n) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨finiteLehmerCode_injective n, ?_⟩
  rw [Fintype.card_perm, Fintype.card_fin, card_artinExponent]

/-- Finite permutations and bounded Artin exponent vectors are equivalent by right
Lehmer code. -/
def finiteLehmerEquiv (n : ℕ) :
    Equiv.Perm (Fin n) ≃ {a : ℕ+ →₀ ℕ // IsArtinExponent n a} :=
  Equiv.ofBijective (finiteLehmerCode n) (finiteLehmerCode_bijective n)

/-- The finite Lehmer equivalence returns the right inversion exponent vector. -/
@[simp] theorem finiteLehmerEquiv_apply (n : ℕ) (w : Equiv.Perm (Fin n)) :
    (finiteLehmerEquiv n w).val = (FinitaryPerm.ofFinite n w).lehmerCode := rfl

end SchubertPolynomial

namespace FinitaryPerm

open SchubertPolynomial

/-- Every finitely supported exponent vector is the right Lehmer code of a
finitary permutation. -/
theorem lehmerCode_surjective : Function.Surjective (lehmerCode : FinitaryPerm ℕ+ → ℕ+ →₀ ℕ) := by
  intro a
  obtain ⟨n, hn⟩ := exists_mem_artinSpan (MvPolynomial.monomial a (1 : ℤ))
  have ha : IsArtinExponent n a := (monomial_one_mem_artinSpan (R := ℤ) n a).mp hn
  let w := (finiteLehmerEquiv n).symm ⟨a, ha⟩
  refine ⟨ofFinite n w, ?_⟩
  exact congrArg Subtype.val ((finiteLehmerEquiv n).apply_symm_apply ⟨a, ha⟩)

/-- Finitary permutations are equivalent to finitely supported exponent vectors
by their right Lehmer codes. -/
def lehmerEquiv : FinitaryPerm ℕ+ ≃ (ℕ+ →₀ ℕ) :=
  Equiv.ofBijective lehmerCode ⟨lehmerCode_injective, lehmerCode_surjective⟩

/-- The Lehmer equivalence sends a permutation to its right inversion code. -/
@[simp] theorem lehmerEquiv_apply (w : FinitaryPerm ℕ+) : lehmerEquiv w = w.lehmerCode := rfl

end FinitaryPerm

end
