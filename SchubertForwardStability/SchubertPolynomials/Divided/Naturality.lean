import SchubertForwardStability.SchubertPolynomials.Divided.Positive

/-! # Naturality of polynomial divided differences

## Main results

Variable swaps and divided differences commute with coefficient homomorphisms
and injective variable renamings.

## Implementation notes

The proofs use quotient uniqueness, so no coefficient-map injectivity or domain
assumption is needed. Injectivity is required only for the variable embedding.
-/

namespace SchubertPolynomial

variable {σ τ R S : Type*} [CommRing R] [CommRing S]

/-- Coefficient homomorphisms commute with variable swaps. -/
theorem variableSwap_map (f : R →+* S) (i j : σ) (p : MvPolynomial σ R) :
    variableSwap S i j (MvPolynomial.map f p) =
      MvPolynomial.map f (variableSwap R i j p) := by
  classical
  simp only [variableSwap, MvPolynomial.renameEquiv_apply]
  exact (MvPolynomial.map_rename f (Equiv.swap i j) p).symm

/-- Divided differences commute with any coefficient homomorphism. -/
theorem variableDividedDifference_map (f : R →+* S) {i j : σ} (hij : i ≠ j)
    (p : MvPolynomial σ R) :
    variableDividedDifference S i j (MvPolynomial.map f p) =
      MvPolynomial.map f (variableDividedDifference R i j p) := by
  apply (variableDividedDifference_eq_iff hij _ _).mpr
  rw [variableSwap_map]
  have hm := congrArg (MvPolynomial.map f) (root_mul_variableDividedDifference hij p)
  simpa only [map_mul, map_sub, MvPolynomial.map_X] using hm

/-- An injective variable embedding intertwines the corresponding variable swaps. -/
theorem variableSwap_rename (f : σ → τ) (hf : Function.Injective f) (i j : σ)
    (p : MvPolynomial σ R) :
    variableSwap R (f i) (f j) (MvPolynomial.rename f p) =
      MvPolynomial.rename f (variableSwap R i j p) := by
  classical
  have hs : (Equiv.swap (f i) (f j) : τ → τ) ∘ f = f ∘ Equiv.swap i j := by
    funext k
    simp only [Function.comp_apply]
    by_cases hki : k = i
    · subst k
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    · by_cases hkj : k = j
      · subst k
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj,
          Equiv.swap_apply_of_ne_of_ne (fun h ↦ hki (hf h)) (fun h ↦ hkj (hf h))]
  simp only [variableSwap, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]
  rw [hs]

/-- Divided differences commute with an injective embedding of the variable carrier. -/
theorem variableDividedDifference_rename (f : σ → τ) (hf : Function.Injective f)
    {i j : σ} (hij : i ≠ j) (p : MvPolynomial σ R) :
    variableDividedDifference R (f i) (f j) (MvPolynomial.rename f p) =
      MvPolynomial.rename f (variableDividedDifference R i j p) := by
  apply (variableDividedDifference_eq_iff (fun h ↦ hij (hf h)) _ _).mpr
  rw [variableSwap_rename f hf]
  have hm := congrArg (MvPolynomial.rename f) (root_mul_variableDividedDifference hij p)
  simpa only [map_mul, map_sub, MvPolynomial.rename_X] using hm

/-- Positive-index adjacent divided differences commute with coefficient homomorphisms. -/
theorem dividedDifference_map (f : R →+* S) (i : ℕ+) (p : MvPolynomial ℕ+ R) :
    dividedDifference S i (MvPolynomial.map f p) =
      MvPolynomial.map f (dividedDifference R i p) :=
  variableDividedDifference_map f (show i ≠ i + 1 from
    (show i < i + 1 from Nat.lt_succ_self (i : ℕ)).ne) p

end SchubertPolynomial
