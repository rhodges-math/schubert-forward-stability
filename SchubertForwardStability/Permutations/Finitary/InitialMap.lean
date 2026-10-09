import SchubertForwardStability.Permutations.Finitary.Finite
import Mathlib.Data.Fintype.Card

/-! # Initial permutations from injective bounded value lists

An injective list of `n` values in `{1, ..., n}` defines a permutation supported in
`[1, n]` with these values. A permutation that maps `{1, ..., n}` into itself agrees there
with such a permutation, and maps every larger position to a larger value.
-/

namespace FinitaryPerm

private noncomputable def initialMapEquiv (n : ℕ) (f : Fin n → ℕ+)
    (hBound : ∀ i, (f i : ℕ) ≤ n) (hInj : Function.Injective f) : Equiv.Perm (Fin n) :=
  let g : Fin n → Fin n := fun i => (positiveIndex n).symm ⟨f i, hBound i⟩
  have hg : Function.Injective g := by
    intro i j h
    apply hInj
    exact congrArg Subtype.val ((positiveIndex n).symm.injective h)
  Equiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩

/-- The initial permutation whose finite list is a given injective bounded value list. -/
noncomputable def initialPerm (n : ℕ) (f : Fin n → ℕ+)
    (hBound : ∀ i, (f i : ℕ) ≤ n) (hInj : Function.Injective f) : FinitaryPerm ℕ+ :=
  ofFinite n (initialMapEquiv n f hBound hInj)

/-- An initial list permutation fixes all positions above its list size. -/
theorem initialPerm_supported (n : ℕ) (f : Fin n → ℕ+)
    (hBound : ∀ i, (f i : ℕ) ≤ n) (hInj : Function.Injective f) :
    IsSupported n (initialPerm n f hBound hInj) := isSupported_ofFinite n _

/-- An initial list permutation takes exactly the specified value at each finite index. -/
theorem initialPerm_apply (n : ℕ) (f : Fin n → ℕ+)
    (hBound : ∀ i, (f i : ℕ) ≤ n) (hInj : Function.Injective f) (i : Fin n) :
    initialPerm n f hBound hInj (positiveIndex n i).val = f i := by
  rw [initialPerm, ofFinite_apply_position]
  change (positiveIndex n ((positiveIndex n).symm ⟨f i, hBound i⟩)).val = f i
  rw [Equiv.apply_symm_apply]

/-- A permutation whose initial values stay in the initial alphabet has a matching prefix factor. -/
theorem exists_initial_agree (n : ℕ) (w : FinitaryPerm ℕ+)
    (hBound : ∀ i : ℕ+, (i : ℕ) ≤ n → (w i : ℕ) ≤ n) :
    ∃ u : FinitaryPerm ℕ+, IsSupported n u ∧
      ∀ i : ℕ+, (i : ℕ) ≤ n → u i = w i := by
  let f : Fin n → ℕ+ := fun i => w (positiveIndex n i).val
  have hb : ∀ i, (f i : ℕ) ≤ n := fun i => hBound _ (positiveIndex n i).property
  have hf : Function.Injective f := by
    intro i j h
    apply (positiveIndex n).injective
    apply Subtype.ext
    exact w.injective h
  refine ⟨initialPerm n f hb hf, initialPerm_supported n f hb hf, ?_⟩
  intro i hi
  let j := (positiveIndex n).symm ⟨i, hi⟩
  have he : (positiveIndex n j).val = i :=
    congrArg Subtype.val ((positiveIndex n).apply_symm_apply ⟨i, hi⟩)
  rw [← he]
  exact initialPerm_apply n f hb hf j

/-- Values beyond a permutation's closed initial alphabet lie beyond that alphabet. -/
theorem values_above_prefix (n : ℕ) (w u : FinitaryPerm ℕ+)
    (hu : IsSupported n u) (hAgree : ∀ i : ℕ+, (i : ℕ) ≤ n → u i = w i)
    (j : ℕ+) (hj : n < (j : ℕ)) : n < (w j : ℕ) := by
  by_contra hNot
  have hi : (u⁻¹ (w j) : ℕ) ≤ n :=
    (hu.inv.apply_le_iff (w j)).mpr (le_of_not_gt hNot)
  have he := apply_inv_apply u (w j)
  rw [hAgree _ hi] at he
  have hx := congrArg PNat.val (w.injective he)
  omega

end FinitaryPerm
