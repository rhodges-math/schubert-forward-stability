import SchubertForwardStability.StrongMixing.Coefficients.FiniteReindexing
import Mathlib.Data.Finset.Sort

/-!
# Increasing compression of a finite coordinate set

The sorted coordinate bijection is linearly extended to all integer indices.
Its natural finite interval sums are exactly the sums over the selected set, so
the reindexing bound applies to each remainder in a peeling argument.
-/

open scoped BigOperators

namespace StrongMixing

/-- Increasingly enumerate a nonempty finite integer coordinate set, extending
the enumeration linearly outside its finite interval. The extension is defined
from the coordinate set alone and does not depend on a Laplace parameter. -/
noncomputable def finiteSetExtension (A : Finset ℤ) (hA : A.Nonempty) : ℤ → ℤ :=
  integerRowExtension (A.orderEmbOfFin (show A.card = A.card - 1 + 1 by
    have h := Finset.card_pos.mpr hA
    omega))

/-- The linearly extended sorted enumeration of a nonempty finite coordinate
set is strictly increasing on all integer indices. -/
theorem finiteSetExtension_strictMono (A : Finset ℤ) (hA : A.Nonempty) :
    StrictMono (finiteSetExtension A hA) :=
  integerRowExtension_strictMono _ (A.orderEmbOfFin _).strictMono

/-- At each finite enumeration index, the integer extension agrees with the
sorted order embedding of the selected coordinate set. -/
theorem finiteSetExtension_apply (A : Finset ℤ) (hA : A.Nonempty)
    (i : Fin (A.card - 1 + 1)) :
    finiteSetExtension A hA (i : ℤ) = A.orderEmbOfFin
      (show A.card = A.card - 1 + 1 by have h := Finset.card_pos.mpr hA; omega) i :=
  integerRowExtension_apply _ i

/-- Every index in the interval `[0,card A)` is mapped into the selected
nonempty coordinate set by its sorted integer extension. -/
theorem finiteSetExtension_mem (A : Finset ℤ) (hA : A.Nonempty) {i : ℤ}
    (hi : i ∈ Finset.Ico 0 (A.card : ℤ)) : finiteSetExtension A hA i ∈ A := by
  have hc := Finset.card_pos.mpr hA
  rw [Finset.mem_Ico] at hi
  let j : Fin (A.card - 1 + 1) := ⟨i.toNat, by omega⟩
  have hj : (j : ℤ) = i := by dsimp [j]; omega
  rw [← hj, finiteSetExtension_apply]
  exact A.orderEmbOfFin_mem _ j

/-- Summing any real function over the interval `[0,card A)` after sorted integer
reindexing is exactly its sum over the selected nonempty finite coordinate set.
The assertion includes singleton sets and negative selected coordinates. -/
theorem finiteSetExtension_sum (A : Finset ℤ) (hA : A.Nonempty) (f : ℤ → ℝ) :
    (∑ i ∈ Finset.Ico 0 (A.card : ℤ), f (finiteSetExtension A hA i)) = ∑ i ∈ A, f i := by
  have hc := Finset.card_pos.mpr hA
  have hcard : A.card = A.card - 1 + 1 := by omega
  refine Finset.sum_nbij (finiteSetExtension A hA) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hi
    exact finiteSetExtension_mem A hA hi
  · intro i _hi j _hj hij
    exact (finiteSetExtension_strictMono A hA).injective hij
  · intro i hi
    have hs : i ∈ Set.range (A.orderEmbOfFin hcard) := by
      rw [A.range_orderEmbOfFin hcard]
      exact hi
    obtain ⟨j, hj⟩ := Set.mem_range.mp hs
    refine ⟨(j : ℤ), ?_, ?_⟩
    · change (j : ℤ) ∈ Finset.Ico 0 (A.card : ℤ)
      rw [Finset.mem_Ico]
      omega
    · exact (finiteSetExtension_apply A hA j).trans hj

end StrongMixing
