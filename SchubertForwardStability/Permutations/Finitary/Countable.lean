import SchubertForwardStability.Permutations.Finitary.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Basic.Countable.Basic

/-! # Countability of finitely supported permutations

## Main results

Finitary permutations of a countable carrier form a countable type.

## Implementation notes

A permutation is encoded by the finite graph of its action on moved points.
Fixed points are recovered as the complement of the graph's domain.
-/

namespace FinitaryPerm

variable {α : Type*} [DecidableEq α]

noncomputable section

private def finiteGraph (w : FinitaryPerm α) : Finset (α × α) :=
  w.movedPoints.image fun a => (a, w a)

private theorem finiteGraph_injective : Function.Injective (finiteGraph (α := α)) := by
  intro w v h
  apply ext
  intro a
  by_cases hw : w a = a
  · by_cases hv : v a = a
    · exact hw.trans hv.symm
    · have ha : (a, v a) ∈ finiteGraph v :=
        Finset.mem_image.mpr ⟨a, (mem_movedPoints _ _).mpr hv, rfl⟩
      rw [← h] at ha
      obtain ⟨b, hb, he⟩ := Finset.mem_image.mp ha
      have hba : b = a := congrArg Prod.fst he
      subst b
      exact False.elim ((mem_movedPoints _ _).mp hb hw)
  · have ha : (a, w a) ∈ finiteGraph w :=
      Finset.mem_image.mpr ⟨a, (mem_movedPoints _ _).mpr hw, rfl⟩
    rw [h] at ha
    obtain ⟨b, _, he⟩ := Finset.mem_image.mp ha
    have hba : b = a := congrArg Prod.fst he
    subst b
    exact (congrArg Prod.snd he).symm

/-- Finitary permutations of a countable type form a countable type. -/
instance [Countable α] : Countable (FinitaryPerm α) := finiteGraph_injective.countable

end

end FinitaryPerm
