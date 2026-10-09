import SchubertForwardStability.Permutations.Finitary.Basic
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! # Extension of finitary permutations along an embedding

Extending a permutation fixes every point outside the image of the embedding.
Finite moved support is transported into its finite image, giving an injective
group homomorphism compatible with transpositions.
-/

namespace FinitaryPerm

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

open scoped Classical

/-- Extend a finitary permutation along an embedding, fixing the complementary points. -/
noncomputable def embeddingPerm (e : α ↪ β) (w : FinitaryPerm α) : FinitaryPerm β :=
  ofPerm (w.val.viaEmbedding e) (by
    apply (w.finite_movedSet.image e).subset
    intro y hy
    by_cases hRange : y ∈ Set.range e
    · obtain ⟨x, rfl⟩ := hRange
      refine ⟨x, ?_, rfl⟩
      intro hFixed
      exact hy (by rw [Equiv.Perm.viaEmbedding_apply, hFixed])
    · exact (hy (Equiv.Perm.viaEmbedding_apply_of_notMem w.val e y hRange)).elim)

/-- The extended permutation acts through the embedding on its image. -/
theorem embeddingPerm_apply (e : α ↪ β) (w : FinitaryPerm α) (x : α) :
    embeddingPerm e w (e x) = e (w x) := Equiv.Perm.viaEmbedding_apply w.val e x

/-- The extended permutation fixes every point outside the embedding image. -/
theorem embeddingPerm_fixed (e : α ↪ β) (w : FinitaryPerm α) (y : β)
    (hy : y ∉ Set.range e) : embeddingPerm e w y = y :=
  Equiv.Perm.viaEmbedding_apply_of_notMem w.val e y hy

/-- Extension along an embedding is a group homomorphism on finitary permutations. -/
noncomputable def embeddingPermHom (e : α ↪ β) : FinitaryPerm α →* FinitaryPerm β where
  toFun := embeddingPerm e
  map_one' := Subtype.ext ((Equiv.Perm.viaEmbeddingHom e).map_one)
  map_mul' u v := Subtype.ext ((Equiv.Perm.viaEmbeddingHom e).map_mul u.val v.val)

/-- Extension along an embedding is injective. -/
theorem embeddingPerm_injective (e : α ↪ β) : Function.Injective (embeddingPerm e) := by
  intro u v he
  apply ext
  intro x
  apply e.injective
  have h := congrArg (fun w : FinitaryPerm β => w (e x)) he
  simpa only [embeddingPerm_apply] using h

/-- Extending a transposition exchanges the two corresponding image points. -/
theorem embeddingPerm_swap (e : α ↪ β) (a b : α) :
    embeddingPerm e (swap a b) = swap (e a) (e b) := by
  apply ext
  intro y
  by_cases hRange : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hRange
    by_cases hxa : x = a
    · subst x
      rw [embeddingPerm_apply, swap_apply_left, swap_apply_left]
    · by_cases hxb : x = b
      · subst x
        rw [embeddingPerm_apply, swap_apply_right, swap_apply_right]
      · rw [embeddingPerm_apply, swap_apply_of_ne hxa hxb,
          swap_apply_of_ne (fun he => hxa (e.injective he)) (fun he => hxb (e.injective he))]
  · rw [embeddingPerm_fixed e _ y hRange]
    exact (swap_apply_of_ne (fun he => hRange ⟨a, he.symm⟩)
      (fun he => hRange ⟨b, he.symm⟩)).symm

end FinitaryPerm
