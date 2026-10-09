import SchubertForwardStability.Permutations.Random.Uniform
import SchubertForwardStability.Permutations.ForMathlib.FiberUniform

/-! # Uniform statistic laws from finite fibers

Equal fiber cardinalities determine the pushforward of finite uniform laws.
For permutation families, this equality also determines the joint statistic
law of independent uniform pairs and every measurable function of the pair.
Empty sampling families are included as zero measures.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace FinitaryPerm

variable {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]

/-- Equal statistic fibers in finite permutation families give the same uniform statistic law. -/
theorem map_unif_eq_of_fibers (W V : Finset (FinitaryPerm ℕ+))
    (f g : FinitaryPerm ℕ+ → β)
    (h : ∀ b, (W.filter fun w => f w = b).card = (V.filter fun w => g w = b).card) :
    (unif W).map f = (unif V).map g :=
  map_uniform_eq_of_fibers W V f g (measurable_of_countable f)
    (measurable_of_countable g) h

/-- The two statistic coordinates of independent uniform pairs have matching joint laws. -/
theorem map_pairLaw_eq_of_fibers (W V : Finset (FinitaryPerm ℕ+))
    (f g : FinitaryPerm ℕ+ → β)
    (h : ∀ b, (W.filter fun w => f w = b).card = (V.filter fun w => g w = b).card) :
    (pairLaw W).map (Prod.map f f) = (pairLaw V).map (Prod.map g g) := by
  rw [pairLaw_eq_prod, pairLaw_eq_prod,
    ← Measure.map_prod_map _ _ (measurable_of_countable f) (measurable_of_countable f),
    ← Measure.map_prod_map _ _ (measurable_of_countable g) (measurable_of_countable g),
    map_unif_eq_of_fibers W V f g h]

/-- Matching fibers give identical distributions of the independent statistic pairs. -/
theorem identDistrib_pairLaw_of_fibers (W V : Finset (FinitaryPerm ℕ+))
    (f g : FinitaryPerm ℕ+ → β)
    (h : ∀ b, (W.filter fun w => f w = b).card = (V.filter fun w => g w = b).card) :
    IdentDistrib (Prod.map f f) (Prod.map g g) (pairLaw W) (pairLaw V) :=
  ⟨(measurable_of_countable _).aemeasurable, (measurable_of_countable _).aemeasurable,
    map_pairLaw_eq_of_fibers W V f g h⟩

/-- Every function of a pair of matching finite statistics has the same distribution. -/
theorem identDistrib_pairStat_of_fibers {γ : Type*} [MeasurableSpace γ]
    (W V : Finset (FinitaryPerm ℕ+)) (f g : FinitaryPerm ℕ+ → β) (F : β × β → γ)
    (h : ∀ b, (W.filter fun w => f w = b).card = (V.filter fun w => g w = b).card) :
    IdentDistrib (fun p => F (f p.1, f p.2)) (fun p => F (g p.1, g p.2))
      (pairLaw W) (pairLaw V) :=
  (identDistrib_pairLaw_of_fibers W V f g h).comp (measurable_of_countable F)

/-- Every real function of a pair of matching finite statistics has equal expectations. -/
theorem integral_pairStat_eq_of_fibers (W V : Finset (FinitaryPerm ℕ+))
    (f g : FinitaryPerm ℕ+ → β) (F : β × β → ℝ)
    (h : ∀ b, (W.filter fun w => f w = b).card = (V.filter fun w => g w = b).card) :
    (∫ p, F (f p.1, f p.2) ∂pairLaw W) = ∫ p, F (g p.1, g p.2) ∂pairLaw V :=
  (identDistrib_pairStat_of_fibers W V f g F h).integral_eq

/-- Every uniform ordered pair lies in its two sampling families almost surely. -/
theorem ae_mem_pairLaw (W : Finset (FinitaryPerm ℕ+)) :
    ∀ᵐ p ∂pairLaw W, p.1 ∈ W ∧ p.2 ∈ W := by
  by_cases hW : W.Nonempty
  · filter_upwards [ae_mem_uniformOn_finset (W.product W) (hW.product hW)] with p hp
    exact Finset.mem_product.mp hp
  · have hw : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    simp [hw, pairLaw]

/-- Statistics factoring through matching fibers on the sampled pairs have the same law. -/
theorem identDistrib_pairFactor_of_fibers {γ : Type*} [MeasurableSpace γ]
    (W V : Finset (FinitaryPerm ℕ+)) (f g : FinitaryPerm ℕ+ → β) (F : β × β → γ)
    (X Y : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ → γ)
    (h : ∀ b, (W.filter fun w => f w = b).card = (V.filter fun w => g w = b).card)
    (hX : ∀ p, p.1 ∈ W → p.2 ∈ W → X p = F (f p.1, f p.2))
    (hY : ∀ p, p.1 ∈ V → p.2 ∈ V → Y p = F (g p.1, g p.2)) :
    IdentDistrib X Y (pairLaw W) (pairLaw V) := by
  have hx : (fun p => F (f p.1, f p.2)) =ᵐ[pairLaw W] X := by
    filter_upwards [ae_mem_pairLaw W] with p hp
    exact (hX p hp.1 hp.2).symm
  have hy : (fun p => F (g p.1, g p.2)) =ᵐ[pairLaw V] Y := by
    filter_upwards [ae_mem_pairLaw V] with p hp
    exact (hY p hp.1 hp.2).symm
  have hd := identDistrib_pairStat_of_fibers W V f g F h
  exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst hx).symm.trans hd).trans
    (IdentDistrib.of_ae_eq hd.aemeasurable_snd hy)

/-- Real statistics factoring through matching finite fibers have equal pair expectations. -/
theorem integral_pairFactor_eq_of_fibers (W V : Finset (FinitaryPerm ℕ+))
    (f g : FinitaryPerm ℕ+ → β) (F : β × β → ℝ)
    (X Y : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ → ℝ)
    (h : ∀ b, (W.filter fun w => f w = b).card = (V.filter fun w => g w = b).card)
    (hX : ∀ p, p.1 ∈ W → p.2 ∈ W → X p = F (f p.1, f p.2))
    (hY : ∀ p, p.1 ∈ V → p.2 ∈ V → Y p = F (g p.1, g p.2)) :
    (∫ p, X p ∂pairLaw W) = ∫ p, Y p ∂pairLaw V :=
  (identDistrib_pairFactor_of_fibers W V f g F X Y h hX hY).integral_eq

end FinitaryPerm
