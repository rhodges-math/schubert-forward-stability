import SchubertForwardStability.Permutations.Random.Uniform

/-! # Event probabilities in finite permutation families

A uniform law supported on a finite family gives every event the number of its elements
in the family divided by the family cardinality, including for the empty family.
-/

namespace FinitaryPerm

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- An event under a finite uniform permutation law has its filtered-cardinality mass. -/
theorem unif_real_event (W : Finset (FinitaryPerm ℕ+)) (E : Set (FinitaryPerm ℕ+)) :
    (unif W).real E = ((W.filter fun w => w ∈ E).card : ℝ) / W.card := by
  have hSet : (W : Set (FinitaryPerm ℕ+)) ∩ E =
      (W.filter fun w => w ∈ E : Set (FinitaryPerm ℕ+)) := by ext w; simp
  have hInter : W ∩ (W.filter fun w => w ∈ E) = W.filter fun w => w ∈ E := by
    ext w
    simp
  have hμ : unif W E = ((W.filter fun w => w ∈ E).card : ENNReal) / W.card := by
    rw [unif, ← uniformOn_inter_self W.finite_toSet, hSet, uniformOn_apply_finset, hInter]
  simp only [measureReal_def, hμ, ENNReal.toReal_div, ENNReal.toReal_natCast]

end FinitaryPerm
