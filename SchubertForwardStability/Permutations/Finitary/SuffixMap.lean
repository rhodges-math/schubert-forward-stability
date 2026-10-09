import SchubertForwardStability.Permutations.Finitary.InitialMap
import SchubertForwardStability.Permutations.Finitary.PositiveShift
import Mathlib.Tactic

/-! # Permutations encoded by shifted bounded suffix values

If a permutation maps the positions `a+1, ..., a+b` to values in `{a+1, ..., a+b}`, then its
values there, shifted down by `a`, are those of a permutation supported in `[1, b]`.
-/

namespace FinitaryPerm

/-- A shifted suffix on the consecutive alphabet a+1 through a+b has an initial factor. -/
theorem exists_suffix_agree (a b : ℕ) (w : FinitaryPerm ℕ+)
    (hBound : ∀ t : ℕ+, (t : ℕ) ≤ b →
      a < (w (shiftPosition (a + 1) t) : ℕ) ∧
        (w (shiftPosition (a + 1) t) : ℕ) ≤ a + b) :
    ∃ v : FinitaryPerm ℕ+, IsSupported b v ∧
      ∀ t : ℕ+, (t : ℕ) ≤ b →
        shiftPosition a (v t) = w (shiftPosition (a + 1) t) := by
  let f : Fin b → ℕ+ := fun i =>
    ⟨(w (shiftPosition (a + 1) (positiveIndex b i).val) : ℕ) - a, by
      have h := (hBound _ (positiveIndex b i).property).1
      omega⟩
  have hb : ∀ i, (f i : ℕ) ≤ b := by
    intro i
    have h := (hBound _ (positiveIndex b i).property).2
    change (w (shiftPosition (a + 1) (positiveIndex b i).val) : ℕ) - a ≤ b
    omega
  have hf : Function.Injective f := by
    intro i j h
    apply (positiveIndex b).injective
    apply Subtype.ext
    apply (shiftPosition (a + 1)).injective
    apply w.injective
    apply PNat.eq
    have hx := congrArg PNat.val h
    change (w (shiftPosition (a + 1) (positiveIndex b i).val) : ℕ) - a =
      (w (shiftPosition (a + 1) (positiveIndex b j).val) : ℕ) - a at hx
    have hi := (hBound _ (positiveIndex b i).property).1
    have hj := (hBound _ (positiveIndex b j).property).1
    omega
  refine ⟨initialPerm b f hb hf, initialPerm_supported b f hb hf, ?_⟩
  intro t ht
  let i := (positiveIndex b).symm ⟨t, ht⟩
  have hIndex : (positiveIndex b i).val = t :=
    congrArg Subtype.val ((positiveIndex b).apply_symm_apply ⟨t, ht⟩)
  have hValue := initialPerm_apply b f hb hf i
  rw [hIndex] at hValue
  apply PNat.eq
  have hx := congrArg PNat.val hValue
  change (initialPerm b f hb hf t : ℕ) =
    (w (shiftPosition (a + 1) (positiveIndex b i).val) : ℕ) - a at hx
  rw [hIndex] at hx
  change a + (initialPerm b f hb hf t : ℕ) = (w (shiftPosition (a + 1) t) : ℕ)
  have h := (hBound t ht).1
  omega

end FinitaryPerm
