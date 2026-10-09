import SchubertForwardStability.Permutations.Random.RecordCode
import SchubertForwardStability.Permutations.ForMathlib.UniformCode
import SchubertForwardStability.Permutations.Random.FamilyInstances

/-!
# Uniform record independence

## Main results

The uniform symmetric-group law maps to the product law of left inversion coordinates.
Record indicators are mutually independent with reciprocal probability and expectation.

## Implementation notes

The total coordinates are the left inversion counts, also outside the finite
support family. Size zero gives the empty independent coordinate family.

## References

* A. Renyi, Theorie des elements saillants d'une suite d'observations,
  Annales faculte sciences Clermont Math. 8(2), 7-13 (1962), Lemma 1.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace FinitaryPerm

noncomputable section

/-- The total left inversion coordinates agree with the finite left-code equivalence. -/
theorem leftCoordinates_eq (n : ℕ) (w : {w : FinitaryPerm ℕ+ // IsSupported n w}) :
    leftCoordinates n w.val = leftCodeEquiv n w := by
  funext i
  apply Fin.ext
  exact (leftCodeEquiv_apply n w i).symm

/-- A record is exactly a zero left inversion coordinate. -/
theorem isRecord_iff_leftCoordinate (n : ℕ) (w : FinitaryPerm ℕ+) (i : Fin n) :
    IsRecord w i.val.succPNat ↔ leftCoordinates n w i = 0 := by
  rw [isRecord_iff_leftInversionCount]
  change (leftCoordinates n w i).val = 0 ↔ leftCoordinates n w i = 0
  exact Fin.val_eq_zero_iff

/-- Uniform finite permutations have the uniform law on all left inversion coordinates. -/
theorem map_leftCoordinates (n : ℕ) :
    (unif (symmetricGroup n)).map (leftCoordinates n) =
      uniformOn (Set.univ : Set (LeftCoordinates n)) := by
  let : Fintype {w : FinitaryPerm ℕ+ // IsSupported n w} :=
    Fintype.ofEquiv (Equiv.Perm (Fin n)) (finiteEquiv n)
  have hc : (uniformOn (Set.univ : Set {w : FinitaryPerm ℕ+ // IsSupported n w})).map
      Subtype.val = unif (symmetricGroup n) := by
    rw [map_uniformOn_finite_injective Subtype.val Subtype.val_injective, unif]
    congr 1
    ext w
    simp only [Finset.mem_coe, Finset.mem_image, mem_symmetricGroup]
    constructor
    · rintro ⟨v, _, rfl⟩
      exact v.property
    · intro hw
      exact ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩
  rw [← hc, Measure.map_map (measurable_of_countable _) measurable_subtype_coe]
  have he : leftCoordinates n ∘ Subtype.val = leftCodeEquiv n :=
    funext (leftCoordinates_eq n)
  rw [he]
  exact map_uniformOn_equiv (leftCodeEquiv n)

/-- Each left inversion coordinate is uniform on its increasing-bound finite type. -/
theorem map_leftCoordinate (n : ℕ) (i : Fin n) :
    (unif (symmetricGroup n)).map (fun w => leftCoordinates n w i) =
      uniformOn (Set.univ : Set (Fin (i.val + 1))) := by
  change (unif (symmetricGroup n)).map (Function.eval i ∘ leftCoordinates n) = _
  rw [← Measure.map_map (measurable_pi_apply i)
      (measurable_of_countable (leftCoordinates n)),
    map_leftCoordinates, uniformOn_univ_pi_dep]
  exact (measurePreserving_eval (fun j : Fin n =>
    uniformOn (Set.univ : Set (Fin (j.val + 1)))) i).map_eq

/-- The left inversion coordinates are mutually independent under the uniform group law. -/
theorem iIndepFun_leftCoordinates (n : ℕ) :
    iIndepFun (fun i : Fin n => fun w : FinitaryPerm ℕ+ => leftCoordinates n w i)
      (unif (symmetricGroup n)) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun _ => (measurable_of_countable _).aemeasurable)).mpr
  rw [map_leftCoordinates, uniformOn_univ_pi_dep]
  congr 1
  funext i
  exact (map_leftCoordinate n i).symm

/-- The natural record indicator is the zero-coordinate indicator. -/
theorem recordIndicator_leftCoordinate (n : ℕ) (w : FinitaryPerm ℕ+) (i : Fin n) :
    1 - w.nonRecordIndicator i.val.succPNat =
      if leftCoordinates n w i = 0 then 1 else 0 := by
  by_cases hr : IsRecord w i.val.succPNat
  · simp [nonRecordIndicator, hr, (isRecord_iff_leftCoordinate n w i).mp hr]
  · simp [nonRecordIndicator, hr, mt (isRecord_iff_leftCoordinate n w i).mpr hr]

/-- Record indicators are mutually independent, including the empty size-zero family. -/
theorem iIndepFun_uniform_records (n : ℕ) :
    iIndepFun (fun i : Fin n => fun w : FinitaryPerm ℕ+ =>
      1 - w.nonRecordIndicator i.val.succPNat) (unif (symmetricGroup n)) := by
  have h := (iIndepFun_leftCoordinates n).comp
    (fun i (a : Fin (i.val + 1)) => if a = 0 then (1 : ℕ) else 0)
    (fun _ => measurable_of_countable _)
  have he : (fun i : Fin n => fun w : FinitaryPerm ℕ+ =>
      1 - w.nonRecordIndicator i.val.succPNat) =
      (fun i : Fin n => (fun a : Fin (i.val + 1) => if a = 0 then (1 : ℕ) else 0) ∘
        fun w : FinitaryPerm ℕ+ => leftCoordinates n w i) := by
    funext i w
    exact recordIndicator_leftCoordinate n w i
  rw [he]
  exact h

/-- The record event at a finite coordinate has reciprocal extended-real mass. -/
theorem uniform_record_mass (n : ℕ) (i : Fin n) :
    unif (symmetricGroup n) {w | IsRecord w i.val.succPNat} =
      ((i.val + 1 : ℕ) : ENNReal)⁻¹ := by
  have he : {w : FinitaryPerm ℕ+ | IsRecord w i.val.succPNat} =
      (fun w => leftCoordinates n w i) ⁻¹' {0} := by
    ext w
    exact isRecord_iff_leftCoordinate n w i
  rw [he, ← Measure.map_apply (measurable_of_countable _) (measurableSet_singleton 0),
    map_leftCoordinate, uniformOn_univ, Measure.count_singleton, one_div, Fintype.card_fin]

/-- A positive ambient position has reciprocal record probability. -/
theorem uniform_record_probability (n : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ n) :
    (unif (symmetricGroup n)).real {w | IsRecord w j} = ((j : ℕ) : ℝ)⁻¹ := by
  let i : Fin n := ⟨(j : ℕ) - 1, by have := PNat.pos j; omega⟩
  have hi : i.val.succPNat = j := by
    apply PNat.eq
    change (j : ℕ) - 1 + 1 = (j : ℕ)
    have := PNat.pos j
    omega
  have h := uniform_record_mass n i
  rw [hi] at h
  have hv : i.val + 1 = (j : ℕ) := congrArg PNat.val hi
  rw [hv] at h
  simp only [measureReal_def, h, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- The expectation of the natural record indicator is the reciprocal position. -/
theorem integral_uniform_record (n : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ n) :
    (∫ w, ((1 - w.nonRecordIndicator j : ℕ) : ℝ) ∂unif (symmetricGroup n)) =
      ((j : ℕ) : ℝ)⁻¹ := by
  have he : (fun w : FinitaryPerm ℕ+ => ((1 - w.nonRecordIndicator j : ℕ) : ℝ)) =
      {w : FinitaryPerm ℕ+ | IsRecord w j}.indicator (fun _ => (1 : ℝ)) := by
    funext w
    by_cases hr : IsRecord w j <;> simp [nonRecordIndicator, hr]
  rw [he, integral_indicator_const (1 : ℝ) (by trivial), smul_eq_mul, mul_one]
  exact uniform_record_probability n j hj

end

end FinitaryPerm
