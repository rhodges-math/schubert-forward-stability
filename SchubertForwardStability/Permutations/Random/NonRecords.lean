import SchubertForwardStability.Permutations.Random.Records

/-!
# Uniform non-record indicators

## Main results

Non-record indicators are mutually independent. Their zero-event probabilities are
reciprocal positions and their means are one minus the reciprocal position.

## Implementation notes

These results use the complementary natural indicators of the record family.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace FinitaryPerm

noncomputable section

/-- Non-record indicators are mutually independent under every ambient uniform law. -/
theorem iIndepFun_uniform_nonRecords (n : ℕ) :
    iIndepFun (fun i : Fin n => fun w : FinitaryPerm ℕ+ =>
      w.nonRecordIndicator i.val.succPNat) (unif (symmetricGroup n)) := by
  have h := (iIndepFun_uniform_records n).comp (fun _ (a : ℕ) => 1 - a)
    (fun _ => measurable_of_countable _)
  have he : (fun i : Fin n => fun w : FinitaryPerm ℕ+ =>
      w.nonRecordIndicator i.val.succPNat) =
      (fun i : Fin n => (fun a : ℕ => 1 - a) ∘
        fun w : FinitaryPerm ℕ+ => 1 - w.nonRecordIndicator i.val.succPNat) := by
    funext i w
    by_cases hr : IsRecord w i.val.succPNat <;> simp [nonRecordIndicator, hr]
  rw [he]
  exact h

/-- The zero event of a non-record indicator has reciprocal probability. -/
theorem uniform_nonRecord_zero (n : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ n) :
    (unif (symmetricGroup n)).real {w | w.nonRecordIndicator j = 0} =
      ((j : ℕ) : ℝ)⁻¹ := by
  have he : {w : FinitaryPerm ℕ+ | w.nonRecordIndicator j = 0} =
      {w : FinitaryPerm ℕ+ | IsRecord w j} := by
    ext w
    by_cases hr : IsRecord w j <;> simp [nonRecordIndicator, hr]
  rw [he]
  exact uniform_record_probability n j hj

/-- The mean non-record indicator is one minus the reciprocal position. -/
theorem integral_uniform_nonRecord (n : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ n) :
    (∫ w, (w.nonRecordIndicator j : ℝ) ∂unif (symmetricGroup n)) =
      (((j : ℕ) : ℝ) - 1) / (j : ℕ) := by
  have he : (fun w : FinitaryPerm ℕ+ => (w.nonRecordIndicator j : ℝ)) =
      {w : FinitaryPerm ℕ+ | IsRecord w j}ᶜ.indicator (fun _ => (1 : ℝ)) := by
    funext w
    by_cases hr : IsRecord w j <;> simp [nonRecordIndicator, hr]
  rw [he, integral_indicator_const (1 : ℝ) (by trivial), smul_eq_mul, mul_one,
    probReal_compl_eq_one_sub (by trivial), uniform_record_probability n j hj]
  have hp : ((j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (PNat.pos j).ne'
  field_simp

end

end FinitaryPerm
