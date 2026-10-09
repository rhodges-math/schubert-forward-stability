import SchubertForwardStability.Permutations.Random.Records
import SchubertForwardStability.Permutations.Statistics.RecordSums
import SchubertForwardStability.Permutations.ForMathlib.UniformIntegrals
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Uniform record means and centered moments

## Main definitions

* `centeredRecord`: a real record indicator centered by its reciprocal probability.

## Main results

The record count has harmonic mean. Centered record rows have zero mean, Bernoulli
second moment, bounded third absolute moment, and mutually independent coordinates.

## Implementation notes

Moment identities require positions within the sampling range. Absolute bounds and
Lp membership hold at every position. Size zero is included in the harmonic mean.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Section 3.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

private theorem integral_unif_sum (n : ℕ) {ι : Type*} (t : Finset ι)
    (f : ι → FinitaryPerm ℕ+ → ℝ) :
    (∫ w, ∑ j ∈ t, f j w ∂unif (symmetricGroup n)) =
      ∑ j ∈ t, ∫ w, f j w ∂unif (symmetricGroup n) :=
  integral_uniform_finsetSum _ _ _

private theorem integral_unif_add (n : ℕ) (f g : FinitaryPerm ℕ+ → ℝ) :
    (∫ w, f w + g w ∂unif (symmetricGroup n)) =
      (∫ w, f w ∂unif (symmetricGroup n)) + ∫ w, g w ∂unif (symmetricGroup n) :=
  integral_uniform_finset_add _ _ _

private theorem integral_unif_sub (n : ℕ) (f g : FinitaryPerm ℕ+ → ℝ) :
    (∫ w, f w - g w ∂unif (symmetricGroup n)) =
      (∫ w, f w ∂unif (symmetricGroup n)) - ∫ w, g w ∂unif (symmetricGroup n) :=
  integral_uniform_finset_sub _ _ _

/-- A real record indicator centered by the reciprocal position. -/
noncomputable def centeredRecord (i : ℕ+) (w : FinitaryPerm ℕ+) : ℝ :=
  ((1 - w.nonRecordIndicator i : ℕ) : ℝ) - ((i : ℕ) : ℝ)⁻¹

/-- The mean uniform record count is the harmonic number, including size zero. -/
theorem integral_uniform_recordCount (n : ℕ) :
    (∫ w, (recordCount n w : ℝ) ∂unif (symmetricGroup n)) = (harmonic n : ℝ) := by
  have he : (fun w : FinitaryPerm ℕ+ => (recordCount n w : ℝ)) =
      (fun w => ∑ j ∈ positions n, ((1 - w.nonRecordIndicator j : ℕ) : ℝ)) := by
    funext w
    rw [recordCount_eq_sum, Nat.cast_sum]
  rw [he, integral_unif_sum]
  calc
    _ = ∑ j ∈ positions n, ((j : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_uniform_record n j ((mem_positions n j).mp hj)
    _ = (harmonic n : ℝ) := by
      rw [positions, Finset.sum_image]
      · rw [Finset.sum_fin_eq_sum_range]
        simp only [positiveIndex_val, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        apply Finset.sum_congr rfl
        intro i hi
        rw [dite_eq_left (Finset.mem_range.mp hi)]
      · intro a _ b _ hab
        exact (positiveIndex n).injective (Subtype.ext hab)

/-- A reciprocal-centered record indicator is bounded in absolute value by one. -/
theorem abs_centeredRecord_le (i : ℕ+) (w : FinitaryPerm ℕ+) :
    |centeredRecord i w| ≤ 1 := by
  have hp : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast PNat.pos i
  have hpi : 0 ≤ (((i : ℕ) : ℝ)⁻¹) := inv_nonneg.mpr (by positivity)
  have hle : (((i : ℕ) : ℝ)⁻¹) ≤ 1 := by
    exact (inv_le_one₀ (by positivity)).mpr hp
  by_cases hr : IsRecord w i <;>
    simp only [centeredRecord, nonRecordIndicator, hr, ite_true, ite_false,
      Nat.sub_zero, Nat.sub_self, Nat.cast_one, Nat.cast_zero]
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [zero_sub, abs_neg, abs_of_nonneg hpi]
    exact hle

/-- Centered record indicators belong to every finite-law Lp space. -/
theorem memLp_centeredRecord (n : ℕ) (i : ℕ+) (p : ENNReal) :
    MemLp (centeredRecord i) p (unif (symmetricGroup n)) := by
  apply MemLp.of_bound ((measurable_of_countable _).aestronglyMeasurable) 1
  exact Filter.Eventually.of_forall fun w => by
    simpa only [Real.norm_eq_abs] using abs_centeredRecord_le i w

/-- The reciprocal-centered uniform record indicator has zero mean. -/
theorem integral_centeredRecord (n : ℕ) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    (∫ w, centeredRecord i w ∂unif (symmetricGroup n)) = 0 := by
  unfold centeredRecord
  rw [integral_unif_sub]
  rw [integral_uniform_record n i hi]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self]

/-- The second centered record moment is the reciprocal Bernoulli variance. -/
theorem integral_centeredRecord_sq (n : ℕ) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    (∫ w, (centeredRecord i w) ^ 2 ∂unif (symmetricGroup n)) =
      (((i : ℕ) : ℝ)⁻¹) * (1 - (((i : ℕ) : ℝ)⁻¹)) := by
  have he : (fun w : FinitaryPerm ℕ+ => (centeredRecord i w) ^ 2) =
      (fun w => (1 - 2 * (((i : ℕ) : ℝ)⁻¹)) *
        ((1 - w.nonRecordIndicator i : ℕ) : ℝ) + (((i : ℕ) : ℝ)⁻¹) ^ 2) := by
    funext w
    by_cases hr : IsRecord w i <;>
      simp only [centeredRecord, nonRecordIndicator, hr, ite_true, ite_false,
        Nat.sub_zero, Nat.sub_self, Nat.cast_one, Nat.cast_zero] <;> ring
  rw [he, integral_unif_add, integral_const_mul,
    integral_uniform_record n i hi]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- The third centered absolute record moment is bounded by its Bernoulli variance. -/
theorem integral_abs_centeredRecord_cube (n : ℕ) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    (∫ w, |centeredRecord i w| ^ 3 ∂unif (symmetricGroup n)) ≤
      (((i : ℕ) : ℝ)⁻¹) * (1 - (((i : ℕ) : ℝ)⁻¹)) := by
  rw [← integral_centeredRecord_sq n i hi]
  apply integral_uniform_finset_mono
  intro w hw
  have hb := abs_centeredRecord_le i w
  calc
    |centeredRecord i w| ^ 3 = |centeredRecord i w| ^ 2 * |centeredRecord i w| := by ring
    _ ≤ |centeredRecord i w| ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = (centeredRecord i w) ^ 2 := by rw [mul_one, sq_abs]

/-- Centered record rows remain mutually independent under the uniform law. -/
theorem iIndepFun_centeredRecord (n : ℕ) :
    iIndepFun (fun i : Fin n => centeredRecord i.val.succPNat)
      (unif (symmetricGroup n)) := by
  exact (iIndepFun_uniform_records n).comp
    (fun i (a : ℕ) => (a : ℝ) - ((i.val + 1 : ℕ) : ℝ)⁻¹)
    (fun _ => measurable_of_countable _)

end RecordStability
