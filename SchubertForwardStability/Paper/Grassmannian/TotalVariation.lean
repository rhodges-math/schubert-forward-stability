import SchubertForwardStability.Permutations.Random.GrassRecordLaw
import SchubertForwardStability.Permutations.Random.FamilyInstances
import SchubertForwardStability.LimitTheorems.TotalVariation.Support

/-! # Total variation of Grassmannian sampling laws

## Main results

The subset-pushforward law and the uniform law on the family differ only by the
excess identity mass and the equal deficits on nonidentity points. Their finite
half-sum gives the exact total variation and its powerset-ratio bound.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

namespace RecordStability

open FinitaryPerm LimitTheorems

private theorem powerset_gap (n : ℕ) : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
  have h := Finset.card_filter_le (positions n).powerset
    (fun V => subsetPermutation n V = 1)
  rw [card_subsetPermutation_one_fiber, Finset.card_powerset, card_positions] at h
  exact_mod_cast h

private theorem family_real_pos (n : ℕ) : 0 < (2 : ℝ) ^ n - n := by
  rw [← card_grassmannian_real]
  exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨1, one_mem_grassmannian n⟩)

/-- Each supported point of the uniform Grassmannian law has reciprocal mass. -/
theorem unif_grassmannian_real_singleton (n : ℕ) (w : FinitaryPerm ℕ+)
    (hw : w ∈ grassmannian n) :
    (unif (grassmannian n)).real {w} = 1 / ((2 : ℝ) ^ n - n) := by
  rw [unif, measureReal_def, uniformOn_finset_singleton, ite_eq_left hw,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, card_grassmannian_real, one_div]

private theorem mass_differences_nonneg (n : ℕ) :
    0 ≤ ((n : ℝ) + 1) / (2 : ℝ) ^ n - 1 / ((2 : ℝ) ^ n - n) ∧
      0 ≤ 1 / ((2 : ℝ) ^ n - n) - ((2 : ℝ) ^ n)⁻¹ := by
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  have hq := family_real_pos n
  constructor
  · apply sub_nonneg.mpr
    apply (div_le_div_iff₀ hq hp).mpr
    have hprod := mul_nonneg (Nat.cast_nonneg n (α := ℝ))
      (by linarith [powerset_gap n] : 0 ≤ (2 : ℝ) ^ n - n - 1)
    nlinarith
  · apply sub_nonneg.mpr
    rw [← one_div]
    apply (div_le_div_iff₀ hp hq).mpr
    nlinarith [Nat.cast_nonneg n (α := ℝ)]

private theorem grass_variation_sum (n : ℕ) :
    (∑ w ∈ grassmannian n,
      |(grassmannianLaw n).real {w} - (unif (grassmannian n)).real {w}|) =
      (((n : ℝ) + 1) / (2 : ℝ) ^ n - 1 / ((2 : ℝ) ^ n - n)) +
        ((2 : ℝ) ^ n - n - 1) *
          (1 / ((2 : ℝ) ^ n - n) - ((2 : ℝ) ^ n)⁻¹) := by
  have hm := one_mem_grassmannian n
  have hd := mass_differences_nonneg n
  rw [← Finset.add_sum_erase _ _ hm, grassmannianLaw_real_one,
    unif_grassmannian_real_singleton n 1 hm]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonneg hd.1]
  congr 1
  have he : (((grassmannian n).erase 1).card : ℝ) = (2 : ℝ) ^ n - n - 1 := by
    have h : (((grassmannian n).erase 1).card : ℝ) + 1 =
        ((grassmannian n).card : ℝ) := by
      exact_mod_cast Finset.card_erase_add_one hm
    rw [card_grassmannian_real] at h
    linarith
  calc
    _ = ∑ w ∈ (grassmannian n).erase 1,
        (1 / ((2 : ℝ) ^ n - n) - ((2 : ℝ) ^ n)⁻¹) := by
      apply Finset.sum_congr rfl
      intro w hw
      obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
      rw [grassmannianLaw_real_nonid n w hw hne,
        unif_grassmannian_real_singleton n w hw, abs_sub_comm, abs_of_nonneg hd.2]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, he]

/-- The two Grassmannian sampling laws have the exact finite total variation. -/
theorem grassmannian_totalVariation (n : ℕ) :
    LimitTheorems.totalVariation (grassmannianLaw n) (unif (grassmannian n)) =
      (n : ℝ) * ((2 : ℝ) ^ n - n - 1) /
        ((2 : ℝ) ^ n * ((2 : ℝ) ^ n - n)) := by
  rw [LimitTheorems.totalVariation_eq_half_sum_support (grassmannian n)
    (grassmannianLaw n) (unif (grassmannian n)) (ae_mem_grassmannianLaw n)
    (ae_mem_unif _ ⟨1, one_mem_grassmannian n⟩), grass_variation_sum]
  have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hq := (family_real_pos n).ne'
  field_simp
  ring

/-- Total variation is at most the ambient size divided by its powerset size. -/
theorem grassmannian_totalVariation_le (n : ℕ) :
    LimitTheorems.totalVariation (grassmannianLaw n) (unif (grassmannian n)) ≤
      (n : ℝ) / (2 : ℝ) ^ n := by
  rw [grassmannian_totalVariation]
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  have hq := family_real_pos n
  apply (div_le_div_iff₀ (mul_pos hp hq) hp).mpr
  nlinarith [mul_nonneg (Nat.cast_nonneg n (α := ℝ)) hp.le]

end RecordStability
