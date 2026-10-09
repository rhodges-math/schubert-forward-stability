import SchubertForwardStability.Paper.Uniform.Moments
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Real.Sqrt

/-! # Divergence of the uniform record variance

## Main definitions

* `reciprocalSquares`: the finite reciprocal-square correction to harmonic variance.
* `recordVariance`: the sum of the reciprocal Bernoulli variances.

## Main results

The correction is bounded by two, while record variance and standard deviation
diverge. The centered second-moment sum equals variance and dominates the third sum.

## Implementation notes

Variance is positive from size two. Empty and singleton record rows have zero variance.
The correction bound is proved by a finite telescoping inequality.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Section 3.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory Filter
open scoped Classical BigOperators Topology

/-- The reciprocal-square partial sum of a record row. -/
noncomputable def reciprocalSquares (n : ℕ) : ℝ :=
  ∑ i : Fin n, ((i.val : ℝ) + 1)⁻¹ ^ 2

/-- The total Bernoulli variance of the first n uniform records. -/
noncomputable def recordVariance (n : ℕ) : ℝ :=
  ∑ i : Fin n, ((i.val : ℝ) + 1)⁻¹ * (1 - ((i.val : ℝ) + 1)⁻¹)

/-- The sum of reciprocal probabilities of a finite record row is harmonic. -/
theorem sum_reciprocal_harmonic (n : ℕ) :
    (∑ i : Fin n, ((i.val : ℝ) + 1)⁻¹) = (harmonic n : ℝ) := by
  rw [← Finset.sum_range (fun i : ℕ => ((i : ℝ) + 1)⁻¹)]
  simp [harmonic, Rat.cast_sum]

/-- Record variance is harmonic mean minus the reciprocal-square correction. -/
theorem recordVariance_eq_harmonic (n : ℕ) :
    recordVariance n = (harmonic n : ℝ) - reciprocalSquares n := by
  simp only [recordVariance, mul_sub, mul_one, ← pow_two, Finset.sum_sub_distrib,
    sum_reciprocal_harmonic, reciprocalSquares]

/-- The reciprocal-square correction adds one new square at each ambient step. -/
theorem reciprocalSquares_succ (n : ℕ) :
    reciprocalSquares (n + 1) = reciprocalSquares n + ((n : ℝ) + 1)⁻¹ ^ 2 := by
  simp only [reciprocalSquares, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

/-- The reciprocal-square correction is nonnegative. -/
theorem reciprocalSquares_nonneg (n : ℕ) : 0 ≤ reciprocalSquares n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A telescoping rational bound controls every reciprocal-square partial sum. -/
theorem reciprocalSquares_le (n : ℕ) :
    reciprocalSquares n ≤ 2 - 2 * ((n : ℝ) + 1)⁻¹ := by
  induction n with
  | zero => norm_num [reciprocalSquares]
  | succ n ih =>
    have htel : ((n : ℝ) + 1)⁻¹ ^ 2 ≤
        2 * (((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      field_simp
      nlinarith
    rw [reciprocalSquares_succ]
    calc
      _ ≤ (2 - 2 * ((n : ℝ) + 1)⁻¹) +
          2 * (((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹) := add_le_add ih htel
      _ = _ := by push_cast; ring

/-- The reciprocal-square correction is at most two. -/
theorem reciprocalSquares_le_two (n : ℕ) : reciprocalSquares n ≤ 2 :=
  (reciprocalSquares_le n).trans (by
    have h : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    linarith)

private theorem record_term_nonneg (i : ℕ) :
    0 ≤ ((i : ℝ) + 1)⁻¹ * (1 - ((i : ℝ) + 1)⁻¹) := by
  have hx : (1 : ℝ) ≤ (i : ℝ) + 1 := by linarith [Nat.cast_nonneg i (α := ℝ)]
  have hi : ((i : ℝ) + 1)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr hx
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hi)

/-- Every finite uniform record variance is nonnegative. -/
theorem recordVariance_nonneg (n : ℕ) : 0 ≤ recordVariance n :=
  Finset.sum_nonneg fun i _ => record_term_nonneg i.val

/-- A uniform record row has positive variance from size two onward. -/
theorem recordVariance_pos (n : ℕ) (hn : 2 ≤ n) : 0 < recordVariance n := by
  let i : Fin n := ⟨1, by omega⟩
  have h : (1 / 4 : ℝ) ≤ recordVariance n := by
    calc
      _ = ((i.val : ℝ) + 1)⁻¹ * (1 - ((i.val : ℝ) + 1)⁻¹) := by norm_num [i]
      _ ≤ _ := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin n => ((j.val : ℝ) + 1)⁻¹ * (1 - ((j.val : ℝ) + 1)⁻¹))
        (fun j _ => record_term_nonneg j.val) (Finset.mem_univ i)
  linarith

/-- Harmonic mean minus two is a uniform lower bound for record variance. -/
theorem harmonic_sub_two_le_recordVariance (n : ℕ) :
    (harmonic n : ℝ) - 2 ≤ recordVariance n := by
  rw [recordVariance_eq_harmonic]
  linarith [reciprocalSquares_le_two n]

/-- Uniform record variance diverges to infinity. -/
theorem tendsto_recordVariance_atTop : Tendsto recordVariance atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hh : Tendsto (fun n : ℕ => (harmonic n : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono _ hlog
    intro n
    simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic n
  apply tendsto_atTop_mono harmonic_sub_two_le_recordVariance
  simpa only [sub_eq_add_neg] using
    tendsto_atTop_add_const_right atTop (-2 : ℝ) hh

/-- The uniform record standard deviation diverges to infinity. -/
theorem tendsto_sqrt_recordVariance_atTop :
    Tendsto (fun n => Real.sqrt (recordVariance n)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_recordVariance_atTop

/-- The total centered second moment is exactly record variance. -/
theorem sum_integral_centeredRecord_sq (n : ℕ) :
    (∑ i : Fin n, ∫ w, centeredRecord i.val.succPNat w ^ 2
      ∂unif (symmetricGroup n)) = recordVariance n := by
  apply Finset.sum_congr rfl
  intro i hi
  have h := integral_centeredRecord_sq n i.val.succPNat
    (by change i.val + 1 ≤ n; omega)
  simpa only [Nat.succPNat_coe, Nat.cast_succ] using h

/-- The total centered third absolute moment is at most record variance. -/
theorem sum_integral_abs_centeredRecord_cube_le (n : ℕ) :
    (∑ i : Fin n, ∫ w, |centeredRecord i.val.succPNat w| ^ 3
      ∂unif (symmetricGroup n)) ≤ recordVariance n := by
  apply Finset.sum_le_sum
  intro i hi
  have h := integral_abs_centeredRecord_cube n i.val.succPNat
    (by change i.val + 1 ≤ n; omega)
  simpa only [Nat.succPNat_coe, Nat.cast_succ] using h

end RecordStability
