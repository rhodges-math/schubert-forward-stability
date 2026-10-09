import SchubertForwardStability.StrongMixing.Inequalities.IntervalMoments
import Mathlib.Data.Int.Interval

/-!
# Terminal interval log-Laplace estimates

The centered bounded-variable estimate and the geometric second-moment
bound give a quadratic log-Laplace bound for short intervals. Natural ranges and
integer half-open intervals are related by an explicit finite-sum bijection.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Summing a function over the integer half-open interval from `a` to `a + n`
is the same as summing its translated coordinates over the natural range `n`.
The identity includes zero length and arbitrary negative translations. -/
theorem sum_int_interval_eq (f : ℤ → ℝ) (a : ℤ) (n : ℕ) :
    (∑ i ∈ Finset.Ico a (a + n), f i) = ∑ k ∈ Finset.range n, f (a + k) := by
  symm
  refine Finset.sum_nbij (fun k : ℕ => a + (k : ℤ)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro k hk
    rw [Finset.mem_Ico]
    have hk := Finset.mem_range.mp hk
    omega
  · intro k hk l hl hkl
    change a + (k : ℤ) = a + (l : ℤ) at hkl
    omega
  · intro i hi
    change i ∈ Finset.Ico a (a + n) at hi
    rw [Finset.mem_Ico] at hi
    refine ⟨(i - a).toNat, ?_, ?_⟩
    · change (i - a).toNat ∈ Finset.range n
      rw [Finset.mem_range]
      omega
    · change a + ((i - a).toNat : ℤ) = i
      omega

/-- A centered bounded sequence with positive-lag geometric coefficient bound
has log-Laplace transform over an interval of length `n` at most
`t^2 * n * M^2 * (1 + 8*r/(1-r))`, provided `|t| * n * M <= 1`.
The interval may be empty, the bound may be zero, and the parameter may be negative. -/
theorem interval_log_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M r : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ω, |X i ω| ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ r ^ h)
    (a : ℤ) (n : ℕ) (t : ℝ) (hsmall : |t| * n * M ≤ 1) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ Finset.Ico a (a + n), X i ω) ∂μ) ≤
      t ^ 2 * n * M ^ 2 * (1 + 8 * r / (1 - r)) := by
  let P (ω : Ω) := ∑ k ∈ Finset.range n, X (a + k) ω
  have hb (ω : Ω) : |P ω| ≤ n * M := by
    simpa only [Finset.card_range] using
      abs_sum_le_card_mul (fun k : ℕ => X (a + k)) (Finset.range n)
        (fun k _ => hbound (a + k)) ω
  have hp : MemLp P 2 μ :=
    MemLp.of_bound
      (Finset.measurable_sum (Finset.range n) (fun k _ => hX (a + k))).aestronglyMeasurable
      (n * M) (Filter.Eventually.of_forall (fun ω => by simpa using hb ω))
  have hxi (i : ℤ) : Integrable (X i) μ :=
    (MemLp.of_bound (hX i).aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun ω => by simpa using hbound i ω)) :
        MemLp (X i) 1 μ).integrable le_rfl
  have hc : ∫ ω, P ω ∂μ = 0 := by
    rw [integral_finsetSum (Finset.range n) (f := fun k => X (a + k))
      (fun k _ => hxi (a + k))]
    simp only [hcenter, Finset.sum_const_zero]
  have hs : ∀ᵐ ω ∂μ, |t * P ω| ≤ 1 := Filter.Eventually.of_forall (fun ω => by
    calc
      |t * P ω| = |t| * |P ω| := abs_mul _ _
      _ ≤ |t| * (n * M) := mul_le_mul_of_nonneg_left (hb ω) (abs_nonneg _)
      _ ≤ 1 := by simpa only [mul_assoc] using hsmall)
  have hl := log_integral_exp_centered_le hp hc hs
  have hm := interval_second_moment_le μ X hX hcenter hM hbound hr0 hr1 hmix a n
  simp_rw [sum_int_interval_eq]
  change Real.log (∫ ω, Real.exp (t * P ω) ∂μ) ≤ _
  calc
    _ ≤ t ^ 2 * (∫ ω, (P ω) ^ 2 ∂μ) := hl
    _ ≤ t ^ 2 * (n * M ^ 2 * (1 + 8 * r / (1 - r))) :=
      mul_le_mul_of_nonneg_left hm (sq_nonneg t)
    _ = _ := by ring

/-- An exponential coefficient bound with exponent `-2*c*h`, for `c > 0`,
specializes the interval quadratic log-Laplace bound with ratio `exp (-2*c)`.
No stationarity is required. -/
theorem geometric_interval_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (a : ℤ) (n : ℕ) (t : ℝ) (hsmall : |t| * n * M ≤ 1) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ Finset.Ico a (a + n), X i ω) ∂μ) ≤
      t ^ 2 * n * M ^ 2 *
        (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) := by
  apply interval_log_laplace_le μ X hX hcenter hM hbound (Real.exp_pos _).le
    (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)) _ a n t hsmall
  intro h hh
  simpa only [← Real.exp_nat_mul, mul_comm (h : ℝ)] using hmix h hh

end StrongMixing
