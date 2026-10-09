import SchubertForwardStability.StrongMixing.Inequalities.AlternatingLaplace
import SchubertForwardStability.StrongMixing.Inequalities.TerminalChoice

/-!
# Size-controlled terminal subset log-Laplace estimate

Explicit rounded alternating blocks extend the small-interval quadratic estimate
to arbitrary subsets of an interval whose length is of order `1/(t*M)^2`.
The remaining decoupling error is exponentially small in `1/(t*M)`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Rounded alternating blocks that fit in the interval give the quadratic
terminal bound and its exponentially small decoupling error. -/
private theorem terminal_fitting_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (a : ℤ) (B len : ℕ) (hA : A ⊆ Finset.Ico a (a + B))
    (ht : 0 < t) (hlen : 1 ≤ len) (hfit : len ≤ B)
    (hlow : 1 / (8 * (t * M)) ≤ (len : ℝ)) (hlenSmall : 2 * (t * M) * len ≤ 1)
    (hsize : (t * M) ^ 2 * B ≤ c / 24) :
    Real.log (∫ ω, Real.exp (t * ∑ j ∈ A, X j ω) ∂μ) ≤
      6 * B * (t * M) ^ 2 *
          (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
        16 * B * (t * M) * Real.exp (-c / (8 * (t * M))) := by
  let u := t * M
  let K := 1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))
  let p : ℕ := B / (2 * len) + 1
  have hu : 0 < u := mul_pos ht hM
  have h8 : 0 < 8 * u := by positivity
  have hr1 : Real.exp (-2 * c) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlenR : (len : ℝ) ≤ B := by exact_mod_cast hfit
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hdiv : ((B / (2 * len) : ℕ) : ℝ) * (2 * (len : ℝ)) ≤ B := by
    exact_mod_cast Nat.div_mul_le_self B (2 * len)
  have hp : (p : ℝ) = (B / (2 * len) : ℕ) + 1 := by dsimp [p]; push_cast; rfl
  have hpl : (p : ℝ) * len ≤ (3 / 2 : ℝ) * B := by nlinarith
  have hcover : B ≤ 2 * p * len := by
    have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * len)).mp
      (show B / (2 * len) < p from by dsimp [p]; omega)
    have hid : p * (2 * len) = 2 * p * len := by ring
    rw [hid] at h
    omega
  have hAcover : A ⊆ Finset.Ico a (a + (2 * p * len : ℕ)) := by
    intro j hj
    have hj := Finset.mem_Ico.mp (hA hj)
    have hcoverR : (B : ℤ) ≤ (2 * p * len : ℕ) := by exact_mod_cast hcover
    exact Finset.mem_Ico.mpr ⟨hj.1, hj.2.trans_le (add_le_add le_rfl hcoverR)⟩
  have hs : 2 * |t| * len * M ≤ 1 := by
    rw [abs_of_pos ht]
    have hid : 2 * t * (len : ℝ) * M = 2 * u * len := by dsimp [u]; ring
    rw [hid]
    exact hlenSmall
  have hb := alternating_laplace_le μ X hX hcenter hM.le hc hbound hmix
    A a len p hlen hAcover t hs
  change _ ≤ 4 * p * t ^ 2 * len * M ^ 2 * K +
    ((p - 1 : ℕ) : ℝ) * Real.exp (-2 * c * len + 2 * |t| * p * len * M) at hb
  have hquad : 4 * p * t ^ 2 * len * M ^ 2 * K = 4 * p * len * u ^ 2 * K := by
    dsimp [u]
    ring
  have hexp : -2 * c * len + 2 * |t| * p * len * M = -2 * c * len + 2 * u * p * len := by
    rw [abs_of_pos ht]
    dsimp [u]
    ring
  rw [hquad, hexp] at hb
  have hquadB : 4 * p * len * u ^ 2 * K ≤ 6 * B * u ^ 2 * K := by
    have h := mul_le_mul_of_nonneg_right hpl
      (mul_nonneg (by positivity : 0 ≤ 4 * u ^ 2) hK)
    nlinarith only [h]
  have hfrac : 3 * u * B ≤ c / (8 * u) := by
    apply (le_div_iff₀ h8).mpr
    change u ^ 2 * B ≤ c / 24 at hsize
    nlinarith only [hsize]
  have hcLow : c / (8 * u) ≤ c * len := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hlow hc.le
  have hgap : 3 * u * B ≤ c * len := hfrac.trans hcLow
  have heUpper : Real.exp (-2 * c * len + 2 * u * p * len) ≤
      Real.exp (-c / (8 * u)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    have h := mul_le_mul_of_nonneg_left hpl (by positivity : 0 ≤ 2 * u)
    nlinarith only [h, hgap, hcLow]
  have hunit := (div_le_iff₀ h8).mp hlow
  have hcoef : ((p - 1 : ℕ) : ℝ) ≤ 16 * B * u := by
    have hpLower := mul_le_mul_of_nonneg_left hunit hp0
    have hpUpper := mul_le_mul_of_nonneg_left hpl (by positivity : 0 ≤ 8 * u)
    have hpSub : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
    have hBu : 0 ≤ (B : ℝ) * u := mul_nonneg (Nat.cast_nonneg B) hu.le
    nlinarith only [hpLower, hpUpper, hpSub, hBu]
  have heB : ((p - 1 : ℕ) : ℝ) * Real.exp (-2 * c * len + 2 * u * p * len) ≤
      16 * B * u * Real.exp (-c / (8 * u)) :=
    (mul_le_mul_of_nonneg_left heUpper (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))
  exact hb.trans (add_le_add hquadB heB)

/-- For a centered sequence uniformly bounded by positive `M` with
exponential mixing, an arbitrary subset of an interval of length `B` has
log-Laplace transform at most `6*B*(t*M)^2*K_c` plus
`16*B*t*M*exp(-c/(8*t*M))`. Here `0 < t*M <= 1/8`, `(t*M)^2*B <= c/24`, and
`K_c = 1 + 8*exp(-2*c)/(1-exp(-2*c))`. No stationarity is imposed. -/
theorem terminal_subset_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (a : ℤ) (B : ℕ) (hA : A ⊆ Finset.Ico a (a + B))
    (ht : 0 < t) (hsmall : t * M ≤ 1 / 8) (hsize : (t * M) ^ 2 * B ≤ c / 24) :
    Real.log (∫ ω, Real.exp (t * ∑ j ∈ A, X j ω) ∂μ) ≤
      6 * B * (t * M) ^ 2 *
          (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
        16 * B * t * M * Real.exp (-c / (8 * t * M)) := by
  let u := t * M
  let len := terminalBlockLength u
  let K := 1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))
  have hu : 0 < u := mul_pos ht hM
  obtain ⟨hlen, hlow, hlenSmall⟩ := terminalBlockLength_bounds hu hsmall
  change 1 ≤ len at hlen
  change 1 / (8 * u) ≤ (len : ℝ) at hlow
  change 2 * u * len ≤ 1 at hlenSmall
  have hr1 : Real.exp (-2 * c) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmixR : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c) ^ h := by
    intro h hh
    simpa only [← Real.exp_nat_mul, mul_comm (h : ℝ)] using hmix h hh
  have hgoal : 16 * B * t * M * Real.exp (-c / (8 * t * M)) =
      16 * B * u * Real.exp (-c / (8 * u)) := by
    dsimp [u]
    congr 1
    · ring
    · congr 1
      congr 1
      ring
  rw [hgoal]
  change _ ≤ 6 * B * u ^ 2 * K + 16 * B * u * Real.exp (-c / (8 * u))
  by_cases hfit : len ≤ B
  · exact terminal_fitting_laplace_le μ X hX hcenter hM hc hbound hmix
      A a B len hA ht hlen hfit hlow hlenSmall hsize
  · have hlenR : (B : ℝ) ≤ len := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hfit))
    have hs : |t| * B * M ≤ 1 := by
      rw [abs_of_pos ht]
      have h := mul_le_mul_of_nonneg_left hlenR hu.le
      dsimp [u] at h hlenSmall
      nlinarith only [h, hlenSmall]
    have hb := subset_interval_laplace_le μ X hX hcenter hM.le hbound
      (Real.exp_pos _).le hr1 hmixR A a B hA t hs
    have hquad : t ^ 2 * B * M ^ 2 * K = (B : ℝ) * u ^ 2 * K := by dsimp [u]; ring
    change _ ≤ t ^ 2 * B * M ^ 2 * K at hb
    rw [hquad] at hb
    have hQ : 0 ≤ (B : ℝ) * u ^ 2 * K := by positivity
    have hE : 0 ≤ 16 * B * u * Real.exp (-c / (8 * u)) := by positivity
    linarith only [hb, hQ, hE]

end StrongMixing
