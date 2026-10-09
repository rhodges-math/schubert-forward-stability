import SchubertForwardStability.Paper.Uniform.ProductGaussian
import SchubertForwardStability.Permutations.Statistics.RecordBound

/-! # The gap between ambient and intrinsic walk maxima

The maximum of the record walk over `[1, n+1]` exceeds its intrinsic maximum only at a
position that is the last record of both permutations. For independent uniform `u, v` in
`S_n`, the mean gap lies in `[0, 1/n]` and tends to zero.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

private theorem walk_above_support (u v : FinitaryPerm ℕ+) (i : ℕ+)
    (hu : u.forwardStability < (i : ℕ)) (hv : v.forwardStability < (i : ℕ)) :
    recordWalk u v i = (i : ℕ) - 1 := by
  rw [recordWalk, u.isSupported_forwardStability.nonRecordsFrom_eq_zero i hu,
    v.isSupported_forwardStability.nonRecordsFrom_eq_zero i hv]
  simp only [Nat.cast_zero, zero_add]

/-- Enlarging a supported walk's interval only adds its linear terminal tail. -/
theorem recordWalkMaxAt_eq_max {n : ℕ} (hn : 1 ≤ n) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported n u) (hv : IsSupported n v) :
    recordWalkMaxAt n u v = max (recordWalkMax u v) (n : ℤ) := by
  have huf := (u.forwardStability_le_iff hn).mpr hu
  have hvf := (v.forwardStability_le_iff hn).mpr hv
  have hterm : recordWalk u v n.succPNat = n := by
    rw [walk_above_support u v n.succPNat (by change u.forwardStability < n + 1; omega)
      (by change v.forwardStability < n + 1; omega)]
    change ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ)
    push_cast
    ring
  apply le_antisymm ?_ (max_le (recordWalkMax_le_maxAt u v huf hvf) ?_)
  · obtain ⟨i, hi, he⟩ := exists_recordWalk_eq_maxAt n u v
    rw [←he]
    by_cases hib : (i : ℕ) ≤ max u.forwardStability v.forwardStability + 1
    · exact (recordWalk_le_max u v hib).trans (le_max_left _ _)
    · rw [walk_above_support u v i (by omega) (by omega)]
      have hic : ((i : ℕ) : ℤ) ≤ (n : ℤ) + 1 := by exact_mod_cast hi
      exact (by omega : ((i : ℕ) : ℤ) - 1 ≤ (n : ℤ)).trans (le_max_right _ _)
  · rw [←hterm]
    exact recordWalk_le_maxAt u v (by change n + 1 ≤ n + 1; rfl)

/-- An ambient maximum can exceed the intrinsic maximum only at a simultaneous last record. -/
theorem maximum_gap_le_last_upward {n : ℕ} (hn : 1 ≤ n) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported n u) (hv : IsSupported n v) :
    recordWalkMaxAt n u v - recordWalkMax u v ≤
      (n : ℤ) * upwardIndicator u v (n.toPNat hn) := by
  have huf := (u.forwardStability_le_iff hn).mpr hu
  have hvf := (v.forwardStability_le_iff hn).mpr hv
  by_cases hN : max u.forwardStability v.forwardStability = n
  · have he : recordWalkMaxAt n u v = recordWalkMax u v := by
      rw [←hN]
      rfl
    rw [he]
    simp only [sub_self]
    exact mul_nonneg (Int.natCast_nonneg _) (upwardIndicator_nonneg _ _ _)
  · have hlt : max u.forwardStability v.forwardStability < n := by omega
    have hur : IsRecord u (n.toPNat hn) := u.isRecord_above (by change _ < n; omega)
    have hvr : IsRecord v (n.toPNat hn) := v.isRecord_above (by change _ < n; omega)
    rw [upwardIndicator_eq_records, ite_eq_left ⟨hur, hvr⟩, mul_one,
      recordWalkMaxAt_eq_max hn u v hu hv]
    have hm := one_le_recordWalkMax u v
    exact sub_le_iff_le_add.mpr (max_le (by omega) (by omega))

/-- The mean ambient-to-intrinsic gap is between zero and the reciprocal ambient size. -/
theorem integral_uniform_maximum_gap {n : ℕ} (hn : 1 ≤ n) :
    (∫ p, ((recordWalkMaxAt n p.1 p.2 - recordWalkMax p.1 p.2 : ℤ) : ℝ)
      ∂pairLaw (symmetricGroup n)) ∈ Set.Icc (0 : ℝ) (1 / n) := by
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_mem_uniformOn_finset
      ((symmetricGroup n).product (symmetricGroup n))
      ⟨(1, 1), Finset.mem_product.mpr ⟨one_mem_symmetricGroup n,
        one_mem_symmetricGroup n⟩⟩] with p hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
    have huf := (p.1.forwardStability_le_iff hn).mpr ((mem_symmetricGroup _ _).mp hu)
    have hvf := (p.2.forwardStability_le_iff hn).mpr ((mem_symmetricGroup _ _).mp hv)
    change (0 : ℝ) ≤ ((recordWalkMaxAt n p.1 p.2 - recordWalkMax p.1 p.2 : ℤ) : ℝ)
    exact_mod_cast sub_nonneg.mpr (recordWalkMax_le_maxAt p.1 p.2 huf hvf)
  · calc
      _ ≤ ∫ p, (n : ℝ) * (upwardIndicator p.1 p.2 (n.toPNat hn) : ℝ)
          ∂pairLaw (symmetricGroup n) := by
        apply integral_uniform_finset_mono
        intro p hp
        obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
        exact_mod_cast maximum_gap_le_last_upward hn p.1 p.2
          ((mem_symmetricGroup _ _).mp hu) ((mem_symmetricGroup _ _).mp hv)
      _ = 1 / n := by
        rw [integral_const_mul, integral_uniform_upward n (n.toPNat hn) (by rfl)]
        have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        change (n : ℝ) * (1 / (n : ℝ) ^ 2) = 1 / (n : ℝ)
        field_simp

/-- The finite uniform mean difference between ambient and intrinsic maxima vanishes. -/
theorem tendsto_integral_uniform_maximum_gap :
    Tendsto (fun n : ℕ =>
      ∫ p, ((recordWalkMaxAt n p.1 p.2 - recordWalkMax p.1 p.2 : ℤ) : ℝ)
        ∂pairLaw (symmetricGroup n)) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ tendsto_one_div_atTop_nhds_zero_nat
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (integral_uniform_maximum_gap hn).1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (integral_uniform_maximum_gap hn).2

/-- Positive ambient walk maxima bound product stability and agree at full individual size. -/
theorem product_ambient_walk_bound (n : ℕ) (hn : 1 ≤ n) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported n u) (hv : IsSupported n v) :
    (SchubertPolynomial.productForwardStability u v : ℤ) ≤ recordWalkMaxAt n u v ∧
      (max u.forwardStability v.forwardStability = n →
        (SchubertPolynomial.productForwardStability u v : ℤ) = recordWalkMaxAt n u v) := by
  have he : (SchubertPolynomial.productForwardStability u v : ℤ) = recordWalkMax u v := by
    rw [SchubertPolynomial.productForwardStability_eq_recordBound]
    rfl
  rw [he]
  refine ⟨recordWalkMax_le_maxAt u v ((u.forwardStability_le_iff hn).mpr hu)
    ((v.forwardStability_le_iff hn).mpr hv), ?_⟩
  intro hfull
  rw [recordWalkMax_eq_maxAt, hfull]

end RecordStability
