import SchubertForwardStability.SchubertPolynomials.Backward.Stabilization

/-! # Backward stability and reversed forward stability

For `u, v ∈ S_n` with `n ≥ 1`, write `ρ(w) = w₀ w w₀` for conjugation by the longest element of
`S_n`. Backward stability of `𝔖_u 𝔖_v` is determined by forward stability of `𝔖_{ρ(u)} 𝔖_{ρ(v)}`:
`BS(u,v) + n = max(n, FS(ρ(u), ρ(v)))`.

## Main results

* `productBackStability_add_eq_max`: `BS(u,v) + n = max(n, FS(ρ(u), ρ(v)))`.
* `productBackStability_eq_sub`: the same identity with truncated natural subtraction,
  `BS(u,v) = FS(ρ(u), ρ(v)) - n`, that is `max(0, FS(ρ(u), ρ(v)) - n)`.

## Implementation notes

The boundary hits after `k ≥ 0` shifts are the signed back-stability witnesses at shift `k`, whose
greatest element is `FS(ρ(u), ρ(v)) - n` for every pair other than the identity pair. The identity
pair has backward stability `0` and forward stability `1`, so the hypothesis `n ≥ 1` is needed.

## References

* A. Hardt and D. Wallach, *When do Schubert polynomial products stabilize?*,
  arXiv:2412.06976, Theorems 1.3 and 1.6.
-/

namespace SchubertPolynomial

open FinitaryPerm
open scoped Classical

/-- Backward stability plus the ambient size is the larger of the ambient size and the reversed
forward stability. -/
theorem productBackStability_add_eq_max {n : ℕ} (hn : 1 ≤ n) {u v : FinitaryPerm ℕ+}
    (hu : IsSupported n u) (hv : IsSupported n v) :
    productBackStability u v + n =
      max n (productForwardStability (longestElement n * u * longestElement n)
        (longestElement n * v * longestElement n)) := by
  by_cases hid : u = 1 ∧ v = 1
  · obtain ⟨rfl, rfl⟩ := hid
    simp only [productBackStability_one, mul_one, longestElement_mul_self,
      productForwardStability_one, zero_add]
    omega
  · have h : u ≠ 1 ∨ v ≠ 1 := not_and_or.mp hid
    have hg := isGreatest_backShiftWitness hu hv h
    set F := productForwardStability (longestElement n * u * longestElement n)
      (longestElement n * v * longestElement n)
    have hwit (k : ℕ) : BoundaryHit u v k ↔ BackShiftWitness u v k :=
      boundaryHit_iff_backShiftWitness u v k
    rw [productBackStability_eq_sSup]
    by_cases hF : n ≤ F
    · have hmem : F - n ∈ {k | BoundaryHit u v k} := by
        rw [Set.mem_ofPred_eq, hwit]
        have h1 := hg.1
        have hc : ((F - n : ℕ) : ℤ) = (F : ℤ) - n := by omega
        rw [Set.mem_ofPred_eq] at h1
        rwa [hc]
      have hle : ∀ k ∈ {k | BoundaryHit u v k}, k ≤ F - n := by
        intro k hk
        have := hg.2 ((hwit k).mp hk)
        omega
      rw [(IsGreatest.csSup_eq ⟨hmem, hle⟩)]
      omega
    · have he : {k | BoundaryHit u v k} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro k hk
        have := hg.2 ((hwit k).mp hk)
        omega
      rw [he, csSup_empty]
      change 0 + n = max n F
      omega

/-- Backward stability is reversed forward stability minus the ambient size, with truncated
natural subtraction: `BS(u,v) = max(0, FS(ρ(u), ρ(v)) - n)`. -/
theorem productBackStability_eq_sub {n : ℕ} (hn : 1 ≤ n) {u v : FinitaryPerm ℕ+}
    (hu : IsSupported n u) (hv : IsSupported n v) :
    productBackStability u v =
      productForwardStability (longestElement n * u * longestElement n)
        (longestElement n * v * longestElement n) - n := by
  have h := productBackStability_add_eq_max hn hu hv
  omega

end SchubertPolynomial
