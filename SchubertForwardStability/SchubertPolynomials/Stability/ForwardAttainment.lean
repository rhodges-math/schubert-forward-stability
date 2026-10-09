import SchubertForwardStability.SchubertPolynomials.Stability.SignedLongest
import SchubertForwardStability.SchubertPolynomials.Stability.InitialShift
import SchubertForwardStability.SchubertPolynomials.Backward.Witnesses

/-! # Attainment and reversal of forward support

The final position in a nonidentity forward support bound is moved.
Finite reversal exchanges movement of the first and final positions, and
a Schubert product has a coordinate attaining its finite forward bound.
-/

namespace FinitaryPerm

/-- Conjugation by a finite reversal preserves and reflects identity. -/
theorem conjugate_longest_eq_one (n : ℕ) (w : FinitaryPerm ℕ+) :
    longestElement n * w * longestElement n = 1 ↔ w = 1 := by
  constructor
  · intro h
    have he := congrArg (fun a => longestElement n * a * longestElement n) h
    simpa only [conjugate_longest_twice, mul_one, longestElement_mul_self] using he
  · rintro rfl
    simp only [mul_one, longestElement_mul_self]

/-- Signed translation preserves and reflects identity. -/
theorem SignedShift.eq_one_iff {k : ℤ} {u v : FinitaryPerm ℕ+}
    (h : SignedShift k u v) : u = 1 ↔ v = 1 := by
  constructor
  · intro he
    subst u
    exact h.eq_one
  · intro he
    subst v
    exact h.symm.eq_one

/-- Every moved position lies within the permutation's positive forward bound. -/
theorem moved_le_forwardStability {w : FinitaryPerm ℕ+} {i : ℕ+} (hi : w i ≠ i) :
    (i : ℕ) ≤ w.forwardStability := by
  by_contra hn
  exact hi (w.isSupported_forwardStability i (lt_of_not_ge hn))

/-- The final position of a forward bound greater than one is moved. -/
theorem forwardStability_last_moved (w : FinitaryPerm ℕ+) (hw : 1 < w.forwardStability) :
    w ⟨w.forwardStability, by omega⟩ ≠ ⟨w.forwardStability, by omega⟩ := by
  intro hfix
  have hs : IsSupported (w.forwardStability - 1) w := by
    intro j hj
    by_cases he : (j : ℕ) = w.forwardStability
    · have he' : j = ⟨w.forwardStability, by omega⟩ := PNat.eq he
      simpa only [he'] using hfix
    · exact w.isSupported_forwardStability j (by omega)
  have hb := (forwardStability_le_iff w (by omega : 1 ≤ w.forwardStability - 1)).mpr hs
  omega

/-- Reversal exchanges movement of the first and final positions in a positive interval. -/
theorem conjugate_longest_moves_first {n : ℕ} (hn : 1 ≤ n) (w : FinitaryPerm ℕ+) :
    (longestElement n * w * longestElement n) 1 ≠ 1 ↔
      w ⟨n, by omega⟩ ≠ ⟨n, by omega⟩ := by
  have hl : longestElement n 1 = ⟨n, by omega⟩ := by
    apply PNat.eq
    rw [longestElement_apply_val n 1 hn]
    change n + 1 - 1 = n
    omega
  have hr : longestElement n ⟨n, by omega⟩ = 1 := by
    rw [←hl, longestElement_apply_twice]
  change longestElement n (w (longestElement n 1)) ≠ 1 ↔
    w ⟨n, by omega⟩ ≠ ⟨n, by omega⟩
  rw [hl]
  exact not_congr ⟨fun h => (longestElement n).injective (h.trans hr.symm),
    fun h => by rw [h, hr]⟩

/-- Reversing an output moving the first position fills its ambient forward bound. -/
theorem forward_conjugate_moves_first {n : ℕ} {w : FinitaryPerm ℕ+}
    (hn : 1 ≤ n) (hw : IsSupported n w) (h1 : w 1 ≠ 1) :
    (longestElement n * w * longestElement n).forwardStability = n := by
  apply le_antisymm ((forwardStability_le_iff _ hn).mpr hw.conjugate_longest)
  have hl : (longestElement n * w * longestElement n) ⟨n, by omega⟩ ≠ ⟨n, by omega⟩ := by
    apply (conjugate_longest_moves_first hn (longestElement n * w * longestElement n)).mp
    simpa only [conjugate_longest_twice] using h1
  exact moved_le_forwardStability hl

end FinitaryPerm

namespace SchubertPolynomial

open FinitaryPerm
open scoped Classical

/-- A nonzero integer product coordinate attains the product's finite forward bound. -/
theorem exists_forward_attaining (u v : FinitaryPerm ℕ+) :
    ∃ w, structureConst u v w ≠ 0 ∧ w.forwardStability = productForwardStability u v := by
  obtain ⟨w, hw, he⟩ := Finset.exists_mem_eq_sup (structureCoefficients ℤ u v).support
    (structureCoefficients_support_nonempty u v) FinitaryPerm.forwardStability
  refine ⟨w, Finsupp.mem_support_iff.mp hw, ?_⟩
  rw [productForwardStability_eq_sup, he]

/-- Extending the common reversal interval increases nonidentity product support by its length. -/
theorem productForward_conjugate_extend {n : ℕ} {u v : FinitaryPerm ℕ+}
    (hu : IsSupported n u) (hv : IsSupported n v) (h : u ≠ 1 ∨ v ≠ 1) (d : ℕ) :
    productForwardStability (longestElement (n + d) * u * longestElement (n + d))
      (longestElement (n + d) * v * longestElement (n + d)) =
        productForwardStability (longestElement n * u * longestElement n)
          (longestElement n * v * longestElement n) + d := by
  have hn : longestElement n * u * longestElement n ≠ 1 ∨
      longestElement n * v * longestElement n ≠ 1 := by
    exact h.elim (fun he => Or.inl (fun hh => he ((conjugate_longest_eq_one n u).mp hh)))
      (fun he => Or.inr (fun hh => he ((conjugate_longest_eq_one n v).mp hh)))
  rw [conjugate_longest_extend hu, conjugate_longest_extend hv]
  exact productForward_initialShift d _ _ hn

end SchubertPolynomial
