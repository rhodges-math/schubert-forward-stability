import SchubertForwardStability.SchubertPolynomials.Stability.LinearOperators
import SchubertForwardStability.SchubertPolynomials.Divided.Unreduced
import SchubertForwardStability.Permutations.Classes.WordExchange

/-! # Extracting Schubert coordinates of linear products

## Main results

An equal-length displayed word extracts the coordinate of its permutation product,
even if the displayed word is not reduced. A linear factor is extracted by its
deleted-letter expansion when the target length is one higher.
-/

namespace SchubertPolynomial

open FinitaryPerm
open scoped Classical

variable {R : Type*} [CommRing R]

/-- Every finite linear form is homogeneous of degree one, including the zero form. -/
theorem linearForm_isHomogeneous (a : ℕ+ →₀ R) : (linearForm R a).IsHomogeneous 1 := by
  rw [linearForm_apply]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun j _ =>
    MvPolynomial.isHomogeneous_C_mul_X (a j) j)

/-- A homogeneous polynomial has zero extraction at every different inversion length. -/
theorem schubertFunctional_off_degree (w : FinitaryPerm ℕ+) {p : MvPolynomial ℕ+ R}
    {n : ℕ} (hp : p.IsHomogeneous n) (hn : w.length ≠ n) :
    schubertFunctional R w p = 0 := by
  rw [schubertFunctional_apply]
  rcases lt_or_gt_of_ne hn with hl | hg
  · apply (permutationDivided_isHomogeneous w hp).coeff_eq_zero
    rw [map_zero]
    omega
  · rw [permutationDivided_zero_of_degree_lt w hp hg,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- Equal-length word extraction gives the product-indexed Schubert delta. -/
theorem wordDivided_schubert_coeff (word : List ℕ+) (u : FinitaryPerm ℕ+)
    (hlen : word.length = u.length) :
    (wordDividedDifference R word (schubert R u)).coeff 0 =
      if wordProduct word = u then 1 else 0 := by
  by_cases hr : IsReducedWord (wordProduct word) word
  · rw [← permutationDividedDifference_eq word hr, ← schubertFunctional_apply,
      schubertFunctional_schubert]
  · have hn : wordProduct word ≠ u := by
      intro he
      apply hr
      exact ⟨rfl, by simpa only [he] using hlen⟩
    rw [wordDividedDifference_zero word hr, LinearMap.zero_apply,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ite_eq_right hn]

/-- Extracting a deletion term multiplies its root coefficient by its Schubert delta. -/
theorem wordDeletionTerm_coeff (a : ℕ+ →₀ R) (c : List ℕ+ × ℕ+ × List ℕ+)
    (u : FinitaryPerm ℕ+) (hlen : (c.1 ++ c.2.2).length = u.length) :
    (wordDeletionTerm a c (schubert R u)).coeff 0 =
      (a (wordCutRoot c).1 - a (wordCutRoot c).2) *
        (if wordProduct (c.1 ++ c.2.2) = u then 1 else 0) := by
  change (MvPolynomial.lcoeff R 0) (wordDeletionTerm a c (schubert R u)) = _
  rw [wordDeletionTerm, map_smul]
  simp only [wordCoefficients_apply, wordCutRoot, MvPolynomial.lcoeff_apply,
    wordDivided_schubert_coeff _ _ hlen, smul_eq_mul]

/-- A linear Schubert product is extracted by the selected roots and deleted products. -/
theorem schubertFunctional_linearForm (a : ℕ+ →₀ R) (u w : FinitaryPerm ℕ+)
    (word : List ℕ+) (hr : IsReducedWord w word) (hlen : w.length = u.length + 1) :
    schubertFunctional R w (linearForm R a * schubert R u) =
      ((wordCuts word).map (fun c =>
        (a (wordCutRoot c).1 - a (wordCutRoot c).2) *
          (if wordProduct (c.1 ++ c.2.2) = u then 1 else 0))).sum := by
  rw [schubertFunctional_apply, permutationDividedDifference_eq word hr,
    wordDivided_linearForm]
  have hz : wordDividedDifference R word (schubert R u) = 0 := by
    rw [← permutationDividedDifference_eq word hr]
    exact permutationDivided_zero_of_degree_lt w (schubert_isHomogeneous u) (by omega)
  rw [hz, mul_zero, zero_add]
  change (MvPolynomial.lcoeff R 0) _ = _
  rw [map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  apply wordDeletionTerm_coeff
  have hd : (c.1 ++ c.2.2).length + 1 = word.length := wordCuts_deleted_length hc
  have hw := hr.2
  omega

/-- Across a right-transposition cover, a linear factor contributes its endpoint difference. -/
theorem schubertFunctional_linear_cover (a : ℕ+ →₀ R) (w : FinitaryPerm ℕ+)
    (q r : ℕ+) (hqr : q < r) (hl : (w * swap q r).length + 1 = w.length) :
    schubertFunctional R w (linearForm R a * schubert R (w * swap q r)) =
      a q - a r := by
  obtain ⟨word, hr, _⟩ := exists_reducedWordIn w w.isSupported_forwardStability
  have hr' : IsReducedWord (wordProduct word) word := by rw [hr.1]; exact hr
  have hp := exchange_cover_inversion hqr hl
  rw [← hr.1] at hp
  obtain ⟨c, ⟨hc, he⟩, hu⟩ := exists_unique_wordCutRoot hr' hp
  have hprod : wordProduct (c.1 ++ c.2.2) = w * swap q r := by
    simpa only [hr.1, he] using wordCuts_deleted_product hc
  let f := fun d : List ℕ+ × ℕ+ × List ℕ+ =>
    (a (wordCutRoot d).1 - a (wordCutRoot d).2) *
      (if wordProduct (d.1 ++ d.2.2) = w * swap q r then 1 else 0)
  have hf : ∀ d, d ≠ c → d ∈ wordCuts word → f d = 0 := by
    intro d hne hd
    have hn : wordProduct (d.1 ++ d.2.2) ≠ w * swap q r := by
      intro hprod'
      have hs : swap (wordCutRoot d).1 (wordCutRoot d).2 = swap q r := by
        apply mul_left_cancel (a := w)
        rw [← hr.1, ← wordCuts_deleted_product hd]
        simpa only [hr.1] using hprod'
      have hs' := swap_ordered_injective (wordCutRoot_lt hr' hd) hqr hs
      exact hne (hu d ⟨hd, Prod.ext hs'.1 hs'.2⟩)
    simp only [f, ite_eq_right hn, mul_zero]
  rw [schubertFunctional_linearForm a (w * swap q r) w word hr hl.symm]
  change ((wordCuts word).map f).sum = _
  have hc1 := @List.count_eq_one_of_mem _
    (@instBEqOfDecidableEq _ inferInstance) _ c (wordCuts word)
    (List.Nodup.of_map wordCutRoot (wordRoots_nodup hr')) hc
  rw [List.sum_map_eq_nsmul_single c f hf,
    hc1, one_nsmul]
  simp only [f, hprod, ite_true, he, mul_one]

/-- A linear Schubert product has no coordinate away from the next inversion length. -/
theorem schubertFunctional_linear_off_length (a : ℕ+ →₀ R) (u w : FinitaryPerm ℕ+)
    (hn : w.length ≠ u.length + 1) :
    schubertFunctional R w (linearForm R a * schubert R u) = 0 := by
  apply schubertFunctional_off_degree w
    ((linearForm_isHomogeneous a).mul (schubert_isHomogeneous u))
  simpa only [Nat.add_comm] using hn

/-- At the next length, only right-transposition covers can occur in a linear product. -/
theorem schubertFunctional_linear_outside (a : ℕ+ →₀ R) (u w : FinitaryPerm ℕ+)
    (hlen : w.length = u.length + 1)
    (hn : ∀ q r : ℕ+, q < r → u ≠ w * swap q r) :
    schubertFunctional R w (linearForm R a * schubert R u) = 0 := by
  obtain ⟨word, hr, _⟩ := exists_reducedWordIn w w.isSupported_forwardStability
  have hr' : IsReducedWord (wordProduct word) word := by rw [hr.1]; exact hr
  rw [schubertFunctional_linearForm a u w word hr hlen]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  have he : wordProduct (c.1 ++ c.2.2) ≠ u := by
    rw [wordCuts_deleted_product hc, hr.1]
    exact (hn _ _ (wordCutRoot_lt hr' hc)).symm
  simp only [ite_eq_right he, mul_zero]

end SchubertPolynomial
