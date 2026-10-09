import SchubertForwardStability.SchubertPolynomials.Backward.GreatestWitness
import SchubertForwardStability.SchubertPolynomials.Stability.RightShiftIterate

/-! # Backward stability of Schubert products

Shifting both factors of a Schubert product to the right adds an initial fixed position. The
backward stability of `𝔖_u 𝔖_v` is the number of such shifts after which the support of the
product no longer changes, up to the same shift of its outputs.

## Main definitions

* `shiftedProductSupport u v k`: the permutations `w` with `c^w_{1^k × u, 1^k × v} ≠ 0`.
* `BoundaryHit u v k`: some output of the `k`-fold shifted product moves the first position.
* `IsSupportStableFrom u v k`: for every `r`, the support after `k + r` shifts is the `r`-fold
  shift of the support after `k` shifts.
* `productBackStability u v`: the least `k` from which the support is stable
  (Hardt–Wallach, Definition 1.1).

## Main results

* `isSupportStableFrom_iff`: the support is stable from `k` exactly when no boundary hit occurs
  after `k` shifts.
* `productBackStability_eq_sSup`: backward stability is the last boundary hit, and `0` when
  there is none.
* `isSupportStableFrom_iff_expansion`: stability from `k` means that for every `r`,
  `𝔖_{1^{k+r} × u} 𝔖_{1^{k+r} × v} = ∑_w c^w_{1^k × u, 1^k × v} 𝔖_{1^r × w}`.
* `productBackStability_isLeast` and `productBackStability_one`.

## Implementation notes

Hardt–Wallach compare the shifted supports after translating them back to permutations of the
integers. Since the right shift is injective, comparing the support after `k + r` shifts with
the `r`-fold shift of the support after `k` shifts is the same condition, and it stays inside
the finitary permutations of the positive integers. The value does not depend on any ambient
symmetric group.

## References

* A. Hardt and D. Wallach, *When do Schubert polynomial products stabilize?*,
  arXiv:2412.06976, Definition 1.1.
-/

namespace SchubertPolynomial

open FinitaryPerm
open scoped Classical

/-- The permutations `w` with nonzero coefficient in `𝔖_{1^k × u} 𝔖_{1^k × v}`. -/
def shiftedProductSupport (u v : FinitaryPerm ℕ+) (k : ℕ) : Set (FinitaryPerm ℕ+) :=
  {w | structureConst (shiftRight^[k] u) (shiftRight^[k] v) w ≠ 0}

/-- After `k` right shifts of both factors, some output of the product moves the first
position. -/
def BoundaryHit (u v : FinitaryPerm ℕ+) (k : ℕ) : Prop :=
  ∃ w ∈ shiftedProductSupport u v k, w 1 ≠ 1

/-- The product support is stable from `k` shifts on: every further `r` shifts of the factors
shift the support by `r`. -/
def IsSupportStableFrom (u v : FinitaryPerm ℕ+) (k : ℕ) : Prop :=
  ∀ r : ℕ, shiftedProductSupport u v (k + r) = shiftRight^[r] '' shiftedProductSupport u v k

/-- Backward stability: the least number of right shifts from which the support of the
product is stable (Hardt–Wallach, Definition 1.1). -/
noncomputable def productBackStability (u v : FinitaryPerm ℕ+) : ℕ :=
  sInf {k | IsSupportStableFrom u v k}

/-- Shifting an output of the `k`-fold shifted product gives an output after `k + 1` shifts. -/
theorem shiftRight_mem_shiftedProductSupport {u v w : FinitaryPerm ℕ+} {k : ℕ}
    (hw : w ∈ shiftedProductSupport u v k) :
    shiftRight w ∈ shiftedProductSupport u v (k + 1) := by
  change structureConst (shiftRight^[k + 1] u) (shiftRight^[k + 1] v) (shiftRight w) ≠ 0
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', structureConst_shiftRight]
  exact hw

/-- An output after `k + 1` shifts that fixes the first position is the shift of an output
after `k` shifts. -/
theorem mem_image_shiftRight_of_apply_one {u v w : FinitaryPerm ℕ+} {k : ℕ}
    (hw : w ∈ shiftedProductSupport u v (k + 1)) (h1 : w 1 = 1) :
    w ∈ shiftRight '' shiftedProductSupport u v k := by
  obtain ⟨w₀, rfl⟩ := exists_shiftRight_eq h1
  refine ⟨w₀, ?_, rfl⟩
  change structureConst (shiftRight^[k + 1] u) (shiftRight^[k + 1] v) (shiftRight w₀) ≠ 0 at hw
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', structureConst_shiftRight] at hw
  exact hw

/-- One more shift leaves the support unchanged up to shifting exactly when it creates no
boundary hit. -/
theorem shiftedProductSupport_succ_eq_iff (u v : FinitaryPerm ℕ+) (k : ℕ) :
    shiftedProductSupport u v (k + 1) = shiftRight '' shiftedProductSupport u v k ↔
      ¬BoundaryHit u v (k + 1) := by
  constructor
  · rintro he ⟨w, hw, h1⟩
    rw [he] at hw
    obtain ⟨w₀, -, rfl⟩ := hw
    exact h1 (shiftRight_apply_one w₀)
  · intro hn
    apply Set.Subset.antisymm
    · intro w hw
      by_cases h1 : w 1 = 1
      · exact mem_image_shiftRight_of_apply_one hw h1
      · exact absurd ⟨w, hw, h1⟩ hn
    · rintro _ ⟨w, hw, rfl⟩
      exact shiftRight_mem_shiftedProductSupport hw

/-- The support is stable from `k` exactly when no boundary hit occurs after more than `k`
shifts. -/
theorem isSupportStableFrom_iff (u v : FinitaryPerm ℕ+) (k : ℕ) :
    IsSupportStableFrom u v k ↔ ∀ j, k < j → ¬BoundaryHit u v j := by
  constructor
  · rintro hs j hj ⟨w, hw, h1⟩
    obtain ⟨r, rfl⟩ : ∃ r, j = k + r := ⟨j - k, by omega⟩
    rw [hs r] at hw
    obtain ⟨w₀, -, rfl⟩ := hw
    exact h1 (iterate_shiftRight_apply_le w₀ r 1 (by simp; omega))
  · intro hn r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [← add_assoc, (shiftedProductSupport_succ_eq_iff u v (k + r)).mpr
        (hn (k + r + 1) (by omega)), ih, Set.image_image, Function.iterate_succ']
      rfl

/-- A boundary hit after `k` shifts is a signed back-stability witness at shift `k`. -/
theorem boundaryHit_iff_backShiftWitness (u v : FinitaryPerm ℕ+) (k : ℕ) :
    BoundaryHit u v k ↔ BackShiftWitness u v k := by
  constructor
  · rintro ⟨w, hw, h1⟩
    exact ⟨_, _, w, signedShift_iterate_shiftRight u k, signedShift_iterate_shiftRight v k, hw, h1⟩
  · rintro ⟨u', v', w, hu, hv, hc, h1⟩
    rw [signedShift_natCast_iff] at hu hv
    subst u' v'
    exact ⟨w, hc, h1⟩

/-- The identity pair has no boundary hit. -/
theorem not_boundaryHit_one (k : ℕ) : ¬BoundaryHit 1 1 k := fun h =>
  not_backShiftWitness_one k ((boundaryHit_iff_backShiftWitness 1 1 k).mp h)

/-- Boundary hits occur after only finitely many shifts. -/
theorem bddAbove_boundaryHit (u v : FinitaryPerm ℕ+) : BddAbove {k | BoundaryHit u v k} := by
  by_cases h : u ≠ 1 ∨ v ≠ 1
  · let N := max u.forwardStability v.forwardStability
    have hu : IsSupported N u := u.isSupported_forwardStability.mono (le_max_left _ _)
    have hv : IsSupported N v := v.isSupported_forwardStability.mono (le_max_right _ _)
    refine ⟨(productForwardStability (longestElement N * u * longestElement N)
      (longestElement N * v * longestElement N) : ℤ).toNat, fun k hk => ?_⟩
    have hle := (isGreatest_backShiftWitness hu hv h).2
      ((boundaryHit_iff_backShiftWitness u v k).mp hk)
    omega
  · obtain ⟨rfl, rfl⟩ : u = 1 ∧ v = 1 :=
      ⟨not_not.mp (not_or.mp h).1, not_not.mp (not_or.mp h).2⟩
    exact ⟨0, fun k hk => absurd hk (not_boundaryHit_one k)⟩

/-- Li's identity for `r`-fold shifts: `c^{1^r × w}_{1^r × u, 1^r × v} = c^w_{u,v}`. -/
theorem structureConst_iterate_shiftRight (r : ℕ) (u v w : FinitaryPerm ℕ+) :
    structureConst (shiftRight^[r] u) (shiftRight^[r] v) (shiftRight^[r] w) =
      structureConst u v w := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', structureConst_shiftRight, ih]

/-- The coordinates after `k + r` shifts are those after `k` shifts, moved by the `r`-fold
shift, exactly when the support is stable from `k` to `k + r`. -/
theorem structureCoefficients_eq_mapDomain_iff (u v : FinitaryPerm ℕ+) (k r : ℕ) :
    structureCoefficients ℤ (shiftRight^[k + r] u) (shiftRight^[k + r] v) =
        (structureCoefficients ℤ (shiftRight^[k] u) (shiftRight^[k] v)).mapDomain
          (shiftRight^[r]) ↔
      shiftedProductSupport u v (k + r) = shiftRight^[r] '' shiftedProductSupport u v k := by
  have hinj : Function.Injective (shiftRight^[r]) := shiftRight_injective.iterate r
  have hsupp (j : ℕ) : shiftedProductSupport u v j =
      ((structureCoefficients ℤ (shiftRight^[j] u) (shiftRight^[j] v)).support :
        Set (FinitaryPerm ℕ+)) := by
    ext w
    simp [shiftedProductSupport, structureConst]
  have hshift (a : FinitaryPerm ℕ+) : shiftRight^[k + r] a = shiftRight^[r] (shiftRight^[k] a) := by
    rw [add_comm, Function.iterate_add_apply]
  constructor
  · intro h
    rw [hsupp, hsupp, h, Finsupp.mapDomain_support_of_injective hinj, Finset.coe_image]
  · intro h
    ext w'
    by_cases hw : w' ∈ Set.range (shiftRight^[r])
    · obtain ⟨w, rfl⟩ := hw
      rw [Finsupp.mapDomain_apply_of_injective hinj, hshift, hshift]
      exact structureConst_iterate_shiftRight r _ _ w
    · rw [Finsupp.mapDomain_of_notMem_range _ _ hw]
      have hn : w' ∉ shiftedProductSupport u v (k + r) := by
        rw [h]
        exact fun ⟨w, _, hw'⟩ => hw ⟨w, hw'⟩
      simpa [shiftedProductSupport, structureConst] using hn

/-- The support is stable from `k` exactly when, for every `r`, the shifted product expands as
`𝔖_{1^{k+r} × u} 𝔖_{1^{k+r} × v} = ∑_w c^w_{1^k × u, 1^k × v} 𝔖_{1^r × w}`: further shifts
introduce no new terms. -/
theorem isSupportStableFrom_iff_expansion (u v : FinitaryPerm ℕ+) (k : ℕ) :
    IsSupportStableFrom u v k ↔ ∀ r : ℕ,
      schubert ℤ (shiftRight^[k + r] u) * schubert ℤ (shiftRight^[k + r] v) =
        ∑ w ∈ (structureCoefficients ℤ (shiftRight^[k] u) (shiftRight^[k] v)).support,
          structureConst (shiftRight^[k] u) (shiftRight^[k] v) w •
            schubert ℤ (shiftRight^[r] w) := by
  refine forall_congr' fun r => ?_
  rw [← structureCoefficients_eq_mapDomain_iff]
  set a := structureCoefficients ℤ (shiftRight^[k] u) (shiftRight^[k] v)
  have hsum : (a.mapDomain (shiftRight^[r])).sum (fun w c => c • schubert ℤ w) =
      ∑ w ∈ a.support, structureConst (shiftRight^[k] u) (shiftRight^[k] v) w •
        schubert ℤ (shiftRight^[r] w) := by
    rw [Finsupp.sum_mapDomain_index (h := fun w (c : ℤ) => c • schubert ℤ w)
      (fun _ => zero_smul ℤ _) (fun _ _ _ => add_smul _ _ _)]
    rfl
  constructor
  · intro h
    rw [← hsum, ← h, ← schubert_mul_expansion]
    rfl
  · intro h
    exact structureCoefficients_unique _ _ _ (hsum.trans h.symm)

/-- Backward stability is the least `k ≥ 0` such that for every `r ≥ 0`,
`𝔖_{1^{k+r} × u} 𝔖_{1^{k+r} × v} = ∑_w c^w_{1^k × u, 1^k × v} 𝔖_{1^r × w}`
(Hardt–Wallach, Definition 1.1). -/
theorem productBackStability_eq_sInf_expansion (u v : FinitaryPerm ℕ+) :
    productBackStability u v = sInf {k | ∀ r : ℕ,
      schubert ℤ (shiftRight^[k + r] u) * schubert ℤ (shiftRight^[k + r] v) =
        ∑ w ∈ (structureCoefficients ℤ (shiftRight^[k] u) (shiftRight^[k] v)).support,
          structureConst (shiftRight^[k] u) (shiftRight^[k] v) w •
            schubert ℤ (shiftRight^[r] w)} := by
  rw [productBackStability]
  congr 1
  ext k
  exact isSupportStableFrom_iff_expansion u v k

/-- Backward stability is the least shift from which the support is stable. -/
theorem productBackStability_isLeast (u v : FinitaryPerm ℕ+) :
    IsLeast {k | IsSupportStableFrom u v k} (productBackStability u v) := by
  have hb := bddAbove_boundaryHit u v
  set M := sSup {k | BoundaryHit u v k}
  have hM : IsLeast {k | IsSupportStableFrom u v k} M := by
    constructor
    · rw [Set.mem_ofPred_eq, isSupportStableFrom_iff]
      intro j hj hh
      exact absurd (le_csSup hb hh) (by omega)
    · intro k hk
      rw [Set.mem_ofPred_eq, isSupportStableFrom_iff] at hk
      rcases Set.eq_empty_or_nonempty {k | BoundaryHit u v k} with he | hne
      · simp only [M, he, csSup_empty, bot_eq_zero', zero_le]
      · by_contra hlt
        exact hk M (by omega) (Nat.sSup_mem hne hb)
  rw [productBackStability, hM.csInf_eq]
  exact hM

/-- Backward stability is the last boundary hit, and `0` when there is none. -/
theorem productBackStability_eq_sSup (u v : FinitaryPerm ℕ+) :
    productBackStability u v = sSup {k | BoundaryHit u v k} := by
  have hb := bddAbove_boundaryHit u v
  have hM : IsLeast {k | IsSupportStableFrom u v k} (sSup {k | BoundaryHit u v k}) := by
    constructor
    · rw [Set.mem_ofPred_eq, isSupportStableFrom_iff]
      intro j hj hh
      exact absurd (le_csSup hb hh) (by omega)
    · intro k hk
      rw [Set.mem_ofPred_eq, isSupportStableFrom_iff] at hk
      rcases Set.eq_empty_or_nonempty {k | BoundaryHit u v k} with he | hne
      · simp only [he, csSup_empty, bot_eq_zero', zero_le]
      · by_contra hlt
        exact hk _ (by omega) (Nat.sSup_mem hne hb)
  exact (productBackStability_isLeast u v).unique hM

/-- The support is stable from backward stability on. -/
theorem isSupportStableFrom_productBackStability (u v : FinitaryPerm ℕ+) :
    IsSupportStableFrom u v (productBackStability u v) :=
  (productBackStability_isLeast u v).1

/-- Every boundary hit occurs at most at backward stability. -/
theorem le_productBackStability_of_boundaryHit {u v : FinitaryPerm ℕ+} {k : ℕ}
    (h : BoundaryHit u v k) : k ≤ productBackStability u v := by
  rw [productBackStability_eq_sSup]
  exact le_csSup (bddAbove_boundaryHit u v) h

/-- The product of two identity Schubert polynomials has backward stability zero. -/
@[simp] theorem productBackStability_one : productBackStability 1 1 = 0 := by
  rw [productBackStability_eq_sSup]
  have he : {k | BoundaryHit (1 : FinitaryPerm ℕ+) 1 k} = ∅ :=
    Set.eq_empty_of_forall_notMem (fun k => not_boundaryHit_one k)
  rw [he, csSup_empty]
  rfl

/-- Exchanging the factors preserves backward stability. -/
theorem productBackStability_comm (u v : FinitaryPerm ℕ+) :
    productBackStability u v = productBackStability v u := by
  have he : {k | BoundaryHit u v k} = {k | BoundaryHit v u k} := by
    ext k
    simp only [Set.mem_ofPred_eq, boundaryHit_iff_backShiftWitness, backShiftWitness_comm]
  rw [productBackStability_eq_sSup, productBackStability_eq_sSup, he]

end SchubertPolynomial
