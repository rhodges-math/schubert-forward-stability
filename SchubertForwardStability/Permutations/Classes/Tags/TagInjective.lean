import SchubertForwardStability.Permutations.Classes.Tags.TagReadout
import SchubertForwardStability.Permutations.Classes.ProjectionWords

/-! # Injectivity of Boolean boundary vectors

Boundary symbols determine generator presence and the order of every neighboring
pair. The least distinct word is recovered by normal-word uniqueness.
-/

namespace FinitaryPerm

/-- Every generator in the selected word lies below any ambient support bound. -/
theorem lexFirst_letter_bound {n : ℕ} (w : FinitaryPerm ℕ+) (hs : IsSupported n w)
    (i : ℕ+) (hi : i ∈ w.lexFirstReducedWord) : (i : ℕ) < n := by
  obtain ⟨word, hword⟩ := exists_reducedWordIn w hs
  have he := reducedWord_toFinset_eq w word _ hword.1 (isReducedWordIn_lexFirst w).1
  have hm := List.mem_toFinset.mpr hi
  rw [← he] at hm
  exact hword.2 i (List.mem_toFinset.mp hm)

private theorem continues_present (w : FinitaryPerm ℕ+) (t : ℕ)
    (hc : GeneratorContinues w t) : GeneratorPresent w t := by
  obtain ⟨i, j, hi, _, hPair⟩ := hc
  exact ⟨i, hi, hPair.sublist.subset (by simp)⟩

private theorem continues_tag (n : ℕ) (w : FinitaryPerm ℕ+) (t : ℕ)
    (hp : 0 < t) (hn : t < n) : GeneratorContinues w t ↔ blockTag n w t = .cont := by
  rw [blockTag_eq_cont_iff]
  constructor
  · intro hc
    exact ⟨⟨hp, hn, continues_present w t hc⟩, hc⟩
  · exact And.right

private theorem not_continues_above {n : ℕ} (w : FinitaryPerm ℕ+) (hs : IsSupported n w)
    (t : ℕ) (ht : n ≤ t) : ¬GeneratorContinues w t := by
  intro hc
  obtain ⟨i, hi, hm⟩ := continues_present w t hc
  have hb := lexFirst_letter_bound w hs i hm
  omega

private theorem tag_eq_at {n : ℕ} (u v : FinitaryPerm ℕ+)
    (hTags : booleanTags n u = booleanTags n v) (i : ℕ+) (hi : (i : ℕ) < n) :
    blockTag n u (i : ℕ) = blockTag n v (i : ℕ) := by
  let p : Fin (n - 1) := ⟨(i : ℕ) - 1, by have hp := i.pos; omega⟩
  have he := congrFun hTags p
  change blockTag n u ((i : ℕ) - 1 + 1) = blockTag n v ((i : ℕ) - 1 + 1) at he
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt i.pos)] at he
  exact he

private theorem membership_of_tags {n : ℕ} (u v : FinitaryPerm ℕ+)
    (hsu : IsSupported n u) (hsv : IsSupported n v)
    (hTags : booleanTags n u = booleanTags n v) (i : ℕ+) :
    i ∈ u.lexFirstReducedWord ↔ i ∈ v.lexFirstReducedWord := by
  by_cases hi : (i : ℕ) < n
  · have hU : blockTag n u (i : ℕ) ≠ .zero ↔ i ∈ u.lexFirstReducedWord := by
      rw [blockTag_ne_zero_iff, generatorPresent_iff_mem]
      simp [i.pos, hi]
    have hV : blockTag n v (i : ℕ) ≠ .zero ↔ i ∈ v.lexFirstReducedWord := by
      rw [blockTag_ne_zero_iff, generatorPresent_iff_mem]
      simp [i.pos, hi]
    rw [← hU, ← hV, tag_eq_at u v hTags i hi]
  · exact iff_of_false (fun hm => hi (lexFirst_letter_bound u hsu i hm))
      (fun hm => hi (lexFirst_letter_bound v hsv i hm))

private theorem continuations_of_tags {n : ℕ} (u v : FinitaryPerm ℕ+)
    (hsu : IsSupported n u) (hsv : IsSupported n v)
    (hTags : booleanTags n u = booleanTags n v) (j : ℕ+) :
    GeneratorContinues u ((j + 1 : ℕ+) : ℕ) ↔
      GeneratorContinues v ((j + 1 : ℕ+) : ℕ) := by
  by_cases hj : ((j + 1 : ℕ+) : ℕ) < n
  · rw [continues_tag n u _ (j + 1).pos hj, continues_tag n v _ (j + 1).pos hj,
      tag_eq_at u v hTags (j + 1) hj]
  · exact iff_of_false (not_continues_above u hsu _ (Nat.le_of_not_gt hj))
      (not_continues_above v hsv _ (Nat.le_of_not_gt hj))

private theorem lower_projection_eq (u v : FinitaryPerm ℕ+)
    (hBu : IsBoolean u) (hBv : IsBoolean v)
    (hMem : ∀ i : ℕ+, i ∈ u.lexFirstReducedWord ↔ i ∈ v.lexFirstReducedWord)
    (hCont : ∀ j : ℕ+, GeneratorContinues u ((j + 1 : ℕ+) : ℕ) ↔
      GeneratorContinues v ((j + 1 : ℕ+) : ℕ)) (i j : ℕ+) (hij : i + 1 = j) :
    neighborProjection i j u.lexFirstReducedWord =
      neighborProjection i j v.lexFirstReducedWord := by
  have hNe : i ≠ j := by
    intro he
    have hN := congrArg PNat.val hij
    change (i : ℕ) + 1 = (j : ℕ) at hN
    have heN := congrArg PNat.val he
    omega
  apply neighborProjection_eq_of_flags _ _ hBu.lexFirst_nodup hBv.lexFirst_nodup
    i j hNe (hMem i) (hMem j)
  have hc := hCont i
  rw [hBu.continues_iff_projection, hBv.continues_iff_projection, hij,
    neighborProjection_comm j i u.lexFirstReducedWord,
    neighborProjection_comm j i v.lexFirstReducedWord] at hc
  exact hc

/-- The boundary vector is injective on every finite Boolean family. -/
theorem booleanTags_injective (n : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : u ∈ boolean n) (hv : v ∈ boolean n)
    (hTags : booleanTags n u = booleanTags n v) : u = v := by
  obtain ⟨hsu, hBu⟩ := (mem_boolean n u).mp hu
  obtain ⟨hsv, hBv⟩ := (mem_boolean n v).mp hv
  have hMem := membership_of_tags u v hsu hsv hTags
  have hCont := continuations_of_tags u v hsu hsv hTags
  have hSupport : u.lexFirstReducedWord.toFinset = v.lexFirstReducedWord.toFinset := by
    ext i
    simpa using hMem i
  have hWords : u.lexFirstReducedWord = v.lexFirstReducedWord := by
    apply normalWord_eq_of_projections _ _ hBu.lexFirst_nodup hBv.lexFirst_nodup
      (not_hasCommutingInversion_lexFirst u) (not_hasCommutingInversion_lexFirst v) hSupport
    intro i j hij
    rcases hij with hij | hij
    · exact lower_projection_eq u v hBu hBv hMem hCont i j hij
    · exact (neighborProjection_comm i j _).trans
        ((lower_projection_eq u v hBu hBv hMem hCont j i hij).trans
          (neighborProjection_comm i j _).symm)
  exact (isReducedWordIn_lexFirst u).1.1.symm.trans
    ((congrArg wordProduct hWords).trans (isReducedWordIn_lexFirst v).1.1)

/-- The tag map is injective on every finite Boolean family, including size zero. -/
theorem booleanTags_injOn (n : ℕ) :
    Set.InjOn (booleanTags n) (boolean n : Set (FinitaryPerm ℕ+)) := by
  intro u hu v hv hTags
  exact booleanTags_injective n u v hu hv hTags

end FinitaryPerm
