import Results.FcMorrisV2.Defs
import Mathlib.Data.Fintype.Basic

/-!
# Solution/Chain: the parity-chain lemma (paper Lemma 4.3)

Proof (paper): put `S = {i | [k] ∖ {i} ∈ J}` and `R = [k] ∖ S`.  The complement family
`L = {[k] ∖ I | I ∈ J}` is union-closed, contains `{i}` for `i ∈ S` and every pair `{i, j} ⊆ R`.
We work with `J` directly: a set `I ≠ [k]` belongs to `J` as soon as every point outside `I` is
avoided by a member of `J` containing `I` (`Chain.mem_of_witness`).  For a nonempty `D` in which
every `R`-point has a second `R`-point, the witnesses are `[k] ∖ {x}` (`x ∈ S`) and
`[k] ∖ {x, y}` (`x, y ∈ R`, `Chain.pair_mem`).  The nested sets `D_m` (`|D_m| = 2m`) are the
initial segments of a duplicate-free list that starts with two points of `R` when `|R| ≥ 2`, and
lists only points of `S` otherwise; the chain is `I_j = [k] ∖ D_{h-j}`.
-/

namespace Results.FcMorrisV2

open Finset

namespace Chain

/-- `|Fin k| = k`, from the definition of the `Fintype (Fin k)` instance. -/
theorem card_univ_fin (k : ℕ) : (univ : Finset (Fin k)).card = k := by
  rw [Fin.univ_def, card_mk, Multiset.coe_card, List.length_finRange]

/-- In an intersection-closed family `J` of subsets of `Fin k`: if `I` misses some point and every
point outside `I` is avoided by a member of `J` containing `I`, then `I ∈ J` (it is the
intersection of those members). -/
theorem mem_of_witness {k : ℕ} (J : Finset (Finset (Fin k)))
    (hJ2 : ∀ I ∈ J, ∀ I' ∈ J, I ∩ I' ∈ J) (I : Finset (Fin k))
    (hI : (univ \ I).Nonempty)
    (hw : ∀ x, x ∉ I → ∃ M ∈ J, I ⊆ M ∧ x ∉ M) : I ∈ J := by
  have key : ∀ T : Finset (Fin k), T.Nonempty → T ⊆ univ \ I →
      ∃ M ∈ J, I ⊆ M ∧ Disjoint M T := by
    intro T hT
    induction hT using Finset.Nonempty.cons_induction with
    | singleton a =>
      intro hsub
      have ha : a ∉ I := (mem_sdiff.mp (hsub (mem_singleton_self a))).2
      obtain ⟨M, hMJ, hIM, haM⟩ := hw a ha
      exact ⟨M, hMJ, hIM, disjoint_singleton_right.mpr haM⟩
    | cons a T haT hT ih =>
      intro hsub
      have ha : a ∉ I := (mem_sdiff.mp (hsub (mem_cons_self a T))).2
      obtain ⟨M, hMJ, hIM, haM⟩ := hw a ha
      obtain ⟨M', hM'J, hIM', hM'T⟩ := ih ((subset_cons haT).trans hsub)
      refine ⟨M ∩ M', hJ2 M hMJ M' hM'J, subset_inter hIM hIM', ?_⟩
      rw [disjoint_left]
      intro x hx hxc
      rw [mem_inter] at hx
      rw [mem_cons] at hxc
      rcases hxc with rfl | hxT
      · exact haM hx.1
      · exact disjoint_left.mp hM'T hx.2 hxT
  obtain ⟨M, hMJ, hIM, hMd⟩ := key (univ \ I) hI subset_rfl
  have hMI : M = I := by
    apply Subset.antisymm _ hIM
    intro x hxM
    by_contra hxI
    exact disjoint_left.mp hMd hxM (mem_sdiff.mpr ⟨mem_univ x, hxI⟩)
  rwa [hMI] at hMJ

/-- If both single-deletion facets `univ.erase x`, `univ.erase y` (`x ≠ y`) are missing from `J`,
then the `(k-2)`-set `univ \ {x, y}` belongs to `J`: a member of `J` containing it is proper, and
is neither of the two missing facets. -/
theorem pair_mem {k : ℕ} (J : Finset (Finset (Fin k)))
    (hJ1 : ∀ I ∈ J, I ≠ Finset.univ)
    (hcov : ∀ I : Finset (Fin k), I.card = k - 2 → ∃ I' ∈ J, I ⊆ I')
    {x y : Fin k} (hxy : x ≠ y) (hx : univ.erase x ∉ J) (hy : univ.erase y ∉ J) :
    univ \ {x, y} ∈ J := by
  have hcard : (univ \ {x, y} : Finset (Fin k)).card = k - 2 := by
    rw [card_sdiff_of_subset (subset_univ _), Chain.card_univ_fin, card_pair hxy]
  obtain ⟨I', hI'J, hsub⟩ := hcov _ hcard
  have hmem : ∀ z, z ≠ x → z ≠ y → z ∈ I' := by
    intro z hzx hzy
    apply hsub
    rw [mem_sdiff, mem_insert, mem_singleton]
    exact ⟨mem_univ z, fun h' => h'.elim hzx hzy⟩
  have hI' : I' = univ \ {x, y} := by
    by_cases hxI : x ∈ I'
    · by_cases hyI : y ∈ I'
      · exfalso
        apply hJ1 I' hI'J
        apply eq_univ_of_forall
        intro z
        by_cases hzx : z = x
        · rw [hzx]; exact hxI
        by_cases hzy : z = y
        · rw [hzy]; exact hyI
        exact hmem z hzx hzy
      · exfalso
        apply hy
        have hI'y : I' = univ.erase y := by
          ext z
          rw [mem_erase]
          constructor
          · intro hz
            refine ⟨?_, mem_univ z⟩
            rintro rfl
            exact hyI hz
          · rintro ⟨hzy, -⟩
            by_cases hzx : z = x
            · rw [hzx]; exact hxI
            exact hmem z hzx hzy
        rw [← hI'y]; exact hI'J
    · by_cases hyI : y ∈ I'
      · exfalso
        apply hx
        have hI'x : I' = univ.erase x := by
          ext z
          rw [mem_erase]
          constructor
          · intro hz
            refine ⟨?_, mem_univ z⟩
            rintro rfl
            exact hxI hz
          · rintro ⟨hzx, -⟩
            by_cases hzy : z = y
            · rw [hzy]; exact hyI
            exact hmem z hzx hzy
        rw [← hI'x]; exact hI'J
      · apply Subset.antisymm _ hsub
        intro z hz
        rw [mem_sdiff, mem_insert, mem_singleton]
        refine ⟨mem_univ z, ?_⟩
        rintro (rfl | rfl)
        · exact hxI hz
        · exact hyI hz
  rw [← hI']; exact hI'J

end Chain

/-- **Parity-chain lemma.** Let `k ≥ 3`, `k = p + 2h` with `p ∈ {1,2}`, and let `J` be an
intersection-closed family of proper subsets of `[k]` such that every `(k-2)`-subset of `[k]` is
contained in a member of `J`.  Then `J` contains a chain `I₀ ⊂ I₁ ⊂ ⋯ ⊂ I_{h-1}` with
`|I_j| = p + 2j`. -/
theorem chain_lemma (k p h : ℕ) (hk : 3 ≤ k) (hp : p = 1 ∨ p = 2) (hkph : k = p + 2 * h)
    (J : Finset (Finset (Fin k)))
    (hJ1 : ∀ I ∈ J, I ≠ Finset.univ) (hJ2 : ∀ I ∈ J, ∀ I' ∈ J, I ∩ I' ∈ J)
    (hcov : ∀ I : Finset (Fin k), I.card = k - 2 → ∃ I' ∈ J, I ⊆ I') :
    ∃ Ich : ℕ → Finset (Fin k), (∀ j < h, Ich j ∈ J ∧ (Ich j).card = p + 2 * j) ∧
      (∀ j, j + 1 < h → Ich j ⊆ Ich (j + 1)) := by
  classical
  -- a nonempty `D` in which every `R`-point has a second `R`-point has its complement in `J`
  have good : ∀ D : Finset (Fin k), D.Nonempty →
      (∀ x ∈ D, univ.erase x ∉ J → ∃ y ∈ D, y ≠ x ∧ univ.erase y ∉ J) → univ \ D ∈ J := by
    intro D hD hgood
    apply Chain.mem_of_witness J hJ2 (univ \ D)
    · rwa [Finset.sdiff_sdiff_eq_self (subset_univ D)]
    · intro x hx
      have hxD : x ∈ D := by simpa using hx
      by_cases hxS : univ.erase x ∈ J
      · refine ⟨univ.erase x, hxS, ?_, ?_⟩
        · intro z hz
          rw [mem_erase]
          refine ⟨?_, mem_univ z⟩
          rintro rfl
          exact (mem_sdiff.mp hz).2 hxD
        · simp
      · obtain ⟨y, hyD, hyx, hyR⟩ := hgood x hxD hxS
        refine ⟨univ \ {x, y}, Chain.pair_mem J hJ1 hcov (Ne.symm hyx) hxS hyR, ?_, ?_⟩
        · apply sdiff_subset_sdiff (subset_refl _)
          intro z hz
          rw [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hxD
          · exact hyD
        · simp
  -- a duplicate-free list whose initial segments of even positive length are all good
  obtain ⟨l, hlnd, hllen, hlgood⟩ : ∃ l : List (Fin k), l.Nodup ∧ 2 * h ≤ l.length ∧
      ∀ m, 1 ≤ m → ∀ x ∈ l.take (2 * m), univ.erase x ∉ J →
        ∃ y ∈ l.take (2 * m), y ≠ x ∧ univ.erase y ∉ J := by
    by_cases hR : ∃ r1 r2 : Fin k, r1 ≠ r2 ∧ univ.erase r1 ∉ J ∧ univ.erase r2 ∉ J
    · -- `|R| ≥ 2`: start with two points of `R`
      obtain ⟨r1, r2, h12, hr1, hr2⟩ := hR
      refine ⟨r1 :: r2 :: (univ \ {r1, r2}).toList, ?_, ?_, ?_⟩
      · rw [List.nodup_cons, List.nodup_cons]
        refine ⟨?_, ?_, nodup_toList _⟩
        · rw [List.mem_cons, mem_toList]
          rintro (h' | h')
          · exact h12 h'
          · simp at h'
        · rw [mem_toList]
          simp
      · rw [List.length_cons, List.length_cons, length_toList,
          card_sdiff_of_subset (subset_univ _), Chain.card_univ_fin, card_pair h12]
        omega
      · intro m hm x hx hxR
        have h2m : 2 * m = (2 * m - 2) + 1 + 1 := by omega
        rw [h2m, List.take_succ_cons, List.take_succ_cons] at hx ⊢
        by_cases hx1 : x = r1
        · exact ⟨r2, by simp, fun h' => h12 (h'.trans hx1).symm, hr2⟩
        · exact ⟨r1, by simp, fun h' => hx1 h'.symm, hr1⟩
    · -- `|R| ≤ 1`: list the points of `S`; there are at least `k - 1 ≥ 2h` of them
      refine ⟨(univ.filter fun i => univ.erase i ∈ J).toList, nodup_toList _, ?_, ?_⟩
      · rw [length_toList]
        have hRcard : (univ.filter fun i => ¬ (univ.erase i ∈ J)).card ≤ 1 := by
          rw [card_le_one]
          intro a ha b hb
          by_contra hab
          rw [mem_filter] at ha hb
          exact hR ⟨a, b, hab, ha.2, hb.2⟩
        have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin k)))
          (fun i => univ.erase i ∈ J)
        rw [Chain.card_univ_fin] at hsum
        omega
      · intro m hm x hx hxR
        exfalso
        have hx' := List.mem_of_mem_take hx
        rw [mem_toList, mem_filter] at hx'
        exact hxR hx'.2
  -- the chain: `Ich j = univ \ D_{h-j}` with `D_m` the first `2m` entries of `l`
  refine ⟨fun j => univ \ (l.take (2 * (h - j))).toFinset, ?_, ?_⟩
  · intro j hj
    dsimp only
    have hcardD : (l.take (2 * (h - j))).toFinset.card = 2 * (h - j) := by
      rw [List.toFinset_card_of_nodup ((List.take_sublist _ _).nodup hlnd), List.length_take]
      omega
    refine ⟨?_, ?_⟩
    · apply good
      · rw [← card_pos, hcardD]
        omega
      · intro x hx hxR
        rw [List.mem_toFinset] at hx
        obtain ⟨y, hy, hyx, hyR⟩ := hlgood (h - j) (by omega) x hx hxR
        exact ⟨y, List.mem_toFinset.mpr hy, hyx, hyR⟩
    · rw [card_sdiff_of_subset (subset_univ _), Chain.card_univ_fin, hcardD]
      omega
  · intro j hj
    dsimp only
    apply sdiff_subset_sdiff (subset_refl _)
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact List.take_subset_take_left l (by omega) hx

end Results.FcMorrisV2
