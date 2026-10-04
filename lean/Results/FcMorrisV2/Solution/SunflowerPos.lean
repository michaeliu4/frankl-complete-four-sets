import Results.FcMorrisV2.Solution.SunflowerDefs

/-!
# Solution/SunflowerPos: positive direction of Theorem 1.2 (paper Section 5.1: charging inequality)

The proof follows the paper's charging inequality (Lemma "Charging inequality") and the
weighted proposition with core weight `a = 3`, but is organised through subfamilies of the
admissible family `B` instead of core-trace slices:

* `up B A = {X ∈ B : A ⊆ X, X \ A ∉ B}` and `dn B A = {Y ∈ B : Y ∩ A = ∅, Y ∪ A ∉ B}`.
  For `A = C` these correspond (via `X ↦ X \ C`) to the paper's `𝒳 = 𝒟_C \ 𝒟_∅` and
  `𝒴 = 𝒟_∅ \ 𝒟_C`; for `A = Pᵢ` they are the positive and negative pair fibres.
* Share identity (`share_eq`):
  `∑_{X ∈ B} (3|X ∩ C| + |X \ C| - (3 + t)) = 3 (|up C| - |dn C|) + ∑ᵢ (|up Pᵢ| - |dn Pᵢ|)`.
* Negative charge (`neg_charge`): `∑ᵢ |dn Pᵢ| ≤ 3 |up C|`, by the injection
  `(i, Y) ↦ (Y ∩ C, Y ∪ (C ∪ Pᵢ))` into `(2^C \ {C}) × up C`.
* Positive charge (`pos_charge`): `|dn C| ≤ 3 |up Pᵢ|` for every `i`, by the injection
  `Y ↦ (Y ∪ (C ∪ Pᵢ), Y ∩ Pᵢ)` into `up Pᵢ × (2^{Pᵢ} \ {Pᵢ})`.
* Hence `3 Q ≥ (t - 9) |dn C| ≥ 0` for `t ≥ 9`.
-/

namespace Results.FcMorrisV2

open Finset

namespace SunflowerPos

/-- Members of `B` containing `A` whose lower partner `X \ A` is missing from `B`. -/
def up (B : Fam) (A : Finset ℕ) : Fam := B.filter fun X => A ⊆ X ∧ X \ A ∉ B

/-- Members of `B` disjoint from `A` whose upper partner `Y ∪ A` is missing from `B`. -/
def dn (B : Fam) (A : Finset ℕ) : Fam := B.filter fun Y => Disjoint Y A ∧ Y ∪ A ∉ B

lemma mem_up {B : Fam} {A X : Finset ℕ} : X ∈ up B A ↔ X ∈ B ∧ A ⊆ X ∧ X \ A ∉ B :=
  mem_filter

lemma mem_dn {B : Fam} {A Y : Finset ℕ} : Y ∈ dn B A ↔ Y ∈ B ∧ Disjoint Y A ∧ Y ∪ A ∉ B :=
  mem_filter

/-- For a two-element set `A`: `|X ∩ A| - 1 = [A ⊆ X] - [X ∩ A = ∅]`. -/
lemma pair_card (A X : Finset ℕ) (hA : A.card = 2) :
    ((X ∩ A).card : ℚ) - 1 = (if A ⊆ X then 1 else 0) - (if Disjoint X A then 1 else 0) := by
  by_cases h1 : A ⊆ X
  · have hXA : X ∩ A = A := inter_eq_right.mpr h1
    have h2 : ¬ Disjoint X A := by
      rw [disjoint_iff_inter_eq_empty, hXA]
      intro h
      rw [h, card_empty] at hA
      exact absurd hA (by norm_num)
    rw [if_pos h1, if_neg h2, hXA, hA]
    norm_num
  · by_cases h2 : Disjoint X A
    · rw [if_neg h1, if_pos h2, disjoint_iff_inter_eq_empty.mp h2, card_empty]
      norm_num
    · have hne : (X ∩ A).card ≠ 0 := by
        intro h
        exact h2 (disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp h))
      have hne2 : (X ∩ A).card ≠ 2 := by
        intro h
        exact h1 (inter_eq_right.mp (eq_of_subset_of_card_le inter_subset_right (by rw [h, hA])))
      have hle : (X ∩ A).card ≤ 2 := hA ▸ card_le_card inter_subset_right
      have h1' : (X ∩ A).card = 1 := by omega
      rw [if_neg h1, if_neg h2, h1']
      norm_num

/-- Cancelling the pairs `X ↔ X \ A` of members of `B` that are both present. -/
lemma flip_card (B : Fam) (A : Finset ℕ) :
    ((B.filter fun X => A ⊆ X).card : ℚ) - ((B.filter fun Y => Disjoint Y A).card : ℚ)
      = ((up B A).card : ℚ) - ((dn B A).card : ℚ) := by
  have h1 : (B.filter fun X => A ⊆ X).card
      = (up B A).card + (B.filter fun X => A ⊆ X ∧ X \ A ∈ B).card := by
    rw [← card_filter_add_card_filter_not (s := B.filter fun X => A ⊆ X) (fun X => X \ A ∈ B),
      filter_filter, filter_filter, add_comm]
    rfl
  have h2 : (B.filter fun Y => Disjoint Y A).card
      = (dn B A).card + (B.filter fun Y => Disjoint Y A ∧ Y ∪ A ∈ B).card := by
    rw [← card_filter_add_card_filter_not (s := B.filter fun Y => Disjoint Y A)
        (fun Y => Y ∪ A ∈ B), filter_filter, filter_filter, add_comm]
    rfl
  have h3 : (B.filter fun X => A ⊆ X ∧ X \ A ∈ B).card
      = (B.filter fun Y => Disjoint Y A ∧ Y ∪ A ∈ B).card := by
    apply card_bij' (fun X _ => X \ A) (fun Y _ => Y ∪ A)
    · intro X hX
      rw [mem_filter] at hX ⊢
      refine ⟨?_, sdiff_disjoint, ?_⟩
      · exact hX.2.2
      · rw [sdiff_union_of_subset hX.2.1]
        exact hX.1
    · intro Y hY
      rw [mem_filter] at hY ⊢
      refine ⟨hY.2.2, subset_union_right, ?_⟩
      rw [union_sdiff_cancel_right hY.2.1]
      exact hY.1
    · intro X hX
      rw [mem_filter] at hX
      exact sdiff_union_of_subset hX.2.1
    · intro Y hY
      rw [mem_filter] at hY
      exact union_sdiff_cancel_right hY.2.1
  rw [h1, h2, h3]
  push_cast
  ring

variable {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ}

lemma mem_supp_iff {u : ℕ} : u ∈ supp (sunflowerCfg t C P) ↔ ∃ i, u ∈ C ∪ P i := by
  unfold supp sunflowerCfg
  rw [mem_biUnion]
  constructor
  · rintro ⟨g, hg, hu⟩
    rw [mem_image] at hg
    obtain ⟨i, -, rfl⟩ := hg
    exact ⟨i, hu⟩
  · rintro ⟨i, hu⟩
    exact ⟨C ∪ P i, mem_image.mpr ⟨i, mem_univ i, rfl⟩, hu⟩

lemma gen_mem (i : Fin t) : C ∪ P i ∈ sunflowerCfg t C P :=
  mem_image.mpr ⟨i, mem_univ i, rfl⟩

lemma petal_subset_supp (i : Fin t) : P i ⊆ supp (sunflowerCfg t C P) := fun _ hu =>
  mem_supp_iff.mpr ⟨i, mem_union_right C hu⟩

lemma sdiff_core_eq (hd : SunflowerData t C P) {X : Finset ℕ}
    (hX : X ⊆ supp (sunflowerCfg t C P)) : X \ C = univ.biUnion fun i => X ∩ P i := by
  ext u
  rw [mem_sdiff, mem_biUnion]
  constructor
  · rintro ⟨huX, huC⟩
    obtain ⟨i, hi⟩ := mem_supp_iff.mp (hX huX)
    rcases mem_union.mp hi with h | h
    · exact absurd h huC
    · exact ⟨i, mem_univ i, mem_inter.mpr ⟨huX, h⟩⟩
  · rintro ⟨i, -, hu⟩
    rw [mem_inter] at hu
    exact ⟨hu.1, fun huC => disjoint_left.mp (hd.hCP i) huC hu.2⟩

/-- For `X ⊆ supp`, the petal part of `X` splits over the disjoint petals. -/
lemma card_sdiff_core (hd : SunflowerData t C P) {X : Finset ℕ}
    (hX : X ⊆ supp (sunflowerCfg t C P)) : (X \ C).card = ∑ i, (X ∩ P i).card := by
  rw [sdiff_core_eq hd hX, card_biUnion]
  intro i _ j _ hij
  exact Disjoint.mono inter_subset_right inter_subset_right (hd.hPP i j hij)

/-- Pointwise form of the share identity. -/
lemma pointwise (hd : SunflowerData t C P) {X : Finset ℕ} (hX : X ⊆ supp (sunflowerCfg t C P)) :
    3 * ((X ∩ C).card : ℚ) + ((X \ C).card : ℚ) - (3 + (t : ℚ))
      = 3 * ((if C ⊆ X then (1 : ℚ) else 0) - (if Disjoint X C then 1 else 0))
        + ∑ i, ((if P i ⊆ X then (1 : ℚ) else 0) - (if Disjoint X (P i) then 1 else 0)) := by
  have hsum : ∑ i, ((if P i ⊆ X then (1 : ℚ) else 0) - (if Disjoint X (P i) then 1 else 0))
      = ∑ i, (((X ∩ P i).card : ℚ) - 1) :=
    sum_congr rfl fun i _ => (pair_card (P i) X (hd.hP i)).symm
  rw [hsum, ← pair_card C X hd.hC, sum_sub_distrib, card_sdiff_core hd hX, Nat.cast_sum,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- Share identity: `Q = 3 (|up C| - |dn C|) + ∑ᵢ (|up Pᵢ| - |dn Pᵢ|)`. -/
lemma share_eq (hd : SunflowerData t C P) {B : Fam}
    (hB : ∀ X ∈ B, X ⊆ supp (sunflowerCfg t C P)) :
    ∑ X ∈ B, (3 * ((X ∩ C).card : ℚ) + ((X \ C).card : ℚ) - (3 + (t : ℚ)))
      = 3 * (((up B C).card : ℚ) - (dn B C).card)
        + ∑ i, (((up B (P i)).card : ℚ) - (dn B (P i)).card) := by
  have key : ∀ A : Finset ℕ,
      ∑ X ∈ B, ((if A ⊆ X then (1 : ℚ) else 0) - (if Disjoint X A then 1 else 0))
        = ((up B A).card : ℚ) - (dn B A).card := by
    intro A
    rw [sum_sub_distrib, sum_boole, sum_boole]
    exact flip_card B A
  rw [sum_congr rfl fun X hX => pointwise hd (hB X hX), sum_add_distrib, ← mul_sum, sum_comm,
    key C]
  congr 1
  exact sum_congr rfl fun i _ => key (P i)

/-- Negative charge: `∑ᵢ |dn Pᵢ| ≤ 3 |up C|`. -/
lemma neg_charge (hd : SunflowerData t C P) {B : Fam} (hB : Admissible (sunflowerCfg t C P) B) :
    ∑ i, (dn B (P i)).card ≤ 3 * (up B C).card := by
  have hcard : ((C.powerset.erase C) ×ˢ up B C).card = 3 * (up B C).card := by
    rw [card_product, card_erase_of_mem (mem_powerset_self C), card_powerset, hd.hC]
    rfl
  calc ∑ i, (dn B (P i)).card = (univ.sigma fun i => dn B (P i)).card := (card_sigma _ _).symm
    _ ≤ ((C.powerset.erase C) ×ˢ up B C).card := by
      apply card_le_card_of_injOn
        (fun p : (Σ _ : Fin t, Finset ℕ) => (p.2 ∩ C, p.2 ∪ (C ∪ P p.1)))
      · rintro ⟨i, Y⟩ hY
        simp only [mem_coe, mem_sigma, mem_univ, true_and, mem_dn] at hY
        obtain ⟨hYB, -, hYn⟩ := hY
        have hPC : ∀ u, u ∈ P i → u ∉ C := fun u hu huC => disjoint_left.mp (hd.hCP i) huC hu
        have hstab : Y ∪ (C ∪ P i) ∈ B := hB.2.2 Y hYB _ (gen_mem i)
        simp only [mem_coe, mem_product, mem_erase, mem_powerset, mem_up]
        refine ⟨⟨?_, inter_subset_right⟩, hstab, ?_, ?_⟩
        · intro h
          apply hYn
          have hCY : C ⊆ Y := inter_eq_right.mp h
          have hY' : Y ∪ (C ∪ P i) = Y ∪ P i := by
            rw [← union_assoc, union_eq_left.mpr hCY]
          rw [← hY']
          exact hstab
        · intro u hu
          exact mem_union_right Y (mem_union_left _ hu)
        · intro h
          apply hYn
          have hY' : (Y ∪ (C ∪ P i)) \ C ∪ Y = Y ∪ P i := by
            ext u
            simp only [mem_union, mem_sdiff]
            constructor
            · rintro (⟨h | h | h, hc⟩ | h)
              · exact Or.inl h
              · exact absurd h hc
              · exact Or.inr h
              · exact Or.inl h
            · rintro (h | h)
              · exact Or.inr h
              · exact Or.inl ⟨Or.inr (Or.inr h), hPC u h⟩
          rw [← hY']
          exact hB.2.1 _ h Y hYB
      · rintro ⟨i, Y⟩ hY ⟨j, Y'⟩ hY' heq
        simp only [mem_coe, mem_sigma, mem_univ, true_and, mem_dn] at hY hY'
        obtain ⟨hYB, hYP, hYn⟩ := hY
        obtain ⟨hYB', hYP', -⟩ := hY'
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hC', hU'⟩ := heq
        by_cases hij : i = j
        · subst hij
          have hYY : Y = Y' := by
            ext u
            have h1 := Finset.ext_iff.mp hC' u
            have h2 := Finset.ext_iff.mp hU' u
            simp only [mem_inter, mem_union] at h1 h2
            constructor
            · intro hu
              by_cases huC : u ∈ C
              · exact (h1.mp ⟨hu, huC⟩).1
              · rcases h2.mp (Or.inl hu) with h | h | h
                · exact h
                · exact absurd h huC
                · exact absurd h (disjoint_left.mp hYP hu)
            · intro hu
              by_cases huC : u ∈ C
              · exact (h1.mpr ⟨hu, huC⟩).1
              · rcases h2.mpr (Or.inl hu) with h | h | h
                · exact h
                · exact absurd h huC
                · exact absurd h (disjoint_left.mp hYP' hu)
          rw [hYY]
        · exfalso
          apply hYn
          have hYY : Y ∪ Y' = Y ∪ P i := by
            ext u
            have h1 := Finset.ext_iff.mp hC' u
            have h2 := Finset.ext_iff.mp hU' u
            simp only [mem_inter, mem_union] at h1 h2 ⊢
            constructor
            · rintro (hu | hu)
              · exact Or.inl hu
              · by_cases huC : u ∈ C
                · exact Or.inl (h1.mpr ⟨hu, huC⟩).1
                · rcases h2.mpr (Or.inl hu) with h | h | h
                  · exact Or.inl h
                  · exact absurd h huC
                  · exact Or.inr h
            · rintro (hu | hu)
              · exact Or.inl hu
              · rcases h2.mp (Or.inr (Or.inr hu)) with h | h | h
                · exact Or.inr h
                · exact absurd h (fun huC => disjoint_left.mp (hd.hCP i) huC hu)
                · exact absurd h (disjoint_left.mp (hd.hPP i j hij) hu)
          rw [← hYY]
          exact hB.2.1 Y hYB Y' hYB'
    _ = 3 * (up B C).card := hcard

/-- Positive charge: `|dn C| ≤ 3 |up Pᵢ|` for every petal direction `i`. -/
lemma pos_charge (hd : SunflowerData t C P) {B : Fam} (hB : Admissible (sunflowerCfg t C P) B)
    (i : Fin t) : (dn B C).card ≤ 3 * (up B (P i)).card := by
  have hcard : (up B (P i) ×ˢ (P i).powerset.erase (P i)).card = 3 * (up B (P i)).card := by
    rw [card_product, card_erase_of_mem (mem_powerset_self _), card_powerset, hd.hP i,
      mul_comm]
    rfl
  rw [← hcard]
  apply card_le_card_of_injOn (fun Y => (Y ∪ (C ∪ P i), Y ∩ P i))
  · intro Y hY
    rw [mem_coe, mem_dn] at hY
    obtain ⟨hYB, -, hYn⟩ := hY
    have hstab : Y ∪ (C ∪ P i) ∈ B := hB.2.2 Y hYB _ (gen_mem i)
    simp only [mem_coe, mem_product, mem_up, mem_erase, mem_powerset]
    refine ⟨⟨hstab, ?_, ?_⟩, ?_, inter_subset_right⟩
    · intro u hu
      exact mem_union_right Y (mem_union_right C hu)
    · intro h
      apply hYn
      have hY' : (Y ∪ (C ∪ P i)) \ P i ∪ Y = Y ∪ C := by
        ext u
        simp only [mem_union, mem_sdiff]
        constructor
        · rintro (⟨h | h | h, hp⟩ | h)
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hp
          · exact Or.inl h
        · rintro (h | h)
          · exact Or.inr h
          · exact Or.inl ⟨Or.inr (Or.inl h), disjoint_left.mp (hd.hCP i) h⟩
      rw [← hY']
      exact hB.2.1 _ h Y hYB
    · intro h
      apply hYn
      have hPY : P i ⊆ Y := inter_eq_right.mp h
      have hY' : Y ∪ (C ∪ P i) = Y ∪ C := by
        rw [union_comm C (P i), ← union_assoc, union_eq_left.mpr hPY]
      rw [← hY']
      exact hstab
  · intro Y hY Y' hY' heq
    rw [mem_coe, mem_dn] at hY hY'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hU', hP'⟩ := heq
    ext u
    have h1 := Finset.ext_iff.mp hU' u
    have h2 := Finset.ext_iff.mp hP' u
    simp only [mem_inter, mem_union] at h1 h2
    constructor
    · intro hu
      by_cases huP : u ∈ P i
      · exact (h2.mp ⟨hu, huP⟩).1
      · rcases h1.mp (Or.inl hu) with h | h | h
        · exact h
        · exact absurd h (disjoint_left.mp hY.2.1 hu)
        · exact absurd h huP
    · intro hu
      by_cases huP : u ∈ P i
      · exact (h2.mpr ⟨hu, huP⟩).1
      · rcases h1.mpr (Or.inl hu) with h | h | h
        · exact h
        · exact absurd h (disjoint_left.mp hY'.2.1 hu)
        · exact absurd h huP

/-- Main argument: `3 Q ≥ (t - 9) |dn C|` from the share identity and the two charges. -/
lemma share_nonneg (hd : SunflowerData t C P) (ht : 9 ≤ t) {B : Fam}
    (hB : Admissible (sunflowerCfg t C P) B) :
    0 ≤ ∑ X ∈ B, (3 * ((X ∩ C).card : ℚ) + ((X \ C).card : ℚ) - (3 + (t : ℚ))) := by
  rw [share_eq hd hB.1, sum_sub_distrib]
  have hN := neg_charge hd hB
  have hP : t * (dn B C).card ≤ 3 * ∑ i, (up B (P i)).card := by
    calc t * (dn B C).card = ∑ _i : Fin t, (dn B C).card := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      _ ≤ ∑ i, 3 * (up B (P i)).card := sum_le_sum fun i _ => pos_charge hd hB i
      _ = 3 * ∑ i, (up B (P i)).card := (mul_sum _ _ _).symm
  have hN' : (∑ i, ((dn B (P i)).card : ℚ)) ≤ 3 * ((up B C).card : ℚ) := by exact_mod_cast hN
  have hP' : (t : ℚ) * ((dn B C).card : ℚ) ≤ 3 * ∑ i, ((up B (P i)).card : ℚ) := by
    exact_mod_cast hP
  have ht' : (9 : ℚ) ≤ t := by exact_mod_cast ht
  have hy : (0 : ℚ) ≤ (dn B C).card := Nat.cast_nonneg _
  linarith [mul_nonneg (sub_nonneg.mpr ht') hy]

end SunflowerPos

/-- Weighted charging inequality: weight `3` on core points and `1` on petal points give a
nonnegative share on every admissible family when `t ≥ 9` (paper Proposition 5.3 with `a = 3`). -/
theorem sunflower_share_nonneg {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ}
    (hd : SunflowerData t C P) (ht : 9 ≤ t) (B : Fam) (hB : Admissible (sunflowerCfg t C P) B) :
    0 ≤ ∑ X ∈ B, (3 * ((X ∩ C).card : ℚ) + ((X \ C).card : ℚ) - (3 + (t : ℚ))) := by
  exact SunflowerPos.share_nonneg hd ht hB

/-- Positive direction of Theorem 1.2. -/
theorem sunflower_isFC {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ}
    (hd : SunflowerData t C P) (ht : 9 ≤ t) : IsFC (sunflowerCfg t C P) := by
  have ht1 : 0 < t := by omega
  have hCsupp : C ⊆ supp (sunflowerCfg t C P) := fun _ hu =>
    SunflowerPos.mem_supp_iff.mpr ⟨⟨0, ht1⟩, mem_union_left _ hu⟩
  have hsum : ∀ X : Finset ℕ, (∑ u ∈ X, (if u ∈ C then (3 : ℚ) else 1))
      = 3 * ((X ∩ C).card : ℚ) + ((X \ C).card : ℚ) := by
    intro X
    rw [sum_ite, sum_const, sum_const, filter_mem_eq_inter, filter_notMem_eq_sdiff,
      nsmul_eq_mul, nsmul_eq_mul]
    ring
  have hW : (∑ u ∈ supp (sunflowerCfg t C P), (if u ∈ C then (3 : ℚ) else 1)) = 6 + 2 * t := by
    rw [hsum, inter_eq_right.mpr hCsupp, SunflowerPos.card_sdiff_core hd subset_rfl, hd.hC]
    have h2 : ∀ i, (supp (sunflowerCfg t C P) ∩ P i).card = 2 := fun i => by
      rw [inter_eq_right.mpr (SunflowerPos.petal_subset_supp i), hd.hP i]
    rw [sum_congr rfl fun i _ => h2 i, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id]
    push_cast
    ring
  apply isFC_of_weights _ (fun u => if u ∈ C then (3 : ℚ) else 1)
  · intro u
    split_ifs <;> norm_num
  · rw [hW]
    positivity
  · intro B hB
    dsimp only [share]
    rw [hW]
    have h := sunflower_share_nonneg hd ht B hB
    calc (0 : ℚ) ≤ _ := h
      _ = _ := by
        apply sum_congr rfl
        intro X _
        rw [hsum]
        ring

end Results.FcMorrisV2
