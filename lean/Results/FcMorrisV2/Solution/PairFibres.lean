import Results.FcMorrisV2.Solution.Robust

/-!
# Solution/PairFibres: the three fibre-counting inequalities of the robust pair lifting
(paper Theorem 3.1, equations (3.2)-(3.4)); each concerns ONE generator `C` with `t` new pairs.
-/

namespace Results.FcMorrisV2

open Finset

/-- Positive pair fibres of `B` in direction `P` within the ground set `U`:
`A ⊆ U ∖ P` with `A ∉ B` and `A ∪ P ∈ B`. -/
def posFib (U : Finset ℕ) (B : Fam) (P : Finset ℕ) : Finset (Finset ℕ) :=
  (U \ P).powerset.filter fun A => A ∉ B ∧ A ∪ P ∈ B

/-- Negative pair fibres of `B` in direction `P` within `U`: `A ⊆ U ∖ P`, `A ∈ B`, `A ∪ P ∉ B`. -/
def negFib (U : Finset ℕ) (B : Fam) (P : Finset ℕ) : Finset (Finset ℕ) :=
  (U \ P).powerset.filter fun A => A ∈ B ∧ A ∪ P ∉ B

/-- Setting: `B ⊆ 2^U` is union-closed and stable under adjoining the `t` sets `C ∪ P j`, where
`P 0, …, P (t-1)` are pairwise disjoint pairs in `U` disjoint from `C ⊆ U`. -/
structure PairSetting (U : Finset ℕ) (B : Fam) (C : Finset ℕ) (t : ℕ)
    (P : ℕ → Finset ℕ) : Prop where
  memU : ∀ X ∈ B, X ⊆ U
  uc : UnionClosed B
  hC : C ⊆ U
  hPcard : ∀ j < t, (P j).card = 2
  hPU : ∀ j < t, P j ⊆ U
  hPC : ∀ j < t, Disjoint (P j) C
  hPP : ∀ j < t, ∀ j' < t, j ≠ j' → Disjoint (P j) (P j')
  stab : ∀ X ∈ B, ∀ j < t, X ∪ (C ∪ P j) ∈ B

namespace PairFibres

/-- The proper subsets of `s` number `2^{|s|} - 1`. -/
theorem card_proper (s : Finset ℕ) : (s.powerset.erase s).card = 2 ^ s.card - 1 := by
  rw [card_erase_of_mem (mem_powerset_self s), card_powerset]

/-- Membership in the set of proper subsets. -/
theorem mem_proper {c s : Finset ℕ} : c ∈ s.powerset.erase s ↔ c ≠ s ∧ c ⊆ s := by
  rw [mem_erase, mem_powerset]

/-- Positive fibres, one direction: `Y_C ≤ 3 (2^{|C|} - 1) · |posFib U B (P j)|`.  The map
`A ↦ ((A ∩ C, A ∩ P j), (A ∪ C) ∖ P j)` is injective from the defects of `C` into
(proper traces on `C`) × (proper traces on `P j`) × (positive fibres in direction `P j`). -/
theorem pos_one {U : Finset ℕ} {B : Fam} {C : Finset ℕ} {t : ℕ} {P : ℕ → Finset ℕ}
    (h : PairSetting U B C t P) {j : ℕ} (hj : j < t) :
    ycount B C ≤ 3 * (2 ^ C.card - 1) * (posFib U B (P j)).card := by
  have hP2 : ((P j).powerset.erase (P j)).card = 3 := by
    rw [card_proper, h.hPcard j hj]
    rfl
  have htarget :
      (((C.powerset.erase C) ×ˢ ((P j).powerset.erase (P j))) ×ˢ posFib U B (P j)).card
        = 3 * (2 ^ C.card - 1) * (posFib U B (P j)).card := by
    rw [card_product, card_product, hP2, card_proper, Nat.mul_comm (2 ^ C.card - 1) 3]
  rw [← htarget]
  unfold ycount
  apply card_le_card_of_injOn (fun A => ((A ∩ C, A ∩ P j), (A ∪ C) \ P j))
  · intro A hA
    have hA' : A ∈ B.filter (fun A => A ∪ C ∉ B) := mem_coe.mp hA
    rw [mem_filter] at hA'
    obtain ⟨hAB, hACB⟩ := hA'
    have hPC : Disjoint (P j) C := h.hPC j hj
    have hAU : A ⊆ U := h.memU A hAB
    have hstab : A ∪ (C ∪ P j) ∈ B := h.stab A hAB j hj
    rw [mem_coe, mem_product, mem_product, mem_proper, mem_proper]
    refine ⟨⟨⟨?_, inter_subset_right⟩, ⟨?_, inter_subset_right⟩⟩, ?_⟩
    · -- the trace on `C` is proper, else `A ∪ C = A ∈ B`
      intro hc
      have hCA : C ⊆ A := inter_eq_right.mp hc
      apply hACB
      rw [union_eq_left.mpr hCA]
      exact hAB
    · -- the trace on `P j` is proper, else stability fills the defect
      intro hp
      have hPA : P j ⊆ A := inter_eq_right.mp hp
      apply hACB
      have he : A ∪ (C ∪ P j) = A ∪ C := by
        rw [union_comm C (P j), ← union_assoc, union_eq_left.mpr hPA]
      rw [← he]
      exact hstab
    · -- `(A ∪ C) ∖ P j` is a positive fibre in direction `P j`
      unfold posFib
      rw [mem_filter, mem_powerset]
      refine ⟨sdiff_subset_sdiff (union_subset hAU h.hC) (le_refl _), ?_, ?_⟩
      · -- its empty endpoint is absent: union with `A` would give `A ∪ C`
        intro hZ
        apply hACB
        have hCZ : C ⊆ (A ∪ C) \ P j := subset_sdiff.mpr ⟨subset_union_right, hPC.symm⟩
        have he : A ∪ ((A ∪ C) \ P j) = A ∪ C :=
          subset_antisymm (union_subset subset_union_left sdiff_subset)
            (union_subset subset_union_left (hCZ.trans subset_union_right))
        rw [← he]
        exact h.uc A hAB _ hZ
      · -- its full endpoint is present by stability
        rw [sdiff_union_self_eq_union, union_assoc]
        exact hstab
  · intro A _ A' _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨h1, h2⟩, h3⟩ := heq
    ext x
    have e1 := Finset.ext_iff.mp h1 x
    have e2 := Finset.ext_iff.mp h2 x
    have e3 := Finset.ext_iff.mp h3 x
    simp only [mem_inter, mem_union, mem_sdiff] at e1 e2 e3
    by_cases hxC : x ∈ C
    · exact ⟨fun hx => (e1.mp ⟨hx, hxC⟩).1, fun hx => (e1.mpr ⟨hx, hxC⟩).1⟩
    by_cases hxP : x ∈ P j
    · exact ⟨fun hx => (e2.mp ⟨hx, hxP⟩).1, fun hx => (e2.mpr ⟨hx, hxP⟩).1⟩
    exact ⟨fun hx => (e3.mp ⟨Or.inl hx, hxP⟩).1.resolve_right hxC,
      fun hx => (e3.mpr ⟨Or.inl hx, hxP⟩).1.resolve_right hxC⟩

end PairFibres

/-- Negative fibres: `N⁻ ≤ (2^{|C|} - 1) · X_C` (paper (3.2)). -/
theorem neg_fibre_bound {U : Finset ℕ} {B : Fam} {C : Finset ℕ} {t : ℕ} {P : ℕ → Finset ℕ}
    (h : PairSetting U B C t P) :
    ∑ j ∈ range t, (negFib U B (P j)).card ≤ (2 ^ C.card - 1) * xcount U B C := by
  rw [← card_sigma, ← PairFibres.card_proper, xcount, ← card_product]
  apply card_le_card_of_injOn
    (fun p : (Σ _ : ℕ, Finset ℕ) => (p.2 ∩ C, (p.2 \ C) ∪ P p.1))
  · rintro ⟨j, A⟩ hp
    have hp' := mem_coe.mp hp
    rw [mem_sigma, mem_range] at hp'
    obtain ⟨hj, hA⟩ := hp'
    unfold negFib at hA
    rw [mem_filter, mem_powerset] at hA
    obtain ⟨hAsub, hAB, hAPB⟩ := hA
    have hPC : Disjoint (P j) C := h.hPC j hj
    have hstab : A ∪ (C ∪ P j) ∈ B := h.stab A hAB j hj
    rw [mem_coe, mem_product, PairFibres.mem_proper, mem_filter, mem_powerset]
    refine ⟨⟨?_, inter_subset_right⟩, ?_, ?_, ?_⟩
    · -- the trace on `C` is proper, else stability gives `A ∪ P j ∈ B`
      intro hc
      have hCA : C ⊆ A := inter_eq_right.mp hc
      apply hAPB
      have he : A ∪ (C ∪ P j) = A ∪ P j := by
        rw [← union_assoc, union_eq_left.mpr hCA]
      rw [← he]
      exact hstab
    · -- `Z = (A ∖ C) ∪ P j ⊆ U ∖ C`
      intro x hx
      rw [mem_union] at hx
      rw [mem_sdiff]
      rcases hx with hx | hx
      · rw [mem_sdiff] at hx
        exact ⟨(mem_sdiff.mp (hAsub hx.1)).1, hx.2⟩
      · exact ⟨h.hPU j hj hx, disjoint_left.mp hPC hx⟩
    · -- `Z ∉ B`, else `A ∪ Z = A ∪ P j ∈ B`
      intro hZ
      apply hAPB
      have he : A ∪ ((A \ C) ∪ P j) = A ∪ P j := by
        rw [← union_assoc, union_eq_left.mpr sdiff_subset]
      rw [← he]
      exact h.uc A hAB _ hZ
    · -- `Z ∪ C = A ∪ (C ∪ P j) ∈ B`
      have he : (A \ C) ∪ P j ∪ C = A ∪ (C ∪ P j) := by
        rw [union_assoc, union_comm (P j) C, ← union_assoc, sdiff_union_self_eq_union,
          union_assoc]
      rw [he]
      exact hstab
  · rintro ⟨j, A⟩ hp ⟨j', A'⟩ hp' heq
    have hp1 := mem_coe.mp hp
    have hp2 := mem_coe.mp hp'
    rw [mem_sigma, mem_range] at hp1 hp2
    obtain ⟨hj, hA⟩ := hp1
    obtain ⟨hj', hA'⟩ := hp2
    unfold negFib at hA hA'
    rw [mem_filter, mem_powerset] at hA hA'
    obtain ⟨hAsub, hAB, hAPB⟩ := hA
    obtain ⟨hAsub', hAB', -⟩ := hA'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hc, hZ⟩ := heq
    -- the two directions coincide: otherwise `A ∪ A' = A ∪ P j`, contradicting union-closure
    have hjj : j = j' := by
      by_contra hne
      have hdisj : Disjoint (P j) (P j') := h.hPP j hj j' hj' hne
      apply hAPB
      have he : A ∪ A' = A ∪ P j := by
        ext x
        have e1 := Finset.ext_iff.mp hc x
        have e2 := Finset.ext_iff.mp hZ x
        simp only [mem_inter, mem_union, mem_sdiff] at e1 e2 ⊢
        constructor
        · rintro (hx | hx)
          · exact Or.inl hx
          · by_cases hxC : x ∈ C
            · exact Or.inl (e1.mpr ⟨hx, hxC⟩).1
            · rcases e2.mpr (Or.inl ⟨hx, hxC⟩) with h' | h'
              · exact Or.inl h'.1
              · exact Or.inr h'
        · rintro (hx | hx)
          · exact Or.inl hx
          · right
            rcases e2.mp (Or.inr hx) with h' | h'
            · exact h'.1
            · exact absurd h' (disjoint_left.mp hdisj hx)
      rw [← he]
      exact h.uc A hAB A' hAB'
    subst hjj
    -- and then the sources coincide: `A = (Z ∖ P j) ∪ c`
    have hAA : A = A' := by
      ext x
      have e1 := Finset.ext_iff.mp hc x
      have e2 := Finset.ext_iff.mp hZ x
      simp only [mem_inter, mem_union, mem_sdiff] at e1 e2
      by_cases hxC : x ∈ C
      · exact ⟨fun hx => (e1.mp ⟨hx, hxC⟩).1, fun hx => (e1.mpr ⟨hx, hxC⟩).1⟩
      constructor
      · intro hx
        rcases e2.mp (Or.inl ⟨hx, hxC⟩) with h' | h'
        · exact h'.1
        · exact absurd h' (mem_sdiff.mp (hAsub hx)).2
      · intro hx
        rcases e2.mpr (Or.inl ⟨hx, hxC⟩) with h' | h'
        · exact h'.1
        · exact absurd h' (mem_sdiff.mp (hAsub' hx)).2
    subst hAA
    rfl

/-- Positive fibres: `t · Y_C ≤ 3 (2^{|C|} - 1) · N⁺` (paper (3.3)). -/
theorem pos_fibre_bound {U : Finset ℕ} {B : Fam} {C : Finset ℕ} {t : ℕ} {P : ℕ → Finset ℕ}
    (h : PairSetting U B C t P) :
    t * ycount B C ≤ 3 * (2 ^ C.card - 1) * ∑ j ∈ range t, (posFib U B (P j)).card := by
  calc t * ycount B C = ∑ _j ∈ range t, ycount B C := by
        rw [sum_const_nat (fun _ _ => rfl), card_range]
    _ ≤ ∑ j ∈ range t, 3 * (2 ^ C.card - 1) * (posFib U B (P j)).card :=
        sum_le_sum fun j hj => PairFibres.pos_one h (mem_range.mp hj)
    _ = 3 * (2 ^ C.card - 1) * ∑ j ∈ range t, (posFib U B (P j)).card := by
        rw [mul_sum]

end Results.FcMorrisV2
