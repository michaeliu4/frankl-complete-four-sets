import Results.FcMorrisV2.Solution.PairFibres

/-!
# Solution/PairBoundary: the new-boundary inequality of the robust pair lifting (paper (3.4))
-/

namespace Results.FcMorrisV2

open Finset

namespace PairBoundary

/-- Per-direction form of the new-boundary inequality (paper (3.4)): for a set `Q` disjoint from
`C ⊆ U`, `x_{C ∪ Q} ≤ x_C + |posFib U B Q|`.  A boundary source `A` of `C ∪ Q` is either a boundary
source of `C` (when `A ∪ C ∈ B`) or else `A ∪ C` is the empty endpoint of a positive `Q`-fibre;
the map `A ↦ A ∪ C` is injective on sets disjoint from `C`. -/
theorem xcount_union_le {U : Finset ℕ} {B : Fam} {C Q : Finset ℕ}
    (hC : C ⊆ U) (hQC : Disjoint Q C) :
    xcount U B (C ∪ Q) ≤ xcount U B C + (posFib U B Q).card := by
  classical
  unfold xcount
  rw [← card_filter_add_card_filter_not (s := ((U \ (C ∪ Q)).powerset.filter
      fun A => A ∉ B ∧ A ∪ (C ∪ Q) ∈ B)) (fun A => A ∪ C ∈ B)]
  apply add_le_add
  · -- first case: `A ∪ C ∈ B`, so `A` is a boundary source of `C`
    apply card_le_card
    intro A hA
    simp only [mem_filter, mem_powerset] at hA ⊢
    obtain ⟨⟨hAU, hAB, -⟩, hAC⟩ := hA
    exact ⟨hAU.trans (sdiff_subset_sdiff (subset_refl U) subset_union_left), hAB, hAC⟩
  · -- second case: `A ∪ C ∉ B`, so `A ∪ C` is the empty endpoint of a positive `Q`-fibre
    apply card_le_card_of_injOn (fun A => A ∪ C)
    · intro A hA
      simp only [coe_filter, mem_filter, mem_powerset, Set.mem_setOf_eq] at hA
      unfold posFib
      simp only [coe_filter, mem_powerset, Set.mem_setOf_eq]
      obtain ⟨⟨hAU, -, hACQ⟩, hAC⟩ := hA
      refine ⟨?_, hAC, ?_⟩
      · intro x hx
        rw [mem_union] at hx
        rw [mem_sdiff]
        rcases hx with hx | hx
        · have hx' := hAU hx
          rw [mem_sdiff, mem_union] at hx'
          exact ⟨hx'.1, fun hq => hx'.2 (Or.inr hq)⟩
        · exact ⟨hC hx, fun hq => disjoint_left.mp hQC hq hx⟩
      · rwa [union_assoc]
    · intro A hA A' hA' hEq
      simp only [coe_filter, mem_filter, mem_powerset, Set.mem_setOf_eq] at hA hA'
      have hdisj : ∀ {A : Finset ℕ}, A ⊆ U \ (C ∪ Q) → Disjoint A C := by
        intro A hAU
        rw [disjoint_left]
        intro x hxA hxC
        have hx' := hAU hxA
        rw [mem_sdiff, mem_union] at hx'
        exact hx'.2 (Or.inl hxC)
      have hEq' : A ∪ C = A' ∪ C := hEq
      calc A = (A ∪ C) \ C := (union_sdiff_cancel_right (hdisj hA.1.1)).symm
        _ = (A' ∪ C) \ C := by rw [hEq']
        _ = A' := union_sdiff_cancel_right (hdisj hA'.1.1)

end PairBoundary

/-- New boundaries: `∑_j x_{C ∪ P_j} ≤ t · X_C + N⁺` (paper (3.4)). -/
theorem new_boundary_bound {U : Finset ℕ} {B : Fam} {C : Finset ℕ} {t : ℕ}
    {P : ℕ → Finset ℕ} (h : PairSetting U B C t P) :
    ∑ j ∈ range t, xcount U B (C ∪ P j) ≤
      t * xcount U B C + ∑ j ∈ range t, (posFib U B (P j)).card := by
  calc ∑ j ∈ range t, xcount U B (C ∪ P j)
      ≤ ∑ j ∈ range t, (xcount U B C + (posFib U B (P j)).card) := by
        apply sum_le_sum
        intro j hj
        exact PairBoundary.xcount_union_le h.hC (h.hPC j (mem_range.mp hj))
    _ = t * xcount U B C + ∑ j ∈ range t, (posFib U B (P j)).card := by
        rw [sum_add_distrib, sum_const, card_range, Nat.nsmul_eq_mul]

end Results.FcMorrisV2
