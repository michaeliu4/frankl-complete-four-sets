import Results.FcMorrisV2.Solution.PairBoundary

/-!
# Solution/Lifting: robust pair-petal lifting (paper Theorem 3.1, uniform branch number `t`)
-/

namespace Results.FcMorrisV2

open Finset

/-- The lifted configuration `{C ∪ P C j : C ∈ G, j < t}`. -/
def lift (G : Fam) (t : ℕ) (P : Finset ℕ → ℕ → Finset ℕ) : Fam :=
  (G ×ˢ range t).image fun p => p.1 ∪ P p.1 p.2

/-- Weights of the lifted certificate: `lam · w` on old points `V`, weight `1` elsewhere. -/
def liftW (lam : ℕ) (w : ℕ → ℚ) (V : Finset ℕ) (u : ℕ) : ℚ :=
  if u ∈ V then (lam : ℚ) * w u else 1

namespace Lifting

/-! ### Slicing a family on `V ⊔ R` by its exact trace on `R` -/

/-- Generic slicing identity: a sum over a filtered powerset of a disjoint union `V ∪ R`,
regrouped by the exact trace `S ⊆ R`. -/
theorem slice_sum {β : Type*} [AddCommMonoid β] {V R : Finset ℕ} (hVR : Disjoint V R)
    (Φ : Finset ℕ → Prop) [DecidablePred Φ] (f : Finset ℕ → β) :
    ∑ S ∈ R.powerset, ∑ D ∈ V.powerset.filter (fun D => Φ (D ∪ S)), f (D ∪ S) =
      ∑ X ∈ (V ∪ R).powerset.filter Φ, f X := by
  rw [← sum_fiberwise_of_maps_to (s := (V ∪ R).powerset.filter Φ) (t := R.powerset)
    (g := fun X => X ∩ R) (fun X _ => mem_powerset.mpr inter_subset_right)]
  refine sum_congr rfl fun S hS => ?_
  have hSR : S ⊆ R := mem_powerset.mp hS
  have hSV : S ∩ V = ∅ := disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_left hSR hVR.symm)
  refine sum_nbij' (fun D => D ∪ S) (fun X => X ∩ V) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    simp only [mem_filter, mem_powerset] at hD ⊢
    have hDR : D ∩ R = ∅ := disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_left hD.1 hVR)
    rw [union_inter_distrib_right, hDR, empty_union, inter_eq_left.mpr hSR]
    exact ⟨⟨union_subset_union hD.1 hSR, hD.2⟩, rfl⟩
  · intro X hX
    simp only [mem_filter, mem_powerset] at hX ⊢
    rw [← hX.2, ← inter_union_distrib_left, inter_eq_left.mpr hX.1.1]
    exact ⟨inter_subset_right, hX.1.2⟩
  · intro D hD
    simp only [mem_filter, mem_powerset] at hD
    rw [union_inter_distrib_right, inter_eq_left.mpr hD.1, hSV, union_empty]
  · intro X hX
    simp only [mem_filter, mem_powerset] at hX
    rw [← hX.2, ← inter_union_distrib_left, inter_eq_left.mpr hX.1.1]
  · intro D _
    rfl

/-- Cardinality version of `slice_sum`. -/
theorem slice_card {V R : Finset ℕ} (hVR : Disjoint V R) (Φ : Finset ℕ → Prop)
    [DecidablePred Φ] :
    ∑ S ∈ R.powerset, (V.powerset.filter (fun D => Φ (D ∪ S))).card =
      ((V ∪ R).powerset.filter Φ).card := by
  simpa only [← card_eq_sum_ones] using slice_sum (β := ℕ) hVR Φ (fun _ => 1)

/-- The slice of `B` at the exact new-point trace `S`: `K_S = {D ⊆ V : D ∪ S ∈ B}`. -/
def slice (V : Finset ℕ) (B : Fam) (S : Finset ℕ) : Fam :=
  V.powerset.filter fun D => D ∪ S ∈ B

theorem slice_sub {V : Finset ℕ} {B : Fam} {S : Finset ℕ} : ∀ X ∈ slice V B S, X ⊆ V :=
  fun _ hX => mem_powerset.mp (mem_filter.mp hX).1

theorem slice_uc {V : Finset ℕ} {B : Fam} {S : Finset ℕ} (hB : UnionClosed B) :
    UnionClosed (slice V B S) := by
  intro X hX Y hY
  simp only [slice, mem_filter, mem_powerset] at hX hY ⊢
  refine ⟨union_subset hX.1 hY.1, ?_⟩
  rw [union_union_distrib_right]
  exact hB _ hX.2 _ hY.2

/-- The trace on `V` of `D ∪ S` with `D ⊆ V`, `S ⊆ R`. -/
theorem trace_inter {V R D S : Finset ℕ} (hVR : Disjoint V R) (hD : D ⊆ V) (hS : S ⊆ R) :
    (D ∪ S) ∩ V = D := by
  rw [union_inter_distrib_right, inter_eq_left.mpr hD,
    disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_left hS hVR.symm), union_empty]

/-- Slicing the boundary count `x_C`. -/
theorem xcount_slice {V R : Finset ℕ} (hVR : Disjoint V R) {B : Fam} {C : Finset ℕ}
    (hCV : C ⊆ V) :
    ∑ S ∈ R.powerset, xcount V (slice V B S) C = xcount (V ∪ R) B C := by
  have hdisj : Disjoint (V \ C) R := disjoint_of_subset_left sdiff_subset hVR
  have hUC : (V ∪ R) \ C = (V \ C) ∪ R := by
    rw [union_sdiff_distrib, sdiff_eq_self_of_disjoint (disjoint_of_subset_left hCV hVR).symm]
  unfold xcount
  rw [hUC, ← slice_card hdisj (fun A => A ∉ B ∧ A ∪ C ∈ B)]
  refine sum_congr rfl fun S _ => ?_
  congr 1
  refine filter_congr fun D hD => ?_
  rw [mem_powerset] at hD
  have hDV : D ⊆ V := hD.trans sdiff_subset
  simp only [slice, mem_filter, mem_powerset]
  rw [union_right_comm D C S]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨fun h => h1 ⟨hDV, h⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 h.2, union_subset hDV hCV, h2⟩

/-- Slicing the defect count `y_C`. -/
theorem ycount_slice {V R : Finset ℕ} (hVR : Disjoint V R) {B : Fam} (hB : ∀ X ∈ B, X ⊆ V ∪ R)
    {C : Finset ℕ} (hCV : C ⊆ V) :
    ∑ S ∈ R.powerset, ycount (slice V B S) C = ycount B C := by
  have hY : ycount B C = ((V ∪ R).powerset.filter fun A => A ∈ B ∧ A ∪ C ∉ B).card := by
    unfold ycount
    congr 1
    ext A
    simp only [mem_filter, mem_powerset]
    constructor
    · rintro ⟨hA, h⟩
      exact ⟨hB A hA, hA, h⟩
    · rintro ⟨-, hA, h⟩
      exact ⟨hA, h⟩
  rw [hY, ← slice_card hVR (fun A => A ∈ B ∧ A ∪ C ∉ B)]
  refine sum_congr rfl fun S _ => ?_
  unfold ycount slice
  rw [filter_filter]
  congr 1
  refine filter_congr fun D hD => ?_
  rw [mem_powerset] at hD
  simp only [mem_filter, mem_powerset]
  rw [union_right_comm D C S]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 ⟨union_subset hD hCV, h⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 h.2⟩

/-! ### The pair identity -/

/-- Local share on a pair: `|X ∩ P| - 1 = [P ⊆ X] - [X ∩ P = ∅]` when `|P| = 2`. -/
theorem pair_local {P : Finset ℕ} (hP : P.card = 2) (X : Finset ℕ) :
    ((X ∩ P).card : ℚ) - 1 = (if P ⊆ X then 1 else 0) - (if Disjoint X P then 1 else 0) := by
  have hle : (X ∩ P).card ≤ 2 := (card_le_card inter_subset_right).trans hP.le
  rcases (show (X ∩ P).card = 0 ∨ (X ∩ P).card = 1 ∨ (X ∩ P).card = 2 by omega) with h | h | h
  · have hd : Disjoint X P := disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp h)
    have hs : ¬ P ⊆ X := fun hs => by
      rw [inter_eq_right.mpr hs, hP] at h
      exact absurd h (by norm_num)
    rw [if_neg hs, if_pos hd, h]
    norm_num
  · have hd : ¬ Disjoint X P := fun hd => by
      rw [disjoint_iff_inter_eq_empty.mp hd, card_empty] at h
      exact absurd h (by norm_num)
    have hs : ¬ P ⊆ X := fun hs => by
      rw [inter_eq_right.mpr hs, hP] at h
      exact absurd h (by norm_num)
    rw [if_neg hs, if_neg hd, h]
    norm_num
  · have hs : P ⊆ X :=
      inter_eq_right.mp (eq_of_subset_of_card_le inter_subset_right (by rw [hP, h]))
    have hd : ¬ Disjoint X P := fun hd => by
      rw [disjoint_iff_inter_eq_empty.mp hd, card_empty] at h
      exact absurd h (by norm_num)
    rw [if_pos hs, if_neg hd, h]
    norm_num

/-- Pair identity: `∑_{X ∈ B} (|X ∩ P| - 1) = |posFib| - |negFib|` for a pair `P`. -/
theorem pair_identity {U : Finset ℕ} {B : Fam} (hB : ∀ X ∈ B, X ⊆ U) {P : Finset ℕ}
    (hP : P.card = 2) :
    ∑ X ∈ B, (((X ∩ P).card : ℚ) - 1) = ((posFib U B P).card : ℚ) - (negFib U B P).card := by
  rw [sum_congr rfl fun X _ => pair_local hP X, sum_sub_distrib, sum_boole, sum_boole]
  have h1 : (B.filter fun X => P ⊆ X).card =
      ((U \ P).powerset.filter fun A => A ∪ P ∈ B).card := by
    refine card_nbij' (fun X => X \ P) (fun A => A ∪ P) ?_ ?_ ?_ ?_
    · intro X hX
      simp only [coe_filter, Set.mem_setOf_eq] at hX
      simp only [coe_filter, Set.mem_setOf_eq, mem_powerset, sdiff_union_of_subset hX.2]
      exact ⟨sdiff_subset_sdiff (hB X hX.1) (subset_refl P), hX.1⟩
    · intro A hA
      simp only [coe_filter, Set.mem_setOf_eq] at hA
      simp only [coe_filter, Set.mem_setOf_eq]
      exact ⟨hA.2, subset_union_right⟩
    · intro X hX
      simp only [coe_filter, Set.mem_setOf_eq] at hX
      exact sdiff_union_of_subset hX.2
    · intro A hA
      simp only [coe_filter, Set.mem_setOf_eq, mem_powerset] at hA
      exact union_sdiff_cancel_right (disjoint_of_subset_left hA.1 sdiff_disjoint)
  have h2 : (B.filter fun X => Disjoint X P) = ((U \ P).powerset.filter fun A => A ∈ B) := by
    ext X
    rw [mem_filter, mem_filter, mem_powerset, subset_sdiff]
    exact ⟨fun h => ⟨⟨hB X h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  have h3 : ((posFib U B P).card : ℚ) - (negFib U B P).card =
      (((U \ P).powerset.filter fun A => A ∪ P ∈ B).card : ℚ) -
        ((U \ P).powerset.filter fun A => A ∈ B).card := by
    unfold posFib negFib
    rw [natCast_card_filter, natCast_card_filter, natCast_card_filter, natCast_card_filter,
      ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun A _ => ?_
    by_cases hA : A ∈ B <;> by_cases hAP : A ∪ P ∈ B <;>
      simp only [hA, hAP, not_true_eq_false, not_false_eq_true, and_true, and_false, and_self,
        ↓reduceIte, sub_self, zero_sub, sub_zero]
  rw [h1, h2, h3]

/-! ### The weighted share of the lifted family -/

/-- Splitting the lifted weight of a set `X ⊆ V ∪ R`. -/
theorem sum_liftW (lam : ℕ) (w : ℕ → ℚ) {V R X : Finset ℕ} (hVR : Disjoint V R)
    (hX : X ⊆ V ∪ R) :
    ∑ u ∈ X, liftW lam w V u = (lam : ℚ) * ∑ u ∈ X ∩ V, w u + ((X ∩ R).card : ℚ) := by
  have hXR : X \ V = X ∩ R := by
    ext x
    rw [mem_sdiff, mem_inter]
    constructor
    · rintro ⟨hxX, hxV⟩
      exact ⟨hxX, (mem_union.mp (hX hxX)).resolve_left hxV⟩
    · rintro ⟨hxX, hxR⟩
      exact ⟨hxX, fun hxV => disjoint_left.mp hVR hxV hxR⟩
  rw [← sum_filter_add_sum_filter_not X (fun u => u ∈ V), filter_mem_eq_inter,
    filter_notMem_eq_sdiff, hXR, mul_sum, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  congr 1
  · exact sum_congr rfl fun u hu => if_pos (mem_inter.mp hu).2
  · exact sum_congr rfl fun u hu => if_neg fun hV => disjoint_left.mp hVR hV (mem_inter.mp hu).2

/-- Cardinality of a trace on a pairwise disjoint union. -/
theorem card_inter_biUnion {I : Finset (Finset ℕ × ℕ)} {Q : Finset ℕ × ℕ → Finset ℕ}
    (hQ : (I : Set (Finset ℕ × ℕ)).PairwiseDisjoint Q) (X : Finset ℕ) :
    (X ∩ I.biUnion Q).card = ∑ p ∈ I, (X ∩ Q p).card := by
  rw [inter_biUnion]
  refine card_biUnion ?_
  intro p hp q hq hpq
  exact Disjoint.mono inter_subset_right inter_subset_right (hQ hp hq hpq)

/-- The share identity of the lifting (old-point slices plus pair fibres). -/
theorem share_lift {V U : Finset ℕ} {I : Finset (Finset ℕ × ℕ)} {Q : Finset ℕ × ℕ → Finset ℕ}
    (hVR : Disjoint V (I.biUnion Q)) (hU : U = V ∪ I.biUnion Q)
    (hQ : (I : Set (Finset ℕ × ℕ)).PairwiseDisjoint Q) (hQc : ∀ p ∈ I, (Q p).card = 2)
    (lam : ℕ) (w : ℕ → ℚ) {B : Fam} (hB : ∀ X ∈ B, X ⊆ U) :
    share (liftW lam w V) U B =
      lam * ∑ S ∈ (I.biUnion Q).powerset, share w V (slice V B S) +
        ∑ p ∈ I, (((posFib U B (Q p)).card : ℚ) - (negFib U B (Q p)).card) := by
  have hBR : ∀ X ∈ B, X ⊆ V ∪ I.biUnion Q := fun X hX => hU ▸ hB X hX
  have hRcard : ((I.biUnion Q).card : ℚ) = 2 * I.card := by
    rw [card_biUnion hQ, sum_congr rfl hQc, sum_const, Nat.nsmul_eq_mul]
    push_cast
    ring
  have hW : ∑ u ∈ U, liftW lam w V u = lam * ∑ u ∈ V, w u + 2 * I.card := by
    rw [sum_liftW lam w hVR (by rw [hU]), hU, union_inter_cancel_left, union_inter_cancel_right,
      hRcard]
  have hpt : ∀ X ∈ B, ∑ u ∈ X, liftW lam w V u - (∑ u ∈ U, liftW lam w V u) / 2 =
      lam * (∑ u ∈ X ∩ V, w u - (∑ u ∈ V, w u) / 2) +
        ∑ p ∈ I, (((X ∩ Q p).card : ℚ) - 1) := by
    intro X hX
    rw [sum_liftW lam w hVR (hBR X hX), hW, card_inter_biUnion hQ, Nat.cast_sum,
      sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
    ring
  have hslice : ∑ X ∈ B, (∑ u ∈ X ∩ V, w u - (∑ u ∈ V, w u) / 2) =
      ∑ S ∈ (I.biUnion Q).powerset, share w V (slice V B S) := by
    have hBf : (V ∪ I.biUnion Q).powerset.filter (· ∈ B) = B := by
      rw [filter_mem_eq_inter, inter_eq_right]
      intro X hX
      exact mem_powerset.mpr (hBR X hX)
    calc ∑ X ∈ B, (∑ u ∈ X ∩ V, w u - (∑ u ∈ V, w u) / 2)
        = ∑ X ∈ (V ∪ I.biUnion Q).powerset.filter (· ∈ B),
            (∑ u ∈ X ∩ V, w u - (∑ u ∈ V, w u) / 2) := by rw [hBf]
      _ = ∑ S ∈ (I.biUnion Q).powerset, ∑ D ∈ V.powerset.filter (fun D => D ∪ S ∈ B),
            (∑ u ∈ (D ∪ S) ∩ V, w u - (∑ u ∈ V, w u) / 2) := (slice_sum hVR (· ∈ B) _).symm
      _ = ∑ S ∈ (I.biUnion Q).powerset, share w V (slice V B S) := by
          refine sum_congr rfl fun S hS => ?_
          refine sum_congr rfl fun D hD => ?_
          rw [slice, mem_filter, mem_powerset] at hD
          rw [trace_inter hVR hD.1 (mem_powerset.mp hS)]
  calc share (liftW lam w V) U B
      = ∑ X ∈ B, ((lam : ℚ) * (∑ u ∈ X ∩ V, w u - (∑ u ∈ V, w u) / 2) +
          ∑ p ∈ I, (((X ∩ Q p).card : ℚ) - 1)) := sum_congr rfl hpt
    _ = lam * ∑ X ∈ B, (∑ u ∈ X ∩ V, w u - (∑ u ∈ V, w u) / 2) +
          ∑ p ∈ I, ∑ X ∈ B, (((X ∩ Q p).card : ℚ) - 1) := by
        rw [sum_add_distrib, ← mul_sum, sum_comm (s := B)]
    _ = _ := by
        rw [hslice]
        congr 1
        exact sum_congr rfl fun p hp => pair_identity hB (hQc p hp)

/-! ### The finite-defect bound summed over all slices -/

theorem subset_supp {G : Fam} {C : Finset ℕ} (hC : C ∈ G) : C ⊆ supp G :=
  subset_biUnion_of_mem id hC

theorem defect_sum {G : Fam} {w : ℕ → ℚ} {δ : ℚ} (hG : RobustFC G w δ) {R U : Finset ℕ}
    (hVR : Disjoint (supp G) R) (hU : U = supp G ∪ R) {B : Fam} (hB : ∀ X ∈ B, X ⊆ U)
    (huc : UnionClosed B) :
    δ * ∑ C ∈ G, (xcount U B C : ℚ) -
      (2 ^ (supp G).card * ((G.card : ℚ) * δ + (∑ u ∈ supp G, w u) / 2)) *
        ∑ C ∈ G, (ycount B C : ℚ) ≤
      ∑ S ∈ R.powerset, share w (supp G) (slice (supp G) B S) := by
  have hBR : ∀ X ∈ B, X ⊆ supp G ∪ R := fun X hX => hU ▸ hB X hX
  have hx : ∀ C ∈ G, (xcount U B C : ℚ) =
      ∑ S ∈ R.powerset, (xcount (supp G) (slice (supp G) B S) C : ℚ) := by
    intro C hC
    rw [hU, ← xcount_slice hVR (subset_supp hC), Nat.cast_sum]
  have hy : ∀ C ∈ G, (ycount B C : ℚ) =
      ∑ S ∈ R.powerset, (ycount (slice (supp G) B S) C : ℚ) := by
    intro C hC
    rw [← ycount_slice hVR hBR (subset_supp hC), Nat.cast_sum]
  rw [sum_congr rfl hx, sum_congr rfl hy, sum_comm (s := G), sum_comm (s := G),
    mul_sum R.powerset, mul_sum R.powerset, ← sum_sub_distrib]
  exact sum_le_sum fun S _ => defect_bound hG _ ⟨slice_sub, slice_uc huc⟩

/-! ### Combinatorics of the lifted configuration -/

theorem mem_lift {G : Fam} {t : ℕ} {P : Finset ℕ → ℕ → Finset ℕ} {C : Finset ℕ} {j : ℕ}
    (hC : C ∈ G) (hj : j < t) : C ∪ P C j ∈ lift G t P :=
  mem_image.mpr ⟨(C, j), mem_product.mpr ⟨hC, mem_range.mpr hj⟩, rfl⟩

theorem supp_lift (G : Fam) {t : ℕ} (ht : 0 < t) (P : Finset ℕ → ℕ → Finset ℕ) :
    supp (lift G t P) = supp G ∪ (G ×ˢ range t).biUnion fun p => P p.1 p.2 := by
  ext x
  constructor
  · intro hx
    obtain ⟨E, hE, hxE⟩ := mem_biUnion.mp hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hE
    rcases mem_union.mp hxE with h | h
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p.1, (mem_product.mp hp).1, h⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p, hp, h⟩)
  · intro hx
    rcases mem_union.mp hx with h | h
    · obtain ⟨C, hC, hxC⟩ := mem_biUnion.mp h
      exact mem_biUnion.mpr ⟨_, mem_lift hC ht, mem_union_left _ hxC⟩
    · obtain ⟨p, hp, hxp⟩ := mem_biUnion.mp h
      exact mem_biUnion.mpr ⟨_, mem_image.mpr ⟨p, hp, rfl⟩, mem_union_right _ hxp⟩

theorem disj_VR {G : Fam} {t : ℕ} {P : Finset ℕ → ℕ → Finset ℕ}
    (hPV : ∀ C ∈ G, ∀ j < t, Disjoint (P C j) (supp G)) :
    Disjoint (supp G) ((G ×ˢ range t).biUnion fun p => P p.1 p.2) := by
  rw [disjoint_biUnion_right]
  intro p hp
  rw [mem_product, mem_range] at hp
  exact (hPV p.1 hp.1 p.2 hp.2).symm

theorem pairwise_disj {G : Fam} {t : ℕ} {P : Finset ℕ → ℕ → Finset ℕ}
    (hPP : ∀ C ∈ G, ∀ j < t, ∀ C' ∈ G, ∀ j' < t, (C ≠ C' ∨ j ≠ j') →
      Disjoint (P C j) (P C' j')) :
    ((G ×ˢ range t : Finset (Finset ℕ × ℕ)) : Set (Finset ℕ × ℕ)).PairwiseDisjoint
      fun p => P p.1 p.2 := by
  intro p hp q hq hpq
  rw [mem_coe, mem_product, mem_range] at hp hq
  have hne : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
    by_cases h1 : p.1 = q.1
    · exact Or.inr fun h2 => hpq (Prod.ext h1 h2)
    · exact Or.inl h1
  exact hPP p.1 hp.1 p.2 hp.2 q.1 hq.1 q.2 hq.2 hne

theorem lift_injOn {G : Fam} {t : ℕ} {P : Finset ℕ → ℕ → Finset ℕ}
    (hPc : ∀ C ∈ G, ∀ j < t, (P C j).card = 2)
    (hPV : ∀ C ∈ G, ∀ j < t, Disjoint (P C j) (supp G))
    (hPP : ∀ C ∈ G, ∀ j < t, ∀ C' ∈ G, ∀ j' < t, (C ≠ C' ∨ j ≠ j') →
      Disjoint (P C j) (P C' j')) :
    Set.InjOn (fun p : Finset ℕ × ℕ => p.1 ∪ P p.1 p.2) ↑(G ×ˢ range t) := by
  rintro ⟨C, j⟩ hp ⟨C', j'⟩ hq hpq
  simp only [mem_coe, mem_product, mem_range] at hp hq
  simp only at hpq
  have key : ∀ D ∈ G, ∀ k < t, (D ∪ P D k) ∩ supp G = D := fun D hD k hk => by
    rw [union_inter_distrib_right, inter_eq_left.mpr (subset_supp hD),
      disjoint_iff_inter_eq_empty.mp (hPV D hD k hk), union_empty]
  have hCC : C = C' := by
    calc C = (C ∪ P C j) ∩ supp G := (key C hp.1 j hp.2).symm
      _ = (C' ∪ P C' j') ∩ supp G := by rw [hpq]
      _ = C' := key C' hq.1 j' hq.2
  subst hCC
  have key2 : ∀ k < t, (C ∪ P C k) \ C = P C k := fun k hk =>
    union_sdiff_cancel_left (disjoint_of_subset_right (subset_supp hp.1) (hPV C hp.1 k hk)).symm
  have hPeq : P C j = P C j' := by
    calc P C j = (C ∪ P C j) \ C := (key2 j hp.2).symm
      _ = (C ∪ P C j') \ C := by rw [hpq]
      _ = P C j' := key2 j' hq.2
  by_contra hne
  have hjj : j ≠ j' := fun h => hne (by rw [h])
  have hd := hPP C hp.1 j hp.2 C hq.1 j' hq.2 (Or.inr hjj)
  rw [hPeq, disjoint_self_iff_empty] at hd
  have h2 := hPc C hq.1 j' hq.2
  rw [hd, card_empty] at h2
  exact absurd h2 (by norm_num)

theorem lift_sum {G : Fam} {t : ℕ} {P : Finset ℕ → ℕ → Finset ℕ}
    (hinj : Set.InjOn (fun p : Finset ℕ × ℕ => p.1 ∪ P p.1 p.2) ↑(G ×ˢ range t))
    (f : Finset ℕ → ℚ) :
    ∑ E ∈ lift G t P, f E = ∑ C ∈ G, ∑ j ∈ range t, f (C ∪ P C j) := by
  rw [lift, sum_image hinj, sum_product]

/-! ### Arithmetic of the shares -/

/-- The per-generator arithmetic of "Summing the shares". -/
theorem arith {a t lam δ L X Y Np Nm Z : ℚ} (ht : 0 < t) (ha : 0 ≤ a) (hlam0 : 0 ≤ lam)
    (hL : 0 ≤ L) (hX : 0 ≤ X) (hNp : 0 ≤ Np) (hlam : 2 * a ≤ lam * δ) (ht1 : 2 * a ≤ t)
    (ht2 : 6 * a * lam * L ≤ t) (hneg : Nm ≤ a * X) (hpos : t * Y ≤ 3 * a * Np)
    (hnew : Z ≤ t * X + Np) :
    a / t * Z ≤ lam * δ * X - lam * L * Y + (Np - Nm) := by
  rw [div_mul_eq_mul_div, div_le_iff₀ ht]
  have h1 : a * Z ≤ a * (t * X + Np) := mul_le_mul_of_nonneg_left hnew ha
  have h2 : 2 * a * (X * t) ≤ lam * δ * (X * t) :=
    mul_le_mul_of_nonneg_right hlam (mul_nonneg hX ht.le)
  have h3 : lam * L * (t * Y) ≤ lam * L * (3 * a * Np) :=
    mul_le_mul_of_nonneg_left hpos (mul_nonneg hlam0 hL)
  have h4 : 6 * a * lam * L * Np ≤ t * Np := mul_le_mul_of_nonneg_right ht2 hNp
  have h5 : Nm * t ≤ a * X * t := mul_le_mul_of_nonneg_right hneg ht.le
  have h6 : 2 * a * Np ≤ t * Np := mul_le_mul_of_nonneg_right ht1 hNp
  linarith

/-- The per-generator inequality, from the three fibre-counting bounds. -/
theorem per_C {U : Finset ℕ} {B : Fam} {C : Finset ℕ} {t : ℕ} {Pj : ℕ → Finset ℕ}
    (h : PairSetting U B C t Pj) {a lam : ℕ} {δ L : ℚ} (ha : 2 ^ C.card - 1 ≤ a)
    (ht0 : 0 < t) (hlam : 2 * (a : ℚ) ≤ lam * δ) (ht1 : 2 * a ≤ t)
    (ht2 : 6 * (a : ℚ) * lam * L ≤ t) (hL : 0 ≤ L) :
    (a : ℚ) / t * ∑ j ∈ range t, (xcount U B (C ∪ Pj j) : ℚ) ≤
      lam * δ * xcount U B C - lam * L * ycount B C +
        (∑ j ∈ range t, ((posFib U B (Pj j)).card : ℚ) -
          ∑ j ∈ range t, ((negFib U B (Pj j)).card : ℚ)) := by
  have hneg : ∑ j ∈ range t, (negFib U B (Pj j)).card ≤ a * xcount U B C :=
    (neg_fibre_bound h).trans (Nat.mul_le_mul_right _ ha)
  have hpos : t * ycount B C ≤ 3 * a * ∑ j ∈ range t, (posFib U B (Pj j)).card :=
    (pos_fibre_bound h).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 ha))
  have hnew := new_boundary_bound h
  have hnegQ : ∑ j ∈ range t, ((negFib U B (Pj j)).card : ℚ) ≤ a * xcount U B C := by
    exact_mod_cast hneg
  have hposQ : (t : ℚ) * ycount B C ≤ 3 * a * ∑ j ∈ range t, ((posFib U B (Pj j)).card : ℚ) := by
    exact_mod_cast hpos
  have hnewQ : ∑ j ∈ range t, (xcount U B (C ∪ Pj j) : ℚ) ≤
      t * xcount U B C + ∑ j ∈ range t, ((posFib U B (Pj j)).card : ℚ) := by
    exact_mod_cast hnew
  have ht1Q : 2 * (a : ℚ) ≤ t := by exact_mod_cast ht1
  have ht0Q : (0 : ℚ) < t := by exact_mod_cast ht0
  exact arith ht0Q (Nat.cast_nonneg a) (Nat.cast_nonneg lam) hL (Nat.cast_nonneg _)
    (sum_nonneg fun j _ => Nat.cast_nonneg _) hlam ht1Q ht2 hnegQ hposQ hnewQ

/-- The robust inequality for the lifted configuration. -/
theorem main_ineq {G : Fam} {w : ℕ → ℚ} {δ : ℚ} (hG : RobustFC G w δ) {t lam a : ℕ}
    (ha : ∀ C ∈ G, 2 ^ C.card - 1 ≤ a)
    (hlam : 2 * (a : ℚ) ≤ lam * δ) (ht1 : 2 * a ≤ t) (ht0 : 0 < t)
    (ht2 : 6 * (a : ℚ) * lam *
      (2 ^ (supp G).card * ((G.card : ℚ) * δ + (∑ u ∈ supp G, w u) / 2)) ≤ t)
    {P : Finset ℕ → ℕ → Finset ℕ}
    (hPc : ∀ C ∈ G, ∀ j < t, (P C j).card = 2)
    (hPV : ∀ C ∈ G, ∀ j < t, Disjoint (P C j) (supp G))
    (hPP : ∀ C ∈ G, ∀ j < t, ∀ C' ∈ G, ∀ j' < t, (C ≠ C' ∨ j ≠ j') →
      Disjoint (P C j) (P C' j'))
    {U : Finset ℕ} (hU : U = supp G ∪ (G ×ˢ range t).biUnion fun p => P p.1 p.2)
    {B : Fam} (hBU : ∀ X ∈ B, X ⊆ U) (huc : UnionClosed B)
    (hstab : ∀ X ∈ B, ∀ g ∈ lift G t P, X ∪ g ∈ B) :
    (a : ℚ) / t * ∑ E ∈ lift G t P, (xcount U B E : ℚ) ≤
      share (liftW lam w (supp G)) U B := by
  have hVR := disj_VR hPV
  have hQ := pairwise_disj hPP
  have hQc : ∀ p ∈ G ×ˢ range t, (P p.1 p.2).card = 2 := fun p hp => by
    rw [mem_product, mem_range] at hp
    exact hPc p.1 hp.1 p.2 hp.2
  have hshare : share (liftW lam w (supp G)) U B =
      lam * ∑ S ∈ ((G ×ˢ range t).biUnion fun p => P p.1 p.2).powerset,
          share w (supp G) (slice (supp G) B S) +
        ∑ C ∈ G, (∑ j ∈ range t, ((posFib U B (P C j)).card : ℚ) -
          ∑ j ∈ range t, ((negFib U B (P C j)).card : ℚ)) := by
    rw [share_lift hVR hU hQ hQc lam w hBU, sum_product]
    simp only [sum_sub_distrib]
  have hdef := defect_sum hG hVR hU hBU huc
  have hL : 0 ≤ 2 ^ (supp G).card * ((G.card : ℚ) * δ + (∑ u ∈ supp G, w u) / 2) := by
    have h3 : 0 ≤ (G.card : ℚ) * δ := mul_nonneg (Nat.cast_nonneg _) hG.2.2.2.2.1.le
    have h4 : 0 ≤ (G.card : ℚ) * δ + (∑ u ∈ supp G, w u) / 2 := by linarith [hG.2.2.2.1]
    exact mul_nonneg (pow_nonneg (by norm_num) _) h4
  have hC : ∀ C ∈ G, (a : ℚ) / t * ∑ j ∈ range t, (xcount U B (C ∪ P C j) : ℚ) ≤
      lam * δ * xcount U B C -
        lam * (2 ^ (supp G).card * ((G.card : ℚ) * δ + (∑ u ∈ supp G, w u) / 2)) *
          ycount B C +
        (∑ j ∈ range t, ((posFib U B (P C j)).card : ℚ) -
          ∑ j ∈ range t, ((negFib U B (P C j)).card : ℚ)) := by
    intro C hC
    have hset : PairSetting U B C t (P C) :=
      { memU := hBU
        uc := huc
        hC := by
          rw [hU]
          exact (subset_supp hC).trans subset_union_left
        hPcard := fun j hj => hPc C hC j hj
        hPU := fun j hj => by
          rw [hU]
          exact (subset_biUnion_of_mem (fun p : Finset ℕ × ℕ => P p.1 p.2) (x := (C, j))
            (mem_product.mpr ⟨hC, mem_range.mpr hj⟩)).trans subset_union_right
        hPC := fun j hj => disjoint_of_subset_right (subset_supp hC) (hPV C hC j hj)
        hPP := fun j hj j' hj' hne => hPP C hC j hj C hC j' hj' (Or.inr hne)
        stab := fun X hX j hj => hstab X hX _ (mem_lift hC hj) }
    exact per_C hset (ha C hC) ht0 hlam ht1 ht2 hL
  rw [lift_sum (lift_injOn hPc hPV hPP), mul_sum]
  have hsum := sum_le_sum hC
  have hlin : ∑ C ∈ G, ((lam : ℚ) * δ * xcount U B C -
        lam * (2 ^ (supp G).card * ((G.card : ℚ) * δ + (∑ u ∈ supp G, w u) / 2)) *
          ycount B C +
        (∑ j ∈ range t, ((posFib U B (P C j)).card : ℚ) -
          ∑ j ∈ range t, ((negFib U B (P C j)).card : ℚ))) =
      lam * δ * ∑ C ∈ G, (xcount U B C : ℚ) -
        lam * (2 ^ (supp G).card * ((G.card : ℚ) * δ + (∑ u ∈ supp G, w u) / 2)) *
          ∑ C ∈ G, (ycount B C : ℚ) +
        ∑ C ∈ G, (∑ j ∈ range t, ((posFib U B (P C j)).card : ℚ) -
          ∑ j ∈ range t, ((negFib U B (P C j)).card : ℚ)) := by
    rw [sum_add_distrib, sum_sub_distrib (s := G) (f := fun C => (lam : ℚ) * δ * xcount U B C),
      mul_sum, mul_sum]
  have h5 := mul_le_mul_of_nonneg_left hdef (Nat.cast_nonneg lam : (0 : ℚ) ≤ lam)
  rw [hshare]
  linarith

end Lifting

open Lifting in
/-- **Robust pair-petal lifting** (paper Theorem 3.1).  `a` is any natural number with
`a ≥ 1` and `a ≥ 2^{|C|} - 1` for all `C ∈ G`; `L = 2^v (m δ + W/2)` is the defect constant. -/
theorem lifting (G : Fam) (w : ℕ → ℚ) (δ : ℚ) (hG : RobustFC G w δ) (t lam a : ℕ)
    (ha1 : 1 ≤ a) (ha : ∀ C ∈ G, 2 ^ C.card - 1 ≤ a)
    (hlam : 2 * (a : ℚ) ≤ lam * δ) (ht1 : 2 * a ≤ t)
    (ht2 : 6 * (a : ℚ) * lam *
      (2 ^ (supp G).card * ((G.card : ℚ) * δ + (∑ u ∈ supp G, w u) / 2)) ≤ t)
    (P : Finset ℕ → ℕ → Finset ℕ)
    (hPc : ∀ C ∈ G, ∀ j < t, (P C j).card = 2)
    (hPV : ∀ C ∈ G, ∀ j < t, Disjoint (P C j) (supp G))
    (hPP : ∀ C ∈ G, ∀ j < t, ∀ C' ∈ G, ∀ j' < t, (C ≠ C' ∨ j ≠ j') →
      Disjoint (P C j) (P C' j')) :
    RobustFC (lift G t P) (liftW lam w (supp G)) ((a : ℚ) / t) := by
  have ht0 : 0 < t := by omega
  have hwt : ∀ u, 0 ≤ liftW lam w (supp G) u := fun u => by
    unfold liftW
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (hG.2.2.1 u)
    · exact zero_le_one
  refine ⟨?_, ?_, hwt, ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hG.1
    exact ⟨_, mem_lift hC ht0⟩
  · intro E hE
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hE
    exact (hG.2.1 p.1 (mem_product.mp hp).1).mono subset_union_left
  · rw [supp_lift G ht0 P]
    obtain ⟨C, hC⟩ := hG.1
    have hcard : 0 < (P C 0).card := by rw [hPc C hC 0 ht0]; norm_num
    obtain ⟨x, hx⟩ := card_pos.mp hcard
    have hxR : x ∈ (G ×ˢ range t).biUnion fun p => P p.1 p.2 :=
      mem_biUnion.mpr ⟨(C, 0), mem_product.mpr ⟨hC, mem_range.mpr ht0⟩, hx⟩
    have hxV : x ∉ supp G := fun h => disjoint_left.mp (hPV C hC 0 ht0) hx h
    refine sum_pos' (fun u _ => hwt u) ⟨x, mem_union_right _ hxR, ?_⟩
    unfold liftW
    rw [if_neg hxV]
    norm_num
  · have h1 : (0 : ℚ) < a := by exact_mod_cast ha1
    have h2 : (0 : ℚ) < t := by exact_mod_cast ht0
    exact div_pos h1 h2
  · intro B hB
    exact main_ineq hG ha hlam ht1 ht0 ht2 hPc hPV hPP (supp_lift G ht0 P) hB.1 hB.2.1 hB.2.2

end Results.FcMorrisV2
