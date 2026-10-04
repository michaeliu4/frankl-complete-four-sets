import Results.FcMorrisV2.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Solution/Basic: weighted shares, negative certificates, coatom families

Public API shared by all solution modules (paper Section 2).  Statements are fixed; proofs may be
developed independently of the dependent modules.

* `ucl G`   : `⟨G ∪ {∅}⟩`, all unions of subfamilies of `G`.
* `rho B u` : imbalance `2 |B_u| - |B|`.
* `share w U B` : weighted share `Q_w(B) = ∑_{X ∈ B} (∑_{u ∈ X} w_u - W/2)`, `W = ∑_{u ∈ U} w_u`.
* `coatom G z` : `E_z = 2^{U∖{z}} ∪ ↑{g ∈ G : z ∈ g}` (upward closure within `U = supp G`).
* `omitted G z` : `2^U ∖ E_z`.
-/

namespace Results.FcMorrisV2

open Finset

/-- Union closure of `G ∪ {∅}`: all unions of subfamilies of `G`. -/
def ucl (G : Fam) : Fam := G.powerset.image fun S => S.sup id

/-- Imbalance of a family at a point. -/
def rho (B : Fam) (u : ℕ) : ℤ := 2 * (deg B u : ℤ) - (B.card : ℤ)

/-- Weighted share of `B` relative to the ground set `U`. -/
def share (w : ℕ → ℚ) (U : Finset ℕ) (B : Fam) : ℚ :=
  ∑ X ∈ B, (∑ u ∈ X, w u - (∑ u ∈ U, w u) / 2)

/-- The coatom family `E_z`. -/
def coatom (G : Fam) (z : ℕ) : Fam :=
  (supp G).powerset.filter fun A => z ∉ A ∨ ∃ g ∈ G, z ∈ g ∧ g ⊆ A

/-- The omitted family `2^U ∖ E_z`. -/
def omitted (G : Fam) (z : ℕ) : Fam :=
  (supp G).powerset.filter fun A => z ∈ A ∧ ∀ g ∈ G, z ∈ g → ¬ g ⊆ A

namespace Basic

/-! ### Support -/

theorem mem_supp {G : Fam} {u : ℕ} : u ∈ supp G ↔ ∃ g ∈ G, u ∈ g := by
  unfold supp
  simp only [Finset.mem_biUnion, id]

theorem subset_supp {G : Fam} {g : Finset ℕ} (hg : g ∈ G) : g ⊆ supp G := fun _ hx =>
  mem_supp.2 ⟨g, hg, hx⟩

theorem supp_mono {G G' : Fam} (h : G ⊆ G') : supp G ⊆ supp G' := fun _ hx => by
  obtain ⟨g, hg, hxg⟩ := mem_supp.1 hx
  exact mem_supp.2 ⟨g, h hg, hxg⟩

end Basic

/-- A configuration containing an FC subconfiguration is FC. -/
theorem isFC_mono {G G' : Fam} (h : G ⊆ G') (hG : IsFC G) : IsFC G' := by
  intro F hF hUC
  obtain ⟨u, hu, hle⟩ := hG F (h.trans hF) hUC
  exact ⟨u, Basic.supp_mono h hu, hle⟩

/-- Every subconfiguration of a non-FC configuration is non-FC. -/
theorem not_isFC_of_subset {G G' : Fam} (h : G ⊆ G') (hG' : ¬ IsFC G') : ¬ IsFC G :=
  fun hG => hG' (isFC_mono h hG)

/-- The empty configuration is not FC. -/
theorem not_isFC_empty : ¬ IsFC (∅ : Fam) := by
  intro h
  obtain ⟨u, hu, -⟩ := h ∅ (Finset.Subset.refl _) (fun A hA => absurd hA (Finset.notMem_empty A))
  obtain ⟨g, hg, -⟩ := Basic.mem_supp.1 hu
  exact Finset.notMem_empty g hg

namespace Basic

/-! ### Union closure -/

theorem mem_ucl {G : Fam} {X : Finset ℕ} : X ∈ ucl G ↔ ∃ S ⊆ G, S.sup id = X := by
  unfold ucl
  simp only [Finset.mem_image, Finset.mem_powerset]

theorem sup_subset_supp {G S : Fam} (hS : S ⊆ G) : S.sup id ⊆ supp G :=
  Finset.sup_le fun _ hg => subset_supp (hS hg)

theorem subset_supp_of_mem_ucl {G : Fam} {X : Finset ℕ} (hX : X ∈ ucl G) : X ⊆ supp G := by
  obtain ⟨S, hS, rfl⟩ := mem_ucl.1 hX
  exact sup_subset_supp hS

theorem supp_subset_of_subset_ucl {G H : Fam} (hH : H ⊆ ucl G) : supp H ⊆ supp G := by
  intro x hx
  obtain ⟨h, hh, hxh⟩ := mem_supp.1 hx
  exact subset_supp_of_mem_ucl (hH hh) hxh

theorem self_subset_ucl (G : Fam) : G ⊆ ucl G := by
  intro g hg
  refine mem_ucl.2 ⟨{g}, Finset.singleton_subset_iff.2 hg, ?_⟩
  rw [Finset.sup_singleton, id_eq]

theorem ucl_unionClosed (G : Fam) : UnionClosed (ucl G) := by
  intro X hX Y hY
  obtain ⟨S, hS, rfl⟩ := mem_ucl.1 hX
  obtain ⟨S', hS', rfl⟩ := mem_ucl.1 hY
  refine mem_ucl.2 ⟨S ∪ S', Finset.union_subset hS hS', ?_⟩
  rw [Finset.sup_union, Finset.sup_eq_union]

/-- A nonempty union of members of a union-closed family is a member. -/
theorem sup_mem_of_unionClosed {F : Fam} (hF : UnionClosed F) :
    ∀ S : Fam, S ⊆ F → S.Nonempty → S.sup id ∈ F := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ hne; exact absurd hne Finset.not_nonempty_empty
  | insert a S _ ih =>
    intro hS _
    rw [Finset.sup_insert]
    have haF : a ∈ F := hS (Finset.mem_insert_self a S)
    rcases S.eq_empty_or_nonempty with hS0 | hSne
    · subst hS0
      rw [Finset.sup_empty, sup_bot_eq]
      exact haF
    · rw [Finset.sup_eq_union]
      exact hF _ haF _ (ih ((Finset.subset_insert a S).trans hS) hSne)

theorem ucl_subset_insert_empty {G F : Fam} (hGF : G ⊆ F) (hF : UnionClosed F) :
    ucl G ⊆ insert ∅ F := by
  intro X hX
  obtain ⟨S, hS, rfl⟩ := mem_ucl.1 hX
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · subst hS0
    rw [Finset.sup_empty, Finset.bot_eq_empty]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (sup_mem_of_unionClosed hF S (hS.trans hGF) hSne)

theorem insert_empty_unionClosed {F : Fam} (hF : UnionClosed F) :
    UnionClosed (insert ∅ F) := by
  intro A hA B hB
  rcases Finset.mem_insert.1 hA with rfl | hA'
  · rwa [Finset.empty_union]
  · rcases Finset.mem_insert.1 hB with rfl | hB'
    · rw [Finset.union_empty]
      exact Finset.mem_insert_of_mem hA'
    · exact Finset.mem_insert_of_mem (hF A hA' B hB')

theorem deg_insert_empty (F : Fam) (u : ℕ) : deg (insert ∅ F) u = deg F u := by
  unfold deg
  rw [Finset.filter_insert, if_neg (Finset.notMem_empty u)]

/-- An admissible family is stable under adjoining any member of `ucl G`. -/
theorem admissible_union_ucl {G B : Fam} (hB : Admissible G B) {X Y : Finset ℕ} (hX : X ∈ B)
    (hY : Y ∈ ucl G) : X ∪ Y ∈ B := by
  obtain ⟨S, hS, rfl⟩ := mem_ucl.1 hY
  clear hY
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.bot_eq_empty, Finset.union_empty]
    exact hX
  | insert a S _ ih =>
    rw [Finset.sup_insert, Finset.sup_eq_union, id_eq, Finset.union_comm a,
      ← Finset.union_assoc]
    exact hB.2.2 _ (ih ((Finset.subset_insert a S).trans hS)) a
      (hS (Finset.mem_insert_self a S))

end Basic

/-- Paper Lemma 2.3 (inheritance through union closure). -/
theorem not_isFC_of_subset_ucl {G H : Fam} (hG : ¬ IsFC G) (hH : H ⊆ ucl G) : ¬ IsFC H := by
  intro hHFC
  apply hG
  intro F hGF hF
  obtain ⟨u, hu, hle⟩ := hHFC (insert ∅ F)
    (hH.trans (Basic.ucl_subset_insert_empty hGF hF)) (Basic.insert_empty_unionClosed hF)
  refine ⟨u, Basic.supp_subset_of_subset_ucl hH hu, ?_⟩
  rw [Basic.deg_insert_empty] at hle
  exact (Finset.card_le_card (Finset.subset_insert ∅ F)).trans hle

namespace Basic

/-! ### Weighted transfer -/

/-- The exact outside-trace family `{X ∩ U : X ∈ F, X \ U = T}`. -/
def traceFam (F : Fam) (U T : Finset ℕ) : Fam :=
  (F.filter fun X => X \ U = T).image (· ∩ U)

theorem traceFam_admissible {G F : Fam} (hGF : G ⊆ F) (hF : UnionClosed F) (T : Finset ℕ) :
    Admissible G (traceFam F (supp G) T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨X, -, rfl⟩ := Finset.mem_image.1 hS
    exact Finset.inter_subset_right
  · intro S₁ hS₁ S₂ hS₂
    obtain ⟨X₁, hX₁, rfl⟩ := Finset.mem_image.1 hS₁
    obtain ⟨X₂, hX₂, rfl⟩ := Finset.mem_image.1 hS₂
    rw [Finset.mem_filter] at hX₁ hX₂
    refine Finset.mem_image.2 ⟨X₁ ∪ X₂, Finset.mem_filter.2 ⟨hF _ hX₁.1 _ hX₂.1, ?_⟩, ?_⟩
    · rw [Finset.union_sdiff_distrib, hX₁.2, hX₂.2, Finset.union_self]
    · exact Finset.union_inter_distrib_right _ _ _
  · intro S hS g hg
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hS
    rw [Finset.mem_filter] at hX
    have hgU : g ⊆ supp G := subset_supp hg
    refine Finset.mem_image.2 ⟨X ∪ g, Finset.mem_filter.2 ⟨hF _ hX.1 _ (hGF hg), ?_⟩, ?_⟩
    · rw [Finset.union_sdiff_distrib, hX.2, Finset.sdiff_eq_empty_iff_subset.2 hgU,
        Finset.union_empty]
    · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.2 hgU]

/-- Decomposition of a sum over `F` along exact outside traces. -/
theorem sum_eq_sum_traceFam (F : Fam) (U : Finset ℕ) (f : Finset ℕ → ℚ) :
    ∑ X ∈ F, f (X ∩ U) = ∑ T ∈ F.image (· \ U), ∑ S ∈ traceFam F U T, f S := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun X => X \ U) (t := F.image (· \ U))
    (fun X hX => Finset.mem_image_of_mem _ hX)]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold traceFam
  rw [Finset.sum_image]
  intro X₁ hX₁ X₂ hX₂ heq
  rw [Finset.mem_coe, Finset.mem_filter] at hX₁ hX₂
  have h2 : X₁ \ U = X₂ \ U := hX₁.2.trans hX₂.2.symm
  have h1 : X₁ ∩ U = X₂ ∩ U := heq
  ext x
  by_cases hx : x ∈ U
  · have := Finset.ext_iff.1 h1 x
    simp only [Finset.mem_inter, hx, and_true] at this
    exact this
  · have := Finset.ext_iff.1 h2 x
    simp only [Finset.mem_sdiff, hx, not_false_eq_true, and_true] at this
    exact this

/-- Double counting: `∑_{X ∈ F} ∑_{u ∈ X ∩ U} w u = ∑_{u ∈ U} w u · deg F u`. -/
theorem sum_inter_eq_sum_deg (F : Fam) (U : Finset ℕ) (w : ℕ → ℚ) :
    ∑ X ∈ F, ∑ u ∈ X ∩ U, w u = ∑ u ∈ U, w u * (deg F u : ℚ) := by
  have e1 : ∀ X ∈ F, ∑ u ∈ X ∩ U, w u = ∑ u ∈ U, if u ∈ X then w u else 0 := by
    intro X _
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rfl

end Basic

/-- Paper Lemma 2.2 (weighted transfer). -/
theorem isFC_of_weights (G : Fam) (w : ℕ → ℚ) (hw : ∀ u, 0 ≤ w u)
    (hW : 0 < ∑ u ∈ supp G, w u)
    (h : ∀ B : Fam, Admissible G B → 0 ≤ share w (supp G) B) : IsFC G := by
  intro F hGF hF
  by_contra hno
  simp only [not_exists, not_and, not_le] at hno
  -- every trace family has nonnegative share; summing gives the averaged inequality
  have key : 0 ≤ ∑ X ∈ F, (∑ u ∈ X ∩ supp G, w u - (∑ u ∈ supp G, w u) / 2) := by
    rw [Basic.sum_eq_sum_traceFam F (supp G)
      (fun S => ∑ u ∈ S, w u - (∑ u ∈ supp G, w u) / 2)]
    exact Finset.sum_nonneg fun T _ => h _ (Basic.traceFam_admissible hGF hF T)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Basic.sum_inter_eq_sum_deg] at key
  obtain ⟨u₀, hu₀, hpos⟩ : ∃ u ∈ supp G, (0 : ℚ) < w u := by
    have h0 : ∑ u ∈ supp G, (0 : ℚ) < ∑ u ∈ supp G, w u := by
      rw [Finset.sum_const_zero]
      exact hW
    exact Finset.exists_lt_of_sum_lt h0
  have hlt : ∑ u ∈ supp G, w u * (2 * (deg F u : ℚ)) <
      ∑ u ∈ supp G, w u * (F.card : ℚ) := by
    apply Finset.sum_lt_sum
    · intro u hu
      apply mul_le_mul_of_nonneg_left _ (hw u)
      exact_mod_cast (hno u hu).le
    · exact ⟨u₀, hu₀, mul_lt_mul_of_pos_left (by exact_mod_cast hno u₀ hu₀) hpos⟩
  rw [← Finset.sum_mul] at hlt
  have h2 : ∑ u ∈ supp G, w u * (2 * (deg F u : ℚ)) =
      2 * ∑ u ∈ supp G, w u * (deg F u : ℚ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [h2] at hlt
  linarith

/-- The coatom family is admissible (paper (2.4)). -/
theorem coatom_admissible (G : Fam) (z : ℕ) : Admissible G (coatom G z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    exact Finset.mem_powerset.1 (Finset.mem_filter.1 hX).1
  · intro A hA B hB
    unfold coatom at hA hB ⊢
    rw [Finset.mem_filter, Finset.mem_powerset] at hA hB ⊢
    refine ⟨Finset.union_subset hA.1 hB.1, ?_⟩
    by_cases hzA : z ∈ A
    · rcases hA.2 with h | ⟨g, hg, hzg, hgA⟩
      · exact absurd hzA h
      · exact Or.inr ⟨g, hg, hzg, hgA.trans Finset.subset_union_left⟩
    · by_cases hzB : z ∈ B
      · rcases hB.2 with h | ⟨g, hg, hzg, hgB⟩
        · exact absurd hzB h
        · exact Or.inr ⟨g, hg, hzg, hgB.trans Finset.subset_union_right⟩
      · left
        rw [Finset.mem_union]
        rintro (h | h)
        · exact hzA h
        · exact hzB h
  · intro A hA g hg
    unfold coatom at hA ⊢
    rw [Finset.mem_filter, Finset.mem_powerset] at hA ⊢
    refine ⟨Finset.union_subset hA.1 (Basic.subset_supp hg), ?_⟩
    by_cases hzg : z ∈ g
    · exact Or.inr ⟨g, hg, hzg, Finset.subset_union_right⟩
    · by_cases hzA : z ∈ A
      · rcases hA.2 with h | ⟨g', hg', hzg', hg'A⟩
        · exact absurd hzA h
        · exact Or.inr ⟨g', hg', hzg', hg'A.trans Finset.subset_union_left⟩
      · left
        rw [Finset.mem_union]
        rintro (h | h)
        · exact hzA h
        · exact hzg h

namespace Basic

/-! ### Imbalance -/

theorem rho_eq_sum (B : Fam) (u : ℕ) :
    rho B u = ∑ X ∈ B, (if u ∈ X then (1 : ℤ) else -1) := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h := Finset.card_filter_add_card_filter_not (s := B) (fun X => u ∈ X)
  have h' : ((B.filter fun X => u ∈ X).card : ℤ) + ((B.filter fun X => ¬ u ∈ X).card : ℤ)
      = B.card := by
    exact_mod_cast h
  unfold rho deg
  linarith

theorem rho_le_card (B : Fam) (u : ℕ) : rho B u ≤ B.card := by
  have h : ((B.filter fun A => u ∈ A).card : ℤ) ≤ B.card := by
    exact_mod_cast Finset.card_filter_le _ _
  unfold rho deg
  linarith

theorem rho_powerset' (U : Finset ℕ) {u : ℕ} (hu : u ∈ U) : rho U.powerset u = 0 := by
  have hbij : (U.powerset.filter fun A => u ∈ A).card =
      (U.powerset.filter fun A => ¬ u ∈ A).card := by
    apply Finset.card_nbij' (fun A => A.erase u) (fun A => insert u A)
    · intro A hA
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hA
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨(Finset.erase_subset u A).trans hA.1, Finset.notMem_erase u A⟩
    · intro A hA
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hA
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset hu hA.1, Finset.mem_insert_self u A⟩
    · intro A hA
      rw [Finset.mem_coe, Finset.mem_filter] at hA
      exact Finset.insert_erase hA.2
    · intro A hA
      rw [Finset.mem_coe, Finset.mem_filter] at hA
      exact Finset.erase_insert hA.2
  have h := Finset.card_filter_add_card_filter_not (s := U.powerset) (fun A => u ∈ A)
  unfold rho deg
  omega

/-- Additivity of `rho` over a partition of a family by a predicate. -/
theorem rho_filter_add (P : Fam) (p : Finset ℕ → Prop) [DecidablePred p] (u : ℕ) :
    rho (P.filter p) u + rho (P.filter fun A => ¬ p A) u = rho P u := by
  have hc := Finset.card_filter_add_card_filter_not (s := P) p
  have hd := Finset.card_filter_add_card_filter_not (s := P.filter fun A => u ∈ A) p
  unfold rho deg
  rw [Finset.filter_comm p, Finset.filter_comm (fun A => ¬ p A)]
  omega

/-! ### Tagged extensions (negative certificates) -/

/-- The tagged extension `⋃_{T ⊆ Z} {S ∪ T : S ∈ Φ T}`. -/
def tagExt (Z : Finset ℕ) (Φ : Finset ℕ → Fam) : Fam :=
  Z.powerset.biUnion fun T => (Φ T).image (· ∪ T)

theorem mem_tagExt {Z : Finset ℕ} {Φ : Finset ℕ → Fam} {X : Finset ℕ} :
    X ∈ tagExt Z Φ ↔ ∃ T ⊆ Z, ∃ S ∈ Φ T, S ∪ T = X := by
  unfold tagExt
  simp only [Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]

theorem union_inter_tags {S T Z : Finset ℕ} (hS : Disjoint S Z) (hT : T ⊆ Z) :
    (S ∪ T) ∩ Z = T := by
  ext x
  rw [Finset.mem_inter, Finset.mem_union]
  have h1 : x ∈ S → x ∉ Z := fun h => Finset.disjoint_left.1 hS h
  have h2 : x ∈ T → x ∈ Z := fun h => hT h
  tauto

theorem union_sdiff_tags {S T Z : Finset ℕ} (hS : Disjoint S Z) (hT : T ⊆ Z) :
    (S ∪ T) \ Z = S := by
  ext x
  rw [Finset.mem_sdiff, Finset.mem_union]
  have h1 : x ∈ S → x ∉ Z := fun h => Finset.disjoint_left.1 hS h
  have h2 : x ∈ T → x ∈ Z := fun h => hT h
  tauto

/-- Sums over a tagged extension split along the tag traces. -/
theorem sum_tagExt {β : Type*} [AddCommMonoid β] (Z : Finset ℕ) (Φ : Finset ℕ → Fam)
    (hΦ : ∀ T ⊆ Z, ∀ S ∈ Φ T, Disjoint S Z) (φ : Finset ℕ → β) :
    ∑ X ∈ tagExt Z Φ, φ X = ∑ T ∈ Z.powerset, ∑ S ∈ Φ T, φ (S ∪ T) := by
  unfold tagExt
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    rw [Finset.sum_image]
    intro S₁ hS₁ S₂ hS₂ heq
    rw [Finset.mem_coe] at hS₁ hS₂
    have e : (S₁ ∪ T) \ Z = (S₂ ∪ T) \ Z := by
      have heq' : S₁ ∪ T = S₂ ∪ T := heq
      rw [heq']
    rwa [union_sdiff_tags (hΦ T hT S₁ hS₁) hT, union_sdiff_tags (hΦ T hT S₂ hS₂) hT] at e
  · intro T₁ hT₁ T₂ hT₂ hne
    rw [Finset.mem_coe, Finset.mem_powerset] at hT₁ hT₂
    refine Finset.disjoint_left.2 fun X hX₁ hX₂ => hne ?_
    obtain ⟨S₁, hS₁, e₁⟩ := Finset.mem_image.1 hX₁
    obtain ⟨S₂, hS₂, e₂⟩ := Finset.mem_image.1 hX₂
    have e₁' : S₁ ∪ T₁ = X := e₁
    have e₂' : S₂ ∪ T₂ = X := e₂
    have e : (S₁ ∪ T₁) ∩ Z = (S₂ ∪ T₂) ∩ Z := by rw [e₁', e₂']
    rwa [union_inter_tags (hΦ T₁ hT₁ S₁ hS₁) hT₁, union_inter_tags (hΦ T₂ hT₂ S₂ hS₂) hT₂] at e

/-- The imbalance of a tagged extension at an untagged point is the sum over the traces. -/
theorem rho_tagExt (Z : Finset ℕ) (Φ : Finset ℕ → Fam)
    (hΦ : ∀ T ⊆ Z, ∀ S ∈ Φ T, Disjoint S Z) {u : ℕ} (hu : u ∉ Z) :
    rho (tagExt Z Φ) u = ∑ T ∈ Z.powerset, rho (Φ T) u := by
  rw [rho_eq_sum, sum_tagExt Z Φ hΦ]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [rho_eq_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have huT : u ∉ T := fun h => hu (Finset.mem_powerset.1 hT h)
  simp only [Finset.mem_union, huT, or_false]

/-- Trace families of the negative-certificate extension: `ucl G` on the empty trace, the family
of the tag's type on a singleton trace, and the full cube on larger traces. -/
def trFam (G : Fam) (fam : ℕ → Fam) (typ : ℕ → ℕ) (T : Finset ℕ) : Fam :=
  if T = ∅ then ucl G else if T.card = 1 then fam (typ (T.sup id)) else (supp G).powerset

theorem trFam_empty (G : Fam) (fam : ℕ → Fam) (typ : ℕ → ℕ) : trFam G fam typ ∅ = ucl G := by
  unfold trFam
  exact if_pos rfl

theorem trFam_singleton (G : Fam) (fam : ℕ → Fam) (typ : ℕ → ℕ) (τ : ℕ) :
    trFam G fam typ {τ} = fam (typ τ) := by
  unfold trFam
  rw [if_neg (Finset.singleton_ne_empty τ), if_pos (Finset.card_singleton τ),
    Finset.sup_singleton, id_eq]

theorem trFam_big (G : Fam) (fam : ℕ → Fam) (typ : ℕ → ℕ) {T : Finset ℕ} (h0 : T ≠ ∅)
    (h1 : T.card ≠ 1) : trFam G fam typ T = (supp G).powerset := by
  unfold trFam
  rw [if_neg h0, if_neg h1]

theorem trFam_subset {G : Fam} {fam : ℕ → Fam} {typ : ℕ → ℕ} {Z : Finset ℕ}
    (hadm : ∀ τ ∈ Z, Admissible G (fam (typ τ))) {T S : Finset ℕ} (hT : T ⊆ Z)
    (hS : S ∈ trFam G fam typ T) : S ⊆ supp G := by
  by_cases h0 : T = ∅
  · subst h0
    rw [trFam_empty] at hS
    exact subset_supp_of_mem_ucl hS
  · by_cases h1 : T.card = 1
    · obtain ⟨τ, rfl⟩ := Finset.card_eq_one.1 h1
      rw [trFam_singleton] at hS
      exact (hadm τ (hT (Finset.mem_singleton_self τ))).1 S hS
    · rw [trFam_big G fam typ h0 h1, Finset.mem_powerset] at hS
      exact hS

theorem trFam_union {G : Fam} {fam : ℕ → Fam} {typ : ℕ → ℕ} {Z : Finset ℕ}
    (hadm : ∀ τ ∈ Z, Admissible G (fam (typ τ)))
    {T₁ T₂ S₁ S₂ : Finset ℕ} (hT₁ : T₁ ⊆ Z) (hT₂ : T₂ ⊆ Z)
    (hS₁ : S₁ ∈ trFam G fam typ T₁) (hS₂ : S₂ ∈ trFam G fam typ T₂) :
    S₁ ∪ S₂ ∈ trFam G fam typ (T₁ ∪ T₂) := by
  by_cases h0 : T₁ ∪ T₂ = ∅
  · obtain ⟨rfl, rfl⟩ := Finset.union_eq_empty.1 h0
    rw [trFam_empty] at hS₁ hS₂
    rw [Finset.union_empty, trFam_empty]
    exact ucl_unionClosed G _ hS₁ _ hS₂
  · by_cases h1 : (T₁ ∪ T₂).card = 1
    · obtain ⟨τ, hτ⟩ := Finset.card_eq_one.1 h1
      have hτZ : τ ∈ Z := by
        have : τ ∈ T₁ ∪ T₂ := by
          rw [hτ]
          exact Finset.mem_singleton_self τ
        exact Finset.union_subset hT₁ hT₂ this
      have hB := hadm τ hτZ
      rw [hτ, trFam_singleton]
      have h1' : T₁ ⊆ {τ} := by
        rw [← hτ]
        exact Finset.subset_union_left
      have h2' : T₂ ⊆ {τ} := by
        rw [← hτ]
        exact Finset.subset_union_right
      rcases Finset.subset_singleton_iff.1 h1' with rfl | rfl <;>
        rcases Finset.subset_singleton_iff.1 h2' with rfl | rfl
      · exact absurd (Finset.union_empty ∅) h0
      · rw [trFam_empty] at hS₁
        rw [trFam_singleton] at hS₂
        rw [Finset.union_comm]
        exact admissible_union_ucl hB hS₂ hS₁
      · rw [trFam_singleton] at hS₁
        rw [trFam_empty] at hS₂
        exact admissible_union_ucl hB hS₁ hS₂
      · rw [trFam_singleton] at hS₁ hS₂
        exact hB.2.1 _ hS₁ _ hS₂
    · rw [trFam_big G fam typ h0 h1, Finset.mem_powerset]
      exact Finset.union_subset (trFam_subset hadm hT₁ hS₁) (trFam_subset hadm hT₂ hS₂)

theorem negExt_unionClosed {G : Fam} {fam : ℕ → Fam} {typ : ℕ → ℕ} {Z : Finset ℕ}
    (hadm : ∀ τ ∈ Z, Admissible G (fam (typ τ))) :
    UnionClosed (tagExt Z (trFam G fam typ)) := by
  intro X hX Y hY
  obtain ⟨T₁, hT₁, S₁, hS₁, rfl⟩ := mem_tagExt.1 hX
  obtain ⟨T₂, hT₂, S₂, hS₂, rfl⟩ := mem_tagExt.1 hY
  refine mem_tagExt.2 ⟨T₁ ∪ T₂, Finset.union_subset hT₁ hT₂, S₁ ∪ S₂,
    trFam_union hadm hT₁ hT₂ hS₁ hS₂, ?_⟩
  exact Finset.union_union_union_comm S₁ S₂ T₁ T₂

theorem sum_rho_trFam (G : Fam) (fam : ℕ → Fam) (typ : ℕ → ℕ) (Z : Finset ℕ) {u : ℕ}
    (hu : u ∈ supp G) :
    ∑ T ∈ Z.powerset, rho (trFam G fam typ T) u =
      rho (ucl G) u + ∑ τ ∈ Z, rho (fam (typ τ)) u := by
  have hpt : ∀ T ∈ Z.powerset, rho (trFam G fam typ T) u =
      (if T = ∅ then rho (ucl G) u else 0) +
        (if T.card = 1 then rho (trFam G fam typ T) u else 0) := by
    intro T _
    by_cases h0 : T = ∅
    · subst h0
      rw [if_pos rfl, if_neg (by rw [Finset.card_empty]; exact Nat.zero_ne_one), add_zero,
        trFam_empty]
    · by_cases h1 : T.card = 1
      · rw [if_neg h0, if_pos h1, zero_add]
      · rw [if_neg h0, if_neg h1, add_zero, trFam_big G fam typ h0 h1, rho_powerset' _ hu]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.empty_mem_powerset Z), ← Finset.sum_filter, ← Finset.powersetCard_eq_filter,
    Finset.powersetCard_one, Finset.sum_map]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Function.Embedding.coeFn_mk, trFam_singleton]

/-- Abstract negative-certificate extension: tags `Z` disjoint from the support, each with an
admissible family `fam (typ τ)`, and strictly negative total imbalance. -/
theorem not_isFC_of_tags (G : Fam) (fam : ℕ → Fam) (typ : ℕ → ℕ) (Z : Finset ℕ)
    (hadm : ∀ τ ∈ Z, Admissible G (fam (typ τ))) (hdisj : Disjoint (supp G) Z)
    (hneg : ∀ u ∈ supp G, rho (ucl G) u + ∑ τ ∈ Z, rho (fam (typ τ)) u < 0) : ¬ IsFC G := by
  intro hFC
  have hΦ : ∀ T ⊆ Z, ∀ S ∈ trFam G fam typ T, Disjoint S Z := fun T hT S hS =>
    Finset.disjoint_of_subset_left (trFam_subset hadm hT hS) hdisj
  have hGF : G ⊆ tagExt Z (trFam G fam typ) := by
    intro g hg
    refine mem_tagExt.2 ⟨∅, Finset.empty_subset _, g, ?_, Finset.union_empty g⟩
    rw [trFam_empty]
    exact self_subset_ucl G hg
  obtain ⟨u, hu, hle⟩ := hFC _ hGF (negExt_unionClosed hadm)
  have hρ := rho_tagExt Z (trFam G fam typ) hΦ (Finset.disjoint_left.1 hdisj hu)
  rw [sum_rho_trFam G fam typ Z hu] at hρ
  have hlt := hneg u hu
  rw [← hρ] at hlt
  unfold rho at hlt
  have hle' : ((tagExt Z (trFam G fam typ)).card : ℤ) ≤
      2 * (deg (tagExt Z (trFam G fam typ)) u : ℤ) := by
    exact_mod_cast hle
  linarith

/-! ### Explicit tags -/

/-- Tag number `i` of type `j`. -/
def tag (N K j i : ℕ) : ℕ := N + (j + K * i)

/-- Type of a tag. -/
def tagType (N K τ : ℕ) : ℕ := (τ - N) % K

/-- All tags: `cnt j` tags of each type `j ∈ Idx`. -/
def tags (N K : ℕ) (Idx : Finset ℕ) (cnt : ℕ → ℕ) : Finset ℕ :=
  Idx.biUnion fun j => (range (cnt j)).image (tag N K j)

theorem tagType_tag {N K j : ℕ} (hj : j < K) (i : ℕ) : tagType N K (tag N K j i) = j := by
  unfold tagType tag
  rw [Nat.add_sub_cancel_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

theorem tag_injective {N K j : ℕ} (hK : 0 < K) : Function.Injective (tag N K j) := by
  intro i i' h
  unfold tag at h
  have h' : K * i = K * i' := by omega
  exact Nat.eq_of_mul_eq_mul_left hK h'

theorem tagType_mem_of_mem_tags {N K : ℕ} {Idx : Finset ℕ} (hK : ∀ j ∈ Idx, j < K)
    {cnt : ℕ → ℕ} {τ : ℕ} (hτ : τ ∈ tags N K Idx cnt) : tagType N K τ ∈ Idx := by
  unfold tags at hτ
  obtain ⟨j, hj, hτj⟩ := Finset.mem_biUnion.1 hτ
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hτj
  rw [tagType_tag (hK j hj)]
  exact hj

theorem le_of_mem_tags {N K : ℕ} {Idx : Finset ℕ} {cnt : ℕ → ℕ} {τ : ℕ}
    (hτ : τ ∈ tags N K Idx cnt) : N ≤ τ := by
  unfold tags at hτ
  obtain ⟨j, -, hτj⟩ := Finset.mem_biUnion.1 hτ
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hτj
  exact Nat.le_add_right _ _

theorem sum_tags {N K : ℕ} {Idx : Finset ℕ} (hK : ∀ j ∈ Idx, j < K) (hKpos : 0 < K)
    (cnt : ℕ → ℕ) (f : ℕ → ℤ) :
    ∑ τ ∈ tags N K Idx cnt, f (tagType N K τ) = ∑ j ∈ Idx, (cnt j : ℤ) * f j := by
  unfold tags
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_image (fun i _ i' _ h => tag_injective hKpos h)]
    have e : ∀ i ∈ range (cnt j), f (tagType N K (tag N K j i)) = f j := fun i _ => by
      rw [tagType_tag (hK j hj)]
    rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · intro j₁ hj₁ j₂ hj₂ hne
    rw [Finset.mem_coe] at hj₁ hj₂
    refine Finset.disjoint_left.2 fun τ h₁ h₂ => hne ?_
    obtain ⟨i₁, -, e₁⟩ := Finset.mem_image.1 h₁
    obtain ⟨i₂, -, e₂⟩ := Finset.mem_image.1 h₂
    have e : tagType N K (tag N K j₁ i₁) = tagType N K (tag N K j₂ i₂) := by rw [e₁, e₂]
    rwa [tagType_tag (hK j₁ hj₁), tagType_tag (hK j₂ hj₂)] at e

theorem lt_sup_succ {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) : x < s.sup id + 1 :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)

end Basic

/-- Paper Lemma 2.4 (negative certificates), in a form indexed by an arbitrary finite index set:
if admissible families `fam j` and natural multipliers `lam j` give strictly negative total
imbalance at every support point, then `G` is not FC. -/
theorem not_isFC_of_cert (G : Fam) (Idx : Finset ℕ) (fam : ℕ → Fam) (lam : ℕ → ℕ)
    (hadm : ∀ j ∈ Idx, Admissible G (fam j))
    (hneg : ∀ u ∈ supp G, ∑ j ∈ Idx, (lam j : ℤ) * rho (fam j) u < 0) : ¬ IsFC G := by
  have hK : ∀ j ∈ Idx, j < Idx.sup id + 1 := fun j hj => Basic.lt_sup_succ hj
  apply Basic.not_isFC_of_tags G fam (Basic.tagType ((supp G).sup id + 1) (Idx.sup id + 1))
    (Basic.tags ((supp G).sup id + 1) (Idx.sup id + 1) Idx (fun j => ((ucl G).card + 1) * lam j))
  · intro τ hτ
    exact hadm _ (Basic.tagType_mem_of_mem_tags hK hτ)
  · refine Finset.disjoint_left.2 fun u hu hτ => ?_
    have h1 := Basic.le_of_mem_tags hτ
    have h2 := Basic.lt_sup_succ hu
    omega
  · intro u hu
    rw [Basic.sum_tags hK (Nat.succ_pos _) _ (fun j => rho (fam j) u)]
    have hs : ∑ j ∈ Idx, ((((ucl G).card + 1) * lam j : ℕ) : ℤ) * rho (fam j) u =
        (((ucl G).card : ℤ) + 1) * ∑ j ∈ Idx, (lam j : ℤ) * rho (fam j) u := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [hs]
    have h1 := hneg u hu
    have h2 := Basic.rho_le_card (ucl G) u
    have h1' : ∑ j ∈ Idx, (lam j : ℤ) * rho (fam j) u ≤ -1 := by omega
    have h3 : (((ucl G).card : ℤ) + 1) * ∑ j ∈ Idx, (lam j : ℤ) * rho (fam j) u ≤
        (((ucl G).card : ℤ) + 1) * (-1) :=
      mul_le_mul_of_nonneg_left h1' (by positivity)
    linarith

/-- Negative certificate from coatom families. -/
theorem not_isFC_of_coatoms (G : Fam) (lam : ℕ → ℕ)
    (hneg : ∀ u ∈ supp G, ∑ z ∈ supp G, (lam z : ℤ) * rho (coatom G z) u < 0) : ¬ IsFC G :=
  not_isFC_of_cert G (supp G) (coatom G) lam (fun z _ => coatom_admissible G z) hneg

/-- The full cube has zero imbalance. -/
theorem rho_powerset (U : Finset ℕ) {u : ℕ} (hu : u ∈ U) : rho U.powerset u = 0 :=
  Basic.rho_powerset' U hu

/-- `ρ_u(E_z) = -ρ_u(N_z)` where `N_z` is the omitted family. -/
theorem rho_coatom (G : Fam) (z : ℕ) {u : ℕ} (hu : u ∈ supp G) :
    rho (coatom G z) u = - rho (omitted G z) u := by
  have h := Basic.rho_filter_add (supp G).powerset
    (fun A => z ∉ A ∨ ∃ g ∈ G, z ∈ g ∧ g ⊆ A) u
  have hom : omitted G z =
      (supp G).powerset.filter fun A => ¬ (z ∉ A ∨ ∃ g ∈ G, z ∈ g ∧ g ⊆ A) := by
    unfold omitted
    refine Finset.filter_congr fun A _ => ?_
    constructor
    · rintro ⟨hzA, hall⟩ (hz | ⟨g, hg, hzg, hgA⟩)
      · exact hz hzA
      · exact hall g hg hzg hgA
    · intro hn
      refine ⟨?_, fun g hg hzg hgA => hn (Or.inr ⟨g, hg, hzg, hgA⟩)⟩
      by_contra hz
      exact hn (Or.inl hz)
  rw [rho_powerset _ hu] at h
  unfold coatom
  rw [hom]
  linarith

end Results.FcMorrisV2
