import Results.FcMorrisV2.Solution.SunflowerDefs
import Results.FcMorrisV2.Solution.Product

/-!
# Solution/SunflowerNeg: negative direction of Theorem 1.2 (coatom certificate, paper Section 5.1)

For `G = S_t` with support `U = C ⊔ R` (`R = ⋃ P i`) we compute every coatom row
`ρ_u(E_z) = -ρ_u(N_z)` (`N_z` the omitted family, `rho_coatom`) from the decompositions
* `z ∈ C`:   `N_z = (↑{z} \ ↑C) ⊔ F₂`, where `F₂ = {A ⊆ U : C ⊆ A, A contains no whole petal}`
  is a product family (`prodFam`);
* `z ∈ P i`: `N_z = ↑{z} \ ↑(C ∪ P i)`,
where `↑S = {A ⊆ U : S ⊆ A}` (`supF U S`).  With `t = s + 1` the rows are (paper (coatom-rows),
(petal-coatom-rows)):
* `z ∈ C`:   `ρ_z = -(4^t + 3^t)`, `ρ_u = 4^t - 3^t` (`u ∈ C \ {z}`), `ρ_u = 3^{t-1}` (`u ∈ R`);
* `z ∈ P i`: `ρ_z = -7·4^{t-1}`, `ρ_u = 4^{t-1}` (`u ∈ (C ∪ P i) \ {z}`), `ρ_u = 0` (`u ∈ R \ P i`).
The multipliers `6 t 4^{t-1}` (core) and `(t+9) 3^{t-1}` (petals) give total imbalance
`2 t 12^{t-1} (t-9)` at core points and `6·12^{t-1} (t-9)` at petal points, negative for `t ≤ 8`;
`not_isFC_of_coatoms` concludes.
-/

namespace Results.FcMorrisV2

open Finset

namespace SunflowerNeg

/-! ### Imbalance of unions, differences and small families -/

lemma rho_union {A B : Fam} (h : Disjoint A B) (u : ℕ) :
    rho (A ∪ B) u = rho A u + rho B u := by
  have hdeg : deg (A ∪ B) u = deg A u + deg B u := by
    unfold deg
    rw [filter_union]
    exact card_union_of_disjoint (disjoint_filter_filter h)
  unfold rho
  rw [hdeg, card_union_of_disjoint h]
  push_cast
  ring

lemma rho_sdiff {A B : Fam} (h : B ⊆ A) (u : ℕ) :
    rho (A \ B) u = rho A u - rho B u := by
  have key := rho_union (A := A \ B) (B := B) sdiff_disjoint u
  rw [sdiff_union_of_subset h] at key
  linarith

lemma rho_singleton {X : Finset ℕ} {u : ℕ} (hu : u ∈ X) : rho {X} u = 1 := by
  have hdeg : deg {X} u = 1 := by
    unfold deg
    rw [filter_singleton, if_pos hu, card_singleton]
  unfold rho
  rw [hdeg, card_singleton]
  norm_num

lemma rho_erase {B : Fam} {X : Finset ℕ} (hX : X ∈ B) {u : ℕ} (hu : u ∈ X) :
    rho (B.erase X) u = rho B u - 1 := by
  have h1 : ((B.erase X).card : ℤ) + 1 = B.card := by exact_mod_cast card_erase_add_one hX
  have h2 : (deg (B.erase X) u : ℤ) + 1 = deg B u := by
    have h2' : deg (B.erase X) u + 1 = deg B u := by
      unfold deg
      rw [filter_erase]
      exact card_erase_add_one (mem_filter.2 ⟨hX, hu⟩)
    exact_mod_cast h2'
  unfold rho
  linarith

/-! ### Upward families `↑S = {A ⊆ U : S ⊆ A}` -/

/-- Members of `2^U` containing `S`. -/
def supF (U S : Finset ℕ) : Fam := U.powerset.filter fun A => S ⊆ A

lemma mem_supF {U S A : Finset ℕ} : A ∈ supF U S ↔ A ⊆ U ∧ S ⊆ A := by
  rw [supF, mem_filter, mem_powerset]

lemma supF_anti {U S S' : Finset ℕ} (h : S ⊆ S') : supF U S' ⊆ supF U S := by
  intro A hA
  rw [mem_supF] at hA ⊢
  exact ⟨hA.1, h.trans hA.2⟩

lemma card_supF {U S : Finset ℕ} (h : S ⊆ U) : (supF U S).card = 2 ^ (U.card - S.card) := by
  rw [← card_sdiff_of_subset h, ← card_powerset]
  refine card_nbij' (fun A => A \ S) (fun B => B ∪ S) ?_ ?_ ?_ ?_
  · intro A hA
    have hA' := mem_supF.1 (mem_coe.1 hA)
    exact mem_coe.2 (mem_powerset.2 (sdiff_subset_sdiff hA'.1 (Subset.refl S)))
  · intro B hB
    have hB' := mem_powerset.1 (mem_coe.1 hB)
    exact mem_coe.2 (mem_supF.2 ⟨union_subset (hB'.trans sdiff_subset) h, subset_union_right⟩)
  · intro A hA
    exact sdiff_union_of_subset (mem_supF.1 (mem_coe.1 hA)).2
  · intro B hB
    exact union_sdiff_cancel_right
      (disjoint_of_subset_left (mem_powerset.1 (mem_coe.1 hB)) sdiff_disjoint)

lemma rho_supF_of_mem {U S : Finset ℕ} {u : ℕ} (hu : u ∈ S) :
    rho (supF U S) u = (supF U S).card := by
  have hdeg : deg (supF U S) u = (supF U S).card := by
    unfold deg
    rw [filter_true_of_mem fun A hA => (mem_supF.1 hA).2 hu]
  unfold rho
  rw [hdeg]
  ring

lemma rho_supF_of_not_mem {U S : Finset ℕ} (h : S ⊆ U) {u : ℕ} (huU : u ∈ U) (hu : u ∉ S) :
    rho (supF U S) u = 0 := by
  have hins : insert u S ⊆ U := insert_subset huU h
  have hdeg : deg (supF U S) u = (supF U (insert u S)).card := by
    unfold deg
    congr 1
    ext A
    rw [mem_filter, mem_supF, mem_supF, insert_subset_iff]
    tauto
  have hle : (insert u S).card ≤ U.card := card_le_card hins
  have hcard : (insert u S).card = S.card + 1 := card_insert_of_notMem hu
  obtain ⟨m, hm⟩ : ∃ m, U.card - S.card = m + 1 := ⟨U.card - S.card - 1, by omega⟩
  have hm' : U.card - (insert u S).card = m := by omega
  unfold rho
  rw [hdeg, card_supF hins, card_supF h, hm, hm']
  push_cast
  ring

/-! ### Imbalance of a product family -/

/-- Cross-multiplied degree formula: `ρ_u(∏ Q) · |Q j| = ρ_u(Q j) · |∏ Q|` for `u ∈ V j`. -/
lemma rho_prodFam_mul {ι : Type*} [DecidableEq ι] (I : Finset ι) (V : ι → Finset ℕ)
    (hV : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (V i) (V j)) (Q : ι → Fam)
    (hQ : ∀ i ∈ I, Q i ⊆ (V i).powerset) {j : ι} (hj : j ∈ I) {u : ℕ} (hu : u ∈ V j) :
    rho (prodFam I V Q) u * (Q j).card = rho (Q j) u * (prodFam I V Q).card := by
  have hd := prodFam_deg I V hV Q hQ hj hu
  have hm : (Q j).card * ∏ i ∈ I.erase j, (Q i).card = ∏ i ∈ I, (Q i).card :=
    mul_prod_erase I (fun i => (Q i).card) hj
  have hc : (prodFam I V Q).card = (Q j).card * ∏ i ∈ I.erase j, (Q i).card := by
    rw [hm]
    exact prodFam_card I V hV Q hQ
  unfold rho
  rw [hd, hc]
  push_cast
  ring

/-- Index finset for the core-and-petals decomposition: `none` is the core, `some k` petal `k`. -/
def idx (t : ℕ) : Finset (Option (Fin t)) := insert none (univ.image some)

lemma mem_idx {t : ℕ} (o : Option (Fin t)) : o ∈ idx t := by
  cases o with
  | none => exact mem_insert_self _ _
  | some k => exact mem_insert_of_mem (mem_image_of_mem _ (mem_univ k))

lemma prod_idx {t : ℕ} (f : Option (Fin t) → ℕ) :
    ∏ o ∈ idx t, f o = f none * ∏ k : Fin t, f (some k) := by
  have h1 : (none : Option (Fin t)) ∉ univ.image some := by
    intro h
    obtain ⟨k, -, hk⟩ := mem_image.1 h
    exact Option.some_ne_none k hk
  have h2 : Set.InjOn (some : Fin t → Option (Fin t)) ↑(univ : Finset (Fin t)) :=
    fun x _ y _ hxy => Option.some_injective _ hxy
  rw [idx, prod_insert h1, prod_image h2]

/-- Components: the core `C` and the petals `P k`. -/
def comp {t : ℕ} (C : Finset ℕ) (P : Fin t → Finset ℕ) (o : Option (Fin t)) : Finset ℕ :=
  o.elim C P

/-- Traces of `F₂`: the full core, and a proper subset of every petal. -/
def trF2 {t : ℕ} (C : Finset ℕ) (P : Fin t → Finset ℕ) (o : Option (Fin t)) : Fam :=
  o.elim {C} fun k => (P k).powerset.erase (P k)

/-- `F₂ = {A ⊆ U : C ⊆ A, no whole petal in A}`. -/
def F2 {t : ℕ} (C : Finset ℕ) (P : Fin t → Finset ℕ) : Fam :=
  prodFam (idx t) (comp C P) (trF2 C P)

lemma biUnion_comp {t : ℕ} (C : Finset ℕ) (P : Fin t → Finset ℕ) :
    (idx t).biUnion (comp C P) = C ∪ univ.biUnion P := by
  ext u
  rw [mem_biUnion, mem_union, mem_biUnion]
  constructor
  · rintro ⟨o, -, ho⟩
    cases o with
    | none => exact Or.inl ho
    | some k => exact Or.inr ⟨k, mem_univ k, ho⟩
  · rintro (h | ⟨k, -, hk⟩)
    · exact ⟨none, mem_idx _, h⟩
    · exact ⟨some k, mem_idx _, hk⟩

lemma comp_disj {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ} (hd : SunflowerData t C P) :
    ∀ i ∈ idx t, ∀ j ∈ idx t, i ≠ j → Disjoint (comp C P i) (comp C P j) := by
  intro i _ j _ hij
  cases i with
  | none =>
    cases j with
    | none => exact absurd rfl hij
    | some l => exact hd.hCP l
  | some k =>
    cases j with
    | none => exact (hd.hCP k).symm
    | some l => exact hd.hPP k l fun h => hij (congrArg some h)

lemma trF2_sub {t : ℕ} (C : Finset ℕ) (P : Fin t → Finset ℕ) :
    ∀ i ∈ idx t, trF2 C P i ⊆ (comp C P i).powerset := by
  intro i _
  cases i with
  | none => exact singleton_subset_iff.2 (mem_powerset_self C)
  | some k => exact erase_subset _ _

lemma mem_F2 {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ} {A : Finset ℕ} :
    A ∈ F2 C P ↔ A ⊆ C ∪ univ.biUnion P ∧ C ⊆ A ∧ ∀ k, ¬ P k ⊆ A := by
  rw [F2, Product.mem_prodFam, biUnion_comp]
  constructor
  · rintro ⟨hsub, h⟩
    refine ⟨hsub, ?_, fun k hk => ?_⟩
    · have h0 : A ∩ C ∈ ({C} : Fam) := h none (mem_idx _)
      exact inter_eq_right.1 (mem_singleton.1 h0)
    · have h1 : A ∩ P k ∈ (P k).powerset.erase (P k) := h (some k) (mem_idx _)
      exact (mem_erase.1 h1).1 (inter_eq_right.2 hk)
  · rintro ⟨hsub, hC, hP⟩
    refine ⟨hsub, fun o _ => ?_⟩
    cases o with
    | none => exact mem_singleton.2 (inter_eq_right.2 hC)
    | some k =>
      exact mem_erase.2 ⟨fun h => hP k (inter_eq_right.1 h), mem_powerset.2 inter_subset_right⟩

lemma card_trF2_some {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ} (hd : SunflowerData t C P)
    (k : Fin t) : (trF2 C P (some k)).card = 3 := by
  show ((P k).powerset.erase (P k)).card = 3
  rw [card_erase_of_mem (mem_powerset_self _), card_powerset, hd.hP k]
  norm_num

lemma card_F2 {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ} (hd : SunflowerData t C P) :
    (F2 C P).card = 3 ^ t := by
  rw [F2, prodFam_card (idx t) (comp C P) (comp_disj hd) (trF2 C P) (trF2_sub C P), prod_idx]
  have h1 : (trF2 C P none).card = 1 := card_singleton C
  rw [h1, one_mul, prod_congr rfl fun k _ => card_trF2_some hd k, prod_const, card_univ,
    Fintype.card_fin]

lemma rho_F2_core {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ} (hd : SunflowerData t C P)
    {u : ℕ} (hu : u ∈ C) : rho (F2 C P) u = 3 ^ t := by
  have key : rho (F2 C P) u * ((trF2 C P none).card : ℤ) =
      rho (trF2 C P none) u * ((F2 C P).card : ℤ) :=
    rho_prodFam_mul (idx t) (comp C P) (comp_disj hd) (trF2 C P) (trF2_sub C P) (mem_idx none) hu
  have h1 : (trF2 C P none).card = 1 := card_singleton C
  have h2 : rho (trF2 C P none) u = 1 := rho_singleton hu
  rw [h1, h2, card_F2 hd] at key
  push_cast at key
  linarith

lemma rho_F2_petal {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ} (hd : SunflowerData t C P)
    {i : Fin t} {u : ℕ} (hu : u ∈ P i) : rho (F2 C P) u * 3 = -3 ^ t := by
  have key : rho (F2 C P) u * ((trF2 C P (some i)).card : ℤ) =
      rho (trF2 C P (some i)) u * ((F2 C P).card : ℤ) :=
    rho_prodFam_mul (idx t) (comp C P) (comp_disj hd) (trF2 C P) (trF2_sub C P)
      (mem_idx (some i)) hu
  have h2 : rho (trF2 C P (some i)) u = -1 := by
    show rho ((P i).powerset.erase (P i)) u = -1
    rw [rho_erase (mem_powerset_self _) hu, rho_powerset _ hu]
    norm_num
  rw [card_trF2_some hd i, h2, card_F2 hd] at key
  push_cast at key
  linarith

/-! ### The sunflower: support and omitted families -/

lemma supp_eq {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ} (ht : 0 < t) :
    supp (sunflowerCfg t C P) = C ∪ univ.biUnion P := by
  ext u
  unfold supp sunflowerCfg
  rw [mem_biUnion, mem_union, mem_biUnion]
  constructor
  · rintro ⟨g, hg, hug⟩
    obtain ⟨i, -, rfl⟩ := mem_image.1 hg
    rcases mem_union.1 hug with h | h
    · exact Or.inl h
    · exact Or.inr ⟨i, mem_univ i, h⟩
  · rintro (h | ⟨i, -, h⟩)
    · exact ⟨C ∪ P ⟨0, ht⟩, mem_image_of_mem _ (mem_univ _), mem_union_left _ h⟩
    · exact ⟨C ∪ P i, mem_image_of_mem _ (mem_univ _), mem_union_right _ h⟩

lemma disj_core_petals {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ}
    (hd : SunflowerData t C P) : Disjoint C (univ.biUnion P) :=
  (disjoint_biUnion_right C univ P).2 fun i _ => hd.hCP i

lemma card_petals {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ} (hd : SunflowerData t C P) :
    (univ.biUnion P).card = 2 * t := by
  have hpw : ((univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint P := by
    intro i _ j _ hij
    exact hd.hPP i j hij
  rw [card_biUnion hpw, sum_congr rfl fun i _ => hd.hP i, sum_const, card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul, mul_comm]

lemma mem_omitted_iff {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ} {z : ℕ} {A : Finset ℕ} :
    A ∈ omitted (sunflowerCfg t C P) z ↔
      A ⊆ supp (sunflowerCfg t C P) ∧ z ∈ A ∧ ∀ i, z ∈ C ∪ P i → ¬ C ∪ P i ⊆ A := by
  unfold omitted
  rw [mem_filter, mem_powerset]
  constructor
  · rintro ⟨hA, hz, h⟩
    exact ⟨hA, hz, fun i hi => h (C ∪ P i) (mem_image_of_mem _ (mem_univ i)) hi⟩
  · rintro ⟨hA, hz, h⟩
    refine ⟨hA, hz, fun g hg hzg => ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_image.1 hg
    exact h i hzg

lemma omitted_core {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ} (ht : 0 < t) {z : ℕ}
    (hz : z ∈ C) :
    omitted (sunflowerCfg t C P) z =
      (supF (supp (sunflowerCfg t C P)) {z} \ supF (supp (sunflowerCfg t C P)) C) ∪ F2 C P := by
  ext A
  rw [mem_omitted_iff, mem_union, mem_sdiff, mem_supF, mem_supF, mem_F2,
    ← supp_eq (C := C) (P := P) ht, singleton_subset_iff]
  constructor
  · rintro ⟨hAU, hzA, hall⟩
    by_cases hCA : C ⊆ A
    · exact Or.inr ⟨hAU, hCA, fun k hk => hall k (mem_union_left _ hz) (union_subset hCA hk)⟩
    · exact Or.inl ⟨⟨hAU, hzA⟩, fun h => hCA h.2⟩
  · rintro (⟨⟨hAU, hzA⟩, hn⟩ | ⟨hAU, hCA, hP⟩)
    · exact ⟨hAU, hzA, fun i _ h => hn ⟨hAU, (union_subset_iff.1 h).1⟩⟩
    · exact ⟨hAU, hCA hz, fun i _ h => hP i (union_subset_iff.1 h).2⟩

lemma disj_core_parts {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ} {U : Finset ℕ} {z : ℕ} :
    Disjoint (supF U {z} \ supF U C) (F2 C P) := by
  rw [disjoint_left]
  intro A hA hA2
  rw [mem_sdiff, mem_supF, mem_supF] at hA
  exact hA.2 ⟨hA.1.1, (mem_F2.1 hA2).2.1⟩

lemma omitted_petal {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ} (hd : SunflowerData t C P)
    {i : Fin t} {z : ℕ} (hz : z ∈ P i) :
    omitted (sunflowerCfg t C P) z =
      supF (supp (sunflowerCfg t C P)) {z} \ supF (supp (sunflowerCfg t C P)) (C ∪ P i) := by
  ext A
  rw [mem_omitted_iff, mem_sdiff, mem_supF, mem_supF, singleton_subset_iff]
  constructor
  · rintro ⟨hAU, hzA, hall⟩
    exact ⟨⟨hAU, hzA⟩, fun h => hall i (mem_union_right _ hz) h.2⟩
  · rintro ⟨⟨hAU, hzA⟩, hn⟩
    refine ⟨hAU, hzA, fun j hzj h => ?_⟩
    have hji : j = i := by
      by_contra hne
      rcases mem_union.1 hzj with h' | h'
      · exact disjoint_left.1 (hd.hCP i) h' hz
      · exact disjoint_left.1 (hd.hPP j i hne) h' hz
    subst hji
    exact hn ⟨hAU, h⟩

/-! ### The coatom rows (with `t = s + 1`) -/

section rows

variable {s : ℕ} {C : Finset ℕ} {P : Fin (s + 1) → Finset ℕ}

lemma card_supp (hd : SunflowerData (s + 1) C P) :
    (supp (sunflowerCfg (s + 1) C P)).card = 2 * s + 4 := by
  rw [supp_eq (Nat.succ_pos s), card_union_of_disjoint (disj_core_petals hd), hd.hC,
    card_petals hd]
  ring

lemma core_mem_supp {u : ℕ} (hu : u ∈ C) : u ∈ supp (sunflowerCfg (s + 1) C P) := by
  rw [supp_eq (Nat.succ_pos s)]
  exact mem_union_left _ hu

lemma petal_mem_supp {i : Fin (s + 1)} {u : ℕ} (hu : u ∈ P i) :
    u ∈ supp (sunflowerCfg (s + 1) C P) := by
  rw [supp_eq (Nat.succ_pos s)]
  exact mem_union_right _ (mem_biUnion.2 ⟨i, mem_univ i, hu⟩)

lemma cast_two_pow (s k : ℕ) : (((2 : ℕ) ^ (2 * s + k) : ℕ) : ℤ) = 2 ^ k * 4 ^ s := by
  push_cast
  rw [pow_add, pow_mul, mul_comm]
  norm_num

lemma card_supF_singleton (hd : SunflowerData (s + 1) C P) {z : ℕ}
    (hz : z ∈ supp (sunflowerCfg (s + 1) C P)) :
    ((supF (supp (sunflowerCfg (s + 1) C P)) {z}).card : ℤ) = 8 * 4 ^ s := by
  rw [card_supF (singleton_subset_iff.2 hz), card_supp hd, card_singleton,
    show 2 * s + 4 - 1 = 2 * s + 3 by omega, cast_two_pow]
  norm_num

lemma card_supF_core (hd : SunflowerData (s + 1) C P) :
    ((supF (supp (sunflowerCfg (s + 1) C P)) C).card : ℤ) = 4 * 4 ^ s := by
  have hCU : C ⊆ supp (sunflowerCfg (s + 1) C P) := fun u hu => core_mem_supp hu
  rw [card_supF hCU, card_supp hd, hd.hC, show 2 * s + 4 - 2 = 2 * s + 2 by omega,
    cast_two_pow]
  norm_num

lemma block_sub_supp (i : Fin (s + 1)) : C ∪ P i ⊆ supp (sunflowerCfg (s + 1) C P) :=
  union_subset (fun _ hu => core_mem_supp hu) (fun _ hu => petal_mem_supp hu)

lemma card_supF_block (hd : SunflowerData (s + 1) C P) (i : Fin (s + 1)) :
    ((supF (supp (sunflowerCfg (s + 1) C P)) (C ∪ P i)).card : ℤ) = 4 ^ s := by
  rw [card_supF (block_sub_supp i), card_supp hd, card_union_of_disjoint (hd.hCP i), hd.hC,
    hd.hP i, show 2 * s + 4 - (2 + 2) = 2 * s + 0 by omega, cast_two_pow]
  norm_num

/-- Core coatom, diagonal entry: `ρ_z(E_z) = -(4^t + 3^t)`. -/
lemma row_core_self (hd : SunflowerData (s + 1) C P) {z : ℕ} (hz : z ∈ C) :
    rho (coatom (sunflowerCfg (s + 1) C P) z) z = -(4 * 4 ^ s + 3 * 3 ^ s) := by
  rw [rho_coatom _ z (core_mem_supp (P := P) hz), omitted_core (Nat.succ_pos s) hz,
    rho_union disj_core_parts, rho_sdiff (supF_anti (singleton_subset_iff.2 hz)),
    rho_supF_of_mem (mem_singleton_self z), rho_supF_of_mem hz,
    card_supF_singleton hd (core_mem_supp hz), card_supF_core hd, rho_F2_core hd hz]
  ring

/-- Core coatom, other core point: `ρ_u(E_z) = 4^t - 3^t`. -/
lemma row_core_other (hd : SunflowerData (s + 1) C P) {z u : ℕ} (hz : z ∈ C) (hu : u ∈ C)
    (huz : u ≠ z) :
    rho (coatom (sunflowerCfg (s + 1) C P) z) u = 4 * 4 ^ s - 3 * 3 ^ s := by
  have hnot : u ∉ ({z} : Finset ℕ) := by
    rw [mem_singleton]
    exact huz
  rw [rho_coatom _ z (core_mem_supp (P := P) hu), omitted_core (Nat.succ_pos s) hz,
    rho_union disj_core_parts, rho_sdiff (supF_anti (singleton_subset_iff.2 hz)),
    rho_supF_of_not_mem (singleton_subset_iff.2 (core_mem_supp hz)) (core_mem_supp hu) hnot,
    rho_supF_of_mem hu, card_supF_core hd, rho_F2_core hd hu]
  ring

/-- Core coatom, petal point: `ρ_u(E_z) = 3^{t-1}`. -/
lemma row_core_petal (hd : SunflowerData (s + 1) C P) {z u : ℕ} {i : Fin (s + 1)} (hz : z ∈ C)
    (hu : u ∈ P i) :
    rho (coatom (sunflowerCfg (s + 1) C P) z) u = 3 ^ s := by
  have huC : u ∉ C := fun h => disjoint_left.1 (hd.hCP i) h hu
  have hnot : u ∉ ({z} : Finset ℕ) := by
    rw [mem_singleton]
    rintro rfl
    exact huC hz
  have hF := rho_F2_petal hd hu
  rw [rho_coatom _ z (petal_mem_supp hu), omitted_core (Nat.succ_pos s) hz,
    rho_union disj_core_parts, rho_sdiff (supF_anti (singleton_subset_iff.2 hz)),
    rho_supF_of_not_mem (singleton_subset_iff.2 (core_mem_supp hz)) (petal_mem_supp hu) hnot,
    rho_supF_of_not_mem (fun _ hv => core_mem_supp hv) (petal_mem_supp hu) huC]
  rw [pow_succ] at hF
  linarith

/-- Petal coatom, diagonal entry: `ρ_z(E_z) = -7·4^{t-1}`. -/
lemma row_petal_self (hd : SunflowerData (s + 1) C P) {i : Fin (s + 1)} {z : ℕ}
    (hz : z ∈ P i) :
    rho (coatom (sunflowerCfg (s + 1) C P) z) z = -(7 * 4 ^ s) := by
  rw [rho_coatom _ z (petal_mem_supp hz), omitted_petal hd hz,
    rho_sdiff (supF_anti (singleton_subset_iff.2 (mem_union_right _ hz))),
    rho_supF_of_mem (mem_singleton_self z), rho_supF_of_mem (mem_union_right _ hz),
    card_supF_singleton hd (petal_mem_supp hz), card_supF_block hd i]
  ring

/-- Petal coatom, other point of its four-set: `ρ_u(E_z) = 4^{t-1}`. -/
lemma row_petal_block (hd : SunflowerData (s + 1) C P) {i : Fin (s + 1)} {z u : ℕ}
    (hz : z ∈ P i) (hu : u ∈ C ∪ P i) (huz : u ≠ z) :
    rho (coatom (sunflowerCfg (s + 1) C P) z) u = 4 ^ s := by
  have huU : u ∈ supp (sunflowerCfg (s + 1) C P) := block_sub_supp i hu
  have hnot : u ∉ ({z} : Finset ℕ) := by
    rw [mem_singleton]
    exact huz
  rw [rho_coatom _ z huU, omitted_petal hd hz,
    rho_sdiff (supF_anti (singleton_subset_iff.2 (mem_union_right _ hz))),
    rho_supF_of_not_mem (singleton_subset_iff.2 (petal_mem_supp hz)) huU hnot,
    rho_supF_of_mem hu, card_supF_block hd i]
  ring

/-- Petal coatom, point of another petal: `ρ_u(E_z) = 0`. -/
lemma row_petal_other (hd : SunflowerData (s + 1) C P) {i j : Fin (s + 1)} {z u : ℕ}
    (hz : z ∈ P i) (hu : u ∈ P j) (hij : i ≠ j) :
    rho (coatom (sunflowerCfg (s + 1) C P) z) u = 0 := by
  have huC : u ∉ C := fun h => disjoint_left.1 (hd.hCP j) h hu
  have huPi : u ∉ P i := fun h => disjoint_left.1 (hd.hPP i j hij) h hu
  have hnot : u ∉ ({z} : Finset ℕ) := by
    rw [mem_singleton]
    rintro rfl
    exact huPi hz
  have hblock : u ∉ C ∪ P i := by
    rw [mem_union]
    rintro (h | h)
    · exact huC h
    · exact huPi h
  rw [rho_coatom _ z (petal_mem_supp hu), omitted_petal hd hz,
    rho_sdiff (supF_anti (singleton_subset_iff.2 (mem_union_right _ hz))),
    rho_supF_of_not_mem (singleton_subset_iff.2 (petal_mem_supp hz)) (petal_mem_supp hu) hnot,
    rho_supF_of_not_mem (block_sub_supp i) (petal_mem_supp hu) hblock]
  ring

end rows

/-! ### The certificate -/

/-- Multipliers: `6 t 4^{t-1}` on core points and `(t + 9) 3^{t-1}` elsewhere (`t = s + 1`). -/
def lam (s : ℕ) (C : Finset ℕ) (z : ℕ) : ℕ :=
  if z ∈ C then 6 * (s + 1) * 4 ^ s else (s + 10) * 3 ^ s

lemma lam_core {s : ℕ} {C : Finset ℕ} {z : ℕ} (hz : z ∈ C) :
    (lam s C z : ℤ) = 6 * (s + 1) * 4 ^ s := by
  rw [lam, if_pos hz]
  push_cast
  ring

lemma lam_petal {s : ℕ} {C : Finset ℕ} {z : ℕ} (hz : z ∉ C) :
    (lam s C z : ℤ) = (s + 10) * 3 ^ s := by
  rw [lam, if_neg hz]
  push_cast
  ring

theorem not_isFC_aux {s : ℕ} {C : Finset ℕ} {P : Fin (s + 1) → Finset ℕ}
    (hd : SunflowerData (s + 1) C P) (hs : s ≤ 7) : ¬ IsFC (sunflowerCfg (s + 1) C P) := by
  refine not_isFC_of_coatoms _ (lam s C) fun u hu => ?_
  have hsupp := supp_eq (C := C) (P := P) (Nat.succ_pos s)
  have hdisj := disj_core_petals hd
  have hx : (0 : ℤ) < 4 ^ s := by positivity
  have hy : (0 : ℤ) < 3 ^ s := by positivity
  have hxy : (0 : ℤ) < 4 ^ s * 3 ^ s := mul_pos hx hy
  have hs' : (s : ℤ) ≤ 7 := by exact_mod_cast hs
  rw [hsupp, sum_union hdisj]
  rw [hsupp, mem_union] at hu
  rcases hu with hu | hu
  · -- `u` is a core point
    have hterm : ∀ z ∈ C.erase u,
        (lam s C z : ℤ) * rho (coatom (sunflowerCfg (s + 1) C P) z) u =
          6 * (s + 1) * 4 ^ s * (4 * 4 ^ s - 3 * 3 ^ s) := by
      intro z hz
      rw [lam_core (mem_of_mem_erase hz),
        row_core_other hd (mem_of_mem_erase hz) hu (ne_of_mem_erase hz).symm]
    have hC : ∑ z ∈ C, (lam s C z : ℤ) * rho (coatom (sunflowerCfg (s + 1) C P) z) u =
        6 * (s + 1) * 4 ^ s * (-(4 * 4 ^ s + 3 * 3 ^ s)) +
          6 * (s + 1) * 4 ^ s * (4 * 4 ^ s - 3 * 3 ^ s) := by
      rw [← add_sum_erase C _ hu, lam_core hu, row_core_self hd hu, sum_congr rfl hterm,
        sum_const, card_erase_of_mem hu, hd.hC]
      norm_num
    have hterm' : ∀ z ∈ univ.biUnion P,
        (lam s C z : ℤ) * rho (coatom (sunflowerCfg (s + 1) C P) z) u =
          (s + 10) * 3 ^ s * 4 ^ s := by
      intro z hz
      obtain ⟨i, -, hzi⟩ := mem_biUnion.1 hz
      have huz : u ≠ z := by
        rintro rfl
        exact disjoint_left.1 hdisj hu hz
      rw [lam_petal (disjoint_right.1 hdisj hz), row_petal_block hd hzi (mem_union_left _ hu) huz]
    have hR : ∑ z ∈ univ.biUnion P, (lam s C z : ℤ) * rho (coatom (sunflowerCfg (s + 1) C P) z) u =
        (2 * (s + 1) : ℕ) * ((s + 10) * 3 ^ s * 4 ^ s) := by
      rw [sum_congr rfl hterm', sum_const, card_petals hd, nsmul_eq_mul]
    rw [hC, hR]
    have key : (6 * (s + 1) * 4 ^ s * (-(4 * 4 ^ s + 3 * 3 ^ s)) +
          6 * (s + 1) * 4 ^ s * (4 * 4 ^ s - 3 * 3 ^ s) +
          ((2 * (s + 1) : ℕ) : ℤ) * ((s + 10) * 3 ^ s * 4 ^ s) : ℤ) =
        (4 ^ s * 3 ^ s) * ((s + 1) * (2 * s - 16)) := by
      push_cast
      ring
    rw [key]
    exact mul_neg_of_pos_of_neg hxy (mul_neg_of_pos_of_neg (by positivity) (by linarith))
  · -- `u` is a petal point
    obtain ⟨i, -, hui⟩ := mem_biUnion.1 hu
    have huC : u ∉ C := disjoint_right.1 hdisj hu
    have hterm : ∀ z ∈ C, (lam s C z : ℤ) * rho (coatom (sunflowerCfg (s + 1) C P) z) u =
        6 * (s + 1) * 4 ^ s * 3 ^ s := by
      intro z hz
      rw [lam_core hz, row_core_petal hd hz hui]
    have hC : ∑ z ∈ C, (lam s C z : ℤ) * rho (coatom (sunflowerCfg (s + 1) C P) z) u =
        (2 : ℕ) * (6 * (s + 1) * 4 ^ s * 3 ^ s) := by
      rw [sum_congr rfl hterm, sum_const, hd.hC, nsmul_eq_mul]
    have hPR : P i ⊆ univ.biUnion P := subset_biUnion_of_mem P (mem_univ i)
    have h0 : ∑ z ∈ univ.biUnion P \ P i,
        (lam s C z : ℤ) * rho (coatom (sunflowerCfg (s + 1) C P) z) u = 0 := by
      refine sum_eq_zero fun z hz => ?_
      obtain ⟨hzR, hzi⟩ := mem_sdiff.1 hz
      obtain ⟨j, -, hzj⟩ := mem_biUnion.1 hzR
      have hji : j ≠ i := by
        rintro rfl
        exact hzi hzj
      rw [row_petal_other hd hzj hui hji, mul_zero]
    have hterm' : ∀ z ∈ (P i).erase u,
        (lam s C z : ℤ) * rho (coatom (sunflowerCfg (s + 1) C P) z) u =
          (s + 10) * 3 ^ s * 4 ^ s := by
      intro z hz
      have hzi := mem_of_mem_erase hz
      have hzC : z ∉ C := disjoint_right.1 hdisj (mem_biUnion.2 ⟨i, mem_univ i, hzi⟩)
      rw [lam_petal hzC, row_petal_block hd hzi (mem_union_right _ hui) (ne_of_mem_erase hz).symm]
    have hR : ∑ z ∈ univ.biUnion P, (lam s C z : ℤ) * rho (coatom (sunflowerCfg (s + 1) C P) z) u =
        (s + 10) * 3 ^ s * (-(7 * 4 ^ s)) + (s + 10) * 3 ^ s * 4 ^ s := by
      rw [← sum_sdiff hPR, h0, zero_add, ← add_sum_erase (P i) _ hui, lam_petal huC,
        row_petal_self hd hui, sum_congr rfl hterm', sum_const, card_erase_of_mem hui, hd.hP i]
      norm_num
    rw [hC, hR]
    have key : (((2 : ℕ) : ℤ) * (6 * (s + 1) * 4 ^ s * 3 ^ s) +
          ((s + 10) * 3 ^ s * (-(7 * 4 ^ s)) + (s + 10) * 3 ^ s * 4 ^ s) : ℤ) =
        (4 ^ s * 3 ^ s) * (6 * s - 48) := by
      push_cast
      ring
    rw [key]
    exact mul_neg_of_pos_of_neg hxy (by linarith)

end SunflowerNeg

/-- Negative direction of Theorem 1.2: `S_t` is not FC for `1 ≤ t ≤ 8`. -/
theorem sunflower_not_isFC {t : ℕ} {C : Finset ℕ} {P : Fin t → Finset ℕ}
    (hd : SunflowerData t C P) (h1 : 1 ≤ t) (h8 : t ≤ 8) : ¬ IsFC (sunflowerCfg t C P) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  exact SunflowerNeg.not_isFC_aux hd (by omega)

end Results.FcMorrisV2
