import Results.FcMorrisV2.Solution.Basic
import Results.FcMorrisV2.Solution.Product

/-!
# Solution/Triples: disjoint triples are not FC (paper Corollary B.5, case `k = 3`)
-/

namespace Results.FcMorrisV2

open Finset

/-- `r` pairwise disjoint triples `{3i, 3i+1, 3i+2}`. -/
def disjointTriples (r : ℕ) : Fam :=
  (range r).image fun i => ({3 * i, 3 * i + 1, 3 * i + 2} : Finset ℕ)

namespace Triples

/-! ### The triples -/

/-- The triple `T_i = {3i, 3i+1, 3i+2}`. -/
def tri (i : ℕ) : Finset ℕ := {3 * i, 3 * i + 1, 3 * i + 2}

theorem mem_tri {i x : ℕ} : x ∈ tri i ↔ x / 3 = i := by
  simp only [tri, mem_insert, mem_singleton]
  omega

theorem tri_card (i : ℕ) : (tri i).card = 3 := by
  have h1 : 3 * i ∉ ({3 * i + 1, 3 * i + 2} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton]; omega
  rw [tri, card_insert_of_notMem h1, card_pair (by omega)]

theorem tri_injective : Function.Injective tri := by
  intro i j h
  have h1 : 3 * i ∈ tri i := mem_tri.2 (by omega)
  rw [h, mem_tri] at h1
  omega

theorem tri_pairwise (r : ℕ) :
    ∀ i ∈ range r, ∀ j ∈ range r, i ≠ j → Disjoint (tri i) (tri j) := by
  intro i _ j _ hij
  rw [disjoint_left]
  intro x hx hx'
  rw [mem_tri] at hx hx'
  exact hij (hx.symm.trans hx')

theorem mem_disjointTriples {r : ℕ} {g : Finset ℕ} :
    g ∈ disjointTriples r ↔ ∃ i < r, g = tri i := by
  simp only [disjointTriples, mem_image, mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem biUnion_tri (r : ℕ) : (range r).biUnion tri = range (3 * r) := by
  ext x
  rw [mem_biUnion, mem_range]
  constructor
  · rintro ⟨i, hi, hx⟩
    rw [mem_range] at hi
    rw [mem_tri] at hx
    omega
  · intro hx
    exact ⟨x / 3, mem_range.2 (by omega), mem_tri.2 rfl⟩

theorem supp_disjointTriples (r : ℕ) : supp (disjointTriples r) = range (3 * r) := by
  rw [← biUnion_tri r]
  ext x
  rw [supp, mem_biUnion, mem_biUnion]
  constructor
  · rintro ⟨g, hg, hx⟩
    obtain ⟨i, hi, rfl⟩ := mem_disjointTriples.1 hg
    exact ⟨i, mem_range.2 hi, hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨tri i, mem_disjointTriples.2 ⟨i, mem_range.1 hi, rfl⟩, hx⟩

/-! ### The local trace family on the triple of `z` -/

/-- Traces on `T_i` containing `z` but not all of `T_i`. -/
def loc (i z : ℕ) : Fam := (tri i).powerset.filter fun B => z ∈ B ∧ ¬ tri i ⊆ B

/-- Trace families of the omitted family `N_z`: the local family on the triple of `z`, full
cubes on the other triples. -/
def Qz (z j : ℕ) : Fam := if j = z / 3 then loc j z else (tri j).powerset

theorem Qz_sub (z : ℕ) (I : Finset ℕ) : ∀ j ∈ I, Qz z j ⊆ (tri j).powerset := by
  intro j _
  unfold Qz
  split_ifs
  · exact filter_subset _ _
  · exact Subset.rfl

/-- Translation by `a` as an embedding. -/
def shift (a : ℕ) : ℕ ↪ ℕ := ⟨fun x => a + x, fun _ _ h => Nat.add_left_cancel h⟩

theorem tri_eq_map (i : ℕ) : tri i = ({0, 1, 2} : Finset ℕ).map (shift (3 * i)) := by
  simp only [tri, map_insert, map_singleton]
  rfl

theorem powerset_map' (f : ℕ ↪ ℕ) (s : Finset ℕ) :
    (s.map f).powerset = s.powerset.map (mapEmbedding f).toEmbedding := by
  ext t
  simp only [mem_powerset, mem_map, RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
  constructor
  · intro ht
    refine ⟨s.filter (fun x => f x ∈ t), filter_subset _ _, ?_⟩
    ext y
    simp only [mem_map, mem_filter]
    constructor
    · rintro ⟨x, ⟨_, hx⟩, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, hx, rfl⟩ := mem_map.1 (ht hy)
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact map_subset_map.2 hu

/-- The local family is a translate of a concrete family on `{0,1,2}`. -/
theorem loc_eq_map (i t : ℕ) :
    loc i (3 * i + t) =
      ((({0, 1, 2} : Finset ℕ).powerset.filter fun B => t ∈ B ∧ ¬ ({0, 1, 2} : Finset ℕ) ⊆ B)).map
        (mapEmbedding (shift (3 * i))).toEmbedding := by
  rw [loc, tri_eq_map, powerset_map', filter_map]
  congr 1
  apply filter_congr
  intro B _
  simp only [Function.comp, RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
  rw [show 3 * i + t = shift (3 * i) t from rfl, mem_map', map_subset_map]

theorem loc_card (i t : ℕ) (ht : t < 3) : (loc i (3 * i + t)).card = 3 := by
  rw [loc_eq_map, card_map]
  obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  all_goals decide

theorem loc_deg (i t s : ℕ) (ht : t < 3) (hs : s < 3) :
    deg (loc i (3 * i + t)) (3 * i + s) = if s = t then 3 else 1 := by
  rw [deg, loc_eq_map, filter_map, card_map]
  have h : ∀ B ∈ (({0, 1, 2} : Finset ℕ).powerset.filter
      fun B => t ∈ B ∧ ¬ ({0, 1, 2} : Finset ℕ) ⊆ B),
      ((fun A => 3 * i + s ∈ A) ∘ (mapEmbedding (shift (3 * i))).toEmbedding) B ↔ s ∈ B := by
    intro B _
    simp only [Function.comp, RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
    rw [show 3 * i + s = shift (3 * i) s from rfl, mem_map']
  rw [filter_congr h]
  obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  all_goals
    obtain rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 := by omega
    all_goals decide

/-! ### The omitted family as a product family -/

theorem omitted_eq {r z : ℕ} (hz : z < 3 * r) :
    omitted (disjointTriples r) z = prodFam (range r) tri (Qz z) := by
  ext A
  rw [Product.mem_prodFam, biUnion_tri, omitted, mem_filter, mem_powerset, supp_disjointTriples]
  have hzi : z ∈ tri (z / 3) := mem_tri.2 rfl
  have hiz : z / 3 < r := by omega
  constructor
  · rintro ⟨hA, hzA, hg⟩
    refine ⟨hA, fun j _ => ?_⟩
    by_cases hjz : j = z / 3
    · rw [Qz, if_pos hjz, hjz, loc, mem_filter, mem_powerset]
      refine ⟨inter_subset_right, mem_inter.2 ⟨hzA, hzi⟩, fun h => ?_⟩
      exact hg (tri (z / 3)) (mem_disjointTriples.2 ⟨z / 3, hiz, rfl⟩) hzi
        (h.trans inter_subset_left)
    · rw [Qz, if_neg hjz, mem_powerset]
      exact inter_subset_right
  · rintro ⟨hA, h⟩
    have hloc := h (z / 3) (mem_range.2 hiz)
    rw [Qz, if_pos rfl, loc, mem_filter] at hloc
    refine ⟨hA, (mem_inter.1 hloc.2.1).1, ?_⟩
    intro g hg hzg hgA
    obtain ⟨j, _, rfl⟩ := mem_disjointTriples.1 hg
    have hj : j = z / 3 := (mem_tri.1 hzg).symm
    subst hj
    exact hloc.2.2 (subset_inter hgA Subset.rfl)

/-! ### The imbalance rows -/

/-- Closed form of the rows: `ρ_u(E_z) = P · ([z, u in the same triple] - 4 [z = u])`. -/
theorem rho_row {r z u : ℕ} (hz : z < 3 * r) (hu : u < 3 * r) :
    rho (coatom (disjointTriples r) z) u =
      ((∏ l ∈ (range r).erase (u / 3), (tri l).powerset.card : ℕ) : ℤ) *
        ((if z / 3 = u / 3 then 1 else 0) - (if z = u then 4 else 0)) := by
  have huS : u ∈ supp (disjointTriples r) := by
    rw [supp_disjointTriples]; exact mem_range.2 hu
  have hj : u / 3 ∈ range r := mem_range.2 (by omega)
  have huj : u ∈ tri (u / 3) := mem_tri.2 rfl
  rw [rho_coatom _ _ huS, omitted_eq hz, rho,
    prodFam_deg _ _ (tri_pairwise r) _ (Qz_sub z _) hj huj,
    prodFam_card _ _ (tri_pairwise r) _ (Qz_sub z _), ← mul_prod_erase _ _ hj]
  by_cases hzu : z / 3 = u / 3
  · have hprod : ∏ l ∈ (range r).erase (u / 3), (Qz z l).card =
        ∏ l ∈ (range r).erase (u / 3), (tri l).powerset.card := by
      apply prod_congr rfl
      intro l hl
      rw [Qz, if_neg (by rw [hzu]; exact ne_of_mem_erase hl)]
    have hQ : Qz z (u / 3) = loc (u / 3) z := by rw [Qz, if_pos hzu.symm]
    have hz' : 3 * (u / 3) + z % 3 = z := by omega
    have hu' : 3 * (u / 3) + u % 3 = u := by omega
    have hc := loc_card (u / 3) (z % 3) (Nat.mod_lt _ (by norm_num))
    have hd := loc_deg (u / 3) (z % 3) (u % 3) (Nat.mod_lt _ (by norm_num))
      (Nat.mod_lt _ (by norm_num))
    rw [hz'] at hc hd
    rw [hu'] at hd
    rw [hprod, hQ, hc, hd, if_pos hzu]
    by_cases h : z = u
    · have : u % 3 = z % 3 := by rw [h]
      rw [if_pos this, if_pos h]
      push_cast
      ring
    · have : u % 3 ≠ z % 3 := by omega
      rw [if_neg this, if_neg h]
      push_cast
      ring
  · have hQ : Qz z (u / 3) = (tri (u / 3)).powerset := by rw [Qz, if_neg (Ne.symm hzu)]
    have h0 := rho_powerset (tri (u / 3)) huj
    rw [rho] at h0
    have hne : ¬ z = u := fun h => hzu (by rw [h])
    rw [hQ, if_neg hzu, if_neg hne]
    push_cast
    have key : ∀ a b R : ℤ, 2 * a - b = 0 → -(2 * (a * R) - b * R) = 0 := by
      intro a b R h
      have e : 2 * (a * R) - b * R = (2 * a - b) * R := by ring
      rw [e, h]
      ring
    rw [mul_zero]
    exact key _ _ _ h0

/-- The filter of `[3r]` by "same triple as `u`" is the triple of `u`. -/
theorem filter_same_triple {r u : ℕ} (hu : u < 3 * r) :
    (range (3 * r)).filter (fun z => z / 3 = u / 3) = tri (u / 3) := by
  ext z
  rw [mem_filter, mem_range, mem_tri]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by omega, h⟩

end Triples

open Triples

theorem disjointTriples_card (r : ℕ) : (disjointTriples r).card = r :=
  (card_image_of_injective (range r) tri_injective).trans (card_range r)

theorem disjointTriples_subset_blocks (r n : ℕ) (h : 3 * r ≤ n) :
    disjointTriples r ⊆ blocks 3 n := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := mem_disjointTriples.1 hg
  rw [blocks, mem_powersetCard]
  refine ⟨?_, tri_card i⟩
  intro x hx
  rw [mem_tri] at hx
  rw [mem_range]
  omega

theorem not_isFC_disjointTriples (r : ℕ) (hr : 1 ≤ r) : ¬ IsFC (disjointTriples r) := by
  apply not_isFC_of_coatoms (disjointTriples r) (fun _ => 1)
  intro u hu
  rw [supp_disjointTriples] at hu ⊢
  have hu' := mem_range.1 hu
  have hrow : ∀ z ∈ range (3 * r), ((1 : ℕ) : ℤ) * rho (coatom (disjointTriples r) z) u =
      ((∏ l ∈ (range r).erase (u / 3), (tri l).powerset.card : ℕ) : ℤ) *
        ((if z / 3 = u / 3 then 1 else 0) - (if z = u then 4 else 0)) := by
    intro z hz
    rw [Nat.cast_one, one_mul, rho_row (mem_range.1 hz) hu']
  rw [sum_congr rfl hrow, ← mul_sum, sum_sub_distrib, sum_boole, filter_same_triple hu',
    tri_card, sum_ite_eq', if_pos hu]
  have hP : 0 < ∏ l ∈ (range r).erase (u / 3), (tri l).powerset.card := by
    have h8 : ∀ l ∈ (range r).erase (u / 3), (tri l).powerset.card = 2 ^ 3 := fun l _ => by
      rw [card_powerset, tri_card]
    rw [prod_congr rfl h8, prod_const]
    positivity
  have hP' : (0 : ℤ) < ((∏ l ∈ (range r).erase (u / 3), (tri l).powerset.card : ℕ) : ℤ) := by
    exact_mod_cast hP
  push_cast
  linarith

end Results.FcMorrisV2
