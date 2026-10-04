import Results.FcMorrisV2.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Solution/Product: counting subsets of a disjoint union by their traces

`prodFam I V Q` is the family of subsets `A ⊆ ⋃_{i∈I} V i` whose trace `A ∩ V i` lies in the
prescribed family `Q i` for every `i ∈ I`.  Cardinalities and degrees factor over the components.
Used by the coatom-row computations of the sunflower and of Morris's construction.
-/

namespace Results.FcMorrisV2

open Finset

/-- Subsets of `⋃_{i ∈ I} V i` with trace in `Q i` on every component. -/
def prodFam {ι : Type*} [DecidableEq ι] (I : Finset ι) (V : ι → Finset ℕ) (Q : ι → Fam) : Fam :=
  ((I.biUnion V).powerset).filter fun A => ∀ i ∈ I, A ∩ V i ∈ Q i

namespace Product

/-- Membership in `prodFam`. -/
lemma mem_prodFam {ι : Type*} [DecidableEq ι] {I : Finset ι} {V : ι → Finset ℕ}
    {Q : ι → Fam} {A : Finset ℕ} :
    A ∈ prodFam I V Q ↔ A ⊆ I.biUnion V ∧ ∀ i ∈ I, A ∩ V i ∈ Q i := by
  simp only [prodFam, Finset.mem_filter, Finset.mem_powerset]

/-- A subset of `⋃_{i ∈ I} V i` is disjoint from a component `V j` disjoint from all `V i`. -/
private lemma disjoint_of_subset_biUnion {ι : Type*} [DecidableEq ι] {I : Finset ι}
    {V : ι → Finset ℕ} {j : ι} (hVj : ∀ i ∈ I, Disjoint (V i) (V j)) {A : Finset ℕ}
    (hA : A ⊆ I.biUnion V) : Disjoint A (V j) :=
  Disjoint.mono_left hA ((Finset.disjoint_biUnion_left I V (V j)).2 hVj)

private lemma union_inter_of_subset {S A T : Finset ℕ} (hS : S ⊆ T) (hA : Disjoint A T) :
    (S ∪ A) ∩ T = S := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hT⟩
    · exact h
    · exact absurd hT (Finset.disjoint_left.1 hA h)
  · intro h
    exact ⟨Or.inl h, hS h⟩

private lemma union_sdiff_of_subset' {S A T : Finset ℕ} (hS : S ⊆ T) (hA : Disjoint A T) :
    (S ∪ A) \ T = A := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hT⟩
    · exact absurd (hS h) hT
    · exact h
  · intro h
    exact ⟨Or.inr h, Finset.disjoint_left.1 hA h⟩

private lemma union_inter_of_disjoint {S A T : Finset ℕ} (hS : Disjoint S T) :
    (S ∪ A) ∩ T = A ∩ T := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hT⟩
    · exact absurd hT (Finset.disjoint_left.1 hS h)
    · exact ⟨h, hT⟩
  · rintro ⟨h, hT⟩
    exact ⟨Or.inr h, hT⟩

private lemma sdiff_inter_of_disjoint {A T U : Finset ℕ} (hU : Disjoint U T) :
    (A \ T) ∩ U = A ∩ U := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨h, _⟩, hU'⟩
    exact ⟨h, hU'⟩
  · rintro ⟨h, hU'⟩
    exact ⟨⟨h, fun hT => Finset.disjoint_left.1 hU hU' hT⟩, hU'⟩

/-- The inductive step: splitting off one component. -/
private lemma prodFam_insert_card {ι : Type*} [DecidableEq ι] (I : Finset ι) (V : ι → Finset ℕ)
    (Q : ι → Fam) {j : ι} (hj : j ∉ I) (hVj : ∀ i ∈ I, Disjoint (V i) (V j))
    (hQj : Q j ⊆ (V j).powerset) :
    (prodFam (insert j I) V Q).card = (Q j).card * (prodFam I V Q).card := by
  rw [← Finset.card_product]
  refine Finset.card_nbij' (fun A => (A ∩ V j, A \ V j)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_
  · -- the map lands in the product
    intro A hA
    obtain ⟨hAsub, hAQ⟩ := mem_prodFam.1 (Finset.mem_coe.1 hA)
    refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨hAQ j (Finset.mem_insert_self j I), ?_⟩)
    refine mem_prodFam.2 ⟨?_, fun i hi => ?_⟩
    · intro x hx
      rw [Finset.mem_sdiff] at hx
      have hx' := hAsub hx.1
      rw [Finset.biUnion_insert, Finset.mem_union] at hx'
      exact hx'.resolve_left hx.2
    · rw [sdiff_inter_of_disjoint (hVj i hi)]
      exact hAQ i (Finset.mem_insert_of_mem hi)
  · -- the inverse lands in the family
    intro p hp
    obtain ⟨hS, hA'⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hp)
    obtain ⟨hA'sub, hA'Q⟩ := mem_prodFam.1 hA'
    have hSsub : p.1 ⊆ V j := Finset.mem_powerset.1 (hQj hS)
    have hdisj : Disjoint p.2 (V j) := disjoint_of_subset_biUnion hVj hA'sub
    refine Finset.mem_coe.2 (mem_prodFam.2 ⟨?_, fun i hi => ?_⟩)
    · rw [Finset.biUnion_insert]
      exact Finset.union_subset_union hSsub hA'sub
    · rcases Finset.mem_insert.1 hi with rfl | hiI
      · show (p.1 ∪ p.2) ∩ V i ∈ Q i
        rw [union_inter_of_subset hSsub hdisj]
        exact hS
      · show (p.1 ∪ p.2) ∩ V i ∈ Q i
        have hSi : Disjoint p.1 (V i) :=
          Disjoint.mono_left hSsub (hVj i hiI).symm
        rw [union_inter_of_disjoint hSi]
        exact hA'Q i hiI
  · -- left inverse
    intro A _
    show A ∩ V j ∪ A \ V j = A
    rw [Finset.union_comm]
    exact Finset.sdiff_union_inter A (V j)
  · -- right inverse
    intro p hp
    obtain ⟨hS, hA'⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hp)
    obtain ⟨hA'sub, hA'Q⟩ := mem_prodFam.1 hA'
    have hSsub : p.1 ⊆ V j := Finset.mem_powerset.1 (hQj hS)
    have hdisj : Disjoint p.2 (V j) := disjoint_of_subset_biUnion hVj hA'sub
    show ((p.1 ∪ p.2) ∩ V j, (p.1 ∪ p.2) \ V j) = p
    rw [union_inter_of_subset hSsub hdisj, union_sdiff_of_subset' hSsub hdisj]

end Product

/-- The product family has `∏ |Q i|` members. -/
theorem prodFam_card {ι : Type*} [DecidableEq ι] (I : Finset ι) (V : ι → Finset ℕ)
    (hV : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (V i) (V j)) (Q : ι → Fam)
    (hQ : ∀ i ∈ I, Q i ⊆ (V i).powerset) :
    (prodFam I V Q).card = ∏ i ∈ I, (Q i).card := by
  induction I using Finset.induction_on with
  | empty => simp [prodFam]
  | insert j I hj ih =>
    have hVj : ∀ i ∈ I, Disjoint (V i) (V j) := fun i hi =>
      hV i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_self j I)
        (fun h => hj (h ▸ hi))
    rw [Product.prodFam_insert_card I V Q hj hVj (hQ j (Finset.mem_insert_self j I)),
      Finset.prod_insert hj,
      ih (fun i hi k hk hik => hV i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk) hik)
        (fun i hi => hQ i (Finset.mem_insert_of_mem hi))]

/-- Degree of a point `u ∈ V j` in the product family. -/
theorem prodFam_deg {ι : Type*} [DecidableEq ι] (I : Finset ι) (V : ι → Finset ℕ)
    (hV : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (V i) (V j)) (Q : ι → Fam)
    (hQ : ∀ i ∈ I, Q i ⊆ (V i).powerset) {j : ι} (hj : j ∈ I) {u : ℕ} (hu : u ∈ V j) :
    deg (prodFam I V Q) u = deg (Q j) u * ∏ i ∈ I.erase j, (Q i).card := by
  -- the modified family `Q'` : restrict the `j`-th factor to the members containing `u`
  obtain ⟨Q', hQ'j, hQ'i⟩ : ∃ Q' : ι → Fam, Q' j = (Q j).filter (fun A => u ∈ A) ∧
      ∀ i, i ≠ j → Q' i = Q i :=
    ⟨Function.update Q j ((Q j).filter (fun A => u ∈ A)), Function.update_self _ _ _,
      fun i hi => Function.update_of_ne hi _ _⟩
  have hfam : prodFam I V Q' = (prodFam I V Q).filter (fun A => u ∈ A) := by
    ext A
    rw [Finset.mem_filter, Product.mem_prodFam, Product.mem_prodFam]
    constructor
    · rintro ⟨hsub, h⟩
      refine ⟨⟨hsub, fun i hi => ?_⟩, ?_⟩
      · by_cases hij : i = j
        · subst hij
          have := h i hi
          rw [hQ'j, Finset.mem_filter] at this
          exact this.1
        · have := h i hi
          rwa [hQ'i i hij] at this
      · have := h j hj
        rw [hQ'j, Finset.mem_filter] at this
        exact (Finset.mem_inter.1 this.2).1
    · rintro ⟨⟨hsub, h⟩, huA⟩
      refine ⟨hsub, fun i hi => ?_⟩
      by_cases hij : i = j
      · subst hij
        rw [hQ'j, Finset.mem_filter]
        exact ⟨h i hi, Finset.mem_inter.2 ⟨huA, hu⟩⟩
      · rw [hQ'i i hij]
        exact h i hi
  have hQ'sub : ∀ i ∈ I, Q' i ⊆ (V i).powerset := by
    intro i hi
    by_cases hij : i = j
    · subst hij
      rw [hQ'j]
      exact (Finset.filter_subset _ _).trans (hQ i hi)
    · rw [hQ'i i hij]
      exact hQ i hi
  calc deg (prodFam I V Q) u = (prodFam I V Q').card := by
        rw [hfam]; rfl
    _ = ∏ i ∈ I, (Q' i).card := prodFam_card I V hV Q' hQ'sub
    _ = (Q' j).card * ∏ i ∈ I.erase j, (Q' i).card := (Finset.mul_prod_erase I _ hj).symm
    _ = deg (Q j) u * ∏ i ∈ I.erase j, (Q i).card := by
        congr 1
        · rw [hQ'j]; rfl
        · exact Finset.prod_congr rfl fun i hi => by
            rw [hQ'i i (Finset.ne_of_mem_erase hi)]

end Results.FcMorrisV2
