import Results.FcMorrisV2.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Solution/Elementary: elementary extremal bounds (paper Appendix A)

Pure hypergraph combinatorics (no Frankl-completeness).

* `graph_bound` (Lemma A.1): the vertex set of a maximum matching is a vertex cover.
* `triple_bound` (Lemma A.2), with `q = k - 1`: vertex links have matching number `≤ q`
  (`Elementary.link_matching`); heavy pairs (in `> 2q` triples) have maximum degree `≤ q`
  (`Elementary.heavy_nbr_card`, via a greedy system of distinct representatives); triples without
  a heavy pair are counted through their links (`Elementary.part_c`), the others through the
  vertex opposite to a heavy pair (`Elementary.part_d`).
* `four_bound` (Proposition A.3): apply `triple_bound` to every vertex link and double count.
-/

namespace Results.FcMorrisV2

open Finset

/-- Paper Lemma A.1: a graph with maximum degree `≤ d` and matching number `≤ q` has at most
`2 q d` edges. -/
theorem graph_bound (E : Fam) (hE : ∀ e ∈ E, e.card = 2) (d q : ℕ)
    (hdeg : ∀ v : ℕ, (E.filter fun e => v ∈ e).card ≤ d)
    (hmat : ∀ M ∈ E.powerset,
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → Disjoint e e') → M.card ≤ q) :
    E.card ≤ 2 * q * d := by
  -- a matching of maximum cardinality
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image
    (E.powerset.filter fun M => ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → Disjoint e e') Finset.card
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset E,
      fun e he => absurd he (Finset.notMem_empty e)⟩⟩
  obtain ⟨hMp, hMdisj⟩ := Finset.mem_filter.mp hM
  have hMsub : M ⊆ E := Finset.mem_powerset.mp hMp
  have hMq : M.card ≤ q := hmat M hMp hMdisj
  -- its vertex set has at most `2 q` points
  have hU : (M.biUnion id).card ≤ 2 * q := by
    calc (M.biUnion id).card ≤ ∑ e ∈ M, (id e).card := Finset.card_biUnion_le
      _ = ∑ _e ∈ M, 2 := Finset.sum_congr rfl (fun e he => hE e (hMsub he))
      _ = 2 * M.card := by rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]
      _ ≤ 2 * q := by omega
  -- and it is a vertex cover (maximality)
  have hcover : E ⊆ (M.biUnion id).biUnion (fun v => E.filter fun e => v ∈ e) := by
    intro e he
    by_contra hcon
    have hout : ∀ v ∈ e, v ∉ M.biUnion id := fun v hv hvU =>
      hcon (Finset.mem_biUnion.mpr ⟨v, hvU, Finset.mem_filter.mpr ⟨he, hv⟩⟩)
    have heM : e ∉ M := by
      intro heM
      obtain ⟨w, hw⟩ : e.Nonempty := Finset.card_pos.mp (by have := hE e he; omega)
      exact hout w hw (Finset.mem_biUnion.mpr ⟨e, heM, hw⟩)
    have hnew : insert e M ∈ E.powerset.filter
        fun M => ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → Disjoint e e' := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset he hMsub), ?_⟩
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · rw [ha]
        exact Finset.disjoint_left.mpr fun w hwa hwb =>
          hout w hwa (Finset.mem_biUnion.mpr ⟨b, hb, hwb⟩)
      · rw [hb]
        exact Finset.disjoint_left.mpr fun w hwa hwb =>
          hout w hwb (Finset.mem_biUnion.mpr ⟨a, ha, hwa⟩)
      · exact hMdisj a ha b hb hab
    have h1 := hmax _ hnew
    rw [Finset.card_insert_of_notMem heM] at h1
    omega
  calc E.card ≤ ((M.biUnion id).biUnion (fun v => E.filter fun e => v ∈ e)).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ v ∈ M.biUnion id, (E.filter fun e => v ∈ e).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ M.biUnion id, d := Finset.sum_le_sum (fun v _ => hdeg v)
    _ = (M.biUnion id).card * d := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ ≤ 2 * q * d := Nat.mul_le_mul_right d hU

namespace Elementary

/-- Number of members of `T` containing both `x` and `y`. -/
def pairDeg (T : Fam) (x y : ℕ) : ℕ := (T.filter fun f => x ∈ f ∧ y ∈ f).card

theorem pairDeg_comm (T : Fam) (x y : ℕ) : pairDeg T x y = pairDeg T y x := by
  unfold pairDeg
  rw [Finset.filter_congr (fun f _ => and_comm)]

/-- `f` contains no heavy pair (a heavy pair lies in more than `2q` members of `T`).
(An `abbrev`, so that its decidability is found by unfolding.) -/
abbrev NoHeavy (T : Fam) (q : ℕ) (f : Finset ℕ) : Prop :=
  ∀ a ∈ f, ∀ b ∈ f, a ≠ b → pairDeg T a b ≤ 2 * q

/-- Members of `T` through `v` whose pair opposite to `v` is heavy. -/
def heavyAt (T : Fam) (q v : ℕ) : Fam :=
  T.filter fun f => v ∈ f ∧ ∀ a ∈ f.erase v, ∀ b ∈ f.erase v, a ≠ b → 2 * q < pairDeg T a b

theorem mem_heavyAt {T : Fam} {q v : ℕ} {f : Finset ℕ} :
    f ∈ heavyAt T q v ↔ f ∈ T ∧ v ∈ f ∧
      ∀ a ∈ f.erase v, ∀ b ∈ f.erase v, a ≠ b → 2 * q < pairDeg T a b := by
  unfold heavyAt
  exact Finset.mem_filter

/-- Third points `z ∉ {x, y}` with `{x, y, z} ∈ T`. -/
def thirdPts (T : Fam) (V : Finset ℕ) (x y : ℕ) : Finset ℕ :=
  V.filter fun z => z ≠ x ∧ z ≠ y ∧ ({x, y, z} : Finset ℕ) ∈ T

theorem mem_thirdPts {T : Fam} {V : Finset ℕ} {x y z : ℕ} :
    z ∈ thirdPts T V x y ↔ z ∈ V ∧ z ≠ x ∧ z ≠ y ∧ ({x, y, z} : Finset ℕ) ∈ T := by
  unfold thirdPts
  exact Finset.mem_filter

/-- Erasing a common point is injective. -/
theorem card_image_erase (S : Fam) (v : ℕ) (hS : ∀ f ∈ S, v ∈ f) :
    (S.image fun f => f.erase v).card = S.card := by
  apply Finset.card_image_of_injOn
  intro f hf f' hf' h
  have h' : f.erase v = f'.erase v := h
  rw [← Finset.insert_erase (hS f (Finset.mem_coe.mp hf)),
    ← Finset.insert_erase (hS f' (Finset.mem_coe.mp hf')), h']

/-- Double counting of incidences. -/
theorem sum_deg (F : Fam) (V : Finset ℕ) (c : ℕ) (hF : ∀ f ∈ F, f ⊆ V ∧ f.card = c) :
    ∑ v ∈ V, (F.filter fun f => v ∈ f).card = c * F.card := by
  calc ∑ v ∈ V, (F.filter fun f => v ∈ f).card
      = ∑ v ∈ V, ∑ f ∈ F, if v ∈ f then 1 else 0 := by simp only [Finset.card_filter]
    _ = ∑ f ∈ F, ∑ v ∈ V, if v ∈ f then 1 else 0 := Finset.sum_comm
    _ = ∑ f ∈ F, (V.filter fun v => v ∈ f).card := by simp only [Finset.card_filter]
    _ = ∑ _f ∈ F, c := by
        apply Finset.sum_congr rfl
        intro f hf
        rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hF f hf).1, (hF f hf).2]
    _ = c * F.card := by rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]

/-- A three-set containing two distinct points `a, b` is `{a, b, c}`. -/
theorem eq_triple_of_mem (f : Finset ℕ) (hf : f.card = 3) (a b : ℕ) (ha : a ∈ f) (hb : b ∈ f)
    (hab : a ≠ b) : ∃ c, c ≠ a ∧ c ≠ b ∧ f = {a, b, c} := by
  have hsub : ({a, b} : Finset ℕ) ⊆ f :=
    Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)
  have hc : (f \ {a, b}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hf, Finset.card_pair hab]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hc
  have hcf : c ∈ f \ {a, b} := by rw [hc]; exact Finset.mem_singleton_self c
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hcf
  have hca : c ≠ a := fun h => hcf.2 (Or.inl h)
  have hcb : c ≠ b := fun h => hcf.2 (Or.inr h)
  refine ⟨c, hca, hcb, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · exact Finset.insert_subset ha (Finset.insert_subset hb (Finset.singleton_subset_iff.mpr hcf.1))
  · have hnot : a ∉ ({b, c} : Finset ℕ) := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact fun h => h.elim hab (fun h' => hca h'.symm)
    have h1 := Finset.card_insert_of_notMem hnot
    have h2 := Finset.card_pair (Ne.symm hcb)
    omega

/-- A two-set containing `y` is `{y, w}`. -/
theorem eq_pair_of_mem (e : Finset ℕ) (he : e.card = 2) (y : ℕ) (hy : y ∈ e) :
    ∃ w, w ≠ y ∧ e = {y, w} := by
  have h1 : (e.erase y).card = 1 := by rw [Finset.card_erase_of_mem hy, he]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
  have hwe : w ∈ e.erase y := by rw [hw]; exact Finset.mem_singleton_self w
  refine ⟨w, Finset.ne_of_mem_erase hwe, ?_⟩
  rw [← Finset.insert_erase hy, hw]

/-- Lifting a sunflower of a vertex link (core `C`) to a sunflower with core `insert v C`. -/
theorem lift_sunflower (F : Fam) (v : ℕ) (S : Fam) (C : Finset ℕ)
    (hS : S ⊆ (F.filter fun f => v ∈ f).image fun f => f.erase v)
    (hC : ∀ e ∈ S, C ⊆ e) (hpair : ∀ e ∈ S, ∀ e' ∈ S, e ≠ e' → e ∩ e' = C) :
    IsSunflower F S.card (insert v C) := by
  have hmem : ∀ e ∈ S, v ∉ e ∧ insert v e ∈ F := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp (hS he)
    obtain ⟨hfF, hvf⟩ := Finset.mem_filter.mp hf
    exact ⟨Finset.notMem_erase v f, by rw [Finset.insert_erase hvf]; exact hfF⟩
  refine ⟨S.image (insert v), ?_, ?_, ?_, ?_⟩
  · rw [Finset.mem_powerset]
    intro f hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    exact (hmem e he).2
  · apply Finset.card_image_of_injOn
    intro e he e' he' h
    have h' : insert v e = insert v e' := h
    rw [← Finset.erase_insert (hmem e (Finset.mem_coe.mp he)).1,
      ← Finset.erase_insert (hmem e' (Finset.mem_coe.mp he')).1, h']
  · intro f hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    exact Finset.insert_subset_insert v (hC e he)
  · intro f hf f' hf' hne
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hf'
    have hee' : e ≠ e' := fun h => hne (by rw [h])
    rw [← Finset.insert_inter_distrib, hpair e he e' he' hee']

/-- A matching in the link of `v` has fewer than `k` edges if there is no `k`-petal sunflower
with core `{v}`. -/
theorem link_matching (T : Fam) (k v : ℕ) (hno : ¬ IsSunflower T k {v}) (M : Fam)
    (hM : M ⊆ (T.filter fun f => v ∈ f).image fun f => f.erase v)
    (hdisj : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → Disjoint e e') : M.card < k := by
  by_contra hlt
  obtain ⟨M', hM'M, hM'card⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_lt hlt)
  apply hno
  have h := lift_sunflower T v M' ∅ (hM'M.trans hM) (fun e _ => Finset.empty_subset e)
    (fun e he e' he' hne =>
      Finset.disjoint_iff_inter_eq_empty.mp (hdisj e (hM'M he) e' (hM'M he') hne))
  rw [hM'card] at h
  exact h

/-- Greedy system of distinct representatives: if each of the sets `A i` (`i ∈ s`) has at least
`n ≥ |s|` elements, they have an injective choice function. -/
theorem exists_sdr {ι : Type*} [DecidableEq ι] (A : ι → Finset ℕ) (n : ℕ) (s : Finset ι) :
    s.card ≤ n → (∀ i ∈ s, n ≤ (A i).card) →
      ∃ z : ι → ℕ, (∀ i ∈ s, z i ∈ A i) ∧ ∀ i ∈ s, ∀ j ∈ s, z i = z j → i = j := by
  induction s using Finset.induction_on with
  | empty =>
    intro _ _
    exact ⟨fun _ => 0, fun i hi => absurd hi (Finset.notMem_empty i),
      fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert i s hi ih =>
    intro hcard hA
    rw [Finset.card_insert_of_notMem hi] at hcard
    obtain ⟨z, hz, hinj⟩ := ih (by omega) (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    have hlt : (s.image z).card < (A i).card :=
      lt_of_le_of_lt Finset.card_image_le
        (lt_of_lt_of_le (by omega) (hA i (Finset.mem_insert_self i s)))
    obtain ⟨a, haA, haz⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨fun j => if j = i then a else z j, ?_, ?_⟩
    · intro j hj
      dsimp only
      by_cases hji : j = i
      · rw [if_pos hji, hji]
        exact haA
      · rw [if_neg hji]
        exact hz j ((Finset.mem_insert.mp hj).resolve_left hji)
    · intro j hj j' hj' h
      dsimp only at h
      by_cases h1 : j = i <;> by_cases h2 : j' = i
      · rw [h1, h2]
      · rw [if_pos h1, if_neg h2] at h
        exact absurd (Finset.mem_image.mpr
          ⟨j', (Finset.mem_insert.mp hj').resolve_left h2, h.symm⟩) haz
      · rw [if_neg h1, if_pos h2] at h
        exact absurd (Finset.mem_image.mpr
          ⟨j, (Finset.mem_insert.mp hj).resolve_left h1, h⟩) haz
      · rw [if_neg h1, if_neg h2] at h
        exact hinj j ((Finset.mem_insert.mp hj).resolve_left h1)
          j' ((Finset.mem_insert.mp hj').resolve_left h2) h

/-- Heavy pairs through a fixed point `x`: at most `q` of them (paper, proof of Lemma A.2). -/
theorem heavy_nbr_card (T : Fam) (V : Finset ℕ) (q : ℕ) (hT : ∀ f ∈ T, f ⊆ V ∧ f.card = 3)
    (hno : ∀ x, ¬ IsSunflower T (q + 1) {x}) (x : ℕ) (Y : Finset ℕ)
    (hY : ∀ y ∈ Y, y ≠ x ∧ 2 * q < pairDeg T x y) : Y.card ≤ q := by
  by_contra hlt
  obtain ⟨Y', hY'Y, hY'card⟩ := Finset.exists_subset_card_eq (show q + 1 ≤ Y.card by omega)
  have key : ∀ y ∈ Y', q + 1 ≤ (thirdPts T V x y \ Y').card := by
    intro y hy
    obtain ⟨hyx, hheavy⟩ := hY y (hY'Y hy)
    have hW1 : pairDeg T x y ≤ (thirdPts T V x y).card := by
      have hsub : T.filter (fun f => x ∈ f ∧ y ∈ f) ⊆
          (thirdPts T V x y).image fun z => ({x, y, z} : Finset ℕ) := by
        intro f hf
        obtain ⟨hfT, hxf, hyf⟩ := Finset.mem_filter.mp hf
        obtain ⟨hfV, hf3⟩ := hT f hfT
        obtain ⟨c, hcx, hcy, hfeq⟩ := eq_triple_of_mem f hf3 x y hxf hyf (Ne.symm hyx)
        have hcf : c ∈ f := by
          rw [hfeq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
          exact Or.inr (Or.inr rfl)
        exact Finset.mem_image.mpr
          ⟨c, mem_thirdPts.mpr ⟨hfV hcf, hcx, hcy, hfeq ▸ hfT⟩, hfeq.symm⟩
      exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
    have hW2 : (thirdPts T V x y ∩ Y').card ≤ q := by
      have hsub : thirdPts T V x y ∩ Y' ⊆ Y'.erase y := by
        intro w hw
        rw [Finset.mem_inter] at hw
        exact Finset.mem_erase.mpr ⟨(mem_thirdPts.mp hw.1).2.2.1, hw.2⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hy, hY'card] at h1
      omega
    have := Finset.card_sdiff_add_card_inter (thirdPts T V x y) Y'
    omega
  obtain ⟨z, hzA, hzinj⟩ :=
    exists_sdr (fun y => thirdPts T V x y \ Y') (q + 1) Y' hY'card.le key
  have hz : ∀ y ∈ Y', y ≠ x ∧ z y ≠ x ∧ z y ≠ y ∧ ({x, y, z y} : Finset ℕ) ∈ T ∧ z y ∉ Y' := by
    intro y hy
    have h := Finset.mem_sdiff.mp (hzA y hy)
    have h' := mem_thirdPts.mp h.1
    exact ⟨(hY y (hY'Y hy)).1, h'.2.1, h'.2.2.1, h'.2.2.2, h.2⟩
  apply hno x
  refine ⟨Y'.image fun y => ({x, y, z y} : Finset ℕ), ?_, ?_, ?_, ?_⟩
  · rw [Finset.mem_powerset]
    intro f hf
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hf
    exact (hz y hy).2.2.2.1
  · rw [Finset.card_image_of_injOn, hY'card]
    intro y hy y' hy' h
    have hy := Finset.mem_coe.mp hy
    have hy' := Finset.mem_coe.mp hy'
    have h' : ({x, y, z y} : Finset ℕ) = {x, y', z y'} := h
    have hmem : y ∈ ({x, y', z y'} : Finset ℕ) := by
      rw [← h', Finset.mem_insert, Finset.mem_insert]
      exact Or.inr (Or.inl rfl)
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1
    · exact absurd h1 (hz y hy).1
    · exact h1
    · exact absurd hy (by rw [h1]; exact (hz y' hy').2.2.2.2)
  · intro f hf
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hf
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
  · intro f hf f' hf' hne
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hf'
    have hyy' : y ≠ y' := fun h => hne (by rw [h])
    obtain ⟨h1, h2, h3, _, h5⟩ := hz y hy
    obtain ⟨h1', h2', h3', _, h5'⟩ := hz y' hy'
    have hzz : z y ≠ z y' := fun h => hyy' (hzinj y hy y' hy' h)
    have hzy' : z y ≠ y' := fun h => h5 (by rw [h]; exact hy')
    have hz'y : z y' ≠ y := fun h => h5' (by rw [h]; exact hy)
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    omega

/-- Part (c) of the proof of Lemma A.2: triples without heavy pairs. -/
theorem part_c (T : Fam) (V : Finset ℕ) (q : ℕ) (hT : ∀ f ∈ T, f ⊆ V ∧ f.card = 3)
    (hno : ∀ x, ¬ IsSunflower T (q + 1) {x}) :
    3 * (T.filter (NoHeavy T q)).card ≤ V.card * (2 * q * (2 * q)) := by
  have hT0 : ∀ f ∈ T.filter (NoHeavy T q), f ⊆ V ∧ f.card = 3 :=
    fun f hf => hT f (Finset.mem_filter.mp hf).1
  have hlink : ∀ v ∈ V,
      ((T.filter (NoHeavy T q)).filter fun f => v ∈ f).card ≤ 2 * q * (2 * q) := by
    intro v _
    rw [← card_image_erase ((T.filter (NoHeavy T q)).filter fun f => v ∈ f) v
      (fun f hf => (Finset.mem_filter.mp hf).2)]
    refine graph_bound _ ?_ (2 * q) q ?_ ?_
    · intro e he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hf0, hvf⟩ := Finset.mem_filter.mp hf
      rw [Finset.card_erase_of_mem hvf, (hT0 f hf0).2]
    · intro y
      rw [Finset.filter_image]
      refine le_trans Finset.card_image_le ?_
      rcases Finset.eq_empty_or_nonempty
          (((T.filter (NoHeavy T q)).filter fun f => v ∈ f).filter fun f => y ∈ f.erase v)
          with h | ⟨f₀, hf₀⟩
      · rw [h, Finset.card_empty]
        exact Nat.zero_le _
      · simp only [Finset.mem_filter] at hf₀
        obtain ⟨⟨⟨_, hnh⟩, hvf⟩, hyf⟩ := hf₀
        have hle : pairDeg T v y ≤ 2 * q :=
          hnh v hvf y (Finset.mem_of_mem_erase hyf) (Ne.symm (Finset.ne_of_mem_erase hyf))
        unfold pairDeg at hle
        refine le_trans (Finset.card_le_card ?_) hle
        intro f hf
        simp only [Finset.mem_filter] at hf ⊢
        exact ⟨hf.1.1.1, hf.1.2, Finset.mem_of_mem_erase hf.2⟩
    · intro M hM hdisj
      have := link_matching T (q + 1) v (hno v) M
        ((Finset.mem_powerset.mp hM).trans (Finset.image_subset_image
          (Finset.filter_subset_filter _ (Finset.filter_subset _ _)))) hdisj
      omega
  calc 3 * (T.filter (NoHeavy T q)).card
      = ∑ v ∈ V, ((T.filter (NoHeavy T q)).filter fun f => v ∈ f).card :=
        (sum_deg _ V 3 hT0).symm
    _ ≤ ∑ _v ∈ V, 2 * q * (2 * q) := Finset.sum_le_sum hlink
    _ = V.card * (2 * q * (2 * q)) := by rw [Finset.sum_const, Nat.nsmul_eq_mul]

/-- Part (d) of the proof of Lemma A.2: triples containing a heavy pair. -/
theorem part_d (T : Fam) (V : Finset ℕ) (q : ℕ) (hT : ∀ f ∈ T, f ⊆ V ∧ f.card = 3)
    (hno : ∀ x, ¬ IsSunflower T (q + 1) {x}) :
    (T.filter fun f => ¬ NoHeavy T q f).card ≤ V.card * (2 * q * q) := by
  have hcover : (T.filter fun f => ¬ NoHeavy T q f) ⊆ V.biUnion (heavyAt T q) := by
    intro f hf
    obtain ⟨hfT, hnh⟩ := Finset.mem_filter.mp hf
    obtain ⟨hfV, hf3⟩ := hT f hfT
    unfold NoHeavy at hnh
    simp only [not_forall, not_le] at hnh
    obtain ⟨a, ha, b, hb, hab, hlt⟩ := hnh
    obtain ⟨c, hca, hcb, hfeq⟩ := eq_triple_of_mem f hf3 a b ha hb hab
    have hcf : c ∈ f := by
      rw [hfeq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr rfl)
    refine Finset.mem_biUnion.mpr ⟨c, hfV hcf, mem_heavyAt.mpr ⟨hfT, hcf, ?_⟩⟩
    intro a' ha' b' hb' hab'
    rw [hfeq, Finset.mem_erase, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at ha' hb'
    rcases ha'.2 with h1 | h1 | h1
    · rcases hb'.2 with h2 | h2 | h2
      · exact absurd (h1.trans h2.symm) hab'
      · rw [h1, h2]; exact hlt
      · exact absurd h2 hb'.1
    · rcases hb'.2 with h2 | h2 | h2
      · rw [h1, h2, pairDeg_comm]; exact hlt
      · exact absurd (h1.trans h2.symm) hab'
      · exact absurd h2 hb'.1
    · exact absurd h1 ha'.1
  have hQ : ∀ v ∈ V, (heavyAt T q v).card ≤ 2 * q * q := by
    intro v _
    rw [← card_image_erase (heavyAt T q v) v (fun f hf => (mem_heavyAt.mp hf).2.1)]
    refine graph_bound _ ?_ q q ?_ ?_
    · intro e he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hfT, hvf, _⟩ := mem_heavyAt.mp hf
      rw [Finset.card_erase_of_mem hvf, (hT f hfT).2]
    · intro y
      have hsub : ((heavyAt T q v).image fun f => f.erase v).filter (fun e => y ∈ e) ⊆
          (V.filter fun w => w ≠ y ∧ 2 * q < pairDeg T y w).image
            fun w => ({y, w} : Finset ℕ) := by
        intro e he
        obtain ⟨he, hye⟩ := Finset.mem_filter.mp he
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨hfT, hvf, hheavy⟩ := mem_heavyAt.mp hf
        obtain ⟨hfV, hf3⟩ := hT f hfT
        obtain ⟨w, hwy, hweq⟩ := eq_pair_of_mem (f.erase v)
          (by rw [Finset.card_erase_of_mem hvf, hf3]) y hye
        have hwe : w ∈ f.erase v := by
          rw [hweq, Finset.mem_insert, Finset.mem_singleton]
          exact Or.inr rfl
        exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr
          ⟨hfV (Finset.mem_of_mem_erase hwe), hwy, hheavy y hye w hwe (Ne.symm hwy)⟩,
          hweq.symm⟩
      refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
      exact heavy_nbr_card T V q hT hno y _ (fun w hw => (Finset.mem_filter.mp hw).2)
    · intro M hM hdisj
      have := link_matching T (q + 1) v (hno v) M
        ((Finset.mem_powerset.mp hM).trans (Finset.image_subset_image (fun f hf => by
          obtain ⟨hfT, hvf, _⟩ := mem_heavyAt.mp hf
          exact Finset.mem_filter.mpr ⟨hfT, hvf⟩))) hdisj
      omega
  calc (T.filter fun f => ¬ NoHeavy T q f).card ≤ (V.biUnion (heavyAt T q)).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ v ∈ V, (heavyAt T q v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ V, 2 * q * q := Finset.sum_le_sum hQ
    _ = V.card * (2 * q * q) := by rw [Finset.sum_const, Nat.nsmul_eq_mul]

end Elementary

/-- Paper Lemma A.2: a triple system on the ground set `V` with no `k`-petal sunflower with a
one-point core has at most `(10/3)(k-1)² |V|` triples. -/
theorem triple_bound (k : ℕ) (hk : 2 ≤ k) (V : Finset ℕ) (T : Fam)
    (hT : ∀ f ∈ T, f ⊆ V ∧ f.card = 3) (hno : ¬ ∃ x : ℕ, IsSunflower T k {x}) :
    3 * T.card ≤ 10 * (k - 1) ^ 2 * V.card := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  have hno' : ∀ x, ¬ IsSunflower T (q + 1) {x} := fun x h => hno ⟨x, h⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (Elementary.NoHeavy T q)
  have hc := Elementary.part_c T V q hT hno'
  have hd := Elementary.part_d T V q hT hno'
  rw [Nat.add_sub_cancel]
  linarith

/-- Paper Proposition A.3: a four-uniform system on the ground set `V` with no `k`-petal
sunflower with a two-point core has at most `(5/6)(k-1)² |V| (|V|-1)` members. -/
theorem four_bound (k : ℕ) (hk : 2 ≤ k) (V : Finset ℕ) (H : Fam)
    (hH : ∀ f ∈ H, f ⊆ V ∧ f.card = 4) (hno : ¬ ∃ D : Finset ℕ, D.card = 2 ∧ IsSunflower H k D) :
    6 * H.card ≤ 5 * (k - 1) ^ 2 * V.card * (V.card - 1) := by
  have hlink : ∀ v ∈ V,
      3 * (H.filter fun f => v ∈ f).card ≤ 10 * (k - 1) ^ 2 * (V.card - 1) := by
    intro v hv
    rw [← Elementary.card_image_erase (H.filter fun f => v ∈ f) v
      (fun f hf => (Finset.mem_filter.mp hf).2), ← Finset.card_erase_of_mem hv]
    apply triple_bound k hk (V.erase v)
    · intro e he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hfH, hvf⟩ := Finset.mem_filter.mp hf
      exact ⟨Finset.erase_subset_erase v (hH f hfH).1,
        by rw [Finset.card_erase_of_mem hvf, (hH f hfH).2]⟩
    · rintro ⟨x, S, hS, hScard, hScore, hSpair⟩
      apply hno
      have hS' := Finset.mem_powerset.mp hS
      obtain ⟨e₀, he₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
      have hxv : x ≠ v := by
        have hx : x ∈ e₀ := Finset.singleton_subset_iff.mp (hScore e₀ he₀)
        obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp (hS' he₀)
        exact Finset.ne_of_mem_erase hx
      refine ⟨{v, x}, Finset.card_pair (Ne.symm hxv), ?_⟩
      have h := Elementary.lift_sunflower H v S {x} hS' hScore hSpair
      rw [hScard] at h
      exact h
  have hsum := Elementary.sum_deg H V 4 hH
  have h12 : 3 * (4 * H.card) ≤ V.card * (10 * (k - 1) ^ 2 * (V.card - 1)) := by
    rw [← hsum, Finset.mul_sum]
    calc ∑ v ∈ V, 3 * (H.filter fun f => v ∈ f).card
        ≤ ∑ _v ∈ V, 10 * (k - 1) ^ 2 * (V.card - 1) := Finset.sum_le_sum hlink
      _ = V.card * (10 * (k - 1) ^ 2 * (V.card - 1)) := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
  generalize (k - 1) ^ 2 = a at h12 ⊢
  generalize V.card - 1 = m at h12 ⊢
  generalize V.card = n at h12 ⊢
  linarith

end Results.FcMorrisV2
