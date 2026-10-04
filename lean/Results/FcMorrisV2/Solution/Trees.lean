import Results.FcMorrisV2.Solution.Lifting
import Results.FcMorrisV2.Solution.TreeDefs

/-!
# Solution/Trees: the recursive configurations `T_k` are robustly FC (paper Corollary 3.2)

Proof outline.  We prove by induction on the height `h` a statement that is uniform in the
labelling (`Trees.robust_tree_aux`): there is a shape `ts` of length `h` with positive entries and
natural constants `Wn, n, d` (`n, d ≥ 1`) such that every validly labelled configuration of shape
`ts` with a `p`-point root has a robust certificate `(w, n/d)` of total weight `≤ Wn`.

* `h = 0`: `treeCfg [] R0 pr = {R0}`; use the seeds `robust_singleton` / `robust_pair`.
* `h → h+1`: a labelled tree of shape `ts ++ [t']` is the pair lifting
  `lift (treeCfg ts R0 pr) t' P` with `P C j = pr (π_C ++ [j])`, where `π_C` is the (unique) leaf
  path with `pathSet R0 pr π_C = C` (`Trees.treeCfg_append`).  The support of a labelled tree of
  shape `ts` has at most `p + 2 · nodeCount ts` points and the tree has at most
  `|leafPaths ts|` generators, so the constants of `lifting` can be chosen from `ts` alone:
  `a = 2^vb - 1`, `λ = 2 a d`, `t' = max (2a) (6 a λ 2^vb (mb n + Wn))`.
-/

namespace Results.FcMorrisV2

open Finset

namespace Trees

/-! ### Leaf paths and node paths -/

theorem mem_leafPaths_nil {σ : List ℕ} : σ ∈ leafPaths [] ↔ σ = [] := by
  simp only [leafPaths, mem_singleton]

theorem mem_leafPaths_cons {t : ℕ} {ts σ : List ℕ} :
    σ ∈ leafPaths (t :: ts) ↔ ∃ j < t, ∃ π ∈ leafPaths ts, σ = j :: π := by
  simp only [leafPaths, mem_biUnion, mem_range, mem_image]
  constructor
  · rintro ⟨j, hj, π, hπ, rfl⟩
    exact ⟨j, hj, π, hπ, rfl⟩
  · rintro ⟨j, hj, π, hπ, rfl⟩
    exact ⟨j, hj, π, hπ, rfl⟩

theorem length_of_mem_leafPaths : ∀ {ts σ : List ℕ}, σ ∈ leafPaths ts → σ.length = ts.length
  | [], σ, h => by
    rw [mem_leafPaths_nil] at h
    rw [h]
  | t :: ts, σ, h => by
    obtain ⟨j, _, π, hπ, rfl⟩ := mem_leafPaths_cons.1 h
    rw [List.length_cons, List.length_cons, length_of_mem_leafPaths hπ]

theorem mem_leafPaths_append : ∀ {ts : List ℕ} {t' : ℕ} {σ : List ℕ},
    σ ∈ leafPaths (ts ++ [t']) ↔ ∃ π ∈ leafPaths ts, ∃ j < t', σ = π ++ [j]
  | [], t', σ => by
    rw [List.nil_append, mem_leafPaths_cons]
    constructor
    · rintro ⟨j, hj, π, hπ, rfl⟩
      rw [mem_leafPaths_nil] at hπ
      subst hπ
      exact ⟨[], mem_leafPaths_nil.2 rfl, j, hj, rfl⟩
    · rintro ⟨π, hπ, j, hj, rfl⟩
      rw [mem_leafPaths_nil] at hπ
      subst hπ
      exact ⟨j, hj, [], mem_leafPaths_nil.2 rfl, rfl⟩
  | t :: ts, t', σ => by
    rw [List.cons_append, mem_leafPaths_cons]
    constructor
    · rintro ⟨j, hj, π, hπ, rfl⟩
      obtain ⟨π0, hπ0, j', hj', rfl⟩ := (mem_leafPaths_append (ts := ts)).1 hπ
      exact ⟨j :: π0, mem_leafPaths_cons.2 ⟨j, hj, π0, hπ0, rfl⟩, j', hj', rfl⟩
    · rintro ⟨π, hπ, j', hj', rfl⟩
      obtain ⟨j, hj, π0, hπ0, rfl⟩ := mem_leafPaths_cons.1 hπ
      exact ⟨j, hj, π0 ++ [j'], (mem_leafPaths_append (ts := ts)).2 ⟨π0, hπ0, j', hj', rfl⟩, rfl⟩

theorem mem_nodePaths {ts σ : List ℕ} :
    σ ∈ nodePaths ts ↔ ∃ π ∈ leafPaths ts, ∃ i < π.length, σ = π.take (i + 1) := by
  simp only [nodePaths, mem_biUnion, mem_image, mem_range]
  constructor
  · rintro ⟨π, hπ, i, hi, rfl⟩
    exact ⟨π, hπ, i, hi, rfl⟩
  · rintro ⟨π, hπ, i, hi, rfl⟩
    exact ⟨π, hπ, i, hi, rfl⟩

theorem take_mem_nodePaths {ts π : List ℕ} (hπ : π ∈ leafPaths ts) {i : ℕ} (hi : i < π.length) :
    π.take (i + 1) ∈ nodePaths ts :=
  mem_nodePaths.2 ⟨π, hπ, i, hi, rfl⟩

theorem length_le_of_mem_nodePaths {ts σ : List ℕ} (h : σ ∈ nodePaths ts) :
    σ.length ≤ ts.length := by
  obtain ⟨π, hπ, i, hi, rfl⟩ := mem_nodePaths.1 h
  rw [List.length_take, ← length_of_mem_leafPaths hπ]
  exact min_le_right _ _

/-- A nonempty leaf path is a node. -/
theorem leaf_mem_nodePaths {ts π : List ℕ} (hπ : π ∈ leafPaths ts) (hne : π ≠ []) :
    π ∈ nodePaths ts := by
  have hlen : 0 < π.length := List.length_pos_of_ne_nil hne
  have h := take_mem_nodePaths hπ (i := π.length - 1) (by omega)
  rwa [Nat.sub_add_cancel hlen, List.take_length] at h

/-- Adding a nonempty last level keeps all old nodes. -/
theorem nodePaths_subset_append {ts : List ℕ} {t' : ℕ} (ht : 0 < t') :
    nodePaths ts ⊆ nodePaths (ts ++ [t']) := by
  intro σ hσ
  obtain ⟨π, hπ, i, hi, rfl⟩ := mem_nodePaths.1 hσ
  have h1 : π ++ [0] ∈ leafPaths (ts ++ [t']) := mem_leafPaths_append.2 ⟨π, hπ, 0, ht, rfl⟩
  have h2 : i < (π ++ [0]).length := by
    rw [List.length_append, List.length_singleton]
    omega
  have h := take_mem_nodePaths h1 h2
  rwa [List.take_append_of_le_length (by omega)] at h

theorem append_mem_nodePaths {ts π : List ℕ} {t' j : ℕ} (hπ : π ∈ leafPaths ts) (hj : j < t') :
    π ++ [j] ∈ nodePaths (ts ++ [t']) :=
  leaf_mem_nodePaths (mem_leafPaths_append.2 ⟨π, hπ, j, hj, rfl⟩)
    (List.append_ne_nil_of_right_ne_nil π (List.cons_ne_nil j []))

/-- A valid labelling of `ts ++ [t']` (with `t' ≥ 1`) restricts to a valid labelling of `ts`. -/
theorem validLabel_of_append {ts : List ℕ} {t' : ℕ} {R0 : Finset ℕ} {pr : List ℕ → Finset ℕ}
    (ht : 0 < t') (h : ValidLabel (ts ++ [t']) R0 pr) : ValidLabel ts R0 pr where
  card σ hσ := h.card σ (nodePaths_subset_append ht hσ)
  disjRoot σ hσ := h.disjRoot σ (nodePaths_subset_append ht hσ)
  disjPair σ hσ σ' hσ' hne :=
    h.disjPair σ (nodePaths_subset_append ht hσ) σ' (nodePaths_subset_append ht hσ') hne

/-! ### Path sets -/

theorem pathSet_append (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) (π : List ℕ) (j : ℕ) :
    pathSet R0 pr (π ++ [j]) = pathSet R0 pr π ∪ pr (π ++ [j]) := by
  unfold pathSet
  rw [List.length_append, List.length_singleton, range_add_one, biUnion_insert]
  have h1 : (π ++ [j]).take (π.length + 1) = π ++ [j] := by
    apply List.take_of_length_le
    rw [List.length_append, List.length_singleton]
  have h2 : (range π.length).biUnion (fun i => pr ((π ++ [j]).take (i + 1))) =
      (range π.length).biUnion (fun i => pr (π.take (i + 1))) := by
    apply biUnion_congr rfl
    intro i hi
    rw [mem_range] at hi
    rw [List.take_append_of_le_length (by omega)]
  rw [h1, h2]
  ext x
  simp only [mem_union]
  tauto

theorem pr_take_subset_pathSet (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) {π : List ℕ} {i : ℕ}
    (hi : i < π.length) : pr (π.take (i + 1)) ⊆ pathSet R0 pr π := by
  intro x hx
  exact mem_union_right _ (mem_biUnion.2 ⟨i, mem_range.2 hi, hx⟩)

theorem pr_subset_pathSet (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) {π : List ℕ} (hne : π ≠ []) :
    pr π ⊆ pathSet R0 pr π := by
  have hlen : 0 < π.length := List.length_pos_of_ne_nil hne
  have h := pr_take_subset_pathSet R0 pr (π := π) (i := π.length - 1) (by omega)
  rwa [Nat.sub_add_cancel hlen, List.take_length] at h

theorem pathSet_subset {ts : List ℕ} {R0 : Finset ℕ} {pr : List ℕ → Finset ℕ} {π : List ℕ}
    (hπ : π ∈ leafPaths ts) : pathSet R0 pr π ⊆ R0 ∪ (nodePaths ts).biUnion pr := by
  intro x hx
  rcases mem_union.1 hx with h | h
  · exact mem_union_left _ h
  · obtain ⟨i, hi, hx⟩ := mem_biUnion.1 h
    exact mem_union_right _ (mem_biUnion.2 ⟨_, take_mem_nodePaths hπ (mem_range.1 hi), hx⟩)

/-- Under a valid labelling, distinct leaves have distinct path sets. -/
theorem pathSet_inj {ts : List ℕ} {R0 : Finset ℕ} {pr : List ℕ → Finset ℕ}
    (hv : ValidLabel ts R0 pr) {π π' : List ℕ} (hπ : π ∈ leafPaths ts) (hπ' : π' ∈ leafPaths ts)
    (h : pathSet R0 pr π = pathSet R0 pr π') : π = π' := by
  by_contra hne
  have hl := length_of_mem_leafPaths hπ
  have hl' := length_of_mem_leafPaths hπ'
  have hπne : π ≠ [] := by
    rintro rfl
    apply hne
    have h0 : π'.length = 0 := by
      rw [hl', ← hl]
      rfl
    exact (List.length_eq_zero_iff.1 h0).symm
  have hnode : π ∈ nodePaths ts := leaf_mem_nodePaths hπ hπne
  obtain ⟨x, hx⟩ := card_pos.1 (by rw [hv.card π hnode]; norm_num)
  have hxπ : x ∈ pathSet R0 pr π' := h ▸ pr_subset_pathSet R0 pr hπne hx
  rcases mem_union.1 hxπ with hR | hB
  · exact disjoint_left.1 (hv.disjRoot π hnode) hx hR
  · obtain ⟨i, hi, hxi⟩ := mem_biUnion.1 hB
    rw [mem_range] at hi
    have hnode' : π'.take (i + 1) ∈ nodePaths ts := take_mem_nodePaths hπ' hi
    by_cases heq : π = π'.take (i + 1)
    · have hlen : (π'.take (i + 1)).length = π.length := by rw [← heq]
      rw [List.length_take, Nat.min_eq_left (by omega)] at hlen
      have hi1 : i + 1 = π'.length := by omega
      rw [hi1, List.take_length] at heq
      exact hne heq
    · exact disjoint_left.1 (hv.disjPair π hnode _ hnode' heq) hx hxi

/-! ### Tree configurations -/

theorem mem_treeCfg {ts : List ℕ} {R0 : Finset ℕ} {pr : List ℕ → Finset ℕ} {X : Finset ℕ} :
    X ∈ treeCfg ts R0 pr ↔ ∃ π ∈ leafPaths ts, pathSet R0 pr π = X :=
  mem_image

theorem mem_lift {G : Fam} {t : ℕ} {P : Finset ℕ → ℕ → Finset ℕ} {X : Finset ℕ} :
    X ∈ lift G t P ↔ ∃ C ∈ G, ∃ j < t, C ∪ P C j = X := by
  unfold lift
  simp only [mem_image, mem_product, mem_range, Prod.exists]
  constructor
  · rintro ⟨C, j, ⟨hC, hj⟩, rfl⟩
    exact ⟨C, hC, j, hj, rfl⟩
  · rintro ⟨C, hC, j, hj, rfl⟩
    exact ⟨C, j, ⟨hC, hj⟩, rfl⟩

theorem subset_supp {G : Fam} {C : Finset ℕ} (hC : C ∈ G) : C ⊆ supp G := by
  intro x hx
  exact mem_biUnion.2 ⟨C, hC, hx⟩

theorem supp_singleton (C : Finset ℕ) : supp ({C} : Fam) = C := by
  unfold supp
  rw [singleton_biUnion]
  rfl

theorem treeCfg_nil (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) : treeCfg [] R0 pr = {R0} := by
  have h : pathSet R0 pr [] = R0 := by
    unfold pathSet
    rw [List.length_nil, range_zero, biUnion_empty, union_empty]
  unfold treeCfg leafPaths
  rw [image_singleton, h]

theorem supp_treeCfg_subset (ts : List ℕ) (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) :
    supp (treeCfg ts R0 pr) ⊆ R0 ∪ (nodePaths ts).biUnion pr := by
  intro x hx
  obtain ⟨C, hC, hx⟩ := mem_biUnion.1 hx
  obtain ⟨π, hπ, rfl⟩ := mem_treeCfg.1 hC
  exact pathSet_subset hπ hx

theorem card_supp_treeCfg_le {ts : List ℕ} {R0 : Finset ℕ} {pr : List ℕ → Finset ℕ}
    (hv : ValidLabel ts R0 pr) :
    (supp (treeCfg ts R0 pr)).card ≤ R0.card + 2 * nodeCount ts := by
  calc (supp (treeCfg ts R0 pr)).card ≤ (R0 ∪ (nodePaths ts).biUnion pr).card :=
        card_le_card (supp_treeCfg_subset ts R0 pr)
    _ ≤ R0.card + ((nodePaths ts).biUnion pr).card := card_union_le _ _
    _ ≤ R0.card + ∑ σ ∈ nodePaths ts, (pr σ).card := Nat.add_le_add_left card_biUnion_le _
    _ = R0.card + 2 * nodeCount ts := by
        rw [sum_const_nat hv.card, nodeCount, Nat.mul_comm]

theorem card_treeCfg_le (ts : List ℕ) (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) :
    (treeCfg ts R0 pr).card ≤ (leafPaths ts).card :=
  card_image_le

/-! ### The tree of shape `ts ++ [t']` is a pair lifting of the tree of shape `ts` -/

open Classical in
/-- A leaf path whose path set is `C` (chosen), or `[]` if there is none. -/
noncomputable def choosePath (ts : List ℕ) (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ)
    (C : Finset ℕ) : List ℕ :=
  if h : ∃ π ∈ leafPaths ts, pathSet R0 pr π = C then h.choose else []

/-- The new pairs: `P C j = pr (π_C ++ [j])`. -/
noncomputable def liftPairs (ts : List ℕ) (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) :
    Finset ℕ → ℕ → Finset ℕ :=
  fun C j => pr (choosePath ts R0 pr C ++ [j])

theorem choosePath_spec {ts : List ℕ} {R0 : Finset ℕ} {pr : List ℕ → Finset ℕ} {C : Finset ℕ}
    (hC : C ∈ treeCfg ts R0 pr) :
    choosePath ts R0 pr C ∈ leafPaths ts ∧ pathSet R0 pr (choosePath ts R0 pr C) = C := by
  have h : ∃ π ∈ leafPaths ts, pathSet R0 pr π = C := mem_treeCfg.1 hC
  unfold choosePath
  rw [dif_pos h]
  exact h.choose_spec

theorem choosePath_pathSet {ts : List ℕ} {R0 : Finset ℕ} {pr : List ℕ → Finset ℕ}
    (hv : ValidLabel ts R0 pr) {π : List ℕ} (hπ : π ∈ leafPaths ts) :
    choosePath ts R0 pr (pathSet R0 pr π) = π := by
  obtain ⟨h1, h2⟩ := choosePath_spec (mem_treeCfg.2 ⟨π, hπ, rfl⟩)
  exact pathSet_inj hv h1 hπ h2

theorem treeCfg_append {ts : List ℕ} {t' : ℕ} {R0 : Finset ℕ} {pr : List ℕ → Finset ℕ}
    (hv : ValidLabel ts R0 pr) :
    treeCfg (ts ++ [t']) R0 pr = lift (treeCfg ts R0 pr) t' (liftPairs ts R0 pr) := by
  ext X
  rw [mem_treeCfg, mem_lift]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨π, hπ, j, hj, rfl⟩ := mem_leafPaths_append.1 hσ
    refine ⟨pathSet R0 pr π, mem_treeCfg.2 ⟨π, hπ, rfl⟩, j, hj, ?_⟩
    rw [liftPairs, choosePath_pathSet hv hπ, pathSet_append]
  · rintro ⟨C, hC, j, hj, rfl⟩
    obtain ⟨h1, h2⟩ := choosePath_spec hC
    refine ⟨choosePath ts R0 pr C ++ [j], mem_leafPaths_append.2 ⟨_, h1, j, hj, rfl⟩, ?_⟩
    rw [liftPairs, pathSet_append, h2]

/-! ### The uniform induction -/

theorem robust_tree_aux (p h : ℕ) (hp : p = 1 ∨ p = 2) :
    ∃ ts : List ℕ, ts.length = h ∧ (∀ t ∈ ts, 1 ≤ t) ∧
      ∃ Wn n d : ℕ, 1 ≤ n ∧ 1 ≤ d ∧
      ∀ (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ), R0.card = p → ValidLabel ts R0 pr →
        ∃ w : ℕ → ℚ, (∑ u ∈ supp (treeCfg ts R0 pr), w u) ≤ Wn ∧
          RobustFC (treeCfg ts R0 pr) w ((n : ℚ) / d) := by
  induction h with
  | zero =>
    refine ⟨[], rfl, fun t ht => absurd ht List.not_mem_nil, ?_⟩
    -- the seed `{R0}` with unit weights has total weight `p ≤ 2`
    have hW : ∀ (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ), R0.card = p →
        (∑ _u ∈ supp (treeCfg [] R0 pr), (1 : ℚ)) ≤ ((2 : ℕ) : ℚ) := by
      intro R0 pr hR0
      rw [treeCfg_nil, supp_singleton, sum_const, nsmul_eq_mul, mul_one, hR0]
      exact_mod_cast (show p ≤ 2 by rcases hp with rfl | rfl <;> norm_num)
    rcases hp with rfl | rfl
    · refine ⟨2, 1, 2, le_rfl, by norm_num, ?_⟩
      intro R0 pr hR0 _
      refine ⟨fun _ => 1, hW R0 pr hR0, ?_⟩
      obtain ⟨u, rfl⟩ := card_eq_one.1 hR0
      rw [treeCfg_nil, Nat.cast_one, Nat.cast_ofNat]
      exact robust_singleton u
    · refine ⟨2, 1, 1, le_rfl, le_rfl, ?_⟩
      intro R0 pr hR0 _
      refine ⟨fun _ => 1, hW R0 pr hR0, ?_⟩
      obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hR0
      rw [treeCfg_nil, Nat.cast_one, div_one]
      exact robust_pair hxy
  | succ h ih =>
    obtain ⟨ts, hlen, hpos, Wn, n, d, hn, hd, H⟩ := ih
    -- constants depending only on `ts`
    obtain ⟨vb, hvb⟩ : ∃ vb : ℕ, vb = p + 2 * nodeCount ts := ⟨_, rfl⟩
    obtain ⟨mb, hmb⟩ : ∃ mb : ℕ, mb = (leafPaths ts).card := ⟨_, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : ℕ, a = 2 ^ vb - 1 := ⟨_, rfl⟩
    obtain ⟨lam, hlam⟩ : ∃ lam : ℕ, lam = 2 * a * d := ⟨_, rfl⟩
    obtain ⟨t', ht'⟩ : ∃ t' : ℕ, t' = max (2 * a) (6 * a * lam * (2 ^ vb * (mb * n + Wn))) :=
      ⟨_, rfl⟩
    have hp1 : 1 ≤ p := by rcases hp with rfl | rfl <;> norm_num
    have ha1 : 1 ≤ a := by
      have h2 : 2 ^ 1 ≤ 2 ^ vb := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have ht2a : 2 * a ≤ t' := by
      rw [ht']
      exact le_max_left _ _
    have ht6 : 6 * a * lam * (2 ^ vb * (mb * n + Wn)) ≤ t' := by
      rw [ht']
      exact le_max_right _ _
    have ht'pos : 0 < t' := by omega
    refine ⟨ts ++ [t'], by rw [List.length_append, List.length_singleton, hlen], ?_,
      lam * Wn + (p + 2 * nodeCount (ts ++ [t'])), a, t', ha1, ht'pos, ?_⟩
    · intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · exact hpos t ht
      · rw [List.mem_singleton.1 ht]
        exact ht'pos
    intro R0 pr hR0 hv'
    have hv : ValidLabel ts R0 pr := validLabel_of_append ht'pos hv'
    obtain ⟨w, hW, hR⟩ := H R0 pr hR0 hv
    -- size bounds, uniform in the labelling
    have hsupp : (supp (treeCfg ts R0 pr)).card ≤ vb := by
      rw [hvb, ← hR0]
      exact card_supp_treeCfg_le hv
    have hcard : (treeCfg ts R0 pr).card ≤ mb := by
      rw [hmb]
      exact card_treeCfg_le ts R0 pr
    have hw0 : ∀ u, 0 ≤ w u := hR.2.2.1
    have hW0 : 0 ≤ ∑ u ∈ supp (treeCfg ts R0 pr), w u := sum_nonneg fun u _ => hw0 u
    -- the hypotheses of `lifting`
    have hA : ∀ C ∈ treeCfg ts R0 pr, 2 ^ C.card - 1 ≤ a := by
      intro C hC
      have hC' : C.card ≤ vb := le_trans (card_le_card (subset_supp hC)) hsupp
      rw [ha]
      exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) hC') 1
    have hd0 : (d : ℚ) ≠ 0 := by
      have : (0 : ℚ) < d := by exact_mod_cast hd
      exact ne_of_gt this
    have hLam : 2 * (a : ℚ) ≤ lam * ((n : ℚ) / d) := by
      have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
      have h1 : (lam : ℚ) * ((n : ℚ) / d) = 2 * a * n := by
        rw [hlam]
        push_cast
        rw [mul_assoc (2 * (a : ℚ)) d, mul_div_cancel₀ _ hd0]
      rw [h1]
      exact le_mul_of_one_le_right (by positivity) hn'
    have hT2 : 6 * (a : ℚ) * lam * (2 ^ (supp (treeCfg ts R0 pr)).card *
        (((treeCfg ts R0 pr).card : ℚ) * ((n : ℚ) / d) +
          (∑ u ∈ supp (treeCfg ts R0 pr), w u) / 2)) ≤ t' := by
      have hq0 : (0 : ℚ) ≤ (n : ℚ) / d := div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg d)
      have hqn : (n : ℚ) / d ≤ n := div_le_self (Nat.cast_nonneg n) (by exact_mod_cast hd)
      have h1 : ((treeCfg ts R0 pr).card : ℚ) * ((n : ℚ) / d) ≤ (mb : ℚ) * n :=
        mul_le_mul (by exact_mod_cast hcard) hqn hq0 (Nat.cast_nonneg mb)
      have h2 : (∑ u ∈ supp (treeCfg ts R0 pr), w u) / 2 ≤ Wn := by linarith
      have hX0 : 0 ≤ ((treeCfg ts R0 pr).card : ℚ) * ((n : ℚ) / d) +
          (∑ u ∈ supp (treeCfg ts R0 pr), w u) / 2 := by positivity
      have h3 : (2 : ℚ) ^ (supp (treeCfg ts R0 pr)).card ≤ 2 ^ vb :=
        pow_le_pow_right₀ (by norm_num) hsupp
      have h4 : (2 : ℚ) ^ (supp (treeCfg ts R0 pr)).card *
          (((treeCfg ts R0 pr).card : ℚ) * ((n : ℚ) / d) +
            (∑ u ∈ supp (treeCfg ts R0 pr), w u) / 2) ≤ 2 ^ vb * ((mb : ℚ) * n + Wn) :=
        mul_le_mul h3 (by linarith) hX0 (by positivity)
      have h5 : (0 : ℚ) ≤ 6 * (a : ℚ) * lam := by positivity
      calc _ ≤ 6 * (a : ℚ) * lam * (2 ^ vb * ((mb : ℚ) * n + Wn)) :=
            mul_le_mul_of_nonneg_left h4 h5
        _ ≤ t' := by exact_mod_cast ht6
    have hPc : ∀ C ∈ treeCfg ts R0 pr, ∀ j < t', (liftPairs ts R0 pr C j).card = 2 := by
      intro C hC j hj
      exact hv'.card _ (append_mem_nodePaths (choosePath_spec hC).1 hj)
    have hPV : ∀ C ∈ treeCfg ts R0 pr, ∀ j < t',
        Disjoint (liftPairs ts R0 pr C j) (supp (treeCfg ts R0 pr)) := by
      intro C hC j hj
      have h1 := (choosePath_spec hC).1
      have hn := append_mem_nodePaths (t' := t') h1 hj
      refine Disjoint.mono_right (supp_treeCfg_subset ts R0 pr) ?_
      rw [disjoint_union_right, disjoint_biUnion_right]
      refine ⟨hv'.disjRoot _ hn, fun σ hσ =>
        hv'.disjPair _ hn σ (nodePaths_subset_append ht'pos hσ) ?_⟩
      intro heq
      have hσl := length_le_of_mem_nodePaths hσ
      rw [← heq, List.length_append, List.length_singleton, length_of_mem_leafPaths h1] at hσl
      omega
    have hPP : ∀ C ∈ treeCfg ts R0 pr, ∀ j < t', ∀ C' ∈ treeCfg ts R0 pr, ∀ j' < t',
        (C ≠ C' ∨ j ≠ j') → Disjoint (liftPairs ts R0 pr C j) (liftPairs ts R0 pr C' j') := by
      intro C hC j hj C' hC' j' hj' hne
      obtain ⟨h1, h2⟩ := choosePath_spec hC
      obtain ⟨h1', h2'⟩ := choosePath_spec hC'
      refine hv'.disjPair _ (append_mem_nodePaths h1 hj) _ (append_mem_nodePaths h1' hj') ?_
      intro heq
      obtain ⟨hπ, hjj⟩ := List.append_inj' heq rfl
      rcases hne with hne | hne
      · apply hne
        rw [← h2, ← h2', hπ]
      · exact hne (List.cons.inj hjj).1
    have key := lifting (treeCfg ts R0 pr) w ((n : ℚ) / d) hR t' lam a ha1 hA hLam ht2a hT2
      (liftPairs ts R0 pr) hPc hPV hPP
    rw [← treeCfg_append hv] at key
    refine ⟨liftW lam w (supp (treeCfg ts R0 pr)), ?_, key⟩
    -- total weight of the lifted certificate
    have hS : (supp (treeCfg (ts ++ [t']) R0 pr)).card ≤ p + 2 * nodeCount (ts ++ [t']) := by
      rw [← hR0]
      exact card_supp_treeCfg_le hv'
    unfold liftW
    rw [sum_ite]
    have hfirst : ∑ u ∈ supp (treeCfg (ts ++ [t']) R0 pr) with u ∈ supp (treeCfg ts R0 pr),
        (lam : ℚ) * w u ≤ lam * Wn := by
      calc _ ≤ ∑ u ∈ supp (treeCfg ts R0 pr), (lam : ℚ) * w u :=
            sum_le_sum_of_subset_of_nonneg (fun u hu => (mem_filter.1 hu).2)
              (fun u _ _ => mul_nonneg (Nat.cast_nonneg _) (hw0 u))
        _ = lam * ∑ u ∈ supp (treeCfg ts R0 pr), w u := (mul_sum _ _ _).symm
        _ ≤ lam * Wn := mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg _)
    have hsecond : ∑ u ∈ supp (treeCfg (ts ++ [t']) R0 pr) with u ∉ supp (treeCfg ts R0 pr),
        (1 : ℚ) ≤ ((p + 2 * nodeCount (ts ++ [t']) : ℕ) : ℚ) := by
      rw [sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast le_trans (card_filter_le _ _) hS
    push_cast at hsecond ⊢
    linarith

end Trees

/-- For root size `p ∈ {1,2}` and height `h` there are positive branch numbers `ts` such that
every validly labelled tree configuration of shape `ts` is FC (indeed robustly FC). -/
theorem robust_tree (p h : ℕ) (hp : p = 1 ∨ p = 2) :
    ∃ ts : List ℕ, ts.length = h ∧ (∀ t ∈ ts, 1 ≤ t) ∧
      ∀ (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ), R0.card = p → ValidLabel ts R0 pr →
        IsFC (treeCfg ts R0 pr) := by
  obtain ⟨ts, hlen, hpos, Wn, n, d, _, _, H⟩ := Trees.robust_tree_aux p h hp
  refine ⟨ts, hlen, hpos, fun R0 pr hR0 hv => ?_⟩
  obtain ⟨w, _, hR⟩ := H R0 pr hR0 hv
  exact hR.isFC

end Results.FcMorrisV2
