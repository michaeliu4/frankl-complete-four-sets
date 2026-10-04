import Results.FcMorrisV2.Solution.TreeDefs

/-!
# Solution/EmbedCore: the top-down embedding of the tree configuration (paper Lemma 4.4)

Pure combinatorics: once Füredi's theorem has produced a `k`-partite family `Hs` with parts `X`,
kernel chain `Ich` and sunflowers over every kernel, a validly labelled copy of the tree
configuration of any shape lives in `Hs`.
-/

namespace Results.FcMorrisV2

open Finset

namespace EmbedCore

/-! ### Projections `e[I] = e ∩ ⋃_{i ∈ I} X i` of edges -/

/-- The number of indices `Fin k`. -/
theorem card_univ_fin (k : ℕ) : (univ : Finset (Fin k)).card = k := by
  rw [Fin.univ_def, Finset.card_mk, Multiset.coe_card, List.length_finRange]

section Proj

variable {k : ℕ} (X : Fin k → Finset ℕ)

/-- (F1) An edge meeting every (pairwise disjoint) part in one point has `|e[I]| = |I|`. -/
theorem card_proj (hX : ∀ i j, i ≠ j → Disjoint (X i) (X j)) {e : Finset ℕ}
    (he : ∀ i, (e ∩ X i).card = 1) (I : Finset (Fin k)) :
    (e ∩ I.biUnion X).card = I.card := by
  rw [inter_biUnion, card_biUnion]
  · simp [he]
  · intro i _ j _ hij
    exact Disjoint.mono inter_subset_right inter_subset_right (hX i j hij)

/-- (F2) `e[univ] = e` for an edge with `k` points. -/
theorem proj_univ (hX : ∀ i j, i ≠ j → Disjoint (X i) (X j)) {e : Finset ℕ}
    (he : ∀ i, (e ∩ X i).card = 1) (hek : e.card = k) :
    e ∩ (univ : Finset (Fin k)).biUnion X = e := by
  apply eq_of_subset_of_card_le inter_subset_left
  rw [card_proj X hX he, card_univ_fin, hek]

/-- (F3) Projections are monotone in the index set. -/
theorem proj_mono {e : Finset ℕ} {I I' : Finset (Fin k)} (h : I ⊆ I') :
    e ∩ I.biUnion X ⊆ e ∩ I'.biUnion X :=
  inter_subset_inter_left (biUnion_subset_biUnion_of_subset_left X h)

/-- (F4) If the projection `e[I]` lies in another edge `f`, then `f[I] = e[I]`. -/
theorem proj_eq_of_subset (hX : ∀ i j, i ≠ j → Disjoint (X i) (X j)) {e f : Finset ℕ}
    (he : ∀ i, (e ∩ X i).card = 1) (hf : ∀ i, (f ∩ X i).card = 1) {I : Finset (Fin k)}
    (hsub : e ∩ I.biUnion X ⊆ f) : f ∩ I.biUnion X = e ∩ I.biUnion X := by
  symm
  apply eq_of_subset_of_card_le
  · intro x hx
    exact mem_inter.2 ⟨hsub hx, (mem_inter.1 hx).2⟩
  · rw [card_proj X hX hf, card_proj X hX he]

end Proj

/-- (F5) A sunflower with `s` petals and exact core `D` has a member whose petal avoids any given
set of fewer than `s` points. -/
theorem sunflower_avoid {H : Fam} {s : ℕ} {D : Finset ℕ} (hS : IsSunflower H s D)
    (F : Finset ℕ) (hF : F.card < s) : ∃ f ∈ H, D ⊆ f ∧ Disjoint (f \ D) F := by
  obtain ⟨S, hSH, hSc, hSD, hSi⟩ := hS
  rw [mem_powerset] at hSH
  by_contra hcon
  have hne : ∀ f ∈ S, ((f \ D) ∩ F).Nonempty := fun f hf =>
    not_disjoint_iff_nonempty_inter.1 fun hdisj => hcon ⟨f, hSH hf, hSD f hf, hdisj⟩
  choose! g hg using hne
  have hmaps : Set.MapsTo g S F := fun f hf => (mem_inter.1 (hg f hf)).2
  have hinj : Set.InjOn g S := by
    intro f hf f' hf' hgg
    by_contra hff'
    have h1 := mem_sdiff.1 (mem_inter.1 (hg f hf)).1
    have h2 := mem_sdiff.1 (mem_inter.1 (hg f' hf')).1
    have h3 : g f ∈ f ∩ f' := mem_inter.2 ⟨h1.1, hgg ▸ h2.1⟩
    rw [hSi f hf f' hf' hff'] at h3
    exact h1.2 h3
  have := card_le_card_of_injOn g hmaps hinj
  omega

/-! ### The extended kernel chain `Ifull` -/

section Ifull

variable {k : ℕ}

/-- The kernel chain extended by `Ifull h = univ`. -/
def Ifull (h : ℕ) (Ich : ℕ → Finset (Fin k)) (j : ℕ) : Finset (Fin k) :=
  if j < h then Ich j else univ

theorem Ifull_of_lt {h j : ℕ} (Ich : ℕ → Finset (Fin k)) (hj : j < h) :
    Ifull h Ich j = Ich j := if_pos hj

theorem Ifull_self (h : ℕ) (Ich : ℕ → Finset (Fin k)) : Ifull h Ich h = univ :=
  if_neg (lt_irrefl h)

theorem card_Ifull {p h : ℕ} (hk : k = p + 2 * h) {Ich : ℕ → Finset (Fin k)}
    (hIc : ∀ j < h, (Ich j).card = p + 2 * j) {j : ℕ} (hj : j ≤ h) :
    (Ifull h Ich j).card = p + 2 * j := by
  rcases lt_or_eq_of_le hj with hlt | rfl
  · rw [Ifull_of_lt Ich hlt, hIc j hlt]
  · rw [Ifull_self, card_univ_fin, hk]

theorem Ifull_mono {h : ℕ} {Ich : ℕ → Finset (Fin k)}
    (hIm : ∀ j, j + 1 < h → Ich j ⊆ Ich (j + 1)) {j : ℕ} (hj : j < h) :
    Ifull h Ich j ⊆ Ifull h Ich (j + 1) := by
  rw [Ifull_of_lt Ich hj]
  by_cases hj1 : j + 1 < h
  · rw [Ifull_of_lt Ich hj1]
    exact hIm j hj1
  · unfold Ifull
    rw [if_neg hj1]
    exact subset_univ _

end Ifull

/-! ### Leaf paths and node paths -/

theorem length_of_mem_leafPaths :
    ∀ {ts π : List ℕ}, π ∈ leafPaths ts → π.length = ts.length
  | [], π, hπ => by
    simp only [leafPaths, mem_singleton] at hπ
    simp [hπ]
  | t :: ts, π, hπ => by
    simp only [leafPaths, mem_biUnion, mem_range, mem_image] at hπ
    obtain ⟨j, _, π', hπ', rfl⟩ := hπ
    simp [length_of_mem_leafPaths hπ']

theorem mem_nodePaths_iff {ts τ : List ℕ} :
    τ ∈ nodePaths ts ↔ ∃ π ∈ leafPaths ts, ∃ i < π.length, π.take (i + 1) = τ := by
  simp [nodePaths]

theorem length_of_mem_nodePaths {ts τ : List ℕ} (hτ : τ ∈ nodePaths ts) :
    1 ≤ τ.length ∧ τ.length ≤ ts.length := by
  obtain ⟨π, hπ, i, hi, rfl⟩ := mem_nodePaths_iff.1 hτ
  rw [List.length_take, ← length_of_mem_leafPaths hπ]
  omega

theorem dropLast_mem_nodePaths {ts τ : List ℕ} (hτ : τ ∈ nodePaths ts) (h2 : 2 ≤ τ.length) :
    τ.dropLast ∈ nodePaths ts := by
  obtain ⟨π, hπ, i, hi, rfl⟩ := mem_nodePaths_iff.1 hτ
  rw [List.length_take] at h2
  refine mem_nodePaths_iff.2 ⟨π, hπ, i - 1, by omega, ?_⟩
  rw [List.dropLast_eq_take, List.take_take, List.length_take]
  congr 1
  omega

theorem leaf_mem_nodePaths {ts π : List ℕ} (hts : 1 ≤ ts.length) (hπ : π ∈ leafPaths ts) :
    π ∈ nodePaths ts := by
  have hl := length_of_mem_leafPaths hπ
  refine mem_nodePaths_iff.2 ⟨π, hπ, π.length - 1, by omega, ?_⟩
  rw [Nat.sub_add_cancel (by omega), List.take_length]

/-! ### Path sets -/

theorem pathSet_nil (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) : pathSet R0 pr [] = R0 := by
  simp [pathSet]

theorem pathSet_congr (R0 : Finset ℕ) {pr pr' : List ℕ → Finset ℕ} {σ : List ℕ}
    (h : ∀ i < σ.length, pr (σ.take (i + 1)) = pr' (σ.take (i + 1))) :
    pathSet R0 pr σ = pathSet R0 pr' σ := by
  unfold pathSet
  congr 1
  apply biUnion_congr rfl
  intro i hi
  exact h i (mem_range.1 hi)

theorem pathSet_eq_dropLast (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) {τ : List ℕ}
    (hτ : τ ≠ []) : pathSet R0 pr τ = pathSet R0 pr τ.dropLast ∪ pr τ := by
  obtain ⟨n, hn⟩ : ∃ n, τ.length = n + 1 :=
    ⟨τ.length - 1, by have := List.length_pos_iff.2 hτ; omega⟩
  unfold pathSet
  rw [List.length_dropLast, hn, Nat.add_sub_cancel, range_add_one, biUnion_insert]
  have h1 : τ.take (n + 1) = τ := by rw [← hn, List.take_length]
  have h2 : (range n).biUnion (fun i => pr (τ.dropLast.take (i + 1))) =
      (range n).biUnion (fun i => pr (τ.take (i + 1))) := by
    apply biUnion_congr rfl
    intro i hi
    rw [mem_range] at hi
    rw [List.dropLast_eq_take, List.take_take, hn]
    congr 2
    omega
  rw [h1, h2, union_comm (pr τ), union_assoc]

theorem pr_subset_pathSet (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) {σ : List ℕ}
    (hσ : σ ≠ []) : pr σ ⊆ pathSet R0 pr σ := by
  rw [pathSet_eq_dropLast R0 pr hσ]
  exact subset_union_right

/-- Changing `pr` at a node `τ` does not affect path sets of other nodes of length `≤ |τ|`. -/
theorem pathSet_update (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) {τ σ : List ℕ}
    (P : Finset ℕ) (hne : σ ≠ τ) (hlen : σ.length ≤ τ.length) :
    pathSet R0 (Function.update pr τ P) σ = pathSet R0 pr σ := by
  apply pathSet_congr
  intro i hi
  apply Function.update_of_ne
  intro heq
  apply hne
  have hl : (σ.take (i + 1)).length = i + 1 := List.length_take_of_le (by omega)
  rw [heq] at hl
  have hi' : i + 1 = σ.length := by omega
  rw [hi', List.take_length] at heq
  exact heq

/-! ### Induction adding a longest path last -/

theorem exists_max_length (S : Finset (List ℕ)) (hS : S.Nonempty) :
    ∃ τ ∈ S, ∀ x ∈ S, x.length ≤ τ.length := by
  induction S using Finset.induction_on with
  | empty => exact absurd hS not_nonempty_empty
  | insert a S _ ih =>
    rcases S.eq_empty_or_nonempty with hS' | hS'
    · refine ⟨a, mem_insert_self a S, fun x hx => ?_⟩
      rw [hS', insert_empty, mem_singleton] at hx
      rw [hx]
    · obtain ⟨τ, hτ, hmax⟩ := ih hS'
      by_cases hle : a.length ≤ τ.length
      · refine ⟨τ, mem_insert_of_mem hτ, fun x hx => ?_⟩
        rcases mem_insert.1 hx with rfl | hx
        · exact hle
        · exact hmax x hx
      · refine ⟨a, mem_insert_self a S, fun x hx => ?_⟩
        rcases mem_insert.1 hx with rfl | hx
        · exact le_rfl
        · exact (hmax x hx).trans (by omega)

/-- Induction on finite sets of paths, inserting a longest path in each step. -/
theorem induction_max_length {motive : Finset (List ℕ) → Prop} (empty : motive ∅)
    (step : ∀ τ D0, τ ∉ D0 → (∀ x ∈ D0, x.length ≤ τ.length) → motive D0 →
      motive (insert τ D0)) :
    ∀ n (S : Finset (List ℕ)), S.card = n → motive S := by
  intro n
  induction n with
  | zero =>
    intro S hS
    rw [card_eq_zero.1 hS]
    exact empty
  | succ n ih =>
    intro S hS
    obtain ⟨τ, hτ, hmax⟩ := exists_max_length S (card_pos.1 (by omega))
    rw [← insert_erase hτ]
    refine step τ (S.erase τ) (notMem_erase τ S) (fun x hx => hmax x (mem_of_mem_erase hx)) ?_
    apply ih
    rw [card_erase_of_mem hτ, hS, Nat.add_sub_cancel]

/-! ### The inductive construction -/

/-- The invariant of the top-down construction, for a downward closed set `Done` of processed
nonroot nodes: witnesses `wit σ ∈ Hs` whose projections realize the path sets, and a valid
labelling on `Done`. -/
theorem main_ind (k p h s : ℕ) (hh : 1 ≤ h) (hk : k = p + 2 * h)
    (Hs : Fam) (X : Fin k → Finset ℕ) (Ich : ℕ → Finset (Fin k))
    (hX : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hcard : ∀ e ∈ Hs, e.card = k)
    (hpart : ∀ e ∈ Hs, ∀ i, (e ∩ X i).card = 1)
    (hIc : ∀ j < h, (Ich j).card = p + 2 * j)
    (hIm : ∀ j, j + 1 < h → Ich j ⊆ Ich (j + 1))
    (hsun : ∀ e ∈ Hs, ∀ j < h, IsSunflower Hs s (e ∩ (Ich j).biUnion X))
    (ts : List ℕ) (hts : ts.length = h)
    (hs : k * (nodeCount ts + 1) < s) (e0 : Finset ℕ) (he0 : e0 ∈ Hs)
    (Done : Finset (List ℕ)) :
    Done ⊆ nodePaths ts → (∀ τ ∈ Done, 2 ≤ τ.length → τ.dropLast ∈ Done) →
      ∃ (wit : List ℕ → Finset ℕ) (pr : List ℕ → Finset ℕ),
        wit [] = e0 ∧
        (∀ σ ∈ Done, wit σ ∈ Hs) ∧
        (∀ σ ∈ insert [] Done, wit σ ∩ (Ifull h Ich σ.length).biUnion X =
          pathSet (e0 ∩ (Ich 0).biUnion X) pr σ) ∧
        (∀ σ ∈ Done, (pr σ).card = 2) ∧
        (∀ σ ∈ Done, Disjoint (pr σ) (e0 ∩ (Ich 0).biUnion X)) ∧
        (∀ σ ∈ Done, ∀ σ' ∈ Done, σ ≠ σ' → Disjoint (pr σ) (pr σ')) := by
  revert Done
  refine fun Done => induction_max_length (motive := fun Done =>
    Done ⊆ nodePaths ts → (∀ τ ∈ Done, 2 ≤ τ.length → τ.dropLast ∈ Done) →
      ∃ (wit : List ℕ → Finset ℕ) (pr : List ℕ → Finset ℕ),
        wit [] = e0 ∧
        (∀ σ ∈ Done, wit σ ∈ Hs) ∧
        (∀ σ ∈ insert [] Done, wit σ ∩ (Ifull h Ich σ.length).biUnion X =
          pathSet (e0 ∩ (Ich 0).biUnion X) pr σ) ∧
        (∀ σ ∈ Done, (pr σ).card = 2) ∧
        (∀ σ ∈ Done, Disjoint (pr σ) (e0 ∩ (Ich 0).biUnion X)) ∧
        (∀ σ ∈ Done, ∀ σ' ∈ Done, σ ≠ σ' → Disjoint (pr σ) (pr σ'))) ?_ ?_ Done.card Done rfl
  · intro _ _
    refine ⟨fun _ => e0, fun _ => ∅, rfl, fun σ hσ => absurd hσ (notMem_empty σ), ?_,
      fun σ hσ => absurd hσ (notMem_empty σ), fun σ hσ => absurd hσ (notMem_empty σ),
      fun σ hσ => absurd hσ (notMem_empty σ)⟩
    intro σ hσ
    rw [insert_empty, mem_singleton] at hσ
    subst hσ
    rw [pathSet_nil, List.length_nil, Ifull_of_lt Ich (by omega)]
  · intro τ D0 hτ hmax ih hsub hdc
    set R0 := e0 ∩ (Ich 0).biUnion X
    have hτN : τ ∈ nodePaths ts := hsub (mem_insert_self τ D0)
    have hD0sub : D0 ⊆ nodePaths ts := (subset_insert τ D0).trans hsub
    obtain ⟨hτ1, hτh⟩ := length_of_mem_nodePaths hτN
    rw [hts] at hτh
    have hτnil : τ ≠ [] := List.length_pos_iff.1 (by omega)
    have hD0dc : ∀ σ ∈ D0, 2 ≤ σ.length → σ.dropLast ∈ D0 := by
      intro σ hσ h2
      rcases mem_insert.1 (hdc σ (mem_insert_of_mem hσ) h2) with heq | hmem
      · exfalso
        have h1 := hmax σ hσ
        have h3 : σ.dropLast.length = σ.length - 1 := List.length_dropLast
        rw [heq] at h3
        omega
      · exact hmem
    obtain ⟨wit, pr, hw0, hwH, hI2, hc2, hdR, hdP⟩ := ih hD0sub hD0dc
    -- the nodes already present (including the root) differ from `τ` and are not longer
    have hold : ∀ σ' ∈ insert [] D0, σ' ≠ τ ∧ σ'.length ≤ τ.length := by
      intro σ' hσ'
      rcases mem_insert.1 hσ' with heq | hmem
      · subst heq
        exact ⟨hτnil.symm, by simp⟩
      · exact ⟨fun heq => hτ (heq ▸ hmem), hmax σ' hmem⟩
    -- the parent of `τ`
    have hσlen : τ.dropLast.length = τ.length - 1 := List.length_dropLast
    have hσmem : τ.dropLast ∈ insert [] D0 := by
      by_cases h2 : 2 ≤ τ.length
      · rcases mem_insert.1 (hdc τ (mem_insert_self τ D0) h2) with heq | hmem
        · exfalso
          rw [heq] at hσlen
          omega
        · exact mem_insert_of_mem hmem
      · have : τ.dropLast = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [this]
        exact mem_insert_self _ _
    have hjh : τ.dropLast.length < h := by omega
    have hwσ : wit τ.dropLast ∈ Hs := by
      rcases mem_insert.1 hσmem with heq | hmem
      · rw [heq, hw0]
        exact he0
      · exact hwH _ hmem
    have hDpath : wit τ.dropLast ∩ (Ich τ.dropLast.length).biUnion X =
        pathSet R0 pr τ.dropLast := by
      rw [← Ifull_of_lt Ich hjh]
      exact hI2 _ hσmem
    -- the forbidden set: all earlier witnesses
    have hFcard : ((insert [] D0).biUnion wit).card < s := by
      have hD0card : D0.card + 1 ≤ nodeCount ts := by
        have := card_le_card hsub
        rwa [card_insert_of_notMem hτ] at this
      calc ((insert [] D0).biUnion wit).card ≤ ∑ σ' ∈ insert [] D0, (wit σ').card :=
            card_biUnion_le
        _ = (insert [] D0).card * k := by
            apply sum_const_nat
            intro σ' hσ'
            rcases mem_insert.1 hσ' with heq | hmem
            · rw [heq, hw0, hcard e0 he0]
            · rw [hcard _ (hwH σ' hmem)]
        _ ≤ (D0.card + 1) * k := Nat.mul_le_mul_right _ (card_insert_le _ _)
        _ ≤ nodeCount ts * k := Nat.mul_le_mul_right _ hD0card
        _ < s := by
            have : k * nodeCount ts ≤ k * (nodeCount ts + 1) := Nat.mul_le_mul_left _ (by omega)
            rw [mul_comm]
            omega
    obtain ⟨f, hfH, hDf, hfF⟩ :=
      sunflower_avoid (hsun _ hwσ _ hjh) ((insert [] D0).biUnion wit) hFcard
    -- notation for the parent's core and the new pair
    set j := τ.dropLast.length with hj
    set D := wit τ.dropLast ∩ (Ich j).biUnion X with hD
    have hτj : τ.length = j + 1 := by omega
    have hfD : f ∩ (Ich j).biUnion X = D :=
      proj_eq_of_subset X hX (hpart _ hwσ) (hpart f hfH) hDf
    have hDsub : D ⊆ f ∩ (Ifull h Ich (j + 1)).biUnion X := by
      rw [← hfD, ← Ifull_of_lt Ich hjh]
      exact proj_mono X (Ifull_mono hIm hjh)
    set P := (f ∩ (Ifull h Ich (j + 1)).biUnion X) \ D with hP
    have hPf : P ⊆ f \ D := sdiff_subset_sdiff inter_subset_left subset_rfl
    have hPF : Disjoint P ((insert [] D0).biUnion wit) := Disjoint.mono_left hPf hfF
    -- every earlier witness lies in the forbidden set
    have hwF : ∀ σ' ∈ insert [] D0, wit σ' ⊆ (insert [] D0).biUnion wit :=
      fun σ' hσ' => subset_biUnion_of_mem wit hσ'
    have hR0F : R0 ⊆ (insert [] D0).biUnion wit := by
      have := hwF [] (mem_insert_self _ _)
      rw [hw0] at this
      exact inter_subset_left.trans this
    have hprF : ∀ σ' ∈ D0, pr σ' ⊆ (insert [] D0).biUnion wit := by
      intro σ' hσ'
      have hσ'nil : σ' ≠ [] :=
        List.length_pos_iff.1 (length_of_mem_nodePaths (hD0sub hσ')).1
      refine (pr_subset_pathSet R0 pr hσ'nil).trans ?_
      rw [← hI2 σ' (mem_insert_of_mem hσ')]
      exact inter_subset_left.trans (hwF σ' (mem_insert_of_mem hσ'))
    have hpathold : ∀ σ' ∈ insert [] D0,
        pathSet R0 (Function.update pr τ P) σ' = pathSet R0 pr σ' := fun σ' hσ' =>
      pathSet_update R0 pr P (hold σ' hσ').1 (hold σ' hσ').2
    refine ⟨Function.update wit τ f, Function.update pr τ P, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- root witness
      rw [Function.update_of_ne hτnil.symm, hw0]
    · -- witnesses lie in `Hs`
      intro σ' hσ'
      rcases mem_insert.1 hσ' with heq | hmem
      · rw [heq, Function.update_self]
        exact hfH
      · rw [Function.update_of_ne (hold σ' (mem_insert_of_mem hmem)).1]
        exact hwH σ' hmem
    · -- path sets are projections of witnesses
      intro σ' hσ'
      rcases mem_insert.1 hσ' with heq | hmem'
      · -- σ' = [] : unchanged
        rw [heq, Function.update_of_ne hτnil.symm, hpathold [] (mem_insert_self _ _)]
        exact hI2 [] (mem_insert_self _ _)
      · rcases mem_insert.1 hmem' with heq | hmem
        · -- the new node
          rw [heq, Function.update_self, pathSet_eq_dropLast R0 _ hτnil,
            hpathold _ hσmem, Function.update_self, ← hDpath, hτj]
          exact (union_sdiff_of_subset hDsub).symm
        · have hσ'1 : σ' ∈ insert [] D0 := mem_insert_of_mem hmem
          rw [Function.update_of_ne (hold σ' hσ'1).1, hpathold σ' hσ'1]
          exact hI2 σ' hσ'1
    · -- pairs have two points
      intro σ' hσ'
      rcases mem_insert.1 hσ' with heq | hmem
      · rw [heq, Function.update_self, hP, card_sdiff_of_subset hDsub,
          card_proj X hX (hpart f hfH), card_proj X hX (hpart _ hwσ),
          card_Ifull hk hIc (by omega : j + 1 ≤ h), hIc j hjh]
        omega
      · rw [Function.update_of_ne (hold σ' (mem_insert_of_mem hmem)).1]
        exact hc2 σ' hmem
    · -- pairs avoid the root
      intro σ' hσ'
      rcases mem_insert.1 hσ' with heq | hmem
      · rw [heq, Function.update_self]
        exact Disjoint.mono_right hR0F hPF
      · rw [Function.update_of_ne (hold σ' (mem_insert_of_mem hmem)).1]
        exact hdR σ' hmem
    · -- pairs are pairwise disjoint
      intro σ₁ hσ₁ σ₂ hσ₂ hne
      rcases mem_insert.1 hσ₁ with h1 | h1 <;> rcases mem_insert.1 hσ₂ with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [h1, Function.update_self, Function.update_of_ne (hold σ₂ (mem_insert_of_mem h2)).1]
        exact Disjoint.mono_right (hprF σ₂ h2) hPF
      · rw [h2, Function.update_self, Function.update_of_ne (hold σ₁ (mem_insert_of_mem h1)).1]
        exact (Disjoint.mono_right (hprF σ₁ h1) hPF).symm
      · rw [Function.update_of_ne (hold σ₁ (mem_insert_of_mem h1)).1,
          Function.update_of_ne (hold σ₂ (mem_insert_of_mem h2)).1]
        exact hdP σ₁ h1 σ₂ h2 hne

end EmbedCore

/-- **Embedding core.**  `k = p + 2h`; every edge of `Hs` meets each part `X i` in exactly one
point; `Ich 0 ⊂ ⋯ ⊂ Ich (h-1)` is a chain with `|Ich j| = p + 2j`; for every edge `e` and `j < h`
the kernel `e ∩ ⋃_{i ∈ Ich j} X i` is the exact core of an `s`-member sunflower of `Hs`;
and `s > k (nodeCount ts + 1)`.  Then every shape `ts` of length `h` with positive branch numbers
has a validly labelled copy inside `Hs`. -/
theorem embed_tree (k p h s : ℕ) (hp : p = 1 ∨ p = 2) (hh : 1 ≤ h) (hk : k = p + 2 * h)
    (Hs : Fam) (X : Fin k → Finset ℕ) (Ich : ℕ → Finset (Fin k)) (hne : Hs.Nonempty)
    (hX : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hcard : ∀ e ∈ Hs, e.card = k)
    (hpart : ∀ e ∈ Hs, ∀ i, (e ∩ X i).card = 1)
    (hIc : ∀ j < h, (Ich j).card = p + 2 * j)
    (hIm : ∀ j, j + 1 < h → Ich j ⊆ Ich (j + 1))
    (hsun : ∀ e ∈ Hs, ∀ j < h, IsSunflower Hs s (e ∩ (Ich j).biUnion X))
    (ts : List ℕ) (hts : ts.length = h) (hts1 : ∀ t ∈ ts, 1 ≤ t)
    (hs : k * (nodeCount ts + 1) < s) :
    ∃ (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ), R0.card = p ∧ ValidLabel ts R0 pr ∧
      treeCfg ts R0 pr ⊆ Hs := by
  obtain ⟨e0, he0⟩ := hne
  obtain ⟨wit, pr, -, hwH, hI2, hc2, hdR, hdP⟩ :=
    EmbedCore.main_ind k p h s hh hk Hs X Ich hX hcard hpart hIc hIm hsun ts hts hs e0 he0
      (nodePaths ts) subset_rfl (fun τ hτ h2 => EmbedCore.dropLast_mem_nodePaths hτ h2)
  refine ⟨e0 ∩ (Ich 0).biUnion X, pr, ?_, ⟨hc2, hdR, hdP⟩, ?_⟩
  · rw [EmbedCore.card_proj X hX (hpart e0 he0), hIc 0 (by omega)]
    omega
  · intro g hg
    unfold treeCfg at hg
    obtain ⟨π, hπ, rfl⟩ := mem_image.1 hg
    have hπN : π ∈ nodePaths ts := EmbedCore.leaf_mem_nodePaths (by omega) hπ
    have hπlen : π.length = h := (EmbedCore.length_of_mem_leafPaths hπ).trans hts
    have hw := hwH π hπN
    have key := hI2 π (mem_insert_of_mem hπN)
    rw [hπlen, EmbedCore.Ifull_self,
      EmbedCore.proj_univ X hX (hpart _ hw) (hcard _ hw)] at key
    rw [← key]
    exact hw

end Results.FcMorrisV2
