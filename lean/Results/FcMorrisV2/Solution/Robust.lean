import Results.FcMorrisV2.Solution.Basic

/-!
# Solution/Robust: robust certificates, defect lemma, seeds (paper Section 2, end)
-/

namespace Results.FcMorrisV2

open Finset

/-- `x_C^V(K)`: sets `A ⊆ V ∖ C` with `A ∉ K` but `A ∪ C ∈ K` (paper (2.5)). -/
def xcount (V : Finset ℕ) (K : Fam) (C : Finset ℕ) : ℕ :=
  ((V \ C).powerset.filter fun A => A ∉ K ∧ A ∪ C ∈ K).card

/-- `y_C(K)`: members `A ∈ K` with `A ∪ C ∉ K` (all stability failures; paper (2.6)). -/
def ycount (K : Fam) (C : Finset ℕ) : ℕ := (K.filter fun A => A ∪ C ∉ K).card

/-- A nonempty configuration of nonempty sets is *robustly FC* with weights `w` and margin `δ`:
`Q_w(K) ≥ δ ∑_{C ∈ G} x_C^V(K)` for every `G`-admissible `K`. -/
def RobustFC (G : Fam) (w : ℕ → ℚ) (δ : ℚ) : Prop :=
  G.Nonempty ∧ (∀ C ∈ G, C.Nonempty) ∧ (∀ u, 0 ≤ w u) ∧ 0 < ∑ u ∈ supp G, w u ∧ 0 < δ ∧
    ∀ K : Fam, Admissible G K →
      δ * ∑ C ∈ G, (xcount (supp G) K C : ℚ) ≤ share w (supp G) K

/-- Robustly FC implies FC (weighted transfer). -/
theorem RobustFC.isFC {G : Fam} {w : ℕ → ℚ} {δ : ℚ} (h : RobustFC G w δ) : IsFC G := by
  obtain ⟨-, -, hw, hW, hδ, hrob⟩ := h
  refine isFC_of_weights G w hw hW fun B hB => le_trans ?_ (hrob B hB)
  exact mul_nonneg hδ.le (sum_nonneg fun C _ => Nat.cast_nonneg _)

namespace Robust

/-- Each boundary count is at most `2^|V|`. -/
theorem xcount_le (V : Finset ℕ) (K : Fam) (C : Finset ℕ) : xcount V K C ≤ 2 ^ V.card := by
  unfold xcount
  calc _ ≤ (V \ C).powerset.card := card_filter_le _ _
    _ = 2 ^ (V \ C).card := card_powerset _
    _ ≤ 2 ^ V.card := Nat.pow_le_pow_right (by norm_num) (card_le_card sdiff_subset)

/-- Crude lower bound `Q_w(K) ≥ -(W/2) 2^|V|` for a family of subsets of `V`. -/
theorem share_ge (w : ℕ → ℚ) (hw : ∀ u, 0 ≤ w u) (V : Finset ℕ) (hW : 0 ≤ ∑ u ∈ V, w u)
    (K : Fam) (hK : ∀ X ∈ K, X ⊆ V) :
    -((∑ u ∈ V, w u) / 2) * 2 ^ V.card ≤ share w V K := by
  unfold share
  have hcard : (K.card : ℚ) ≤ 2 ^ V.card := by
    have h1 : K.card ≤ 2 ^ V.card := by
      calc K.card ≤ V.powerset.card := card_le_card fun X hX => mem_powerset.mpr (hK X hX)
        _ = 2 ^ V.card := card_powerset _
    exact_mod_cast h1
  have h2 : 0 ≤ (∑ u ∈ V, w u) / 2 := by linarith
  calc -((∑ u ∈ V, w u) / 2) * 2 ^ V.card ≤ -((∑ u ∈ V, w u) / 2) * K.card := by
        have := mul_le_mul_of_nonneg_left hcard h2
        linarith
    _ = ∑ _X ∈ K, -((∑ u ∈ V, w u) / 2) := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ X ∈ K, (∑ u ∈ X, w u - (∑ u ∈ V, w u) / 2) := by
        refine sum_le_sum fun X _ => ?_
        have : 0 ≤ ∑ u ∈ X, w u := sum_nonneg fun u _ => hw u
        linarith

/-- The boundary count of the whole ground set. -/
theorem xcount_self (V : Finset ℕ) (K : Fam) :
    xcount V K V = if (∅ ∉ K ∧ V ∈ K) then 1 else 0 := by
  unfold xcount
  rw [Finset.sdiff_self, powerset_empty, filter_singleton, empty_union]
  split_ifs <;> rfl

/-- Share with unit weights. -/
theorem share_one (V : Finset ℕ) (K : Fam) :
    share (fun _ => 1) V K = ∑ X ∈ K, ((X.card : ℚ) - (V.card : ℚ) / 2) := by
  simp only [share, sum_const, nsmul_eq_mul, mul_one]

/-- Pointwise share on the singleton universe. -/
theorem local_singleton (u : ℕ) (X : Finset ℕ) (hX : X ⊆ {u}) :
    (X.card : ℚ) - (({u} : Finset ℕ).card : ℚ) / 2 =
      (1 / 2) * ((if X = {u} then 1 else 0) - (if X = ∅ then 1 else 0)) := by
  rw [card_singleton]
  rcases subset_singleton_iff.mp hX with h | h
  · subst h
    have hne : (∅ : Finset ℕ) ≠ {u} := (singleton_ne_empty u).symm
    rw [if_neg hne, if_pos rfl, card_empty]
    norm_num
  · subst h
    rw [if_pos rfl, if_neg (singleton_ne_empty u), card_singleton]
    norm_num

/-- Pointwise share on the pair universe. -/
theorem local_pair {u v : ℕ} (huv : u ≠ v) (X : Finset ℕ) (hX : X ⊆ {u, v}) :
    (X.card : ℚ) - (({u, v} : Finset ℕ).card : ℚ) / 2 =
      ((if X = {u, v} then 1 else 0) - (if X = ∅ then 1 else 0)) := by
  have h2 : ({u, v} : Finset ℕ).card = 2 := card_pair huv
  rw [h2]
  have hle : X.card ≤ 2 := h2 ▸ card_le_card hX
  have hne : ({u, v} : Finset ℕ) ≠ ∅ := ne_empty_of_mem (mem_insert_self u {v})
  rcases (show X.card = 0 ∨ X.card = 1 ∨ X.card = 2 by omega) with h | h | h
  · have hX0 : X = ∅ := card_eq_zero.mp h
    subst hX0
    rw [if_neg hne.symm, if_pos rfl, card_empty]
    norm_num
  · have h1 : X ≠ {u, v} := fun he => by rw [he, h2] at h; exact absurd h (by norm_num)
    have h0 : X ≠ ∅ := fun he => by rw [he, card_empty] at h; exact absurd h (by norm_num)
    rw [if_neg h1, if_neg h0, h]
    norm_num
  · have hXV : X = {u, v} := eq_of_subset_of_card_le hX (by rw [h2, h])
    subst hXV
    rw [if_pos rfl, if_neg hne, h2]
    norm_num

/-- Support of a single generator. -/
theorem supp_singleton (C : Finset ℕ) : supp ({C} : Fam) = C := by
  simp only [supp, singleton_biUnion, id]

end Robust

open Robust in
/-- Paper Lemma 2.7 (finite-defect bound). -/
theorem defect_bound {G : Fam} {w : ℕ → ℚ} {δ : ℚ} (h : RobustFC G w δ) (K : Fam)
    (hK : (∀ X ∈ K, X ⊆ supp G) ∧ UnionClosed K) :
    δ * ∑ C ∈ G, (xcount (supp G) K C : ℚ) -
      (2 ^ (supp G).card * ((G.card : ℚ) * δ + (∑ u ∈ supp G, w u) / 2)) *
        ∑ C ∈ G, (ycount K C : ℚ) ≤ share w (supp G) K := by
  obtain ⟨-, -, hw, hW, hδ, hrob⟩ := h
  by_cases hY : ∀ C ∈ G, ycount K C = 0
  · have hadm : Admissible G K := by
      refine ⟨hK.1, hK.2, fun X hX g hg => ?_⟩
      have h0 := hY g hg
      unfold ycount at h0
      rw [card_eq_zero, filter_eq_empty_iff] at h0
      by_contra hc
      exact h0 hX hc
    have hsum : ∑ C ∈ G, (ycount K C : ℚ) = 0 :=
      sum_eq_zero fun C hC => by rw [hY C hC, Nat.cast_zero]
    rw [hsum, mul_zero, sub_zero]
    exact hrob K hadm
  · push Not at hY
    obtain ⟨C₀, hC₀, hy₀⟩ := hY
    have hY1 : (1 : ℚ) ≤ ∑ C ∈ G, (ycount K C : ℚ) := by
      have h1 : (ycount K C₀ : ℚ) ≤ ∑ C ∈ G, (ycount K C : ℚ) :=
        single_le_sum (f := fun C => (ycount K C : ℚ)) (fun C _ => Nat.cast_nonneg _) hC₀
      have h2 : (1 : ℚ) ≤ ycount K C₀ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hy₀
      linarith
    have hX : ∑ C ∈ G, (xcount (supp G) K C : ℚ) ≤ G.card * 2 ^ (supp G).card := by
      calc ∑ C ∈ G, (xcount (supp G) K C : ℚ) ≤ ∑ _C ∈ G, (2 : ℚ) ^ (supp G).card :=
            sum_le_sum fun C _ => by exact_mod_cast xcount_le (supp G) K C
        _ = G.card * 2 ^ (supp G).card := by rw [sum_const, nsmul_eq_mul]
    have hQ := share_ge w hw (supp G) hW.le K hK.1
    have hL : 0 ≤ 2 ^ (supp G).card * ((G.card : ℚ) * δ + (∑ u ∈ supp G, w u) / 2) := by
      have h3 : 0 ≤ (G.card : ℚ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
      have h4 : 0 ≤ (G.card : ℚ) * δ + (∑ u ∈ supp G, w u) / 2 := by linarith
      exact mul_nonneg (pow_nonneg (by norm_num) _) h4
    have h1 := mul_le_mul_of_nonneg_left hX hδ.le
    have h2 := mul_le_mul_of_nonneg_left hY1 hL
    linarith

open Robust in
/-- Paper Lemma 2.8 (seeds), singleton. -/
theorem robust_singleton (u : ℕ) : RobustFC ({({u} : Finset ℕ)} : Fam) (fun _ => 1) (1 / 2) := by
  have hsupp : supp ({({u} : Finset ℕ)} : Fam) = {u} := supp_singleton _
  refine ⟨singleton_nonempty _, fun C hC => ?_, fun _ => zero_le_one, ?_, by norm_num, ?_⟩
  · rw [mem_singleton.mp hC]; exact singleton_nonempty u
  · rw [hsupp, sum_singleton]; norm_num
  · intro K hK
    obtain ⟨hsub, -, hstab⟩ := hK
    rw [hsupp] at hsub
    rw [hsupp, sum_singleton, xcount_self, share_one]
    rw [sum_congr rfl fun X hX => local_singleton u X (hsub X hX), ← mul_sum, sum_sub_distrib,
      sum_ite_eq', sum_ite_eq']
    have hst : ∅ ∈ K → ({u} : Finset ℕ) ∈ K := fun h0 => by
      simpa using hstab ∅ h0 {u} (mem_singleton_self _)
    by_cases h0 : (∅ : Finset ℕ) ∈ K
    · rw [if_pos h0, if_pos (hst h0), if_neg (fun h => h.1 h0)]
      norm_num
    · by_cases h1 : ({u} : Finset ℕ) ∈ K
      · rw [if_pos h1, if_neg h0, if_pos ⟨h0, h1⟩]
        norm_num
      · rw [if_neg h1, if_neg h0, if_neg (fun h => h1 h.2)]
        norm_num

open Robust in
/-- Paper Lemma 2.8 (seeds), pair. -/
theorem robust_pair {u v : ℕ} (h : u ≠ v) :
    RobustFC ({({u, v} : Finset ℕ)} : Fam) (fun _ => 1) 1 := by
  have hsupp : supp ({({u, v} : Finset ℕ)} : Fam) = {u, v} := supp_singleton _
  refine ⟨singleton_nonempty _, fun C hC => ?_, fun _ => zero_le_one, ?_, by norm_num, ?_⟩
  · rw [mem_singleton.mp hC]; exact insert_nonempty u {v}
  · rw [hsupp, sum_const, nsmul_eq_mul, mul_one, card_pair h]; norm_num
  · intro K hK
    obtain ⟨hsub, -, hstab⟩ := hK
    rw [hsupp] at hsub
    rw [hsupp, sum_singleton, xcount_self, share_one]
    rw [sum_congr rfl fun X hX => local_pair h X (hsub X hX), sum_sub_distrib,
      sum_ite_eq', sum_ite_eq']
    have hst : ∅ ∈ K → ({u, v} : Finset ℕ) ∈ K := fun h0 => by
      simpa using hstab ∅ h0 {u, v} (mem_singleton_self _)
    by_cases h0 : (∅ : Finset ℕ) ∈ K
    · rw [if_pos h0, if_pos (hst h0), if_neg (fun h => h.1 h0)]
      norm_num
    · by_cases h1 : ({u, v} : Finset ℕ) ∈ K
      · rw [if_pos h1, if_neg h0, if_pos ⟨h0, h1⟩]
        norm_num
      · rw [if_neg h1, if_neg h0, if_neg (fun h => h1 h.2)]
        norm_num

end Results.FcMorrisV2
