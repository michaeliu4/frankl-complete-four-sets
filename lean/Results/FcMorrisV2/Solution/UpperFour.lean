import Results.FcMorrisV2.Solution.SunflowerPos
import Results.FcMorrisV2.Solution.Elementary

/-!
# Solution/UpperFour: upper bounds for `FC(4,n)` (Theorem 1.3(b), 1.3(c) upper)

* `not_isFC_no_sunflower_nine`: a nine-petal two-core sunflower of a four-uniform configuration is
  a copy of `S_9`, which is FC (`sunflower_isFC`), so a non-FC configuration has none.
* `isFC_blocks_four`: for `n ≥ 20` the complete four-uniform hypergraph contains `S_9`, hence is FC.
* `upper_explicit`: Theorem 1.3(b), via `four_bound` with `k = 9`.
* `upper_asymp`: Theorem 1.3(c) upper bound, via the vertex-link reduction and the Chung–Frankl
  bound for each link.
-/

namespace Results.FcMorrisV2

open Finset

namespace UpperFour

/-- Enumerate a finite family of `t` sets by `Fin t`. -/
lemma exists_enum (S : Fam) {t : ℕ} (hS : S.card = t) :
    ∃ e : Fin t → Finset ℕ, Function.Injective e ∧ (univ : Finset (Fin t)).image e = S := by
  subst hS
  refine ⟨fun i => ((S.equivFin.symm i : S) : Finset ℕ), ?_, ?_⟩
  · intro i j h
    exact S.equivFin.symm.injective (Subtype.ext h)
  · ext f
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (S.equivFin.symm i).2
    · intro hf
      exact ⟨S.equivFin ⟨f, hf⟩, by simp only [Equiv.symm_apply_apply]⟩

end UpperFour

/-- A non-FC four-uniform configuration contains no nine-petal sunflower with a two-point core
(because such a sunflower is a copy of the FC configuration `S_9`, Theorem 1.2). -/
theorem not_isFC_no_sunflower_nine (H : Fam) (hH : ∀ f ∈ H, f.card = 4) (hnf : ¬ IsFC H) :
    ¬ ∃ D : Finset ℕ, D.card = 2 ∧ IsSunflower H 9 D := by
  rintro ⟨D, hD, S, hSH, hS9, hDS, hSS⟩
  rw [mem_powerset] at hSH
  obtain ⟨e, he_inj, hS⟩ := UpperFour.exists_enum S hS9
  have he : ∀ i, e i ∈ S := fun i => hS ▸ mem_image_of_mem e (mem_univ i)
  have hd : SunflowerData 9 D (fun i => e i \ D) := by
    refine ⟨hD, ?_, ?_, ?_⟩
    · intro i
      rw [card_sdiff, inter_eq_left.mpr (hDS (e i) (he i)), hH (e i) (hSH (he i)), hD]
    · intro i
      exact disjoint_sdiff
    · intro i j hij
      rw [disjoint_left]
      intro x hxi hxj
      rw [mem_sdiff] at hxi hxj
      have hx : x ∈ e i ∩ e j := mem_inter.mpr ⟨hxi.1, hxj.1⟩
      rw [hSS (e i) (he i) (e j) (he j) (fun h => hij (he_inj h))] at hx
      exact hxi.2 hx
  have hcfg : sunflowerCfg 9 D (fun i => e i \ D) = S := by
    rw [← hS, sunflowerCfg]
    congr 1
    funext i
    exact union_sdiff_of_subset (hDS (e i) (he i))
  have hFC : IsFC S := hcfg ▸ sunflower_isFC hd (le_refl 9)
  exact hnf (isFC_mono hSH hFC)

/-- For `n ≥ 20` the complete four-uniform hypergraph on `[n]` contains a copy of `S_9`
(core `{0,1}`, petals `{2+2i, 3+2i}`, `i < 9`), hence is FC. -/
theorem isFC_blocks_four (n : ℕ) (hn : 20 ≤ n) : IsFC (blocks 4 n) := by
  have hd : SunflowerData 9 {0, 1} (fun i : Fin 9 => {2 + 2 * (i : ℕ), 3 + 2 * (i : ℕ)}) := by
    refine ⟨card_pair (by omega), ?_, ?_, ?_⟩
    · intro i
      exact card_pair (by omega)
    · intro i
      rw [disjoint_left]
      intro x hx hx'
      rw [mem_insert, mem_singleton] at hx hx'
      omega
    · intro i j hij
      have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
      rw [disjoint_left]
      intro x hx hx'
      rw [mem_insert, mem_singleton] at hx hx'
      omega
  refine isFC_mono ?_ (sunflower_isFC hd (le_refl 9))
  intro f hf
  rw [sunflowerCfg, mem_image] at hf
  obtain ⟨i, -, rfl⟩ := hf
  rw [blocks, mem_powersetCard]
  refine ⟨?_, ?_⟩
  · intro x hx
    have hi : (i : ℕ) < 9 := i.isLt
    rw [mem_union, mem_insert, mem_singleton, mem_insert, mem_singleton] at hx
    rw [mem_range]
    omega
  · rw [card_union_of_disjoint (hd.hCP i), hd.hC, hd.hP i]

namespace UpperFour

/-- If every non-FC subfamily of `blocks 4 n` has at most `B` members and `n ≥ 20`, then
`min (1 + B) (C(n,4))` is an admissible threshold size. -/
lemma allFC_min (n B : ℕ) (hn : 20 ≤ n)
    (hB : ∀ G ⊆ blocks 4 n, ¬ IsFC G → G.card ≤ B) :
    AllFC 4 n (min (1 + B) (n.choose 4)) := by
  have hpos : 0 < n.choose 4 := Nat.choose_pos (by omega)
  refine ⟨by omega, min_le_right _ _, ?_⟩
  intro G hG
  rw [mem_powersetCard] at hG
  obtain ⟨hGsub, hGcard⟩ := hG
  by_contra hnf
  have h1 := hB G hGsub hnf
  have hcard : (blocks 4 n).card = n.choose 4 := by
    rw [blocks, card_powersetCard, card_range]
  have h3 : G = blocks 4 n := eq_of_subset_of_card_le hGsub (by omega)
  exact hnf (h3 ▸ isFC_blocks_four n hn)

/-- Vertex-link bound: in a non-FC four-uniform `G` on `[n]`, `n ≥ 1694`, the number of members
through a fixed vertex `v` is at most `72 (n-1) + C₀`, by the Chung–Frankl bound applied to the link
of `v` (a one-core nine-petal sunflower of the link lifts to a two-core one of `G`). -/
lemma link_card_le (C₀ : ℕ)
    (hC₀ : ∀ V : Finset ℕ, 1692 < V.card → ∀ T : Fam, (∀ f ∈ T, f ⊆ V ∧ f.card = 3) →
      (¬ ∃ x : ℕ, IsSunflower T 9 {x}) → T.card ≤ 72 * V.card + C₀)
    (n : ℕ) (hn : 1694 ≤ n) (G : Fam) (hG : ∀ f ∈ G, f ⊆ range n ∧ f.card = 4)
    (hnf : ¬ IsFC G) (v : ℕ) (hv : v ∈ range n) :
    (G.filter fun f => v ∈ f).card ≤ 72 * (n - 1) + C₀ := by
  have hinj : Set.InjOn (fun f : Finset ℕ => f.erase v) ↑(G.filter fun f => v ∈ f) := by
    intro f hf f' hf' h
    rw [coe_filter] at hf hf'
    rw [← insert_erase hf.2, ← insert_erase hf'.2]
    exact congrArg (insert v) h
  have hVcard : ((range n).erase v).card = n - 1 := by
    rw [card_erase_of_mem hv, card_range]
  rw [← card_image_of_injOn hinj, ← hVcard]
  refine hC₀ ((range n).erase v) (by omega) _ ?_ ?_
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hg
    rw [mem_filter] at hf
    refine ⟨erase_subset_erase v (hG f hf.1).1, ?_⟩
    rw [card_erase_of_mem hf.2, (hG f hf.1).2]
  · rintro ⟨x, S, hSL, hS9, hxS, hSS⟩
    rw [mem_powerset] at hSL
    have hSv : ∀ g ∈ S, v ∉ g ∧ insert v g ∈ G := by
      intro g hg
      obtain ⟨f, hf, rfl⟩ := mem_image.mp (hSL hg)
      rw [mem_filter] at hf
      exact ⟨notMem_erase v f, by rw [insert_erase hf.2]; exact hf.1⟩
    obtain ⟨g₀, hg₀⟩ : S.Nonempty := by
      rw [← card_pos, hS9]
      norm_num
    have hxv : x ≠ v := by
      intro h
      apply (hSv g₀ hg₀).1
      rw [← h]
      exact hxS g₀ hg₀ (mem_singleton_self x)
    apply not_isFC_no_sunflower_nine G (fun f hf => (hG f hf).2) hnf
    refine ⟨{x, v}, card_pair hxv, S.image (insert v), ?_, ?_, ?_, ?_⟩
    · rw [mem_powerset]
      intro f hf
      obtain ⟨g, hg, rfl⟩ := mem_image.mp hf
      exact (hSv g hg).2
    · rw [card_image_of_injOn, hS9]
      intro g hg g' hg' h
      have h' := congrArg (fun s : Finset ℕ => s.erase v) h
      rwa [erase_insert (hSv g hg).1, erase_insert (hSv g' hg').1] at h'
    · intro f hf
      obtain ⟨g, hg, rfl⟩ := mem_image.mp hf
      intro y hy
      rw [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact mem_insert_of_mem (hxS g hg (mem_singleton_self y))
      · exact mem_insert_self y g
    · intro f hf f' hf' hne
      obtain ⟨g, hg, rfl⟩ := mem_image.mp hf
      obtain ⟨g', hg', rfl⟩ := mem_image.mp hf'
      have hgg : g ≠ g' := fun h => hne (by rw [h])
      rw [← insert_inter_distrib, hSS g hg g' hg' hgg]
      exact pair_comm v x

/-- Double counting over vertex links: `4 |G| ≤ n (72 (n-1) + C₀)` for a non-FC four-uniform
configuration `G` on `[n]`, `n ≥ 1694`. -/
lemma four_mul_card_le (C₀ : ℕ)
    (hC₀ : ∀ V : Finset ℕ, 1692 < V.card → ∀ T : Fam, (∀ f ∈ T, f ⊆ V ∧ f.card = 3) →
      (¬ ∃ x : ℕ, IsSunflower T 9 {x}) → T.card ≤ 72 * V.card + C₀)
    (n : ℕ) (hn : 1694 ≤ n) (G : Fam) (hG : ∀ f ∈ G, f ⊆ range n ∧ f.card = 4)
    (hnf : ¬ IsFC G) :
    G.card * 4 ≤ n * (72 * (n - 1) + C₀) := by
  have key := sum_card_inter_le (s := range n) (B := G) (n := 72 * (n - 1) + C₀)
    (fun v hv => link_card_le C₀ hC₀ n hn G hG hnf v hv)
  rw [card_range] at key
  have hsum : ∑ t ∈ G, (range n ∩ t).card = ∑ _t ∈ G, 4 := by
    refine sum_congr rfl fun t ht => ?_
    rw [inter_eq_right.mpr (hG t ht).1, (hG t ht).2]
  rw [hsum, sum_const, Nat.nsmul_eq_mul] at key
  exact key

end UpperFour

/-- Theorem 1.3(b). -/
theorem upper_explicit (n : ℕ) (hn : 20 ≤ n) :
    FCle 4 n (((1 + 160 * n * (n - 1) / 3 : ℕ)) : ℚ) := by
  refine ⟨min (1 + 160 * n * (n - 1) / 3) (n.choose 4),
    UpperFour.allFC_min n _ hn ?_, ?_⟩
  · intro G hGsub hnf
    have hG : ∀ f ∈ G, f ⊆ range n ∧ f.card = 4 := fun f hf => mem_powersetCard.mp (hGsub hf)
    have hno := not_isFC_no_sunflower_nine G (fun f hf => (hG f hf).2) hnf
    have key := four_bound 9 (by norm_num) (range n) G hG hno
    rw [card_range] at key
    have e1 : 5 * (9 - 1) ^ 2 * n * (n - 1) = 320 * (n * (n - 1)) := by ring
    have e2 : 160 * n * (n - 1) = 160 * (n * (n - 1)) := by ring
    rw [e1] at key
    rw [Nat.le_div_iff_mul_le (by norm_num), e2]
    omega
  · exact_mod_cast min_le_left _ _

/-- Theorem 1.3(c), upper coefficient `18`, assuming the Chung–Frankl theorem. -/
theorem upper_asymp (hCF : ChungFranklNine) (ε : ℚ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → FCle 4 n ((18 + ε) * (n : ℚ) ^ 2) := by
  obtain ⟨C₀, hC₀⟩ := hCF
  refine ⟨max 1694 ((C₀ + 4) * ε.den), fun n hn => ?_⟩
  have hn1 : 1694 ≤ n := le_of_max_le_left hn
  have hn2 : (C₀ + 4) * ε.den ≤ n := le_of_max_le_right hn
  refine ⟨min (1 + n * (72 * (n - 1) + C₀) / 4) (n.choose 4),
    UpperFour.allFC_min n _ (by omega) ?_, ?_⟩
  · intro G hGsub hnf
    have hG : ∀ f ∈ G, f ⊆ range n ∧ f.card = 4 := fun f hf => mem_powersetCard.mp (hGsub hf)
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    exact UpperFour.four_mul_card_le C₀ hC₀ n hn1 G hG hnf
  · -- arithmetic: `1 + ⌊n (72 (n-1) + C₀) / 4⌋ ≤ (18 + ε) n²`
    set B := n * (72 * (n - 1) + C₀) / 4 with hB
    have h1 : ((min (1 + B) (n.choose 4) : ℕ) : ℚ) ≤ 1 + (B : ℚ) := by
      exact_mod_cast min_le_left _ _
    have h2 : 4 * B ≤ n * (72 * (n - 1) + C₀) := Nat.mul_div_le _ _
    have h2' : 4 * (B : ℚ) ≤ (n : ℚ) * (72 * ((n : ℚ) - 1) + (C₀ : ℚ)) := by
      have h := (Nat.cast_le (α := ℚ)).mpr h2
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at h
      exact h
    -- `ε n ≥ C₀ + 4`
    have hden : (1 : ℚ) ≤ ε * (ε.den : ℚ) := by
      rw [Rat.mul_den_eq_num]
      have : (1 : ℤ) ≤ ε.num := Rat.num_pos.mpr hε
      exact_mod_cast this
    have hn2' : ((C₀ : ℚ) + 4) * (ε.den : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn2
    have h3 : (C₀ : ℚ) + 4 ≤ ε * (n : ℚ) := by
      have hC : (0 : ℚ) ≤ (C₀ : ℚ) + 4 := by positivity
      calc (C₀ : ℚ) + 4 ≤ ((C₀ : ℚ) + 4) * (ε * (ε.den : ℚ)) := le_mul_of_one_le_right hC hden
        _ = ε * (((C₀ : ℚ) + 4) * (ε.den : ℚ)) := by ring
        _ ≤ ε * (n : ℚ) := mul_le_mul_of_nonneg_left hn2' hε.le
    have hn0 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (by omega : 1 ≤ n)
    have h4 : ((C₀ : ℚ) + 4) * (n : ℚ) ≤ ε * (n : ℚ) * (n : ℚ) :=
      mul_le_mul_of_nonneg_right h3 (by linarith)
    have hC0 : (0 : ℚ) ≤ (C₀ : ℚ) := Nat.cast_nonneg C₀
    have h5 : (0 : ℚ) ≤ (C₀ : ℚ) * (n : ℚ) := mul_nonneg hC0 (by linarith)
    calc ((min (1 + B) (n.choose 4) : ℕ) : ℚ) ≤ 1 + (B : ℚ) := h1
      _ ≤ (18 + ε) * (n : ℚ) ^ 2 := by linarith

end Results.FcMorrisV2
