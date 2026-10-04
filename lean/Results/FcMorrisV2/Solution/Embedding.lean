import Results.FcMorrisV2.Solution.Chain
import Results.FcMorrisV2.Solution.EmbedCore

/-!
# Solution/Embedding: Füredi's theorem forces the tree configuration (paper Section 4)

Projection bound (Lemma 4.2), embedding (Lemma 4.4) and the extremal bound (Corollary 4.5), in the
form: a `k`-uniform hypergraph `H` on `[n]` with more than `A · C(n, k-2)` edges contains a
validly labelled copy of the tree configuration of any given shape.
-/

namespace Results.FcMorrisV2

open Finset

namespace Embedding

/-- The projection `e ↦ e ∩ ⋃_{i ∈ I} X i` of an edge meeting every (pairwise disjoint) part in
exactly one point has exactly `|I|` points. -/
lemma card_proj {k : ℕ} (X : Fin k → Finset ℕ) (hX : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (e : Finset ℕ) (he : ∀ i, (e ∩ X i).card = 1) (I : Finset (Fin k)) :
    (e ∩ I.biUnion X).card = I.card := by
  rw [inter_biUnion, card_biUnion]
  · simp only [he]
    exact (card_eq_sum_ones I).symm
  · intro i _ j _ hij
    exact Disjoint.mono inter_subset_right inter_subset_right (hX i j hij)

/-- **Projection bound** (paper Lemma 4.2), general form.  If no member of the common pattern `J`
contains `I`, then the projection `e ↦ e ∩ ⋃_{i ∈ I} X i` is injective on `Hs` (two distinct
edges with equal projections would have an intersection pattern containing `I`), and it takes
values among the `|I|`-subsets of `[n]`; hence `|Hs| ≤ C(n, |I|)`. -/
lemma card_le_choose_of_not_covered {k n : ℕ} (Hs : Fam) (X : Fin k → Finset ℕ)
    (J : Finset (Finset (Fin k)))
    (hrange : ∀ e ∈ Hs, e ⊆ range n)
    (hX : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hpart : ∀ e ∈ Hs, ∀ i, (e ∩ X i).card = 1)
    (hpat : ∀ e ∈ Hs, (Hs.erase e).image
        (fun f => (Finset.univ : Finset (Fin k)).filter fun i => (e ∩ f ∩ X i).Nonempty) = J)
    (I : Finset (Fin k)) (hI : ∀ I' ∈ J, ¬ I ⊆ I') :
    Hs.card ≤ n.choose I.card := by
  have key := card_le_card_of_injOn (s := Hs) (t := (range n).powersetCard I.card)
    (fun e => e ∩ I.biUnion X) ?_ ?_
  · rwa [card_powersetCard, card_range] at key
  · intro e he
    rw [mem_coe] at he
    rw [mem_coe, mem_powersetCard]
    exact ⟨inter_subset_left.trans (hrange e he), card_proj X hX e (hpart e he) I⟩
  · intro e he f hf hef
    rw [mem_coe] at he hf
    simp only at hef
    by_contra hne
    apply hI ((Finset.univ : Finset (Fin k)).filter fun i => (e ∩ f ∩ X i).Nonempty)
    · rw [← hpat e he]
      exact mem_image_of_mem _ (mem_erase.mpr ⟨Ne.symm hne, hf⟩)
    · intro i hi
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      obtain ⟨x, hx⟩ := card_eq_one.mp (hpart e he i)
      have hxe : x ∈ e ∩ X i := by rw [hx]; exact mem_singleton_self x
      have hxp : x ∈ e ∩ I.biUnion X :=
        mem_inter.mpr ⟨(mem_inter.mp hxe).1, mem_biUnion.mpr ⟨i, hi, (mem_inter.mp hxe).2⟩⟩
      rw [hef] at hxp
      exact ⟨x, mem_inter.mpr ⟨mem_inter.mpr ⟨(mem_inter.mp hxe).1, (mem_inter.mp hxp).1⟩,
        (mem_inter.mp hxe).2⟩⟩

/-- `ex_tree` with the uniformity `k = p + 2h` as a separate variable. -/
theorem ex_tree_aux (hFur : FurediSemilattice) (k p h : ℕ) (hk : k = p + 2 * h)
    (hp : p = 1 ∨ p = 2) (hh : 1 ≤ h)
    (ts : List ℕ) (hts : ts.length = h) (hts1 : ∀ t ∈ ts, 1 ≤ t) :
    ∃ A : ℕ, ∀ (n : ℕ) (H : Fam), (∀ e ∈ H, e ⊆ range n ∧ e.card = k) →
      A * n.choose (k - 2) < H.card →
      ∃ (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ), R0.card = p ∧ ValidLabel ts R0 pr ∧
        treeCfg ts R0 pr ⊆ H := by
  have hk3 : 3 ≤ k := by omega
  obtain ⟨gam, hgam, hF⟩ := hFur k (k * (nodeCount ts + 1) + 1) (by omega) (Nat.succ_pos _)
  -- `A := den γ`, so that `γ · A = num γ ≥ 1` (this plays the role of `⌈1/γ⌉`).
  refine ⟨gam.den, ?_⟩
  intro n H hH hA
  have hHne : H.Nonempty := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hA)
  obtain ⟨Hs, X, J, hsub, hgamHs, hX, hpart, hJ1, hJ2, hpat, hsun⟩ := hF n H hHne hH
  -- Step 1: `|Hs| ≥ γ |H| > γ A C(n, k-2) ≥ C(n, k-2)`.
  have hbig : n.choose (k - 2) < Hs.card := by
    have h1 : (1 : ℚ) ≤ gam * ((gam.den : ℕ) : ℚ) := by
      rw [Rat.mul_den_eq_num]
      have h0 : 0 < gam.num := Rat.num_pos.mpr hgam
      exact_mod_cast (show (1 : ℤ) ≤ gam.num by omega)
    have h2 : ((gam.den : ℕ) : ℚ) * ((n.choose (k - 2) : ℕ) : ℚ) < ((H.card : ℕ) : ℚ) := by
      exact_mod_cast hA
    have hC : (0 : ℚ) ≤ ((n.choose (k - 2) : ℕ) : ℚ) := Nat.cast_nonneg _
    have h3 : ((n.choose (k - 2) : ℕ) : ℚ) < ((Hs.card : ℕ) : ℚ) :=
      calc ((n.choose (k - 2) : ℕ) : ℚ) = 1 * ((n.choose (k - 2) : ℕ) : ℚ) := (one_mul _).symm
        _ ≤ (gam * ((gam.den : ℕ) : ℚ)) * ((n.choose (k - 2) : ℕ) : ℚ) :=
          mul_le_mul_of_nonneg_right h1 hC
        _ = gam * (((gam.den : ℕ) : ℚ) * ((n.choose (k - 2) : ℕ) : ℚ)) := mul_assoc _ _ _
        _ < gam * ((H.card : ℕ) : ℚ) := mul_lt_mul_of_pos_left h2 hgam
        _ ≤ ((Hs.card : ℕ) : ℚ) := hgamHs
    exact_mod_cast h3
  -- Step 2: projection bound -- every `(k-2)`-subset of `[k]` lies in a member of `J`.
  have hcov : ∀ I : Finset (Fin k), I.card = k - 2 → ∃ I' ∈ J, I ⊆ I' := by
    intro I hI
    by_contra hcon
    have hle := card_le_choose_of_not_covered Hs X J (fun e he => (hH e (hsub he)).1) hX hpart
      hpat I (fun I' hI' hII' => hcon ⟨I', hI', hII'⟩)
    rw [hI] at hle
    exact absurd hbig (not_lt.mpr hle)
  -- Step 3: parity chain of kernels.
  obtain ⟨Ich, hIch, hImono⟩ := chain_lemma k p h hk3 hp hk J hJ1 hJ2 hcov
  -- Step 4: top-down embedding inside `Hs ⊆ H`.
  have hHsne : Hs.Nonempty := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hbig)
  obtain ⟨R0, pr, hR0, hval, hsubT⟩ := embed_tree k p h (k * (nodeCount ts + 1) + 1) hp hh hk
    Hs X Ich hHsne hX (fun e he => (hH e (hsub he)).2) hpart (fun j hj => (hIch j hj).2) hImono
    (fun e he j hj => hsun e he (Ich j) (hIch j hj).1) ts hts hts1 (lt_add_one _)
  exact ⟨R0, pr, hR0, hval, hsubT.trans hsub⟩

end Embedding

/-- **Extremal bound for the recursive configurations** (paper Corollary 4.5), assuming
Füredi's theorem. -/
theorem ex_tree (hFur : FurediSemilattice) (p h : ℕ) (hp : p = 1 ∨ p = 2) (hh : 1 ≤ h)
    (ts : List ℕ) (hts : ts.length = h) (hts1 : ∀ t ∈ ts, 1 ≤ t) :
    ∃ A : ℕ, ∀ (n : ℕ) (H : Fam), (∀ e ∈ H, e ⊆ range n ∧ e.card = p + 2 * h) →
      A * n.choose (p + 2 * h - 2) < H.card →
      ∃ (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ), R0.card = p ∧ ValidLabel ts R0 pr ∧
        treeCfg ts R0 pr ⊆ H :=
  Embedding.ex_tree_aux hFur (p + 2 * h) p h rfl hp hh ts hts hts1

end Results.FcMorrisV2
