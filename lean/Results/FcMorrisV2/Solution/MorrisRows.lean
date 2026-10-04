import Results.FcMorrisV2.Solution.MorrisDefs
import Results.FcMorrisV2.Solution.Product

/-!
# Solution/MorrisRows: exact imbalance rows of the coatom families of `M_{r,p}`
(paper Proposition B.3, rows (B.2)-(B.4)).

Proof outline.  By `rho_coatom`, `ρ_u(E_z) = -ρ_u(N_z)` for the omitted family `N_z`.
* Tail coatoms (`4r ≤ z`): `N_z` is the product (`prodFam`) of the 13-set block families `F13`
  on every block, `{{z}}` on `{z}`, and the full cube on the rest of the tail.
* Block coatoms (`z = 4 i₀ + t`): `N_z` is the disjoint union of two products over the blocks
  `Q_0, …, Q_{i₀}` and the later points `L_{i₀}`: `F13` on the earlier blocks, and on
  `(Q_{i₀}, L_{i₀})` either `(SA, full cube)` or `(SB, {∅})`.
The local counts of `F13`, `SA`, `SB` are computed on `range 4` (by translation and `decide`).
-/

namespace Results.FcMorrisV2

open Finset

namespace MorrisRows

/-! ## Generic facts about `deg` and `rho` -/

lemma deg_union {A B : Fam} (h : Disjoint A B) (u : ℕ) : deg (A ∪ B) u = deg A u + deg B u := by
  unfold deg
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

lemma rho_union {A B : Fam} (h : Disjoint A B) (u : ℕ) : rho (A ∪ B) u = rho A u + rho B u := by
  unfold rho
  rw [deg_union h, card_union_of_disjoint h]
  push_cast
  ring

lemma rho_prodFam {ι : Type*} [DecidableEq ι] (I : Finset ι) (V : ι → Finset ℕ)
    (hV : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (V i) (V j)) (Q : ι → Fam)
    (hQ : ∀ i ∈ I, Q i ⊆ (V i).powerset) {j : ι} (hj : j ∈ I) {u : ℕ} (hu : u ∈ V j) :
    rho (prodFam I V Q) u = rho (Q j) u * ((∏ i ∈ I.erase j, (Q i).card : ℕ) : ℤ) := by
  unfold rho
  rw [prodFam_deg I V hV Q hQ hj hu, prodFam_card I V hV Q hQ,
    ← mul_prod_erase I (fun i => (Q i).card) hj]
  push_cast
  ring

lemma prod_erase_eq {s : Finset ℕ} {f : ℕ → ℕ} {k : ℕ} (hk : k ∈ s) {c P : ℕ} (hc : 0 < c)
    (hfk : f k = c) (htot : ∏ x ∈ s, f x = c * P) : ∏ x ∈ s.erase k, f x = P := by
  have h := mul_prod_erase s f hk
  rw [hfk, htot] at h
  exact Nat.eq_of_mul_eq_mul_left hc h

lemma rho_singleton_empty (u : ℕ) : rho ({∅} : Fam) u = -1 := by
  simp [rho, deg]

lemma rho_singleton_self (z : ℕ) : rho ({{z}} : Fam) z = 1 := by
  unfold rho deg
  rw [filter_singleton, if_pos (mem_singleton_self z)]
  simp

lemma mem_prodFam_iff {ι : Type*} [DecidableEq ι] {I : Finset ι} {V : ι → Finset ℕ}
    {Q : ι → Fam} {A : Finset ℕ} :
    A ∈ prodFam I V Q ↔ A ⊆ I.biUnion V ∧ ∀ i ∈ I, A ∩ V i ∈ Q i := by
  simp only [prodFam, mem_filter, mem_powerset]

lemma forall_range_add_two {P : ℕ → Prop} {r : ℕ} :
    (∀ k ∈ range (r + 2), P k) ↔ (∀ k < r, P k) ∧ P r ∧ P (r + 1) := by
  simp only [mem_range]
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h r (by omega), h (r + 1) (by omega)⟩
  · rintro ⟨h1, h2, h3⟩ k hk
    rcases (by omega : k < r ∨ k = r ∨ k = r + 1) with h | rfl | rfl
    exacts [h1 k h, h2, h3]

/-! ## Local block families and their counts (translation to `range 4`) -/

lemma Ico_eq_image (m : ℕ) : Ico m (m + 4) = (range 4).image (m + ·) := by
  ext x
  simp only [mem_Ico, mem_image, mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x - m, by omega, by omega⟩
  · rintro ⟨a, ha, rfl⟩
    omega

lemma mem_shift (m k : ℕ) (B : Finset ℕ) : m + k ∈ B.image (m + ·) ↔ k ∈ B :=
  (add_right_injective m).mem_finset_image

lemma mem_shift_zero (m : ℕ) (B : Finset ℕ) : m ∈ B.image (m + ·) ↔ 0 ∈ B := by
  have h := mem_shift m 0 B
  rwa [add_zero] at h

lemma shift_card (m : ℕ) (P : Finset ℕ → Prop) [DecidablePred P]
    (P₀ : Finset ℕ → Prop) [DecidablePred P₀] (hP : ∀ B, P (B.image (m + ·)) ↔ P₀ B) :
    ((Ico m (m + 4)).powerset.filter P).card = ((range 4).powerset.filter P₀).card := by
  rw [Ico_eq_image, powerset_image, filter_image,
    card_image_of_injective _ (image_injective (add_right_injective m))]
  exact congrArg card (filter_congr fun B _ => hP B)

lemma shift_rho (m s : ℕ) (P : Finset ℕ → Prop) [DecidablePred P]
    (P₀ : Finset ℕ → Prop) [DecidablePred P₀] (hP : ∀ B, P (B.image (m + ·)) ↔ P₀ B) :
    rho ((Ico m (m + 4)).powerset.filter P) (m + s) = rho ((range 4).powerset.filter P₀) s := by
  unfold rho deg
  rw [filter_filter, filter_filter, shift_card m P P₀ hP,
    shift_card m _ (fun B => P₀ B ∧ s ∈ B) fun B => by rw [hP, mem_shift]]

/-- Subsets of the block `{m, m+1, m+2, m+3}` avoiding both triples `abc` and `abd`. -/
def F13 (m : ℕ) : Fam :=
  (Ico m (m + 4)).powerset.filter fun B =>
    ¬(m ∈ B ∧ m + 1 ∈ B ∧ m + 2 ∈ B) ∧ ¬(m ∈ B ∧ m + 1 ∈ B ∧ m + 3 ∈ B)

/-- Local traces on the block of `z = m + t` compatible with a nonempty later trace. -/
def SA (m t : ℕ) : Fam :=
  (Ico m (m + 4)).powerset.filter fun B => m + t ∈ B ∧
    (t ≠ 3 → ¬(m ∈ B ∧ m + 1 ∈ B ∧ m + 2 ∈ B)) ∧ (t ≠ 2 → ¬(m ∈ B ∧ m + 1 ∈ B ∧ m + 3 ∈ B))

/-- The remaining local traces (only allowed together with an empty later trace). -/
def SB (m t : ℕ) : Fam :=
  (Ico m (m + 4)).powerset.filter fun B => m + t ∈ B ∧
    ¬(m ∈ B ∧ m + 1 ∈ B ∧ m + 2 ∈ B ∧ m + 3 ∈ B) ∧
    ¬((t ≠ 3 → ¬(m ∈ B ∧ m + 1 ∈ B ∧ m + 2 ∈ B)) ∧
      (t ≠ 2 → ¬(m ∈ B ∧ m + 1 ∈ B ∧ m + 3 ∈ B)))

lemma F13_card (m : ℕ) : (F13 m).card = 13 := by
  rw [F13, shift_card m _ (fun B => ¬(0 ∈ B ∧ 1 ∈ B ∧ 2 ∈ B) ∧ ¬(0 ∈ B ∧ 1 ∈ B ∧ 3 ∈ B))
    fun B => by simp only [mem_shift, mem_shift_zero]]
  decide

lemma SA_card (m t : ℕ) (ht : t < 4) : (SA m t).card = if t < 2 then 5 else 6 := by
  rw [SA, shift_card m _ (fun B => t ∈ B ∧ (t ≠ 3 → ¬(0 ∈ B ∧ 1 ∈ B ∧ 2 ∈ B)) ∧
    (t ≠ 2 → ¬(0 ∈ B ∧ 1 ∈ B ∧ 3 ∈ B))) fun B => by simp only [mem_shift, mem_shift_zero]]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;> decide

lemma SB_card (m t : ℕ) (ht : t < 4) : (SB m t).card = if t < 2 then 2 else 1 := by
  rw [SB, shift_card m _ (fun B => t ∈ B ∧ ¬(0 ∈ B ∧ 1 ∈ B ∧ 2 ∈ B ∧ 3 ∈ B) ∧
    ¬((t ≠ 3 → ¬(0 ∈ B ∧ 1 ∈ B ∧ 2 ∈ B)) ∧ (t ≠ 2 → ¬(0 ∈ B ∧ 1 ∈ B ∧ 3 ∈ B))))
    fun B => by simp only [mem_shift, mem_shift_zero]]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;> decide

lemma F13_rho (k u : ℕ) (h1 : 4 * k ≤ u) (h2 : u < 4 * k + 4) :
    rho (F13 (4 * k)) u = if u % 4 < 2 then -3 else -1 := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, s < 4 ∧ u = 4 * k + s := ⟨u - 4 * k, by omega, by omega⟩
  rw [show (4 * k + s) % 4 = s by omega, F13,
    shift_rho (4 * k) s _ (fun B => ¬(0 ∈ B ∧ 1 ∈ B ∧ 2 ∈ B) ∧ ¬(0 ∈ B ∧ 1 ∈ B ∧ 3 ∈ B))
    fun B => by simp only [mem_shift, mem_shift_zero]]
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) with rfl | rfl | rfl | rfl <;> decide

lemma SA_rho (k t u : ℕ) (ht : t < 4) (h1 : 4 * k ≤ u) (h2 : u < 4 * k + 4) :
    rho (SA (4 * k) t) u =
      if u % 4 = t then (if t < 2 then 5 else 6)
      else if u % 4 < 2 then (if t < 2 then -3 else -2) else (if t < 2 then -1 else 0) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, s < 4 ∧ u = 4 * k + s := ⟨u - 4 * k, by omega, by omega⟩
  rw [show (4 * k + s) % 4 = s by omega, SA,
    shift_rho (4 * k) s _ (fun B => t ∈ B ∧ (t ≠ 3 → ¬(0 ∈ B ∧ 1 ∈ B ∧ 2 ∈ B)) ∧
      (t ≠ 2 → ¬(0 ∈ B ∧ 1 ∈ B ∧ 3 ∈ B))) fun B => by simp only [mem_shift, mem_shift_zero]]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) with rfl | rfl | rfl | rfl <;> decide

lemma SB_rho (k t u : ℕ) (ht : t < 4) (h1 : 4 * k ≤ u) (h2 : u < 4 * k + 4) :
    rho (SB (4 * k) t) u =
      if u % 4 = t then (if t < 2 then 2 else 1)
      else if u % 4 < 2 then (if t < 2 then 2 else 1) else (if t < 2 then 0 else -1) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, s < 4 ∧ u = 4 * k + s := ⟨u - 4 * k, by omega, by omega⟩
  rw [show (4 * k + s) % 4 = s by omega, SB,
    shift_rho (4 * k) s _ (fun B => t ∈ B ∧ ¬(0 ∈ B ∧ 1 ∈ B ∧ 2 ∈ B ∧ 3 ∈ B) ∧
      ¬((t ≠ 3 → ¬(0 ∈ B ∧ 1 ∈ B ∧ 2 ∈ B)) ∧ (t ≠ 2 → ¬(0 ∈ B ∧ 1 ∈ B ∧ 3 ∈ B))))
    fun B => by simp only [mem_shift, mem_shift_zero]]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) with rfl | rfl | rfl | rfl <;> decide

/-! ## Traces on a block -/

lemma mem_F13_inter (m : ℕ) (A : Finset ℕ) :
    A ∩ Ico m (m + 4) ∈ F13 m ↔
      ¬(m ∈ A ∧ m + 1 ∈ A ∧ m + 2 ∈ A) ∧ ¬(m ∈ A ∧ m + 1 ∈ A ∧ m + 3 ∈ A) := by
  have h0 : m ∈ Ico m (m + 4) := mem_Ico.2 ⟨le_refl _, by omega⟩
  have h1 : m + 1 ∈ Ico m (m + 4) := mem_Ico.2 ⟨by omega, by omega⟩
  have h2 : m + 2 ∈ Ico m (m + 4) := mem_Ico.2 ⟨by omega, by omega⟩
  have h3 : m + 3 ∈ Ico m (m + 4) := mem_Ico.2 ⟨by omega, by omega⟩
  simp only [F13, mem_filter, mem_powerset, inter_subset_right, true_and, mem_inter, h0, h1, h2,
    h3, and_true]

lemma mem_SA_inter (m t : ℕ) (ht : t < 4) (A : Finset ℕ) :
    A ∩ Ico m (m + 4) ∈ SA m t ↔ m + t ∈ A ∧
      (t ≠ 3 → ¬(m ∈ A ∧ m + 1 ∈ A ∧ m + 2 ∈ A)) ∧
      (t ≠ 2 → ¬(m ∈ A ∧ m + 1 ∈ A ∧ m + 3 ∈ A)) := by
  have h0 : m ∈ Ico m (m + 4) := mem_Ico.2 ⟨le_refl _, by omega⟩
  have h1 : m + 1 ∈ Ico m (m + 4) := mem_Ico.2 ⟨by omega, by omega⟩
  have h2 : m + 2 ∈ Ico m (m + 4) := mem_Ico.2 ⟨by omega, by omega⟩
  have h3 : m + 3 ∈ Ico m (m + 4) := mem_Ico.2 ⟨by omega, by omega⟩
  have h4 : m + t ∈ Ico m (m + 4) := mem_Ico.2 ⟨by omega, by omega⟩
  simp only [SA, mem_filter, mem_powerset, inter_subset_right, true_and, mem_inter, h0, h1, h2,
    h3, h4, and_true]

lemma mem_SB_inter (m t : ℕ) (ht : t < 4) (A : Finset ℕ) :
    A ∩ Ico m (m + 4) ∈ SB m t ↔ m + t ∈ A ∧
      ¬(m ∈ A ∧ m + 1 ∈ A ∧ m + 2 ∈ A ∧ m + 3 ∈ A) ∧
      ¬((t ≠ 3 → ¬(m ∈ A ∧ m + 1 ∈ A ∧ m + 2 ∈ A)) ∧
        (t ≠ 2 → ¬(m ∈ A ∧ m + 1 ∈ A ∧ m + 3 ∈ A))) := by
  have h0 : m ∈ Ico m (m + 4) := mem_Ico.2 ⟨le_refl _, by omega⟩
  have h1 : m + 1 ∈ Ico m (m + 4) := mem_Ico.2 ⟨by omega, by omega⟩
  have h2 : m + 2 ∈ Ico m (m + 4) := mem_Ico.2 ⟨by omega, by omega⟩
  have h3 : m + 3 ∈ Ico m (m + 4) := mem_Ico.2 ⟨by omega, by omega⟩
  have h4 : m + t ∈ Ico m (m + 4) := mem_Ico.2 ⟨by omega, by omega⟩
  simp only [SB, mem_filter, mem_powerset, inter_subset_right, true_and, mem_inter, h0, h1, h2,
    h3, h4, and_true]

/-! ## The generators of `M_{r,p}` -/

lemma mem4 {x a b c d : ℕ} : x ∈ ({a, b, c, d} : Finset ℕ) ↔ x = a ∨ x = b ∨ x = c ∨ x = d := by
  simp only [mem_insert, mem_singleton]

lemma sub4 {a b c d : ℕ} {A : Finset ℕ} :
    ({a, b, c, d} : Finset ℕ) ⊆ A ↔ a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ d ∈ A := by
  simp only [insert_subset_iff, singleton_subset_iff]

lemma mem_morrisFam_cases {r p : ℕ} {g : Finset ℕ} (hg : g ∈ morrisFam r p) :
    ∃ i < r, g = {4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3} ∨
      ∃ y, 4 * i + 4 ≤ y ∧ y < 4 * r + p ∧
        (g = {4 * i, 4 * i + 1, 4 * i + 2, y} ∨ g = {4 * i, 4 * i + 1, 4 * i + 3, y}) := by
  simp only [morrisFam, mem_biUnion, mem_range, mem_insert, mem_Ico, mem_singleton] at hg
  obtain ⟨i, hi, h | ⟨y, ⟨hy1, hy2⟩, h⟩⟩ := hg
  · exact ⟨i, hi, Or.inl h⟩
  · exact ⟨i, hi, Or.inr ⟨y, hy1, hy2, h⟩⟩

lemma gen_Q_mem {r p i : ℕ} (hi : i < r) :
    ({4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3} : Finset ℕ) ∈ morrisFam r p :=
  mem_biUnion.2 ⟨i, mem_range.2 hi, mem_insert_self _ _⟩

lemma gen_c_mem {r p i y : ℕ} (hi : i < r) (hy1 : 4 * i + 4 ≤ y) (hy2 : y < 4 * r + p) :
    ({4 * i, 4 * i + 1, 4 * i + 2, y} : Finset ℕ) ∈ morrisFam r p :=
  mem_biUnion.2 ⟨i, mem_range.2 hi,
    mem_insert_of_mem (mem_biUnion.2 ⟨y, mem_Ico.2 ⟨hy1, hy2⟩, mem_insert_self _ _⟩)⟩

lemma gen_d_mem {r p i y : ℕ} (hi : i < r) (hy1 : 4 * i + 4 ≤ y) (hy2 : y < 4 * r + p) :
    ({4 * i, 4 * i + 1, 4 * i + 3, y} : Finset ℕ) ∈ morrisFam r p :=
  mem_biUnion.2 ⟨i, mem_range.2 hi,
    mem_insert_of_mem (mem_biUnion.2 ⟨y, mem_Ico.2 ⟨hy1, hy2⟩,
      mem_insert_of_mem (mem_singleton_self _)⟩)⟩

lemma mem_omitted_morris {r p z : ℕ} (hr : 1 ≤ r) {A : Finset ℕ} :
    A ∈ omitted (morrisFam r p) z ↔
      A ⊆ range (4 * r + p) ∧ z ∈ A ∧ ∀ g ∈ morrisFam r p, z ∈ g → ¬ g ⊆ A := by
  rw [omitted, mem_filter, mem_powerset, morrisFam_supp r p hr]

/-! ## Tail coatoms: `4r ≤ z` -/

lemma noGen_tail {r p z : ℕ} (hz1 : 4 * r ≤ z) (hz2 : z < 4 * r + p) {A : Finset ℕ}
    (hzA : z ∈ A) :
    (∀ g ∈ morrisFam r p, z ∈ g → ¬ g ⊆ A) ↔
      ∀ k < r, ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 2 ∈ A) ∧
        ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 3 ∈ A) := by
  constructor
  · intro h k hk
    exact ⟨fun ⟨h0, h1, h2⟩ => h _ (gen_c_mem hk (by omega) hz2) (mem4.2 (by omega))
        (sub4.2 ⟨h0, h1, h2, hzA⟩),
      fun ⟨h0, h1, h3⟩ => h _ (gen_d_mem hk (by omega) hz2) (mem4.2 (by omega))
        (sub4.2 ⟨h0, h1, h3, hzA⟩)⟩
  · intro h g hg hzg hgA
    obtain ⟨i, hi, rfl | ⟨y, hy1, hy2, rfl | rfl⟩⟩ := mem_morrisFam_cases hg
    · rw [mem4] at hzg
      omega
    · obtain ⟨h0, h1, h2, -⟩ := sub4.1 hgA
      exact (h i hi).1 ⟨h0, h1, h2⟩
    · obtain ⟨h0, h1, h3, -⟩ := sub4.1 hgA
      exact (h i hi).2 ⟨h0, h1, h3⟩

/-- Components for a tail coatom: the blocks, `{z}`, and the rest of the tail. -/
def tailV (r n z k : ℕ) : Finset ℕ :=
  if k < r then Ico (4 * k) (4 * k + 4) else if k = r then {z} else (Ico (4 * r) n).erase z

/-- Trace families for a tail coatom. -/
def tailQ (r n z k : ℕ) : Fam :=
  if k < r then F13 (4 * k) else if k = r then {{z}} else ((Ico (4 * r) n).erase z).powerset

lemma tailV_disj {r n z : ℕ} (hz1 : 4 * r ≤ z) :
    ∀ i ∈ range (r + 2), ∀ j ∈ range (r + 2), i ≠ j →
      Disjoint (tailV r n z i) (tailV r n z j) := by
  intro i hi j hj hij
  rw [mem_range] at hi hj
  rw [disjoint_left]
  intro x hxi hxj
  unfold tailV at hxi hxj
  split_ifs at hxi hxj <;> simp only [mem_Ico, mem_singleton, mem_erase] at hxi hxj <;> omega

lemma tailQ_sub {r n z : ℕ} : ∀ i ∈ range (r + 2), tailQ r n z i ⊆ (tailV r n z i).powerset := by
  intro i _
  unfold tailQ tailV
  split_ifs
  · exact filter_subset _ _
  · exact singleton_subset_iff.2 (mem_powerset.2 (subset_refl _))
  · exact subset_refl _

lemma tail_biUnion {r p z : ℕ} (hz1 : 4 * r ≤ z) (hz2 : z < 4 * r + p) :
    (range (r + 2)).biUnion (tailV r (4 * r + p) z) = range (4 * r + p) := by
  ext x
  simp only [mem_biUnion, mem_range]
  constructor
  · rintro ⟨k, hk, hx⟩
    unfold tailV at hx
    split_ifs at hx <;> simp only [mem_Ico, mem_singleton, mem_erase] at hx <;> omega
  · intro hx
    by_cases h1 : x < 4 * r
    · refine ⟨x / 4, by omega, ?_⟩
      unfold tailV
      rw [if_pos (by omega), mem_Ico]
      omega
    · by_cases h2 : x = z
      · refine ⟨r, by omega, ?_⟩
        unfold tailV
        rw [if_neg (lt_irrefl r), if_pos rfl, mem_singleton]
        exact h2
      · refine ⟨r + 1, by omega, ?_⟩
        unfold tailV
        rw [if_neg (by omega), if_neg (by omega), mem_erase, mem_Ico]
        omega

lemma mem_tailN {r p z : ℕ} (hz1 : 4 * r ≤ z) (hz2 : z < 4 * r + p) {A : Finset ℕ} :
    A ∈ prodFam (range (r + 2)) (tailV r (4 * r + p) z) (tailQ r (4 * r + p) z) ↔
      A ⊆ range (4 * r + p) ∧
      (∀ k < r, ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 2 ∈ A) ∧
        ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 3 ∈ A)) ∧ z ∈ A := by
  rw [mem_prodFam_iff, tail_biUnion hz1 hz2, forall_range_add_two]
  have e1 : ∀ k < r, (A ∩ tailV r (4 * r + p) z k ∈ tailQ r (4 * r + p) z k ↔
      ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 2 ∈ A) ∧
        ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 3 ∈ A)) := by
    intro k hk
    unfold tailV tailQ
    rw [if_pos hk, if_pos hk]
    exact mem_F13_inter (4 * k) A
  have e2 : A ∩ tailV r (4 * r + p) z r ∈ tailQ r (4 * r + p) z r ↔ z ∈ A := by
    unfold tailV tailQ
    rw [if_neg (lt_irrefl r), if_pos rfl, if_neg (lt_irrefl r), if_pos rfl, mem_singleton]
    constructor
    · intro h
      have hz : z ∈ A ∩ {z} := by
        rw [h]
        exact mem_singleton_self z
      exact (mem_inter.1 hz).1
    · intro h
      exact inter_singleton_of_mem h
  have e3 : A ∩ tailV r (4 * r + p) z (r + 1) ∈ tailQ r (4 * r + p) z (r + 1) := by
    unfold tailV tailQ
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact mem_powerset.2 inter_subset_right
  constructor
  · rintro ⟨hA, h1, h2, -⟩
    exact ⟨hA, fun k hk => (e1 k hk).1 (h1 k hk), e2.1 h2⟩
  · rintro ⟨hA, h1, h2⟩
    exact ⟨hA, fun k hk => (e1 k hk).2 (h1 k hk), e2.2 h2, e3⟩

lemma omitted_tail {r p z : ℕ} (hr : 1 ≤ r) (hz1 : 4 * r ≤ z) (hz2 : z < 4 * r + p) :
    omitted (morrisFam r p) z =
      prodFam (range (r + 2)) (tailV r (4 * r + p) z) (tailQ r (4 * r + p) z) := by
  ext A
  rw [mem_omitted_morris hr, mem_tailN hz1 hz2]
  constructor
  · rintro ⟨hA, hzA, h⟩
    exact ⟨hA, (noGen_tail hz1 hz2 hzA).1 h, hzA⟩
  · rintro ⟨hA, h, hzA⟩
    exact ⟨hA, hzA, (noGen_tail hz1 hz2 hzA).2 h⟩

lemma tailQ_card_lt {r n z k : ℕ} (hk : k < r) : (tailQ r n z k).card = 13 := by
  unfold tailQ
  rw [if_pos hk]
  exact F13_card _

lemma tailQ_card_r {r n z : ℕ} : (tailQ r n z r).card = 1 := by
  unfold tailQ
  rw [if_neg (lt_irrefl r), if_pos rfl]
  rfl

lemma tailQ_card_succ {r p z : ℕ} (hz1 : 4 * r ≤ z) (hz2 : z < 4 * r + p) :
    (tailQ r (4 * r + p) z (r + 1)).card = 2 ^ (p - 1) := by
  unfold tailQ
  rw [if_neg (by omega), if_neg (by omega), card_powerset,
    card_erase_of_mem (mem_Ico.2 ⟨hz1, hz2⟩), Nat.card_Ico,
    show 4 * r + p - 4 * r - 1 = p - 1 by omega]

lemma tail_prod {r p z : ℕ} (hz1 : 4 * r ≤ z) (hz2 : z < 4 * r + p) :
    ∏ k ∈ range (r + 2), (tailQ r (4 * r + p) z k).card = 13 ^ r * (1 * 2 ^ (p - 1)) := by
  have h : ∏ k ∈ range r, (tailQ r (4 * r + p) z k).card = 13 ^ r := by
    rw [prod_congr rfl fun k hk => tailQ_card_lt (n := 4 * r + p) (z := z) (mem_range.1 hk),
      prod_const, card_range]
  rw [show r + 2 = r + 1 + 1 from rfl, prod_range_succ, prod_range_succ, h, tailQ_card_r,
    tailQ_card_succ hz1 hz2, mul_assoc]

lemma rho_tail_blk {r p z u : ℕ} (hr : 1 ≤ r) (hz1 : 4 * r ≤ z) (hz2 : z < 4 * r + p)
    (hu : u < 4 * r) :
    rho (omitted (morrisFam r p) z) u =
      (if u % 4 < 2 then -3 else -1) * ((13 ^ (r - 1) * (1 * 2 ^ (p - 1)) : ℕ) : ℤ) := by
  have hk : u / 4 ∈ range (r + 2) := mem_range.2 (by omega)
  have huV : u ∈ tailV r (4 * r + p) z (u / 4) := by
    unfold tailV
    rw [if_pos (by omega), mem_Ico]
    omega
  have hQ : tailQ r (4 * r + p) z (u / 4) = F13 (4 * (u / 4)) := by
    unfold tailQ
    rw [if_pos (by omega)]
  have hP : ∏ i ∈ (range (r + 2)).erase (u / 4), (tailQ r (4 * r + p) z i).card =
      13 ^ (r - 1) * (1 * 2 ^ (p - 1)) := by
    refine prod_erase_eq hk (by norm_num : 0 < 13) (tailQ_card_lt (by omega)) ?_
    rw [tail_prod hz1 hz2]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  rw [omitted_tail hr hz1 hz2, rho_prodFam _ _ (tailV_disj hz1) _ tailQ_sub hk huV, hQ,
    F13_rho (u / 4) u (by omega) (by omega), hP]

lemma rho_tail_z {r p z : ℕ} (hr : 1 ≤ r) (hz1 : 4 * r ≤ z) (hz2 : z < 4 * r + p) :
    rho (omitted (morrisFam r p) z) z = ((13 ^ r * (1 * 2 ^ (p - 1)) : ℕ) : ℤ) := by
  have hk : r ∈ range (r + 2) := mem_range.2 (by omega)
  have hzV : z ∈ tailV r (4 * r + p) z r := by
    unfold tailV
    rw [if_neg (lt_irrefl r), if_pos rfl]
    exact mem_singleton_self z
  have hQ : tailQ r (4 * r + p) z r = {{z}} := by
    unfold tailQ
    rw [if_neg (lt_irrefl r), if_pos rfl]
  have hP : ∏ i ∈ (range (r + 2)).erase r, (tailQ r (4 * r + p) z i).card =
      13 ^ r * (1 * 2 ^ (p - 1)) := by
    refine prod_erase_eq hk (by norm_num : 0 < 1) tailQ_card_r ?_
    rw [tail_prod hz1 hz2]
    ring
  rw [omitted_tail hr hz1 hz2, rho_prodFam _ _ (tailV_disj hz1) _ tailQ_sub hk hzV, hQ,
    rho_singleton_self, hP, one_mul]

lemma rho_tail_D {r p z u : ℕ} (hr : 1 ≤ r) (hz1 : 4 * r ≤ z) (hz2 : z < 4 * r + p)
    (hu1 : 4 * r ≤ u) (hu2 : u < 4 * r + p) (hne : u ≠ z) :
    rho (omitted (morrisFam r p) z) u = 0 := by
  have hk : r + 1 ∈ range (r + 2) := mem_range.2 (by omega)
  have huD : u ∈ (Ico (4 * r) (4 * r + p)).erase z := mem_erase.2 ⟨hne, mem_Ico.2 ⟨hu1, hu2⟩⟩
  have huV : u ∈ tailV r (4 * r + p) z (r + 1) := by
    unfold tailV
    rw [if_neg (by omega), if_neg (by omega)]
    exact huD
  have hQ : tailQ r (4 * r + p) z (r + 1) = ((Ico (4 * r) (4 * r + p)).erase z).powerset := by
    unfold tailQ
    rw [if_neg (by omega), if_neg (by omega)]
  rw [omitted_tail hr hz1 hz2, rho_prodFam _ _ (tailV_disj hz1) _ tailQ_sub hk huV, hQ,
    rho_powerset _ huD, zero_mul]

lemma rho_omitted_tail {r p z u : ℕ} (hr : 1 ≤ r) (hz1 : 4 * r ≤ z) (hz2 : z < 4 * r + p)
    (hu : u < 4 * r + p) :
    rho (omitted (morrisFam r p) z) u = -morrisRow r p z u := by
  unfold morrisRow
  rw [if_pos hz1]
  rcases (by omega : u < 4 * r ∨ u = z ∨ (4 * r ≤ u ∧ u ≠ z)) with h | rfl | ⟨h1, h2⟩
  · rw [rho_tail_blk hr hz1 hz2 h, if_neg (show ¬u = z by omega), if_pos h]
    push_cast
    split_ifs <;> ring
  · rw [rho_tail_z hr hz1 hz2, if_pos rfl]
    push_cast
    ring
  · rw [rho_tail_D hr hz1 hz2 h1 hu h2, if_neg h2, if_neg (show ¬u < 4 * r by omega), neg_zero]


/-! ## Block coatoms: `z = 4 i₀ + t` with `i₀ < r`, `t < 4` -/

lemma pow13_pred {i : ℕ} (hi : 1 ≤ i) : 13 ^ i = 13 * 13 ^ (i - 1) := by
  rw [← pow_succ']
  congr 1
  omega

/-- Components for a block coatom: the blocks `Q_0, …, Q_{i₀}` and the later points `L_{i₀}`. -/
def blkV (i₀ n k : ℕ) : Finset ℕ :=
  if k ≤ i₀ then Ico (4 * k) (4 * k + 4) else Ico (4 * i₀ + 4) n

/-- Trace families of the first part (arbitrary trace on `L_{i₀}`). -/
def Q1 (i₀ t n k : ℕ) : Fam :=
  if k < i₀ then F13 (4 * k) else if k = i₀ then SA (4 * k) t else (Ico (4 * i₀ + 4) n).powerset

/-- Trace families of the second part (empty trace on `L_{i₀}`). -/
def Q2 (i₀ t _n k : ℕ) : Fam :=
  if k < i₀ then F13 (4 * k) else if k = i₀ then SB (4 * k) t else {∅}

lemma blkV_disj {i₀ n : ℕ} :
    ∀ i ∈ range (i₀ + 2), ∀ j ∈ range (i₀ + 2), i ≠ j →
      Disjoint (blkV i₀ n i) (blkV i₀ n j) := by
  intro i hi j hj hij
  rw [mem_range] at hi hj
  rw [disjoint_left]
  intro x hxi hxj
  unfold blkV at hxi hxj
  split_ifs at hxi hxj <;> simp only [mem_Ico] at hxi hxj <;> omega

lemma Q1_sub {i₀ t n : ℕ} : ∀ k ∈ range (i₀ + 2), Q1 i₀ t n k ⊆ (blkV i₀ n k).powerset := by
  intro k hk
  rw [mem_range] at hk
  unfold Q1 blkV
  split_ifs <;> first | exact filter_subset _ _ | exact subset_refl _ | omega

lemma Q2_sub {i₀ t n : ℕ} : ∀ k ∈ range (i₀ + 2), Q2 i₀ t n k ⊆ (blkV i₀ n k).powerset := by
  intro k hk
  rw [mem_range] at hk
  unfold Q2 blkV
  split_ifs <;>
    first | exact filter_subset _ _ | exact singleton_subset_iff.2 (empty_mem_powerset _) | omega

lemma blk_biUnion {r p i₀ : ℕ} (hi₀ : i₀ < r) :
    (range (i₀ + 2)).biUnion (blkV i₀ (4 * r + p)) = range (4 * r + p) := by
  ext x
  simp only [mem_biUnion, mem_range]
  constructor
  · rintro ⟨k, hk, hx⟩
    unfold blkV at hx
    split_ifs at hx <;> simp only [mem_Ico] at hx <;> omega
  · intro hx
    by_cases h1 : x < 4 * i₀ + 4
    · refine ⟨x / 4, by omega, ?_⟩
      unfold blkV
      rw [if_pos (by omega), mem_Ico]
      omega
    · refine ⟨i₀ + 1, by omega, ?_⟩
      unfold blkV
      rw [if_neg (by omega), mem_Ico]
      omega

lemma mem_N1 {r p i₀ t : ℕ} (hi₀ : i₀ < r) (ht : t < 4) {A : Finset ℕ} :
    A ∈ prodFam (range (i₀ + 2)) (blkV i₀ (4 * r + p)) (Q1 i₀ t (4 * r + p)) ↔
      A ⊆ range (4 * r + p) ∧
      (∀ k < i₀, ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 2 ∈ A) ∧
        ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 3 ∈ A)) ∧
      (4 * i₀ + t ∈ A ∧ (t ≠ 3 → ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 2 ∈ A)) ∧
        (t ≠ 2 → ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 3 ∈ A))) := by
  rw [mem_prodFam_iff, blk_biUnion hi₀, forall_range_add_two]
  have e1 : ∀ k < i₀, (A ∩ blkV i₀ (4 * r + p) k ∈ Q1 i₀ t (4 * r + p) k ↔
      ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 2 ∈ A) ∧
        ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 3 ∈ A)) := by
    intro k hk
    unfold blkV Q1
    rw [if_pos hk.le, if_pos hk]
    exact mem_F13_inter (4 * k) A
  have e2 : A ∩ blkV i₀ (4 * r + p) i₀ ∈ Q1 i₀ t (4 * r + p) i₀ ↔
      4 * i₀ + t ∈ A ∧ (t ≠ 3 → ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 2 ∈ A)) ∧
        (t ≠ 2 → ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 3 ∈ A)) := by
    unfold blkV Q1
    rw [if_pos le_rfl, if_neg (lt_irrefl i₀), if_pos rfl]
    exact mem_SA_inter (4 * i₀) t ht A
  have e3 : A ∩ blkV i₀ (4 * r + p) (i₀ + 1) ∈ Q1 i₀ t (4 * r + p) (i₀ + 1) := by
    unfold blkV Q1
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact mem_powerset.2 inter_subset_right
  constructor
  · rintro ⟨hA, h1, h2, -⟩
    exact ⟨hA, fun k hk => (e1 k hk).1 (h1 k hk), e2.1 h2⟩
  · rintro ⟨hA, h1, h2⟩
    exact ⟨hA, fun k hk => (e1 k hk).2 (h1 k hk), e2.2 h2, e3⟩

lemma mem_N2 {r p i₀ t : ℕ} (hi₀ : i₀ < r) (ht : t < 4) {A : Finset ℕ} :
    A ∈ prodFam (range (i₀ + 2)) (blkV i₀ (4 * r + p)) (Q2 i₀ t (4 * r + p)) ↔
      A ⊆ range (4 * r + p) ∧
      (∀ k < i₀, ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 2 ∈ A) ∧
        ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 3 ∈ A)) ∧
      (4 * i₀ + t ∈ A ∧ ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 2 ∈ A ∧ 4 * i₀ + 3 ∈ A) ∧
        ¬((t ≠ 3 → ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 2 ∈ A)) ∧
          (t ≠ 2 → ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 3 ∈ A)))) ∧
      (∀ y ∈ A, ¬(4 * i₀ + 4 ≤ y ∧ y < 4 * r + p)) := by
  rw [mem_prodFam_iff, blk_biUnion hi₀, forall_range_add_two]
  have e1 : ∀ k < i₀, (A ∩ blkV i₀ (4 * r + p) k ∈ Q2 i₀ t (4 * r + p) k ↔
      ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 2 ∈ A) ∧
        ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 3 ∈ A)) := by
    intro k hk
    unfold blkV Q2
    rw [if_pos hk.le, if_pos hk]
    exact mem_F13_inter (4 * k) A
  have e2 : A ∩ blkV i₀ (4 * r + p) i₀ ∈ Q2 i₀ t (4 * r + p) i₀ ↔
      4 * i₀ + t ∈ A ∧ ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 2 ∈ A ∧ 4 * i₀ + 3 ∈ A) ∧
        ¬((t ≠ 3 → ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 2 ∈ A)) ∧
          (t ≠ 2 → ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 3 ∈ A))) := by
    unfold blkV Q2
    rw [if_pos le_rfl, if_neg (lt_irrefl i₀), if_pos rfl]
    exact mem_SB_inter (4 * i₀) t ht A
  have e3 : A ∩ blkV i₀ (4 * r + p) (i₀ + 1) ∈ Q2 i₀ t (4 * r + p) (i₀ + 1) ↔
      ∀ y ∈ A, ¬(4 * i₀ + 4 ≤ y ∧ y < 4 * r + p) := by
    unfold blkV Q2
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), mem_singleton,
      eq_empty_iff_forall_notMem]
    simp only [mem_inter, mem_Ico]
    constructor
    · intro h y hy hy'
      exact h y ⟨hy, hy'⟩
    · rintro h y ⟨hy, hy'⟩
      exact h y hy hy'
  constructor
  · rintro ⟨hA, h1, h2, h3⟩
    exact ⟨hA, fun k hk => (e1 k hk).1 (h1 k hk), e2.1 h2, e3.1 h3⟩
  · rintro ⟨hA, h1, h2, h3⟩
    exact ⟨hA, fun k hk => (e1 k hk).2 (h1 k hk), e2.2 h2, e3.2 h3⟩

lemma noGen_block {r p i₀ t : ℕ} (hi₀ : i₀ < r) (ht : t < 4) {A : Finset ℕ}
    (hzA : 4 * i₀ + t ∈ A) :
    (∀ g ∈ morrisFam r p, 4 * i₀ + t ∈ g → ¬ g ⊆ A) ↔
      (∀ k < i₀, ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 2 ∈ A) ∧
        ¬(4 * k ∈ A ∧ 4 * k + 1 ∈ A ∧ 4 * k + 3 ∈ A)) ∧
      ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 2 ∈ A ∧ 4 * i₀ + 3 ∈ A) ∧
      (t ≠ 3 → (4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 2 ∈ A) →
        ∀ y ∈ A, ¬(4 * i₀ + 4 ≤ y ∧ y < 4 * r + p)) ∧
      (t ≠ 2 → (4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 3 ∈ A) →
        ∀ y ∈ A, ¬(4 * i₀ + 4 ≤ y ∧ y < 4 * r + p)) := by
  constructor
  · intro h
    refine ⟨fun k hk => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rintro ⟨h0, h1, h2⟩
      exact h _ (gen_c_mem (by omega : k < r) (by omega) (by omega)) (mem4.2 (by omega))
        (sub4.2 ⟨h0, h1, h2, hzA⟩)
    · rintro ⟨h0, h1, h3⟩
      exact h _ (gen_d_mem (by omega : k < r) (by omega) (by omega)) (mem4.2 (by omega))
        (sub4.2 ⟨h0, h1, h3, hzA⟩)
    · rintro ⟨h0, h1, h2, h3⟩
      exact h _ (gen_Q_mem hi₀) (mem4.2 (by omega)) (sub4.2 ⟨h0, h1, h2, h3⟩)
    · rintro h3 ⟨h0, h1, h2⟩ y hy ⟨hy1, hy2⟩
      exact h _ (gen_c_mem hi₀ hy1 hy2) (mem4.2 (by omega)) (sub4.2 ⟨h0, h1, h2, hy⟩)
    · rintro h2 ⟨h0, h1, h3⟩ y hy ⟨hy1, hy2⟩
      exact h _ (gen_d_mem hi₀ hy1 hy2) (mem4.2 (by omega)) (sub4.2 ⟨h0, h1, h3, hy⟩)
  · rintro ⟨hF, hQ, hc, hd⟩ g hg hzg hgA
    obtain ⟨i, hi, rfl | ⟨y, hy1, hy2, rfl | rfl⟩⟩ := mem_morrisFam_cases hg
    · rw [mem4] at hzg
      obtain ⟨h0, h1, h2, h3⟩ := sub4.1 hgA
      obtain rfl : i = i₀ := by omega
      exact hQ ⟨h0, h1, h2, h3⟩
    · rw [mem4] at hzg
      obtain ⟨h0, h1, h2, hy⟩ := sub4.1 hgA
      rcases lt_trichotomy i i₀ with hlt | rfl | hgt
      · exact (hF i hlt).1 ⟨h0, h1, h2⟩
      · exact hc (by omega) ⟨h0, h1, h2⟩ y hy ⟨hy1, hy2⟩
      · omega
    · rw [mem4] at hzg
      obtain ⟨h0, h1, h3, hy⟩ := sub4.1 hgA
      rcases lt_trichotomy i i₀ with hlt | rfl | hgt
      · exact (hF i hlt).2 ⟨h0, h1, h3⟩
      · exact hd (by omega) ⟨h0, h1, h3⟩ y hy ⟨hy1, hy2⟩
      · omega

lemma omitted_block {r p i₀ t : ℕ} (hr : 1 ≤ r) (hi₀ : i₀ < r) (ht : t < 4) :
    omitted (morrisFam r p) (4 * i₀ + t) =
      prodFam (range (i₀ + 2)) (blkV i₀ (4 * r + p)) (Q1 i₀ t (4 * r + p)) ∪
        prodFam (range (i₀ + 2)) (blkV i₀ (4 * r + p)) (Q2 i₀ t (4 * r + p)) := by
  ext A
  rw [mem_union, mem_omitted_morris hr, mem_N1 hi₀ ht, mem_N2 hi₀ ht]
  constructor
  · rintro ⟨hA, hzA, h⟩
    obtain ⟨hF, hQ, hc, hd⟩ := (noGen_block hi₀ ht hzA).1 h
    by_cases hX : (t ≠ 3 → ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 2 ∈ A)) ∧
        (t ≠ 2 → ¬(4 * i₀ ∈ A ∧ 4 * i₀ + 1 ∈ A ∧ 4 * i₀ + 3 ∈ A))
    · exact Or.inl ⟨hA, hF, hzA, hX⟩
    · refine Or.inr ⟨hA, hF, ⟨hzA, hQ, hX⟩, ?_⟩
      rcases not_and_or.1 hX with h1 | h1
      · rw [Classical.not_imp, not_not] at h1
        exact hc h1.1 h1.2
      · rw [Classical.not_imp, not_not] at h1
        exact hd h1.1 h1.2
  · rintro (⟨hA, hF, hzA, hX⟩ | ⟨hA, hF, ⟨hzA, hQ, -⟩, hE⟩)
    · refine ⟨hA, hzA, (noGen_block hi₀ ht hzA).2 ⟨hF, ?_, fun h3 hc => absurd hc (hX.1 h3),
        fun h2 hd => absurd hd (hX.2 h2)⟩⟩
      rintro ⟨h0, h1, h2, h3⟩
      by_cases ht3 : t = 3
      · exact hX.2 (by omega) ⟨h0, h1, h3⟩
      · exact hX.1 ht3 ⟨h0, h1, h2⟩
    · exact ⟨hA, hzA, (noGen_block hi₀ ht hzA).2 ⟨hF, hQ, fun _ _ => hE, fun _ _ => hE⟩⟩

lemma N_disj {r p i₀ t : ℕ} (hi₀ : i₀ < r) (ht : t < 4) :
    Disjoint (prodFam (range (i₀ + 2)) (blkV i₀ (4 * r + p)) (Q1 i₀ t (4 * r + p)))
      (prodFam (range (i₀ + 2)) (blkV i₀ (4 * r + p)) (Q2 i₀ t (4 * r + p))) := by
  rw [disjoint_left]
  intro A h1 h2
  rw [mem_N1 hi₀ ht] at h1
  rw [mem_N2 hi₀ ht] at h2
  exact h2.2.2.1.2.2 h1.2.2.2

lemma Q1_card_lt {i₀ t n k : ℕ} (hk : k < i₀) : (Q1 i₀ t n k).card = 13 := by
  unfold Q1
  rw [if_pos hk]
  exact F13_card _

lemma Q2_card_lt {i₀ t n k : ℕ} (hk : k < i₀) : (Q2 i₀ t n k).card = 13 := by
  unfold Q2
  rw [if_pos hk]
  exact F13_card _

lemma Q1_prod {i₀ t n : ℕ} (ht : t < 4) :
    ∏ k ∈ range (i₀ + 2), (Q1 i₀ t n k).card =
      13 ^ i₀ * ((if t < 2 then 5 else 6) * 2 ^ (n - (4 * i₀ + 4))) := by
  have h : ∏ k ∈ range i₀, (Q1 i₀ t n k).card = 13 ^ i₀ := by
    rw [prod_congr rfl fun k hk => Q1_card_lt (t := t) (n := n) (mem_range.1 hk), prod_const,
      card_range]
  have h1 : (Q1 i₀ t n i₀).card = if t < 2 then 5 else 6 := by
    unfold Q1
    rw [if_neg (lt_irrefl i₀), if_pos rfl]
    exact SA_card _ t ht
  have h2 : (Q1 i₀ t n (i₀ + 1)).card = 2 ^ (n - (4 * i₀ + 4)) := by
    unfold Q1
    rw [if_neg (by omega), if_neg (by omega), card_powerset, Nat.card_Ico]
  rw [show i₀ + 2 = i₀ + 1 + 1 from rfl, prod_range_succ, prod_range_succ, h, h1, h2, mul_assoc]

lemma Q2_prod {i₀ t n : ℕ} (ht : t < 4) :
    ∏ k ∈ range (i₀ + 2), (Q2 i₀ t n k).card = 13 ^ i₀ * ((if t < 2 then 2 else 1) * 1) := by
  have h : ∏ k ∈ range i₀, (Q2 i₀ t n k).card = 13 ^ i₀ := by
    rw [prod_congr rfl fun k hk => Q2_card_lt (t := t) (n := n) (mem_range.1 hk), prod_const,
      card_range]
  have h1 : (Q2 i₀ t n i₀).card = if t < 2 then 2 else 1 := by
    unfold Q2
    rw [if_neg (lt_irrefl i₀), if_pos rfl]
    exact SB_card _ t ht
  have h2 : (Q2 i₀ t n (i₀ + 1)).card = 1 := by
    unfold Q2
    rw [if_neg (by omega), if_neg (by omega)]
    rfl
  rw [show i₀ + 2 = i₀ + 1 + 1 from rfl, prod_range_succ, prod_range_succ, h, h1, h2, mul_assoc]

lemma rho_blk_earlier {r p i₀ t u : ℕ} (hr : 1 ≤ r) (hi₀ : i₀ < r) (ht : t < 4)
    (hu : u < 4 * i₀) :
    rho (omitted (morrisFam r p) (4 * i₀ + t)) u =
      (if u % 4 < 2 then -3 else -1) *
        ((13 ^ (i₀ - 1) * ((if t < 2 then 5 else 6) * 2 ^ (4 * r + p - (4 * i₀ + 4))) : ℕ) : ℤ) +
      (if u % 4 < 2 then -3 else -1) *
        ((13 ^ (i₀ - 1) * ((if t < 2 then 2 else 1) * 1) : ℕ) : ℤ) := by
  have hk : u / 4 ∈ range (i₀ + 2) := mem_range.2 (by omega)
  have huV : u ∈ blkV i₀ (4 * r + p) (u / 4) := by
    unfold blkV
    rw [if_pos (by omega), mem_Ico]
    omega
  have h1 : Q1 i₀ t (4 * r + p) (u / 4) = F13 (4 * (u / 4)) := by
    unfold Q1
    rw [if_pos (by omega)]
  have h2 : Q2 i₀ t (4 * r + p) (u / 4) = F13 (4 * (u / 4)) := by
    unfold Q2
    rw [if_pos (by omega)]
  have hP1 : ∏ i ∈ (range (i₀ + 2)).erase (u / 4), (Q1 i₀ t (4 * r + p) i).card =
      13 ^ (i₀ - 1) * ((if t < 2 then 5 else 6) * 2 ^ (4 * r + p - (4 * i₀ + 4))) := by
    refine prod_erase_eq hk (by norm_num : 0 < 13) (Q1_card_lt (by omega)) ?_
    rw [Q1_prod ht, pow13_pred (by omega : 1 ≤ i₀)]
    ring
  have hP2 : ∏ i ∈ (range (i₀ + 2)).erase (u / 4), (Q2 i₀ t (4 * r + p) i).card =
      13 ^ (i₀ - 1) * ((if t < 2 then 2 else 1) * 1) := by
    refine prod_erase_eq hk (by norm_num : 0 < 13) (Q2_card_lt (by omega)) ?_
    rw [Q2_prod ht, pow13_pred (by omega : 1 ≤ i₀)]
    ring
  rw [omitted_block hr hi₀ ht, rho_union (N_disj hi₀ ht),
    rho_prodFam _ _ blkV_disj _ Q1_sub hk huV, rho_prodFam _ _ blkV_disj _ Q2_sub hk huV,
    h1, h2, F13_rho (u / 4) u (by omega) (by omega), hP1, hP2]

lemma rho_blk_same {r p i₀ t u : ℕ} (hr : 1 ≤ r) (hi₀ : i₀ < r) (ht : t < 4)
    (hu1 : 4 * i₀ ≤ u) (hu2 : u < 4 * i₀ + 4) :
    rho (omitted (morrisFam r p) (4 * i₀ + t)) u =
      rho (SA (4 * i₀) t) u * ((13 ^ i₀ * 2 ^ (4 * r + p - (4 * i₀ + 4)) : ℕ) : ℤ) +
      rho (SB (4 * i₀) t) u * ((13 ^ i₀ * 1 : ℕ) : ℤ) := by
  have hk : i₀ ∈ range (i₀ + 2) := mem_range.2 (by omega)
  have huV : u ∈ blkV i₀ (4 * r + p) i₀ := by
    unfold blkV
    rw [if_pos le_rfl, mem_Ico]
    omega
  have h1 : Q1 i₀ t (4 * r + p) i₀ = SA (4 * i₀) t := by
    unfold Q1
    rw [if_neg (lt_irrefl i₀), if_pos rfl]
  have h2 : Q2 i₀ t (4 * r + p) i₀ = SB (4 * i₀) t := by
    unfold Q2
    rw [if_neg (lt_irrefl i₀), if_pos rfl]
  have hP1 : ∏ i ∈ (range (i₀ + 2)).erase i₀, (Q1 i₀ t (4 * r + p) i).card =
      13 ^ i₀ * 2 ^ (4 * r + p - (4 * i₀ + 4)) := by
    refine prod_erase_eq hk (c := if t < 2 then 5 else 6) (by split_ifs <;> norm_num) ?_ ?_
    · show (Q1 i₀ t (4 * r + p) i₀).card = _
      rw [h1, SA_card _ t ht]
    · rw [Q1_prod ht]
      ring
  have hP2 : ∏ i ∈ (range (i₀ + 2)).erase i₀, (Q2 i₀ t (4 * r + p) i).card = 13 ^ i₀ * 1 := by
    refine prod_erase_eq hk (c := if t < 2 then 2 else 1) (by split_ifs <;> norm_num) ?_ ?_
    · show (Q2 i₀ t (4 * r + p) i₀).card = _
      rw [h2, SB_card _ t ht]
    · rw [Q2_prod ht]
      ring
  rw [omitted_block hr hi₀ ht, rho_union (N_disj hi₀ ht),
    rho_prodFam _ _ blkV_disj _ Q1_sub hk huV, rho_prodFam _ _ blkV_disj _ Q2_sub hk huV,
    h1, h2, hP1, hP2]

lemma rho_blk_later {r p i₀ t u : ℕ} (hr : 1 ≤ r) (hi₀ : i₀ < r) (ht : t < 4)
    (hu1 : 4 * i₀ + 4 ≤ u) (hu2 : u < 4 * r + p) :
    rho (omitted (morrisFam r p) (4 * i₀ + t)) u =
      -((13 ^ i₀ * (if t < 2 then 2 else 1) : ℕ) : ℤ) := by
  have hk : i₀ + 1 ∈ range (i₀ + 2) := mem_range.2 (by omega)
  have huL : u ∈ Ico (4 * i₀ + 4) (4 * r + p) := mem_Ico.2 ⟨hu1, hu2⟩
  have huV : u ∈ blkV i₀ (4 * r + p) (i₀ + 1) := by
    unfold blkV
    rw [if_neg (by omega)]
    exact huL
  have h1 : Q1 i₀ t (4 * r + p) (i₀ + 1) = (Ico (4 * i₀ + 4) (4 * r + p)).powerset := by
    unfold Q1
    rw [if_neg (by omega), if_neg (by omega)]
  have h2 : Q2 i₀ t (4 * r + p) (i₀ + 1) = {∅} := by
    unfold Q2
    rw [if_neg (by omega), if_neg (by omega)]
  have hP2 : ∏ i ∈ (range (i₀ + 2)).erase (i₀ + 1), (Q2 i₀ t (4 * r + p) i).card =
      13 ^ i₀ * (if t < 2 then 2 else 1) := by
    refine prod_erase_eq hk (c := 1) (by norm_num) ?_ ?_
    · show (Q2 i₀ t (4 * r + p) (i₀ + 1)).card = 1
      rw [h2]
      rfl
    · rw [Q2_prod ht]
      ring
  rw [omitted_block hr hi₀ ht, rho_union (N_disj hi₀ ht),
    rho_prodFam _ _ blkV_disj _ Q1_sub hk huV, rho_prodFam _ _ blkV_disj _ Q2_sub hk huV,
    h1, h2, rho_powerset _ huL, rho_singleton_empty, hP2]
  ring

lemma rho_omitted_block {r p i₀ t u : ℕ} (hr : 1 ≤ r) (hi₀ : i₀ < r) (ht : t < 4)
    (hu : u < 4 * r + p) :
    rho (omitted (morrisFam r p) (4 * i₀ + t)) u = -morrisRow r p (4 * i₀ + t) u := by
  have hS : (2 : ℤ) ^ (4 * r + p - (4 * i₀ + 4)) = morrisS r p i₀ := by
    unfold morrisS
    rw [show 4 * r + p - (4 * i₀ + 4) = p + 4 * (r - 1 - i₀) by omega]
  have hdiv : (4 * i₀ + t) / 4 = i₀ := by omega
  have hmod : (4 * i₀ + t) % 4 = t := by omega
  unfold morrisRow
  rw [if_neg (show ¬4 * r ≤ 4 * i₀ + t by omega), hdiv, hmod, ← hS]
  rcases (by omega : u < 4 * i₀ ∨ (4 * i₀ ≤ u ∧ u < 4 * i₀ + 4) ∨ 4 * i₀ + 4 ≤ u) with
    h | ⟨h1, h2⟩ | h
  · have hne : ¬u = 4 * i₀ + t := by omega
    have hnb : ¬(u < 4 * r ∧ u / 4 = i₀) := by omega
    rw [rho_blk_earlier hr hi₀ ht h]
    simp only [if_neg hne, if_neg hnb, if_pos h]
    push_cast
    by_cases htc : t < 2 <;> by_cases huc : u % 4 < 2 <;> simp only [htc, huc, ↓reduceIte] <;>
      ring
  · rw [rho_blk_same hr hi₀ ht h1 h2, SA_rho i₀ t u ht h1 h2, SB_rho i₀ t u ht h1 h2]
    push_cast
    by_cases hut : u % 4 = t
    · have hz : u = 4 * i₀ + t := by omega
      simp only [if_pos hut, if_pos hz]
      by_cases htc : t < 2 <;> simp only [htc, ↓reduceIte] <;> ring
    · have hz : ¬u = 4 * i₀ + t := by omega
      have hb : u < 4 * r ∧ u / 4 = i₀ := ⟨by omega, by omega⟩
      simp only [if_neg hut, if_neg hz, if_pos hb]
      by_cases htc : t < 2 <;> by_cases huc : u % 4 < 2 <;> simp only [htc, huc, ↓reduceIte] <;>
        ring
  · have hne : ¬u = 4 * i₀ + t := by omega
    have hnb : ¬(u < 4 * r ∧ u / 4 = i₀) := by omega
    have hnl : ¬u < 4 * i₀ := by omega
    rw [rho_blk_later hr hi₀ ht h hu]
    simp only [if_neg hne, if_neg hnb, if_neg hnl]
    push_cast
    by_cases htc : t < 2 <;> simp only [htc, ↓reduceIte] <;> ring

end MorrisRows

/-- **Row formulas.**  For `z, u ∈ [4r+p]`, the imbalance of the coatom family `E_z` of Morris's
configuration at `u` is given by the closed form `morrisRow r p z u`. -/
theorem rho_coatom_morris (r p : ℕ) (hr : 1 ≤ r) {z u : ℕ} (hz : z < 4 * r + p)
    (hu : u < 4 * r + p) :
    rho (coatom (morrisFam r p) z) u = morrisRow r p z u := by
  have hus : u ∈ supp (morrisFam r p) := by
    rw [morrisFam_supp r p hr]
    exact mem_range.2 hu
  rw [rho_coatom _ _ hus]
  by_cases hzt : 4 * r ≤ z
  · rw [MorrisRows.rho_omitted_tail hr hzt hz hu, neg_neg]
  · obtain ⟨i₀, t, ht, rfl⟩ : ∃ i₀ t, t < 4 ∧ z = 4 * i₀ + t :=
      ⟨z / 4, z % 4, by omega, by omega⟩
    rw [MorrisRows.rho_omitted_block hr (by omega) ht hu, neg_neg]

end Results.FcMorrisV2
