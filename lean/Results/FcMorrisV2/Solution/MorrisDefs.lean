import Results.FcMorrisV2.Solution.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Solution/MorrisDefs: Morris's ordered four-block construction and its basic properties

Points: block `Q_i = {a_i, b_i, c_i, d_i} = {4i, 4i+1, 4i+2, 4i+3}` for `i < r`, tail
`D = [4r, 4r+p)`; `n = 4r + p`; `L_i = [4i+4, n)` are the points after `Q_i`.
-/

namespace Results.FcMorrisV2

open Finset

/-- Morris's configuration `M_{r,p}`: for each `i < r`, the block `Q_i` and the sets
`{a_i,b_i,c_i,y}`, `{a_i,b_i,d_i,y}` for `y ∈ L_i`. -/
def morrisFam (r p : ℕ) : Fam :=
  (range r).biUnion fun i =>
    insert ({4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3} : Finset ℕ)
      ((Ico (4 * i + 4) (4 * r + p)).biUnion fun y =>
        ({{4 * i, 4 * i + 1, 4 * i + 2, y}, {4 * i, 4 * i + 1, 4 * i + 3, y}} : Fam))

/-- Higher-uniformity inheritance: `T ∪ S` with `T ∈ {a_i b_i c_i, a_i b_i d_i}` and `S` a
`(k-3)`-subset of the tail. -/
def morrisHigh (r p k : ℕ) : Fam :=
  (range r).biUnion fun i =>
    ((Ico (4 * r) (4 * r + p)).powersetCard (k - 3)).biUnion fun S =>
      ({({4 * i, 4 * i + 1, 4 * i + 2} : Finset ℕ) ∪ S,
        ({4 * i, 4 * i + 1, 4 * i + 3} : Finset ℕ) ∪ S} : Fam)

/-- `s_i = 2^{|L_i|}` with `|L_i| = p + 4 (r - 1 - i)`, as an integer. -/
def morrisS (r p i : ℕ) : ℤ := 2 ^ (p + 4 * (r - 1 - i))

/-- Closed-form imbalance row `ρ_u(E_z)` of the coatom family of `M_{r,p}` (paper (B.2)-(B.4)):
`z` is a central point of block `i = z/4` iff `z % 4 < 2`; `u` is central iff `u % 4 < 2`;
tail coatoms (`4r ≤ z`) have row `K = 2^{p-1} 13^r`-scaled as in the paper. -/
def morrisRow (r p z u : ℕ) : ℤ :=
  if 4 * r ≤ z then
    (if u = z then -(2 ^ (p - 1) * 13 ^ r)
     else if u < 4 * r then (if u % 4 < 2 then 3 else 1) * (2 ^ (p - 1) * 13 ^ (r - 1))
     else 0)
  else
    (if z % 4 < 2 then
      (if u = z then -(13 ^ (z / 4) * (5 * morrisS r p (z / 4) + 2))
       else if u < 4 * r ∧ u / 4 = z / 4 then
         (if u % 4 < 2 then 13 ^ (z / 4) * (3 * morrisS r p (z / 4) - 2)
          else 13 ^ (z / 4) * morrisS r p (z / 4))
       else if u < 4 * (z / 4) then
         (if u % 4 < 2 then 3 else 1) * (13 ^ (z / 4 - 1) * (5 * morrisS r p (z / 4) + 2))
       else 2 * 13 ^ (z / 4))
     else
      (if u = z then -(13 ^ (z / 4) * (6 * morrisS r p (z / 4) + 1))
       else if u < 4 * r ∧ u / 4 = z / 4 then
         (if u % 4 < 2 then 13 ^ (z / 4) * (2 * morrisS r p (z / 4) - 1) else 13 ^ (z / 4))
       else if u < 4 * (z / 4) then
         (if u % 4 < 2 then 3 else 1) * (13 ^ (z / 4 - 1) * (6 * morrisS r p (z / 4) + 1))
       else 13 ^ (z / 4)))

/-- Integer row multipliers of the negative certificate (paper (B.5) scaled by `4 · 2^{r-1}`). -/
def morrisLam (r p z : ℕ) : ℕ :=
  if 4 * r ≤ z then 4 * 2 ^ (r - 1)
  else if z % 4 < 2 then 11 * (p + 13) * 2 ^ (z / 4) * 13 ^ (r - 1 - z / 4)
  else 4 * (p + 13) * 2 ^ (z / 4) * 13 ^ (r - 1 - z / 4)

namespace MorrisDefs

/-! ### Helper lemmas (module-private namespace `Results.FcMorrisV2.MorrisDefs`) -/

/-- An explicit four-element set of strictly increasing naturals has four elements. -/
theorem card_four {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ({a, b, c, d} : Finset ℕ).card = 4 := by
  have h1 : a ∉ ({b, c, d} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton]; omega
  have h2 : b ∉ ({c, d} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton]; omega
  rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_pair (by omega)]

/-- An explicit three-element set of strictly increasing naturals has three elements. -/
theorem card_three {a b c : ℕ} (hab : a < b) (hbc : b < c) :
    ({a, b, c} : Finset ℕ).card = 3 := by
  have h1 : a ∉ ({b, c} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton]; omega
  rw [card_insert_of_notMem h1, card_pair (by omega)]

/-- Membership in `morrisFam`, unfolded. -/
theorem mem_morrisFam {r p : ℕ} {A : Finset ℕ} :
    A ∈ morrisFam r p ↔ ∃ i < r,
      A = {4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3} ∨
      ∃ y, 4 * i + 4 ≤ y ∧ y < 4 * r + p ∧
        (A = {4 * i, 4 * i + 1, 4 * i + 2, y} ∨ A = {4 * i, 4 * i + 1, 4 * i + 3, y}) := by
  simp only [morrisFam, mem_biUnion, mem_range, mem_insert, mem_Ico, mem_singleton]
  constructor
  · rintro ⟨i, hi, h | ⟨y, ⟨hy1, hy2⟩, h⟩⟩
    · exact ⟨i, hi, Or.inl h⟩
    · exact ⟨i, hi, Or.inr ⟨y, hy1, hy2, h⟩⟩
  · rintro ⟨i, hi, h | ⟨y, hy1, hy2, h⟩⟩
    · exact ⟨i, hi, Or.inl h⟩
    · exact ⟨i, hi, Or.inr ⟨y, ⟨hy1, hy2⟩, h⟩⟩

/-- Every member of `morrisFam r p` is a four-subset of `[4r + p]`. -/
theorem mem_blocks_of_mem_morrisFam {r p : ℕ} {A : Finset ℕ} (hA : A ∈ morrisFam r p) :
    A ⊆ range (4 * r + p) ∧ A.card = 4 := by
  obtain ⟨i, hi, h | ⟨y, hy1, hy2, h | h⟩⟩ := mem_morrisFam.1 hA
  · subst h
    refine ⟨?_, card_four (by omega) (by omega) (by omega)⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_range]; omega
  · subst h
    refine ⟨?_, card_four (by omega) (by omega) (by omega)⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_range]; omega
  · subst h
    refine ⟨?_, card_four (by omega) (by omega) (by omega)⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_range]; omega

/-- Every member of block `i` of `morrisFam` has minimum `4i`. -/
theorem block_min {r p i : ℕ} {A : Finset ℕ}
    (hA : A ∈ insert ({4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3} : Finset ℕ)
      ((Ico (4 * i + 4) (4 * r + p)).biUnion fun y =>
        ({{4 * i, 4 * i + 1, 4 * i + 2, y}, {4 * i, 4 * i + 1, 4 * i + 3, y}} : Fam))) :
    4 * i ∈ A ∧ ∀ x ∈ A, 4 * i ≤ x := by
  simp only [mem_insert, mem_biUnion, mem_Ico, mem_singleton] at hA
  rcases hA with rfl | ⟨y, ⟨hy1, _⟩, rfl | rfl⟩
  all_goals
    refine ⟨by simp, ?_⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    omega

/-- Every member of the `y`-pair of block `i` has maximum `y`. -/
theorem pair_max {i y : ℕ} (hy : 4 * i + 4 ≤ y) {A : Finset ℕ}
    (hA : A ∈ ({{4 * i, 4 * i + 1, 4 * i + 2, y}, {4 * i, 4 * i + 1, 4 * i + 3, y}} : Fam)) :
    y ∈ A ∧ ∀ x ∈ A, x ≤ y := by
  simp only [mem_insert, mem_singleton] at hA
  rcases hA with rfl | rfl
  all_goals
    refine ⟨by simp, ?_⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    omega

/-- The two sets of a `y`-pair are distinct. -/
theorem pair_card {i y : ℕ} (hy : 4 * i + 4 ≤ y) :
    ({{4 * i, 4 * i + 1, 4 * i + 2, y}, {4 * i, 4 * i + 1, 4 * i + 3, y}} : Fam).card = 2 := by
  apply card_pair
  intro h
  have h2 : 4 * i + 2 ∈ ({4 * i, 4 * i + 1, 4 * i + 2, y} : Finset ℕ) := by simp
  rw [h] at h2
  simp only [mem_insert, mem_singleton] at h2
  omega

/-- Cardinality of block `i` of `morrisFam`. -/
theorem block_card (r p i : ℕ) :
    (insert ({4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3} : Finset ℕ)
      ((Ico (4 * i + 4) (4 * r + p)).biUnion fun y =>
        ({{4 * i, 4 * i + 1, 4 * i + 2, y}, {4 * i, 4 * i + 1, 4 * i + 3, y}} : Fam))).card =
      2 * (4 * r + p - (4 * i + 4)) + 1 := by
  have hnot : ({4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3} : Finset ℕ) ∉
      ((Ico (4 * i + 4) (4 * r + p)).biUnion fun y =>
        ({{4 * i, 4 * i + 1, 4 * i + 2, y}, {4 * i, 4 * i + 1, 4 * i + 3, y}} : Fam)) := by
    intro h
    obtain ⟨y, hy, hA⟩ := mem_biUnion.1 h
    rw [mem_Ico] at hy
    have := (pair_max hy.1 hA).1
    simp only [mem_insert, mem_singleton] at this
    omega
  rw [card_insert_of_notMem hnot, card_biUnion]
  · rw [sum_const_nat (fun y hy => pair_card (mem_Ico.1 hy).1), Nat.card_Ico, mul_comm]
  · intro y hy y' hy' hyy'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro A hA hA'
    have h1 := pair_max (mem_Ico.1 (mem_coe.1 hy)).1 hA
    have h2 := pair_max (mem_Ico.1 (mem_coe.1 hy')).1 hA'
    have := h1.2 y' h2.1
    have := h2.2 y h1.1
    omega

/-- The closed-form sum of the block sizes. -/
theorem sum_block_card (r p : ℕ) :
    ∑ i ∈ range r, (2 * (4 * r + p - (4 * i + 4)) + 1) = r * (4 * r + 2 * p - 3) := by
  have aux : ∀ n, ∑ i ∈ range n, (2 * (4 * n + p - (4 * i + 4)) + 1) + 3 * n =
      n * (4 * n + 2 * p) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ']
      have h1 : ∀ i ∈ range n, 2 * (4 * (n + 1) + p - (4 * (i + 1) + 4)) + 1 =
          2 * (4 * n + p - (4 * i + 4)) + 1 := by
        intro i hi
        rw [mem_range] at hi
        omega
      have h2 : 2 * (4 * (n + 1) + p - (4 * 0 + 4)) + 1 = 8 * n + 2 * p + 1 := by omega
      rw [sum_congr rfl h1, h2]
      linarith
  rcases r with _ | s
  · simp
  · have h2 : 4 * (s + 1) + 2 * p - 3 = 4 * s + 2 * p + 1 := by omega
    rw [h2]
    have := aux (s + 1)
    linarith

/-- Members of block `i` of `morrisHigh` have minimum `4i` (for `i < r`). -/
theorem high_block_min {r p k i : ℕ} (hi : i < r) {A : Finset ℕ}
    (hA : A ∈ ((Ico (4 * r) (4 * r + p)).powersetCard (k - 3)).biUnion fun S =>
      ({({4 * i, 4 * i + 1, 4 * i + 2} : Finset ℕ) ∪ S,
        ({4 * i, 4 * i + 1, 4 * i + 3} : Finset ℕ) ∪ S} : Fam)) :
    4 * i ∈ A ∧ ∀ x ∈ A, 4 * i ≤ x := by
  obtain ⟨S, hS, hA⟩ := mem_biUnion.1 hA
  have hS' := (mem_powersetCard.1 hS).1
  simp only [mem_insert, mem_singleton] at hA
  rcases hA with rfl | rfl
  all_goals
    refine ⟨by simp, ?_⟩
    intro x hx
    rw [mem_union] at hx
    rcases hx with hx | hx
    · simp only [mem_insert, mem_singleton] at hx
      omega
    · have := mem_Ico.1 (hS' hx)
      omega

/-- The trace of a `morrisHigh` generator on the tail recovers `S`. -/
theorem tail_trace {r : ℕ} {T S : Finset ℕ} (hT : ∀ x ∈ T, x < 4 * r)
    (hS : ∀ x ∈ S, 4 * r ≤ x) : (T ∪ S).filter (fun x => 4 * r ≤ x) = S := by
  ext x
  simp only [mem_filter, mem_union]
  constructor
  · rintro ⟨hx | hx, hx'⟩
    · exact absurd (hT x hx) (by omega)
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, hS x hx⟩

/-- Cardinality of block `i` of `morrisHigh`. -/
theorem high_block_card {r p k i : ℕ} (hi : i < r) :
    (((Ico (4 * r) (4 * r + p)).powersetCard (k - 3)).biUnion fun S =>
      ({({4 * i, 4 * i + 1, 4 * i + 2} : Finset ℕ) ∪ S,
        ({4 * i, 4 * i + 1, 4 * i + 3} : Finset ℕ) ∪ S} : Fam)).card = 2 * p.choose (k - 3) := by
  rw [card_biUnion]
  · have hpair : ∀ S ∈ (Ico (4 * r) (4 * r + p)).powersetCard (k - 3),
        ({({4 * i, 4 * i + 1, 4 * i + 2} : Finset ℕ) ∪ S,
          ({4 * i, 4 * i + 1, 4 * i + 3} : Finset ℕ) ∪ S} : Fam).card = 2 := by
      intro S hS
      have hS' := (mem_powersetCard.1 hS).1
      apply card_pair
      intro h
      have h2 : 4 * i + 2 ∈ ({4 * i, 4 * i + 1, 4 * i + 2} : Finset ℕ) ∪ S := by simp
      rw [h, mem_union] at h2
      rcases h2 with h2 | h2
      · simp only [mem_insert, mem_singleton] at h2
        omega
      · have := mem_Ico.1 (hS' h2)
        omega
    rw [sum_const_nat hpair, card_powersetCard, Nat.card_Ico, Nat.add_sub_cancel_left, mul_comm]
  · intro S hS S' hS' hSS'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro A hA hA'
    apply hSS'
    have hS1 := (mem_powersetCard.1 (mem_coe.1 hS)).1
    have hS2 := (mem_powersetCard.1 (mem_coe.1 hS')).1
    have key : ∀ S₀ : Finset ℕ, S₀ ⊆ Ico (4 * r) (4 * r + p) →
        A ∈ ({({4 * i, 4 * i + 1, 4 * i + 2} : Finset ℕ) ∪ S₀,
          ({4 * i, 4 * i + 1, 4 * i + 3} : Finset ℕ) ∪ S₀} : Fam) →
        A.filter (fun x => 4 * r ≤ x) = S₀ := by
      intro S₀ hS₀ hA₀
      have hS₀' : ∀ x ∈ S₀, 4 * r ≤ x := fun x hx => (mem_Ico.1 (hS₀ hx)).1
      simp only [mem_insert, mem_singleton] at hA₀
      rcases hA₀ with rfl | rfl
      · apply tail_trace _ hS₀'
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        omega
      · apply tail_trace _ hS₀'
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        omega
    rw [← key S hS1 hA, ← key S' hS2 hA']

end MorrisDefs

open MorrisDefs

/-- Number of generators: `r (2n - 4r - 3)` with `n = 4r + p`. -/
theorem morrisFam_card (r p : ℕ) : (morrisFam r p).card = r * (4 * r + 2 * p - 3) := by
  unfold morrisFam
  rw [card_biUnion]
  · rw [sum_congr rfl (fun i _ => block_card r p i)]
    exact sum_block_card r p
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [disjoint_left]
    intro A hAi hAj
    have h1 := block_min hAi
    have h2 := block_min hAj
    have := h1.2 _ h2.1
    have := h2.2 _ h1.1
    omega

/-- The support of `M_{r,p}` is all of `[4r + p]` (for `r ≥ 1`). -/
theorem morrisFam_supp (r p : ℕ) (hr : 1 ≤ r) : supp (morrisFam r p) = range (4 * r + p) := by
  apply Subset.antisymm
  · intro u hu
    obtain ⟨A, hA, huA⟩ := mem_biUnion.1 hu
    exact (mem_blocks_of_mem_morrisFam hA).1 huA
  · intro u hu
    rw [mem_range] at hu
    apply mem_biUnion.2
    by_cases h : u < 4 * r
    · refine ⟨{4 * (u / 4), 4 * (u / 4) + 1, 4 * (u / 4) + 2, 4 * (u / 4) + 3}, ?_, ?_⟩
      · exact mem_morrisFam.2 ⟨u / 4, by omega, Or.inl rfl⟩
      · simp only [id, mem_insert, mem_singleton]
        omega
    · refine ⟨{4 * 0, 4 * 0 + 1, 4 * 0 + 2, u}, ?_, ?_⟩
      · exact mem_morrisFam.2 ⟨0, by omega, Or.inr ⟨u, by omega, hu, Or.inl rfl⟩⟩
      · simp

theorem morrisFam_subset_blocks (r p : ℕ) : morrisFam r p ⊆ blocks 4 (4 * r + p) := by
  intro A hA
  rw [blocks, mem_powersetCard]
  exact mem_blocks_of_mem_morrisFam hA

theorem morrisHigh_card (r p k : ℕ) (hk : 3 ≤ k) :
    (morrisHigh r p k).card = 2 * r * p.choose (k - 3) := by
  unfold morrisHigh
  rw [card_biUnion]
  · rw [sum_const_nat (fun i hi => high_block_card (mem_range.1 hi)), card_range]
    ring
  · intro i hi j hj hij
    simp only [Function.onFun]
    rw [disjoint_left]
    intro A hAi hAj
    have h1 := high_block_min (mem_range.1 (mem_coe.1 hi)) hAi
    have h2 := high_block_min (mem_range.1 (mem_coe.1 hj)) hAj
    have := h1.2 _ h2.1
    have := h2.2 _ h1.1
    omega

theorem morrisHigh_subset_blocks (r p k : ℕ) (hk : 3 ≤ k) :
    morrisHigh r p k ⊆ blocks k (4 * r + p) := by
  intro A hA
  rw [blocks, mem_powersetCard]
  simp only [morrisHigh, mem_biUnion, mem_range, mem_insert, mem_singleton] at hA
  obtain ⟨i, hi, S, hS, hA⟩ := hA
  obtain ⟨hS1, hS2⟩ := mem_powersetCard.1 hS
  have hSt : ∀ x ∈ S, 4 * r ≤ x ∧ x < 4 * r + p := fun x hx => mem_Ico.1 (hS1 hx)
  rcases hA with rfl | rfl
  · refine ⟨?_, ?_⟩
    · intro x hx
      rw [mem_union] at hx
      rw [mem_range]
      rcases hx with hx | hx
      · simp only [mem_insert, mem_singleton] at hx
        omega
      · have := hSt x hx
        omega
    · rw [card_union_of_disjoint, card_three (by omega) (by omega), hS2]
      · omega
      · rw [disjoint_left]
        intro x hx hxS
        simp only [mem_insert, mem_singleton] at hx
        have := hSt x hxS
        omega
  · refine ⟨?_, ?_⟩
    · intro x hx
      rw [mem_union] at hx
      rw [mem_range]
      rcases hx with hx | hx
      · simp only [mem_insert, mem_singleton] at hx
        omega
      · have := hSt x hx
        omega
    · rw [card_union_of_disjoint, card_three (by omega) (by omega), hS2]
      · omega
      · rw [disjoint_left]
        intro x hx hxS
        simp only [mem_insert, mem_singleton] at hx
        have := hSt x hxS
        omega

theorem morrisHigh_subset_ucl (r p k : ℕ) (hk : 4 ≤ k) :
    morrisHigh r p k ⊆ ucl (morrisFam r p) := by
  intro A hA
  simp only [morrisHigh, mem_biUnion, mem_range, mem_insert, mem_singleton] at hA
  obtain ⟨i, hi, S, hS, hA⟩ := hA
  obtain ⟨hS1, hS2⟩ := mem_powersetCard.1 hS
  have hSt : ∀ x ∈ S, 4 * r ≤ x ∧ x < 4 * r + p := fun x hx => mem_Ico.1 (hS1 hx)
  have hne : S.Nonempty := by
    rw [← card_pos, hS2]
    omega
  obtain ⟨y₀, hy₀⟩ := hne
  rw [ucl, mem_image]
  rcases hA with rfl | rfl
  · refine ⟨S.image fun y => ({4 * i, 4 * i + 1, 4 * i + 2, y} : Finset ℕ), ?_, ?_⟩
    · rw [mem_powerset]
      intro B hB
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hB
      have := hSt y hy
      exact mem_morrisFam.2 ⟨i, hi, Or.inr ⟨y, by omega, this.2, Or.inl rfl⟩⟩
    · rw [sup_image]
      ext x
      simp only [mem_sup, Function.comp, id, mem_insert, mem_singleton, mem_union]
      constructor
      · rintro ⟨y, hy, hx⟩
        rcases hx with hx | hx | hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inl (Or.inr (Or.inl hx))
        · exact Or.inl (Or.inr (Or.inr hx))
        · exact Or.inr (hx ▸ hy)
      · rintro (hx | hx)
        · exact ⟨y₀, hy₀, by tauto⟩
        · exact ⟨x, hx, by tauto⟩
  · refine ⟨S.image fun y => ({4 * i, 4 * i + 1, 4 * i + 3, y} : Finset ℕ), ?_, ?_⟩
    · rw [mem_powerset]
      intro B hB
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hB
      have := hSt y hy
      exact mem_morrisFam.2 ⟨i, hi, Or.inr ⟨y, by omega, this.2, Or.inr rfl⟩⟩
    · rw [sup_image]
      ext x
      simp only [mem_sup, Function.comp, id, mem_insert, mem_singleton, mem_union]
      constructor
      · rintro ⟨y, hy, hx⟩
        rcases hx with hx | hx | hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inl (Or.inr (Or.inl hx))
        · exact Or.inl (Or.inr (Or.inr hx))
        · exact Or.inr (hx ▸ hy)
      · rintro (hx | hx)
        · exact ⟨y₀, hy₀, by tauto⟩
        · exact ⟨x, hx, by tauto⟩

end Results.FcMorrisV2
