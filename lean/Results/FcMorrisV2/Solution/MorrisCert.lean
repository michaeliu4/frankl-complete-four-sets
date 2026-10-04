import Results.FcMorrisV2.Solution.MorrisDefs

/-!
# Solution/MorrisCert: the negative certificate of Morris's configuration is strictly negative
(paper Proposition B.3, multipliers (B.5), totals (B.6)): pure arithmetic on `morrisRow`.

## Proof outline

Write `g z = morrisLam r p z * morrisRow r p z u`.  The sum over `z < 4r + p` splits into the
blocks `z = 4j + c` (`j < r`, `c < 4`) and the tail `z = 4r + t` (`t < p`).  Writing `γ = 3`
for a central point `u` (`u % 4 < 2`) and `γ = 1` for an outer point, the block sums are:

* block `j` before the block of `u` (`4j + 4 ≤ u`): `52 (p+13) 13^(r-1) 2^j`;
* the block `i` of `u = 4i + d`, `r = i + 1 + m`:
  `-(p+13) 2^i 13^(i+m) (6 s_i + 52)` if `d < 2`, `-(p+13) 2^i 13^(i+m) 2 s_i` otherwise,
  where `s_i = 2^(p+4m)`;
* block `j = i + 1 + k` after it (`r = j + 1 + l`):
  `γ (p+13) 2^j 13^(i+k+l) (158 s_j + 52)` with `s_j = 2^(p+4l)`; these are bounded by a
  telescoping sum (paper: `79/13 + 2/s_j < 7` and `7 Σ_{j>i} v_j = v_i - v_{r-1}`), giving
  `≤ γ (p+13) 13^(i+m) 2^(p+r) (2^(3m) - 1)`;
* the tail: `γ p 2^(p+r) 13^(r-1)` for `u < 4r`, and `-2^(p+r) 13^r` for a tail point `u`.

The totals are then at most `13^(r-1) (-39·2^(p+r) - 52(p+13))` (central `u`),
`13^r (4(p+13)(2^i - 1) - 2^(p+r))` (outer `u`) and `13^r (4(p+13)(2^r - 1) - 2^(p+r))`
(tail `u`), all negative because `4(p+13) ≤ 2^p` for `p ≥ 7`.  These closed forms were checked
by exact integer arithmetic for `r ≤ 7`, `7 ≤ p ≤ 21` before formalisation.
-/

namespace Results.FcMorrisV2

open Finset

namespace MorrisCert

/-! ### Splitting the sum into blocks of four and the tail -/

theorem sum_range_four_mul (f : ℕ → ℤ) (r : ℕ) :
    ∑ z ∈ range (4 * r), f z = ∑ j ∈ range r, ∑ c ∈ range 4, f (4 * j + c) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 4 * (r + 1) = 4 * r + 4 by ring, sum_range_add, ih,
      sum_range_succ (fun j => ∑ c ∈ range 4, f (4 * j + c)) r]

theorem sum_split (f : ℕ → ℤ) (r p : ℕ) :
    ∑ z ∈ range (4 * r + p), f z
      = ∑ j ∈ range r, ∑ c ∈ range 4, f (4 * j + c) + ∑ t ∈ range p, f (4 * r + t) := by
  rw [sum_range_add, sum_range_four_mul]

theorem geom_two (n : ℕ) : ∑ j ∈ range n, (2 : ℤ) ^ j = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

theorem sum_le_telescope (f a : ℕ → ℤ) (m : ℕ) (h : ∀ k < m, f k ≤ a k - a (k + 1)) :
    ∑ k ∈ range m, f k ≤ a 0 - a m := by
  rw [← sum_range_sub']
  exact sum_le_sum fun k hk => h k (mem_range.1 hk)

/-! ### Evaluating the multipliers and the rows -/

variable {r p : ℕ}

theorem lam_block {j c a : ℕ} (hr : r = j + 1 + a) (hc : c < 4) :
    (morrisLam r p (4 * j + c) : ℤ)
      = (if c < 2 then 11 else 4) * ((p : ℤ) + 13) * 2 ^ j * 13 ^ a := by
  have h1 : ¬ (4 * r ≤ 4 * j + c) := by omega
  have h2 : (4 * j + c) / 4 = j := by omega
  have h3 : (4 * j + c) % 4 = c := by omega
  have h4 : r - 1 - j = a := by omega
  unfold morrisLam
  rw [if_neg h1, h2, h3, h4]
  split_ifs <;> push_cast <;> ring

theorem lam_tail {z : ℕ} (hz : 4 * r ≤ z) : (morrisLam r p z : ℤ) = 4 * 2 ^ (r - 1) := by
  unfold morrisLam
  rw [if_pos hz]
  push_cast
  ring

/-- Row entry of a block coatom at a point after its block. -/
theorem row_after {j c u : ℕ} (hj : j < r) (hc : c < 4) (hu : 4 * j + 4 ≤ u) :
    morrisRow r p (4 * j + c) u = if c < 2 then 2 * 13 ^ j else 13 ^ j := by
  have h1 : ¬ (4 * r ≤ 4 * j + c) := by omega
  have h2 : (4 * j + c) / 4 = j := by omega
  have h3 : (4 * j + c) % 4 = c := by omega
  have h4 : u ≠ 4 * j + c := by omega
  have h5 : ¬ (u < 4 * r ∧ u / 4 = j) := by omega
  have h6 : ¬ (u < 4 * j) := by omega
  unfold morrisRow
  rw [if_neg h1, h2, h3]
  simp only [if_neg h4, if_neg h5, if_neg h6]

/-- Row entry of a block coatom at a point of an earlier block. -/
theorem row_before {j c i d : ℕ} (hj : j < r) (hc : c < 4) (hd : d < 4) (hij : i < j) :
    morrisRow r p (4 * j + c) (4 * i + d)
      = (if d < 2 then 3 else 1) *
          (13 ^ (j - 1) * (if c < 2 then 5 * morrisS r p j + 2 else 6 * morrisS r p j + 1)) := by
  have h1 : ¬ (4 * r ≤ 4 * j + c) := by omega
  have h2 : (4 * j + c) / 4 = j := by omega
  have h3 : (4 * j + c) % 4 = c := by omega
  have h4 : 4 * i + d ≠ 4 * j + c := by omega
  have h5 : ¬ (4 * i + d < 4 * r ∧ (4 * i + d) / 4 = j) := by omega
  have h6 : 4 * i + d < 4 * j := by omega
  have h7 : (4 * i + d) % 4 = d := by omega
  unfold morrisRow
  rw [if_neg h1, h2, h3, h7]
  simp only [if_neg h4, if_neg h5, if_pos h6]
  split_ifs <;> rfl

/-- Diagonal row entry of a block coatom. -/
theorem row_self {j c : ℕ} (hj : j < r) (hc : c < 4) :
    morrisRow r p (4 * j + c) (4 * j + c)
      = -(13 ^ j * (if c < 2 then 5 * morrisS r p j + 2 else 6 * morrisS r p j + 1)) := by
  have h1 : ¬ (4 * r ≤ 4 * j + c) := by omega
  have h2 : (4 * j + c) / 4 = j := by omega
  have h3 : (4 * j + c) % 4 = c := by omega
  unfold morrisRow
  rw [if_neg h1, h2, h3]
  split_ifs <;> first | rfl | omega

/-- Row entry of a block coatom at another point of its own block. -/
theorem row_same {j c d : ℕ} (hj : j < r) (hc : c < 4) (hd : d < 4) (hcd : d ≠ c) :
    morrisRow r p (4 * j + c) (4 * j + d)
      = if c < 2 then (if d < 2 then 13 ^ j * (3 * morrisS r p j - 2) else 13 ^ j * morrisS r p j)
        else (if d < 2 then 13 ^ j * (2 * morrisS r p j - 1) else 13 ^ j) := by
  have h1 : ¬ (4 * r ≤ 4 * j + c) := by omega
  have h2 : (4 * j + c) / 4 = j := by omega
  have h3 : (4 * j + c) % 4 = c := by omega
  have h4 : 4 * j + d ≠ 4 * j + c := by omega
  have h5 : 4 * j + d < 4 * r ∧ (4 * j + d) / 4 = j := by omega
  have h7 : (4 * j + d) % 4 = d := by omega
  unfold morrisRow
  rw [if_neg h1, h2, h3, h7]
  simp only [if_neg h4, if_pos h5]

theorem row_tail_self {z : ℕ} (hz : 4 * r ≤ z) :
    morrisRow r p z z = -(2 ^ (p - 1) * 13 ^ r) := by
  unfold morrisRow
  rw [if_pos hz, if_pos rfl]

theorem row_tail_block {z i d : ℕ} (hz : 4 * r ≤ z) (hd : d < 4) (hi : 4 * i + d < 4 * r) :
    morrisRow r p z (4 * i + d) = (if d < 2 then 3 else 1) * (2 ^ (p - 1) * 13 ^ (r - 1)) := by
  have h4 : 4 * i + d ≠ z := by omega
  have h7 : (4 * i + d) % 4 = d := by omega
  unfold morrisRow
  rw [if_pos hz, if_neg h4, if_pos hi, h7]

theorem row_tail_other {z u : ℕ} (hz : 4 * r ≤ z) (hu : 4 * r ≤ u) (huz : u ≠ z) :
    morrisRow r p z u = 0 := by
  have h : ¬ (u < 4 * r) := by omega
  unfold morrisRow
  rw [if_pos hz, if_neg huz, if_neg h]

/-! ### Block sums -/

/-- A block before the block of `u` contributes `52 (p+13) 13^(r-1) 2^j`. -/
theorem blk_after {j u : ℕ} (hj : j < r) (hu : 4 * j + 4 ≤ u) :
    ∑ c ∈ range 4, (morrisLam r p (4 * j + c) : ℤ) * morrisRow r p (4 * j + c) u
      = 52 * ((p : ℤ) + 13) * 13 ^ (r - 1) * 2 ^ j := by
  obtain ⟨a, ha⟩ : ∃ a, r = j + 1 + a := ⟨r - 1 - j, by omega⟩
  rw [sum_congr rfl fun c hc => by
    rw [lam_block ha (mem_range.1 hc), row_after hj (mem_range.1 hc) hu]]
  rw [show r - 1 = j + a by omega]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceLT, ↓reduceIte]
  ring

/-- A block `j = i + 1 + k` after the block `i` of `u = 4i + d` (with `r = j + 1 + l`). -/
theorem blk_before {i d k l : ℕ} (hr : r = i + 1 + k + 1 + l) (hd : d < 4) :
    ∑ c ∈ range 4, (morrisLam r p (4 * (i + 1 + k) + c) : ℤ)
        * morrisRow r p (4 * (i + 1 + k) + c) (4 * i + d)
      = (if d < 2 then 3 else 1) * ((p : ℤ) + 13) * 2 ^ (i + 1 + k) * 13 ^ (i + k + l)
          * (158 * 2 ^ (p + 4 * l) + 52) := by
  have hj : i + 1 + k < r := by omega
  rw [sum_congr rfl fun c hc => by
    rw [lam_block hr (mem_range.1 hc), row_before hj (mem_range.1 hc) hd (by omega)]]
  have e2 : morrisS r p (i + 1 + k) = 2 ^ (p + 4 * l) := by
    unfold morrisS; rw [show r - 1 - (i + 1 + k) = l by omega]
  rw [show i + 1 + k - 1 = i + k by omega, e2]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceLT, ↓reduceIte]
  ring

/-- The own block `i` of `u = 4i + d` (with `r = i + 1 + m`). -/
theorem blk_own {i d m : ℕ} (hr : r = i + 1 + m) (hd : d < 4) :
    ∑ c ∈ range 4, (morrisLam r p (4 * i + c) : ℤ) * morrisRow r p (4 * i + c) (4 * i + d)
      = -(((p : ℤ) + 13) * 2 ^ i * 13 ^ (i + m)
          * (if d < 2 then 6 * 2 ^ (p + 4 * m) + 52 else 2 * 2 ^ (p + 4 * m))) := by
  have hi : i < r := by omega
  have eS : morrisS r p i = 2 ^ (p + 4 * m) := by
    unfold morrisS; rw [show r - 1 - i = m by omega]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [lam_block hr (by norm_num : 0 < 4), lam_block hr (by norm_num : 1 < 4),
    lam_block hr (by norm_num : 2 < 4), lam_block hr (by norm_num : 3 < 4)]
  obtain rfl | rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  · rw [row_self hi (by norm_num : 0 < 4), row_same hi (by norm_num : 1 < 4) hd (by norm_num),
      row_same hi (by norm_num : 2 < 4) hd (by norm_num),
      row_same hi (by norm_num : 3 < 4) hd (by norm_num)]
    simp only [Nat.reduceLT, ↓reduceIte, eS]
    ring
  · rw [row_same hi (by norm_num : 0 < 4) hd (by norm_num), row_self hi (by norm_num : 1 < 4),
      row_same hi (by norm_num : 2 < 4) hd (by norm_num),
      row_same hi (by norm_num : 3 < 4) hd (by norm_num)]
    simp only [Nat.reduceLT, ↓reduceIte, eS]
    ring
  · rw [row_same hi (by norm_num : 0 < 4) hd (by norm_num),
      row_same hi (by norm_num : 1 < 4) hd (by norm_num), row_self hi (by norm_num : 2 < 4),
      row_same hi (by norm_num : 3 < 4) hd (by norm_num)]
    simp only [Nat.reduceLT, ↓reduceIte, eS]
    ring
  · rw [row_same hi (by norm_num : 0 < 4) hd (by norm_num),
      row_same hi (by norm_num : 1 < 4) hd (by norm_num),
      row_same hi (by norm_num : 2 < 4) hd (by norm_num), row_self hi (by norm_num : 3 < 4)]
    simp only [Nat.reduceLT, ↓reduceIte, eS]
    ring

/-! ### Tail sums -/

theorem tail_block {i d : ℕ} (hd : d < 4) (hi : 4 * i + d < 4 * r) :
    ∑ t ∈ range p, (morrisLam r p (4 * r + t) : ℤ) * morrisRow r p (4 * r + t) (4 * i + d)
      = (p : ℤ) *
          (4 * 2 ^ (r - 1) * ((if d < 2 then 3 else 1) * (2 ^ (p - 1) * 13 ^ (r - 1)))) := by
  rw [sum_congr rfl fun t _ => by
    rw [lam_tail (by omega : 4 * r ≤ 4 * r + t), row_tail_block (by omega) hd hi]]
  rw [sum_const, card_range, nsmul_eq_mul]

theorem tail_tail {u : ℕ} (hu1 : 4 * r ≤ u) (hu2 : u < 4 * r + p) :
    ∑ t ∈ range p, (morrisLam r p (4 * r + t) : ℤ) * morrisRow r p (4 * r + t) u
      = 4 * 2 ^ (r - 1) * (-(2 ^ (p - 1) * 13 ^ r)) := by
  rw [sum_eq_single (u - 4 * r)]
  · rw [show 4 * r + (u - 4 * r) = u by omega, lam_tail hu1, row_tail_self hu1]
  · intro t _ ht
    rw [row_tail_other (by omega) hu1 (by omega), mul_zero]
  · intro h
    exact absurd (mem_range.2 (by omega)) h

/-! ### The later blocks: telescoping bound -/

/-- The blocks after the block `i` of `u = 4i + d` contribute at most
`γ (p+13) 13^(i+m) 2^(p+r) (2^(3m) - 1)`, where `r = i + 1 + m`. -/
theorem later_le {i d m : ℕ} (hr : r = i + 1 + m) (hd : d < 4) (hp : 2 ≤ p) :
    ∑ k ∈ range m, ∑ c ∈ range 4, (morrisLam r p (4 * (i + 1 + k) + c) : ℤ)
        * morrisRow r p (4 * (i + 1 + k) + c) (4 * i + d)
      ≤ (if d < 2 then 3 else 1) * ((p : ℤ) + 13) * 13 ^ (i + m) * 2 ^ (p + i + 1 + m)
          * (2 ^ (3 * m) - 1) := by
  refine le_trans (sum_le_telescope _ (fun k => (if d < 2 then 3 else 1) * ((p : ℤ) + 13)
      * 13 ^ (i + m) * 2 ^ (p + i + 1 + m) * 2 ^ (3 * (m - k))) m ?_) (le_of_eq ?_)
  · intro k hk
    obtain ⟨l, rfl⟩ : ∃ l, m = k + 1 + l := ⟨m - 1 - k, by omega⟩
    rw [blk_before (by omega : r = i + 1 + k + 1 + l) hd,
      show k + 1 + l - k = l + 1 by omega, show k + 1 + l - (k + 1) = l by omega]
    have hS : (4 : ℤ) ≤ 2 ^ (p + 4 * l) := by
      calc (4 : ℤ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (p + 4 * l) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hX : (0 : ℤ) ≤ (if d < 2 then 3 else 1) * ((p : ℤ) + 13) * 2 ^ (i + 1 + k)
        * 13 ^ (i + k + l) := by positivity
    have h24 : (0 : ℤ) ≤ 24 * 2 ^ (p + 4 * l) - 52 := by linarith
    -- the telescoping step exceeds the block sum by `X (24 s_j - 52) ≥ 0`
    refine sub_nonneg.1 (le_of_le_of_eq (mul_nonneg hX h24) ?_)
    ring
  · simp only [Nat.sub_zero, Nat.sub_self, mul_zero, pow_zero]
    ring

/-! ### The two cases of the main theorem -/

/-- The total at a tail point `u` is `13^r (4(p+13)(2^r - 1) - 2^(p+r)) < 0`. -/
theorem neg_tail (hr : 1 ≤ r) (hp : 7 ≤ p) {u : ℕ} (hu1 : 4 * r ≤ u) (hu2 : u < 4 * r + p) :
    ∑ j ∈ range r, ∑ c ∈ range 4, (morrisLam r p (4 * j + c) : ℤ) * morrisRow r p (4 * j + c) u
      + ∑ t ∈ range p, (morrisLam r p (4 * r + t) : ℤ) * morrisRow r p (4 * r + t) u < 0 := by
  rw [sum_congr rfl fun j hj => blk_after (mem_range.1 hj) (by have := mem_range.1 hj; omega),
    ← mul_sum, geom_two, tail_tail hu1 hu2]
  obtain ⟨R, rfl⟩ : ∃ R, r = R + 1 := ⟨r - 1, by omega⟩
  obtain ⟨P, rfl⟩ : ∃ P, p = P + 7 := ⟨p - 7, by omega⟩
  rw [show R + 1 - 1 = R by omega, show P + 7 - 1 = P + 6 by omega]
  push_cast
  have e1 : (2 : ℤ) ^ (R + 1) = 2 * 2 ^ R := by ring
  have e2 : (13 : ℤ) ^ (R + 1) = 13 * 13 ^ R := by ring
  have e3 : (2 : ℤ) ^ (P + 6) = 64 * 2 ^ P := by ring
  rw [e1, e2, e3]
  have hP : (P : ℤ) < 2 ^ P := by exact_mod_cast Nat.lt_two_pow_self
  have hP0 : (0 : ℤ) ≤ P := by positivity
  have hX : (1 : ℤ) ≤ 2 ^ P := one_le_pow₀ (by norm_num)
  have hY : (0 : ℤ) < 2 ^ R := by positivity
  have key : ((P : ℤ) + 20) * (2 * 2 ^ R - 1) - 64 * 2 ^ P * 2 ^ R < 0 := by
    linarith [mul_nonneg (by linarith : (0 : ℤ) ≤ 32 * 2 ^ P - (P + 20)) hY.le]
  have key2 := mul_neg_of_pos_of_neg (by positivity : (0 : ℤ) < 52 * 13 ^ R) key
  linarith [key2]

/-- The total at a block point `u = 4i + d` is negative. -/
theorem neg_block (hp : 7 ≤ p) {i d : ℕ} (hd : d < 4) (hi : 4 * i + d < 4 * r) :
    ∑ j ∈ range r, ∑ c ∈ range 4, (morrisLam r p (4 * j + c) : ℤ)
        * morrisRow r p (4 * j + c) (4 * i + d)
      + ∑ t ∈ range p, (morrisLam r p (4 * r + t) : ℤ) * morrisRow r p (4 * r + t) (4 * i + d)
      < 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = i + 1 + m := ⟨r - 1 - i, by omega⟩
  have hL := later_le (p := p) (rfl : i + 1 + m = i + 1 + m) hd (by omega : 2 ≤ p)
  rw [tail_block hd hi, sum_range_add, sum_range_succ, blk_own rfl hd,
    sum_congr rfl fun j hj => blk_after (by have := mem_range.1 hj; omega)
      (by have := mem_range.1 hj; omega), ← mul_sum, geom_two]
  obtain ⟨P, rfl⟩ : ∃ P, p = P + 7 := ⟨p - 7, by omega⟩
  rw [show i + 1 + m - 1 = i + m by omega, show P + 7 - 1 = P + 6 by omega]
  push_cast at hL ⊢
  -- express every power through the atoms `2^P, 2^i, 2^m, 13^i, 13^m`
  have e1 : (13 : ℤ) ^ (i + m) = 13 ^ i * 13 ^ m := by ring
  have e2 : (2 : ℤ) ^ (P + 7 + 4 * m) = 128 * 2 ^ P * (2 ^ m) ^ 4 := by ring
  have e3 : (2 : ℤ) ^ (P + 7 + i + 1 + m) = 256 * 2 ^ P * 2 ^ i * 2 ^ m := by ring
  have e4 : (2 : ℤ) ^ (3 * m) = (2 ^ m) ^ 3 := by ring
  have e5 : (2 : ℤ) ^ (i + m) = 2 ^ i * 2 ^ m := by ring
  have e6 : (2 : ℤ) ^ (P + 6) = 64 * 2 ^ P := by ring
  rw [e1, e2, e5, e6]
  rw [e1, e3, e4] at hL
  have hP : (P : ℤ) < 2 ^ P := by exact_mod_cast Nat.lt_two_pow_self
  have hP0 : (0 : ℤ) ≤ P := by positivity
  have hX : (1 : ℤ) ≤ 2 ^ P := one_le_pow₀ (by norm_num)
  have hE : (1 : ℤ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hD : (1 : ℤ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hA : (0 : ℤ) < 13 ^ i * 13 ^ m := by positivity
  by_cases hd2 : d < 2
  · -- central `u`: the total is at most `13^(i+m) (-52 (p+13) - 39·2^(p+r))`
    simp only [if_pos hd2] at hL ⊢
    have h1 : (0 : ℤ) < 13 ^ i * 13 ^ m * (2 ^ P * 2 ^ i * 2 ^ m) := by positivity
    have h2 : (0 : ℤ) ≤ 13 ^ i * 13 ^ m * P := by positivity
    linarith [hL, h1, h2, hA]
  · -- outer `u`: the total is at most `52·13^(i+m) ((p+13)(2^i - 1) - 2^(p+r-2))`
    simp only [if_neg hd2] at hL ⊢
    have key : ((P : ℤ) + 20) * (2 ^ i - 1) - 64 * 2 ^ P * 2 ^ i * 2 ^ m < 0 := by
      have h1 : (0 : ℤ) ≤ (2 ^ P - P) * 2 ^ i := mul_nonneg (by linarith) (by positivity)
      have h2 : (0 : ℤ) ≤ (2 ^ P - 1) * 2 ^ i := mul_nonneg (by linarith) (by positivity)
      have h3 : (0 : ℤ) ≤ 2 ^ P * 2 ^ i * (2 ^ m - 1) :=
        mul_nonneg (by positivity) (by linarith)
      have h4 : (0 : ℤ) < 2 ^ P * 2 ^ i * 2 ^ m := by positivity
      linarith
    have key2 := mul_neg_of_pos_of_neg (by positivity : (0 : ℤ) < 52 * (13 ^ i * 13 ^ m)) key
    linarith [hL, key2]

end MorrisCert

/-- **Certificate negativity.**  For `r ≥ 1`, `p ≥ 7` and every point `u < 4r + p`, the weighted
sum of the closed-form rows with the integer multipliers `morrisLam` is strictly negative. -/
theorem morris_cert_neg (r p : ℕ) (hr : 1 ≤ r) (hp : 7 ≤ p) {u : ℕ} (hu : u < 4 * r + p) :
    ∑ z ∈ range (4 * r + p), (morrisLam r p z : ℤ) * morrisRow r p z u < 0 := by
  rw [MorrisCert.sum_split]
  by_cases hut : 4 * r ≤ u
  · exact MorrisCert.neg_tail hr hp hut hu
  · obtain ⟨i, d, hd, rfl⟩ : ∃ i d, d < 4 ∧ u = 4 * i + d :=
      ⟨u / 4, u % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod u 4).symm⟩
    exact MorrisCert.neg_block hp hd (by omega)

end Results.FcMorrisV2
