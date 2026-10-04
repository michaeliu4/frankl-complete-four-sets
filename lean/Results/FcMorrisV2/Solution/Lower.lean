import Results.FcMorrisV2.Solution.Morris
import Results.FcMorrisV2.Solution.Triples

/-!
# Solution/Lower: lower bounds for the thresholds (Theorem 1.1 lower, Theorem 1.3 lower)
-/

namespace Results.FcMorrisV2

open Finset

namespace Lower

/-- `FCge` is monotone (antitone in the claimed bound): a smaller bound is implied. -/
theorem fcge_mono {k n : ℕ} {x y : ℚ} (hxy : x ≤ y) (h : FCge k n y) : FCge k n x :=
  fun m hm => hxy.trans (h m hm)

end Lower

/-- A non-FC subfamily of the complete `k`-uniform hypergraph gives `FC(k,n) ≥ |B| + 1`. -/
theorem fcge_of_not_isFC {k n : ℕ} (B : Fam) (hB : B ⊆ blocks k n) (hnf : ¬ IsFC B) :
    FCge k n ((B.card : ℚ) + 1) := by
  intro m hm
  obtain ⟨_, _, hall⟩ := hm
  have hlt : B.card < m := by
    by_contra hle
    obtain ⟨G, hGB, hGcard⟩ := Finset.exists_subset_card_eq (not_lt.1 hle)
    have hG : G ∈ (blocks k n).powersetCard m :=
      Finset.mem_powersetCard.2 ⟨hGB.trans hB, hGcard⟩
    exact hnf (isFC_mono hGB (hall G hG))
  have h1 : B.card + 1 ≤ m := hlt
  exact_mod_cast h1

theorem lower_two (n : ℕ) : FCge 2 n 1 := by
  intro m hm
  exact_mod_cast hm.1

theorem lower_three (n : ℕ) : FCge 3 n ((n : ℚ) / 3) := by
  intro m hm
  set r := n / 3 with hr
  have hrm : (r : ℚ) + 1 ≤ (m : ℚ) := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · rw [h0, Nat.cast_zero, zero_add]
      exact_mod_cast hm.1
    · have hB : disjointTriples r ⊆ blocks 3 n := disjointTriples_subset_blocks r n (by omega)
      have h := fcge_of_not_isFC (disjointTriples r) hB (not_isFC_disjointTriples r hpos) m hm
      rwa [disjointTriples_card] at h
  have hn : n < 3 * r + 3 := by omega
  have hn' : (n : ℚ) < 3 * (r : ℚ) + 3 := by exact_mod_cast hn
  linarith

/-- Theorem 1.1, lower bound for `k ≥ 4`. -/
theorem lower_high (k : ℕ) (hk : 4 ≤ k) :
    ∃ c : ℚ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → FCge k n (c * (n : ℚ) ^ (k - 2)) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 3 := ⟨k - 3, by omega⟩
  have hk2 : d + 3 - 2 = d + 1 := by omega
  have hk3 : d + 3 - 3 = d := by omega
  refine ⟨1 / ((2 : ℚ) ^ (2 * d + 3) * (d.factorial : ℚ)), by positivity, 4 * d + 28, ?_⟩
  intro n hn
  rw [hk2]
  set r := n / 8 with hr
  set p := n - 4 * r with hp
  have hr1 : 1 ≤ r := by omega
  have hp7 : 7 ≤ p := by omega
  have hnrp : 4 * r + p = n := by omega
  have hB : morrisHigh r p (d + 3) ⊆ blocks (d + 3) n := by
    have := morrisHigh_subset_blocks r p (d + 3) (by omega)
    rwa [hnrp] at this
  have hnf : ¬ IsFC (morrisHigh r p (d + 3)) :=
    not_isFC_of_subset_ucl (not_isFC_morris r p hr1 hp7) (morrisHigh_subset_ucl r p (d + 3) hk)
  have hge := fcge_of_not_isFC _ hB hnf
  rw [morrisHigh_card r p (d + 3) (by omega), hk3] at hge
  refine Lower.fcge_mono ?_ hge
  -- the key inequality in `ℕ`: `n^(d+1) ≤ 2^(2d+3) d! · 2 r C(p,d)`
  have h1 : n ≤ 16 * r := by omega
  have h2 : n ≤ 4 * (p + 1 - d) := by omega
  have h3 : (p + 1 - d) ^ d ≤ d.factorial * p.choose d := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.pow_sub_le_descFactorial p d
  have h4 : n ^ d ≤ 4 ^ d * (d.factorial * p.choose d) := by
    calc n ^ d ≤ (4 * (p + 1 - d)) ^ d := Nat.pow_le_pow_left h2 d
      _ = 4 ^ d * (p + 1 - d) ^ d := by rw [mul_pow]
      _ ≤ 4 ^ d * (d.factorial * p.choose d) := Nat.mul_le_mul_left _ h3
  have key : n ^ (d + 1) ≤ 2 ^ (2 * d + 3) * d.factorial * (2 * r * p.choose d) := by
    calc n ^ (d + 1) = n ^ d * n := pow_succ n d
      _ ≤ 4 ^ d * (d.factorial * p.choose d) * (16 * r) := Nat.mul_le_mul h4 h1
      _ = 2 ^ (2 * d + 3) * d.factorial * (2 * r * p.choose d) := by
        rw [pow_add, pow_mul]; ring
  have keyQ : (n : ℚ) ^ (d + 1) ≤
      (2 : ℚ) ^ (2 * d + 3) * (d.factorial : ℚ) * ((2 * r * p.choose d : ℕ) : ℚ) := by
    exact_mod_cast key
  have hpos : (0 : ℚ) < (2 : ℚ) ^ (2 * d + 3) * (d.factorial : ℚ) := by positivity
  have hc : 1 / ((2 : ℚ) ^ (2 * d + 3) * (d.factorial : ℚ)) * (n : ℚ) ^ (d + 1) ≤
      ((2 * r * p.choose d : ℕ) : ℚ) := by
    rw [one_div_mul_eq_div, div_le_iff₀ hpos]
    linarith
  linarith

/-- Theorem 1.3(a): explicit lower bound. -/
theorem lower_explicit (n : ℕ) (hn : 11 ≤ n) :
    FCge 4 n ((1 : ℚ) + (((n - 7) / 4 : ℕ) : ℚ) *
      (2 * (n : ℚ) - 4 * (((n - 7) / 4 : ℕ) : ℚ) - 3)) := by
  set q := (n - 7) / 4 with hq
  set p := n - 4 * q with hp
  have hq1 : 1 ≤ q := by omega
  have hp7 : 7 ≤ p := by omega
  have hnqp : 4 * q + p = n := by omega
  have hB : morrisFam q p ⊆ blocks 4 n := by
    have := morrisFam_subset_blocks q p
    rwa [hnqp] at this
  have h := fcge_of_not_isFC (morrisFam q p) hB (not_isFC_morris q p hq1 hp7)
  rw [morrisFam_card] at h
  refine Lower.fcge_mono (le_of_eq ?_) h
  have h3 : 3 ≤ 4 * q + 2 * p := by omega
  have hn' : (n : ℚ) = 4 * (q : ℚ) + (p : ℚ) := by exact_mod_cast hnqp.symm
  rw [Nat.cast_mul, Nat.cast_sub h3]
  push_cast
  rw [hn']
  ring

/-- Theorem 1.3(c), lower coefficient `1/4`. -/
theorem lower_asymp (ε : ℚ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → FCge 4 n ((1 / 4 - ε) * (n : ℚ) ^ 2) := by
  refine ⟨11 + 5 * ε.den, fun n hn => ?_⟩
  have hn11 : 11 ≤ n := by omega
  refine Lower.fcge_mono ?_ (lower_explicit n hn11)
  set q := (n - 7) / 4 with hq
  have h1 : 4 * q + 7 ≤ n := by omega
  have h2 : n ≤ 4 * q + 10 := by omega
  have h1' : 4 * (q : ℚ) + 7 ≤ (n : ℚ) := by exact_mod_cast h1
  have h2' : (n : ℚ) ≤ 4 * (q : ℚ) + 10 := by exact_mod_cast h2
  have hN : (11 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn11
  have hden : (1 : ℚ) ≤ ε * (ε.den : ℚ) := by
    rw [Rat.mul_den_eq_num]
    have h0 : 0 < ε.num := Rat.num_pos.2 hε
    have hnum : (1 : ℤ) ≤ ε.num := by omega
    exact_mod_cast hnum
  have hden2 : 5 * (ε.den : ℚ) ≤ (n : ℚ) := by
    have : 5 * ε.den ≤ n := by omega
    exact_mod_cast this
  -- `ε n ≥ ε · 5 den = 5 (ε den) ≥ 5`
  have hεn : 5 ≤ ε * (n : ℚ) := by
    linarith [mul_le_mul_of_nonneg_left hden2 hε.le]
  -- `bound - (1/4 - ε) n² = (ε n² - 5n) + (100 - (n - 4q)²)/4 + (5n - 3q - 24)`
  have hA : 5 * (n : ℚ) ≤ ε * (n : ℚ) * (n : ℚ) :=
    mul_le_mul_of_nonneg_right hεn (by linarith)
  have hB : 0 ≤ (4 * (q : ℚ) + 10 - n) * ((n : ℚ) - 4 * q + 10) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

end Results.FcMorrisV2
