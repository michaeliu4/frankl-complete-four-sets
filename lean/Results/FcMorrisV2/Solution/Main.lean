import Results.FcMorrisV2.Solution.Trees
import Results.FcMorrisV2.Solution.Embedding
import Results.FcMorrisV2.Solution.Lower
import Results.FcMorrisV2.Solution.UpperFour
import Results.FcMorrisV2.Solution.SunflowerPos
import Results.FcMorrisV2.Solution.SunflowerNeg

/-!
# Solution/Main: Theorems 1.1, 1.2 and 1.3 (same statements as `Challenge`)
-/

namespace Results.FcMorrisV2

open Finset

namespace Main

/-- `FCge` is antitone in the bound. -/
theorem fcge_of_le {k n : ℕ} {x y : ℚ} (h : FCge k n x) (hyx : y ≤ x) : FCge k n y :=
  fun m hm => le_trans hyx (h m hm)

/-- `C(n,j) ≤ n^j`. -/
theorem choose_le_pow (n : ℕ) : ∀ j : ℕ, n.choose j ≤ n ^ j
  | 0 => by simp only [Nat.choose_zero_right, pow_zero, le_refl]
  | j + 1 => by
    calc n.choose (j + 1) ≤ n.choose (j + 1) * (j + 1) :=
          Nat.le_mul_of_pos_right _ (Nat.succ_pos j)
      _ = n.choose j * (n - j) := Nat.choose_succ_right_eq n j
      _ ≤ n ^ j * n := Nat.mul_le_mul (choose_le_pow n j) (Nat.sub_le n j)
      _ = n ^ (j + 1) := (pow_succ n j).symm

/-- `k(k-1) C(n,k) = C(n,k-2) (n-k+2)(n-k+1)`, written with `k = j + 2`. -/
theorem choose_add_two_mul (n j : ℕ) :
    n.choose (j + 2) * ((j + 2) * (j + 1)) = n.choose j * ((n - j) * (n - (j + 1))) := by
  have h1 := Nat.choose_succ_right_eq n j
  have h2 := Nat.choose_succ_right_eq n (j + 1)
  calc n.choose (j + 2) * ((j + 2) * (j + 1))
      = n.choose (j + 1 + 1) * (j + 1 + 1) * (j + 1) := by ring
    _ = n.choose (j + 1) * (n - (j + 1)) * (j + 1) := by rw [h2]
    _ = n.choose (j + 1) * (j + 1) * (n - (j + 1)) := by ring
    _ = n.choose j * (n - j) * (n - (j + 1)) := by rw [h1]
    _ = n.choose j * ((n - j) * (n - (j + 1))) := by ring

/-- For `n ≥ j + 1 + (A+1)(j+2)(j+1)`: `A·C(n,j) + 1 ≤ C(n,j+2)`. -/
theorem choose_gap (A j n : ℕ) (hn : j + 1 + (A + 1) * ((j + 2) * (j + 1)) ≤ n) :
    A * n.choose j + 1 ≤ n.choose (j + 2) := by
  have hpos : 0 < n.choose j := Nat.choose_pos (by omega)
  have hbig : (A + 1) * ((j + 2) * (j + 1)) ≤ (n - j) * (n - (j + 1)) := by
    have h3 : (A + 1) * ((j + 2) * (j + 1)) ≤ n - (j + 1) := by omega
    have h4 : 1 ≤ n - j := by omega
    calc (A + 1) * ((j + 2) * (j + 1)) ≤ n - (j + 1) := h3
      _ = 1 * (n - (j + 1)) := (one_mul _).symm
      _ ≤ (n - j) * (n - (j + 1)) := Nat.mul_le_mul_right _ h4
  have hD : 0 < (j + 2) * (j + 1) := by positivity
  have hmul : (A + 1) * n.choose j * ((j + 2) * (j + 1)) ≤
      n.choose (j + 2) * ((j + 2) * (j + 1)) := by
    rw [choose_add_two_mul]
    calc (A + 1) * n.choose j * ((j + 2) * (j + 1))
        = n.choose j * ((A + 1) * ((j + 2) * (j + 1))) := by ring
      _ ≤ n.choose j * ((n - j) * (n - (j + 1))) := Nat.mul_le_mul_left _ hbig
  have hle : (A + 1) * n.choose j ≤ n.choose (j + 2) := Nat.le_of_mul_le_mul_right hmul hD
  calc A * n.choose j + 1 ≤ A * n.choose j + n.choose j := by omega
    _ = (A + 1) * n.choose j := by ring
    _ ≤ n.choose (j + 2) := hle

/-- `k = p + 2h` with `p ∈ {1,2}` and `h ≥ 1`, for `k ≥ 3`. -/
theorem decomp (k : ℕ) (hk : 3 ≤ k) :
    ∃ p h : ℕ, (p = 1 ∨ p = 2) ∧ 1 ≤ h ∧ k = p + 2 * h := by
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
  · exact ⟨2, j - 1, Or.inr rfl, by omega, by omega⟩
  · exact ⟨1, j, Or.inl rfl, by omega, by omega⟩

/-- `k = 2`: a single pair is FC, so `m = 1` is admissible for `n ≥ 2`. -/
theorem allFC_two (n : ℕ) (hn : 2 ≤ n) : AllFC 2 n 1 := by
  refine ⟨le_refl 1, Nat.choose_pos hn, ?_⟩
  intro G hG
  rw [Finset.mem_powersetCard] at hG
  obtain ⟨hGsub, hGcard⟩ := hG
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hGcard
  have ha : a ∈ blocks 2 n := hGsub (Finset.mem_singleton_self a)
  rw [blocks, Finset.mem_powersetCard] at ha
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp ha.2
  exact RobustFC.isFC (robust_pair hxy)

/-- Upper bound of Theorem 1.1 for `k ≥ 3` (assuming Füredi's theorem):
`FC(k,n) ≤ A·C(n,k-2) + 1 ≤ (A+1) n^(k-2)` for all large `n`. -/
theorem upper_high (hFur : FurediSemilattice) (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℚ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → FCle k n (C * (n : ℚ) ^ (k - 2)) := by
  obtain ⟨p, h, hp, hh, hkph⟩ := decomp k hk
  obtain ⟨ts, hts, hts1, hFC⟩ := robust_tree p h hp
  obtain ⟨A, hA⟩ := ex_tree hFur p h hp hh ts hts hts1
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  refine ⟨(A : ℚ) + 1, by positivity, j + 1 + (A + 1) * ((j + 2) * (j + 1)), fun n hn => ?_⟩
  rw [Nat.add_sub_cancel]
  refine ⟨A * n.choose j + 1, ⟨Nat.le_add_left 1 _, choose_gap A j n hn, ?_⟩, ?_⟩
  · intro G hG
    rw [Finset.mem_powersetCard] at hG
    obtain ⟨hGsub, hGcard⟩ := hG
    have hedges : ∀ e ∈ G, e ⊆ range n ∧ e.card = p + 2 * h := by
      intro e he
      have he' := hGsub he
      rw [blocks, Finset.mem_powersetCard] at he'
      exact ⟨he'.1, by omega⟩
    have hlt : A * n.choose (p + 2 * h - 2) < G.card := by
      rw [hGcard, show p + 2 * h - 2 = j by omega]
      exact Nat.lt_succ_self _
    obtain ⟨R0, pr, hR0, hVL, hsub⟩ := hA n G hedges hlt
    exact isFC_mono hsub (hFC R0 pr hR0 hVL)
  · have hn1 : 0 < n := by omega
    have hnat : A * n.choose j + 1 ≤ (A + 1) * n ^ j :=
      calc A * n.choose j + 1 ≤ A * n ^ j + n ^ j :=
            Nat.add_le_add (Nat.mul_le_mul_left A (choose_le_pow n j)) (Nat.one_le_pow j n hn1)
        _ = (A + 1) * n ^ j := by ring
    calc ((A * n.choose j + 1 : ℕ) : ℚ) ≤ (((A + 1) * n ^ j : ℕ) : ℚ) := Nat.cast_le.mpr hnat
      _ = ((A : ℚ) + 1) * (n : ℚ) ^ j := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]

/-- Lower bound of Theorem 1.1 for `k ≥ 3`. -/
theorem lower_ge_three (k : ℕ) (hk : 3 ≤ k) :
    ∃ c : ℚ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → FCge k n (c * (n : ℚ) ^ (k - 2)) := by
  rcases Nat.lt_or_ge k 4 with h4 | h4
  · obtain rfl : k = 3 := by omega
    refine ⟨1 / 3, by norm_num, 0, fun n _ => ?_⟩
    have hx : (1 / 3 : ℚ) * (n : ℚ) ^ (3 - 2) = (n : ℚ) / 3 := by
      rw [show (3 : ℕ) - 2 = 1 from rfl, pow_one]; ring
    exact fcge_of_le (lower_three n) (le_of_eq hx)
  · exact lower_high k h4

end Main

/-- **Theorem 1.1** (Morris's asymptotic conjecture). -/
theorem thm_1_1 : FurediSemilattice → ∀ k : ℕ, 2 ≤ k →
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      FCge k n (c * (n : ℚ) ^ (k - 2)) ∧ FCle k n (C * (n : ℚ) ^ (k - 2)) := by
  intro hFur k hk
  rcases Nat.lt_or_ge k 3 with h3 | h3
  · obtain rfl : k = 2 := by omega
    refine ⟨1, 1, one_pos, one_pos, 2, fun n hn => ⟨?_, ?_⟩⟩
    · have h1 : (1 : ℚ) * (n : ℚ) ^ (2 - 2) = 1 := by
        rw [Nat.sub_self, pow_zero, one_mul]
      exact Main.fcge_of_le (lower_two n) (le_of_eq h1)
    · have h1 : ((1 : ℕ) : ℚ) = (1 : ℚ) * (n : ℚ) ^ (2 - 2) := by
        rw [Nat.sub_self, pow_zero, one_mul, Nat.cast_one]
      exact ⟨1, Main.allFC_two n hn, le_of_eq h1⟩
  · obtain ⟨c, hc, n₁, hn₁⟩ := Main.lower_ge_three k h3
    obtain ⟨C, hC, n₂, hn₂⟩ := Main.upper_high hFur k h3
    exact ⟨c, C, hc, hC, max n₁ n₂, fun n hn =>
      ⟨hn₁ n (le_trans (le_max_left _ _) hn), hn₂ n (le_trans (le_max_right _ _) hn)⟩⟩

/-- **Theorem 1.2**. -/
theorem thm_1_2 (t : ℕ) (C : Finset ℕ) (P : Fin t → Finset ℕ) (hC : C.card = 2)
    (hP : ∀ i, (P i).card = 2) (hCP : ∀ i, Disjoint C (P i))
    (hPP : ∀ i j, i ≠ j → Disjoint (P i) (P j)) :
    (IsFC ((Finset.univ : Finset (Fin t)).image fun i => C ∪ P i) ↔ 9 ≤ t) ∧
    (t = 9 → ∀ B : Fam,
      Admissible ((Finset.univ : Finset (Fin t)).image fun i => C ∪ P i) B →
        0 ≤ ∑ X ∈ B, (3 * ((X ∩ C).card : ℤ) + ((X \ C).card : ℤ) - 12)) := by
  have hd : SunflowerData t C P := ⟨hC, hP, hCP, hPP⟩
  change (IsFC (sunflowerCfg t C P) ↔ 9 ≤ t) ∧ (t = 9 → ∀ B : Fam,
      Admissible (sunflowerCfg t C P) B →
        0 ≤ ∑ X ∈ B, (3 * ((X ∩ C).card : ℤ) + ((X \ C).card : ℤ) - 12))
  refine ⟨⟨fun hFC => ?_, fun ht => sunflower_isFC hd ht⟩, fun ht B hB => ?_⟩
  · by_contra hlt
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      have hempty : sunflowerCfg 0 C P = ∅ := by
        simp only [sunflowerCfg, Finset.univ_eq_empty, Finset.image_empty]
      rw [hempty] at hFC
      exact not_isFC_empty hFC
    · exact sunflower_not_isFC hd hpos (by omega) hFC
  · have hQ := sunflower_share_nonneg hd (by omega) B hB
    have h12 : (3 + (t : ℚ)) = 12 := by rw [ht]; norm_num
    rw [h12] at hQ
    have hZ : (0 : ℚ) ≤
        ((∑ X ∈ B, (3 * ((X ∩ C).card : ℤ) + ((X \ C).card : ℤ) - 12) : ℤ) : ℚ) := by
      push_cast
      exact hQ
    exact Int.cast_nonneg_iff.mp hZ

/-- **Theorem 1.3**. -/
theorem thm_1_3 :
    (∀ n : ℕ, 11 ≤ n →
      FCge 4 n ((1 : ℚ) + (((n - 7) / 4 : ℕ) : ℚ) *
        (2 * (n : ℚ) - 4 * (((n - 7) / 4 : ℕ) : ℚ) - 3))) ∧
    (∀ n : ℕ, 20 ≤ n → FCle 4 n (((1 + 160 * n * (n - 1) / 3 : ℕ)) : ℚ)) ∧
    (∀ ε : ℚ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → FCge 4 n ((1 / 4 - ε) * (n : ℚ) ^ 2)) ∧
    (ChungFranklNine → ∀ ε : ℚ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      FCle 4 n ((18 + ε) * (n : ℚ) ^ 2)) := by
  exact ⟨fun n hn => lower_explicit n hn, fun n hn => upper_explicit n hn,
    fun ε hε => lower_asymp ε hε, fun hCF ε hε => upper_asymp hCF ε hε⟩

end Results.FcMorrisV2
