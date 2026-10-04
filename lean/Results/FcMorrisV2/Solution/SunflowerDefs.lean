import Results.FcMorrisV2.Solution.Basic

/-!
# Solution/SunflowerDefs: the four-uniform sunflower configuration `S_t`
-/

namespace Results.FcMorrisV2

open Finset

/-- The four-uniform sunflower `{C ∪ P i : i < t}`. -/
def sunflowerCfg (t : ℕ) (C : Finset ℕ) (P : Fin t → Finset ℕ) : Fam :=
  (Finset.univ : Finset (Fin t)).image fun i => C ∪ P i

/-- Hypotheses: a two-point core and `t` pairwise disjoint pairs disjoint from it. -/
structure SunflowerData (t : ℕ) (C : Finset ℕ) (P : Fin t → Finset ℕ) : Prop where
  hC : C.card = 2
  hP : ∀ i, (P i).card = 2
  hCP : ∀ i, Disjoint C (P i)
  hPP : ∀ i j, i ≠ j → Disjoint (P i) (P j)

end Results.FcMorrisV2
