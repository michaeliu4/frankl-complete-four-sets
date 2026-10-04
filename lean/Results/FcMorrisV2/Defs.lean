import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat

/-!
# Frankl-complete configurations: statement-level definitions

Paper: "Frankl-complete configurations and Morris's asymptotic conjecture" (V2).
Points are natural numbers; a *configuration* is a finite family of finite sets of points.

* `IsFC G` : every finite union-closed extension `F ⊇ G` (which may use arbitrary extra points)
  has a point `u` of the support of `G` lying in at least `|F|/2` members of `F`.
  The empty configuration is not FC (its support is empty).
* `blocks k n` : the complete `k`-uniform hypergraph on `[n] = {0, …, n-1}`.
* `AllFC k n m` : `m` is an admissible size for the threshold `FC(k,n)`, i.e.
  `1 ≤ m ≤ C(n,k)` and every `m`-member subfamily of `blocks k n` is FC.
  `FC(k,n)` is the least such `m` (if one exists).
* `FCge k n x` : `x ≤ FC(k,n)` (every admissible `m` is at least `x`; vacuous when `FC(k,n)` does
  not exist).
* `FCle k n x` : `FC(k,n) ≤ x` (an admissible `m ≤ x` exists, so `FC(k,n)` exists).
* `FurediSemilattice` and `ChungFranklNine` are the two published theorems of the paper that are
  not in Mathlib; they are carried as explicit hypotheses (never as axioms).
-/

namespace Results.FcMorrisV2

open Finset

/-- A family of finite sets of points (points are natural numbers). -/
abbrev Fam := Finset (Finset ℕ)

/-- Union-closed family. -/
def UnionClosed (F : Fam) : Prop := ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- Support of a configuration: the union of its members. -/
def supp (G : Fam) : Finset ℕ := G.biUnion id

/-- Number of members of `F` containing the point `u`. -/
def deg (F : Fam) (u : ℕ) : ℕ := (F.filter fun A => u ∈ A).card

/-- **Frankl-complete** configuration: every finite union-closed extension has a point of the
support lying in at least half of its members. -/
def IsFC (G : Fam) : Prop :=
  ∀ F : Fam, G ⊆ F → UnionClosed F → ∃ u ∈ supp G, F.card ≤ 2 * deg F u

/-- `G`-admissible family on the support `U = supp G`: members lie in `U`, the family is
union-closed and stable under adjoining every generator. -/
def Admissible (G B : Fam) : Prop :=
  (∀ X ∈ B, X ⊆ supp G) ∧ UnionClosed B ∧ ∀ X ∈ B, ∀ g ∈ G, X ∪ g ∈ B

/-- All `k`-subsets of `[n] = {0, …, n-1}`. -/
def blocks (k n : ℕ) : Fam := (range n).powersetCard k

/-- `m` is an admissible size for the threshold `FC(k,n)`: `1 ≤ m ≤ C(n,k)` and every
`m`-member subfamily of `blocks k n` is FC. -/
def AllFC (k n m : ℕ) : Prop :=
  1 ≤ m ∧ m ≤ n.choose k ∧ ∀ G ∈ (blocks k n).powersetCard m, IsFC G

/-- `x ≤ FC(k,n)`, where `FC(k,n)` is the least `m` with `AllFC k n m`. -/
def FCge (k n : ℕ) (x : ℚ) : Prop := ∀ m : ℕ, AllFC k n m → x ≤ (m : ℚ)

/-- `FC(k,n) ≤ x`; in particular `FC(k,n)` exists. -/
def FCle (k n : ℕ) (x : ℚ) : Prop := ∃ m : ℕ, AllFC k n m ∧ (m : ℚ) ≤ x

/-- `H` contains an `s`-member sunflower with exact core `D`: `s` distinct members whose pairwise
intersections all equal `D`. -/
def IsSunflower (H : Fam) (s : ℕ) (D : Finset ℕ) : Prop :=
  ∃ S ∈ H.powerset, S.card = s ∧ (∀ f ∈ S, D ⊆ f) ∧ ∀ f ∈ S, ∀ f' ∈ S, f ≠ f' → f ∩ f' = D

/-- **Füredi's intersection-semilattice theorem** in the form recorded in the paper
(Theorem 4.1; Füredi 1983, O'Neill–Verstraëte 2021, Lemma 9).  For fixed `k, s` there is
`γ > 0` such that every nonempty `k`-uniform hypergraph `H` on `[n]` contains a `k`-partite
subhypergraph `Hs` with `|Hs| ≥ γ |H|` and a common intersection-closed pattern `J` of proper
subsets of `[k]` such that: each edge meets each part `X i` in exactly one vertex; for every edge
`e ∈ Hs` the set of patterns `{i : e ∩ f ∩ X i ≠ ∅}` over `f ∈ Hs`, `f ≠ e`, equals `J`; and for
every `e ∈ Hs`, `I ∈ J` the set `e[I] = e ∩ ⋃_{i ∈ I} X i` is the exact core of an `s`-member
sunflower of edges of `Hs`.  (Formalization notes: the constant `γ` depends only on `(k, s)`; the
parts `X i` are pairwise disjoint but need not cover `[n]`; a one-edge `Hs` has `J = ∅`; the
statement for every `s ≥ 1` follows from the version for large `s` because `IsSunflower` is
monotone in `s`.) -/
def FurediSemilattice : Prop :=
  ∀ k s : ℕ, 1 ≤ k → 1 ≤ s → ∃ γ : ℚ, 0 < γ ∧ ∀ (n : ℕ) (H : Fam),
    H.Nonempty → (∀ e ∈ H, e ⊆ range n ∧ e.card = k) →
    ∃ (Hs : Fam) (X : Fin k → Finset ℕ) (J : Finset (Finset (Fin k))),
      Hs ⊆ H ∧ γ * (H.card : ℚ) ≤ (Hs.card : ℚ) ∧
      (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧
      (∀ e ∈ Hs, ∀ i, (e ∩ X i).card = 1) ∧
      (∀ I ∈ J, I ≠ Finset.univ) ∧
      (∀ I ∈ J, ∀ I' ∈ J, I ∩ I' ∈ J) ∧
      (∀ e ∈ Hs, (Hs.erase e).image
          (fun f => (Finset.univ : Finset (Fin k)).filter fun i => (e ∩ f ∩ X i).Nonempty) = J) ∧
      (∀ e ∈ Hs, ∀ I ∈ J, IsSunflower Hs s (e ∩ I.biUnion X))

/-- **Chung–Frankl theorem** (1987, Theorem 1.1), upper bound for `k = 9` petals and a one-point
core: a triple system on `N > 1692 = 9·8·47/2` points with no `9`-petal sunflower with a one-point
core has at most `72 N + O(1)` triples.  (Only the leading term of the published asymptotic
formula is used.) -/
def ChungFranklNine : Prop :=
  ∃ C₀ : ℕ, ∀ V : Finset ℕ, 1692 < V.card → ∀ T : Fam, (∀ f ∈ T, f ⊆ V ∧ f.card = 3) →
    (¬ ∃ x : ℕ, IsSunflower T 9 {x}) → T.card ≤ 72 * V.card + C₀

end Results.FcMorrisV2
