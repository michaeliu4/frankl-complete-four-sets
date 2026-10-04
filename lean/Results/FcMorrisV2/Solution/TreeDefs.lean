import Results.FcMorrisV2.Defs
import Mathlib.Data.List.Basic

/-!
# Solution/TreeDefs: labelled tree configurations `T_k` (paper Section 3.1)

A shape is a list `ts = [t₁, …, t_h]` of branch numbers (level `i` has `t_i` children per node).
A node is identified by its path from the root (a list of child indices); the leaves are the
paths of length `h`.  A labelling assigns a root set `R0` (of size `p ∈ {1,2}`) and a pair
`pr σ` to every nonroot node `σ`; the generators are the root-to-leaf unions.
-/

namespace Results.FcMorrisV2

open Finset

/-- Leaf paths of the tree with branch numbers `ts`. -/
def leafPaths : List ℕ → Finset (List ℕ)
  | [] => {[]}
  | t :: ts => (range t).biUnion fun j => (leafPaths ts).image fun π => j :: π

/-- Nonroot nodes: the nonempty prefixes of leaf paths. -/
def nodePaths (ts : List ℕ) : Finset (List ℕ) :=
  (leafPaths ts).biUnion fun π => (range π.length).image fun i => π.take (i + 1)

/-- The root together with all pairs on the way to the node `π`. -/
def pathSet (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) (π : List ℕ) : Finset ℕ :=
  R0 ∪ (range π.length).biUnion fun i => pr (π.take (i + 1))

/-- The labelled tree configuration: root-to-leaf unions. -/
def treeCfg (ts : List ℕ) (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) : Fam :=
  (leafPaths ts).image (pathSet R0 pr)

/-- A labelling is valid: every node pair has two points, and all appended pairs are pairwise
disjoint and disjoint from the root. -/
structure ValidLabel (ts : List ℕ) (R0 : Finset ℕ) (pr : List ℕ → Finset ℕ) : Prop where
  card : ∀ σ ∈ nodePaths ts, (pr σ).card = 2
  disjRoot : ∀ σ ∈ nodePaths ts, Disjoint (pr σ) R0
  disjPair : ∀ σ ∈ nodePaths ts, ∀ σ' ∈ nodePaths ts, σ ≠ σ' → Disjoint (pr σ) (pr σ')

/-- Number of nonroot nodes. -/
def nodeCount (ts : List ℕ) : ℕ := (nodePaths ts).card

end Results.FcMorrisV2
