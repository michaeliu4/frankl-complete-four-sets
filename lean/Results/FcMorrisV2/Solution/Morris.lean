import Results.FcMorrisV2.Solution.MorrisRows
import Results.FcMorrisV2.Solution.MorrisCert

/-!
# Solution/Morris: Morris's ordered four-block configuration is not FC (paper Proposition B.3)
-/

namespace Results.FcMorrisV2

open Finset

/-- **Morris's configuration is not FC** (paper Proposition B.3). -/
theorem not_isFC_morris (r p : ℕ) (hr : 1 ≤ r) (hp : 7 ≤ p) : ¬ IsFC (morrisFam r p) := by
  apply not_isFC_of_coatoms (morrisFam r p) (morrisLam r p)
  intro u hu
  rw [morrisFam_supp r p hr] at hu ⊢
  have hu' : u < 4 * r + p := mem_range.1 hu
  rw [sum_congr rfl (fun z hz => by rw [rho_coatom_morris r p hr (mem_range.1 hz) hu'])]
  exact morris_cert_neg r p hr hp hu'

end Results.FcMorrisV2
