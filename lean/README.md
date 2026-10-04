# Frankl complete four-sets Lean package

This standalone Lean 4 package contains the checked proof closure for the Frankl complete-four-sets results formalized under `Results.FcMorrisV2`. The default `Results` library imports `Results.FcMorrisV2.Solution.Main`; challenge and test files are intentionally excluded.

## Main declarations

- `Results.FcMorrisV2.thm_1_1`
- `Results.FcMorrisV2.thm_1_2`
- `Results.FcMorrisV2.thm_1_3`

## Assurance and assumptions

Recorded audit status: **Level 3, full_assuming; EXPLORATORY**. This is conditional verification, not an unconditional full verification. The external mathematical assumptions are the propositions `Results.FcMorrisV2.FurediSemilattice` and `Results.FcMorrisV2.ChungFranklNine`. Theorem 1.1 is conditional on `FurediSemilattice`; the final asymptotic upper-bound conjunct of Theorem 1.3 is conditional on `ChungFranklNine`. Theorem 1.2 is unconditional within the formalization.

`PrintAxioms.lean` prints Lean's axiom dependencies for the three main declarations.

## Provenance and build

The proof sources are byte-for-byte copies from private main commit `b3da9c75451546c72845b58d74308222adb5f9ae`. `SOURCE-PROVENANCE.json` records each source and public Git blob hash. The package pins Lean and mathlib to `v4.32.1` and includes the corresponding dependency manifest.

Run these commands from the repository root. Build and provenance files are at that root.

```sh
lake exe cache get
lake build Results
lake env lean PrintAxioms.lean
```

No license is granted for the Lean source files in this package. These newly packaged Lean sources are excluded from the repository's existing MIT grant.
