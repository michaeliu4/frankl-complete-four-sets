# Frankl-complete sunflowers and extremal families of four-sets

**Mingchang Liu** · [mliu416@gatech.edu](mailto:mliu416@gatech.edu)  
Code and exact certificates accompanying manuscript **v1** · **Release v1**

A configuration is Frankl-complete (FC) if every finite union-closed family containing it has an element of the configuration's support in at least half its members. The manuscript studies this local forcing property for four-subsets: it proves a sharp sunflower criterion and quadratic growth of the extremal threshold, determines the exact value FC(4,9) = 16, and gives a counterexample to lexicographic extremality.

This repository supplies the computational part of the work. Its finite proofs use explicit integer certificates together with exhaustive generation and coverage arguments. The general analytic results are proved in the manuscript and do not depend on extrapolating the finite computations.

## Contents

| Directory | Result and contents |
|---|---|
| `fc49/` | Complete proof data for FC(4,9) = 16: indexed certificates, seven- and eight-point classifications, and exhaustive nine-point augmentation |
| `lexicographic/` | A fourteen-block lexicographic FC configuration and a spanning fourteen-block non-FC comparison |
| `common_pair/` | The sharp common-pair threshold on nine points and an FC configuration with no FC subconfiguration on a proper support |
| `finite_bounds/` | Explicit non-FC configurations giving lower bounds on 10–16 points |
| `portable/` | Optional clang compiler wrapper and standard-header shim |

The fifteen-block lower witness for the exact nine-point result is in `fc49/data/lower15.json`. A non-FC configuration is not a counterexample to Frankl's union-closed sets conjecture: its witness extension makes the original support scarce, while elements outside that support may be abundant.

## Requirements

- Python **3.10 or later**, using the standard library. Run with assertions enabled: do not use `-O`, `-OO`, or `PYTHONOPTIMIZE`.
- A **C++17 compiler** supporting unsigned 128-bit integers and a working compiler/SDK installation.

The drivers invoke `g++`. A working GCC installation can be used directly. For clang, including Apple clang on macOS, enable the supplied wrapper from the repository root:

```sh
export PATH="$PWD/portable/bin:$PATH"
```

The wrapper invokes the installed `clang++` and supplies a relative replacement for GCC's `bits/stdc++.h`. It does not install software. No numerical optimizer, external graph catalogue, network service, or nonstandard Python package is required.

Run the checks in a writable checkout. Entry points resolve their inputs relative to their own locations, so they may also be invoked by absolute path from another working directory.

## Complete nine-point verification

From the repository root:

```sh
python3 fc49/verify.py --workers 4
```

The driver compiles the checkers, invokes the foundation verifier, replays every indexed certificate, regenerates the orbit classifications and coverage witnesses, and performs the final nine-point enumerations. The number of workers may be adjusted.

Expected completed results:

- **4,333 certificate records:** 3,954 positive and 379 negative.
- **26,456,004 positive-tree nodes.**
- **52, 13, and 3** non-FC eight-point boundary types with nine, ten, and eleven blocks, respectively.
- **68 final bases**, with zero surviving sixteen-block augmentations in all three traversal modes.

| Final traversal | Visited states | Survivors |
|---|---:|---:|
| All stated pruning rules | 253,611 | 0 |
| Without seven-point pruning | 714,494 | 0 |
| Without interim degree pruning | 364,570 | 0 |

The foundation contributes 2,517 of the certificate records. Both full drivers describe their command-line options with `--help`.

## Individual certificate checks

These commands exercise smaller components without the complete nine-point replay:

```sh
# Fifteen-block lower witness and explicit tagged-extension counts:
python3 fc49/verify_lower_bound.py

# Fourteen-block lexicographic counterexample:
python3 lexicographic/verify.py

# Common-pair classification and all associated positive trees:
python3 common_pair/verify_all.py

# Nineteen-block and twenty-four-block negative witnesses:
python3 finite_bounds/verify_10_11.py

# Exact certificates for five specified Morris configurations:
python3 finite_bounds/verify_morris.py
```

Their expected coverage is:

| Check | Expected result |
|---|---|
| Lower witness | Nine admissible families; strictly negative integer combination; 100-set generator closure; exact slice counts for an extension on 138 points |
| Lexicographic comparison | Positive tree with 3,015 nodes and 1,508 leaves; exact negative auxiliary-family comparison |
| Common-pair classification | All 116,280 labelled complements and 65 isomorphism orbits; explicit embeddings; 18 positive trees containing 352,238 nodes |
| Bounds on 10 and 11 points | Non-FC configurations with 19 and 24 blocks, respectively |
| Bounds on 12–16 points | Non-FC configurations with 26, 30, 34, 38, and 51 blocks, respectively |

For each negative configuration, the lower bound on FC(4,n) is one more than its number of blocks. These additional lower witnesses do not determine the exact thresholds. The Morris verifier reconstructs the specified data using rational arithmetic, checks the resulting integer identities, and compares every field with the supplied certificate JSON.

## Generated files

No precompiled executable or saved successful run is required as an input. Verification produces:

- `fc49/run/`: compiled checkers, regenerated orbit and coverage files, logs, and the main verification report;
- `fc49/foundation/bin/`, `fc49/foundation/verification_report.json`, and `fc49/foundation/data/nonfc7_labeled.bin`: foundation programs and regenerated outputs;
- `common_pair/verify_positive`: the compiled common-pair checker;
- `finite_bounds/morris_exact.regenerated.json`: the reconstructed finite-bound certificates.

The lexicographic checker compiles in a temporary directory. Generated repository files and Python caches are excluded by `.gitignore`; they are not substitutes for the supplied source and certificates.

## Interpreting the verification

Positive certificates establish a weighted inequality for every admissible family by a complete decision tree with exact integer-flow bounds. Negative certificates supply actual union-closed, generator-stable families and a nonnegative integer combination whose imbalance is strictly negative. Exhaustive generation and coverage connect these local certificates to the finite threshold theorem.

The manuscript gives the mathematical certificate semantics and completeness arguments. Replaying a selected component establishes only its stated scope; it does not replace the complete finite verification. The implementation relies on the inspected source, compiler, standard libraries, and ordinary hardware execution, and is not a proof-assistant formalization.
