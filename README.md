# Frankl-complete sunflowers and extremal families of four-sets

**Mingchang Liu** · [mliu416@gatech.edu](mailto:mliu416@gatech.edu)

Code and exact certificates accompanying manuscript **v1.1**. Repository release: **v1.1**.

This repository supplies the computational material for the finite results in
Sections 5 and 6 of the manuscript. The main verification establishes
**FC(4,9) = 16**. The other programs check a lexicographic counterexample, the
common-pair classification, and additional finite lower bounds. The analytic
sunflower criterion and the quadratic bound FC(4,n) = Θ(n²) are proved in the
manuscript and do not depend on these computations.

## Requirements

Use **Python 3.10 or later** and a **C++17 compiler** supporting unsigned
128-bit integers. Only the Python standard library is needed. Run with
assertions enabled: do not use `-O`, `-OO`, or `PYTHONOPTIMIZE`.

The drivers invoke `g++`. With GCC, use the normal compiler configuration.
For clang, including Apple clang, enable the supplied header shim from the
repository root:

```sh
export PATH="$PWD/portable/bin:$PATH"
```

This wrapper requires an installed `clang++` and its normal compiler/SDK.
No numerical optimizer or external isomorphism catalogue is required.

## Verify FC(4,9) = 16

From a writable checkout or extracted source archive, run:

```sh
python3 fc49/verify.py --workers 4
```

The driver compiles the checkers, verifies the certificates, regenerates the
orbit lists and coverage witnesses, and runs all three final enumerations.
The expected totals are **4,333 certificates** (3,954 positive and 379 negative)
and **26,456,004 positive-tree nodes**. The eight-point boundary layers have
52, 13, and 3 types, giving 68 final bases.

| Final traversal | Visited states | Survivors |
|---|---:|---:|
| All stated pruning rules | 253,611 | 0 |
| Without seven-point pruning | 714,494 | 0 |
| Without interim degree pruning | 364,570 | 0 |

A successful complete run prints `PASS: FC(4,9)=16.` followed by a summary.
Both `fc49/verify.py` and `fc49/foundation/verify.py` list their options with
`--help`; the number of workers may be adjusted.

A complete reference replay of these algorithms and certificates on macOS
arm64 (Darwin 24.6.0), using Python 3.14.2, Apple clang 16.0.0 and four
workers, took about 25 minutes including compilation. This is an observed
runtime, not a bound; peak memory was not measured.

## Check individual results

These commands run the smaller components separately:

```sh
python3 fc49/verify_lower_bound.py
python3 lexicographic/verify.py
python3 common_pair/verify_all.py
python3 finite_bounds/verify_10_11.py
python3 finite_bounds/verify_morris.py
```

| Component | Expected result | Manuscript |
|---|---|---|
| `fc49/` | Complete nine-point verification; the standalone lower-bound check verifies nine admissible families, a 100-set generator closure, and the exact slice counts for an extension on 138 points | Section 5.1–5.4; Tables 1–3 |
| `lexicographic/` | Fourteen-block FC initial segment and non-FC comparison; positive tree with 3,015 nodes and 1,508 leaves | Corollary 5.3 |
| `common_pair/` | All 116,280 labelled complements in 65 orbits, their covering embeddings, and 18 positive trees with 352,238 nodes | Proposition 6.2 |
| `finite_bounds/` | Non-FC configurations with 19, 24, 26, 30, 34, 38, and 51 blocks on 10–16 points, respectively | Table 4 |

A negative configuration with m blocks gives the lower bound FC(4,n) ≥ m+1;
the additional witnesses do not determine exact thresholds. Non-FC refers to
abundance on the original support, so these witnesses are not counterexamples
to Frankl's union-closed sets conjecture. A partial check verifies only its
listed component.

## Files and generated output

Each directory contains its source and required data. Positive proof trees,
negative families, and the operative indexes are supplied; the fifteen-block
witness is `fc49/data/lower15.json`. Entry points resolve inputs relative to
their own locations and can also be invoked by absolute path.

Verification generates the following files, which are excluded by `.gitignore`:

- `fc49/run/`: compiled checkers, regenerated orbit and coverage files, and reports;
- `fc49/foundation/bin/`, `fc49/foundation/verification_report.json`, and
  `fc49/foundation/data/nonfc7_labeled.bin`: foundation programs and outputs;
- `common_pair/verify_positive`: the common-pair executable;
- `finite_bounds/morris_exact.regenerated.json`: reconstructed certificate data.

The common-pair manifest retains `atlas_64` as an additional certified
configuration. It is replayed with the other trees but is not used by the
selected 65-orbit covering witnesses; the stated 18-tree total includes it.

Verification reports contain execution timings and are not expected to have
identical hashes across runs. A successful reproduction completes with
`PASS` and satisfies the driver's exact certificate, generation, coverage,
and final-enumeration assertions. The fixed archive on the release page
identifies the distributed files; a runtime-report hash is not a proof check.

The lexicographic checker compiles in a temporary directory. No previously
compiled executable or saved run report is needed. The manuscript explains the
certificate inequalities and the completeness argument connecting these finite
checks to the theorem.

## Citation and license

Cite the accompanying manuscript and the versioned companion release when
using these results or materials. `CITATION.cff` supplies the repository's
citation metadata. The code, certificate data and documentation in this
repository are distributed under the [MIT License](LICENSE).
