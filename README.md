# fieldStemProof

Formalizing, in Lean 4 + Mathlib, **machine-checked absolute lower bounds for
tensor-network contraction ordering (TNCO)**: certified width/cost floors for **stem
(sweep) contraction orders**, plus a framework-level generic no-compression theorem on
the rank side.

## Claim (layered — see `docs/spec.md` and `paper/main.tex`)

- **Width/cost floors** *(proved; the paper's core)* — interval-Helly bramble bounds
  (`Bramble`, `GridConn`), the exact augmented-bramble floor (`GridExact`), the faithful
  `gridModel` whose orders are genuine path decompositions (`cc = N+1` pinned both
  sides), and the cost floor `2^{N+1} ≤ orderCost` (`GridModel`).
- **Theorem A** *(proved skeleton)* — `cc ≤ pw`, the stem optimum is attained, and given
  the lattice bound `pw ≤ C·cc` a stem order within factor `C` of optimal exists. The
  lattice bound (`pw = Θ(tw)`) stays a named `Prop` supplied per model, never a global
  axiom.
- **Lemma B / Contraction Rigidity** *(proved)* — the genericity engine, the structural
  theorem `BulkEntangling ⇒ ContractionRigid`, and
  `ContractionRigid.no_compression`. The theorem constrains a *given* parametric family;
  the benchmark existential is an instance-independent capability witness — see the
  paper's fidelity scope (`paper/main.tex`, §8).
- **Corollary D** *(arithmetic)* — `sweepCut = min(n, √n·d)`, reproducing the folklore
  `~10^18` / `~10^24` Sycamore figures.

Certified instance: the deep-regime wire-chain `53×53` spacetime grid (a calibration
instance whose only tie to Sycamore-53 is the shared cut value 53). The `(2+1)D` chip
lattice and the `pw = Θ(tw)` tree-order extension are future work
(`docs/publication-overview.md` §4).

## Layout

```
docs/spec.md                  full definitions, theorems, proof roadmap, sources
docs/publication-overview.md  honest status inventory
paper/                        CPP submission (main.tex) + Chinese companion (main-zh.tex)
experiment/                   cotengra comparison pipeline + raw JSON results
FieldStemProof.lean           root module (imports all 18 modules)
FieldStemProof/               17 proof modules + CheckAxioms.lean (build-time axiom audit)
scripts/package_artifact.sh   anonymized review-artifact packaging (renames the
                              Lean namespace to the paper's \sys name)
```

## Toolchain

Lean `v4.30.0`, Mathlib `v4.30.0` (managed by `elan`/`lake`). Build:

```
lake exe cache get   # fetch prebuilt Mathlib oleans (first time)
lake build           # also runs the axiom audit: the build fails if any cited
                     # theorem needs more than propext/Classical.choice/Quot.sound
```
