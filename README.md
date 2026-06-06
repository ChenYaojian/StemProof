# fieldStemProof

Formalizing, in Lean 4 + Mathlib, a **stem-structure lower bound** for contracting the
tensor networks of **random quantum circuits**.

## Claim (layered — see `docs/spec.md`)

For a random quantum circuit on a **(2+1)D = 3D spacetime lattice** (e.g. Sycamore), with
`G = L(TN(C))`:

- **Theorem A** *(low / assembly)* — there exists a stem (caterpillar) contraction path
  achieving `width = pw(G) = Θ(tw(G)) = cc(G)`, i.e. an optimal stem exists.
- **Lemma B** *(medium / original core, first formalization goal)* — for generic gate
  parameters, intermediate tensors stay full-rank, so `Θ(2^{tw}) · steps` is a tight
  lower bound for the contraction method (no rank collapse).
- **Conjecture C** *(hard / open frontier)* — the average-case, above-threshold version;
  the Napp et al. phase transition is a 2D-shallow phenomenon that the 3D deep bulk escapes.
- **Corollary D** — `tw(G) = min(n, √n·d)`-type, reproducing Sycamore `~10^18` / `~10^24`.

## Layout

```
docs/spec.md                  full definitions, theorems, proof roadmap, sources
FieldStemProof.lean           root module
FieldStemProof/Defs.lean      definitions layer (spec §1)
FieldStemProof/TheoremA.lean  existence of optimal stem (spec §3)
FieldStemProof/LemmaB.lean    generic full-rank tightness (spec §3) — first target
```

## Toolchain

Lean `v4.30.0`, Mathlib `v4.30.0` (managed by `elan`/`lake`). Build:

```
lake exe cache get   # fetch prebuilt Mathlib oleans (first time)
lake build
```
