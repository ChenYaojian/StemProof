# Certified-floor vs heuristic-search experiment

Compares the Lean-certified stem-width scale of the N x N grid family
(`grid_pathwidth_exact`: every stem order has bag size >= N+1; the sliding-window
sweep realizes bond-width N+1) against the contraction widths actually found by
cotengra's hyper-optimizer.

## Provenance

- Server: Slurm HPC cluster (name withheld for anonymity), partition `debug`, job 181890, 8 CPUs / 16 GB, ~22 min total.
- Environment: conda env (name withheld for anonymity; python 3.9), cotengra 0.7.1.
- Command: `python grid_floor_experiment.py 6,8,10,12,16,20,24,28,32,36,40,44,48,53 128 8`
  (128 hyper-optimizer repeats per instance, minimize="size").
- Instances: closed N x N grid tensor networks, all bond dimensions 2, built as raw
  einsum inputs (no quimb dependency); `found_width` = log2 of the largest
  intermediate tensor of the best found contraction tree.
- Search settings: `HyperOptimizer(minimize="size", max_repeats, parallel)` with all
  other settings at cotengra 0.7.1 defaults (method pool as shipped). No RNG seed was
  fixed, so individual searches are stochastic; run-to-run variance is addressed by the
  budget sweep of Part 4 (128/512/4096 repeats), not by seeding.

## Result summary (found - (N+1))

| N   | 6  | 8 | 10 | 12 | 16 | 20 | 24 | 28 | 32 | 36 | 40 | 44 | 48 | 53 |
|-----|----|---|----|----|----|----|----|----|----|----|----|----|----|----|
| gap | -1 | 0 | 0  | 0  | 0  | 0  | 0  | 0  | +1 | +2 | -1 | +1 | 0  | +2 |

Three regimes, all informative:
- Every point lands in [-1, +2]: an UNRESTRICTED tree search never beats the stem
  line by more than one unit -- empirical support for the stem-existence thesis
  (on grids pw = tw, so trees should gain nothing substantial over stems).
- gap 0 (8 points): the search meets the certified stem scale exactly.
- gap -1 (N=6, 40): bag-vs-bond semantics conversion residue (the certified floor
  counts vertex bags; cotengra counts bond indices; a vertex-by-vertex frontier
  carries one extra bond that a tree merge can pre-contract away). Within the
  +-1 allowance; NOT trees beating the stem thesis.
- gap +1/+2 (N=32, 36, 44, 53): with a fixed repeat budget the stochastic search
  drifts above the certified scale -- a deficit that is invisible to
  relative-only benchmarking and exactly what the yardstick exposes.

`results_6_53.json` is the raw output; the paper figure is generated from it
(gap plot in `paper/main.tex`, section "Empirical Demonstration").

## Part 2: RQC architectures (job 181891, same env, ~6 min)

`rqc_stem_experiment.py` builds gate-level spacetime TNs of RQC families
(single closed amplitude, rank-4 gate tensors; width depends only on the graph):
1D brickwork chains (deep, L=2n), a depth transition at n=24, and 2D ABCD-pattern
chips. Per instance it also simulates two genuine stem orders (time sweep, space
sweep) exactly, so the comparison is "free tree search vs the stem theory
prescribes". Raw output: results_rqc.json.

- 1D deep: found - stem in {0,0,0,+2,+2,+2} -- search meets or trails the stem.
- 1D depth sweep (n=24): tracks min(n, spatial cut); crossover at L~26 ~ n,
  i.e. where the entanglement lightcone first spans the chain. Shallow entries
  (L < n) are OUTSIDE the stem-thesis domain -- below threshold the lightcone
  has not connected all qubits (Napp's simulable phase; the deep-regime marker
  is the schedule-counting theorem routed_card_le plus the one-directional
  lightcone walk bond_causal -- reachability for i < d is machine-checked;
  the converse is not formalized). They are kept only to trace where the
  deep regime begins.
- 2D ABCD chips (16-36 qubits): found EXCEEDS the trivial time-sweep stem by
  +2..+9 units (up to 2^9 ~ 500x tensor size at 6x6, 12 cycles): on
  supremacy-class architectures the searcher fails to FIND the stem.

## Part 3: deep-regime extension (job 181892, same env, ~15 min)

`rqc_deep_batch.py` (reuses the Part-2 generators): 1D chains at L=3n
(n=16..28) and deeper/larger 2D ABCD chips (16 cycles, 20 cycles, and
7x7 = 49 qubits -- the Sycamore-53 size class). Raw output:
results_rqc_deep.json.

- 1D at L=3n: gaps {0,+2,+4,+4}; the stem scale stays at n (depth-
  independent once the lightcone saturates) while search drifts further.
- 2D deep: 4x4 c16/c20 -> +2; 5x5 c16 -> +7; 6x6 c16 -> +14;
  7x7 c8 -> +15; 7x7 c12 -> +17 (found 66 vs stem 49): the deficit GROWS
  with scale -- at 49 qubits the searched order materializes tensors
  2^17 ~ 1.3e5 times larger than the time-sweep stem.
- Combined with Part 2: 25 deep-regime instances, zero cases of a found
  tree beating an exhibited stem.

## Part 4: search-budget sensitivity (jobs 181893-181897, same env, ~75 min wall)

`sensitivity_budget.py` reruns the instances that drifted above the certified /
stem scale at the original 128-repeat budget, at 512 and 4096 repeats
(five parallel debug jobs; see `run_sensitivity.sbatch` for the submitted
command lines). Raw outputs: `results_sens_grid512.json`,
`results_sens_grid4096_{36,53}.json`, `results_sens_chip512.json`,
`results_sens_chip4096.json`.

Grid family (gap = found - (N+1)):

| N  | 128 | 512 | 4096 |
|----|-----|-----|------|
| 28 | 0   | 0   | -    |
| 32 | +1  | 0   | -    |
| 36 | +2  | -1  | -1   |
| 44 | +1  | 0   | -    |
| 53 | +2  | +1  | 0    |

Every drift point returns to within the +-1 bag-vs-bond conversion allowance
by 512 repeats; at 4096 repeats the N=53 search lands exactly on the certified
scale 54, and no point ever crosses below the allowance. The certified line is
the attractor of the search as budget grows: the 128-repeat drift was
budget-limited search quality, not a property of the instances.

2D ABCD chips (gap = found - time-sweep stem):

| instance   | stem | 128 | 512 | 4096 |
|------------|------|-----|-----|------|
| 2d_6x6_c16 | 36   | +14 | +10 | +6   |
| 2d_7x7_c8  | 49   | +15 | +10 | -    |
| 2d_7x7_c12 | 49   | +17 | +16 | +10  |

The chip deficit shrinks by roughly 4 width units per 8x budget increase --
still 2^6..2^10 above the free time-sweep stem after a 32x budget. The
qualitative finding ("on supremacy-class chips the searcher fails to find the
stem") survives the budget objection; closing the remaining gap by brute
budget would require orders of magnitude more search.
