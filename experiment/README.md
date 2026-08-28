# Certified-floor vs heuristic-search experiment

Compares the Lean-certified stem-width scale of the N x N grid family
(`grid_pathwidth_exact`: every stem order has bag size >= N+1; the sliding-window
sweep realizes bond-width N+1) against the contraction widths actually found by
cotengra's hyper-optimizer.

## Provenance

- Server: umi (Slurm), partition `debug`, job 181890, 8 CPUs / 16 GB, ~22 min total.
- Environment: `/home/cyj/anaconda3/envs/szq_tnc` (python 3.9), cotengra 0.7.1.
- Command: `python grid_floor_experiment.py 6,8,10,12,16,20,24,28,32,36,40,44,48,53 128 8`
  (128 hyper-optimizer repeats per instance, minimize="size").
- Instances: closed N x N grid tensor networks, all bond dimensions 2, built as raw
  einsum inputs (no quimb dependency); `found_width` = log2 of the largest
  intermediate tensor of the best found contraction tree.

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
- 1D depth sweep (n=24): tracks min(n, spatial cut); crossover at L~26; shallow
  entries at -2 measure the slack of the two canonical witnesses (optimal
  shallow stem is a spacetime staircase we do not enumerate).
- 2D ABCD chips (16-36 qubits): found EXCEEDS the trivial time-sweep stem by
  +2..+9 units (up to 2^9 ~ 500x tensor size at 6x6, 12 cycles): on
  supremacy-class architectures the searcher fails to FIND the stem.
