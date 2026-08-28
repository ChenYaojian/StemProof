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
- gap 0 (8 points): the search meets the certified stem scale exactly.
- gap -1 (N=6, 40): tree orders legitimately undercut the stem line by one unit
  (nested dissection vs sweep) -- the pw-vs-tw distinction made empirically visible;
  no contradiction, the unconditional floor quantifies over stem orders in
  vertex-bag semantics.
- gap +1/+2 (N=32, 36, 44, 53): with a fixed repeat budget the stochastic search
  drifts above the certified scale -- a deficit that is invisible to
  relative-only benchmarking and exactly what the yardstick exposes.

`results_6_53.json` is the raw output; the paper figure is generated from it
(gap plot in `paper/main.tex`, section "Empirical Demonstration").
