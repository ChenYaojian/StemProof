#!/usr/bin/env python
"""Certified-floor vs heuristic-search experiment (paper section: Empirical Demonstration).

For each N in NS, build the closed N x N grid tensor network (all bond dims 2),
run cotengra hyper-optimization minimizing intermediate size, and record the best
found contraction width W = log2(largest intermediate) and total cost estimate.
The certified stem-order floor from the Lean development is bag size N+1
(grid_pathwidth_exact), whose sliding-window sweep realizes bond-width N+1 exactly.
"""
import json, sys, time, traceback

def grid_inputs(N):
    idx = {}
    def bond(name):
        if name not in idx:
            idx[name] = len(idx)
        return idx[name]
    inputs = []
    for i in range(N):
        for j in range(N):
            term = []
            if j + 1 < N: term.append(bond(("h", i, j)))
            if j - 1 >= 0: term.append(bond(("h", i, j - 1)))
            if i + 1 < N: term.append(bond(("v", i, j)))
            if i - 1 >= 0: term.append(bond(("v", i - 1, j)))
            inputs.append(tuple(term))
    size_dict = {k: 2 for k in range(len(idx))}
    return inputs, size_dict

def run_one(N, max_repeats, parallel):
    import cotengra as ctg
    inputs, size_dict = grid_inputs(N)
    output = ()
    opt = ctg.HyperOptimizer(minimize="size", max_repeats=max_repeats,
                             parallel=parallel, progbar=False)
    t0 = time.time()
    tree = opt.search(inputs, output, size_dict)
    dt = time.time() - t0
    return {
        "N": N,
        "num_tensors": len(inputs),
        "found_width": float(tree.contraction_width()),   # log2(largest intermediate)
        "found_cost_log10": float(tree.contraction_cost()and __import__("math").log10(tree.contraction_cost())),
        "certified_floor_bag": N + 1,
        "max_repeats": max_repeats,
        "seconds": round(dt, 2),
    }

def main():
    NS = [int(x) for x in sys.argv[1].split(",")] if len(sys.argv) > 1 else [6, 8]
    max_repeats = int(sys.argv[2]) if len(sys.argv) > 2 else 32
    parallel = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    import cotengra
    results = {"cotengra_version": getattr(cotengra, "__version__", "unknown"),
               "runs": []}
    for N in NS:
        try:
            r = run_one(N, max_repeats, parallel)
            results["runs"].append(r)
            print(json.dumps(r), flush=True)
        except Exception:
            traceback.print_exc()
    with open(f"results_{NS[0]}_{NS[-1]}.json", "w") as f:
        json.dump(results, f, indent=1)

if __name__ == "__main__":
    main()
