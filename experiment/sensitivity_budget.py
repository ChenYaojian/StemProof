#!/usr/bin/env python
"""Search-budget sensitivity for the drift instances (paper S8, limitation (7)).

Reruns the instances that drifted above the certified/stem scale at the original
128-repeat budget, at larger hyper-optimizer budgets, to separate "search quality
at a fixed budget" from "limit behavior of the search".

Usage:
  python sensitivity_budget.py grid  28,32,36,44,53      512  8 out.json
  python sensitivity_budget.py chip  2d_6x6_c16,2d_7x7_c12 4096 8 out.json

Results are appended to the output JSON incrementally (one entry per instance)
so partial runs are still usable.
"""
import json, sys, traceback

import grid_floor_experiment as grid
import rqc_stem_experiment as rqc


def parse_chip(tag):
    # "2d_{Lx}x{Ly}_c{cycles}"
    geo, cyc = tag[3:].split("_c")
    lx, ly = geo.split("x")
    return int(lx), int(ly), int(cyc)


def main():
    kind, instances, repeats, parallel, out = (
        sys.argv[1], sys.argv[2].split(","), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
    results = []

    def save():
        with open(out, "w") as f:
            json.dump(results, f, indent=1)

    for inst in instances:
        try:
            if kind == "grid":
                r = grid.run_one(int(inst), repeats, parallel)
            elif kind == "chip":
                lx, ly, c = parse_chip(inst)
                r = rqc.run_one(inst, rqc.gen_2d_rqc(lx, ly, c), repeats, parallel)
                r["max_repeats"] = repeats
            else:
                raise ValueError(f"unknown kind {kind!r}")
            r["kind"] = kind
            results.append(r)
            print(json.dumps(r), flush=True)
            save()
        except Exception:
            traceback.print_exc()
    save()


if __name__ == "__main__":
    main()
