#!/usr/bin/env python
"""Deep-regime extension batch: larger/deeper RQC architectures only."""
import json, traceback
import rqc_stem_experiment as base

def main():
    jobs = []
    for n in [16, 20, 24, 28]:                          # 1D, L = 3n (very deep)
        jobs.append((f"1d_n{n}_L{3*n}", base.gen_1d_rqc(n, 3 * n)))
    for (Lx, Ly, c) in [(4, 4, 16), (5, 5, 16), (6, 6, 16), (4, 4, 20),
                        (7, 7, 8), (7, 7, 12)]:          # 2D, deeper + 49 qubits
        jobs.append((f"2d_{Lx}x{Ly}_c{c}", base.gen_2d_rqc(Lx, Ly, c)))
    results = []
    for tag, tn in jobs:
        try:
            r = base.run_one(tag, tn, 128, 8)
            results.append(r)
            print(json.dumps(r), flush=True)
        except Exception:
            traceback.print_exc()
    with open("results_rqc_deep.json", "w") as f:
        json.dump(results, f, indent=1)

if __name__ == "__main__":
    main()
