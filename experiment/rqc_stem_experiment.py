#!/usr/bin/env python
"""RQC architectures: unrestricted tree search vs per-instance stem sweeps.

Builds gate-level spacetime tensor networks of random-quantum-circuit
architectures (single closed amplitude <x|C|0>, all bond dims 2):
  - 1D chain brickwork, n qubits, L gate layers;
  - 2D chip with the Sycamore-style ABCD coupler pattern, Lx x Ly qubits,
    c cycles (4 gate layers per cycle).
For each instance:
  - run cotengra HyperOptimizer (minimize=size) -> best found tree width;
  - simulate two genuine STEM (linear) orders and compute their exact widths:
      time sweep  (absorb tensors layer by layer),
      space sweep (absorb tensors qubit-column by qubit-column);
  - gap := found_width - min(stem widths).
The stem thesis predicts gap in a small band around 0 (trees gain nothing
substantial over stems on lattice architectures).
"""
import json, math, sys, time, traceback

class TN:
    def __init__(self):
        self.inputs = []   # list of tuples of bond ids
        self.meta = []     # (kind, layer, pos) per tensor, for sweep orders
        self.nbonds = 0
    def new_bond(self):
        b = self.nbonds; self.nbonds += 1; return b
    def add(self, bonds, kind, layer, pos):
        self.inputs.append(tuple(bonds)); self.meta.append((kind, layer, pos))

def gen_1d_rqc(n, layers):
    """Brickwork on a chain: layer t applies gates on pairs (i,i+1), i parity t%2."""
    tn = TN()
    wire = [tn.new_bond() for _ in range(n)]
    for q in range(n):
        tn.add([wire[q]], "cap", 0, q)          # |0> caps
    for t in range(1, layers + 1):
        start = (t - 1) % 2
        for i in range(start, n - 1, 2):
            a, b = tn.new_bond(), tn.new_bond()
            tn.add([wire[i], wire[i+1], a, b], "gate", t, i)
            wire[i], wire[i+1] = a, b
    for q in range(n):
        tn.add([wire[q]], "cap", layers + 1, q) # <x| caps
    return tn

ABCD = {  # coupler direction per layer within a cycle: (di, dj, parity_axis)
    0: (0, 1, 0),  # A: horizontal, even columns
    1: (0, 1, 1),  # B: horizontal, odd columns
    2: (1, 0, 0),  # C: vertical, even rows
    3: (1, 0, 1),  # D: vertical, odd rows
}

def gen_2d_rqc(Lx, Ly, cycles):
    """2D chip, ABCD pattern, one 2q-gate layer per pattern step."""
    tn = TN()
    wire = {}
    for i in range(Lx):
        for j in range(Ly):
            wire[(i, j)] = tn.new_bond()
            tn.add([wire[(i, j)]], "cap", 0, j * Lx + i)
    t = 0
    for c in range(cycles):
        for step in range(4):
            t += 1
            di, dj, par = ABCD[step]
            for i in range(Lx):
                for j in range(Ly):
                    i2, j2 = i + di, j + dj
                    if i2 >= Lx or j2 >= Ly:
                        continue
                    if (dj == 1 and j % 2 != par) or (di == 1 and i % 2 != par):
                        continue
                    a, b = tn.new_bond(), tn.new_bond()
                    tn.add([wire[(i, j)], wire[(i2, j2)], a, b], "gate", t, j * Lx + i)
                    wire[(i, j)], wire[(i2, j2)] = a, b
    for i in range(Lx):
        for j in range(Ly):
            tn.add([wire[(i, j)]], "cap", t + 1, j * Lx + i)
    return tn

def linear_width(tn, order):
    """Exact bond-width of the linear (stem) absorption order: max open bonds."""
    first, last = {}, {}
    for step, ti in enumerate(order):
        for b in tn.inputs[ti]:
            if b not in first: first[b] = step
            last[b] = step
    open_now, best = 0, 0
    delta = [0] * (len(order) + 1)
    for b in first:
        delta[first[b]] += 1
        delta[last[b]] -= 1
    for step in range(len(order)):
        open_now += delta[step]
        best = max(best, open_now)
    return best

def stem_widths(tn):
    idx = list(range(len(tn.inputs)))
    time_order = sorted(idx, key=lambda i: (tn.meta[i][1], tn.meta[i][2]))
    space_order = sorted(idx, key=lambda i: (tn.meta[i][2], tn.meta[i][1]))
    return linear_width(tn, time_order), linear_width(tn, space_order)

def run_one(tag, tn, max_repeats, parallel):
    import cotengra as ctg
    size_dict = {b: 2 for b in range(tn.nbonds)}
    opt = ctg.HyperOptimizer(minimize="size", max_repeats=max_repeats,
                             parallel=parallel, progbar=False)
    t0 = time.time()
    tree = opt.search(tn.inputs, (), size_dict)
    dt = time.time() - t0
    tw_time, tw_space = stem_widths(tn)
    found = float(tree.contraction_width())
    best_stem = min(tw_time, tw_space)
    return {"instance": tag, "num_tensors": len(tn.inputs),
            "found_width": found, "stem_time": tw_time, "stem_space": tw_space,
            "best_stem": best_stem, "gap": found - best_stem,
            "seconds": round(dt, 2)}

def main():
    max_repeats = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    parallel = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    jobs = []
    for n in [8, 12, 16, 20, 24, 28]:                    # 1D deep regime
        jobs.append((f"1d_n{n}_L{2*n}", gen_1d_rqc(n, 2 * n)))
    for L in [6, 10, 14, 18, 22, 26, 30, 38, 46]:        # 1D depth transition, n=24
        jobs.append((f"1d_n24_L{L}", gen_1d_rqc(24, L)))
    for (Lx, Ly, c) in [(4, 4, 8), (5, 5, 8), (6, 6, 8), (5, 5, 12), (6, 6, 12)]:
        jobs.append((f"2d_{Lx}x{Ly}_c{c}", gen_2d_rqc(Lx, Ly, c)))  # 2D chip ABCD
    results = []
    for tag, tn in jobs:
        try:
            r = run_one(tag, tn, max_repeats, parallel)
            results.append(r)
            print(json.dumps(r), flush=True)
        except Exception:
            traceback.print_exc()
    with open("results_rqc.json", "w") as f:
        json.dump(results, f, indent=1)

if __name__ == "__main__":
    main()
