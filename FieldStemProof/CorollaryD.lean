/-
# Corollary D — reproducing the Sycamore complexity numbers (spec §3)

The stem (caterpillar) contraction path sweeps the circuit, and at each step its accumulated
tensor straddles the current cut; its cost is dominated by the widest cut. For a circuit on a
2D chip of `n` qubits run to depth `d`, the two sweep directions give cuts:

* **time sweep** (Schrödinger evolution): boundary = all `n` qubits → `2^n`;
* **space sweep**: boundary ≈ (chip linear size `√n`) × depth `d` → `2^{√n · d}`.

The optimal stem takes the smaller, so the contraction width is
`W = min(n, √n · d)` and the cost is `≈ 4 · 2^W · steps`.

This file is self-contained arithmetic + construction (no graph-theory dependency): it
*computes* `W` and the cost for the Sycamore parameters and bounds them between powers of ten,
reproducing the `~10^18` (Sycamore-53) and `~10^24` (Sycamore-70) figures. The identification
`W = treewidth` (so that this is the *optimal* cost, not just the stem's cost) is the content of
Theorem A; here we evaluate the stem cost directly from the cut.
-/
import Mathlib

namespace FieldStemProof.CorollaryD

/-- The stem sweep cut for an `n`-qubit chip at depth `d`: the smaller of the time-sweep
boundary `n` and the space-sweep boundary `⌊√n⌋ · d`. -/
def sweepCut (n d : ℕ) : ℕ := min n (Nat.sqrt n * d)

/-- The stem contraction cost: `4 · 2^cut · steps` (the `4` is the per-step contraction
constant for the rank-2 bond update; `steps` is the number of stem nodes). -/
def stemCost (n d steps : ℕ) : ℕ := 4 * 2 ^ sweepCut n d * steps

/-! ## Sycamore-53 (depth 20): cut = 53, cost ≈ 10^18 -/

/-- For Sycamore-53 the space-sweep boundary `⌊√53⌋·20 = 140` exceeds `n = 53`, so the optimal
stem sweeps in time and the cut is `53`. -/
theorem sweepCut_sycamore53 : sweepCut 53 20 = 53 := by
  rw [sweepCut]; norm_num [Nat.sqrt]

/-- With ~150 stem steps the Sycamore-53 contraction cost lands in `[10^18, 10^19)`,
i.e. on the order of `10^18`, matching Google's estimate. -/
theorem stemCost_sycamore53 :
    (10:ℕ) ^ 18 ≤ stemCost 53 20 150 ∧ stemCost 53 20 150 < (10:ℕ) ^ 19 := by
  rw [stemCost, sweepCut_sycamore53]
  constructor <;> norm_num

/-! ## Sycamore-70 (depth 24): cut = 70, cost ≈ 10^24 -/

/-- For Sycamore-70 the space-sweep boundary `⌊√70⌋·24 = 192` exceeds `n = 70`, so the cut is
`70`. -/
theorem sweepCut_sycamore70 : sweepCut 70 24 = 70 := by
  rw [sweepCut]; norm_num [Nat.sqrt]

/-- With ~200 stem steps the Sycamore-70 contraction cost lands in `[10^23, 10^24)`,
i.e. on the order of `10^24`, matching the published estimate. -/
theorem stemCost_sycamore70 :
    (10:ℕ) ^ 23 ≤ stemCost 70 24 200 ∧ stemCost 70 24 200 < (10:ℕ) ^ 24 := by
  rw [stemCost, sweepCut_sycamore70]
  constructor <;> norm_num

/-! ## The general min-structure: cut = min(n, √n·d), exponential in min(n, depth-bounded) -/

/-- The cut never exceeds the qubit count: the time sweep always caps the width at `n`,
so the cost is at most `4 · 2^n · steps` — the state-vector bound. -/
theorem sweepCut_le_qubits (n d : ℕ) : sweepCut n d ≤ n := min_le_left _ _

/-- The cut never exceeds the space-sweep boundary `√n · d`, so for shallow circuits
(`√n·d < n`, i.e. small depth) the width is controlled by the depth, not the qubit count —
the `min(n, d)`-type exponent of the conjecture. -/
theorem sweepCut_le_spaceBoundary (n d : ℕ) : sweepCut n d ≤ Nat.sqrt n * d := min_le_right _ _

end FieldStemProof.CorollaryD
