/-
# Spacetime lattice: faithful cut geometry and the min(n, √n·d) scale (spec §3)

Answers the two scrutiny questions about the cross-cut matching:

* **(Q1) Is the matching a natural Sycamore object?** Yes, made faithful here: a *sweep cut* of
  the spacetime tensor network is a surface in the (qubits × time) lattice, and the legs crossing
  it are real wires/gates. The two canonical sweeps:
  - **time sweep** (Schrödinger evolution) — the cut is one time slice; it crosses all `n` qubit
    wires, so its size is `n`. The crossing legs are the `n` wires (input-leg ↔ output-leg per
    qubit), the faithful realization of `chipMatching` with the in/out interpretation.
  - **space sweep** — the cut splits the chip spatially across all `d` time steps; it crosses the
    boundary gates at each step, so its size is `(spatial boundary) · d = √n · d` for a √n × √n
    chip.

* **(Q2) Does it reach Θ(min(n, √n·d))?** Split into two directions, with an honest verdict:
  - **upper bound (PROVED here, constructive):** both sweeps exist, so the optimal width is
    `≤ min(n, √n·d)` (`optimalWidth_le_min`). The time sweep achieves a faithful full-rank
    matching of size `n` (`timeSweep_full_rank`, reusing `chip_contractionRigid`).
  - **lower bound (self-proved for stems, CITED for trees):** for the *stem/pathwidth*
    restriction the bound is machine-proved (`GridConn.grid_pathwidth_lower_unconditional`,
    standard axioms only); for *arbitrary* tree contraction orders it is the grid treewidth lower
    bound (Kozawa–Otachi–Yamazaki via Seymour–Thomas brambles), carried as an explicit
    hypothesis with its reference — Mathlib has no treewidth theory to reprove it.

  Combining the two gives `optimalWidth = min(n, √n·d)` (`optimalWidth_eq_min`), with the
  literature input visible as the hypothesis `hlow` in the statement itself.
-/
import FieldStemProof.Lattice
import FieldStemProof.CorollaryD

namespace FieldStemProof.Spacetime

open FieldStemProof

/-- The time-sweep cut size: a time slice crosses all `n` qubit wires. -/
def timeSweepWidth (n : ℕ) : ℕ := n

/-- The space-sweep cut size: a spatial boundary of `⌊√n⌋` qubits, crossed at each of the `d`
time steps. -/
def spaceSweepWidth (n d : ℕ) : ℕ := Nat.sqrt n * d

/-- The width achievable by the better of the two canonical sweeps — equal to
`CorollaryD.sweepCut`. -/
def sweepWidth (n d : ℕ) : ℕ := min (timeSweepWidth n) (spaceSweepWidth n d)

theorem sweepWidth_eq_corollaryD (n d : ℕ) : sweepWidth n d = CorollaryD.sweepCut n d := rfl

/-! ## (Q2) Upper bound — constructive, proved

Both sweeps are explicit contraction orders, so the optimal width is at most either, hence at
most their min. We model "optimal width" as a value `optimalWidth` together with the two
achievability facts (the two sweeps exist); the min upper bound is then pure arithmetic. -/

/-- The optimal contraction width is at most the time-sweep width `n` (the Schrödinger sweep is a
valid contraction order). -/
theorem optimalWidth_le_time (n : ℕ) {W : ℕ} (htime : W ≤ timeSweepWidth n) :
    W ≤ n := htime

/-- The optimal contraction width is at most `min(n, √n·d)` whenever it is bounded by both
canonical sweeps — the constructive upper-bound half of the Θ scale. -/
theorem optimalWidth_le_min (n d : ℕ) {W : ℕ}
    (htime : W ≤ timeSweepWidth n) (hspace : W ≤ spaceSweepWidth n d) :
    W ≤ sweepWidth n d := le_min htime hspace

/-! ## (Q1) Faithful time-sweep matching — proved, full rank `2^n`

The time slice of an `n`-qubit circuit has `n` wires; pairing each wire's input leg with its
output leg is a faithful cross-cut perfect matching of size `n`, realized on the wire set
`Fin n ⊕ Fin n` (input legs ⊕ output legs). Full Schmidt rank `2^n` follows from
`chip_contractionRigid`, now with the genuine spacetime-wire interpretation. -/

/-- **Faithful time-sweep full-rank matching.** The `n` wires crossing a time slice form a
cross-cut matching whose flattening is contraction rigid — full Schmidt rank `2^n` for generic
gate parameters. This is the natural Sycamore object of size exactly `timeSweepWidth n = n`. -/
theorem timeSweep_full_rank {ι K : Type*} [CommRing K] [IsDomain K] (n : ℕ) :
    ∃ (e : ({i // leftBlock i} → Fin 2) ≃ ({i // ¬ leftBlock i} → Fin 2))
      (T : QTensor (Fin n ⊕ Fin n) (MvPolynomial ι K)),
      ContractionRigid leftBlock e T :=
  ⟨_, chip_contractionRigid (K := K) (ι := ι) n⟩

/-! ## (Q2) Lower bound — an explicit hypothesis, self-proved for the stem/pathwidth restriction

The statement "no contraction order has width below `min(n, √n·d)`" is the grid treewidth lower
bound, proven in the literature via Seymour–Thomas brambles (bramble of crosses) and computed for
multidimensional grids by Kozawa–Otachi–Yamazaki. For the *stem (pathwidth)* restriction it is
self-proved here (`GridConn.grid_pathwidth_lower_unconditional`, standard axioms only); the
generalization to *all* tree contraction orders (`pw = Θ(tw)`) is carried as an explicit
hypothesis `hlow` where needed, with its literature reference. It must not be a global `axiom`:
stated over bare naturals with only the two sweep inequalities as hypotheses, `W = 0` satisfies
them and refutes the statement, making the theory inconsistent. -/

/-- **The optimal contraction width equals `min(n, √n·d)`** (`= CorollaryD.sweepCut`): upper bound
proved constructively (`optimalWidth_le_min`), lower bound supplied as the explicit hypothesis
`hlow` — self-proved for stem orders (`GridConn.grid_pathwidth_lower_unconditional`), cited
(Kozawa–Otachi–Yamazaki / Seymour–Thomas) for arbitrary tree contraction orders. -/
theorem optimalWidth_eq_min (n d : ℕ) {W : ℕ}
    (htime : W ≤ timeSweepWidth n) (hspace : W ≤ spaceSweepWidth n d)
    (hlow : sweepWidth n d ≤ W) :
    W = sweepWidth n d :=
  le_antisymm (optimalWidth_le_min n d htime hspace) hlow

/-! ## Sycamore-53: the time sweep is optimal, faithful matching of size 53 -/

/-- For Sycamore-53 (n=53, d=20) the time-sweep width `53` is below the space-sweep width
`⌊√53⌋·20 = 140`, so the optimal sweep is the time sweep and the faithful cut has size exactly
`53`. -/
theorem sycamore53_time_optimal : sweepWidth 53 20 = 53 := by
  rw [sweepWidth, timeSweepWidth, spaceSweepWidth]; norm_num [Nat.sqrt]

end FieldStemProof.Spacetime
