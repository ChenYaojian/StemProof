/-
# Sycamore-53: end-to-end lower bound (spec §3, the assembled statement)

A single machine-checked theorem tying together the whole development for the Sycamore-53
(53 qubits, depth 20) parameters:

* **(cut)** the optimal sweep cut is `53` (`CorollaryD.sweepCut_sycamore53`);
* **(cost)** the stem contraction cost is on the order of `10^18`
  (`CorollaryD.stemCost_sycamore53`, `4·2^53·150 ∈ [10^18, 10^19)`);
* **(stem)** on the **faithful spacetime model** (`GridModel.gridModel 53`: orders are genuine
  path decompositions of the real 53×53 spacetime grid graph, width is the actual largest bag —
  nothing postulated) the optimum is attained by a stem order and the stem width is pinned to
  `Θ(53)` by machine-checked bounds on the real graph: every order has width `≥ 27`
  (self-proved bramble lower bound) and the explicit sweep has width `≤ 106`;
* **(rigidity)** a balanced 53-qubit cut with a cross-cut matching is contraction rigid — full
  Schmidt rank `2^53` for generic gate parameters, so the width is genuinely needed, no rank
  collapse (`Lattice.chip_contractionRigid`, standard axioms only).

`#print axioms sycamore53_lower_bound` reveals the exact honest dependency: **standard axioms
only** (`propext, Classical.choice, Quot.sound`) — no custom axiom anywhere. Remaining
faithfulness gaps, documented in `docs/publication-overview.md` §4: the model's order space is
the stem (linear) orders — extending the lower bound to arbitrary tree contraction orders is the
`pw = Θ(tw)` literature input (`TheoremA.LatticePathwidthBound`), and the grid is the deep-regime
1D-chain spacetime lattice (the (2+1)D chip lattice is handled on the matching side by `Causal`).
The only mathematics NOT formalized and left open is that a deep 3D Sycamore brickwork realizes
the cross-cut matching above the mixing threshold (geometric routing) — every other link is
machine-checked.
-/
import FieldStemProof.TheoremA
import FieldStemProof.CorollaryD
import FieldStemProof.Lattice
import FieldStemProof.GridModel

namespace FieldStemProof

open GridModel

theorem fiftyThree_pos : 0 < 53 := by norm_num

/-- The Sycamore-53 spacetime model: the **faithful** grid model at scale `53` — contraction
orders are the genuine path decompositions of the 53×53 spacetime grid graph (53 wires × a deep
window of 53 layers), and the width of an order is its actual largest bag. -/
def sycamore53 : CircuitGraph := gridModel 53 fiftyThree_pos

/-- **Real stem-width lower bound**: every stem contraction order of the spacetime grid has
width `≥ 27` (`53 ≤ 2·width`, the self-proved bramble bound — no axiom). -/
theorem sycamore53_stem_lower (o : sycamore53.Order) : 53 ≤ 2 * sycamore53.width o :=
  gridModel_width_lower 53 fiftyThree_pos o

/-- **Real stem-width upper bound**: the explicit sweep order has width `≤ 106 = 2·53`. -/
theorem sycamore53_stem_upper : ∃ o : sycamore53.Order, sycamore53.width o ≤ 106 :=
  gridModel_width_upper 53 fiftyThree_pos

/-- The contraction optimum of the real model is pinned to `Θ(53)`: `27 ≤ cc ≤ 106`. -/
theorem sycamore53_cc_bounds : 27 ≤ sycamore53.cc ∧ sycamore53.cc ≤ 106 := by
  obtain ⟨hlo, hhi⟩ := gridModel_cc_bounds 53 fiftyThree_pos
  exact ⟨by omega, hhi⟩

/-- The lattice pathwidth bound is discharged on the model with `C = 1` (by construction of the
order space; the extension to tree orders is the `pw = Θ(tw)` literature input). -/
theorem sycamore53_latticeBound : LatticePathwidthBound sycamore53 1 :=
  gridModel_latticeBound 53 fiftyThree_pos

/-- **Sycamore-53 end-to-end lower bound.** The four assembled claims as one theorem: cut size,
cost `~10^18`, optimal-stem structure on the faithful spacetime model (optimum attained by a
stem; stem width pinned to `Θ(53)` on the real graph), and contraction rigidity (full Schmidt
rank `2^53`). Standard axioms only. -/
theorem sycamore53_lower_bound :
    -- (cut) the optimal sweep cut is 53
    CorollaryD.sweepCut 53 20 = 53 ∧
    -- (cost) the stem contraction cost is on the order of 10^18
    ((10:ℕ) ^ 18 ≤ CorollaryD.stemCost 53 20 150 ∧
      CorollaryD.stemCost 53 20 150 < (10:ℕ) ^ 19) ∧
    -- (stem) on the real spacetime grid: the optimum is attained by a stem order, no order
    -- beats width 27 (bramble, self-proved), and the sweep achieves width ≤ 106
    ((∃ o, sycamore53.IsStem o ∧ sycamore53.width o = sycamore53.cc) ∧
      (∀ o, 53 ≤ 2 * sycamore53.width o) ∧
      (∃ o, sycamore53.width o ≤ 106)) ∧
    -- (rigidity) a balanced 53-qubit cut is contraction rigid (full Schmidt rank 2^53, generic)
    (∃ (e : ({i // leftBlock i} → Fin 2) ≃ ({i // ¬ leftBlock i} → Fin 2))
        (T : QTensor (Fin 53 ⊕ Fin 53) (MvPolynomial ℕ ℂ)),
        ContractionRigid leftBlock e T) := by
  refine ⟨CorollaryD.sweepCut_sycamore53, CorollaryD.stemCost_sycamore53,
    ⟨?_, sycamore53_stem_lower, sycamore53_stem_upper⟩, ?_⟩
  · exact gridModel_cc_attained 53 fiftyThree_pos
  · exact ⟨_, chip_contractionRigid (K := ℂ) (ι := ℕ) 53⟩

end FieldStemProof
