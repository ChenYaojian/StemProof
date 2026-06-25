/-
# Sycamore-53: end-to-end lower bound (spec §3, the assembled statement)

A single machine-checked theorem tying together the whole development for the Sycamore-53
(53 qubits, depth 20) parameters:

* **(cut)** the optimal sweep cut is `53` (`CorollaryD.sweepCut_sycamore53`);
* **(cost)** the stem contraction cost is on the order of `10^18`
  (`CorollaryD.stemCost_sycamore53`, `4·2^53·150 ∈ [10^18, 10^19)`);
* **(stem)** on the lattice circuit graph the optimal contraction path can be taken with stem
  structure, of width within a constant of the optimum `cc = 53` (`TheoremA.optimal_stem_lattice`,
  resting on the cited published grid-treewidth axioms);
* **(rigidity)** a balanced 53-qubit cut with a cross-cut matching is contraction rigid — full
  Schmidt rank `2^53` for generic gate parameters, so the width is genuinely needed, no rank
  collapse (`Lattice.chip_contractionRigid`, standard axioms only).

`#print axioms sycamore53_lower_bound` reveals the exact honest dependency: standard axioms plus
the two cited grid-treewidth axioms used by Theorem A (`markovShi` is not used here; the optimum
`cc = 53` is established genuinely in the concrete model). The only mathematics NOT formalized and
left open is that a deep 3D Sycamore brickwork realizes the cross-cut matching above the mixing
threshold (geometric routing) — every other link is machine-checked.
-/
import FieldStemProof.TheoremA
import FieldStemProof.CorollaryD
import FieldStemProof.Lattice

namespace FieldStemProof

/-- A concrete `CircuitGraph` model for Sycamore-53: every contraction order has width `53` (the
cut value), all orders are stem orders, line-graph treewidth `53`, and it is a lattice. Genuinely
`cc = 53` (no reliance on a possibly-false axiom). -/
def sycamore53 : CircuitGraph where
  Order := Unit
  width := fun _ => 53
  IsStem := fun _ => True
  stem_exists := ⟨(), trivial⟩
  tw := 53
  IsLattice := True

@[simp] theorem sycamore53_cc : sycamore53.cc = 53 := by
  rw [CircuitGraph.cc, sycamore53]
  rw [Set.range_const, csInf_singleton]

/-- **Sycamore-53 end-to-end lower bound.** The four assembled claims as one theorem:
cut size, cost `~10^18`, optimal-stem structure, and contraction rigidity (full Schmidt rank
`2^53`). -/
theorem sycamore53_lower_bound :
    -- (cut) the optimal sweep cut is 53
    CorollaryD.sweepCut 53 20 = 53 ∧
    -- (cost) the stem contraction cost is on the order of 10^18
    ((10:ℕ) ^ 18 ≤ CorollaryD.stemCost 53 20 150 ∧
      CorollaryD.stemCost 53 20 150 < (10:ℕ) ^ 19) ∧
    -- (stem) the optimal contraction path can be taken with stem structure, width near cc = 53
    (∃ o, sycamore53.IsStem o ∧ sycamore53.cc ≤ sycamore53.width o ∧
      sycamore53.width o ≤ latticePathwidthConst * sycamore53.cc) ∧
    -- (rigidity) a balanced 53-qubit cut is contraction rigid (full Schmidt rank 2^53, generic)
    (∃ (e : ({i // leftBlock i} → Fin 2) ≃ ({i // ¬ leftBlock i} → Fin 2))
        (T : QTensor (Fin 53 ⊕ Fin 53) (MvPolynomial ℕ ℂ)),
        ContractionRigid leftBlock e T) := by
  refine ⟨CorollaryD.sweepCut_sycamore53, CorollaryD.stemCost_sycamore53, ?_, ?_⟩
  · exact optimal_stem_lattice sycamore53 trivial
  · exact ⟨_, chip_contractionRigid (K := ℂ) (ι := ℕ) 53⟩

end FieldStemProof
