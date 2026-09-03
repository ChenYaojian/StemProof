/-
# Build-time axiom audit for the paper-cited theorems

The paper claims every cited theorem depends on standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`). This module makes that claim a
build-time assertion: it collects the axiom dependencies of each cited theorem
and *fails the build* if any set is not contained in the allowed list. The
module is imported by the library root, so `lake build` cannot succeed while
the claim is false.
-/
import FieldStemProof.Sycamore
import FieldStemProof.Causal

open Lean

namespace FieldStemProof.CheckAxioms

/-- The standard axioms the certificate is allowed to depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Every theorem cited in the paper (see the artifact appendix's
paper-to-artifact map). Double-backquoted, so a renamed or deleted theorem
already fails elaboration here. -/
def citedTheorems : List Name := [
  -- §3 the formal framework
  ``FieldStemProof.flatten_map,
  -- §5 stem width via interval Helly
  ``FieldStemProof.Bramble.interval_helly,
  ``FieldStemProof.Bramble.bag_meets_betweenness,
  ``FieldStemProof.Bramble.pathwidth_ge_order_of_touching,
  ``FieldStemProof.GridConn.grid_pathwidth_lower_unconditional,
  -- §6 the exact floor
  ``FieldStemProof.GridExact.grid_pathwidth_exact,
  -- §7 the faithful model
  ``FieldStemProof.GridModel.gridModel_cc_eq,
  ``FieldStemProof.GridModel.gridModel_cost_floor,
  -- §4 contraction rigidity and no-compression
  ``FieldStemProof.contraction_rigidity,
  ``FieldStemProof.ContractionRigid.no_compression,
  ``FieldStemProof.Matching.det_bondProd_ne_zero,
  -- §9 routing scaffolding
  ``FieldStemProof.Brickwork.Schedule.routed_card_le,
  ``FieldStemProof.Brickwork.exists_schedule_routed_card,
  ``FieldStemProof.Causal.bond_causal,
  -- §8 end-to-end certificate and companions
  ``FieldStemProof.CorollaryD.sweepCut_sycamore53,
  ``FieldStemProof.CorollaryD.stemCost_sycamore53,
  ``FieldStemProof.sycamore53_cc_exact,
  ``FieldStemProof.sycamore53_cost_floor,
  ``FieldStemProof.sycamore53_bond_floor,
  ``FieldStemProof.sycamore53_lower_bound]

run_cmd do
  for n in citedTheorems do
    let axs ← collectAxioms n
    for ax in axs do
      unless allowedAxioms.contains ax do
        throwError "axiom audit FAILED: {n} depends on non-standard axiom {ax}"
  logInfo m!"axiom audit passed: {citedTheorems.length} cited theorems depend only on {allowedAxioms}"

end FieldStemProof.CheckAxioms
