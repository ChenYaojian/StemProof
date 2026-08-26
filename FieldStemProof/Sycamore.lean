/-
# Sycamore-53: end-to-end lower bound (spec §3, the assembled statement)

A single machine-checked theorem tying together the whole development for the Sycamore-53
(53 qubits, depth 20) parameters:

* **(cut)** the optimal sweep cut is `53` (`CorollaryD.sweepCut_sycamore53`);
* **(cost)** the stem contraction cost is on the order of `10^18`
  (`CorollaryD.stemCost_sycamore53`, `4·2^53·150 ∈ [10^18, 10^19)`);
* **(stem)** on the **faithful spacetime model** (`GridModel.gridModel 53`: orders are genuine
  path decompositions of the real 53×53 spacetime grid graph, width is the actual largest bag —
  nothing postulated) the optimum is **pinned exactly**: every order has width `≥ 54`
  (augmented-bramble floor, `GridExact`) and the explicit sweep achieves `≤ 54`, so `cc = 54`
  and the sweep is certifiably optimal among stem orders; every order pays total cost `≥ 2^54`
  (`sycamore53_cost_floor`), and no low-rank factorization crosses the 53-qubit cut below inner
  dimension `2^53` generically (`sycamore53_bond_floor`);
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

/-- The Sycamore-53 spacetime model: the **faithful** grid model at scale `53` — contraction
orders are the genuine path decompositions of the 53×53 spacetime grid graph (53 wires × a deep
window of 53 layers), and the width of an order is its actual largest bag. -/
def sycamore53 : CircuitGraph := gridModel 53

/-- **Exact stem-width floor**: every stem contraction order of the spacetime grid has width
`≥ 54` (the augmented-bramble theorem — no axiom), meeting the sweep exactly. -/
theorem sycamore53_stem_lower (o : sycamore53.Order) : 54 ≤ sycamore53.width o :=
  gridModel_width_lower 53 (by norm_num) o

/-- **Stem-width upper bound**: the explicit sweep order has width `≤ 54 = 53 + 1` (textbook
grid pathwidth). -/
theorem sycamore53_stem_upper : ∃ o : sycamore53.Order, sycamore53.width o ≤ 54 :=
  gridModel_width_upper 53

/-- **The optimum is pinned exactly**: `cc = 54` — the certified floor meets the explicit
sweep, so the sweep is certifiably optimal among stem orders. -/
theorem sycamore53_cc_exact : sycamore53.cc = 54 :=
  gridModel_cc_eq 53 (by norm_num)

/-- The lattice pathwidth bound is discharged on the model with `C = 1` (by construction of the
order space; the extension to tree orders is the `pw = Θ(tw)` literature input). -/
theorem sycamore53_latticeBound : LatticePathwidthBound sycamore53 1 :=
  gridModel_latticeBound 53

/-- **Certified cost floor for the benchmark instance**: every stem contraction order of the
spacetime grid pays total cost at least `2^54` — the absolute yardstick for TNCO search on
this instance, at the exact scale of the sweep. -/
theorem sycamore53_cost_floor (o : sycamore53.Order) : 2 ^ 54 ≤ GridModel.orderCost o :=
  gridModel_cost_floor 53 (by norm_num) o

/-- **Generic bond-dimension floor at the benchmark cut.** For the rigid family witnessing the
53-qubit cut, at every gate configuration outside the vanishing subvariety, the cut flattening
admits no factorization with inner dimension below `2^53`: low-rank compression cannot undercut
the width floor except on a measure-zero set of instances. -/
theorem sycamore53_bond_floor :
    ∃ (T : QTensor (Fin 53 ⊕ Fin 53) (MvPolynomial ℕ ℂ)),
      ContractionRigid leftBlock (matchingEquiv leftBlock chipMatching) T ∧
      ∀ (v : ℕ → ℂ),
        MvPolynomial.eval v
          (squareFlatten leftBlock (matchingEquiv leftBlock chipMatching) T).det ≠ 0 →
        ∀ (r : ℕ) (A : Matrix ({i // leftBlock i} → Fin 2) (Fin r) ℂ)
          (B : Matrix (Fin r) ({i // leftBlock i} → Fin 2) ℂ),
          squareFlatten leftBlock (matchingEquiv leftBlock chipMatching)
            (fun x => MvPolynomial.eval v (T x)) = A * B →
          2 ^ 53 ≤ r := by
  obtain ⟨T, hT⟩ := chip_contractionRigid (K := ℂ) (ι := ℕ) 53
  refine ⟨T, hT, fun v hv r A B hfac => ?_⟩
  have hcard : Fintype.card {i : Fin 53 ⊕ Fin 53 // leftBlock i} = 53 := by
    rw [Fintype.card_congr chipLeft, Fintype.card_fin]
  rw [← hcard]
  exact ContractionRigid.no_compression leftBlock
    (matchingEquiv leftBlock chipMatching) hT hv hfac

/-- **Sycamore-53 end-to-end lower bound.** The four assembled claims as one theorem: cut size,
cost `~10^18`, exact optimal-stem structure on the faithful spacetime model (`cc = 54`, the
floor meets the sweep, cost floor `2^54`), and contraction rigidity (full Schmidt rank `2^53`).
Standard axioms only. -/
theorem sycamore53_lower_bound :
    -- (cut) the optimal sweep cut is 53
    CorollaryD.sweepCut 53 20 = 53 ∧
    -- (cost) the stem contraction cost is on the order of 10^18
    ((10:ℕ) ^ 18 ≤ CorollaryD.stemCost 53 20 150 ∧
      CorollaryD.stemCost 53 20 150 < (10:ℕ) ^ 19) ∧
    -- (stem) on the real spacetime grid: cc = 54 exactly (the certified floor meets the
    -- explicit sweep — the sweep is certifiably optimal among stem orders), the optimum is
    -- attained, and every order pays total cost ≥ 2^54 (the certified TNCO floor)
    (sycamore53.cc = 54 ∧
      (∃ o, sycamore53.IsStem o ∧ sycamore53.width o = sycamore53.cc) ∧
      (∀ o : sycamore53.Order, 2 ^ 54 ≤ GridModel.orderCost o)) ∧
    -- (rigidity) a balanced 53-qubit cut is contraction rigid (full Schmidt rank 2^53, generic)
    (∃ (e : ({i // leftBlock i} → Fin 2) ≃ ({i // ¬ leftBlock i} → Fin 2))
        (T : QTensor (Fin 53 ⊕ Fin 53) (MvPolynomial ℕ ℂ)),
        ContractionRigid leftBlock e T) := by
  refine ⟨CorollaryD.sweepCut_sycamore53, CorollaryD.stemCost_sycamore53,
    ⟨sycamore53_cc_exact, gridModel_cc_attained 53, sycamore53_cost_floor⟩, ?_⟩
  exact ⟨_, chip_contractionRigid (K := ℂ) (ι := ℕ) 53⟩

end FieldStemProof
