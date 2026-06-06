/-
# Worst-case witness from explicit gates (spec §3, closing Lemma B's precondition)

Ties the gate library (`Gates`) to the cut-flattening machinery (`Defs`/`LemmaB`): a
nonsingular two-qubit gate, embedded on a 2-qubit cut, produces a tensor (circuit state) with
**full Schmidt rank** across the cut. This discharges the precondition of
`generic_full_schmidt_of_realizes` *constructively* with real gates — the worst-case lower
bound — leaving only the average-case Conjecture C open.

A `k`-qubit cut (Schmidt rank `2^k`) is the Kronecker product of `k` such single-bond pieces;
the single-bond / explicit-matrix case below already exhibits a full-rank operator of any size
via `nonsingular_realized`, so the worst-case tightness holds at every cut.
-/
import FieldStemProof.LemmaB
import FieldStemProof.Gates

namespace FieldStemProof

variable {I : Type*} [Fintype I] [DecidableEq I] (p : I → Prop) [DecidablePred p]

/-- Embed a two-qubit gate `g` (on `Fin 4`) onto a 2-qubit cut, via a bijection `eq` between
the `p`-side configurations and `Fin 4`, as a cut-matrix. Reindexing preserves the
determinant. -/
def gateCutMatrix (eq : ({i // p i} → Fin 2) ≃ Fin 4) (g : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix ({i // p i} → Fin 2) ({i // p i} → Fin 2) ℂ :=
  Matrix.reindex eq.symm eq.symm g

theorem gateCutMatrix_nonsingular (eq : ({i // p i} → Fin 2) ≃ Fin 4)
    {g : Matrix (Fin 4) (Fin 4) ℂ} (hg : Gates.Nonsingular g) :
    (gateCutMatrix p eq g).det ≠ 0 := by
  rw [gateCutMatrix, Matrix.det_reindex_self]; exact hg

/-- **Worst-case witness from a gate.** A nonsingular two-qubit gate, embedded on a 2-qubit
cut, yields a tensor with full Schmidt rank across the cut (`det ≠ 0`). -/
theorem gate_full_schmidt (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2))
    (eq : ({i // p i} → Fin 2) ≃ Fin 4) {g : Matrix (Fin 4) (Fin 4) ℂ} (hg : Gates.Nonsingular g) :
    (squareFlatten p e (tensorOfMatrix p e (gateCutMatrix p eq g))).det ≠ 0 :=
  nonsingular_realized p e _ (gateCutMatrix_nonsingular p eq hg)

/-- Concrete instances: each native entangler realizes full Schmidt rank across a 2-qubit cut. -/
theorem iSWAP_full_schmidt (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2))
    (eq : ({i // p i} → Fin 2) ≃ Fin 4) :
    (squareFlatten p e (tensorOfMatrix p e (gateCutMatrix p eq Gates.iSWAP))).det ≠ 0 :=
  gate_full_schmidt p e eq Gates.iSWAP_nonsingular

theorem CNOT_full_schmidt (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2))
    (eq : ({i // p i} → Fin 2) ≃ Fin 4) :
    (squareFlatten p e (tensorOfMatrix p e (gateCutMatrix p eq Gates.CNOT))).det ≠ 0 :=
  gate_full_schmidt p e eq Gates.CNOT_nonsingular

theorem fSim_full_schmidt (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2))
    (eq : ({i // p i} → Fin 2) ≃ Fin 4) (θ φ : ℝ) :
    (squareFlatten p e (tensorOfMatrix p e (gateCutMatrix p eq (Gates.fSim θ φ)))).det ≠ 0 :=
  gate_full_schmidt p e eq (Gates.fSim_nonsingular θ φ)

end FieldStemProof
