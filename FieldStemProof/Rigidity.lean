/-
# Contraction Rigidity — the structural theorem (spec §3, reframing Conjecture C)

Restates the no-rank-collapse content as a **structural theorem** rather than a probabilistic
one: instead of "a Haar-random circuit has full Schmidt rank with high probability", we prove
"*any* circuit family that can entangle across a cut has full Schmidt rank generically — for all
gate parameters outside a measure-zero subvariety". Random circuits, Sycamore, and the Google
supremacy circuits then become *corollaries* (verify they satisfy the structural hypothesis),
avoiding the random-matrix `Pr(·)` analysis entirely.

The engine is `LemmaB.generic_full_schmidt`: one full-rank parameter point upgrades to generic
full rank. Here we name the hypothesis (`BulkEntangling`) and the conclusion
(`ContractionRigid`), and record that the explicit-gate / Bell witnesses already discharge the
hypothesis (so the structural theorem is non-vacuous and applies to real gate sets).

This is the layer that turns the open "Conjecture C" into:
* a **proved structural theorem** (`contraction_rigidity`) — done, no `sorry`;
* a **remaining hypothesis-checking task** (`BulkEntangling` for a routable k-matching of the
  spacetime lattice — `Rigidity.lean` reduces it to the worst-case witness; the lattice routing
  itself is future work);
* a **probabilistic corollary** (`Pr(rank collapse) → 0` over a continuous gate measure), which
  follows because the bad set is a measure-zero subvariety.
-/
import FieldStemProof.LemmaB
import FieldStemProof.Worstcase

namespace FieldStemProof

open MvPolynomial

variable {ι : Type*} {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]
  (p : I → Prop) [DecidablePred p]

/-- **Bulk entangling property at a cut.** A parameter-dependent tensor family `T` (entries are
polynomials in the gate parameters) is bulk-entangling across the balanced cut `(p, e)` if some
gate configuration `θ₀` makes the square flattening across the cut nonsingular — i.e. the
architecture is *capable* of full Schmidt rank `2^{|p-side|}` across the cut. This is the
structural hypothesis replacing "Haar-random". -/
def BulkEntangling (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2))
    (T : QTensor I (MvPolynomial ι K)) : Prop :=
  ∃ θ₀ : ι → K, (squareFlatten p e (fun x => eval θ₀ (T x))).det ≠ 0

/-- **Contraction rigidity at a cut.** The flattening's determinant is a nonzero polynomial and
the evaluated flattening is full rank for all gate parameters outside its proper vanishing
subvariety — i.e. no rank collapse, generically. -/
def ContractionRigid (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2))
    (T : QTensor I (MvPolynomial ι K)) : Prop :=
  (squareFlatten p e T).det ≠ 0 ∧
    ∀ v, eval v (squareFlatten p e T).det ≠ 0 →
      (squareFlatten p e (fun x => eval v (T x))).det ≠ 0

/-- **Contraction Rigidity Theorem (structural).** Bulk entangling ⇒ contraction rigid:
a circuit family capable of full Schmidt rank at *one* gate configuration is rigid for *generic*
gate configurations. This is the structural replacement for Conjecture C — proved, no `sorry`,
from `generic_full_schmidt` (Schwartz–Zippel genericity), with no probability. -/
theorem contraction_rigidity (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2))
    {T : QTensor I (MvPolynomial ι K)} (h : BulkEntangling p e T) :
    ContractionRigid p e T := by
  obtain ⟨θ₀, hθ₀⟩ := h
  exact generic_full_schmidt p e T (v₀ := θ₀) hθ₀

/-! ### The hypothesis is satisfiable — structural theorem is non-vacuous

The explicit witnesses already built (`bellWitness`, entangling gates) discharge
`BulkEntangling`, so `ContractionRigid` holds for them. This shows the structural theorem
applies to real gate sets, not just abstractly. -/

/-- A constant tensor family realizing the Bell (identity-flattening) witness is bulk
entangling: the witness configuration itself makes the flattening the identity. -/
theorem bulkEntangling_of_bellWitness [Nontrivial K]
    (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2)) :
    BulkEntangling p e (fun x => (C (bellWitness p e x) : MvPolynomial ι K)) := by
  refine ⟨fun _ => 0, ?_⟩
  have : (fun x => eval (fun _ => (0 : K)) (C (bellWitness p e x) : MvPolynomial ι K))
      = bellWitness p e := by funext x; rw [eval_C]
  rw [this, det_squareFlatten_bellWitness]
  exact one_ne_zero

end FieldStemProof
