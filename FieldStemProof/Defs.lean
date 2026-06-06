/-
# Definitions layer (spec §1)

Formalizes the objects the main results quantify over:

* `1.1`  random quantum circuit architecture `A = (n, d, L, {G_t})` and ensemble `𝒞(A, μ)`
* `1.1′` spacetime-lattice geometry — the distinction between a 2D grid (1D qubit chain
        × time) and the **(2+1)D = 3D** spacetime lattice (2D chip × time). The main
        results target the 3D deep-bulk regime.
* `1.2`  tensor network `TN(C)`, its network graph `G`, and line graph `L(G)`
* `1.3`  contraction tree, `width(T)`, contraction width `cc(G)`
* `1.4`  stem / caterpillar contraction tree and pathwidth
* `1.6`  minimum transverse separator (cut)

Built on Mathlib's `Matrix` / `Equiv` / `SimpleGraph`. This file currently formalizes the
**flattening across a cut** (spec §1.6): a qubit tensor reshaped into a matrix whose row /
column indices are the two sides of a bipartition of its legs. Its rank is the Schmidt rank
across the cut, and full rank at the bottleneck is exactly "no rank collapse" — the quantity
Lemma B controls. Evaluation commutes with flattening (`flatten_map`), which is the hook
that lets the genericity engine in `LemmaB` act on flattenings.
-/
import Mathlib

namespace FieldStemProof

open MvPolynomial

variable {I : Type*} {R : Type*}

/-- A qubit tensor on legs indexed by `I`: an array of entries indexed by a bit per leg. -/
abbrev QTensor (I R : Type*) := (I → Fin 2) → R

/-- The **universal qubit tensor**: every amplitude is its own free parameter (one polynomial
variable per configuration). Any concrete tensor over `K` is an evaluation of this one, so a
property holding *generically* for `genericTensor` is exactly the "random / generic tensor"
statement — e.g. no Schmidt-rank collapse for a generic tensor. -/
noncomputable def genericTensor (I K : Type*) [CommSemiring K] :
    QTensor I (MvPolynomial (I → Fin 2) K) :=
  fun x => MvPolynomial.X x

variable (p : I → Prop) [DecidablePred p]

/-- Reshaping a tensor's legs across the cut `p`: a bit-assignment to all legs is the same
data as a bit-assignment to the `p`-side together with one to the `¬p`-side. -/
def cutEquiv : (I → Fin 2) ≃ (({i // p i} → Fin 2) × ({i // ¬ p i} → Fin 2)) :=
  (Equiv.arrowCongr (Equiv.sumCompl p).symm (Equiv.refl (Fin 2))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- **Flattening across a cut** (spec §1.6). The tensor `T` reshaped into a matrix with rows
indexed by bit-assignments to the `p`-side and columns by bit-assignments to the `¬p`-side. -/
def flatten (T : QTensor I R) :
    Matrix ({i // p i} → Fin 2) ({i // ¬ p i} → Fin 2) R :=
  Matrix.of fun a b => T ((cutEquiv p).symm (a, b))

@[simp] theorem flatten_apply (T : QTensor I R) (a b) :
    flatten p T a b = T ((cutEquiv p).symm (a, b)) := rfl

/-- Evaluation/relabelling commutes with flattening: flattening then applying `f` entrywise
equals applying `f` to the tensor then flattening. This transports the genericity engine
(`LemmaB.generic_nonsingular`, stated for `eval v`) onto flattenings. -/
theorem flatten_map {S : Type*} (T : QTensor I S) (f : S → R) :
    (flatten p T).map f = flatten p (fun x => f (T x)) := rfl

/-- **Square flattening at a balanced cut.** When the two sides of the cut carry the same
number of bit-configurations — witnessed by a bijection `σ` between them — the flattening
becomes a square matrix, so its determinant (hence nonsingularity = full Schmidt rank) is
available. `σ` exists iff `|p-side| = |¬p-side|`, i.e. the bottleneck balanced cut. -/
def squareFlatten (σ : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2)) (T : QTensor I R) :
    Matrix ({i // p i} → Fin 2) ({i // p i} → Fin 2) R :=
  (flatten p T).submatrix id σ

/-- Entrywise relabelling commutes with the square flattening (carries `flatten_map`
through the reindexing), transporting the genericity engine onto square flattenings. -/
theorem squareFlatten_map {S : Type*} (σ : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2))
    (T : QTensor I S) (f : S → R) :
    (squareFlatten p σ T).map f = squareFlatten p σ (fun x => f (T x)) := rfl

section Witness
variable [Fintype I] [Zero R] [One R]

/-- The maximally-entangling ("Bell"/identity) witness across the balanced cut `p` paired by
`e`: the tensor whose entry is `1` exactly when the `¬p`-side bits are the `e`-image of the
`p`-side bits, and `0` otherwise. Its flattening is the identity matrix — the extreme case of
full Schmidt rank, i.e. a maximally entangled state across the cut. -/
def bellWitness (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2)) : QTensor I R :=
  fun x => if (cutEquiv p x).2 = e (cutEquiv p x).1 then (1 : R) else 0

/-- The Bell witness flattens to the **identity matrix**: full Schmidt rank by construction. -/
theorem squareFlatten_bellWitness (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2)) :
    squareFlatten p e (bellWitness p e : QTensor I R) = 1 := by
  ext a a'
  simp only [squareFlatten, Matrix.submatrix_apply, id_eq, flatten_apply, bellWitness,
    Equiv.apply_symm_apply, e.injective.eq_iff, Matrix.one_apply]
  by_cases h : a' = a
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun he => h he.symm)]

end Witness

end FieldStemProof
