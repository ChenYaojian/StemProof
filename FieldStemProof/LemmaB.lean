/-
# Lemma B — generic full-rank tightness (spec §3, difficulty: medium / original core)

Along `T★`, for all gate parameters outside a measure-zero algebraic variety `{P = 0}`,
each intermediate tensor's flattening across its cut `cut_i` has full rank `2^{|cut_i|}`.
Hence the contraction width along `T★` equals `pw(G)`, and `Θ(2^{tw}) · steps` is a tight
lower bound for the contraction method.

Proof skeleton (Schwartz–Zippel / generic rank):
* the flattening `M_i(θ)` is a polynomial matrix in the gate entries;
* exhibit ONE assignment making `M_i` full rank (explicit max-entangling construction that
  realizes the lattice cut) ⇒ some `2^{|cut_i|}`-minor is a nonzero polynomial in `θ`;
* its zero set is a measure-zero variety; union over all `i` stays measure-zero.

Technical burden: the explicit full-rank assignment (lattice cut ⇒ realized entanglement).
This is the highest value-to-effort target and the first formalization goal.

────────────────────────────────────────────────────────────────────────────────────────
This file formalizes the **genericity engine** of Lemma B, fully and abstractly:

    a square matrix whose entries are polynomials in the parameters, if nonsingular at
    ONE parameter point, is nonsingular for ALL parameters outside a proper subvariety.

This is the "some point full rank ⇒ generic full rank" principle — the step that turns the
graph-theoretic width bound into a *tight* lower bound (no rank collapse). It is matrix-
and parameter-agnostic, hence reusable for every intermediate flattening `M_i(θ)`.

The bridge onto tensor flattenings is below (`generic_full_schmidt`); the named
hypothesis/conclusion packaging (`BulkEntangling` ⇒ `ContractionRigid`) and the
matching-based discharge of the witness live in `Rigidity` / `Matching` / `Lattice`.
-/
import Mathlib
import FieldStemProof.Defs

namespace FieldStemProof

open MvPolynomial

variable {σ K n : Type*} [CommRing K] [Fintype n] [DecidableEq n]

/-- Evaluation commutes with the determinant of a parameter-dependent matrix:
`eval v (det M) = det (eval v ∘ M)`.  (Instance of `RingHom.map_det` for `eval v`.) -/
theorem det_map_eval (M : Matrix n n (MvPolynomial σ K)) (v : σ → K) :
    eval v M.det = (M.map (eval v)).det :=
  (eval v).map_det M

/-- **Generic nonsingularity — the genericity engine of Lemma B.**
If a parameter-dependent square matrix `M` is nonsingular at a single parameter point `v₀`
(`det` of the evaluated matrix is nonzero), then:

* `det M` is a *nonzero* polynomial, and
* `M` is nonsingular at every parameter `v` outside the zero locus `{v | eval v (det M) = 0}`.

Thus the singular ("rank-collapse") locus is contained in the vanishing set of one fixed
nonzero polynomial `det M`. -/
theorem generic_nonsingular (M : Matrix n n (MvPolynomial σ K)) {v₀ : σ → K}
    (h : (M.map (eval v₀)).det ≠ 0) :
    M.det ≠ 0 ∧ ∀ v, eval v M.det ≠ 0 → (M.map (eval v)).det ≠ 0 := by
  refine ⟨fun hzero => h ?_, fun v hv => ?_⟩
  · rw [← det_map_eval, hzero, map_zero]
  · rwa [← det_map_eval]

/-- The singular locus equals the vanishing set of the polynomial `det M` (unconditional;
properness — that `det M ≠ 0` — is supplied by `generic_nonsingular`). -/
theorem singular_locus_eq (M : Matrix n n (MvPolynomial σ K)) :
    {v : σ → K | (M.map (eval v)).det = 0} = {v | eval v M.det = 0} := by
  ext v
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, det_map_eval]

section InfiniteDomain
variable [IsDomain K] [Infinite K]

/-- Over an infinite integral domain a nonzero determinant polynomial cannot vanish
everywhere, so the nonsingular locus is *nonempty*: the singular subvariety `V(det M)` is
**proper**.  (Over `ℝ`/`ℂ` this upgrades to "the singular locus has measure zero".) -/
theorem exists_nonsingular_of_det_ne_zero {M : Matrix n n (MvPolynomial σ K)}
    (h : M.det ≠ 0) : ∃ v, (M.map (eval v)).det ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  refine h (MvPolynomial.funext fun v => ?_)
  rw [map_zero, det_map_eval]
  exact hcon v

end InfiniteDomain

/-! ### Bridge: genericity engine acting on tensor flattenings

Instantiating `generic_nonsingular` at the square flattening of a parameter-dependent qubit
tensor across a balanced cut. This is the form Lemma B actually needs: the gate entries are
the parameters, the tensor is an intermediate contraction result, and `det ≠ 0` of the
square flattening is "full Schmidt rank across the cut" (no rank collapse). -/

variable {ι : Type*} [Fintype I] [DecidableEq I] (p : I → Prop) [DecidablePred p]

/-- Evaluation commutes with the determinant of a square tensor flattening. -/
theorem det_squareFlatten_map
    (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2)) (T : QTensor I (MvPolynomial ι K))
    (v : ι → K) :
    eval v (squareFlatten p e T).det = (squareFlatten p e (fun x => eval v (T x))).det := by
  rw [det_map_eval, squareFlatten_map]

/-- **Generic full Schmidt rank (Lemma B at a balanced cut).**
If the square flattening of a parameter-dependent tensor across the balanced cut `p` is full
rank (`det ≠ 0`) at a single parameter point `v₀` (a max-entangling witness), then:

* `det (squareFlatten p e T)` is a *nonzero* polynomial in the gate parameters, and
* for every parameter `v` outside that polynomial's proper vanishing subvariety, the
  evaluated tensor's flattening is full rank — generic no-rank-collapse across the cut. -/
theorem generic_full_schmidt
    (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2)) (T : QTensor I (MvPolynomial ι K))
    {v₀ : ι → K} (h : (squareFlatten p e (fun x => eval v₀ (T x))).det ≠ 0) :
    (squareFlatten p e T).det ≠ 0 ∧
      ∀ v, eval v (squareFlatten p e T).det ≠ 0 →
        (squareFlatten p e (fun x => eval v (T x))).det ≠ 0 := by
  have h' : ((squareFlatten p e T).map (eval v₀)).det ≠ 0 := by rwa [squareFlatten_map]
  obtain ⟨hne, hgen⟩ := generic_nonsingular (squareFlatten p e T) h'
  refine ⟨hne, fun v hv => ?_⟩
  have hv' := hgen v hv
  rwa [squareFlatten_map] at hv'

/-! ### The max-entangling witness discharges the hypothesis

`generic_full_schmidt` is conditional on a single parameter point achieving full rank. The
`bellWitness` (identity flattening) shows that condition is *satisfiable*: full Schmidt rank
across a balanced cut is achievable, so the genericity engine is non-vacuous. What remains
(needs the gate/`TN(C)` model) is to show a real random circuit *realizes* the witness at
some gate parameter `v₀`. -/

/-- The max-entangling witness has full Schmidt rank: its square flattening has determinant
`1`. -/
theorem det_squareFlatten_bellWitness [Nontrivial K]
    (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2)) :
    (squareFlatten p e (bellWitness p e : QTensor I K)).det = 1 := by
  rw [squareFlatten_bellWitness, Matrix.det_one]

/-- Full-rank flattenings across a balanced cut exist — the hypothesis of
`generic_full_schmidt` is satisfiable, not vacuous. -/
theorem exists_full_schmidt [Nontrivial K]
    (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2)) :
    ∃ T : QTensor I K, (squareFlatten p e T).det ≠ 0 :=
  ⟨bellWitness p e, by rw [det_squareFlatten_bellWitness]; exact one_ne_zero⟩

/-- **Lemma B, precondition discharged by realizability.**
If a parameter family `T` *realizes* the max-entangling witness at some gate parameter `v₀`
(i.e. `eval v₀ ∘ T` is the Bell witness across the cut), then full Schmidt rank across the
cut is generic: `det (squareFlatten p e T)` is a nonzero polynomial and the evaluated
flattening is full rank off its proper vanishing subvariety. -/
theorem generic_full_schmidt_of_realizes [Nontrivial K]
    (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2)) (T : QTensor I (MvPolynomial ι K))
    {v₀ : ι → K} (hreal : (fun x => eval v₀ (T x)) = bellWitness p e) :
    (squareFlatten p e T).det ≠ 0 ∧
      ∀ v, eval v (squareFlatten p e T).det ≠ 0 →
        (squareFlatten p e (fun x => eval v (T x))).det ≠ 0 := by
  refine generic_full_schmidt p e T (v₀ := v₀) ?_
  rw [hreal, det_squareFlatten_bellWitness]
  exact one_ne_zero

/-! ### Generic tensors have full Schmidt rank (no rank collapse)

Specializing to the universal tensor `genericTensor`, whose entries are independent
parameters. The max-entangling witness is the evaluation at `v₀ = bellWitness`, so the
realizability hypothesis holds *by construction*, and we obtain unconditionally: a generic
qubit tensor has full Schmidt rank across every balanced cut, with rank collapse confined to
a proper subvariety. This is the "generic ⇒ no rank collapse" core of Lemma B for
*unconstrained* tensors.

The remaining circuit-specific content: an intermediate tensor of an actual random circuit is
NOT unconstrained — its entries are polynomials in the *local gate* parameters. That this
constrained subfamily still avoids rank collapse is the realizability question: worst-case it
does (a SWAP/Bell gate layer across the cut realizes `bellWitness`). The average-case question
is reframed structurally in `Rigidity` (`BulkEntangling ⇒ ContractionRigid`), whose remaining
hypothesis for a concrete architecture is a cross-cut matching (`Matching`/`Lattice`); concrete
circuits over discrete gate sets stay outside any vanishing-set (generic) statement. -/

omit [DecidableEq I] in
/-- The universal tensor realizes the max-entangling witness at the parameter point
`v₀ = bellWitness`. -/
theorem genericTensor_realizes [Nontrivial K]
    (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2)) :
    (fun x => eval (bellWitness p e : QTensor I K) (genericTensor I K x)) = bellWitness p e := by
  funext x
  rw [genericTensor, eval_X]
/-- **Generic no-rank-collapse (Lemma B for a generic tensor).**
A generic qubit tensor has full Schmidt rank across the balanced cut `p`: the determinant of
its square flattening is a nonzero polynomial in the tensor entries, and the flattening is
full rank for all entry-values outside that polynomial's proper vanishing subvariety. -/
theorem generic_tensor_full_schmidt [Nontrivial K]
    (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2)) :
    (squareFlatten p e (genericTensor I K)).det ≠ 0 ∧
      ∀ v, eval v (squareFlatten p e (genericTensor I K)).det ≠ 0 →
        (squareFlatten p e (fun x => eval v (genericTensor I K x))).det ≠ 0 :=
  generic_full_schmidt_of_realizes p e (genericTensor I K) (genericTensor_realizes p e)

/-! ### Worst-case: any nonsingular operator realizes full Schmidt rank

Since flattening is surjective onto matrices (`squareFlatten_tensorOfMatrix`), *any* nonsingular
cut-matrix `M` is realized as a full-rank flattening — `det = 0` cannot occur. In particular
`M` may be a (reindexed) entangling gate from `Gates`, giving an explicit worst-case circuit
state with maximal Schmidt rank `2^k` across the cut. This discharges Lemma B's precondition
constructively (worst-case), independent of the average-case Conjecture C. -/

/-- A nonsingular cut-matrix `M` is realized as a full-rank flattening of an explicit tensor. -/
theorem nonsingular_realized
    (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2))
    (M : Matrix ({i // p i} → Fin 2) ({i // p i} → Fin 2) K) (hM : M.det ≠ 0) :
    (squareFlatten p e (tensorOfMatrix p e M)).det ≠ 0 := by
  rw [squareFlatten_tensorOfMatrix]; exact hM

end FieldStemProof
