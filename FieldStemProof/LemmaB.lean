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

Still to bridge (needs the §1 definitions of `TN(C)`, cuts, flattenings):
* instantiate the parameter type `σ` as the gate matrix entries and `M` as a maximal
  square submatrix (size `2^{|cut_i|}`) of the flattening across `cut_i`;
* supply the explicit max-entangling witness `v₀` realizing the lattice cut.
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

end FieldStemProof
