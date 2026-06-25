/-
# Routable k-matching ⇒ BulkEntangling (spec §3, Conjecture C.2)

The genuinely new content turning the structural rigidity theorem's hypothesis from an
assumption into a checkable property. A *routable k-matching* across a cut pairs the `k` qubits
on each side and routes one entangling two-qubit gate through each pair; the rest act trivially.
The resulting cut flattening is the **Kronecker product of the `k` per-bond matrices**, and a
Kronecker product of nonsingular bonds is nonsingular — so the architecture reaches full Schmidt
rank `2^k`, i.e. `BulkEntangling` holds.

* `Nonsingular.kronecker` — a Kronecker product of two nonsingular matrices is nonsingular
  (over an integral domain), via `det_kronecker`.
* `bondProd` — the `k`-bond product matrix on `(Fin k → Fin 2)` configurations:
  `(bondProd B) a b = ∏ j, B j (a j) (b j)`.
* `det_bondProd_ne_zero` — if every bond `B j` is nonsingular, so is `bondProd B`
  (the `k`-fold Kronecker routing aggregation, by induction on `k`).

This is the bond-by-bond mechanism behind "each entangling bond contributes a factor 2 to the
Schmidt rank", giving the `2^k` lower bound from `k` routed gates. Connecting `bondProd` to the
spacetime-lattice cut flattening of a concrete Sycamore brickwork is the remaining step.
-/
import Mathlib

namespace FieldStemProof.Matching

open Matrix Kronecker

variable {K : Type*} [CommRing K]

/-- The `k`-bond product matrix: on configurations `(Fin k → Fin 2)` (one bit per bond), the
entry is the product of the per-bond entries. This is the iterated Kronecker product realizing
`k` independent entangling bonds across the cut. -/
def bondProd {k : ℕ} (B : Fin k → Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin k → Fin 2) (Fin k → Fin 2) K :=
  Matrix.of fun a b => ∏ j, B j (a j) (b j)

@[simp] theorem bondProd_apply {k : ℕ} (B : Fin k → Matrix (Fin 2) (Fin 2) K) (a b) :
    bondProd B a b = ∏ j, B j (a j) (b j) := rfl

/-- Splitting a `bondProd` over `Fin (k+1)` bonds as the Kronecker product of the head bond and
the remaining `bondProd`, reindexed along the head/tail equivalence. -/
theorem bondProd_succ {k : ℕ} (B : Fin (k + 1) → Matrix (Fin 2) (Fin 2) K) :
    bondProd B =
      ((B 0 ⊗ₖ bondProd (fun j => B j.succ)).submatrix
        (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm) := by
  ext a b
  simp only [bondProd_apply, submatrix_apply]
  rw [Fin.prod_univ_succ]
  rfl

section Domain
variable [IsDomain K]

/-- A Kronecker product of two nonsingular matrices is nonsingular. -/
theorem nonsingular_kronecker {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {A : Matrix m m K} {B : Matrix n n K}
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) : (A ⊗ₖ B).det ≠ 0 := by
  rw [det_kronecker]
  exact mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB)

/-- **Kronecker routing aggregation.** If every bond is nonsingular, the `k`-bond product matrix
is nonsingular — `k` routed entangling gates give full Schmidt rank `2^k` across the cut. -/
theorem det_bondProd_ne_zero {k : ℕ} (B : Fin k → Matrix (Fin 2) (Fin 2) K)
    (hB : ∀ j, (B j).det ≠ 0) : (bondProd B).det ≠ 0 := by
  induction k with
  | zero =>
    -- `Fin 0 → Fin 2` has one element; the empty product is the 1×1 matrix [1], det 1 ≠ 0.
    have : bondProd B = 1 := by
      ext a b
      simp only [bondProd_apply, Finset.univ_eq_empty, Finset.prod_empty]
      rw [Matrix.one_apply, if_pos (Subsingleton.elim a b)]
    rw [this, Matrix.det_one]; exact one_ne_zero
  | succ k ih =>
    rw [bondProd_succ, det_submatrix_equiv_self]
    exact nonsingular_kronecker (hB 0) (ih _ (fun j => hB j.succ))

/-- A `k`-matching of routed entangling gates exhibits a full-rank cut matrix of size `2^k`:
packaging `det_bondProd_ne_zero` as an existence statement, the bridge to `BulkEntangling`. -/
theorem exists_nonsingular_of_matching {k : ℕ} (B : Fin k → Matrix (Fin 2) (Fin 2) K)
    (hB : ∀ j, (B j).det ≠ 0) :
    ∃ M : Matrix (Fin k → Fin 2) (Fin k → Fin 2) K, M.det ≠ 0 :=
  ⟨bondProd B, det_bondProd_ne_zero B hB⟩

end Domain

end FieldStemProof.Matching
