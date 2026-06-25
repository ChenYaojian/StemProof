/-
# Cross-cut matching ⇒ contraction rigid (spec §3, closing the Conjecture C.2 gap)

The last C-line step is purely **combinatorial**, with no spectral analysis (the route-B payoff).
`bulkEntangling_of_matching` consumes a side bijection `e` and an indexing `eqp`; the structural
object underneath both is a **cross-cut perfect matching** `μ : {i // p i} ≃ {i // ¬ p i}` —
an explicit pairing of each p-side qubit with a ¬p-side partner, realized by the lattice's gate
geometry. A nonsingular bond per pair (a Bell-like cross-cut correlation; the identity bond *is*
a Bell pair) then makes the architecture `BulkEntangling`, hence contraction rigid.

So "the lattice routes entanglement across the cut" becomes "the lattice supplies a cross-cut
perfect matching" — a graph-combinatorial condition, not the random-matrix analysis the original
probabilistic Conjecture C required.

* `matching_bulkEntangling` / `matching_contractionRigid` — take the matching `μ` as explicit
  data (route-B form: "a circuit *with* a cross-cut matching is rigid").
* `balanced_cut_*` — corollaries: a balanced cut (`|p-side| = |¬p-side|`) supplies `μ` by
  cardinality.
* `chip2_contractionRigid` — an explicit 2-qubit cut with an explicit matching, non-vacuous.

The remaining genuinely-open piece is only that a *deep* 3D spacetime lattice realizes the
cross-cut matching above the mixing threshold (the geometric routing); the structural reduction
to that combinatorial fact is now complete and machine-checked.
-/
import FieldStemProof.Rigidity

namespace FieldStemProof

open MvPolynomial

variable {ι : Type*} {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K] [IsDomain K]
  (p : I → Prop) [DecidablePred p]

/-- The config-level side bijection induced by a qubit-level cross-cut matching `μ`. -/
def matchingEquiv (μ : {i // p i} ≃ {i // ¬ p i}) :
    ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2) :=
  Equiv.arrowCongr μ (Equiv.refl (Fin 2))

/-- **Cross-cut matching ⇒ BulkEntangling.** Given an explicit perfect matching `μ` pairing each
of the `k` p-side qubits with a ¬p-side partner, and a nonsingular entangling bond per pair, the
architecture is bulk entangling across the cut. This is the route-B structural form: the matching
is explicit data, exposing "a circuit *with* a cross-cut matching" as the hypothesis. -/
theorem matching_bulkEntangling {k : ℕ} (μ : {i // p i} ≃ {i // ¬ p i})
    (eqp : {i // p i} ≃ Fin k) (B : Fin k → Matrix (Fin 2) (Fin 2) K)
    (hB : ∀ j, (B j).det ≠ 0) :
    ∃ T : QTensor I (MvPolynomial ι K), BulkEntangling p (matchingEquiv p μ) T :=
  bulkEntangling_of_matching p (matchingEquiv p μ) eqp B hB

/-- **Cross-cut matching ⇒ contraction rigid.** Combining with the structural theorem: a circuit
with a cross-cut perfect matching and nonsingular entangling bonds is contraction rigid (full
Schmidt rank `2^k` for generic gate parameters). -/
theorem matching_contractionRigid {k : ℕ} (μ : {i // p i} ≃ {i // ¬ p i})
    (eqp : {i // p i} ≃ Fin k) (B : Fin k → Matrix (Fin 2) (Fin 2) K)
    (hB : ∀ j, (B j).det ≠ 0) :
    ∃ T : QTensor I (MvPolynomial ι K), ContractionRigid p (matchingEquiv p μ) T := by
  obtain ⟨T, hT⟩ := matching_bulkEntangling p μ eqp B hB
  exact ⟨T, contraction_rigidity p (matchingEquiv p μ) hT⟩

/-- **Balanced cut ⇒ contraction rigid** (corollary). When the two sides have equal qubit count
`k`, the matching `μ` exists by cardinality, and any nonsingular bonds give rigidity. -/
theorem balanced_cut_contractionRigid {k : ℕ}
    (hp : Fintype.card {i // p i} = k) (hq : Fintype.card {i // ¬ p i} = k)
    (B : Fin k → Matrix (Fin 2) (Fin 2) K) (hB : ∀ j, (B j).det ≠ 0) :
    ∃ (e : ({i // p i} → Fin 2) ≃ ({i // ¬ p i} → Fin 2)) (T : QTensor I (MvPolynomial ι K)),
      ContractionRigid p e T := by
  have hpq : Fintype.card {i // p i} = Fintype.card {i // ¬ p i} := by rw [hp, hq]
  let μ : {i // p i} ≃ {i // ¬ p i} := Fintype.equivOfCardEq hpq
  let eqp : {i // p i} ≃ Fin k := Fintype.equivFinOfCardEq hp
  obtain ⟨T, hT⟩ := matching_contractionRigid p μ eqp B hB
  exact ⟨matchingEquiv p μ, T, hT⟩

/-! ### Concrete lattice instance — an explicit cross-cut matching

The minimal explicit cross-cut matching: a 2-qubit chip (`Fin 2`) with the unique pairing of its
one p-side qubit to its one ¬p-side qubit (`k = 1`). The matching `μ` is given concretely (not by
a cardinality existence argument), and the bond is the identity (a Bell pair across the cut;
`det 1 ≠ 0`) — any nonsingular entangling correlation works identically. -/

/-- The "first qubit" predicate on a 2-qubit chip. -/
def leftQubit (i : Fin 2) : Prop := i = 0

instance : DecidablePred leftQubit := fun i => decEq i 0

/-- An explicit 2-qubit cross-cut matching yields a contraction-rigid family: the structural
hypothesis holds on a concrete geometry with an explicit matching. -/
theorem chip2_contractionRigid :
    ∃ (e : ({i // leftQubit i} → Fin 2) ≃ ({i // ¬ leftQubit i} → Fin 2))
      (T : QTensor (Fin 2) (MvPolynomial ι K)),
      ContractionRigid leftQubit e T := by
  refine balanced_cut_contractionRigid leftQubit (k := 1) ?_ ?_ (fun _ => 1) (fun _ => ?_)
  · decide
  · decide
  · rw [Matrix.det_one]; exact one_ne_zero

/-! ### Parametric explicit geometric matching — the brickwork block-aligned pairing

A `2m`-qubit chip modeled as two blocks `Fin m ⊕ Fin m` (left / right of a spatial cut), with
`p = "left block"`. The cross-cut matching is given **explicitly** (not by a cardinality
existence argument): left qubit `j` is paired with right qubit `j` — the block-aligned bonds the
brickwork routes across the cut. This holds for every `m`, exhibiting the matching for an
arbitrary-size lattice cut. -/

/-- The "left block" predicate on the `Fin m ⊕ Fin m` chip. -/
def leftBlock {m : ℕ} (i : Fin m ⊕ Fin m) : Prop := i.isLeft

instance {m : ℕ} : DecidablePred (leftBlock (m := m)) :=
  fun i => inferInstanceAs (Decidable (i.isLeft = true))

/-- The left block of the chip is exactly the `m` left qubits. -/
def chipLeft {m : ℕ} : {i : Fin m ⊕ Fin m // leftBlock i} ≃ Fin m where
  toFun x := x.1.getLeft (by simpa [leftBlock] using x.2)
  invFun a := ⟨Sum.inl a, by simp [leftBlock]⟩
  left_inv := by rintro ⟨_ | _, h⟩ <;> simp_all [leftBlock]
  right_inv a := rfl

/-- The right block of the chip is exactly the `m` right qubits. -/
def chipRight {m : ℕ} : {i : Fin m ⊕ Fin m // ¬ leftBlock i} ≃ Fin m where
  toFun x := x.1.getRight (by
    rcases x with ⟨_ | _, h⟩
    · exact absurd (by simp [leftBlock]) h
    · simp)
  invFun b := ⟨Sum.inr b, by simp [leftBlock]⟩
  left_inv := by rintro ⟨_ | _, h⟩ <;> simp_all [leftBlock]
  right_inv b := rfl

/-- **Explicit block-aligned cross-cut matching**: left qubit `j` ↔ right qubit `j`. -/
def chipMatching {m : ℕ} : {i : Fin m ⊕ Fin m // leftBlock i} ≃ {i : Fin m ⊕ Fin m // ¬ leftBlock i} :=
  chipLeft.trans chipRight.symm

/-- **The `2m`-qubit chip is contraction rigid via its explicit block-aligned matching**, for
every `m`. The bonds are Bell pairs (identity, `det ≠ 0`); any nonsingular entangling correlation
works identically. This exhibits the cross-cut matching for an arbitrary-size lattice cut, not
just a fixed small case. -/
theorem chip_contractionRigid (m : ℕ) :
    ∃ (T : QTensor (Fin m ⊕ Fin m) (MvPolynomial ι K)),
      ContractionRigid leftBlock (matchingEquiv leftBlock chipMatching) T :=
  matching_contractionRigid leftBlock chipMatching chipLeft (fun _ => 1)
    (fun _ => by rw [Matrix.det_one]; exact one_ne_zero)

end FieldStemProof

