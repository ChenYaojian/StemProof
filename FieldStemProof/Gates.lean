/-
# Gate library (spec §1.1)

The common one- and two-qubit gates of current random quantum circuits (Google Sycamore,
USTC Zuchongzhi), as complex matrices, together with their **nonsingularity** (`det ≠ 0`,
equivalently full rank). Nonsingularity is the only property the worst-case lower-bound
witness needs: a layer of full-rank entangling gates straddling a cut realizes full Schmidt
rank (cf. `LemmaB`). Normalization constants are irrelevant to rank, so where a gate carries a
`1/√2` or `1/2` factor we discharge `det ≠ 0` via `det_smul` and a nonzero scalar rather than
evaluating the determinant exactly.
-/
import Mathlib

namespace FieldStemProof.Gates

open Matrix Complex

/-- A gate is nonsingular when its determinant is nonzero (full rank). -/
def Nonsingular {n : Type*} [Fintype n] [DecidableEq n] (g : Matrix n n ℂ) : Prop := g.det ≠ 0

/-! ## Single-qubit gates -/

/-- Pauli `X` (NOT). -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `Y`. -/
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Pauli `Z`. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Hadamard `H = (1/√2)[[1,1],[1,-1]]`. -/
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1]

/-- Phase gate `S = diag(1, i)`. -/
def S : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, I]

/-- `T = diag(1, e^{iπ/4})`. -/
noncomputable def T : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, exp (I * (Real.pi / 4))]

/-- `√X = (1/2)[[1+i, 1-i], [1-i, 1+i]]` — a Sycamore native single-qubit gate. -/
noncomputable def sqrtX : Matrix (Fin 2) (Fin 2) ℂ :=
  (2⁻¹ : ℂ) • !![1 + I, 1 - I; 1 - I, 1 + I]

/-- `√Y = (1/2)[[1+i, -(1+i)], [1+i, 1+i]]` — a Sycamore native single-qubit gate. -/
noncomputable def sqrtY : Matrix (Fin 2) (Fin 2) ℂ :=
  (2⁻¹ : ℂ) • !![1 + I, -(1 + I); 1 + I, 1 + I]

theorem X_nonsingular : Nonsingular X := by
  rw [Nonsingular, X, det_fin_two_of]; norm_num

theorem Y_nonsingular : Nonsingular Y := by
  rw [Nonsingular, Y, det_fin_two_of]; simp

theorem Z_nonsingular : Nonsingular Z := by
  rw [Nonsingular, Z, det_fin_two_of]; norm_num

theorem H_nonsingular : Nonsingular H := by
  rw [Nonsingular, H, det_smul, det_fin_two_of]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact Real.sqrt_ne_zero'.mpr (by norm_num)
  simp only [Fintype.card_fin]
  apply mul_ne_zero
  · exact pow_ne_zero _ (inv_ne_zero h2)
  · norm_num

theorem S_nonsingular : Nonsingular S := by
  rw [Nonsingular, S, det_fin_two_of]; simp [Complex.ext_iff]

theorem T_nonsingular : Nonsingular T := by
  rw [Nonsingular, T, det_fin_two_of]
  simp

theorem sqrtX_nonsingular : Nonsingular sqrtX := by
  rw [Nonsingular, sqrtX, det_smul, det_fin_two_of, Fintype.card_fin]
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  simp [Complex.ext_iff]; norm_num

theorem sqrtY_nonsingular : Nonsingular sqrtY := by
  rw [Nonsingular, sqrtY, det_smul, det_fin_two_of, Fintype.card_fin]
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  simp [Complex.ext_iff]; norm_num

/-! ## Two-qubit gates

Indexed by `Fin 4` (computational basis `00, 01, 10, 11`). Permutation gates (`SWAP`, `CNOT`)
and the diagonal gate (`CZ`) get clean `det ≠ 0` proofs; the native continuous entanglers
(`iSWAP`, `√iSWAP`, `fSim`) are defined here, with nonsingularity to follow. -/

/-- Any permutation matrix is nonsingular: its determinant is `±1`. -/
theorem permMatrix_nonsingular {n : Type*} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) :
    Nonsingular (σ.permMatrix ℂ) := by
  rw [Nonsingular, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp

/-- Controlled-`Z`, `diag(1,1,1,-1)`. -/
def CZ : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal (fun i => if i = 3 then -1 else 1)

/-- `SWAP` exchanges the two qubits: the basis transposition `01 ↔ 10`. -/
def SWAP : Matrix (Fin 4) (Fin 4) ℂ := (Equiv.swap (1 : Fin 4) 2).permMatrix ℂ

/-- `CNOT` (control = first qubit): the basis transposition `10 ↔ 11`. -/
def CNOT : Matrix (Fin 4) (Fin 4) ℂ := (Equiv.swap (2 : Fin 4) 3).permMatrix ℂ

/-- `iSWAP`: `01 ↦ i·10`, `10 ↦ i·01`. -/
def iSWAP : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 0, I, 0; 0, I, 0, 0; 0, 0, 0, 1]

/-- `√iSWAP`, a native Sycamore-class entangler. -/
noncomputable def sqrtiSWAP : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, (Real.sqrt 2)⁻¹, I * (Real.sqrt 2)⁻¹, 0;
     0, I * (Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹, 0;
     0, 0, 0, 1]

/-- Google's native `fSim(θ, φ)` gate. -/
noncomputable def fSim (θ φ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, Real.cos θ, -I * Real.sin θ, 0;
     0, -I * Real.sin θ, Real.cos θ, 0;
     0, 0, 0, exp (-I * φ)]

theorem CZ_nonsingular : Nonsingular CZ := by
  rw [Nonsingular, CZ, det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split <;> norm_num

theorem SWAP_nonsingular : Nonsingular SWAP := permMatrix_nonsingular _

theorem CNOT_nonsingular : Nonsingular CNOT := permMatrix_nonsingular _

end FieldStemProof.Gates
