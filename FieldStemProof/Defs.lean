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

Built on Mathlib's `SimpleGraph`. Treewidth/pathwidth are taken from Mathlib where
available, otherwise defined here against the line graph.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace FieldStemProof

-- Definitions to be added here.

end FieldStemProof
