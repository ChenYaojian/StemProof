/-
# Theorem A — existence of an optimal stem path (spec §3, difficulty: low / assembly)

On a (spacetime-)lattice circuit graph `G = L(TN(C))` there exists a stem (caterpillar)
contraction tree `T★` with `width(T★) = pw(G) = Θ(tw(G)) = cc(G)`.

Proof assembly:
* `[M1]` Markov–Shi   : `cc(G) = tw(L(G))`  (equality, no constant)
* `[M2]` grid pw≈tw   : `pw(G) = Θ(tw(G))` for lattice graphs (no large complete-binary-tree minor)
* construction        : a width-`pw(G)` path decomposition ⇒ a linear absorption order ⇒ `T★`

Open constants: the path-decomposition → contraction-order map under dangling open indices;
the `pw = Θ(tw)` constant for the 3D spacetime lattice (separator-theorem constant).
-/
import FieldStemProof.Defs

namespace FieldStemProof

-- Theorem A to be stated and proved here.

end FieldStemProof
