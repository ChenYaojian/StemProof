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
-/
import FieldStemProof.Defs

namespace FieldStemProof

-- Lemma B to be stated and proved here.

end FieldStemProof
