/-
# FieldStemProof

Formalization of the stem-structure lower bound for contracting tensor networks of
random quantum circuits. See `docs/spec.md` for the full statement and proof roadmap.

Layered targets:
* `FieldStemProof.Defs`     — definitions (spec §1)
* `FieldStemProof.Gates`    — common random-circuit gate library + nonsingularity (spec §1.1)
* `FieldStemProof.TheoremA` — existence of an optimal stem path (spec §3, Theorem A)
* `FieldStemProof.CorollaryD` — Sycamore complexity numbers 10^18 / 10^24 (spec §3, Cor. D)
* `FieldStemProof.LemmaB`   — generic full-rank tightness (spec §3, Lemma B) — first goal
* `FieldStemProof.Worstcase` — worst-case witness: explicit gates realize full Schmidt rank
* `FieldStemProof.Rigidity` — Contraction Rigidity: the structural theorem (reframes Conj. C)
* `FieldStemProof.Matching` — Kronecker routing: a k-matching of entanglers ⇒ full rank 2^k
* `FieldStemProof.Lattice` — balanced sweep cut ⇒ matching ⇒ contraction rigid (closes C.2 gap)
* `FieldStemProof.Sycamore` — end-to-end Sycamore-53 lower bound (cut + cost + stem + rigidity)
* `FieldStemProof.Spacetime` — faithful cut geometry: time/space sweeps, min(n,√n·d) scale
* `FieldStemProof.Bramble` — interval-Helly pathwidth lower bound (stem width ≥ bramble order)
* `FieldStemProof.GridConn` — grid cross connectivity ⇒ self-contained pathwidth lower bound
* `FieldStemProof.Brickwork` — keystone: deep brickwork routes a min(n,√n·d) cross-cut matching
-/
import FieldStemProof.Defs
import FieldStemProof.Gates
import FieldStemProof.TheoremA
import FieldStemProof.CorollaryD
import FieldStemProof.LemmaB
import FieldStemProof.Worstcase
import FieldStemProof.Matching
import FieldStemProof.Rigidity
import FieldStemProof.Lattice
import FieldStemProof.Sycamore
import FieldStemProof.Spacetime
import FieldStemProof.Bramble
import FieldStemProof.GridConn
import FieldStemProof.Brickwork
