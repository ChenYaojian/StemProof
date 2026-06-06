/-
# FieldStemProof

Formalization of the stem-structure lower bound for contracting tensor networks of
random quantum circuits. See `docs/spec.md` for the full statement and proof roadmap.

Layered targets:
* `FieldStemProof.Defs`     — definitions (spec §1)
* `FieldStemProof.Gates`    — common random-circuit gate library + nonsingularity (spec §1.1)
* `FieldStemProof.TheoremA` — existence of an optimal stem path (spec §3, Theorem A)
* `FieldStemProof.LemmaB`   — generic full-rank tightness (spec §3, Lemma B) — first goal
* `FieldStemProof.Worstcase` — worst-case witness: explicit gates realize full Schmidt rank
-/
import FieldStemProof.Defs
import FieldStemProof.Gates
import FieldStemProof.TheoremA
import FieldStemProof.LemmaB
import FieldStemProof.Worstcase
