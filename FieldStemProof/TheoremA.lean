/-
# Theorem A — existence of an optimal stem path (spec §3)

On a lattice circuit graph there exists a stem (caterpillar) contraction order whose width is
within a constant factor of the global contraction optimum. Structurally:

* a *contraction order* has a `width` (the max intermediate-tensor rank along it);
* `cc` = the global optimum width (min over ALL orders) = the contraction width;
* `pw` = the stem optimum (min over STEM/linear orders) = the pathwidth.

What is **proved here** (self-contained, no `sorry`):
* `cc ≤ pw` — a stem order can never beat the global optimum (stems are a subclass);
* `pw` is attained by an actual stem order;
* hence, *given* the lattice bound `pw ≤ C · cc`, there is a stem order of width in `[cc, C·cc]`,
  i.e. within a constant factor of optimal.

What is **cited from the literature** (Mathlib has NO treewidth/pathwidth theory, so these
research-level graph results are recorded as named `Prop`s a caller supplies per concrete model —
NOT as global axioms, which would be falsifiable over this abstract structure; see the section
comment below):
* `[M1]` Markov–Shi: `cc = tw(L(G))` (contraction width = line-graph treewidth);
* `[M2]` lattice bound: for a lattice graph, `pw ≤ C · cc` (since `pw = Θ(tw)` on lattices —
  no large complete-binary-tree minor). The constant `C` is the separator-theorem constant.

The exponential cost `4·2^cc·steps` and its Sycamore values are in `CorollaryD`.
-/
import Mathlib

namespace FieldStemProof

/-- Abstract model of a circuit tensor network for the contraction-width analysis: a type of
contraction `Order`s, each with a `width`, a predicate `IsStem` marking the caterpillar/linear
orders, a treewidth `tw` of the line graph, and the lattice flag `IsLattice`. -/
structure CircuitGraph where
  /-- Contraction orders (binary contraction trees) of the network. -/
  Order : Type
  /-- The width of an order: the max intermediate-tensor rank (number of open indices) along it. -/
  width : Order → ℕ
  /-- Whether an order is a stem (caterpillar / linear sweep) order. -/
  IsStem : Order → Prop
  /-- There is at least one stem order (a sweep always exists). -/
  stem_exists : ∃ o, IsStem o
  /-- The treewidth of the line graph (Markov–Shi's invariant). -/
  tw : ℕ
  /-- Whether the underlying graph is a lattice (grid / 3D spacetime). -/
  IsLattice : Prop

namespace CircuitGraph

variable (G : CircuitGraph)

/-- The set of widths of stem orders. -/
def stemWidths : Set ℕ := {w | ∃ o, G.IsStem o ∧ G.width o = w}

/-- Contraction width: the global optimum over all contraction orders. -/
noncomputable def cc : ℕ := sInf (Set.range G.width)

/-- Pathwidth: the optimum over stem (linear) orders only. -/
noncomputable def pw : ℕ := sInf G.stemWidths

theorem stemWidths_nonempty : G.stemWidths.Nonempty := by
  obtain ⟨o, ho⟩ := G.stem_exists
  exact ⟨G.width o, o, ho, rfl⟩

/-- `pw` is attained by an actual stem order. -/
theorem exists_stem_pw : ∃ o, G.IsStem o ∧ G.width o = G.pw := by
  obtain ⟨o, ho, hw⟩ := Nat.sInf_mem G.stemWidths_nonempty
  exact ⟨o, ho, hw⟩

/-- **The easy, real direction:** a stem order cannot beat the global contraction optimum. -/
theorem cc_le_pw : G.cc ≤ G.pw := by
  obtain ⟨o, _, hw⟩ := G.exists_stem_pw
  rw [← hw]
  exact Nat.sInf_le ⟨o, rfl⟩

/-- **Theorem A (proved form).** Given the lattice pathwidth bound `pw ≤ C · cc`, there exists a
stem (caterpillar) contraction order whose width is within the constant factor `C` of the global
optimum: `cc ≤ width ≤ C · cc`. Hence an (asymptotically) optimal stem path exists. -/
theorem optimal_stem_within_const (C : ℕ) (hbound : G.pw ≤ C * G.cc) :
    ∃ o, G.IsStem o ∧ G.cc ≤ G.width o ∧ G.width o ≤ C * G.cc := by
  obtain ⟨o, ho, hw⟩ := G.exists_stem_pw
  exact ⟨o, ho, hw ▸ G.cc_le_pw, hw ▸ hbound⟩

end CircuitGraph

/-! ### Cited external inputs (named `Prop`s, supplied per model — NOT global axioms)

These are **established, published theorems**, not conjectures — Mathlib simply lacks the
treewidth/pathwidth theory to reprove them, and no importable formalization exists (the only
machine-checked treewidth library is in Coq, Doczkal–Pous). They are recorded as named `Prop`s
that a caller supplies *for the concrete model at hand* (via `optimal_stem_within_const`), where
they are either discharged by computation (the Sycamore model, `Sycamore.lean`) or carried as an
explicit hypothesis with its literature reference.

They must NOT be global `axiom`s quantified over all of `CircuitGraph`: the structure's `tw` and
`IsLattice` are free fields, so adversarial instances falsify any such axiom and make the theory
inconsistent (`width ≡ 3, tw := 5` refutes a global `cc = tw`; an instance whose only stem order
is strictly wider than some non-stem order refutes a global `pw ≤ C·cc`). The published theorems
are about *faithful lattice graphs*, a subclass this abstract structure does not carve out.

* `[M1]` Markov & Shi, *Simulating quantum computation by contracting tensor networks*,
  SIAM J. Comput. 38(3):963–981, 2008 (arXiv:quant-ph/0511069): `cc(G) = tw(L(G))` exactly;
  for bounded-degree circuit graphs `tw(L(G)) = Θ(tw(G))` (their Lemma 4.4).
* `[M2a]` Grid pathwidth = treewidth: for an `n × r` grid, `pw = tw = min(n, r)` (classical;
  lower bound via the Seymour–Thomas bramble-of-crosses + treewidth duality).
* `[M2b]` Kozawa–Otachi–Yamazaki, treewidth of multidimensional grids: the `√n × √n × d`
  spacetime lattice has `tw = min(n, √n·d) + min(√n, d) − 1` (bramble lower bound), whose
  leading term `min(n, √n·d)` is exactly `CorollaryD.sweepCut`. -/

/-- `[M1]` **Markov–Shi 2008** (SIAM J. Comput. 38(3):963–981; arXiv:quant-ph/0511069): the
contraction width equals the treewidth of the line graph. A property of a *faithful* model `G`,
supplied where needed; the proved theorems above do not depend on it. -/
def MarkovShi (G : CircuitGraph) : Prop := G.cc = G.tw

/-- `[M2]` **Lattice pathwidth–treewidth bound** with constant `C` (`[M2a]` grid `pw = tw`,
Seymour–Thomas; `[M2b]` Kozawa–Otachi–Yamazaki for the spacetime lattice; `C` absorbs the
bounded-degree line-graph relation of `[M1]` Lemma 4.4): stem orders lose at most the factor `C`
against arbitrary contraction orders. A property of a *faithful* lattice model, supplied per
model — discharged by computation on the concrete Sycamore model (`sycamore53_pw`, with
`C = 1`). Feeding it to `optimal_stem_within_const` yields Theorem A for that model. -/
def LatticePathwidthBound (G : CircuitGraph) (C : ℕ) : Prop := G.pw ≤ C * G.cc

/-- **Theorem A (hypothesis form).** On any model satisfying the lattice pathwidth–treewidth
bound there exists a stem contraction order within the constant factor `C` of the optimal
contraction width — the optimal contraction path can be taken to have stem structure. -/
theorem optimal_stem_lattice (G : CircuitGraph) (C : ℕ) (h : LatticePathwidthBound G C) :
    ∃ o, G.IsStem o ∧ G.cc ≤ G.width o ∧ G.width o ≤ C * G.cc :=
  G.optimal_stem_within_const C h

end FieldStemProof
