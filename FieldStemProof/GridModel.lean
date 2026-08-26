/-
# A faithful grid model: `CircuitGraph` instantiated by REAL path decompositions (spec §3)

Replaces the degenerate Sycamore model (`Order := Unit`, constant `width`) with a model derived
from the genuine spacetime lattice graph:

* `Order` := all path decompositions of the `k × k` grid graph `GridConn.gridGraph k`
  (`Bramble.LinearBags` satisfying the three defining axioms `IsPathDecomp`) — the linear/stem
  contraction orders of the spacetime tensor network, an infinite genuine order space;
* `width` := the actual largest bag size of the decomposition (`bagsWidth`), a *derived*
  quantity — nothing is postulated;
* the **lower bound** `k ≤ 2 · width` for *every* order is the self-proved bramble theorem
  (`GridConn.grid_pathwidth_lower_unconditional`);
* the **upper bound** is an explicit sliding-window sweep decomposition (`sweepBags`, the
  state-vector sweep boundary) of width `≤ k + 1` — the textbook grid pathwidth.

Hence the model's `pw = cc` is genuinely pinned to `Θ(k)` — `k/2 ≤ pw ≤ k + 1` — by
machine-checked bounds on a real graph, and the stem optimum is *attained* (`Nat.sInf_mem`).

Honest scope: `IsStem ≡ True` here is *definitional*, not degenerate — the order space of this
model consists exactly of the linear (stem) orders; extending the lower bound to arbitrary tree
contraction orders is precisely the `pw = Θ(tw)` literature input (`LatticePathwidthBound`),
carried as an explicit hypothesis elsewhere. The `k × k` grid is the spacetime lattice of a
`k`-wire chain in the deep regime (`d ≥ k` layers); the (2+1)D chip lattice is the remaining
faithfulness step (cf. `Causal` for its matching side).
-/
import FieldStemProof.GridConn
import FieldStemProof.TheoremA

namespace FieldStemProof.GridModel

open FieldStemProof.Bramble FieldStemProof.GridConn

variable {V : Type*} [DecidableEq V]

/-- Total width of a bag sequence: the largest bag size (`Finset.sup`, so no nonemptiness side
condition; agrees with `maxBag` when `len > 0`). -/
def bagsWidth (L : LinearBags V) : ℕ :=
  Finset.univ.sup fun i => (L.bag i).card

theorem bagsWidth_eq_maxBag (L : LinearBags V) (hlen : 0 < L.len) :
    bagsWidth L = L.maxBag hlen :=
  (Finset.sup'_eq_sup _ _).symm

/-- **Path decomposition of the `k × k` grid graph** — the three defining axioms: vertex bags
form index intervals (`vint`), every grid edge lies in a bag (`edge`), every vertex is covered
(`cov`). Exactly the hypotheses of `grid_pathwidth_lower_unconditional`. -/
structure IsPathDecomp (k : ℕ) (L : LinearBags (Fin k × Fin k)) : Prop where
  vint : ∀ (v : Fin k × Fin k) (a c j : Fin L.len),
    a ≤ j → j ≤ c → v ∈ L.bag a → v ∈ L.bag c → v ∈ L.bag j
  edge : ∀ ⦃x y : Fin k × Fin k⦄, (gridGraph k).Adj x y → ∃ m, x ∈ L.bag m ∧ y ∈ L.bag m
  cov : ∀ v : Fin k × Fin k, ∃ i, v ∈ L.bag i

theorem IsPathDecomp.len_pos {k : ℕ} (hk : 0 < k) {L : LinearBags (Fin k × Fin k)}
    (h : IsPathDecomp k L) : 0 < L.len := by
  obtain ⟨i, _⟩ := h.cov (⟨0, hk⟩, ⟨0, hk⟩)
  exact i.pos

/-! ## The explicit sweep decomposition (tight upper bound): a `k + 1` sliding window

The state-vector sweep absorbs vertices in column-major order; at each step the live boundary is
the last `k` absorbed vertices plus the current one — a sliding window of `k + 1` consecutive
positions. This realizes the textbook grid pathwidth upper bound `pw ≤ k` (bag size `k + 1`),
matching the sweep-cut narrative (`cut + 1`). -/

/-- Column-major position of a grid vertex: the order in which the sweep absorbs vertices
(first coordinate fast). -/
def pos {k : ℕ} (p : Fin k × Fin k) : ℕ := p.1.val + k * p.2.val

theorem pos_lt {k : ℕ} (p : Fin k × Fin k) : pos p < k * k :=
  calc pos p < k + k * p.2.val := Nat.add_lt_add_right p.1.isLt _
    _ = k * (p.2.val + 1) := by ring
    _ ≤ k * k := Nat.mul_le_mul_left k p.2.isLt

theorem pos_inj {k : ℕ} {p q : Fin k × Fin k} (h : pos p = pos q) : p = q := by
  have hk : 0 < k := p.1.pos
  have h1 : ∀ r : Fin k × Fin k, pos r % k = r.1.val := fun r => by
    rw [pos, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.1.isLt]
  have h2 : ∀ r : Fin k × Fin k, pos r / k = r.2.val := fun r => by
    rw [pos, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt r.1.isLt, Nat.zero_add]
  exact Prod.ext (Fin.ext (by rw [← h1 p, ← h1 q, h])) (Fin.ext (by rw [← h2 p, ← h2 q, h]))

/-- The sweep as a path decomposition: bag `t` is the window of positions `[t, t + k]` — the
sweep boundary (last `k` absorbed vertices) plus the vertex being absorbed. -/
def sweepBags (k : ℕ) : LinearBags (Fin k × Fin k) where
  len := k * k
  bag := fun t => Finset.univ.filter fun p => t.val ≤ pos p ∧ pos p ≤ t.val + k

theorem mem_sweepBags {k : ℕ} {t : Fin (k * k)} {p : Fin k × Fin k} :
    p ∈ (sweepBags k).bag t ↔ t.val ≤ pos p ∧ pos p ≤ t.val + k := by
  simp [sweepBags]

/-- The sweep is a genuine path decomposition of the grid graph. -/
theorem sweepBags_isPathDecomp (k : ℕ) : IsPathDecomp k (sweepBags k) where
  vint := by
    intro v a c j haj hjc hva hvc
    rw [mem_sweepBags] at hva hvc ⊢
    rw [Fin.le_def] at haj hjc
    omega
  edge := by
    intro x y hxy
    -- both endpoints of an edge differ in position by 1 (vertical) or k (horizontal);
    -- the window at the smaller position contains both
    have key : ∀ (u v : Fin k × Fin k) (d : ℕ), d ≤ k → pos v = pos u + d →
        ∃ m, u ∈ (sweepBags k).bag m ∧ v ∈ (sweepBags k).bag m := by
      intro u v d hd hpos
      exact ⟨⟨pos u, pos_lt u⟩,
        mem_sweepBags.mpr ⟨by show pos u ≤ pos u; omega, by show pos u ≤ pos u + k; omega⟩,
        mem_sweepBags.mpr ⟨by show pos u ≤ pos v; omega, by show pos v ≤ pos u + k; omega⟩⟩
    have hk : 0 < k := x.1.pos
    rcases (SimpleGraph.boxProd_adj).mp hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- vertical edge: first coordinates adjacent, second equal — position difference 1
      rcases (SimpleGraph.pathGraph_adj).mp h1 with h | h
      · exact key x y 1 hk (by rw [pos, pos, ← h, ← h2]; ring)
      · obtain ⟨m, hm1, hm2⟩ := key y x 1 hk (by rw [pos, pos, ← h, h2]; ring)
        exact ⟨m, hm2, hm1⟩
    · -- horizontal edge: second coordinates adjacent, first equal — position difference k
      rcases (SimpleGraph.pathGraph_adj).mp h1 with h | h
      · exact key x y k (le_refl k) (by rw [pos, pos, ← h, ← h2]; ring)
      · obtain ⟨m, hm1, hm2⟩ := key y x k (le_refl k) (by rw [pos, pos, ← h, h2]; ring)
        exact ⟨m, hm2, hm1⟩
  cov := fun v =>
    ⟨⟨pos v, pos_lt v⟩,
      mem_sweepBags.mpr ⟨by show pos v ≤ pos v; omega, by show pos v ≤ pos v + k; omega⟩⟩

/-- Each window bag holds at most `k + 1` vertices (positions are injective, the window has
`k + 1` slots). -/
theorem sweepBags_card_le (k : ℕ) (t : Fin (k * k)) :
    ((sweepBags k).bag t).card ≤ k + 1 := by
  classical
  have hinj : Set.InjOn (pos : Fin k × Fin k → ℕ) ↑((sweepBags k).bag t) :=
    fun p _ q _ h => pos_inj h
  calc ((sweepBags k).bag t).card
      = (((sweepBags k).bag t).image pos).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc t.val (t.val + k)).card := by
        apply Finset.card_le_card
        intro n hn
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
        exact Finset.mem_Icc.mpr (mem_sweepBags.mp hp)
    _ = k + 1 := by rw [Nat.card_Icc]; omega

theorem sweepBags_width_le (k : ℕ) : bagsWidth (sweepBags k) ≤ k + 1 :=
  Finset.sup_le fun t _ => sweepBags_card_le k t

/-! ## The faithful model -/

/-- **The faithful grid circuit model.** Orders are the genuine path decompositions of the
`k × k` spacetime grid graph; the width of an order is its actual largest bag. Every order is a
stem order by construction (linear orders are exactly path decompositions); the sweep witnesses
nonemptiness. -/
def gridModel (k : ℕ) : CircuitGraph where
  Order := {L : LinearBags (Fin k × Fin k) // IsPathDecomp k L}
  width := fun o => bagsWidth o.1
  IsStem := fun _ => True
  stem_exists := ⟨⟨sweepBags k, sweepBags_isPathDecomp k⟩, trivial⟩
  tw := k
  IsLattice := True

/-- **Real lower bound, every order** (the self-proved bramble theorem, now speaking about the
model): every stem contraction order of the `k × k` spacetime grid has width `≥ k/2`. -/
theorem gridModel_width_lower (k : ℕ) (hk : 0 < k) (o : (gridModel k).Order) :
    k ≤ 2 * (gridModel k).width o := by
  obtain ⟨L, hL⟩ := o
  have hlen : 0 < L.len := hL.len_pos hk
  have h := grid_pathwidth_lower_unconditional k hk L hlen hL.vint hL.edge hL.cov
  rwa [show (gridModel k).width ⟨L, hL⟩ = bagsWidth L from rfl,
    bagsWidth_eq_maxBag L hlen]

/-- **Real upper bound**: the sweep order has width `≤ k + 1` (the textbook grid pathwidth). -/
theorem gridModel_width_upper (k : ℕ) :
    ∃ o : (gridModel k).Order, (gridModel k).width o ≤ k + 1 :=
  ⟨⟨sweepBags k, sweepBags_isPathDecomp k⟩, sweepBags_width_le k⟩

/-- The model's contraction optimum is genuinely pinned: `k ≤ 2 · cc` and `cc ≤ k + 1` — `Θ(k)`
with tight upper constant, both bounds machine-checked on the real graph. -/
theorem gridModel_cc_bounds (k : ℕ) (hk : 0 < k) :
    k ≤ 2 * (gridModel k).cc ∧ (gridModel k).cc ≤ k + 1 := by
  have hne : (Set.range (gridModel k).width).Nonempty :=
    ⟨_, ⟨⟨sweepBags k, sweepBags_isPathDecomp k⟩, rfl⟩⟩
  constructor
  · obtain ⟨o, ho⟩ := Nat.sInf_mem hne
    rw [CircuitGraph.cc, ← ho]
    exact gridModel_width_lower k hk o
  · obtain ⟨o, ho⟩ := gridModel_width_upper k
    exact le_trans (Nat.sInf_le ⟨o, rfl⟩) ho

/-- Every order being a stem, the stem optimum equals the global optimum: `pw ≤ cc` (with
`cc ≤ pw` from `cc_le_pw`, equality). Hence `LatticePathwidthBound (gridModel k) 1` holds *by
construction of the order space* — the genuine content of extending to tree orders is the
`pw = Θ(tw)` literature input, carried as an explicit hypothesis where used. -/
theorem gridModel_pw_le_cc (k : ℕ) :
    (gridModel k).pw ≤ (gridModel k).cc := by
  have hne : (Set.range (gridModel k).width).Nonempty :=
    ⟨_, ⟨⟨sweepBags k, sweepBags_isPathDecomp k⟩, rfl⟩⟩
  obtain ⟨o, ho⟩ := Nat.sInf_mem hne
  rw [CircuitGraph.cc, ← ho]
  exact Nat.sInf_le ⟨o, trivial, rfl⟩

/-- The lattice pathwidth bound holds for the model with `C = 1`. -/
theorem gridModel_latticeBound (k : ℕ) :
    LatticePathwidthBound (gridModel k) 1 := by
  show (gridModel k).pw ≤ 1 * (gridModel k).cc
  rw [one_mul]
  exact gridModel_pw_le_cc k

/-- The optimum is *attained* by a stem order (the infimum over the genuine order space is a
member, and every order is a stem). -/
theorem gridModel_cc_attained (k : ℕ) :
    ∃ o, (gridModel k).IsStem o ∧ (gridModel k).width o = (gridModel k).cc := by
  have hne : (Set.range (gridModel k).width).Nonempty :=
    ⟨_, ⟨⟨sweepBags k, sweepBags_isPathDecomp k⟩, rfl⟩⟩
  obtain ⟨o, ho⟩ := Nat.sInf_mem hne
  exact ⟨o, trivial, ho⟩

end FieldStemProof.GridModel
