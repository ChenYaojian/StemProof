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
* the **upper bound** is an explicit two-column sweep decomposition (`sweepBags`, the
  state-vector sweep) of width `≤ 2k`.

Hence the model's `pw = cc` is genuinely pinned to `Θ(k)` — `k/2 ≤ pw ≤ 2k` — by machine-checked
bounds on a real graph, and the stem optimum is *attained* (`Nat.sInf_mem`).

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

/-! ## The explicit sweep decomposition (upper bound): two adjacent slices per bag -/

/-- The state-vector sweep as a path decomposition: bag `t` holds slices `t` and `t+1` of the
first coordinate (the boundary of the sweep at step `t`). -/
def sweepBags (k : ℕ) : LinearBags (Fin k × Fin k) where
  len := k
  bag := fun t => Finset.univ.filter fun p => p.1.val = t.val ∨ p.1.val = t.val + 1

theorem mem_sweepBags {k : ℕ} {t : Fin k} {p : Fin k × Fin k} :
    p ∈ (sweepBags k).bag t ↔ p.1.val = t.val ∨ p.1.val = t.val + 1 := by
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
    rcases (SimpleGraph.boxProd_adj).mp hxy with ⟨h1, _⟩ | ⟨_, h1⟩
    · -- first coordinates adjacent on the path: both slices fit in the lower one's bag
      rcases (SimpleGraph.pathGraph_adj).mp h1 with h | h
      · exact ⟨x.1, mem_sweepBags.mpr (Or.inl rfl), mem_sweepBags.mpr (Or.inr h.symm)⟩
      · exact ⟨y.1, mem_sweepBags.mpr (Or.inr h.symm), mem_sweepBags.mpr (Or.inl rfl)⟩
    · -- first coordinates equal: same slice, same bag
      exact ⟨x.1, mem_sweepBags.mpr (Or.inl rfl), mem_sweepBags.mpr (Or.inl (by rw [h1]))⟩
  cov := fun v => ⟨v.1, mem_sweepBags.mpr (Or.inl rfl)⟩

/-- Each sweep bag holds at most two slices: `card ≤ 2k`. -/
theorem sweepBags_card_le (k : ℕ) (t : Fin k) : ((sweepBags k).bag t).card ≤ 2 * k := by
  classical
  have hsub : (sweepBags k).bag t ⊆
      (Finset.univ.filter fun p : Fin k × Fin k => p.1.val = t.val) ∪
        (Finset.univ.filter fun p : Fin k × Fin k => p.1.val = t.val + 1) := by
    intro p hp
    rcases mem_sweepBags.mp hp with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hslice : ∀ c : ℕ,
      (Finset.univ.filter fun p : Fin k × Fin k => p.1.val = c).card ≤ k := by
    intro c
    have hinj : Set.InjOn Prod.snd
        ↑(Finset.univ.filter fun p : Fin k × Fin k => p.1.val = c) := by
      intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      exact Prod.ext (Fin.ext (hp.2.trans hq.2.symm)) hpq
    calc (Finset.univ.filter fun p : Fin k × Fin k => p.1.val = c).card
        = ((Finset.univ.filter fun p : Fin k × Fin k => p.1.val = c).image Prod.snd).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = k := by rw [Finset.card_univ, Fintype.card_fin]
  calc ((sweepBags k).bag t).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ _ + _ := Finset.card_union_le _ _
    _ ≤ k + k := Nat.add_le_add (hslice _) (hslice _)
    _ = 2 * k := by ring

theorem sweepBags_width_le (k : ℕ) : bagsWidth (sweepBags k) ≤ 2 * k :=
  Finset.sup_le fun t _ => sweepBags_card_le k t

/-! ## The faithful model -/

/-- **The faithful grid circuit model.** Orders are the genuine path decompositions of the
`k × k` spacetime grid graph; the width of an order is its actual largest bag. Every order is a
stem order by construction (linear orders are exactly path decompositions); the sweep witnesses
nonemptiness. -/
def gridModel (k : ℕ) (hk : 0 < k) : CircuitGraph where
  Order := {L : LinearBags (Fin k × Fin k) // IsPathDecomp k L}
  width := fun o => bagsWidth o.1
  IsStem := fun _ => True
  stem_exists := ⟨⟨sweepBags k, sweepBags_isPathDecomp k⟩, trivial⟩
  tw := k
  IsLattice := True

/-- **Real lower bound, every order** (the self-proved bramble theorem, now speaking about the
model): every stem contraction order of the `k × k` spacetime grid has width `≥ k/2`. -/
theorem gridModel_width_lower (k : ℕ) (hk : 0 < k) (o : (gridModel k hk).Order) :
    k ≤ 2 * (gridModel k hk).width o := by
  obtain ⟨L, hL⟩ := o
  have hlen : 0 < L.len := hL.len_pos hk
  have h := grid_pathwidth_lower_unconditional k hk L hlen hL.vint hL.edge hL.cov
  rwa [show (gridModel k hk).width ⟨L, hL⟩ = bagsWidth L from rfl,
    bagsWidth_eq_maxBag L hlen]

/-- **Real upper bound**: the sweep order has width `≤ 2k`. -/
theorem gridModel_width_upper (k : ℕ) (hk : 0 < k) :
    ∃ o : (gridModel k hk).Order, (gridModel k hk).width o ≤ 2 * k :=
  ⟨⟨sweepBags k, sweepBags_isPathDecomp k⟩, sweepBags_width_le k⟩

/-- The model's contraction optimum is genuinely pinned: `k ≤ 2 · cc` and `cc ≤ 2k` — `Θ(k)`,
with both bounds machine-checked on the real graph. -/
theorem gridModel_cc_bounds (k : ℕ) (hk : 0 < k) :
    k ≤ 2 * (gridModel k hk).cc ∧ (gridModel k hk).cc ≤ 2 * k := by
  have hne : (Set.range (gridModel k hk).width).Nonempty :=
    ⟨_, ⟨⟨sweepBags k, sweepBags_isPathDecomp k⟩, rfl⟩⟩
  constructor
  · obtain ⟨o, ho⟩ := Nat.sInf_mem hne
    rw [CircuitGraph.cc, ← ho]
    exact gridModel_width_lower k hk o
  · obtain ⟨o, ho⟩ := gridModel_width_upper k hk
    exact le_trans (Nat.sInf_le ⟨o, rfl⟩) ho

/-- Every order being a stem, the stem optimum equals the global optimum: `pw ≤ cc` (with
`cc ≤ pw` from `cc_le_pw`, equality). Hence `LatticePathwidthBound (gridModel k) 1` holds *by
construction of the order space* — the genuine content of extending to tree orders is the
`pw = Θ(tw)` literature input, carried as an explicit hypothesis where used. -/
theorem gridModel_pw_le_cc (k : ℕ) (hk : 0 < k) :
    (gridModel k hk).pw ≤ (gridModel k hk).cc := by
  have hne : (Set.range (gridModel k hk).width).Nonempty :=
    ⟨_, ⟨⟨sweepBags k, sweepBags_isPathDecomp k⟩, rfl⟩⟩
  obtain ⟨o, ho⟩ := Nat.sInf_mem hne
  rw [CircuitGraph.cc, ← ho]
  exact Nat.sInf_le ⟨o, trivial, rfl⟩

/-- The lattice pathwidth bound holds for the model with `C = 1`. -/
theorem gridModel_latticeBound (k : ℕ) (hk : 0 < k) :
    LatticePathwidthBound (gridModel k hk) 1 := by
  show (gridModel k hk).pw ≤ 1 * (gridModel k hk).cc
  rw [one_mul]
  exact gridModel_pw_le_cc k hk

/-- The optimum is *attained* by a stem order (the infimum over the genuine order space is a
member, and every order is a stem). -/
theorem gridModel_cc_attained (k : ℕ) (hk : 0 < k) :
    ∃ o, (gridModel k hk).IsStem o ∧ (gridModel k hk).width o = (gridModel k hk).cc := by
  have hne : (Set.range (gridModel k hk).width).Nonempty :=
    ⟨_, ⟨⟨sweepBags k, sweepBags_isPathDecomp k⟩, rfl⟩⟩
  obtain ⟨o, ho⟩ := Nat.sInf_mem hne
  exact ⟨o, trivial, ho⟩

end FieldStemProof.GridModel
