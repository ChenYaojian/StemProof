/-
# Bramble lower bound for stem width (pathwidth) (spec §3, the Q2 lower-bound piece)

The stem (caterpillar) contraction order is a *path* decomposition, whose width is the
**pathwidth**. The lower bound "no stem beats `min(n, √n·d)`" is therefore a pathwidth lower
bound, and pathwidth lower bounds have an **elementary** core — *interval Helly* (pairwise
intersecting intervals on a line share a point) — unlike treewidth, whose bramble argument needs
the (Mathlib-absent) subtree Helly on trees.

This file builds that core, isolating the elementary mathematical heart from graph plumbing:

* `interval_helly` — finitely many intervals `[a s, b s]` that pairwise overlap (`a s ≤ b t`
  for all `s, t`) share a common point. Fully proved.
* `linear_bramble_bound` — abstract pathwidth-style lower bound: if a family of "blocks" sits in
  a linear (path) bag-sequence so that each block occupies an index *interval* and the blocks
  pairwise overlap in index (the combinatorial shadow of "connected blocks, pairwise touching, in
  a path decomposition"), then some bag meets every block — so its size is at least the number of
  blocks that are pairwise disjoint as vertex sets (the bramble order). Fully proved.

The graph-connectivity ⇒ index-interval bridge (a connected vertex set occupies an index
interval of a path decomposition) and the concrete grid cross-bramble are the remaining steps to
turn this into `pw(grid) ≥ min(n, d)`; the Helly core they rest on is now machine-checked.
-/
import Mathlib

namespace FieldStemProof.Bramble

/-- **Interval Helly (1D).** A nonempty finite family of intervals `[a s, b s]` in a linear order
that pairwise overlap (every left endpoint is below every right endpoint) has a common point. -/
theorem interval_helly {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {α : Type*} [LinearOrder α] (a b : ι → α)
    (h : ∀ i ∈ s, ∀ j ∈ s, a i ≤ b j) :
    ∃ x, ∀ i ∈ s, a i ≤ x ∧ x ≤ b i := by
  -- the common point is the largest left endpoint
  refine ⟨s.sup' hs a, fun i hi => ⟨Finset.le_sup' a hi, ?_⟩⟩
  obtain ⟨j, hj, hje⟩ := Finset.exists_mem_eq_sup' hs a
  rw [hje]
  exact h j hj i hi

/-- A linear (path) bag-sequence over `Fin m`: each index carries a finite bag of vertices. -/
structure LinearBags (V : Type*) where
  /-- number of bags along the path -/
  len : ℕ
  /-- the bag at each index -/
  bag : Fin len → Finset V

/-- The width of a linear bag-sequence: the largest bag size (here we track the raw bag size; the
conventional pathwidth subtracts one). -/
noncomputable def LinearBags.maxBag {V : Type*} [DecidableEq V] (L : LinearBags V)
    (hlen : 0 < L.len) : ℕ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hlen⟩⟩) fun i => (L.bag i).card

/-- **Linear bramble lower bound (core).** Suppose a finite family of blocks `β : Fin r → Finset V`
sits in the path `L` so that "block `s` meets bag `i`" holds exactly on an index interval
`[lo s, hi s]` (`mem_iff`), and these intervals pairwise overlap (`overlap`, the shadow of
pairwise-touching blocks in a path decomposition). Then some single bag meets *every* block. -/
theorem some_bag_hits_all {V : Type*} [DecidableEq V] (L : LinearBags V)
    {r : ℕ} (hr : 0 < r) (β : Fin r → Finset V) (lo hi : Fin r → Fin L.len)
    (mem_iff : ∀ s i, (L.bag i ∩ β s).Nonempty ↔ (lo s ≤ i ∧ i ≤ hi s))
    (overlap : ∀ s t, lo s ≤ hi t) :
    ∃ i : Fin L.len, ∀ s : Fin r, (L.bag i ∩ β s).Nonempty := by
  have hrs : (Finset.univ : Finset (Fin r)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩
  obtain ⟨x, hx⟩ := interval_helly Finset.univ hrs lo hi
    (fun i _ j _ => overlap i j)
  refine ⟨x, fun s => ?_⟩
  rw [mem_iff]
  exact hx s (Finset.mem_univ s)

/-- A bag that meets every block is a *hitting set* (transversal) of the bramble. -/
def IsHittingSet {V : Type*} [DecidableEq V] {r : ℕ} (β : Fin r → Finset V) (H : Finset V) : Prop :=
  ∀ s, (H ∩ β s).Nonempty

/-- The order of the bramble: the least size of a hitting set. -/
noncomputable def order {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (β : Fin r → Finset V) : ℕ :=
  sInf {k | ∃ H : Finset V, IsHittingSet β H ∧ H.card = k}

/-- If a bag is a hitting set, its size is at least the bramble order. -/
theorem order_le_card_of_hitting {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (β : Fin r → Finset V) {H : Finset V} (hH : IsHittingSet β H) : order β ≤ H.card :=
  Nat.sInf_le ⟨H, hH, rfl⟩

/-- **Pathwidth bramble lower bound.** Under the interval/overlap shadow of a bramble in a path
decomposition, the largest bag is at least the bramble order: `order β ≤ maxBag`. Hence the
pathwidth (`maxBag − 1`) is at least `order β − 1`. -/
theorem order_le_maxBag {V : Type*} [Fintype V] [DecidableEq V] (L : LinearBags V)
    (hlen : 0 < L.len) {r : ℕ} (hr : 0 < r) (β : Fin r → Finset V) (lo hi : Fin r → Fin L.len)
    (mem_iff : ∀ s i, (L.bag i ∩ β s).Nonempty ↔ (lo s ≤ i ∧ i ≤ hi s))
    (overlap : ∀ s t, lo s ≤ hi t) :
    order β ≤ L.maxBag hlen := by
  obtain ⟨i, hi'⟩ := some_bag_hits_all L hr β lo hi mem_iff overlap
  calc order β ≤ (L.bag i).card := order_le_card_of_hitting β hi'
    _ ≤ L.maxBag hlen := Finset.le_sup' (fun j => (L.bag j).card) (Finset.mem_univ i)

end FieldStemProof.Bramble
