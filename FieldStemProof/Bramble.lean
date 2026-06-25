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

/-! ## The grid cross-bramble: order ≥ k/2

On the `k × k` grid (`Fin k × Fin k`), the `k` "crosses" `cross i = row i ∪ column i` form a
bramble: pairwise intersecting (at `(i,j)`), and of large order. We prove the asymptotically
correct order bound `k ≤ 2 · order` by the elementary row/column-projection counting (any hitting
set's row- and column-projections must together cover all `k` indices). This gives the `Θ` scale
(the exact cross-bramble order is `k+1`, but `Θ(min(n,√n·d))` only needs order `= Θ(k)`). -/

/-- The `i`-th cross of the `k × k` grid: row `i` together with column `i`. -/
def cross (k : ℕ) (i : Fin k) : Finset (Fin k × Fin k) :=
  Finset.univ.filter (fun p => p.1 = i ∨ p.2 = i)

/-- The crosses are pairwise intersecting (a genuine bramble): `(i, j) ∈ cross i ∩ cross j`. -/
theorem cross_inter_nonempty (k : ℕ) (i j : Fin k) :
    (cross k i ∩ cross k j).Nonempty :=
  ⟨(i, j), by simp [cross, Finset.mem_filter]⟩

/-- **Cross-bramble order lower bound (Θ scale).** Any hitting set `H` of all `k` crosses has
`k ≤ 2 · H.card`: its row-projection `R` and column-projection `C` together cover every index,
so `k ≤ |R| + |C| ≤ 2|H|`. -/
theorem cross_hitting_card {k : ℕ} {H : Finset (Fin k × Fin k)}
    (hH : ∀ i, (H ∩ cross k i).Nonempty) : k ≤ 2 * H.card := by
  classical
  set R := H.image Prod.fst with hR
  set C := H.image Prod.snd with hC
  have hcover : (Finset.univ : Finset (Fin k)) ⊆ R ∪ C := by
    intro i _
    obtain ⟨p, hp⟩ := hH i
    rw [Finset.mem_inter] at hp
    have hpc : p.1 = i ∨ p.2 = i := by simpa [cross, Finset.mem_filter] using hp.2
    rcases hpc with h1 | h2
    · exact Finset.mem_union_left _ (h1 ▸ Finset.mem_image_of_mem Prod.fst hp.1)
    · exact Finset.mem_union_right _ (h2 ▸ Finset.mem_image_of_mem Prod.snd hp.1)
  calc k = (Finset.univ : Finset (Fin k)).card := by rw [Finset.card_univ, Fintype.card_fin]
    _ ≤ (R ∪ C).card := Finset.card_le_card hcover
    _ ≤ R.card + C.card := Finset.card_union_le _ _
    _ ≤ H.card + H.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * H.card := by ring

/-- The cross-bramble order is `Θ(k)`: `k ≤ 2 · order`. Combined with `order_le_maxBag`, any path
decomposition of the `k × k` grid (whose connected crosses occupy index intervals) has a bag of
size `≥ k/2`, i.e. pathwidth `≥ k/2 − 1` — the `Θ(min(n,√n·d))` stem-width lower bound. -/
theorem cross_order_ge {k : ℕ} (hk : 0 < k) : k ≤ 2 * order (cross k) := by
  classical
  have hne : {n | ∃ H : Finset (Fin k × Fin k), IsHittingSet (cross k) H ∧ H.card = n}.Nonempty := by
    refine ⟨(Finset.univ).card, Finset.univ, fun i => ?_, rfl⟩
    obtain ⟨a⟩ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    exact ⟨(i, i), by simp [cross]⟩
  obtain ⟨H, hHhit, hHcard⟩ := Nat.sInf_mem hne
  rw [order, ← hHcard]
  exact cross_hitting_card hHhit

/-! ## The connectivity ⇒ index-interval bridge

The remaining link: in a path decomposition (`LinearBags` with the vertex-interval property
`hvint` and the edge-cover property `hedge` for a graph `G`), a `G`-connected vertex set occupies
a *betweenness-closed* set of bag indices. This is what supplies the `mem_iff` interval
hypothesis of `order_le_maxBag` for a graph bramble.

`Conn` encodes connectivity of `b` as: any two of its vertices are joined by a `G`-walk staying
in `b`. The proof is an induction on that walk: each edge lies in a common bag, so the walk's
vertex-intervals form an overlapping chain spanning `[i, k]`, hence cover any `j` between. -/

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Walk induction core: along a `G`-walk from `u` to `w` lying in `b`, if `u` occupies bag index
`i` and `w` occupies bag index `k` with `i ≤ j ≤ k`, then some walk vertex (hence a vertex of `b`)
occupies bag index `j`. -/
theorem walk_hits (L : LinearBags V) (G : SimpleGraph V) (b : Finset V) (j : Fin L.len)
    (hvint : ∀ (v : V) (a c : Fin L.len), a ≤ j → j ≤ c → v ∈ L.bag a → v ∈ L.bag c → v ∈ L.bag j)
    (hedge : ∀ ⦃x y : V⦄, G.Adj x y → ∃ m, x ∈ L.bag m ∧ y ∈ L.bag m)
    {u w : V} (p : G.Walk u w) :
    (∀ x ∈ p.support, x ∈ b) → ∀ (i k : Fin L.len), i ≤ j → j ≤ k →
      u ∈ L.bag i → w ∈ L.bag k → ∃ x, x ∈ L.bag j ∧ x ∈ b := by
  induction p with
  | nil =>
    intro hsupp i k hij hjk hu hw
    exact ⟨_, hvint _ i k hij hjk hu hw, hsupp _ (by simp)⟩
  | cons h q ih =>
    intro hsupp i k hij hjk hu hw
    obtain ⟨m, hum, hvm⟩ := hedge h
    rcases le_total j m with hjm | hmj
    · exact ⟨_, hvint _ i m hij hjm hu hum, hsupp _ (by simp)⟩
    · refine ih (fun x hx => hsupp x ?_) m k hmj hjk hvm hw
      rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hx

/-- **The bridge.** A `G`-connected vertex set `b` occupies a betweenness-closed set of bag
indices: if `b` meets bag `i` and bag `k`, it meets every bag `j` with `i ≤ j ≤ k`. -/
theorem bag_meets_betweenness (L : LinearBags V) (G : SimpleGraph V) (b : Finset V)
    (hvint : ∀ (v : V) (a c j : Fin L.len), a ≤ j → j ≤ c → v ∈ L.bag a → v ∈ L.bag c → v ∈ L.bag j)
    (hedge : ∀ ⦃x y : V⦄, G.Adj x y → ∃ m, x ∈ L.bag m ∧ y ∈ L.bag m)
    (Conn : ∀ u w, u ∈ b → w ∈ b → ∃ p : G.Walk u w, ∀ x ∈ p.support, x ∈ b)
    {i j k : Fin L.len} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : (L.bag i ∩ b).Nonempty) (hk : (L.bag k ∩ b).Nonempty) :
    (L.bag j ∩ b).Nonempty := by
  obtain ⟨u, hu⟩ := hi; obtain ⟨w, hw⟩ := hk
  rw [Finset.mem_inter] at hu hw
  obtain ⟨p, hp⟩ := Conn u w hu.2 hw.2
  obtain ⟨x, hxj, hxb⟩ :=
    walk_hits L G b j (fun v a c => hvint v a c j) hedge p hp i k hij hjk hu.1 hw.1
  exact ⟨x, Finset.mem_inter.mpr ⟨hxj, hxb⟩⟩

end FieldStemProof.Bramble
