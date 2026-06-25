/-
# Grid cross connectivity — discharging the last hypothesis (spec §3)

The only external input of `Bramble.grid_pathwidth_lower` is `hconn`: each cross `row s ∪ col s`
is connected in the grid graph. Here we discharge it for the genuine nearest-neighbour grid
`gridGraph k = pathGraph k □ pathGraph k`, using Mathlib's path-graph connectivity and the
box-product walk embeddings (`boxProdRight s : x ↦ (s, x)` walks along row `s`; `boxProdLeft s :
x ↦ (x, s)` walks along column `s`). Routing any cross vertex to the centre `(s, s)` and
concatenating gives a walk staying inside the cross.

With this, `grid_pathwidth_lower_unconditional` has NO bramble/graph hypotheses left beyond the
defining axioms of a path decomposition — the `Θ(min(n, √n·d))` stem-width lower bound is fully
self-contained (the treewidth lower-bound axiom is discharged for the stem/pathwidth width).
-/
import FieldStemProof.Bramble

namespace FieldStemProof.GridConn

open SimpleGraph FieldStemProof.Bramble

/-- The nearest-neighbour `k × k` grid graph: the box product of two path graphs. -/
abbrev gridGraph (k : ℕ) : SimpleGraph (Fin k × Fin k) := pathGraph k □ pathGraph k

theorem mem_cross {k : ℕ} {s : Fin k} {x : Fin k × Fin k} :
    x ∈ cross k s ↔ x.1 = s ∨ x.2 = s := by
  simp [cross, Finset.mem_filter]

/-- The graph hom embedding the row `s` (first coord fixed) into the grid. -/
def rowHom (k : ℕ) (s : Fin k) : pathGraph k →g gridGraph k :=
  (boxProdRight (pathGraph k) (pathGraph k) s).toHom

/-- The graph hom embedding the column `s` (second coord fixed) into the grid. -/
def colHom (k : ℕ) (s : Fin k) : pathGraph k →g gridGraph k :=
  (boxProdLeft (pathGraph k) (pathGraph k) s).toHom

@[simp] theorem rowHom_apply (k : ℕ) (s y : Fin k) : rowHom k s y = (s, y) := rfl
@[simp] theorem colHom_apply (k : ℕ) (s y : Fin k) : colHom k s y = (y, s) := rfl

/-- A walk from any cross vertex to the centre `(s, s)` staying inside the cross. -/
theorem to_center (k : ℕ) (s : Fin k) :
    ∀ v : Fin k × Fin k, (v.1 = s ∨ v.2 = s) →
      ∃ p : (gridGraph k).Walk v (s, s), ∀ x ∈ p.support, x ∈ cross k s := by
  rintro ⟨v1, v2⟩ h
  rcases h with h1 | h2
  · -- first coord = s: walk along the row via rowHom
    simp only at h1; subst v1
    obtain ⟨q⟩ := pathGraph_preconnected k v2 s
    refine ⟨q.map (rowHom k s), fun x hx => ?_⟩
    have hx2 : x ∈ q.support.map (rowHom k s) :=
      SimpleGraph.Walk.support_map (rowHom k s) q ▸ hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx2
    exact mem_cross.mpr (Or.inl (by rw [rowHom_apply]))
  · -- second coord = s: walk along the column via colHom
    simp only at h2; subst v2
    obtain ⟨q⟩ := pathGraph_preconnected k v1 s
    refine ⟨q.map (colHom k s), fun x hx => ?_⟩
    have hx2 : x ∈ q.support.map (colHom k s) :=
      SimpleGraph.Walk.support_map (colHom k s) q ▸ hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx2
    exact mem_cross.mpr (Or.inr (by rw [colHom_apply]))

/-- **The grid crosses are connected** (discharges `hconn`): any two vertices of a cross are
joined by a grid walk staying inside the cross (route both to the centre and concatenate). -/
theorem cross_connected (k : ℕ) (s : Fin k) (u w : Fin k × Fin k)
    (hu : u ∈ cross k s) (hw : w ∈ cross k s) :
    ∃ p : (gridGraph k).Walk u w, ∀ x ∈ p.support, x ∈ cross k s := by
  obtain ⟨pu, hpu⟩ := to_center k s u (mem_cross.mp hu)
  obtain ⟨pw, hpw⟩ := to_center k s w (mem_cross.mp hw)
  refine ⟨pu.append pw.reverse, fun x hx => ?_⟩
  rw [SimpleGraph.Walk.support_append, List.mem_append] at hx
  rcases hx with h | h
  · exact hpu x h
  · exact hpw x (by
      have := List.mem_of_mem_tail h
      rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this)

/-- **Self-contained grid stem-width lower bound.** In any path decomposition of the `k × k` grid
graph (vertex-interval `hvint`, edge cover `hedge`, vertex cover `hcov`), the largest bag satisfies
`k ≤ 2 · maxBag` — stem width `≥ k/2 − 1 = Θ(min(n, √n·d))`. No bramble or connectivity
hypothesis remains; the cross connectivity is proved (`cross_connected`). -/
theorem grid_pathwidth_lower_unconditional (k : ℕ) (hk : 0 < k)
    (L : LinearBags (Fin k × Fin k)) (hlen : 0 < L.len)
    (hvint : ∀ (v : Fin k × Fin k) (a c j : Fin L.len),
      a ≤ j → j ≤ c → v ∈ L.bag a → v ∈ L.bag c → v ∈ L.bag j)
    (hedge : ∀ ⦃x y : Fin k × Fin k⦄, (gridGraph k).Adj x y → ∃ m, x ∈ L.bag m ∧ y ∈ L.bag m)
    (hcov : ∀ v : Fin k × Fin k, ∃ i, v ∈ L.bag i) :
    k ≤ 2 * L.maxBag hlen :=
  grid_pathwidth_lower k hk L hlen (gridGraph k) hvint hedge hcov (cross_connected k)

end FieldStemProof.GridConn
