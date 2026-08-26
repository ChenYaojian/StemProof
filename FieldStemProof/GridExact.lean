/-
# Exact grid stem-width floor via the augmented bramble (spec §3, the calibration constant)

The elementary cross bramble pins the stem width of the `k × k` grid only to `Θ(k)`
(`k ≤ 2·maxBag`). For a yardstick that *meets* the found solution, the constant matters. This
file proves the exact textbook floor: every path decomposition of the `(k+1) × (k+1)` grid
graph has a bag of size `≥ k + 2` — matching the sliding-window sweep (`≤ k + 2`,
`GridModel.sweepBags`) exactly, so the optimum is *pinned*, not bracketed, and the sweep is
certifiably optimal among stem orders.

The bramble is the augmented (Seymour–Thomas style) one: the `k²` crosses of the `k × k`
subgrid, plus the last row, plus the last column minus the corner. The boundary blocks are
disjoint from the crosses — they only *touch* through edges — so the bound goes through
`Bramble.pathwidth_ge_order_of_touching`. The transversal counting is the classical
"miss a row and miss a column" argument, formalized by projections. Everything is
self-contained: `#print axioms` shows standard axioms only.
-/
import FieldStemProof.GridConn

namespace FieldStemProof.GridExact

open SimpleGraph FieldStemProof.Bramble FieldStemProof.GridConn

/-! ## Monotone chain walks with support bounds

`GridConn` routes along full rows/columns, where any walk stays inside the block. The subgrid
crosses need walks that do not overshoot the subgrid, so we build the straight ascending walk
and record that its support stays within the endpoints. -/

theorem chain_walk_asc (n : ℕ) : ∀ (d : ℕ) (u v : Fin n), v.val = u.val + d →
    ∃ p : (pathGraph n).Walk u v, ∀ x ∈ p.support, u.val ≤ x.val ∧ x.val ≤ v.val := by
  intro d
  induction d with
  | zero =>
    intro u v h
    have huv : u = v := Fin.ext (by omega)
    subst huv
    exact ⟨Walk.nil, by simp⟩
  | succ d ih =>
    intro u v h
    have hw : u.val + 1 < n := by have := v.isLt; omega
    have hadj : (pathGraph n).Adj u ⟨u.val + 1, hw⟩ := pathGraph_adj.mpr (Or.inl rfl)
    obtain ⟨p, hp⟩ := ih ⟨u.val + 1, hw⟩ v (by show v.val = u.val + 1 + d; omega)
    refine ⟨Walk.cons hadj p, ?_⟩
    intro x hx
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨le_refl _, by omega⟩
    · have h2 := hp x hx
      have h1 : u.val + 1 ≤ x.val := h2.1
      exact ⟨by omega, h2.2⟩

/-- A chain walk between any two vertices whose support stays within `[min, max]` of the
endpoint values. -/
theorem chain_walk_between (n : ℕ) (a b : Fin n) :
    ∃ p : (pathGraph n).Walk a b,
      ∀ x ∈ p.support, min a.val b.val ≤ x.val ∧ x.val ≤ max a.val b.val := by
  rcases le_total a.val b.val with h | h
  · obtain ⟨p, hp⟩ := chain_walk_asc n (b.val - a.val) a b (by omega)
    exact ⟨p, fun x hx => by have := hp x hx; omega⟩
  · obtain ⟨p, hp⟩ := chain_walk_asc n (a.val - b.val) b a (by omega)
    refine ⟨p.reverse, fun x hx => ?_⟩
    rw [Walk.support_reverse, List.mem_reverse] at hx
    have := hp x hx
    omega

/-! ## The augmented bramble on the `(k+1) × (k+1)` grid -/

/-- The `(i, j)` cross of the `k × k` subgrid: row `i` and column `j`, both restricted to the
first `k` coordinates. -/
def stCross (k : ℕ) (i j : Fin k) : Finset (Fin (k+1) × Fin (k+1)) :=
  Finset.univ.filter fun p =>
    (p.1 = i.castSucc ∧ p.2.val < k) ∨ (p.2 = j.castSucc ∧ p.1.val < k)

/-- The last row (full). -/
def stRow (k : ℕ) : Finset (Fin (k+1) × Fin (k+1)) :=
  Finset.univ.filter fun p => p.1 = Fin.last k

/-- The last column minus the corner. -/
def stCol (k : ℕ) : Finset (Fin (k+1) × Fin (k+1)) :=
  Finset.univ.filter fun p => p.2 = Fin.last k ∧ p.1.val < k

theorem mem_stCross {k : ℕ} {i j : Fin k} {p : Fin (k+1) × Fin (k+1)} :
    p ∈ stCross k i j ↔ (p.1 = i.castSucc ∧ p.2.val < k) ∨ (p.2 = j.castSucc ∧ p.1.val < k) := by
  simp [stCross]

theorem mem_stRow {k : ℕ} {p : Fin (k+1) × Fin (k+1)} :
    p ∈ stRow k ↔ p.1 = Fin.last k := by
  simp [stRow]

theorem mem_stCol {k : ℕ} {p : Fin (k+1) × Fin (k+1)} :
    p ∈ stCol k ↔ p.2 = Fin.last k ∧ p.1.val < k := by
  simp [stCol]

/-- The augmented bramble: subgrid crosses ⊕ (last row | last column). -/
def stBlocks (k : ℕ) : (Fin k × Fin k) ⊕ Bool → Finset (Fin (k+1) × Fin (k+1))
  | Sum.inl (i, j) => stCross k i j
  | Sum.inr true => stRow k
  | Sum.inr false => stCol k

/-! ## Connectivity of the blocks -/

/-- Every cross vertex routes to the cross centre `(i, j)` inside the cross. -/
theorem stCross_to_center (k : ℕ) (i j : Fin k) :
    ∀ v ∈ stCross k i j,
      ∃ p : (gridGraph (k+1)).Walk v (i.castSucc, j.castSucc),
        ∀ x ∈ p.support, x ∈ stCross k i j := by
  rintro ⟨v1, v2⟩ hv
  rcases mem_stCross.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- row arm: walk along row `i` from column v2 to column j, staying below k
    simp only at h1
    subst h1
    obtain ⟨q, hq⟩ := chain_walk_between (k+1) v2 j.castSucc
    refine ⟨q.map (rowHom (k+1) i.castSucc), ?_⟩
    intro x hx
    have hx2 : x ∈ q.support.map (rowHom (k+1) i.castSucc) :=
      SimpleGraph.Walk.support_map (rowHom (k+1) i.castSucc) q ▸ hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx2
    have hb := hq y hy
    refine mem_stCross.mpr (Or.inl ⟨rfl, ?_⟩)
    have h2' : v2.val < k := h2
    have hj : (Fin.castSucc j).val < k := by simpa using j.isLt
    show y.val < k
    omega
  · -- column arm: walk along column `j` from row v1 to row i, staying below k
    simp only at h1
    subst h1
    obtain ⟨q, hq⟩ := chain_walk_between (k+1) v1 i.castSucc
    refine ⟨q.map (colHom (k+1) j.castSucc), ?_⟩
    intro x hx
    have hx2 : x ∈ q.support.map (colHom (k+1) j.castSucc) :=
      SimpleGraph.Walk.support_map (colHom (k+1) j.castSucc) q ▸ hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx2
    have hb := hq y hy
    refine mem_stCross.mpr (Or.inr ⟨rfl, ?_⟩)
    have h2' : v1.val < k := h2
    have hi : (Fin.castSucc i).val < k := by simpa using i.isLt
    show y.val < k
    omega

theorem stCross_connected (k : ℕ) (i j : Fin k) (u w : Fin (k+1) × Fin (k+1))
    (hu : u ∈ stCross k i j) (hw : w ∈ stCross k i j) :
    ∃ p : (gridGraph (k+1)).Walk u w, ∀ x ∈ p.support, x ∈ stCross k i j := by
  obtain ⟨pu, hpu⟩ := stCross_to_center k i j u hu
  obtain ⟨pw, hpw⟩ := stCross_to_center k i j w hw
  refine ⟨pu.append pw.reverse, fun x hx => ?_⟩
  rw [SimpleGraph.Walk.support_append, List.mem_append] at hx
  rcases hx with h | h
  · exact hpu x h
  · exact hpw x (by
      have := List.mem_of_mem_tail h
      rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this)

theorem stRow_connected (k : ℕ) (u w : Fin (k+1) × Fin (k+1))
    (hu : u ∈ stRow k) (hw : w ∈ stRow k) :
    ∃ p : (gridGraph (k+1)).Walk u w, ∀ x ∈ p.support, x ∈ stRow k := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨w1, w2⟩ := w
  have hu1 : u1 = Fin.last k := mem_stRow.mp hu
  have hw1 : w1 = Fin.last k := mem_stRow.mp hw
  subst hu1; subst hw1
  obtain ⟨q⟩ := pathGraph_preconnected (k+1) u2 w2
  refine ⟨q.map (rowHom (k+1) (Fin.last k)), fun x hx => ?_⟩
  have hx2 : x ∈ q.support.map (rowHom (k+1) (Fin.last k)) :=
    SimpleGraph.Walk.support_map (rowHom (k+1) (Fin.last k)) q ▸ hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx2
  exact mem_stRow.mpr rfl

theorem stCol_connected (k : ℕ) (u w : Fin (k+1) × Fin (k+1))
    (hu : u ∈ stCol k) (hw : w ∈ stCol k) :
    ∃ p : (gridGraph (k+1)).Walk u w, ∀ x ∈ p.support, x ∈ stCol k := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨w1, w2⟩ := w
  obtain ⟨hu2, hu1⟩ := mem_stCol.mp hu
  obtain ⟨hw2, hw1⟩ := mem_stCol.mp hw
  simp only at hu2 hw2
  subst hu2; subst hw2
  obtain ⟨q, hq⟩ := chain_walk_between (k+1) u1 w1
  refine ⟨q.map (colHom (k+1) (Fin.last k)), fun x hx => ?_⟩
  have hx2 : x ∈ q.support.map (colHom (k+1) (Fin.last k)) :=
    SimpleGraph.Walk.support_map (colHom (k+1) (Fin.last k)) q ▸ hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx2
  have hb := hq y hy
  refine mem_stCol.mpr ⟨rfl, ?_⟩
  have hu1' : u1.val < k := hu1
  have hw1' : w1.val < k := hw1
  show y.val < k
  omega

theorem stBlocks_connected (k : ℕ) :
    ∀ s, ∀ u w, u ∈ stBlocks k s → w ∈ stBlocks k s →
      ∃ p : (gridGraph (k+1)).Walk u w, ∀ x ∈ p.support, x ∈ stBlocks k s := by
  rintro (⟨i, j⟩ | b) u w hu hw
  · exact stCross_connected k i j u w hu hw
  · cases b
    · exact stCol_connected k u w hu hw
    · exact stRow_connected k u w hu hw

/-! ## Touching -/

/-- Rows `k-1` and `k` are adjacent on the path. -/
theorem adj_pred_last {k : ℕ} (hk : 0 < k) :
    (pathGraph (k+1)).Adj ⟨k-1, by omega⟩ (Fin.last k) := by
  rw [pathGraph_adj]
  left
  show (k - 1) + 1 = k
  omega

theorem stBlocks_touch (k : ℕ) (hk : 0 < k) :
    ∀ s t, Touches (gridGraph (k+1)) (stBlocks k s) (stBlocks k t) := by
  rintro (⟨i, j⟩ | b) (⟨i', j'⟩ | b')
  · -- cross / cross: intersect at (i, j')
    exact Or.inl ⟨(i.castSucc, j'.castSucc), Finset.mem_inter.mpr
      ⟨mem_stCross.mpr (Or.inl ⟨rfl, by simpa using j'.isLt⟩),
       mem_stCross.mpr (Or.inr ⟨rfl, by simpa using i.isLt⟩)⟩⟩
  · cases b'
    · -- cross / last column: touch through the row-arm edge (i, k-1) — (i, k)
      refine Or.inr ⟨(i.castSucc, ⟨k-1, by omega⟩),
        mem_stCross.mpr (Or.inl ⟨rfl, by show k - 1 < k; omega⟩),
        (i.castSucc, Fin.last k),
        mem_stCol.mpr ⟨rfl, by simpa using i.isLt⟩, ?_⟩
      exact (SimpleGraph.boxProd_adj).mpr (Or.inr ⟨adj_pred_last hk, rfl⟩)
    · -- cross / last row: touch through the column-arm edge (k-1, j) — (k, j)
      refine Or.inr ⟨(⟨k-1, by omega⟩, j.castSucc),
        mem_stCross.mpr (Or.inr ⟨rfl, by show k - 1 < k; omega⟩),
        (Fin.last k, j.castSucc),
        mem_stRow.mpr rfl, ?_⟩
      exact (SimpleGraph.boxProd_adj).mpr (Or.inl ⟨adj_pred_last hk, rfl⟩)
  · cases b
    · -- last column / cross: symmetric
      refine Or.inr ⟨(i'.castSucc, Fin.last k),
        mem_stCol.mpr ⟨rfl, by simpa using i'.isLt⟩,
        (i'.castSucc, ⟨k-1, by omega⟩),
        mem_stCross.mpr (Or.inl ⟨rfl, by show k - 1 < k; omega⟩), ?_⟩
      exact (SimpleGraph.boxProd_adj).mpr (Or.inr ⟨(adj_pred_last hk).symm, rfl⟩)
    · -- last row / cross: symmetric
      refine Or.inr ⟨(Fin.last k, j'.castSucc),
        mem_stRow.mpr rfl,
        (⟨k-1, by omega⟩, j'.castSucc),
        mem_stCross.mpr (Or.inr ⟨rfl, by show k - 1 < k; omega⟩), ?_⟩
      exact (SimpleGraph.boxProd_adj).mpr (Or.inl ⟨(adj_pred_last hk).symm, rfl⟩)
  · cases b <;> cases b'
    · -- col / col: self-intersect at (0, k)
      exact Or.inl ⟨(⟨0, by omega⟩, Fin.last k), Finset.mem_inter.mpr
        ⟨mem_stCol.mpr ⟨rfl, hk⟩, mem_stCol.mpr ⟨rfl, hk⟩⟩⟩
    · -- col / row: touch through (k-1, k) — (k, k)
      refine Or.inr ⟨(⟨k-1, by omega⟩, Fin.last k),
        mem_stCol.mpr ⟨rfl, by show k - 1 < k; omega⟩,
        (Fin.last k, Fin.last k),
        mem_stRow.mpr rfl, ?_⟩
      exact (SimpleGraph.boxProd_adj).mpr (Or.inl ⟨adj_pred_last hk, rfl⟩)
    · -- row / col: symmetric
      refine Or.inr ⟨(Fin.last k, Fin.last k),
        mem_stRow.mpr rfl,
        (⟨k-1, by omega⟩, Fin.last k),
        mem_stCol.mpr ⟨rfl, by show k - 1 < k; omega⟩, ?_⟩
      exact (SimpleGraph.boxProd_adj).mpr (Or.inl ⟨(adj_pred_last hk).symm, rfl⟩)
    · -- row / row: self-intersect at (k, 0)
      exact Or.inl ⟨(Fin.last k, 0), Finset.mem_inter.mpr
        ⟨mem_stRow.mpr rfl, mem_stRow.mpr rfl⟩⟩

/-! ## Transversal counting: order ≥ k + 2 -/

/-- Any transversal of the augmented bramble has at least `k + 2` vertices: it needs one vertex
in the last row, one in the last column, and its subgrid part must cover all `k` subgrid rows
or all `k` subgrid columns (else some cross is missed). -/
theorem stBlocks_hitting_card {k : ℕ} (hk : 0 < k) {H : Finset (Fin (k+1) × Fin (k+1))}
    (hH : ∀ s, (H ∩ stBlocks k s).Nonempty) : k + 2 ≤ H.card := by
  classical
  obtain ⟨r, hr⟩ := hH (Sum.inr true)
  obtain ⟨c, hc⟩ := hH (Sum.inr false)
  rw [Finset.mem_inter] at hr hc
  have hrrow : r.1 = Fin.last k := mem_stRow.mp hr.2
  obtain ⟨hccol, hclt⟩ := mem_stCol.mp hc.2
  set Hsub := H.filter (fun p => p.1.val < k ∧ p.2.val < k) with hHsubdef
  -- every cross is hit inside the subgrid
  have hcross : ∀ i j : Fin k, ∃ x ∈ Hsub, x.1 = i.castSucc ∨ x.2 = j.castSucc := by
    intro i j
    obtain ⟨x, hx⟩ := hH (Sum.inl (i, j))
    rw [Finset.mem_inter] at hx
    rcases mem_stCross.mp hx.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨x, Finset.mem_filter.mpr ⟨hx.1, ?_, h2⟩, Or.inl h1⟩
      rw [h1]; simpa using i.isLt
    · refine ⟨x, Finset.mem_filter.mpr ⟨hx.1, h2, ?_⟩, Or.inr h1⟩
      rw [h1]; simpa using j.isLt
  -- covering all subgrid rows or columns forces k subgrid vertices
  have hcount : ∀ (f : Fin (k+1) × Fin (k+1) → Fin (k+1)),
      (∀ i : Fin k, ∃ x ∈ Hsub, f x = i.castSucc) → k ≤ Hsub.card := by
    intro f hf
    have hsub2 : Finset.univ.image (Fin.castSucc (n := k)) ⊆ Hsub.image f := by
      intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨x, hx, hfx⟩ := hf i
      exact Finset.mem_image.mpr ⟨x, hx, hfx⟩
    calc k = (Finset.univ.image (Fin.castSucc (n := k))).card := by
          rw [Finset.card_image_of_injective _ (Fin.castSucc_injective k),
            Finset.card_univ, Fintype.card_fin]
      _ ≤ (Hsub.image f).card := Finset.card_le_card hsub2
      _ ≤ Hsub.card := Finset.card_image_le
  have hk_sub : k ≤ Hsub.card := by
    by_cases hrows : ∀ i : Fin k, ∃ x ∈ Hsub, x.1 = i.castSucc
    · exact hcount Prod.fst hrows
    · push_neg at hrows
      obtain ⟨i₀, hi₀⟩ := hrows
      refine hcount Prod.snd fun j => ?_
      obtain ⟨x, hx, hor⟩ := hcross i₀ j
      rcases hor with h | h
      · exact absurd h (hi₀ x hx)
      · exact ⟨x, hx, h⟩
  -- the row and column witnesses are outside the subgrid and distinct
  have hrne : r ∉ Hsub := by
    intro hmem
    have := (Finset.mem_filter.mp hmem).2.1
    rw [hrrow] at this
    simp at this
  have hcne : c ∉ Hsub := by
    intro hmem
    have := (Finset.mem_filter.mp hmem).2.2
    rw [hccol] at this
    simp at this
  have hrc : r ≠ c := fun h => by
    rw [← h, hrrow] at hclt
    simp at hclt
  have hsubset : insert r (insert c Hsub) ⊆ H := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hr.1
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hc.1
    · exact Finset.mem_of_mem_filter x hx
  have hcard : (insert r (insert c Hsub)).card = Hsub.card + 2 := by
    rw [Finset.card_insert_of_notMem (by
        rw [Finset.mem_insert]
        push_neg
        exact ⟨hrc, hrne⟩),
      Finset.card_insert_of_notMem hcne]
  calc k + 2 ≤ Hsub.card + 2 := by omega
    _ = (insert r (insert c Hsub)).card := hcard.symm
    _ ≤ H.card := Finset.card_le_card hsubset

/-- The blocks are nonempty, so `univ` is a transversal; combined with the counting bound,
the bramble order is at least `k + 2`. -/
theorem stBlocks_order (k : ℕ) (hk : 0 < k) : k + 2 ≤ order (stBlocks k) := by
  classical
  have hne : {n | ∃ H : Finset (Fin (k+1) × Fin (k+1)),
      IsHittingSet (stBlocks k) H ∧ H.card = n}.Nonempty := by
    refine ⟨Finset.univ.card, Finset.univ, fun s => ?_, rfl⟩
    match s with
    | Sum.inl (i, j) =>
        exact ⟨(i.castSucc, j.castSucc), Finset.mem_inter.mpr
          ⟨Finset.mem_univ _, mem_stCross.mpr (Or.inl ⟨rfl, by simpa using j.isLt⟩)⟩⟩
    | Sum.inr true =>
        exact ⟨(Fin.last k, 0), Finset.mem_inter.mpr
          ⟨Finset.mem_univ _, mem_stRow.mpr rfl⟩⟩
    | Sum.inr false =>
        exact ⟨(⟨0, by omega⟩, Fin.last k), Finset.mem_inter.mpr
          ⟨Finset.mem_univ _, mem_stCol.mpr ⟨rfl, hk⟩⟩⟩
  obtain ⟨H, hH, hcard⟩ := Nat.sInf_mem hne
  have h2 : k + 2 ≤ H.card := stBlocks_hitting_card hk hH
  rw [hcard] at h2
  exact h2

/-- **Exact grid stem-width floor.** Every path decomposition of the `(k+1) × (k+1)` grid graph
has a bag of size at least `k + 2` — meeting the sliding-window sweep (`≤ k + 2`) exactly, so
the stem optimum of the grid is pinned, not bracketed. Standard axioms only. -/
theorem grid_pathwidth_exact (k : ℕ) (hk : 0 < k)
    (L : LinearBags (Fin (k+1) × Fin (k+1))) (hlen : 0 < L.len)
    (hvint : ∀ (v : Fin (k+1) × Fin (k+1)) (a c j : Fin L.len),
      a ≤ j → j ≤ c → v ∈ L.bag a → v ∈ L.bag c → v ∈ L.bag j)
    (hedge : ∀ ⦃x y : Fin (k+1) × Fin (k+1)⦄, (gridGraph (k+1)).Adj x y →
      ∃ m, x ∈ L.bag m ∧ y ∈ L.bag m)
    (hcov : ∀ v : Fin (k+1) × Fin (k+1), ∃ i, v ∈ L.bag i) :
    k + 2 ≤ L.maxBag hlen := by
  haveI : Nonempty ((Fin k × Fin k) ⊕ Bool) := ⟨Sum.inr true⟩
  exact le_trans (stBlocks_order k hk)
    (pathwidth_ge_order_of_touching L hlen (gridGraph (k+1)) hvint hedge hcov (stBlocks k)
      (stBlocks_connected k) (stBlocks_touch k hk))

end FieldStemProof.GridExact
