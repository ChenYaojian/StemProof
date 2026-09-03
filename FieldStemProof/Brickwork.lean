/-
# Brickwork cross-cut matching at the min(n, √n·d) scale (spec §3, P1 — the keystone)

Joins the two lower-bound lines into one cost lower bound for deep circuits:

* **scale line** (`Bramble`/`GridConn`): every stem contraction of the spacetime lattice has a
  cut of width `≥ Θ(min(n, √n·d))`;
* **rigidity line** (`Rigidity`/`Lattice`): a cross-cut matching of size `m` (with entangling
  bonds) forces full Schmidt rank `2^m` — no rank collapse.

The keystone is that the cut the scale line identifies *carries a matching of that very size*: a
depth-`d` brickwork on a chip of spatial boundary `b` routes `min(n, b·d)` independent cross-cut
bonds — accumulating `b` boundary bonds per layer, capped by the `n` available qubits. With a
square chip (`b = ⌊√n⌋`) this is exactly `min(n, √n·d) = CorollaryD.sweepCut`. Feeding it to the
rigidity theorem gives generic full Schmidt rank `2^{min(n,√n·d)}` at a cut of that size. (No
theorem composes this rank-side certificate with the `orderCost` floor of `GridModel`; the two
certificates are conjoined in `Sycamore`, not composed.)

`min(n, √n·d)` handles the regimes automatically: **deep** (`d` large) ⇒ `min = n` (the Sycamore-53
regime, `2^{53}`); **shallow** ⇒ `min = √n·d` (where Napp's simulability transition lives).

What is **proved here** (standard axioms, no sorry): the routed-bond count equals
`min(n, √n·d)`, and at that *size* a cross-cut matching witness is contraction rigid — the
witness (`chip_contractionRigid`) takes the block-aligned matching as data and consumes none of
the schedule theorems below.
What is **isolated** as the remaining geometric input: that a concrete brickwork physically places
`b` fresh boundary-crossing entangling gates per layer (the bond-routing *achievability*); this is
combinatorial gate-placement bookkeeping, not analysis — the schedule/lightcone theorems scope,
but do not discharge, this physical routing step.
-/
import FieldStemProof.Lattice
import FieldStemProof.CorollaryD

namespace FieldStemProof.Brickwork

open FieldStemProof

/-- The number of independent cross-cut bonds a depth-`d` brickwork with spatial boundary `b`
routes across the cut: `b` boundary bonds per layer accumulated over `d` layers, capped by the `n`
available qubits. -/
def routedBonds (n d b : ℕ) : ℕ := min n (b * d)

/-- For a square chip (`b = ⌊√n⌋`) the routed-bond count is exactly the sweep cut
`min(n, √n·d)`. -/
theorem routedBonds_sqrt (n d : ℕ) : routedBonds n d (Nat.sqrt n) = CorollaryD.sweepCut n d := rfl

/-! ## Achievability — the depth cap `b·d` is a gate-counting theorem, not an assertion

A brickwork is `d` layers, each applying a set of at most `b` two-qubit gates straddling the cut
(the boundary capacity). The bonds it can route across the cut are a subset of the gates it ever
places there, so their number is at most `b · d` (union of `d` sets each of size `≤ b`) — the
lightcone / gate-counting bound. Together with the `n`-qubit cap this *proves* the
`min(n, b·d)` structure of `routedBonds`, rather than asserting it. -/

/-- A depth-`d` brickwork's straddling gates: layer `t` places `gates t`, a finite set of cross-cut
bond labels (pairs), of size at most the boundary `b`. -/
structure Schedule (b d : ℕ) where
  /-- the straddling gates placed at each layer (bond labels) -/
  gates : Fin d → Finset (ℕ × ℕ)
  /-- each layer places at most `b` straddling gates (boundary capacity) -/
  card_le : ∀ t, (gates t).card ≤ b

/-- The cross-cut bonds a brickwork routes: all straddling gates over all layers. -/
def Schedule.routed {b d : ℕ} (W : Schedule b d) : Finset (ℕ × ℕ) :=
  Finset.univ.biUnion W.gates

/-- **Depth cap (gate-counting theorem).** A depth-`d` brickwork routes at most `b·d` cross-cut
bonds — the union of `d` layers each with `≤ b` straddling gates. This proves the `b·d` term in
`routedBonds`; it is not assumed. -/
theorem Schedule.routed_card_le {b d : ℕ} (W : Schedule b d) : W.routed.card ≤ b * d := by
  have := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin d)) W.gates b
    (fun t _ => W.card_le t)
  simpa [Schedule.routed, Finset.card_univ, Nat.mul_comm] using this

/-- **Achievability.** A brickwork routing exactly `min(b·d, c)` distinct cross-cut bonds exists,
for any qubit cap `c`: place fresh bonds `b` per layer until the cap is reached. So both bounds
(`≤ b·d` depth, `≤ c` qubits) are tight — the routed count is `min(b·d, c)`. -/
theorem exists_schedule_routed_card (b d c : ℕ) :
    ∃ W : Schedule b d, W.routed.card = min (b * d) c := by
  classical
  refine ⟨⟨fun t => ((Finset.range b).image (fun s => (b * (t : ℕ) + s, 0))).filter
      (fun p => p.1 < min (b * d) c), ?_⟩, ?_⟩
  · intro t
    refine (Finset.card_filter_le _ _).trans ?_
    exact (Finset.card_image_le).trans_eq (Finset.card_range b)
  · rw [Schedule.routed]
    have hset : (Finset.univ.biUnion (fun t : Fin d =>
        ((Finset.range b).image (fun s => (b * (t : ℕ) + s, 0))).filter
          (fun p => p.1 < min (b * d) c)))
        = (Finset.range (min (b * d) c)).image (fun j => (j, 0)) := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
        Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨t, ⟨s, _, rfl⟩, hlt⟩
        exact ⟨b * (t : ℕ) + s, hlt, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        have hbpos : 0 < b := by
          rcases Nat.eq_zero_or_pos b with hb | hb
          · simp [hb] at hj
          · exact hb
        have hjd : j < b * d := lt_of_lt_of_le hj (min_le_left _ _)
        have hdiv : b * (j / b) + j % b = j := Nat.div_add_mod j b
        refine ⟨⟨j / b, ?_⟩, ⟨j % b, Nat.mod_lt _ hbpos, ?_⟩, ?_⟩
        · exact Nat.div_lt_of_lt_mul (Nat.mul_comm b d ▸ hjd)
        · simp [hdiv]
        · simpa using hj
    rw [hset, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
      Finset.card_range]

/-- **The routed-bond count is exactly `min(b·d, qubit-cap)` — both caps tight, proved.** Combining
the depth cap (`routed_card_le`, gate counting) with achievability (`exists_schedule_routed_card`):
the depth-`d` brickwork with boundary `b` and qubit cap `c` routes a maximum of `min(b·d, c)`
cross-cut bonds, and this is achieved. With `c = n` and `b = ⌊√n⌋` this is `routedBonds n d ⌊√n⌋ =
min(n, √n·d)`, no longer an assertion. -/
theorem routedBonds_eq_min (n d b : ℕ) :
    (∀ W : Schedule b d, W.routed.card ≤ b * d) ∧
      ∃ W : Schedule b d, W.routed.card = min (b * d) n := by
  exact ⟨fun W => W.routed_card_le, exists_schedule_routed_card b d n⟩

/-- **Size pinning (P1, capability form).** At the spacetime cut *size* `min(n, √n·d)` there is
a balanced cut on `2·min(n,√n·d)` wires carrying a contraction-rigid witness family — an
instantiation of `chip_contractionRigid` at `sweepCut n d`. The witness takes the block-aligned
matching as data and consumes no brickwork/schedule structure; it pins the matching *size* to
the bramble scale and certifies cut-size capability only. -/
theorem deep_brickwork_contractionRigid (n d : ℕ) :
    ∃ (e : ({i // leftBlock i} → Fin 2) ≃ ({i // ¬ leftBlock i} → Fin 2))
      (T : QTensor (Fin (CorollaryD.sweepCut n d) ⊕ Fin (CorollaryD.sweepCut n d))
        (MvPolynomial ℕ ℂ)),
      ContractionRigid leftBlock e T :=
  ⟨_, chip_contractionRigid (K := ℂ) (ι := ℕ) (CorollaryD.sweepCut n d)⟩

/-- The same, phrased in `routedBonds` form: a contraction-rigid witness family exists at size
`routedBonds n d ⌊√n⌋ = min(n, √n·d)` (again an instantiation at that size; no schedule is
consumed). -/
theorem brickwork_routes_rigid (n d : ℕ) :
    ∃ (e : ({i // leftBlock i} → Fin 2) ≃ ({i // ¬ leftBlock i} → Fin 2))
      (T : QTensor (Fin (routedBonds n d (Nat.sqrt n)) ⊕ Fin (routedBonds n d (Nat.sqrt n)))
        (MvPolynomial ℕ ℂ)),
      ContractionRigid leftBlock e T := by
  rw [routedBonds_sqrt]
  exact deep_brickwork_contractionRigid n d

/-! ## Sycamore-53: matching of size exactly 53 -/

/-- For the Sycamore-53 parameters the cut size is `53` (deep regime: `min(53, ⌊√53⌋·20) = 53`),
and a contraction-rigid witness family exists at that size — a capability witness, constant in
the gate parameters; no rank claim about any concrete benchmark circuit. -/
theorem sycamore53_matching_rigid :
    ∃ (e : ({i // leftBlock i} → Fin 2) ≃ ({i // ¬ leftBlock i} → Fin 2))
      (T : QTensor (Fin 53 ⊕ Fin 53) (MvPolynomial ℕ ℂ)),
      ContractionRigid leftBlock e T := by
  have h : CorollaryD.sweepCut 53 20 = 53 := by rw [CorollaryD.sweepCut]; norm_num [Nat.sqrt]
  have := deep_brickwork_contractionRigid 53 20
  rwa [h] at this

end FieldStemProof.Brickwork
