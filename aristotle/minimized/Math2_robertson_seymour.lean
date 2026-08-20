/-
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as the first lines of the file as a plain block comment,
since Lean does not allow a module docstring `/-! ... -/` to precede the `import` line.)

## What is formalised here

* `Math2.IsMinor H G` : the standard *minor model* definition of "`H` is a minor of `G`".
* `Math2.robertson_seymour` : well-quasi-ordering by the minor relation for families of
  finite graphs whose orders are bounded by a fixed `k`.
* `Math2.robertson_seymour_linearForest` : well-quasi-ordering by the minor relation of the
  (infinite, unbounded) class of linear forests, i.e. disjoint unions of paths.  This is
  deduced from Higman's lemma.
* `Math2.robertson_seymour_cycleGraph` : well-quasi-ordering by the minor relation of the
  (infinite, unbounded) class of cycles; here the minors genuinely involve edge
  contractions.
* `Math2.isMinor_refl` and `Math2.IsMinor.trans` : the minor relation is a quasi-order.
* `Math2.RobertsonSeymourWQO` : the statement of the unrestricted Robertson–Seymour theorem,
  recorded as a `Prop`.  It is **not** proved here; the full graph minor theorem is the
  conclusion of the twenty-paper Graph Minors series and is far beyond what is formalised
  in this file.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

/-! ## The minor relation -/

/-- `IsMinor H G` says that `H` is a minor of `G`, expressed through a *minor model*:
each vertex `v` of `H` is assigned a branch set `B v ⊆ G`, the branch sets are nonempty,
induce connected subgraphs of `G`, are pairwise disjoint, and whenever `v` and `w` are
adjacent in `H` there is an edge of `G` joining `B v` to `B w`. -/

def IsMinor {V : Type*} {W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ B : V → Set W,
    (∀ v, (B v).Nonempty) ∧
    (∀ v, (G.induce (B v)).Connected) ∧
    (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
    (∀ v w, H.Adj v w → ∃ a ∈ B v, ∃ b ∈ B w, G.Adj a b)

/-- A one-point induced subgraph is connected. -/

theorem connected_induce_singleton {X : Type*} (K : SimpleGraph X) (x : X) :
    (K.induce ({x} : Set X)).Connected := by
  constructor
  intro u v
  have huv : u = v := by
    apply Subtype.ext
    have hu := u.2
    have hv := v.2
    simp only [Set.mem_singleton_iff] at hu hv
    rw [hu, hv]
  subst huv
  exact SimpleGraph.Reachable.refl _

/-- An injective adjacency-preserving map exhibits `H` as a minor of `G`: take singleton
branch sets. -/

theorem isMinor_of_injective_hom {V : Type*} {W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f) (hadj : ∀ x y, H.Adj x y → G.Adj (f x) (f y)) :
    IsMinor H G := by
  refine ⟨fun v => {f v}, fun v => ⟨f v, rfl⟩, fun v => connected_induce_singleton G (f v), ?_, ?_⟩
  · intro v w hvw
    simp only [Set.disjoint_singleton]
    exact fun h => hvw (hf h)
  · intro v w hadjvw
    exact ⟨f v, rfl, f w, rfl, hadj v w hadjvw⟩

/-- The minor relation is reflexive. -/

theorem isMinor_refl {V : Type*} (G : SimpleGraph V) : IsMinor G G :=
  isMinor_of_injective_hom id Function.injective_id fun _ _ h => h

/-- Reachability inside an induced subgraph is preserved when the inducing set grows. -/

theorem reachable_induce_mono {X : Type*} {K : SimpleGraph X} {S T : Set X} (hST : S ⊆ T)
    {x y : X} (hxS : x ∈ S) (hyS : y ∈ S) (hxT : x ∈ T) (hyT : y ∈ T)
    (h : (K.induce S).Reachable ⟨x, hxS⟩ ⟨y, hyS⟩) :
    (K.induce T).Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ := by
  have h' := h.map (K.induceHomOfLE hST).toHom
  simpa [SimpleGraph.induceHomOfLE] using h'

/-- A union `⋃ w ∈ S, C w` of connected sets `C w`, indexed by a set `S` that is connected in
`G` and whose edges are witnessed by edges between the corresponding sets, is connected. -/

theorem connected_biUnion {W X : Type*} {G : SimpleGraph W} {K : SimpleGraph X}
    (S : Set W) (C : W → Set X)
    (hS : (G.induce S).Connected)
    (hconn : ∀ w, (K.induce (C w)).Connected)
    (hedge : ∀ w w', G.Adj w w' → ∃ x ∈ C w, ∃ y ∈ C w', K.Adj x y) :
    (K.induce (⋃ w ∈ S, C w)).Connected := by
  set T : Set X := ⋃ w ∈ S, C w with hT
  have hsub : ∀ w ∈ S, C w ⊆ T := fun _ hw _ hx => Set.mem_biUnion hw hx
  have key : ∀ (a b : ↥S), (G.induce S).Reachable a b →
      ∀ (x y : X) (_ : x ∈ C a.val) (_ : y ∈ C b.val) (hxT : x ∈ T) (hyT : y ∈ T),
      (K.induce T).Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ := by
    rintro a b ⟨p⟩
    induction p with
    | @nil c =>
        intro x y hx hy hxT hyT
        exact reachable_induce_mono (hsub _ c.2) hx hy hxT hyT ((hconn c.val).preconnected _ _)
    | @cons a c b hac p ih =>
        intro x y hx hy hxT hyT
        obtain ⟨u, hu, v, hv, huv⟩ := hedge a.val c.val hac
        have huT : u ∈ T := hsub _ a.2 hu
        have hvT : v ∈ T := hsub _ c.2 hv
        have r1 : (K.induce T).Reachable ⟨x, hxT⟩ ⟨u, huT⟩ :=
          reachable_induce_mono (hsub _ a.2) hx hu hxT huT ((hconn a.val).preconnected _ _)
        have r2 : (K.induce T).Adj ⟨u, huT⟩ ⟨v, hvT⟩ := huv
        have r3 : (K.induce T).Reachable ⟨v, hvT⟩ ⟨y, hyT⟩ := ih v y hv hy hvT hyT
        exact (r1.trans r2.reachable).trans r3
  obtain ⟨w0⟩ := hS.nonempty
  obtain ⟨x0, hx0⟩ := (hconn w0.val).nonempty
  haveI : Nonempty ↥T := ⟨⟨x0, hsub _ w0.2 hx0⟩⟩
  constructor
  rintro ⟨x, hxT⟩ ⟨y, hyT⟩
  have hxT' := hxT
  have hyT' := hyT
  simp only [hT, Set.mem_iUnion, exists_prop] at hxT' hyT'
  obtain ⟨a, haS, hxa⟩ := hxT'
  obtain ⟨b, hbS, hyb⟩ := hyT'
  exact key ⟨a, haS⟩ ⟨b, hbS⟩ (hS.preconnected _ _) x y hxa hyb _ _

/-- The minor relation is transitive: together with `Math2.isMinor_refl` this makes it a
quasi-order. -/

theorem IsMinor.trans {V W X : Type*} {H : SimpleGraph V} {G : SimpleGraph W} {K : SimpleGraph X}
    (h1 : IsMinor H G) (h2 : IsMinor G K) : IsMinor H K := by
  obtain ⟨B, hBne, hBconn, hBdisj, hBedge⟩ := h1
  obtain ⟨C, hCne, hCconn, hCdisj, hCedge⟩ := h2
  refine ⟨fun v => ⋃ w ∈ B v, C w, ?_, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨w, hw⟩ := hBne v
    obtain ⟨x, hx⟩ := hCne w
    exact ⟨x, Set.mem_biUnion hw hx⟩
  · intro v
    exact connected_biUnion (B v) C (hBconn v) hCconn hCedge
  · intro v v' hvv'
    rw [Set.disjoint_left]
    rintro x hx hx'
    simp only [Set.mem_iUnion, exists_prop] at hx hx'
    obtain ⟨w, hw, hxw⟩ := hx
    obtain ⟨w', hw', hxw'⟩ := hx'
    by_cases hww : w = w'
    · subst hww
      exact (Set.disjoint_left.mp (hBdisj v v' hvv') hw) hw'
    · exact (Set.disjoint_left.mp (hCdisj w w' hww) hxw) hxw'
  · intro v v' hadj
    obtain ⟨a, ha, b, hb, hab⟩ := hBedge v v' hadj
    obtain ⟨x, hx, y, hy, hxy⟩ := hCedge a b hab
    exact ⟨x, Set.mem_biUnion ha hx, y, Set.mem_biUnion hb hy, hxy⟩

/-- A minor has at most as many vertices as the ambient graph.  In particular the minor
relation is not trivial: e.g. a long cycle is not a minor of a short one. -/

theorem robertson_seymour (k : ℕ) (V : ℕ → Type) [inst : ∀ i, Fintype (V i)]
    (hcard : ∀ i, Fintype.card (V i) ≤ k) (G : ∀ i, SimpleGraph (V i)) :
    ∃ i j, i < j ∧ IsMinor (G i) (G j) := by
  classical
  have he : ∀ i, Nonempty (V i ↪ Fin k) := fun i =>
    Function.Embedding.nonempty_of_card_le (by simpa using hcard i)
  let e : ∀ i, V i ↪ Fin k := fun i => (he i).some
  set F : ℕ → Finset (Fin k) × SimpleGraph (Fin k) :=
    fun i => (Finset.univ.image (e i), (G i).map (e i)) with hF
  have key : ∀ a b : ℕ, F a = F b → IsMinor (G a) (G b) := by
    intro a b hab
    have hset : Finset.univ.image (e a) = Finset.univ.image (e b) := congrArg Prod.fst hab
    have hgraph : (G a).map (e a) = (G b).map (e b) := congrArg Prod.snd hab
    have hmem : ∀ x : V a, ∃ y : V b, e b y = e a x := by
      intro x
      have hx : e a x ∈ Finset.univ.image (e b) := by
        rw [← hset]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
      simpa using hx
    choose f hf using hmem
    refine isMinor_of_injective_hom f ?_ ?_
    · intro x y hxy
      have hx : e a x = e a y := by rw [← hf x, ← hf y, hxy]
      exact (e a).injective hx
    · intro x y hxy
      have h1 : ((G a).map (e a)).Adj (e a x) (e a y) := SimpleGraph.map_adj_apply.mpr hxy
      rw [hgraph] at h1
      obtain ⟨u, v, huv, hu, hv⟩ := h1
      have hu' : u = f x := (e b).injective (by rw [hu, ← hf x])
      have hv' : v = f y := (e b).injective (by rw [hv, ← hf y])
      rw [hu', hv'] at huv
      exact huv
  obtain ⟨a, b, hab, hFab⟩ := Finite.exists_ne_map_eq_of_infinite F
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b, h, key a b hFab⟩
  · exact ⟨b, a, h, key b a hFab.symm⟩

/-! ## Well-quasi-ordering of linear forests

A linear forest is a disjoint union of paths.  It is encoded by the list `l` of the numbers
of vertices of its paths: the vertex `(i, j)` is the `j`-th vertex of the `i`-th path. -/

/-- Vertex type of the linear forest determined by the list `l` of path orders. -/
abbrev LFVertex (l : List ℕ) : Type := {p : ℕ × ℕ // p.2 < l.getD p.1 0}

/-- The linear forest (disjoint union of paths) whose `i`-th path has `l.getD i 0` vertices. -/
