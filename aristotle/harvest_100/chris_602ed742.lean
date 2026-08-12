import Mathlib

/-!
# Orbits of a permutation

Minimal theory of orbits of a permutation of a finite type, as needed for face counting in a
combinatorial embedding of a graph: a permutation all of whose orbits have at least `n` elements
has at most `#α / n` orbits.
-/

namespace Frontier

variable {α : Type*}

/-- The setoid on `α` whose equivalence classes are the orbits of the permutation `f`. -/
def orbitSetoid (f : Equiv.Perm α) : Setoid α where
  r a b := ∃ k : ℤ, (f ^ k) a = b
  iseqv :=
    { refl := fun a => ⟨0, by simp⟩
      symm := by
        rintro a b ⟨k, rfl⟩
        exact ⟨-k, by simp [← Equiv.Perm.mul_apply]⟩
      trans := by
        rintro a b c ⟨k, rfl⟩ ⟨l, rfl⟩
        exact ⟨l + k, by simp [zpow_add, Equiv.Perm.mul_apply]⟩ }

/-- The number of orbits of a permutation. -/
noncomputable def numOrbits (f : Equiv.Perm α) : ℕ := Nat.card (Quotient (orbitSetoid f))

/-- If no nontrivial power `f ^ i`, `0 < i < n`, fixes any point -- i.e. every orbit of `f` has at
least `n` elements -- then `f` has at most `#α / n` orbits. -/
theorem numOrbits_mul_le [Finite α] (f : Equiv.Perm α) (n : ℕ)
    (h : ∀ (a : α) (i : ℕ), 0 < i → i < n → (f ^ i) a ≠ a) :
    n * numOrbits f ≤ Nat.card α := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fintype (Quotient (orbitSetoid f)) := Quotient.fintype _
  have key : ∀ b : Quotient (orbitSetoid f),
      n ≤ (Finset.univ.filter (fun a : α => Quotient.mk (orbitSetoid f) a = b)).card := by
    intro b
    obtain ⟨a, rfl⟩ := Quotient.exists_rep b
    have hne : ∀ i j : ℕ, i < j → j < n → (f ^ i) a ≠ (f ^ j) a := by
      intro i j hlt hj hij
      have hcomp : (f ^ i) ((f ^ (j - i)) a) = (f ^ j) a := by
        rw [← Equiv.Perm.mul_apply, ← pow_add]
        congr 2
        omega
      exact h a (j - i) (by omega) (by omega) ((f ^ i).injective (hcomp.trans hij.symm))
    have hinj : Set.InjOn (fun i : ℕ => (f ^ i) a) (Finset.range n) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      simp only at hij
      by_contra hij'
      rcases lt_or_gt_of_ne hij' with hlt | hlt
      · exact hne i j hlt hj hij
      · exact hne j i hlt hi hij.symm
    have hsub : ((Finset.range n).image (fun i : ℕ => (f ^ i) a)) ⊆
        Finset.univ.filter (fun x : α => Quotient.mk (orbitSetoid f) x = Quotient.mk _ a) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, _, rfl⟩ := hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply Quotient.sound
      refine ⟨-(i : ℤ), ?_⟩
      rw [← Equiv.Perm.mul_apply, ← zpow_natCast f i, ← zpow_add]
      simp
    calc n = ((Finset.range n).image (fun i : ℕ => (f ^ i) a)).card := by
            rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ _ := Finset.card_le_card hsub
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun a : α => Quotient.mk (orbitSetoid f) a) (s := Finset.univ)
    (t := Finset.univ) (fun x _ => Finset.mem_univ _)
  simp only [numOrbits, Nat.card_eq_fintype_card, ← Finset.card_univ]
  rw [hfib]
  calc n * (Finset.univ : Finset (Quotient (orbitSetoid f))).card
      = ∑ _b : Quotient (orbitSetoid f), n := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun b _ => key b)

/-- If every orbit of `f` has at least three elements then `f` has at most `#α / 3` orbits. -/
theorem three_mul_numOrbits_le [Finite α] (f : Equiv.Perm α)
    (h1 : ∀ a : α, f a ≠ a) (h2 : ∀ a : α, f (f a) ≠ a) :
    3 * numOrbits f ≤ Nat.card α := by
  refine numOrbits_mul_le f 3 ?_
  intro a i hi hi3
  interval_cases i
  · simpa using h1 a
  · simpa [pow_two, Equiv.Perm.mul_apply] using h2 a

/-- If every orbit of `f` has at least four elements then `f` has at most `#α / 4` orbits. -/
theorem four_mul_numOrbits_le [Finite α] (f : Equiv.Perm α)
    (h1 : ∀ a : α, f a ≠ a) (h2 : ∀ a : α, f (f a) ≠ a) (h3 : ∀ a : α, f (f (f a)) ≠ a) :
    4 * numOrbits f ≤ Nat.card α := by
  refine numOrbits_mul_le f 4 ?_
  intro a i hi hi4
  interval_cases i
  · simpa using h1 a
  · simpa [pow_two, Equiv.Perm.mul_apply] using h2 a
  · simpa [pow_succ, Equiv.Perm.mul_apply] using h3 a

/-- A permutation acting transitively on a nonempty type has exactly one orbit. -/
theorem numOrbits_eq_one [Nonempty α] (f : Equiv.Perm α)
    (h : ∀ a b : α, ∃ k : ℤ, (f ^ k) a = b) : numOrbits f = 1 := by
  have hs : Subsingleton (Quotient (orbitSetoid f)) := by
    constructor
    intro a b
    induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
    exact Quotient.sound (h a b)
  have hn : Nonempty (Quotient (orbitSetoid f)) := ⟨Quotient.mk _ (Classical.arbitrary α)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hs, hn⟩

end Frontier

import RequestProject.Orbits

/-!
# Combinatorial planarity, Euler's formula and the degree bound

A *combinatorial embedding* (rotation system) of a simple graph `G` consists of a permutation
`rot` of the darts (directed edges) of `G` which fixes the source of every dart and acts
transitively on the darts emanating from any fixed vertex; `rot` records the cyclic order in
which the edges around a vertex are met when walking around that vertex in the surface.

The *faces* of such an embedding are the orbits of `rot ∘ symm`, where `symm` reverses a dart.
A connected graph with at least one edge, embedded in a closed orientable surface of genus `g`,
satisfies `#V - #E + #F = 2 - 2g`, so the embedding is a plane (equivalently, sphere) embedding
exactly when the Euler characteristic attains its maximal value `2`. Summing over the `c`
connected components of a graph -- and correcting for isolated vertices, which carry no dart and
hence contribute no orbit -- gives the definition `Frontier.IsPlanar` below: `G` is planar when
some rotation system satisfies `#V - #E + #F + #(isolated vertices) ≥ 2c`.

From this we derive, by the classical face-counting argument, the bound `#E ≤ 3 #V - 6`, its
triangle-free refinement `#E ≤ 2 #V - 4`, and the existence of a vertex of small degree in any
nonempty planar graph.
-/

namespace Frontier

open SimpleGraph

variable {V : Type*}

instance instFiniteDart [Finite V] (G : SimpleGraph V) : Finite G.Dart :=
  Finite.of_injective (fun d => d.toProd) (fun _ _ h => SimpleGraph.Dart.ext _ _ h)

/-- Reversal of darts, as a permutation of the darts of `G`. -/
def symmPerm (G : SimpleGraph V) : Equiv.Perm G.Dart :=
  Function.Involutive.toPerm SimpleGraph.Dart.symm SimpleGraph.Dart.symm_symm

@[simp] lemma symmPerm_apply (G : SimpleGraph V) (d : G.Dart) : symmPerm G d = d.symm := rfl

/-- A rotation system (combinatorial embedding) of a simple graph: a permutation of the darts
preserving the source vertex and acting transitively on the darts with a given source. -/
structure RotationSystem (G : SimpleGraph V) where
  /-- The rotation permutation: the cyclic order of the darts around each vertex. -/
  rot : Equiv.Perm G.Dart
  /-- The rotation preserves the source vertex of a dart. -/
  rot_fst : ∀ d : G.Dart, (rot d).fst = d.fst
  /-- The rotation acts transitively on the set of darts with a given source vertex. -/
  rot_transitive : ∀ d d' : G.Dart, d.fst = d'.fst → ∃ k : ℤ, (rot ^ k) d = d'

namespace RotationSystem

variable {G : SimpleGraph V}

/-- The number of faces of a combinatorial embedding: the number of orbits of `rot ∘ symm`. -/
noncomputable def faceCount (R : RotationSystem G) : ℕ := numOrbits (R.rot * symmPerm G)

end RotationSystem

/-- The number of isolated vertices of `G`. An isolated vertex carries no dart, hence lies on no
face in the sense of `faceCount`, although in a drawing it does lie inside a face; the Euler
characteristic below is corrected accordingly. -/
noncomputable def isolatedCount (G : SimpleGraph V) : ℕ := Nat.card {v : V // ∀ w, ¬ G.Adj v w}

/-- A finite simple graph is *planar* if it admits a combinatorial embedding (rotation system)
whose corrected Euler characteristic `#V - #E + #F + #(isolated vertices)` is at least twice the
number of connected components of `G`.

Justification of the definition. The orbits of `rot ∘ symm` are the faces of the embeddings of
the individual connected components of `G` (isolated vertices contribute no orbit, whence the
correction term). A connected graph with at least one edge embedded in a closed orientable
surface of genus `g` satisfies `#V - #E + #F = 2 - 2g ≤ 2`, with equality exactly when `g = 0`,
i.e. when the component is drawn in the sphere -- equivalently, in the plane. Summing over the
`c` components, `#V - #E + #F + #(isolated vertices) = 2c - 2 ∑ gᵢ`, which is `≥ 2c` if and only
if every component has genus `0`, i.e. if and only if `G` is planar. -/
def IsPlanar [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ R : RotationSystem G,
    2 * (Nat.card G.ConnectedComponent : ℤ) ≤ (Fintype.card V : ℤ) - (Nat.card G.edgeSet : ℤ)
      + (R.faceCount : ℤ) + (isolatedCount G : ℤ)

section

variable [Fintype V] {G : SimpleGraph V}

/-- If every vertex has at least two neighbours, the rotation has no fixed dart. -/
theorem RotationSystem.rot_apply_ne (R : RotationSystem G)
    (hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v)) (d : G.Dart) : R.rot d ≠ d := by
  intro hd
  have hnt : Nontrivial (G.neighborSet d.toProd.1) :=
    Finite.one_lt_card_iff_nontrivial.mp (hdeg _)
  obtain ⟨x, hx⟩ := exists_ne (⟨d.toProd.2, d.adj⟩ : G.neighborSet d.toProd.1)
  set d' : G.Dart := ⟨(d.toProd.1, x.1), x.2⟩ with hd'
  obtain ⟨k, hk⟩ := R.rot_transitive d d' rfl
  rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hd k] at hk
  apply hx
  apply Subtype.ext
  have := congrArg (fun y : G.Dart => y.toProd.2) hk
  simpa [hd'] using this.symm

omit [Fintype V] in
/-- No face of an embedding of a simple graph has a single side: this would be a loop. -/
theorem face_apply_ne (R : RotationSystem G) (d : G.Dart) :
    (R.rot * symmPerm G) d ≠ d := by
  intro h
  have h1 : (R.rot (d.symm)).fst = d.fst := by
    rw [show R.rot (d.symm) = (R.rot * symmPerm G) d from rfl, h]
  rw [R.rot_fst] at h1
  exact SimpleGraph.Dart.fst_ne_snd d h1.symm

omit [Fintype V] in
/-- No face of an embedding of a simple graph has exactly two sides: this would either be a
double edge or a vertex fixed by the rotation. -/
theorem face_apply_apply_ne (R : RotationSystem G) (hfix : ∀ d : G.Dart, R.rot d ≠ d)
    (d : G.Dart) : (R.rot * symmPerm G) ((R.rot * symmPerm G) d) ≠ d := by
  intro h
  have h2 : R.rot ((R.rot (d.symm)).symm) = d := h
  have hfst : (R.rot (d.symm)).toProd.1 = d.toProd.2 := by rw [R.rot_fst]; rfl
  have hsnd : (R.rot (d.symm)).toProd.2 = d.toProd.1 := by
    have h3 : (R.rot ((R.rot (d.symm)).symm)).toProd.1 = d.toProd.1 := by rw [h2]
    rwa [R.rot_fst] at h3
  have key : R.rot (d.symm) = d.symm := by
    apply SimpleGraph.Dart.ext
    rw [SimpleGraph.Dart.symm_toProd]
    exact Prod.ext hfst hsnd
  exact hfix d.symm key

omit [Fintype V] in
/-- Three mutually adjacent vertices form a triangle. -/
theorem not_cliqueFree_three (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    ¬ G.CliqueFree 3 := by
  classical
  intro h
  refine h {a, b, c} ?_
  constructor
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      simp_all [G.symm hab, G.symm hbc, G.symm hca]
  · have h1 : a ≠ b := hab.ne
    have h2 : b ≠ c := hbc.ne
    have h3 : a ≠ c := (hca.ne).symm
    rw [Finset.card_insert_of_notMem (by simp_all), Finset.card_insert_of_notMem (by simp_all)]
    simp

omit [Fintype V] in
/-- In a triangle-free graph, no face of an embedding has exactly three sides. -/
theorem face_apply_three_ne (R : RotationSystem G) (htf : G.CliqueFree 3) (d : G.Dart) :
    (R.rot * symmPerm G) ((R.rot * symmPerm G) ((R.rot * symmPerm G) d)) ≠ d := by
  intro h
  set f := R.rot * symmPerm G with hf
  have hfst : ∀ e : G.Dart, (f e).toProd.1 = e.toProd.2 := by
    intro e
    rw [hf]
    show (R.rot (e.symm)).toProd.1 = _
    rw [R.rot_fst]
    rfl
  have h1 : G.Adj d.toProd.1 d.toProd.2 := d.adj
  have h2 : G.Adj d.toProd.2 (f d).toProd.2 := by
    have := (f d).adj
    rwa [hfst d] at this
  have h3 : G.Adj (f d).toProd.2 d.toProd.1 := by
    have hadj := (f (f d)).adj
    rw [hfst (f d)] at hadj
    have hlast : (f (f d)).toProd.2 = d.toProd.1 := by
      have := hfst (f (f d))
      rw [h] at this
      exact this.symm
    rwa [hlast] at hadj
  exact not_cliqueFree_three _ _ _ h1 h2 h3 htf

/-- Twice the number of edges is the number of darts. -/
theorem card_dart_eq (G : SimpleGraph V) : Nat.card G.Dart = 2 * Nat.card G.edgeSet := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    SimpleGraph.dart_card_eq_twice_card_edges]

omit [Fintype V] in
/-- If every vertex has a neighbour there are no isolated vertices. -/
theorem isolatedCount_eq_zero (hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v)) :
    isolatedCount G = 0 := by
  have : IsEmpty {v : V // ∀ w, ¬ G.Adj v w} := by
    constructor
    rintro ⟨v, hv⟩
    have hpos : 0 < Nat.card (G.neighborSet v) := lt_of_lt_of_le (by norm_num) (hdeg v)
    obtain ⟨w, hw⟩ := (Nat.card_pos_iff.mp hpos).1
    exact hv w hw
  simp [isolatedCount]

/-- For a planar graph with no isolated vertices, Euler's inequality `#V - #E + #F ≥ 2` holds
for some rotation system. -/
theorem exists_rotationSystem_euler [Nonempty V] (hp : IsPlanar G)
    (hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v)) :
    ∃ R : RotationSystem G,
      2 ≤ (Fintype.card V : ℤ) - (Nat.card G.edgeSet : ℤ) + (R.faceCount : ℤ) := by
  obtain ⟨R, hE⟩ := hp
  refine ⟨R, ?_⟩
  have hc : 1 ≤ Nat.card G.ConnectedComponent := by
    have : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk (Classical.arbitrary V)⟩
    exact Nat.card_pos
  have hc' : (1 : ℤ) ≤ (Nat.card G.ConnectedComponent : ℤ) := by exact_mod_cast hc
  rw [isolatedCount_eq_zero hdeg] at hE
  push_cast at hE
  linarith

/-- **Euler's edge bound**: a planar simple graph in which every vertex has at least two
neighbours has at most `3 #V - 6` edges. -/
theorem planar_edge_bound [Nonempty V] (hp : IsPlanar G)
    (hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v)) :
    (Nat.card G.edgeSet : ℤ) ≤ 3 * (Fintype.card V : ℤ) - 6 := by
  obtain ⟨R, hE⟩ := exists_rotationSystem_euler hp hdeg
  have hfix := R.rot_apply_ne hdeg
  have h3 : 3 * R.faceCount ≤ Nat.card G.Dart :=
    three_mul_numOrbits_le _ (face_apply_ne R) (face_apply_apply_ne R hfix)
  rw [card_dart_eq] at h3
  have h3' : (3 : ℤ) * (R.faceCount : ℤ) ≤ 2 * (Nat.card G.edgeSet : ℤ) := by exact_mod_cast h3
  linarith

/-- **Euler's edge bound for triangle-free graphs**: a triangle-free planar simple graph in which
every vertex has at least two neighbours has at most `2 #V - 4` edges. -/
theorem planar_trianglefree_edge_bound [Nonempty V] (hp : IsPlanar G) (htf : G.CliqueFree 3)
    (hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v)) :
    (Nat.card G.edgeSet : ℤ) ≤ 2 * (Fintype.card V : ℤ) - 4 := by
  obtain ⟨R, hE⟩ := exists_rotationSystem_euler hp hdeg
  have hfix := R.rot_apply_ne hdeg
  have h4 : 4 * R.faceCount ≤ Nat.card G.Dart :=
    four_mul_numOrbits_le _ (face_apply_ne R) (face_apply_apply_ne R hfix)
      (face_apply_three_ne R htf)
  rw [card_dart_eq] at h4
  have h4' : (4 : ℤ) * (R.faceCount : ℤ) ≤ 2 * (Nat.card G.edgeSet : ℤ) := by exact_mod_cast h4
  linarith

/-- The handshake inequality: if every vertex has degree at least `m` then `m #V ≤ 2 #E`. -/
theorem mul_card_le_two_mul_card_edgeSet [DecidableRel G.Adj] (m : ℕ)
    (h : ∀ v : V, m ≤ G.degree v) :
    (m : ℤ) * (Fintype.card V : ℤ) ≤ 2 * (Nat.card G.edgeSet : ℤ) := by
  have hsum : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  have hlow : m * Fintype.card V ≤ ∑ v : V, G.degree v := by
    calc m * Fintype.card V = ∑ _v : V, m := by simp [mul_comm]
      _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum (fun v _ => h v)
  have hEcard : (G.edgeFinset.card : ℤ) = (Nat.card G.edgeSet : ℤ) := by
    rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  have hlow' : (m : ℤ) * (Fintype.card V : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) := by
    have : ((m * Fintype.card V : ℕ) : ℤ) ≤ ((2 * G.edgeFinset.card : ℕ) : ℤ) := by
      exact_mod_cast hsum ▸ hlow
    push_cast at this ⊢
    linarith
  rwa [hEcard] at hlow'

/-- Degrees and cardinalities of neighbour sets agree. -/
theorem card_neighborSet_eq_degree' [DecidableRel G.Adj] (v : V) :
    Nat.card (G.neighborSet v) = G.degree v := by
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]

/-- **Every nonempty planar graph has a vertex of degree at most five.** -/
theorem exists_degree_le_five [Nonempty V] [DecidableRel G.Adj] (hp : IsPlanar G) :
    ∃ v : V, G.degree v ≤ 5 := by
  by_contra hcon
  push_neg at hcon
  have hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v) := fun v => by
    rw [card_neighborSet_eq_degree']
    exact le_trans (by norm_num) (hcon v)
  have hbound := planar_edge_bound hp hdeg
  have hlow := mul_card_le_two_mul_card_edgeSet 6 (fun v => hcon v)
  have hpos : (0 : ℤ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  push_cast at hlow
  linarith

/-- **A nonempty planar graph on at most eleven vertices has a vertex of degree at most four.**
(The bound `11` is sharp: the icosahedron is a `5`-regular planar graph on twelve vertices.) -/
theorem exists_degree_le_four_of_card_le_eleven [Nonempty V] [DecidableRel G.Adj]
    (hp : IsPlanar G) (hcard : Fintype.card V ≤ 11) : ∃ v : V, G.degree v ≤ 4 := by
  by_contra hcon
  push_neg at hcon
  have hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v) := fun v => by
    rw [card_neighborSet_eq_degree']
    exact le_trans (by norm_num) (hcon v)
  have hbound := planar_edge_bound hp hdeg
  have hlow := mul_card_le_two_mul_card_edgeSet 5 (fun v => hcon v)
  have hcard' : (Fintype.card V : ℤ) ≤ 11 := by exact_mod_cast hcard
  push_cast at hlow
  linarith

/-- **Every nonempty triangle-free planar graph has a vertex of degree at most three.** -/
theorem exists_degree_le_three [Nonempty V] [DecidableRel G.Adj] (hp : IsPlanar G)
    (htf : G.CliqueFree 3) : ∃ v : V, G.degree v ≤ 3 := by
  by_contra hcon
  push_neg at hcon
  have hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v) := fun v => by
    rw [card_neighborSet_eq_degree']
    exact le_trans (by norm_num) (hcon v)
  have hbound := planar_trianglefree_edge_bound hp htf hdeg
  have hlow := mul_card_le_two_mul_card_edgeSet 4 (fun v => hcon v)
  have hpos : (0 : ℤ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  push_cast at hlow
  linarith

end

section Examples

instance instIsEmptyBotDart {α : Type*} : IsEmpty ((⊥ : SimpleGraph α).Dart) := ⟨fun d => d.adj⟩

/-- The (empty) rotation system on an edgeless graph. -/
def botRot {α : Type*} : RotationSystem (⊥ : SimpleGraph α) where
  rot := 1
  rot_fst := fun _ => rfl
  rot_transitive := fun d _ _ => (d.adj).elim

/-- Non-vacuity check: an edgeless graph is planar (with equality in Euler's formula: each of its
`n` vertices is a component, contributing one vertex and one face). -/
theorem isPlanar_bot {α : Type*} [Fintype α] : IsPlanar (⊥ : SimpleGraph α) := by
  refine ⟨botRot, ?_⟩
  have hF : (botRot (α := α)).faceCount = 0 := by
    have : IsEmpty (Quotient (orbitSetoid
        ((botRot (α := α)).rot * symmPerm (⊥ : SimpleGraph α)))) := by
      constructor
      intro q
      induction q using Quotient.inductionOn with | _ d => exact d.adj.elim
    simp [RotationSystem.faceCount, numOrbits]
  have hE : Nat.card ((⊥ : SimpleGraph α).edgeSet) = 0 := by simp
  have hI : isolatedCount (⊥ : SimpleGraph α) = Nat.card α := by
    simp only [isolatedCount]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv (by simp))
  have hC : Nat.card ((⊥ : SimpleGraph α).ConnectedComponent) = Nat.card α := by
    refine (Nat.card_eq_of_bijective
      (fun a : α => SimpleGraph.connectedComponentMk (⊥ : SimpleGraph α) a) ?_).symm
    constructor
    · intro a b h
      exact SimpleGraph.reachable_bot.mp (SimpleGraph.ConnectedComponent.eq.mp h)
    · intro c
      induction c using SimpleGraph.ConnectedComponent.ind with | _ a => exact ⟨a, rfl⟩
  rw [hF, hE, hI, hC, Nat.card_eq_fintype_card]
  push_cast
  ring_nf
  omega

/-- The rotation system of the graph with a single edge. -/
def K2Rot : RotationSystem (⊤ : SimpleGraph (Fin 2)) where
  rot := 1
  rot_fst := fun _ => rfl
  rot_transitive := by
    intro d d' hdd
    refine ⟨0, ?_⟩
    simp only [zpow_zero, Equiv.Perm.coe_one, id_eq]
    apply SimpleGraph.Dart.ext
    have hd : d.toProd = (0, 1) ∨ d.toProd = (1, 0) := by
      obtain ⟨⟨x, y⟩, h⟩ := d
      have hne : x ≠ y := h
      fin_cases x <;> fin_cases y <;> simp_all
    have hd' : d'.toProd = (0, 1) ∨ d'.toProd = (1, 0) := by
      obtain ⟨⟨x, y⟩, h⟩ := d'
      have hne : x ≠ y := h
      fin_cases x <;> fin_cases y <;> simp_all
    have hfst : d.toProd.1 = d'.toProd.1 := hdd
    rcases hd with h1 | h1 <;> rcases hd' with h2 | h2 <;> rw [h1, h2] <;> rw [h1, h2] at hfst <;>
      simp_all

/-- Non-vacuity check: the graph with a single edge is planar, with one face. -/
theorem isPlanar_K2 : IsPlanar (⊤ : SimpleGraph (Fin 2)) := by
  classical
  refine ⟨K2Rot, ?_⟩
  have hc : Nat.card ((⊤ : SimpleGraph (Fin 2)).ConnectedComponent) = 1 := by
    have hs : Subsingleton ((⊤ : SimpleGraph (Fin 2)).ConnectedComponent) := by
      constructor
      intro a b
      induction a using SimpleGraph.ConnectedComponent.ind with | _ a =>
      induction b using SimpleGraph.ConnectedComponent.ind with | _ b =>
      rcases eq_or_ne a b with rfl | hab
      · rfl
      · exact SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hab)
    have hn : Nonempty ((⊤ : SimpleGraph (Fin 2)).ConnectedComponent) :=
      ⟨SimpleGraph.connectedComponentMk _ 0⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨hs, hn⟩
  rw [hc]
  have hE : Nat.card ((⊤ : SimpleGraph (Fin 2)).edgeSet) = 1 := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]; decide
  have hne : Nonempty ((⊤ : SimpleGraph (Fin 2)).Dart) := ⟨⟨(0, 1), by simp⟩⟩
  have hF : K2Rot.faceCount = 1 := by
    apply numOrbits_eq_one
    intro a b
    have ha : a.toProd = (0, 1) ∨ a.toProd = (1, 0) := by
      obtain ⟨⟨x, y⟩, h⟩ := a
      have hxy : x ≠ y := h
      fin_cases x <;> fin_cases y <;> simp_all
    have hb : b.toProd = (0, 1) ∨ b.toProd = (1, 0) := by
      obtain ⟨⟨x, y⟩, h⟩ := b
      have hxy : x ≠ y := h
      fin_cases x <;> fin_cases y <;> simp_all
    rcases ha with h1 | h1 <;> rcases hb with h2 | h2
    · exact ⟨0, by simp [SimpleGraph.Dart.ext_iff, h1, h2]⟩
    · refine ⟨1, ?_⟩
      simp only [zpow_one]
      apply SimpleGraph.Dart.ext
      simp [K2Rot, SimpleGraph.Dart.symm_toProd, h1, h2, Prod.swap]
    · refine ⟨1, ?_⟩
      simp only [zpow_one]
      apply SimpleGraph.Dart.ext
      simp [K2Rot, SimpleGraph.Dart.symm_toProd, h1, h2, Prod.swap]
    · exact ⟨0, by simp [SimpleGraph.Dart.ext_iff, h1, h2]⟩
  rw [hE, hF]
  simp

end Examples

end Frontier

import RequestProject.Planar

/-!
# Greedy colouring of degenerate graphs, and the six colour theorem

A graph is `k`-degenerate if each of its nonempty (induced) subgraphs contains a vertex of degree
at most `k`; such a graph can be greedily coloured with `k + 1` colours.

Every nonempty planar graph has a vertex of degree at most `5`
(`Frontier.exists_degree_le_five`), so any graph all of whose induced subgraphs are planar is
`5`-degenerate, hence `6`-colourable. (Planarity really is inherited by induced subgraphs, so
this hypothesis holds for every planar graph; that implication is a statement about surgery on
rotation systems and is not formalised here.)
-/

namespace Frontier

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `IsDegenerate G k` says that every nonempty set of vertices contains a vertex having at most
`k` neighbours inside that set: `G` is `k`-degenerate. -/
def IsDegenerate (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, ((s.erase v).filter (fun w => G.Adj v w)).card ≤ k

/-- **Greedy colouring**: a `k`-degenerate graph is `(k+1)`-colourable. -/
theorem colorable_of_isDegenerate (k : ℕ) (H : IsDegenerate G k) : G.Colorable (k + 1) := by
  classical
  have main : ∀ n : ℕ, ∀ s : Finset V, s.card = n →
      ∃ c : V → Fin (k + 1), ∀ a ∈ s, ∀ b ∈ s, G.Adj a b → c a ≠ c b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs
      rcases Finset.eq_empty_or_nonempty s with rfl | hne
      · exact ⟨fun _ => 0, by simp⟩
      obtain ⟨v, hv, hvdeg⟩ := H s hne
      have hlt : (s.erase v).card < n := by
        rw [Finset.card_erase_of_mem hv, ← hs]
        exact Nat.sub_lt (Finset.card_pos.mpr hne) one_pos
      obtain ⟨c, hc⟩ := ih (s.erase v).card hlt (s.erase v) rfl
      set T : Finset (Fin (k + 1)) := ((s.erase v).filter (fun w => G.Adj v w)).image c
      have hT : T.card ≤ k := le_trans Finset.card_image_le hvdeg
      have hex : ∃ x : Fin (k + 1), x ∉ T := by
        by_contra hcon
        push_neg at hcon
        have hsub : (Finset.univ : Finset (Fin (k + 1))) ⊆ T := fun x _ => hcon x
        have := Finset.card_le_card hsub
        simp only [Finset.card_univ, Fintype.card_fin] at this
        omega
      obtain ⟨x, hx⟩ := hex
      refine ⟨Function.update c v x, ?_⟩
      intro a ha b hb hab
      have hmemT : ∀ w ∈ s, w ≠ v → G.Adj v w → c w ∈ T := by
        intro w hw hwv hadj
        exact Finset.mem_image_of_mem c
          (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hwv, hw⟩, hadj⟩)
      by_cases hav : a = v
      · subst hav
        have hba : b ≠ a := (G.ne_of_adj hab).symm
        rw [Function.update_self, Function.update_of_ne hba]
        exact fun hcontra => hx (hcontra ▸ hmemT b hb hba hab)
      · by_cases hbv : b = v
        · subst hbv
          rw [Function.update_self, Function.update_of_ne hav]
          exact fun hcontra =>
            hx (hcontra.symm ▸ hmemT a ha hav (G.symm hab))
        · rw [Function.update_of_ne hav, Function.update_of_ne hbv]
          exact hc a (Finset.mem_erase.mpr ⟨hav, ha⟩) b (Finset.mem_erase.mpr ⟨hbv, hb⟩) hab
  obtain ⟨c, hc⟩ := main (Finset.univ : Finset V).card Finset.univ rfl
  exact ⟨SimpleGraph.Coloring.mk c fun {a b} hab =>
    hc a (Finset.mem_univ a) b (Finset.mem_univ b) hab⟩

/-- A graph is *hereditarily planar* if all of its induced subgraphs are planar in the sense of
`Frontier.IsPlanar`. Mathematically this is equivalent to planarity of `G` itself, since an
induced subgraph of a planar graph is planar; that implication involves surgery on rotation
systems and is not formalised here, so the theorems below take it as a hypothesis. -/
def IsHereditarilyPlanar (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, IsPlanar (G.induce (↑s : Set V))

omit [Fintype V] in
/-- The number of neighbours of `v` inside `s` computed in the induced subgraph. -/
theorem card_neighborSet_induce (s : Finset V) (v : (↑s : Set V)) :
    Nat.card ((G.induce (↑s : Set V)).neighborSet v)
      = ((s.erase v.1).filter (fun w => G.Adj v.1 w)).card := by
  have e : ((G.induce (↑s : Set V)).neighborSet v)
      ≃ {x : V // x ∈ (s.erase v.1).filter (fun w => G.Adj v.1 w)} :=
    { toFun := fun w => ⟨w.1.1, by
        have hadj : G.Adj v.1 w.1.1 := w.2
        refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, w.1.2⟩, hadj⟩
        exact (G.ne_of_adj hadj).symm⟩
      invFun := fun x => ⟨⟨x.1, (Finset.mem_erase.mp (Finset.mem_filter.mp x.2).1).2⟩, by
        exact (Finset.mem_filter.mp x.2).2⟩
      left_inv := fun w => by ext; rfl
      right_inv := fun x => by ext; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

omit [Fintype V] in
/-- A hereditarily planar graph is `5`-degenerate. -/
theorem isDegenerate_of_isHereditarilyPlanar (h : IsHereditarilyPlanar G) :
    IsDegenerate G 5 := by
  classical
  intro s hs
  obtain ⟨v₀, hv₀⟩ := hs
  have hne : Nonempty (↑s : Set V) := ⟨⟨v₀, hv₀⟩⟩
  haveI : DecidableRel (G.induce (↑s : Set V)).Adj := fun a b => ‹DecidableRel G.Adj› a.1 b.1
  obtain ⟨v, hv⟩ := exists_degree_le_five (G := G.induce (↑s : Set V)) (h s)
  refine ⟨v.1, v.2, ?_⟩
  rw [← card_neighborSet_induce s v, Nat.card_eq_fintype_card,
    SimpleGraph.card_neighborSet_eq_degree]
  exact hv

omit [Fintype V] [DecidableEq V] in
/-- Non-vacuity check: an edgeless graph is hereditarily planar. -/
theorem isHereditarilyPlanar_bot : IsHereditarilyPlanar (⊥ : SimpleGraph V) := by
  intro s
  have h : (⊥ : SimpleGraph V).induce (↑s : Set V) = (⊥ : SimpleGraph (↑s : Set V)) := by
    ext a b
    simp
  rw [h]
  exact isPlanar_bot

/-- A hereditarily planar graph on at most eleven vertices is `4`-degenerate. -/
theorem isDegenerate_four_of_card_le_eleven (h : IsHereditarilyPlanar G)
    (hcard : Fintype.card V ≤ 11) : IsDegenerate G 4 := by
  intro s hs
  obtain ⟨v₀, hv₀⟩ := hs
  have hne : Nonempty (↑s : Set V) := ⟨⟨v₀, hv₀⟩⟩
  haveI : DecidableRel (G.induce (↑s : Set V)).Adj := fun a b => ‹DecidableRel G.Adj› a.1 b.1
  have hcards : Fintype.card (↑s : Set V) ≤ 11 := by
    have h1 : Fintype.card (↑s : Set V) = s.card := Fintype.card_coe s
    have h2 : s.card ≤ Fintype.card V := Finset.card_le_univ s
    omega
  obtain ⟨v, hv⟩ :=
    exists_degree_le_four_of_card_le_eleven (G := G.induce (↑s : Set V)) (h s) hcards
  refine ⟨v.1, v.2, ?_⟩
  rw [← card_neighborSet_induce s v, Nat.card_eq_fintype_card,
    SimpleGraph.card_neighborSet_eq_degree]
  exact hv

/-- **The six colour theorem**: a (hereditarily) planar graph is `6`-colourable. -/
theorem six_color_theorem (h : IsHereditarilyPlanar G) : G.Colorable 6 :=
  colorable_of_isDegenerate 5 (isDegenerate_of_isHereditarilyPlanar h)

omit [Fintype V] in
/-- A triangle-free hereditarily planar graph is `3`-degenerate. -/
theorem isDegenerate_of_trianglefree (h : IsHereditarilyPlanar G) (htf : G.CliqueFree 3) :
    IsDegenerate G 3 := by
  intro s hs
  obtain ⟨v₀, hv₀⟩ := hs
  have hne : Nonempty (↑s : Set V) := ⟨⟨v₀, hv₀⟩⟩
  haveI : DecidableRel (G.induce (↑s : Set V)).Adj := fun a b => ‹DecidableRel G.Adj› a.1 b.1
  obtain ⟨v, hv⟩ := exists_degree_le_three (G := G.induce (↑s : Set V)) (h s)
    (htf.comap (SimpleGraph.Embedding.induce (↑s : Set V)))
  refine ⟨v.1, v.2, ?_⟩
  rw [← card_neighborSet_induce s v, Nat.card_eq_fintype_card,
    SimpleGraph.card_neighborSet_eq_degree]
  exact hv

/-- **The four colour theorem for triangle-free planar graphs**: a triangle-free (hereditarily)
planar graph is `4`-colourable. -/
theorem four_color_theorem_of_trianglefree (h : IsHereditarilyPlanar G) (htf : G.CliqueFree 3) :
    G.Colorable 4 :=
  colorable_of_isDegenerate 3 (isDegenerate_of_trianglefree h htf)

end Frontier

import Mathlib
import RequestProject.Orbits
import RequestProject.Planar
import RequestProject.Coloring

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# The five colour theorem

The five colour theorem states that every planar graph can be properly coloured with five
colours. Its classical proof runs by induction on the number of vertices: a planar graph always
has a vertex `v` of degree at most `5` (a consequence of Euler's formula), one colours `G - v`
inductively, and if all five colours occur among the neighbours of `v` one recolours using a
*Kempe chain* argument, which relies on the planarity of the embedding (a combinatorial form of
the Jordan curve theorem).

This file develops the following, all of it proved from scratch on top of a combinatorial
(rotation-system) notion of planarity introduced in `RequestProject.Planar`:

* Euler's edge bound `#E ≤ 3 #V - 6` for planar graphs (`Frontier.planar_edge_bound`) and the
  refinement `#E ≤ 2 #V - 4` for triangle-free planar graphs
  (`Frontier.planar_trianglefree_edge_bound`);
* every nonempty planar graph has a vertex of degree at most `5`
  (`Frontier.exists_degree_le_five`); a triangle-free one has a vertex of degree at most `3`
  (`Frontier.exists_degree_le_three`), and one with at most eleven vertices has a vertex of
  degree at most `4` (`Frontier.exists_degree_le_four_of_card_le_eleven`);
* greedy colouring of degenerate graphs (`Frontier.colorable_of_isDegenerate`);
* consequently the **six colour theorem** (`Frontier.six_color_theorem`) and the
  **four colour theorem for triangle-free planar graphs**
  (`Frontier.four_color_theorem_of_trianglefree`);
* the special cases of the five colour theorem collected in `Frontier.five_color_theorem`
  below: planar graphs that are `4`-degenerate, planar graphs on at most eleven vertices
  (`Frontier.five_color_theorem_of_card_le_eleven`), and triangle-free planar graphs.

The general five colour theorem (which needs the Kempe chain argument, hence a combinatorial
Jordan curve theorem for rotation systems) is **not** proved here.
-/

namespace Frontier

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A graph with at most five vertices is `4`-degenerate. -/
theorem isDegenerate_four_of_card_le_five (hcard : Fintype.card V ≤ 5) : IsDegenerate G 4 := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, ?_⟩
  calc ((s.erase v).filter (fun w => G.Adj v w)).card ≤ (s.erase v).card :=
        Finset.card_filter_le _ _
    _ = s.card - 1 := Finset.card_erase_of_mem hv
    _ ≤ Fintype.card V - 1 := by
        have := Finset.card_le_univ s
        omega
    _ ≤ 4 := by omega

/-- **The five colour theorem, special cases.**

Every planar graph that is `4`-degenerate, or has at most eleven vertices, or is triangle-free,
can be properly coloured with five colours.

Here planarity is the combinatorial notion `Frontier.IsHereditarilyPlanar`: every induced
subgraph carries a rotation system whose Euler characteristic is at least twice its number of
connected components, which is exactly what an embedding in the plane provides.

The hypothesis `hp` is not needed in the `4`-degenerate branch (where five colours are available
for a greedy colouring); it is what supplies, via Euler's formula, the degree bounds used in the
other two branches. The general case -- every planar graph is `5`-colourable -- requires the
Kempe chain argument and is not proved here. -/
theorem five_color_theorem (hp : IsHereditarilyPlanar G)
    (hspecial : IsDegenerate G 4 ∨ Fintype.card V ≤ 11 ∨ G.CliqueFree 3) : G.Colorable 5 := by
  rcases hspecial with hdeg | hcard | htf
  · exact colorable_of_isDegenerate 4 hdeg
  · exact colorable_of_isDegenerate 4 (isDegenerate_four_of_card_le_eleven hp hcard)
  · exact (four_color_theorem_of_trianglefree hp htf).mono (by norm_num)

/-- The base case of the induction in the five colour theorem: a graph with at most five
vertices is `5`-colourable (planarity is not needed for this case). -/
theorem five_color_theorem_of_card_le_five (hp : IsHereditarilyPlanar G)
    (hcard : Fintype.card V ≤ 5) : G.Colorable 5 :=
  five_color_theorem hp (Or.inl (isDegenerate_four_of_card_le_five hcard))

/-- **Every planar graph on at most eleven vertices is `5`-colourable.** Euler's formula forces
such a graph, and each of its induced subgraphs, to have a vertex of degree at most four, so no
Kempe chain argument is needed. The bound `11` is sharp for this argument: the icosahedron is a
`5`-regular planar graph on twelve vertices. -/
theorem five_color_theorem_of_card_le_eleven (hp : IsHereditarilyPlanar G)
    (hcard : Fintype.card V ≤ 11) : G.Colorable 5 :=
  five_color_theorem hp (Or.inr (Or.inl hcard))

end Frontier

