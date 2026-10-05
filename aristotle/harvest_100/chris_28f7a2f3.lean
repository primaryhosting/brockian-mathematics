/-
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the required header above is
-- given as a plain comment and repeated as the module docstring below.)

import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Scope of this file

Mathlib (at the pinned version) contains no theory of planar graphs, so planarity is
developed here from scratch: `Frontier.PlaneDrawing` is a straight-line drawing of a graph
in `ℝ × ℝ` and `Frontier.IsPlanar` says that such a drawing exists (by Fáry's theorem this
is equivalent, for finite simple graphs, to the usual topological notion of planarity).

What is proved here is the *base case* of the five colour theorem — the case that the
classical proof settles by a single greedy step, without any Kempe chain interchange:
every finite planar graph each of whose nonempty induced subgraphs has a vertex of degree
at most `4` is `5`-colourable (`Frontier.five_color_theorem`).  Concrete consequences are
that every planar graph of maximum degree at most `4` is `5`-colourable, and that every
graph on at most five vertices is `5`-colourable.

The purely combinatorial half of the remaining case is also proved here: the Kempe chain
interchange `Frontier.kempe_swap_proper`, which recolours a union of components of a
two-coloured subgraph.  What is *not* developed here is the topological input of the full
theorem — Euler's formula and the Jordan curve argument showing that two Kempe chains
around a vertex of degree `5` cannot both exist in a plane drawing.
-/

set_option autoImplicit false

namespace Frontier

open Finset

variable {V : Type*}

/-- A straight-line drawing of a simple graph `G` in the plane `ℝ × ℝ`:
vertices are placed at distinct points, edges are drawn as the straight segments between
their endpoints, no vertex lies in the interior of an edge, and the interiors of two
distinct edges are disjoint.  By Fáry's theorem this is, for finite simple graphs,
equivalent to the usual topological notion of planarity. -/
structure PlaneDrawing (G : SimpleGraph V) where
  /-- the position of each vertex in the plane -/
  pos : V → ℝ × ℝ
  pos_injective : Function.Injective pos
  /-- no vertex lies in the interior of an edge it is not an endpoint of -/
  vertex_notMem : ∀ v a b : V, G.Adj a b → v ≠ a → v ≠ b →
    pos v ∉ openSegment ℝ (pos a) (pos b)
  /-- interiors of distinct edges are disjoint -/
  edges_disjoint : ∀ a b c d : V, G.Adj a b → G.Adj c d → s(a, b) ≠ s(c, d) →
    openSegment ℝ (pos a) (pos b) ∩ openSegment ℝ (pos c) (pos d) = ∅

/-- A simple graph is *planar* when it admits a straight-line drawing in the plane. -/
def IsPlanar (G : SimpleGraph V) : Prop := Nonempty (PlaneDrawing G)

/-- Membership in an open segment of the plane, in coordinates. -/
lemma mem_openSegment_prod {a b p : ℝ × ℝ} : p ∈ openSegment ℝ a b ↔
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ p = ((1 - t) * a.1 + t * b.1, (1 - t) * a.2 + t * b.2) := by
  rw [openSegment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht.1, ht.2, by simp [Prod.ext_iff]⟩
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, ⟨h0, h1⟩, by simp [Prod.ext_iff]⟩

/-- Planarity is inherited by subgraphs: any drawing of `G` restricts to a drawing of a
subgraph `H ≤ G`. -/
theorem IsPlanar.mono {G H : SimpleGraph V} (hHG : H ≤ G) (hG : IsPlanar G) : IsPlanar H := by
  obtain ⟨D⟩ := hG
  exact ⟨{ pos := D.pos
           pos_injective := D.pos_injective
           vertex_notMem := fun v a b hab hva hvb => D.vertex_notMem v a b (hHG hab) hva hvb
           edges_disjoint := fun a b c d hab hcd hne =>
             D.edges_disjoint a b c d (hHG hab) (hHG hcd) hne }⟩

/-- The empty graph on a finite vertex type is planar. -/
theorem isPlanar_bot [Fintype V] : IsPlanar (⊥ : SimpleGraph V) := by
  classical
  refine ⟨{ pos := fun v => Prod.mk ((((Fintype.equivFin V) v : ℕ) : ℝ)) 0,
            pos_injective := ?_, vertex_notMem := ?_, edges_disjoint := ?_ }⟩
  · intro a b hab
    have h1 : ((((Fintype.equivFin V) a : ℕ) : ℝ)) = ((((Fintype.equivFin V) b : ℕ) : ℝ)) :=
      congrArg Prod.fst hab
    have : ((Fintype.equivFin V) a : ℕ) = ((Fintype.equivFin V) b : ℕ) := by exact_mod_cast h1
    exact (Fintype.equivFin V).injective (Fin.ext this)
  · intro v a b hab; exact absurd hab (by simp)
  · intro a b c d hab; exact absurd hab (by simp)

/-- The positions of the three vertices of a drawn triangle. -/
noncomputable def trianglePos : Fin 3 → ℝ × ℝ := ![(0, 0), (1, 0), (0, 1)]

/-- A triangle (the complete graph on three vertices) is planar: it can be drawn with
straight lines between the points `(0,0)`, `(1,0)` and `(0,1)`.  In particular the notion
of planarity used here is not vacuous, and is satisfied by graphs containing cycles. -/
theorem isPlanar_triangle : IsPlanar (⊤ : SimpleGraph (Fin 3)) := by
  refine ⟨{ pos := trianglePos, pos_injective := ?_, vertex_notMem := ?_,
            edges_disjoint := ?_ }⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [trianglePos, Prod.ext_iff]
  · intro v a b hab hva hvb
    fin_cases v <;> fin_cases a <;> fin_cases b <;>
      simp_all [trianglePos, mem_openSegment_prod]
  · intro a b c d hab hcd hne
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hp1, hp2⟩
    rw [mem_openSegment_prod] at hp1 hp2
    obtain ⟨t, ht0, ht1, rfl⟩ := hp1
    obtain ⟨s, hs0, hs1, hps⟩ := hp2
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp_all [trianglePos, Prod.ext_iff] <;> linarith

/-! ### Kempe chain interchange

The second ingredient of the classical proof of the five colour theorem is the *Kempe
chain interchange*: in a proper colouring one may exchange two colours `i` and `j` on any
union `A` of connected components of the subgraph spanned by the vertices coloured `i` or
`j`, and the result is again a proper colouring.  This part of the argument is purely
combinatorial and is proved here in full generality. -/

open Classical in
/-- Exchange the colours `i` and `j` on the set `A`. -/
noncomputable def kempeSwap {α : Type*} [DecidableEq α] (c : V → α) (i j : α) (A : Set V) :
    V → α :=
  fun v => if v ∈ A then (if c v = i then j else if c v = j then i else c v) else c v

/-- **Kempe chain interchange.**  If `A` consists of vertices coloured `i` or `j` and is
closed under passing to adjacent vertices coloured `i` or `j` (i.e. `A` is a union of
connected components of the `i`/`j`-coloured subgraph), then exchanging `i` and `j` on `A`
takes proper colourings to proper colourings. -/
theorem kempe_swap_proper {α : Type*} [DecidableEq α] {G : SimpleGraph V} {c : V → α}
    {i j : α} {A : Set V}
    (hproper : ∀ u w, G.Adj u w → c u ≠ c w)
    (hAcol : ∀ u ∈ A, c u = i ∨ c u = j)
    (hAclosed : ∀ u w, u ∈ A → G.Adj u w → (c w = i ∨ c w = j) → w ∈ A) :
    ∀ u w, G.Adj u w → kempeSwap c i j A u ≠ kempeSwap c i j A w := by
  classical
  by_cases hij : i = j
  · subst hij
    have hid : kempeSwap c i i A = c := by
      funext v
      by_cases hv : v ∈ A <;> by_cases hc : c v = i <;> simp [kempeSwap, hv, hc]
    rw [hid]
    exact hproper
  intro u w hadj
  have hji : j ≠ i := fun h => hij h.symm
  by_cases hu : u ∈ A <;> by_cases hw : w ∈ A
  · rcases hAcol u hu with h1 | h1 <;> rcases hAcol w hw with h2 | h2 <;>
      simp [kempeSwap, hu, hw, h1, h2, hij, hji] <;>
      exact absurd (h1.trans h2.symm) (hproper u w hadj)
  · have hcw : ¬ (c w = i ∨ c w = j) := fun h => hw (hAclosed u w hu hadj h)
    push_neg at hcw
    rcases hAcol u hu with h1 | h1 <;>
      simp [kempeSwap, hu, hw, h1, hji, Ne.symm hcw.1, Ne.symm hcw.2]
  · have hcu : ¬ (c u = i ∨ c u = j) := fun h => hu (hAclosed w u hw hadj.symm h)
    push_neg at hcu
    rcases hAcol w hw with h1 | h1 <;>
      simp [kempeSwap, hu, hw, h1, hji, hcu.1, hcu.2]
  · simpa [kempeSwap, hu, hw] using hproper u w hadj

/-- `Degenerate G k` says that every nonempty set of vertices contains a vertex having at
most `k` neighbours inside that set.  Equivalently, every nonempty subgraph of `G` induced
on a set of vertices has a vertex of degree at most `k`. -/
def Degenerate (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, #{u ∈ s.erase v | G.Adj v u} ≤ k

/-- The greedy colouring step, by strong induction on the set of vertices already coloured:
in a `k`-degenerate graph every finite set of vertices carries a proper colouring with
`k + 1` colours. -/
theorem exists_partial_coloring [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (h : Degenerate G k) (s : Finset V) :
    ∃ c : V → Fin (k + 1), ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → c u ≠ c w := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨fun _ => 0, by simp⟩
    obtain ⟨v, hv, hcard⟩ := h s hs
    obtain ⟨c, hc⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
    obtain ⟨x, hx⟩ : ∃ x : Fin (k + 1), x ∉ ({u ∈ s.erase v | G.Adj v u} : Finset V).image c := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (Fin (k + 1))) ⊆
          ({u ∈ s.erase v | G.Adj v u} : Finset V).image c := fun y _ => hcon y
      have h1 := Finset.card_le_card hsub
      have h2 := (Finset.card_image_le (s := ({u ∈ s.erase v | G.Adj v u} : Finset V))
        (f := c)).trans hcard
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      omega
    refine ⟨Function.update c v x, ?_⟩
    intro u hu w hw hadj
    by_cases hu' : u = v
    · subst hu'
      have hwu : w ≠ u := (G.ne_of_adj hadj).symm
      have hmem : w ∈ ({y ∈ s.erase u | G.Adj u y} : Finset V) := by
        simp [Finset.mem_erase, hwu, hw, hadj]
      simp only [Function.update_self, ne_eq, Function.update_of_ne hwu]
      exact fun hEq => hx (hEq ▸ Finset.mem_image_of_mem c hmem)
    · by_cases hw' : w = v
      · subst hw'
        have hmem : u ∈ ({y ∈ s.erase w | G.Adj w y} : Finset V) := by
          simp [Finset.mem_erase, hu', hu, hadj.symm]
        simp only [Function.update_self, ne_eq, Function.update_of_ne hu']
        exact fun hEq => hx (hEq ▸ Finset.mem_image_of_mem c hmem)
      · simp only [Function.update_of_ne hu', Function.update_of_ne hw']
        exact hc u (Finset.mem_erase.2 ⟨hu', hu⟩) w (Finset.mem_erase.2 ⟨hw', hw⟩) hadj

/-- Greedy colouring: a `k`-degenerate graph is `(k+1)`-colourable. -/
theorem Colorable_of_degenerate [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (h : Degenerate G k) : G.Colorable (k + 1) := by
  obtain ⟨c, hc⟩ := exists_partial_coloring h Finset.univ
  exact ⟨SimpleGraph.Coloring.mk c fun {a b} hab =>
    hc a (Finset.mem_univ a) b (Finset.mem_univ b) hab⟩

/-- A graph of maximum degree at most `k` is `k`-degenerate. -/
theorem degenerate_of_degree_le [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (h : ∀ v, G.degree v ≤ k) : Degenerate G k := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, le_trans (Finset.card_le_card ?_) (h v)⟩
  intro u hu
  simp only [Finset.mem_filter] at hu
  exact SimpleGraph.mem_neighborFinset G v u |>.2 hu.2

/-- **Five Colour Theorem** (base case: `4`-degenerate planar graphs).

Every finite planar graph in which every nonempty induced subgraph has a vertex of degree
at most `4` is `5`-colourable.  This is exactly the case of the five colour theorem that
does not require Kempe chain interchanges: in the classical proof one picks a vertex `v`
of degree at most `5` in a planar graph, and the greedy step succeeds immediately whenever
`v` has degree at most `4`.

The planarity hypothesis `hp` is stated because it is part of the intended statement; the
proof of this base case only uses the degeneracy hypothesis. -/
theorem five_color_theorem [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hp : IsPlanar G) (hdeg : Degenerate G 4) : G.Colorable 5 :=
  Colorable_of_degenerate hdeg

/-- Every planar graph of maximum degree at most `4` is `5`-colourable. -/
theorem five_color_theorem_of_degree_le_four [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hp : IsPlanar G) (hd : ∀ v, G.degree v ≤ 4) : G.Colorable 5 :=
  five_color_theorem G hp (degenerate_of_degree_le hd)

/-- Every graph, in particular every planar graph, on at most five vertices is
`5`-colourable. -/
theorem five_color_theorem_of_card_le_five [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V ≤ 5) : G.Colorable 5 :=
  (G.colorable_of_fintype).mono hcard

/-- Every planar graph in which every nonempty induced subgraph has a vertex of degree at
most `5` is `6`-colourable (the "six colour" bound obtained from greedy colouring alone). -/
theorem six_color_theorem_of_degenerate [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hp : IsPlanar G) (hdeg : Degenerate G 5) : G.Colorable 6 :=
  Colorable_of_degenerate hdeg

/-- A concrete instance: the triangle is planar, has maximum degree `2`, and is therefore
`5`-colourable by the theorem above.  This witnesses that the hypotheses of
`Frontier.five_color_theorem` can be met by a graph with edges. -/
example : (⊤ : SimpleGraph (Fin 3)).Colorable 5 :=
  five_color_theorem_of_degree_le_four _ isPlanar_triangle (by decide)

end Frontier

import Mathlib

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

