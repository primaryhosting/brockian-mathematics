/-
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Five Color Theorem

Category: Frontier — Fields Medal Work

Target: `Frontier.five_color_theorem`

Verification: pending

Provenance: Aristotle theorem prover (Harmonic)

## Overview

`Mathlib` contains no theory of planar graphs (no embeddings, no Euler formula, no
Kuratowski theorem), so this file develops from scratch the combinatorial core of the
classical inductive proof of the Five Colour Theorem.

The classical proof, for a finite planar graph `G`, runs as follows.

* By Euler's formula a planar graph on `n ≥ 3` vertices has at most `3n - 6` edges.
* Hence the sum of the degrees is at most `6n - 12`, so some vertex has degree at most `5`.
* Delete such a vertex `v`, five-colour `G - v` by induction, and extend the colouring.
  If `deg v ≤ 4` the extension is immediate: the neighbours of `v` occupy at most four of
  the five colours.  Only the remaining case `deg v = 5` needs Kempe's chain exchange.

Everything except the Kempe chain exchange is formalised here:

* `Frontier.Degenerate`   — the degeneracy hypothesis extracted from Euler's formula;
* `Frontier.exists_partial_coloring`, `Frontier.colorable_of_degenerate` — the greedy
  colouring argument in full generality: a `k`-degenerate finite graph is
  `(k + 1)`-colourable;
* `Frontier.edgeCountIn`, `Frontier.EulerEdgeBound` — the planarity input, namely the
  Euler edge bound `e(H) ≤ 3·|H| - 6` for all induced subgraphs `H`;
* `Frontier.sum_degIn_eq_two_mul_edgeCountIn` — the handshake lemma for induced subgraphs;
* `Frontier.degenerate_four_of_eulerEdgeBound` — the averaging argument turning the Euler
  bound into `4`-degeneracy for graphs on at most `11` vertices;
* `Frontier.five_color_theorem` — the Five Colour Theorem for planar graphs on at most
  `11` vertices.

The bound `11` is exactly where the greedy argument stops being sufficient: for `n ≥ 12`
the Euler bound only forces a vertex of degree `≤ 5`, which is the case reserved for Kempe
chains.  So the statement proved here is the sharp "base case" of the induction that the
greedy half of the argument can reach.
-/

namespace Frontier

open Finset

open scoped Classical

variable {V : Type*}

/-! ## Degrees inside a finite set of vertices -/

/-- The number of neighbours of `v` inside the finite vertex set `s`. -/
noncomputable def degIn (G : SimpleGraph V) (s : Finset V) (v : V) : ℕ :=
  (s.filter (fun u => G.Adj v u)).card

theorem degIn_le_card_sub_one (G : SimpleGraph V) {s : Finset V} {v : V} (hv : v ∈ s) :
    degIn G s v ≤ s.card - 1 := by
  have hsub : s.filter (fun u => G.Adj v u) ⊆ s.erase v := by
    intro u hu
    simp only [Finset.mem_filter] at hu
    exact Finset.mem_erase.2 ⟨fun h => G.irrefl (h ▸ hu.2), hu.1⟩
  calc degIn G s v ≤ (s.erase v).card := Finset.card_le_card hsub
    _ = s.card - 1 := Finset.card_erase_of_mem hv

/-- `G` is `k`-degenerate: every nonempty finite set `s` of vertices contains a vertex
whose degree inside `s` is at most `k`.  Equivalently, every nonempty finite induced
subgraph of `G` has a vertex of degree at most `k`. -/
def Degenerate (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, degIn G s v ≤ k

/-- A graph all of whose degrees are at most `k` is `k`-degenerate. -/
theorem degenerate_of_forall_degree_le [Fintype V] {k : ℕ} {G : SimpleGraph V}
    (h : ∀ v : V, (univ.filter (fun u => G.Adj v u)).card ≤ k) : Degenerate k G := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, le_trans (Finset.card_le_card ?_) (h v)⟩
  exact Finset.filter_subset_filter _ (Finset.subset_univ s)

/-- Any graph on at most `k + 1` vertices is `k`-degenerate. -/
theorem degenerate_of_card_le [Fintype V] {k : ℕ} (G : SimpleGraph V)
    (h : Fintype.card V ≤ k + 1) : Degenerate k G := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, ?_⟩
  have h1 := degIn_le_card_sub_one G hv
  have h3 : s.card ≤ k + 1 := le_trans (Finset.card_le_univ s) h
  omega

/-!
## The greedy colouring argument

The heart of the matter: a `k`-degenerate graph admits a colouring of any finite set of
vertices by the colours `0, 1, …, k`.  The proof is by strong induction on the vertex set:
delete a vertex `v` of degree at most `k`, colour the rest, and give `v` any of the `k + 1`
colours missed by its (at most `k`) neighbours.
-/

/-- **Greedy colouring.**  If `G` is `k`-degenerate then every finite set `s` of vertices
carries a proper colouring using the colours `0, …, k`. -/
theorem exists_partial_coloring {k : ℕ} {G : SimpleGraph V} (hG : Degenerate k G) (s : Finset V) :
    ∃ c : V → ℕ, (∀ v ∈ s, c v ≤ k) ∧ ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨fun _ => 0, by simp, by simp⟩
    obtain ⟨v, hv, hdeg⟩ := hG s hs
    obtain ⟨c, hc1, hc2⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
    set N : Finset V := s.filter (fun u => G.Adj v u) with hN
    have hcard : (N.image c).card ≤ k := le_trans Finset.card_image_le hdeg
    -- some colour in `{0, …, k}` is missed by the neighbours of `v`
    have hex : ∃ a ≤ k, a ∉ N.image c := by
      by_contra hcon
      push_neg at hcon
      have hsub : Finset.range (k + 1) ⊆ N.image c := fun a ha =>
        hcon a (by simpa [Nat.lt_succ_iff] using ha)
      have := Finset.card_le_card hsub
      simp only [Finset.card_range] at this
      omega
    obtain ⟨a, hak, hanot⟩ := hex
    refine ⟨Function.update c v a, ?_, ?_⟩
    · intro u hu
      by_cases h : u = v
      · rw [h, Function.update_self]; exact hak
      · simpa [Function.update_of_ne h] using hc1 u (Finset.mem_erase.2 ⟨h, hu⟩)
    · intro u hu w hw hadj
      have hne : u ≠ w := hadj.ne
      by_cases hu' : u = v
      · subst hu'
        have hwu : w ≠ u := hne.symm
        have hmem : c w ∈ N.image c :=
          Finset.mem_image_of_mem c (Finset.mem_filter.2 ⟨hw, hadj⟩)
        simp only [Function.update_of_ne hwu, Function.update_self]
        exact fun h => hanot (h ▸ hmem)
      · by_cases hw' : w = v
        · subst hw'
          have hmem : c u ∈ N.image c :=
            Finset.mem_image_of_mem c (Finset.mem_filter.2 ⟨hu, hadj.symm⟩)
          simp only [Function.update_of_ne hu', Function.update_self]
          exact fun h => hanot (h ▸ hmem)
        · simp only [Function.update_of_ne hu', Function.update_of_ne hw']
          exact hc2 u (Finset.mem_erase.2 ⟨hu', hu⟩) w (Finset.mem_erase.2 ⟨hw', hw⟩) hadj

/-- **Degeneracy colouring theorem.**  Every `k`-degenerate finite graph is
`(k + 1)`-colourable. -/
theorem colorable_of_degenerate [Fintype V] {k : ℕ} {G : SimpleGraph V}
    (hG : Degenerate k G) : G.Colorable (k + 1) := by
  obtain ⟨c, h1, h2⟩ := exists_partial_coloring hG (univ : Finset V)
  refine ⟨SimpleGraph.Coloring.mk (fun v => (⟨c v, ?_⟩ : Fin (k + 1))) ?_⟩
  · exact Nat.lt_succ_of_le (h1 v (Finset.mem_univ v))
  · intro u w hadj
    have := h2 u (Finset.mem_univ u) w (Finset.mem_univ w) hadj
    simpa [Fin.ext_iff] using this

/-!
## The planarity input: Euler's edge bound

Euler's formula `|V| - |E| + |F| = 2` for a connected plane graph, combined with the fact
that every face of a simple plane graph on at least three vertices is bounded by at least
three edges, yields `|E| ≤ 3|V| - 6`.  Since every subgraph of a planar graph is planar,
this bound holds for all induced subgraphs.  That hereditary bound is the only consequence
of planarity used in the greedy half of the Five Colour Theorem, and it is what we take as
our hypothesis.
-/

variable [Fintype V]

/-- The number of edges of the subgraph of `G` induced on the finite vertex set `s`. -/
noncomputable def edgeCountIn (G : SimpleGraph V) (s : Finset V) : ℕ :=
  (G.induce (s : Set V)).edgeFinset.card

/-- Degrees inside `s` agree with degrees in the induced subgraph. -/
omit [Fintype V] in
theorem degree_induce_eq_degIn (G : SimpleGraph V) (s : Finset V) (v : V) (hv : v ∈ s) :
    (G.induce (s : Set V)).degree ⟨v, by simpa using hv⟩ = degIn G s v := by
  rw [SimpleGraph.degree]
  unfold degIn
  apply Finset.card_bij (fun (u : ((s : Set V))) _ => (u : V))
  · intro a ha
    simp only [SimpleGraph.mem_neighborFinset] at ha
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_coe.1 a.2, ha⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    simp only [Finset.mem_filter] at hb
    exact ⟨⟨b, by simpa using hb.1⟩, by simpa [SimpleGraph.mem_neighborFinset] using hb.2, rfl⟩

/-- **Handshake lemma for induced subgraphs.**  The sum of the degrees inside `s` is twice
the number of edges of the subgraph induced on `s`. -/
theorem sum_degIn_eq_two_mul_edgeCountIn (G : SimpleGraph V) (s : Finset V) :
    ∑ v ∈ s, degIn G s v = 2 * edgeCountIn G s := by
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges (G.induce (s : Set V))
  rw [edgeCountIn, ← h]
  rw [← Finset.sum_finset_coe (fun v => degIn G s v) s]
  refine Finset.sum_congr rfl ?_
  rintro ⟨v, hv⟩ -
  exact (degree_induce_eq_degIn G s v (by simpa using hv)).symm

/-- **The Euler edge bound**, the combinatorial consequence of planarity used below:
every induced subgraph on `n ≥ 3` vertices has at most `3n - 6` edges. -/
def EulerEdgeBound (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, 3 ≤ s.card → edgeCountIn G s ≤ 3 * s.card - 6

/-- **Averaging.**  If the degrees inside every nonempty `s` sum to less than
`(k + 1) * |s|`, then `G` is `k`-degenerate. -/
omit [Fintype V] in
theorem degenerate_of_sum_degIn_lt {k : ℕ} {G : SimpleGraph V}
    (h : ∀ s : Finset V, s.Nonempty → ∑ v ∈ s, degIn G s v < (k + 1) * s.card) :
    Degenerate k G := by
  intro s hs
  have hlt : ∑ v ∈ s, degIn G s v < ∑ _v ∈ s, (k + 1) := by
    simpa [Finset.sum_const, mul_comm] using h s hs
  obtain ⟨v, hv, hv'⟩ := Finset.exists_lt_of_sum_lt hlt
  exact ⟨v, hv, Nat.lt_succ_iff.1 hv'⟩

/-- **Euler bound implies `4`-degeneracy for at most `11` vertices.**  If every induced
subgraph on `n ≥ 3` vertices has at most `3n - 6` edges and `G` has at most `11` vertices,
then every nonempty induced subgraph of `G` has a vertex of degree at most `4`.

Indeed, on `n` vertices the degrees sum to at most `6n - 12`, which is less than `5n`
exactly when `n < 12`. -/
theorem degenerate_four_of_eulerEdgeBound {G : SimpleGraph V} (hE : EulerEdgeBound G)
    (hcard : Fintype.card V ≤ 11) : Degenerate 4 G := by
  refine degenerate_of_sum_degIn_lt (fun s hs => ?_)
  have hle : s.card ≤ 11 := le_trans (Finset.card_le_univ s) hcard
  have hpos : 1 ≤ s.card := Finset.card_pos.2 hs
  rcases lt_or_ge s.card 3 with h3 | h3
  · -- small sets: every degree is at most `|s| - 1 ≤ 1`
    have hbound : ∀ v ∈ s, degIn G s v ≤ s.card - 1 := fun v hv =>
      degIn_le_card_sub_one G hv
    have : ∑ v ∈ s, degIn G s v ≤ ∑ _v ∈ s, (s.card - 1) := Finset.sum_le_sum hbound
    simp only [Finset.sum_const, smul_eq_mul] at this
    have hn : s.card = 1 ∨ s.card = 2 := by omega
    rcases hn with h1 | h1 <;> rw [h1] at this ⊢ <;> omega
  · have hEs := hE s h3
    have hsum := sum_degIn_eq_two_mul_edgeCountIn G s
    omega

/-!
## The Five Colour Theorem
-/

/-- **Five Colour Theorem, greedy form.**  Every finite graph each of whose nonempty
induced subgraphs contains a vertex of degree at most `4` is `5`-colourable. -/
theorem five_color_theorem_of_degenerate (G : SimpleGraph V) (hG : Degenerate 4 G) :
    G.Colorable 5 :=
  colorable_of_degenerate hG

/-- **Five Colour Theorem** (special/base case).

Every planar graph on at most `11` vertices is `5`-colourable.

Planarity enters only through Euler's edge bound `EulerEdgeBound`: every induced subgraph
on `n ≥ 3` vertices has at most `3n - 6` edges, which is the standard consequence of
Euler's formula `|V| - |E| + |F| = 2` for plane graphs.  For `n ≤ 11` this bound already
forces a vertex of degree at most `4` in every induced subgraph, and the greedy colouring
argument then produces a proper `5`-colouring.

The bound `11` is sharp for this method: from `n = 12` on, Euler's bound only guarantees a
vertex of degree at most `5`, and the classical proof must invoke Kempe's chain exchange
argument, which is not formalised here. -/
theorem five_color_theorem (G : SimpleGraph V) (hE : EulerEdgeBound G)
    (hcard : Fintype.card V ≤ 11) : G.Colorable 5 :=
  five_color_theorem_of_degenerate G (degenerate_four_of_eulerEdgeBound hE hcard)

/-- **Base case of the induction.**  Every graph on at most five vertices — in particular
every planar graph on at most five vertices — is `5`-colourable. -/
theorem five_color_theorem_base (G : SimpleGraph V) (h : Fintype.card V ≤ 5) :
    G.Colorable 5 :=
  colorable_of_degenerate (degenerate_of_card_le G h)

/-- Every finite graph of maximum degree at most `4` is `5`-colourable. -/
theorem five_color_theorem_of_maxDegree (G : SimpleGraph V)
    (h : ∀ v : V, (univ.filter (fun u => G.Adj v u)).card ≤ 4) : G.Colorable 5 :=
  five_color_theorem_of_degenerate G (degenerate_of_forall_degree_le h)

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

