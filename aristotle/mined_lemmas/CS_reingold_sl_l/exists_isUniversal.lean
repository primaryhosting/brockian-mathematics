import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Undirected `s`-`t` connectivity (`USTCON`) and logarithmic space.

We work with the standard *non-uniform logarithmic space* model: a machine with
read-only random access to the adjacency matrix of the input graph and a finite
set of internal configurations; the memory used is `log₂` of the number of
configurations (i.e. a branching program over the adjacency bits).

The algorithmic content formalized here is the exploration/traversal-sequence
algorithm for `USTCON`: a *universal sequence* is a fixed list of port labels
such that, on every undirected graph on `Fin n` and from every start vertex, the
induced deterministic walk visits every vertex of the start vertex's connected
component. Given such a sequence of polynomially bounded length, we build an
explicit machine using `O(log n)` bits of memory that decides `USTCON`, and we
prove it correct (`CS.reingold_sl_l`).

We also prove, unconditionally, that universal sequences exist
(`CS.exists_isUniversal`), so that the statement is not vacuous; that proof only
gives an exponentially long sequence. The existence of *polynomially* long
universal sequences (Aleliunas–Karp–Lipton–Lovász–Rackoff) and their
log-space constructibility (Reingold), which are what upgrade the theorem below
to the full statement `SL = L`, are *not* formalized here.
-/

namespace CS

variable {n : ℕ}

/-! ## Graphs, port walks and connectivity -/

/-- One step of a *port walk*: from `v`, the label `a` moves to `a` if `a` is a
neighbour of `v`, and stays at `v` otherwise (a self-loop). -/

theorem exists_isUniversal (n : ℕ) : ∃ seq : List (Fin n), IsUniversal n seq := by
  classical
  -- handle all triples `(adj, s, t)` one at a time, appending to the sequence
  suffices H : ∀ l : List ((Fin n → Fin n → Bool) × Fin n × Fin n),
      ∃ seq : List (Fin n), ∀ x ∈ l, (∀ u v, x.1 u v = x.1 v u) →
        Connected x.1 x.2.1 x.2.2 →
        ∃ k ≤ seq.length, walk x.1 x.2.1 (seq.take k) = x.2.2 by
    obtain ⟨seq, hseq⟩ := H (Finset.univ : Finset ((Fin n → Fin n → Bool) × Fin n × Fin n)).toList
    exact ⟨seq, fun adj hsymm s t hc => hseq (adj, s, t) (by simp) hsymm hc⟩
  intro l
  induction l with
  | nil => exact ⟨[], by simp⟩
  | cons x l ih =>
      obtain ⟨seq, hseq⟩ := ih
      by_cases hx : (∀ u v, x.1 u v = x.1 v u) ∧ Connected x.1 x.2.1 x.2.2
      · obtain ⟨hsymm, hconn⟩ := hx
        have hsym : Symmetric (Connected x.1) :=
          Relation.ReflTransGen.symmetric (fun u v h => by rw [hsymm]; exact h)
        have hc : Connected x.1 (walk x.1 x.2.1 seq) x.2.2 :=
          (hsym (connected_walk x.1 x.2.1 seq)).trans hconn
        obtain ⟨w, hw⟩ := exists_walk_of_connected x.1 hc
        refine ⟨seq ++ w, ?_⟩
        intro y hy hys hyc
        rcases List.mem_cons.1 hy with rfl | hy
        · refine ⟨(seq ++ w).length, le_rfl, ?_⟩
          rw [List.take_length, walk_append, hw]
        · exact handled_append _ _ _ _ _ (hseq y hy hys hyc)
      · refine ⟨seq, ?_⟩
        intro y hy hys hyc
        rcases List.mem_cons.1 hy with rfl | hy
        · exact absurd ⟨hys, hyc⟩ hx
        · exact hseq y hy hys hyc

end CS

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

