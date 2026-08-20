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

theorem exists_walk_of_connected (adj : Fin n → Fin n → Bool) {s t : Fin n}
    (h : Connected adj s t) : ∃ l : List (Fin n), walk adj s l = t := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | tail hb hbc ih =>
      obtain ⟨l, hl⟩ := ih
      rename_i b c
      refine ⟨l ++ [c], ?_⟩
      rw [walk_append, hl, walk_singleton, portStep, if_pos hbc]

/-! ## Universal sequences -/

/-- `seq` is a *universal sequence* for `n`-vertex undirected graphs: on every
undirected graph on `Fin n`, from every start vertex `s`, the port walk driven by
`seq` visits every vertex of the connected component of `s`. -/
