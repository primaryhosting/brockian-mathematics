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

def portStep (adj : Fin n → Fin n → Bool) (v a : Fin n) : Fin n :=
  if adj v a then a else v

/-- The vertex reached from `v` by following the list of port labels `l`. -/

def walk (adj : Fin n → Fin n → Bool) (v : Fin n) (l : List (Fin n)) : Fin n :=
  l.foldl (portStep adj) v

/-- `s`-`t` connectivity: reflexive-transitive closure of the adjacency relation. -/
