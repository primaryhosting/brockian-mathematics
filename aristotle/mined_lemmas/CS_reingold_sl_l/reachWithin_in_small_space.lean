/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [local instance 0] Classical.propDecidable

namespace CS

/-!
## Overview

This file formalises Reingold's theorem `SL = L`, i.e. that undirected `s`-`t`
connectivity (`USTCON`) can be decided in logarithmic space, in the following
form.

* Section 1 sets up a space-bounded machine model `SMachine`: a deterministic
  machine with a finite state space which reads its input only through oracle
  queries (a read-only input tape with random access).  A machine uses space
  `log₂ (Fintype.card S)`, so *logarithmic space* means a family of machines
  whose state spaces have polynomially bounded cardinality.
* Section 2 proves that such machines compose (`SMachine.comp_computes`): an
  outer machine using an oracle which is itself computed by an inner
  space-bounded machine can be simulated by a single machine whose state space
  is the product of the two.  This is the usual "recompute instead of store"
  closure of logspace under composition.
* Section 3 defines undirected `s`-`t` connectivity and the predicate
  `USTCON_in_L`.
* Section 4 builds, *unconditionally*, an explicit machine `searchM` which
  decides connectivity in a `D`-regular graph presented by a rotation map, all
  of whose components have diameter at most `d`, by trying all `D ^ d` walks of
  length `d` in turn (`searchM_computes`).  Its state space has cardinality
  `O(n² · N³ · D^d · d)`, which is polynomial when `D` is constant and
  `D ^ d` is polynomial; this is the final phase of Reingold's algorithm.
* Section 5 packages the deep combinatorial content of Reingold's theorem — the
  zig-zag/derandomised-squaring transformation of an arbitrary undirected graph
  into a constant-degree graph of logarithmic diameter, computable in
  logarithmic space and preserving connectivity — as the structure
  `ReingoldReduction`, and derives from it the main theorem `reingold_sl_l`:
  undirected `s`-`t` connectivity is decidable in logarithmic space.

Two caveats about the scope of what is proved here.  First, the existence of a
`ReingoldReduction` (the zig-zag construction and its spectral analysis) is a
hypothesis of `reingold_sl_l`, not something proved here; everything else — the
search machine, its correctness, the composition theorem, and the space
accounting — is proved unconditionally.  Second, `USTCON_in_L` asserts the
existence of a family of machines indexed by the input length without imposing
a further uniformity condition on the family; the family produced by
`reingold_sl_l` is nevertheless given by explicit computable data (`searchM`
composed with the given transducer).
-/

/-!
## A space-bounded machine model

A `SMachine Q A I O S` is a deterministic machine with (finite) state space `S`
which reads its input only through *queries*: in state `s` it asks the oracle
`f : Q → A` the question `query s` and uses the answer to move to the next state.
It starts in state `init i` on input `i : I` and halts as soon as `out s` is
`some o`, which is then its output.

The *space* used by such a machine is `log₂ (card S)`, so a family of machines
with `card S ≤ poly(n)` is exactly a logarithmic-space machine family (the input
being read through the oracle, i.e. a read-only input tape with random access).
-/

/-- A deterministic oracle-query machine with state space `S`. -/
structure SMachine (Q A I O S : Type) where
  /-- Initial state on a given input. -/
  init : I → S
  /-- The oracle query asked in a given state. -/
  query : S → Q
  /-- The transition function, given the answer to the query. -/
  step : S → A → S
  /-- Output of a halting state (`none` if the state is not halting). -/
  out : S → Option O

namespace SMachine

variable {Q A I O S : Type}

/-- One step of the machine relative to the oracle `f`; halting states are fixed. -/

theorem reachWithin_in_small_space (N D d : ℕ) (hD : 0 < D) :
    ∃ (S : Type) (inst : Fintype S)
      (M : SMachine ((Fin N × Fin D) ⊕ Fin N) (Fin N) (Fin N × Fin N) Bool S),
      @Fintype.card S inst = N * (N * (4 * (N * (N * (N * (D ^ d * ((d + 1) * 2))))))) ∧
      ∀ rot : Fin N → Fin D → Fin N,
        M.Computes (Sum.elim (fun q => rot q.1 q.2) id)
          (fun p => decide (ReachWithin rot d p.1 p.2)) :=
  ⟨SearchState N N D d, inferInstance, searchM N N D d hD (fun h => h),
    SearchState.card_eq N N D d, fun rot => searchM_computes N N D d hD (fun h => h) rot id⟩

/-!
## Reingold's theorem

The deep content of Reingold's theorem is the construction, using the zig-zag
product, of a logspace transformation taking an arbitrary undirected graph to a
constant-degree graph whose connected components have logarithmic diameter and
which preserves connectivity.  This is packaged in the structure
`ReingoldReduction` below; `reingold_sl_l` derives from it that undirected
`s`-`t` connectivity is decidable in logarithmic space, i.e. `SL = L`.
-/

/-- The data produced by Reingold's zig-zag transformation: a logspace machine
`redM n` which, given the adjacency matrix of an undirected graph on `n`
vertices as an oracle, computes the rotation map of a `D`-regular graph on
`N n` vertices together with an embedding of the original vertices, in such a
way that connectivity in the original graph corresponds to reachability within
`d n` steps in the new graph. -/
structure ReingoldReduction where
  /-- The (constant) degree of the transformed graph. -/
  D : ℕ
  /-- The degree is at least two. -/
  hD : 2 ≤ D
  /-- The number of vertices of the transformed graph. -/
  N : ℕ → ℕ
  /-- The diameter bound for the transformed graph. -/
  d : ℕ → ℕ
  /-- The polynomial bound exponent. -/
  c : ℕ
  /-- The state space of the transducer. -/
  S : ℕ → Type
  /-- The state space is finite. -/
  finS : ∀ n, Fintype (S n)
  /-- The transducer computing the transformed graph. -/
  redM : ∀ n, SMachine (Fin n × Fin n) Bool ((Fin (N n) × Fin D) ⊕ Fin n) (Fin (N n)) (S n)
  /-- The transducer uses logarithmic space. -/
  card_le : ∀ n, @Fintype.card (S n) (finS n) ≤ (n + 2) ^ c
  /-- The transformed graph has polynomially many vertices. -/
  N_le : ∀ n, N n ≤ (n + 2) ^ c
  /-- The diameter of the transformed graph is logarithmic. -/
  pow_le : ∀ n, D ^ d n ≤ (n + 2) ^ c
  /-- Correctness of the transformation. -/
  spec : ∀ (n : ℕ) (adj : Fin n → Fin n → Bool), (∀ u v, adj u v = adj v u) →
    ∃ (rot : Fin (N n) → Fin D → Fin (N n)) (emb : Fin n → Fin (N n)),
      (redM n).Computes (fun p => adj p.1 p.2) (Sum.elim (fun q => rot q.1 q.2) emb) ∧
      ∀ u v, AdjReach adj u v ↔ ReachWithin rot (d n) (emb u) (emb v)

/-- **Reingold's theorem** (`SL = L`): undirected `s`-`t` connectivity is
decidable in logarithmic space. -/
