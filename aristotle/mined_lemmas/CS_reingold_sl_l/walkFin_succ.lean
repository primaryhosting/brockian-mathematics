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

theorem walkFin_succ {N D d : ℕ} (rot : Fin N → Fin D → Fin N) (v0 : Fin N) (w : Fin d → Fin D)
    {k : ℕ} (hk : k < d) :
    walkFin rot v0 w (k + 1) = rot (walkFin rot v0 w k) (w ⟨k, hk⟩) := by
  have h : (List.ofFn w).take (k + 1) = (List.ofFn w).take k ++ [w ⟨k, hk⟩] := by
    rw [List.take_add_one]
    congr 1
    simp [hk]
  unfold walkFin
  rw [h, walkL_append]

/-- A walk of length at most `d` is the same thing as a prefix of a walk with a
label word of length exactly `d`. -/
