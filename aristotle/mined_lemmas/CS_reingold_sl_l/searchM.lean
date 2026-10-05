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

def searchM (n N D d : ℕ) (hD : 0 < D) (hNn : 0 < n → 0 < N) :
    SMachine ((Fin N × Fin D) ⊕ Fin n) (Fin N) (Fin n × Fin n) Bool (SearchState n N D d) where
  init p :=
    ⟨p.1, p.2, 0, ⟨0, hNn (lt_of_le_of_lt (Nat.zero_le _) p.1.isLt)⟩,
      ⟨0, hNn (lt_of_le_of_lt (Nat.zero_le _) p.1.isLt)⟩,
      ⟨0, hNn (lt_of_le_of_lt (Nat.zero_le _) p.1.isLt)⟩,
      ⟨0, Nat.pow_pos hD⟩, ⟨0, Nat.succ_pos d⟩, false⟩
  query st :=
    if st.tag = 0 then Sum.inr st.s
    else if st.tag = 1 then Sum.inr st.t
    else Sum.inl (st.v,
      if h : st.i.1 < d then wordEquiv D d st.j ⟨st.i.1, h⟩ else ⟨0, hD⟩)
  step st a :=
    if st.tag = 0 then { st with tag := 1, sp := a }
    else if st.tag = 1 then
      ⟨st.s, st.t, 2, st.sp, a, st.sp, ⟨0, Nat.pow_pos hD⟩, ⟨0, Nat.succ_pos d⟩,
        decide (st.sp = a)⟩
    else if st.tag = 2 then
      (if h : st.i.1 < d then
        ⟨st.s, st.t, st.tag, st.sp, st.tp, a, st.j, ⟨st.i.1 + 1, by omega⟩,
          st.found || decide (a = st.tp)⟩
      else if h2 : st.j.1 + 1 < D ^ d then
        ⟨st.s, st.t, st.tag, st.sp, st.tp, st.sp, ⟨st.j.1 + 1, h2⟩, ⟨0, Nat.succ_pos d⟩,
          st.found⟩
      else { st with tag := 3 })
    else st
  out st := if st.tag = 3 then some st.found else none

/-- A state of the walking phase of the search machine. -/
