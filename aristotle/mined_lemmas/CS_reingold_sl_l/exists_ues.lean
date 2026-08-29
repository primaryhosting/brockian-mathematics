import Mathlib
import RequestProject.ReingoldSlL

/-!
## Existence of universal exploration sequences

The hypothesis `CS.HasPolyUES` used in `RequestProject/ReingoldSlL.lean` asks for universal
exploration sequences of *polynomial* length; producing such short sequences is the deep part
of Reingold's theorem and is not formalised.  Here we prove, unconditionally, that universal
exploration sequences of *some* finite length always exist (`CS.exists_ues`).  This shows that
the notion is satisfiable — the only missing ingredient in `CS.HasPolyUES` is the polynomial
length bound.
-/

set_option autoImplicit false

namespace CS

namespace RotGraph

variable {n d : ℕ}

/-- The walk of length `k` only depends on the first `k` offsets. -/

theorem exists_ues (n d : ℕ) [NeZero d] : ∃ (T : ℕ) (seq : ℕ → Fin d), IsUES n d T seq := by
  obtain ⟨T, seq, hseq⟩ :=
    exists_seq_for_list (Finset.univ : Finset (RotGraph n d × Fin n × Fin n)).toList
  refine ⟨T, seq, ?_⟩
  intro G s t hst
  exact hseq (G, s, t) (by simp) hst

end CS

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

/-!
## Overview

This file formalises the algorithmic content of Reingold's theorem
(`SL = L`, i.e. undirected `s`-`t` connectivity is decidable in logarithmic space)
in the following model.

* An undirected `d`-regular multigraph on the vertex set `Fin n` is presented by its
  **rotation map** `rot : Fin n × Fin d → Fin n × Fin d`, an involution: `rot (v, i) = (w, j)`
  means that the `i`-th edge leaving `v` arrives at `w` as its `j`-th edge.  (Self-loops are
  allowed, so every symmetric bounded-degree graph can be presented this way after padding.)

* A **space bounded machine** (`CS.Machine`) has a finite configuration type `C`, an initial
  configuration depending on the two query vertices `s`, `t`, and at each step it makes exactly
  one query to the rotation map of the input graph and updates its configuration accordingly.
  The space used by the machine is `log₂ (card C)`; the input is read-only and is accessed
  only through rotation-map queries, so this is the usual model of a log-space algorithm
  with a graph given as input.

* The deep ingredient of Reingold's theorem is isolated as the hypothesis
  `CS.HasPolyUES`: for all `n` and `d` there is a **universal exploration sequence** of
  length polynomial in `n * d`, i.e. a sequence of edge-label offsets which, followed from
  any starting vertex of any `d`-regular rotation graph on `Fin n`, visits the whole connected
  component of the starting vertex.  Reingold's zig-zag construction produces such sequences
  (and produces them log-space uniformly); that construction is *not* formalised here and is
  the reason the results below are stated conditionally on `CS.HasPolyUES`.

Everything else is proved: that the exploration walk never leaves the connected component
(soundness), that the resulting machine is correct on all inputs, that its configuration
space is polynomially bounded — hence it uses logarithmic space — and that consequently every
symmetric nondeterministic space-bounded machine can be simulated deterministically with only
a polynomial blow-up of the configuration space (`SL ⊆ L`).

The companion file `RequestProject/UESExistence.lean` proves unconditionally that universal
exploration sequences of *some* finite (in general exponential) length always exist
(`CS.exists_ues`), so `CS.HasPolyUES` is a statement purely about their *length*; making the
length polynomial is exactly what Reingold's construction achieves.

Two caveats on the formalisation.  First, the converse inclusion `L ⊆ SL` is the easy standard
one and is not formalised here.  Second, the statements quantify, for each input size, over the
existence of a machine; the machine is built from the exploration sequence by one fixed recipe
(`CS.Machine.connMachine`), so log-space uniformity of Reingold's sequences yields a uniform
algorithm, but uniformity of the family is not itself part of the formal statements.
-/

set_option autoImplicit false

namespace CS

/-! ## Rotation graphs -/

/-- An undirected `d`-regular multigraph on `Fin n`, given by its rotation map:
`rot (v, i) = (w, j)` says that the `i`-th edge at `v` leads to `w`, where it is the `j`-th
edge.  The involutivity of `rot` is exactly the statement that the graph is undirected. -/
structure RotGraph (n d : ℕ) where
  /-- The rotation map. -/
  rot : Fin n × Fin d → Fin n × Fin d
  /-- The rotation map is an involution. -/
  rot_involutive : Function.Involutive rot

/-- Add an offset to an edge label (the argument `i : Fin d` witnesses `0 < d`). -/
