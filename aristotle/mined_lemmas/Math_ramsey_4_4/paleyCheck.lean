import Mathlib
/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset

/-! ## Upper bound: every 2-colouring of `K₁₈` has a monochromatic `K₄`

We phrase a 2-colouring of the edges of a complete graph as a simple graph `G`
(the "red" edges); the "blue" edges are the edges of the complement `Gᶜ`.
-/

section Core

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The neighbours of `v` inside the finite set `s`. -/

def paleyCheck : Bool :=
  (List.range 17).all fun a =>
    (List.range 17).all fun b => (a == b) ||
      ((List.range 17).all fun c => (a == c) || (b == c) ||
        ((List.range 17).all fun d => (a == d) || (b == d) || (c == d) ||
          !((padj a c == padj a b) && (padj a d == padj a b) && (padj b c == padj a b) &&
            (padj b d == padj a b) && (padj c d == padj a b))))

