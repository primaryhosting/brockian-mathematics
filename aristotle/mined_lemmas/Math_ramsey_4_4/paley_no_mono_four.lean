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

theorem paley_no_mono_four (a b c d : ℕ) (ha : a < 17) (hb : b < 17) (hc : c < 17) (hd : d < 17)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (x : Bool) (h1 : padj a b = x) (h2 : padj a c = x) (h3 : padj a d = x)
    (h4 : padj b c = x) (h5 : padj b d = x) (h6 : padj c d = x) : False := by
  have H := paleyCheck_true
  simp only [paleyCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at H
  rcases H a ha b hb with h | H
  · exact hab h
  rcases H c hc with (h | h) | H
  · exact hac h
  · exact hbc h
  rcases H d hd with ((h | h) | h) | H
  · exact had h
  · exact hbd h
  · exact hcd h
  · simp [h1, h2, h3, h4, h5, h6] at H

/-- The Paley graph of order `17`, restricted to the first `n` vertices. -/
