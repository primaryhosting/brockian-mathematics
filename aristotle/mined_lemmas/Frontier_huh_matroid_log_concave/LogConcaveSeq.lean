import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

set_option grind.warning false

namespace Frontier

open Polynomial

variable {α : Type*}

/-- The natural-number rank function of a matroid. -/

def LogConcaveSeq (w : ℕ → ℕ) : Prop := ∀ i, w i * w (i + 2) ≤ w (i + 1) * w (i + 1)

/-! ### Binomial coefficients are log-concave -/

/-- The binomial coefficients `k ↦ C(n, k)` form a log-concave sequence. -/
