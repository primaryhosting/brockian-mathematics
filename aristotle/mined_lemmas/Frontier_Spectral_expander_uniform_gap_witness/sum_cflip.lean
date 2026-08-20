/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-- Flip the `i`-th coordinate of a vertex of the hypercube. -/

lemma sum_cflip {k : ℕ} (i : Fin k) (g : (Fin k → Bool) → ℝ) :
    ∑ x : Fin k → Bool, g (cflip i x) = ∑ x : Fin k → Bool, g x :=
  Equiv.sum_comp ((cflip_involutive i).toPerm) g

/-- The `k`-dimensional hypercube graph `Q_k`: vertices are the `2^k` bit strings of length `k`,
two of which are adjacent iff they differ in exactly one coordinate. -/
