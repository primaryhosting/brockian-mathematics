import Mathlib
/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
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

open TensorProduct

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a rational vector
space `V` (conjugation on the left factor, identity on `V`).  It is only `ℚ`-linear
(it is conjugate-linear over `ℂ`). -/

theorem hodgeConjectureAt_of_piece_eq_bot (X : HodgeVariety H) (p : ℕ)
    (hp : (X.hs p).piece p p = ⊥) : HodgeConjectureAt X p := by
  have hb := hodgeClasses_eq_bot_of_piece_eq_bot X p hp
  have hle := alg_le_hodgeClasses X p
  rw [hb] at hle
  rw [HodgeConjectureAt, hb, le_bot_iff.mp hle]

/-- Base case of the Hodge conjecture: it holds in codimension `0`, where every class is a
Hodge class and every class is a rational multiple of the fundamental class. -/
