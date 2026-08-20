/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Lean requires `import` to precede any module docstring, so the header is
repeated as a module docstring immediately after the import below.)
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix

/-- Square complex matrices of size `Fin d`. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

variable {d : ℕ}

/-- The real part of the trace. -/

lemma frobSq_add {X Y : Mat d} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    frobSq (X + Y) = frobSq X + 2 * rinner X Y + frobSq Y := by
  rw [frobSq_eq_rinner (hX.add hY), frobSq_eq_rinner hX, frobSq_eq_rinner hY,
    rinner_add_left, rinner_add_right, rinner_add_right, rinner_comm Y X]
  ring

/-- Young's inequality for the Frobenius inner product. -/
