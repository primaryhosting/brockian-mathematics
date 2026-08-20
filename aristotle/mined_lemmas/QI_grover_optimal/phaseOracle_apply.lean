import Mathlib

/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
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

namespace QI

/-- The Hilbert space of a quantum query algorithm searching a database of `N` items:
the index register `Fin N` together with an arbitrary workspace register `K`. -/
abbrev HSpace (N : ℕ) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  PiLp 2 (fun _ : Fin N => K)

variable {N : ℕ} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The (phase) query operator for the database whose unique marked item is `x`:
it flips the sign of the component of the index register at `x`. -/

@[simp] lemma phaseOracle_apply (x y : Fin N) (psi : HSpace N K) :
    (phaseOracle x psi) y = if y = x then -(psi y) else psi y := rfl

/-- The state of a quantum query algorithm after `t` queries: it starts in `psi0`, and each
step consists of one oracle call followed by an (input independent) unitary. -/
