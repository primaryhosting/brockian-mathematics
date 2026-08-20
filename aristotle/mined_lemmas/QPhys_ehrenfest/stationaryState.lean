/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The commutator `[H, A] = H A - A H` of two continuous linear operators. -/

noncomputable def stationaryState (hbar E0 : ℝ) (v : E) : ℝ → E :=
  fun s => Complex.exp (-Complex.I * E0 * s / hbar) • v

/-- The stationary state solves the Schrödinger equation `ψ'(t) = (-i/ℏ) H ψ(t)`. -/
