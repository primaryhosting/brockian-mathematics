import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The commutator `[A, B] = AB - BA` of two linear operators on `E`. -/

def comm (A B : Module.End ℂ E) : Module.End ℂ E := A * B - B * A

