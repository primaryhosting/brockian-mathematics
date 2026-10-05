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

@[simp] lemma comm_apply (A B : Module.End ℂ E) (v : E) :
    comm A B v = A (B v) - B (A v) := rfl

/-- Leibniz rule: `[A, BC] = B [A, C] + [A, B] C`. -/
