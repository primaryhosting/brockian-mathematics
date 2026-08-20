import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

@[simp] theorem iso_smul_def (f : E ≃ᵢ E) (x : E) : f • x = f x := rfl

instance : MulAction (E ≃ᵢ E) E where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Every linear isometry of `ℝ³` is an isometry of `ℝ³`; as a group homomorphism. -/
