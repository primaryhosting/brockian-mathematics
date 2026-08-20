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

@[simp] theorem linIso_smul_def (f : E ≃ₗᵢ[ℝ] E) (x : E) : f • x = f x := rfl

instance : MulAction (E ≃ₗᵢ[ℝ] E) E where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The group of isometries of `ℝ³` acts on `ℝ³`. -/
instance : SMul (E ≃ᵢ E) E := ⟨fun f x => f x⟩

