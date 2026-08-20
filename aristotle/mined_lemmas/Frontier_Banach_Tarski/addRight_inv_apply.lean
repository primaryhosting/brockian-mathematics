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

theorem addRight_inv_apply (b x : E) : (IsometryEquiv.addRight b)⁻¹ x = x - b := by
  have h : (IsometryEquiv.addRight b) ((IsometryEquiv.addRight b)⁻¹ x) = x :=
    IsometryEquiv.apply_inv_self _ _
  have h2 : (IsometryEquiv.addRight b) (x - b) = x := by
    show x - b + b = x
    abel
  exact (IsometryEquiv.addRight b).injective (h.trans h2.symm)

