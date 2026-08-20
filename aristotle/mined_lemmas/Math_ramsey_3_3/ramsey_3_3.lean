/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
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

namespace Math

/-- Pigeonhole: among five booleans, three are equal. -/

theorem ramsey_3_3 :
    (∀ f : Fin 6 → Fin 6 → Bool,
        ∃ a b c : Fin 6, a < b ∧ b < c ∧ f a b = f a c ∧ f a c = f b c) ∧
      (∃ g : Fin 5 → Fin 5 → Bool,
        ∀ a b c : Fin 5, a < b → b < c → ¬(g a b = g a c ∧ g a c = g b c)) :=
  ⟨exists_mono_triangle_six, ⟨pentagon, pentagon_no_mono_triangle⟩⟩

end Math

