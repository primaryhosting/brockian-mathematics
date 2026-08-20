/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Module Kronecker ComplexOrder

namespace QI

/-! ## Linear algebra preliminaries -/

/-- Swap the first two factors of a triple product type. -/

noncomputable def curryEquiv (α κ : Type*) : ((α × κ) → ℂ) ≃ₗ[ℂ] (κ → (α → ℂ)) where
  toFun x := fun i a => x (a, i)
  map_add' x y := rfl
  map_smul' c x := rfl
  invFun y := fun p => y p.2 p.1
  left_inv x := by funext p; rfl
  right_inv y := by funext i a; rfl

/-- The submodule of `κ`-indexed families with all values in `W` is isomorphic to `κ → W`. -/
