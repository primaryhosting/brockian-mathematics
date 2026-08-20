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

def HasDistanceGE (M : Matrix (Fin n → Fin q) (Fin K) ℂ) (d : ℕ) : Prop :=
  ∀ (T : Finset (Fin n)) (E : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ),
    T.card < d → SupportedOn T E → ∃ lam : ℂ, Mᴴ * E * M = lam • (1 : Matrix (Fin K) (Fin K) ℂ)

/-- Sanity check: any isometric encoding has distance at least one, so the Knill–Laflamme
condition above is satisfiable. -/
