/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is kept as a plain block comment because Lean 4 does not
-- allow a module docstring `/-! ... -/` to precede the `import` command.)

import Mathlib

namespace QC

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, described as a vector in the
Hilbert space `ℂ^(Fin 8 → Bool)` of 8 qubits: its amplitude is `1/√2` on the two
computational basis states `|00000000⟩` and `|11111111⟩`, and `0` elsewhere. -/

theorem ghz8_eq : ghz8 = ((Real.sqrt 2)⁻¹ : ℝ) •
    (EuclideanSpace.single (fun _ => false) (1 : ℂ)
      + EuclideanSpace.single (fun _ => true) (1 : ℂ)) := by
  have hft : ¬ ((fun _ => false : Fin 8 → Bool) = fun _ => true) := by
    intro hcon; simpa using congrFun hcon 0
  ext v
  by_cases h0 : ∀ i, v i = false
  · have hv : v = fun _ => false := funext h0
    subst hv
    simp [ghz8, EuclideanSpace.single_apply, hft]
  · by_cases h1 : ∀ i, v i = true
    · have hv : v = fun _ => true := funext h1
      subst hv
      simp [ghz8, EuclideanSpace.single_apply, Ne.symm hft]
    · have hne0 : v ≠ fun _ => false := fun hc => h0 (fun i => by rw [hc])
      have hne1 : v ≠ fun _ => true := fun hc => h1 (fun i => by rw [hc])
      simp [ghz8, EuclideanSpace.single_apply, h0, h1, hne0, hne1]

/-- Equivalent inner-product form of normalization: `⟪ghz8, ghz8⟫ = 1`. -/
