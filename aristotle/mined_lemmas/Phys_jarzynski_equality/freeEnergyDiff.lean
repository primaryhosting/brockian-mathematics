/-
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Canonical partition function `Z = ∑ₓ e^{-β H(x)}` of a finite classical system. -/

noncomputable def freeEnergyDiff (beta : ℝ) (H₀ H₁ : Ω → ℝ) : ℝ :=
  -(1 / beta) * Real.log (partitionFunction (Ω := Ω) beta H₁ / partitionFunction (Ω := Ω) beta H₀)

/-- **Jarzynski equality.**  For a finite classical system initially in the Gibbs state of `H₀`
at inverse temperature `β ≠ 0`, driven by a measure-preserving (Liouville) evolution `phi`
to a final energy function `H₁`, the equilibrium average of `e^{-βW}` over initial microstates
equals `e^{-βΔF}`, where `ΔF` is the free-energy difference of the two equilibrium ensembles. -/
