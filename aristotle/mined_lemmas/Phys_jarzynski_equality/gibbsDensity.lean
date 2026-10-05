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

variable {Ω : Type*} [Fintype Ω]

/-- The canonical partition function `Z = ∑ₓ e^{-βH(x)}` of a Hamiltonian `H`
on a finite phase space at inverse temperature `β`. -/

noncomputable def gibbsDensity (μ : Measure Ω) (β : ℝ) (H : Ω → ℝ) (x : Ω) : ℝ :=
  Real.exp (-β * H x) / partitionFunctionOn μ β H

/-- **Jarzynski equality on a general phase space.**  For a system prepared in thermal
equilibrium with respect to `H₀` and driven by a deterministic, measure-preserving
invertible evolution `φ` (Liouville's theorem), the equilibrium average of `e^{-βW}`
with `W(x) = H₁(φ x) - H₀(x)` equals `e^{-βΔF}`. -/
