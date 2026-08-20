/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Statement: State the Bekenstein bound S ≤ 2πkRE/ℏc.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Note: Lean 4 requires `import` to be the first command in a file, so this header is written as a
plain block comment `/- ... -/` rather than a module docstring `/-! ... -/`; the text is otherwise
exactly as specified.
-/

import Mathlib

open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Phys

/-- The Bekenstein bound `2 π k R E / (ℏ c)` on the entropy of a system of energy `E`
contained in a sphere of radius `R`. -/

theorem deriv_bhEntropy (k hbar c G M : ℝ) :
    deriv (bhEntropy k hbar c G) M = 8 * Real.pi * k * G * M / (hbar * c) :=
  (hasDerivAt_bhEntropy k hbar c G M).deriv

/-- **The Bekenstein bound.**

A system of energy `E` fitting inside a sphere of radius `R` has entropy at most
`2 π k R E / (ℏ c)`.

Following Bekenstein's derivation, the physical input is the generalized second law: when the
system is lowered to the horizon of a Schwarzschild black hole of mass `M` and dropped in, the
black hole's entropy must increase by at least the entropy `S` lost from the exterior, i.e.
`S ≤ (d S_BH / d M) (M) * ΔM`, where `ΔM = E R / (4 G M)` is the mass delivered.  Given that
law, the bound `S ≤ 2 π k R E / (ℏ c)` is an exact identity: all reference to the auxiliary
black hole (its mass `M` and Newton's constant `G`) cancels. -/
