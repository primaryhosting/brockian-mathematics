import Mathlib

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

namespace Brockian

/-! # Admissible gap ranges and the Hardy–Littlewood singular series for prime pairs

For a gap `g` we consider the two–element pattern `{0, g}`.  Such a pattern is
*admissible* when, for every prime `p`, its residues do not cover all of `ZMod p`.
The Hardy–Littlewood singular series of the pattern `{0, g}` is
`𝔖(g) = 2 C₂ ∏_{p ∣ g, p odd} (p-1)/(p-2)` for even `g`, and `0` for odd `g`;
here we work with the arithmetic factor `∏_{p ∣ g, p odd} (p-1)/(p-2)` and with the
convention that the factor vanishes for odd `g` (matching the vanishing of `𝔖`).
-/

/-- A finite pattern `H ⊆ ℤ` is *admissible* if for every prime `p` some residue class
mod `p` is missed by `H`. -/

noncomputable def singularSeriesFactor (g : ℕ) : ℝ :=
  if Even g then ∏ p ∈ g.primeFactors with p ≠ 2, ((p : ℝ) - 1) / ((p : ℝ) - 2) else 0

/-- A pattern with fewer elements than `p` misses a residue class mod `p`. -/
