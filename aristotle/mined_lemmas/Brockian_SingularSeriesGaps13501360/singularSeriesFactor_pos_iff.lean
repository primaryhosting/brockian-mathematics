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

lemma singularSeriesFactor_pos_iff (g : ℕ) : 0 < singularSeriesFactor g ↔ Even g := by
  constructor
  · intro h
    by_contra hg
    rw [singularSeriesFactor, if_neg hg] at h
    exact lt_irrefl 0 h
  · intro hg
    have := one_le_singularSeriesFactor hg
    linarith

/-- Explicit values of the singular series factor at the even gaps in `[1350, 1360]`. -/
