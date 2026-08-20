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

theorem SingularSeriesGapsValues13501360 :
    singularSeriesFactor 1350 = 8 / 3 ∧
    singularSeriesFactor 1352 = 12 / 11 ∧
    singularSeriesFactor 1354 = 676 / 675 ∧
    singularSeriesFactor 1356 = 224 / 111 ∧
    singularSeriesFactor 1358 = 576 / 475 ∧
    singularSeriesFactor 1360 = 64 / 45 := by
  have h1350 : Nat.primeFactors 1350 = {2, 3, 5} := by decide +kernel
  have h1352 : Nat.primeFactors 1352 = {2, 13} := by decide +kernel
  have h1354 : Nat.primeFactors 1354 = {2, 677} := by decide +kernel
  have h1356 : Nat.primeFactors 1356 = {2, 3, 113} := by decide +kernel
  have h1358 : Nat.primeFactors 1358 = {2, 7, 97} := by decide +kernel
  have h1360 : Nat.primeFactors 1360 = {2, 5, 17} := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [singularSeriesFactor, if_pos (by decide : Even 1350),
      if_pos (by decide : Even 1352), if_pos (by decide : Even 1354),
      if_pos (by decide : Even 1356), if_pos (by decide : Even 1358),
      if_pos (by decide : Even 1360), h1350, h1352, h1354, h1356, h1358, h1360] <;>
    norm_num [Finset.filter_insert, Finset.filter_singleton, Finset.prod_insert]

/-- **Admissible gap ranges, `1350 ≤ g ≤ 1360`.**  For every gap `g` in this range:
the pair pattern `{0, g}` is admissible exactly when `g` is even, which happens exactly
when the Hardy–Littlewood singular series factor of the pattern is positive; moreover on
this range that factor lies in `[1, 8/3]` for the even gaps, the extreme value `8/3`
being attained at `g = 1350`. -/
