/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring before the `import` line; the required
header is reproduced verbatim below as the module docstring.)
-/

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
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

namespace Frontier

open Finset Set

/-! ## Finite games in normal form -/

section Defs

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The set of mixed strategy profiles of a finite game: for each player `i` a probability
distribution on that player's (finite) pure strategy set `S i`. -/

lemma mapsTo_nashMap : Set.MapsTo (nashMap u) (mixedProfiles S) (mixedProfiles S) := by
  intro x hx i _
  have hxi : x i ∈ stdSimplex ℝ (S i) := hx i (Set.mem_univ i)
  have hden : (0:ℝ) < 1 + ∑ t, max 0 (gain u x i t) := lt_of_lt_of_le one_pos (one_le_nashDen u x i)
  constructor
  · intro s
    have h1 : 0 ≤ x i s + max 0 (gain u x i s) :=
      add_nonneg (hxi.1 s) (le_max_left _ _)
    exact div_nonneg h1 hden.le
  · show ∑ s, nashMap u x i s = 1
    unfold nashMap
    rw [← Finset.sum_div, Finset.sum_add_distrib, hxi.2]
    field_simp

