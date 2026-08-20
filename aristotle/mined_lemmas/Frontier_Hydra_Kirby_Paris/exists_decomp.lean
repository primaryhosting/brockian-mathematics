import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open Ordinal
open scoped NaturalOps

namespace Frontier

/-!
## Part 1: `ω ^ c` is principal for natural (Hessenberg) addition

Mathlib knows that `ω ^ c` is principal for ordinary ordinal addition, but not for the
natural sum `♯`.  We prove this here, since the ordinal assignment used for the hydra
game relies on it.
-/

/-- Every ordinal below `ω ^ d * ω` can be written as `ω ^ d * m + r` with `m` a natural
number and `r < ω ^ d`. -/

theorem exists_decomp (d x : Ordinal) (hx : x < ω ^ d * ω) :
    ∃ (m : ℕ) (r : Ordinal), r < ω ^ d ∧ x = ω ^ d * (m : Ordinal) + r := by
  have hne : (ω : Ordinal) ^ d ≠ 0 := (Ordinal.opow_pos d omega0_pos).ne'
  have hq : x / ω ^ d < ω := (Ordinal.div_lt hne).2 hx
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.1 hq
  refine ⟨m, x % ω ^ d, Ordinal.mod_lt _ hne, ?_⟩
  rw [← hm]
  exact (Ordinal.div_add_mod x (ω ^ d)).symm

