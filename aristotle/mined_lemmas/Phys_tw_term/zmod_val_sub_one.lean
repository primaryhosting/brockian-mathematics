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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Part I: an abstract twist (flux insertion) estimate

We model a quantum system on a finite configuration space `α`: states are functions
`ψ : α → ℂ`, the (squared) norm is `∑ c, ‖ψ c‖^2`, and a Hamiltonian is a matrix
`H : α → α → ℂ`.  `qf H ψ` is the energy expectation `⟪ψ, H ψ⟫` (real part).
-/

section Abstract

variable {α : Type*} [Fintype α]

/-- The energy expectation value `⟪ψ, H ψ⟫` (real part). -/

lemma zmod_val_sub_one (k : ZMod L) :
    ((k - 1).val : ℤ) = (k.val : ℤ) - 1 + (if k = 0 then (L : ℤ) else 0) := by
  by_cases h : k = 0
  · subst h
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    have he : (0 - 1 : ZMod L) = ((L - 1 : ℕ) : ZMod L) := by
      push_cast [Nat.cast_sub hL]; simp
    rw [he, ZMod.val_natCast_of_lt (by omega)]
    simp
    omega
  · have hk : k.val ≠ 0 := (ZMod.val_ne_zero k).mpr h
    have h1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.2 hk
    have hlt : k.val < L := ZMod.val_lt k
    have he : k - 1 = ((k.val - 1 : ℕ) : ZMod L) := by
      rw [Nat.cast_sub h1]; simp [ZMod.natCast_val, ZMod.cast_id]
    rw [he, ZMod.val_natCast_of_lt (by omega)]
    simp [h]

