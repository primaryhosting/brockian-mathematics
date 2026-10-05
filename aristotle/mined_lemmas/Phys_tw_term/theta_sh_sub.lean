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

lemma theta_sh_sub (c : Conf n L) (hc : M2 c = 0) :
    theta (sh c) - theta c = Real.pi * (w n (c 0) : ℝ) := by
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  have h1 : ∑ j : ZMod L, (j.val : ℝ) * (w n ((sh c) j) : ℝ)
      = ∑ k : ZMod L, (((k - 1).val : ℕ) : ℝ) * (w n (c k) : ℝ) :=
    Fintype.sum_bijective (fun j : ZMod L => j + 1) (Equiv.addRight (1 : ZMod L)).bijective _ _
      (fun j => by simp [sh])
  have h2 : ∀ k : ZMod L,
      (((k - 1).val : ℕ) : ℝ) = (k.val : ℝ) - 1 + (if k = 0 then (L : ℝ) else 0) := by
    intro k
    have h3 := congrArg (fun z : ℤ => (z : ℝ)) (zmod_val_sub_one (L := L) k)
    push_cast at h3
    simpa using h3
  have hsum : ∑ k : ZMod L, (w n (c k) : ℝ) = 0 := by
    have h4 : ((M2 c : ℤ) : ℝ) = ∑ k : ZMod L, (w n (c k) : ℝ) := by
      rw [M2]; push_cast; ring
    rw [← h4, hc]; simp
  have hzero : ∑ k : ZMod L, (if k = 0 then (L : ℝ) else 0) * (w n (c k) : ℝ)
      = (L : ℝ) * (w n (c 0) : ℝ) := by
    rw [Finset.sum_congr rfl (fun k _ => by
      by_cases hk : k = 0 <;> simp [hk] :
      ∀ k ∈ Finset.univ, (if k = 0 then (L : ℝ) else 0) * (w n (c k) : ℝ)
        = if k = 0 then (L : ℝ) * (w n (c k) : ℝ) else 0)]
    simp
  calc theta (sh c) - theta c
      = (Real.pi / L) * ∑ k : ZMod L,
          ((((k - 1).val : ℕ) : ℝ) - (k.val : ℝ)) * (w n (c k) : ℝ) := by
        rw [theta, theta, h1, ← mul_sub, ← Finset.sum_sub_distrib]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => by ring)
    _ = (Real.pi / L) * (-(∑ k : ZMod L, (w n (c k) : ℝ))
          + ∑ k : ZMod L, (if k = 0 then (L : ℝ) else 0) * (w n (c k) : ℝ)) := by
        rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => by rw [h2 k]; ring)
    _ = Real.pi * (w n (c 0) : ℝ) := by
        rw [hsum, hzero, neg_zero, zero_add]
        field_simp

/-! ## Part III: the Lieb-Schultz-Mattis theorem -/

