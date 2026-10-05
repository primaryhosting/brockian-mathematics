import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MvPolynomial

/-! ## Setting up plane curves over `ℚ` -/

/-- The set of `ℚ`-rational points of the projective plane curve cut out by a homogeneous
form `F` in three variables. A point of `ℙ²(ℚ)` is represented as a point of
`Projectivization ℚ (Fin 3 → ℚ)`; since `F` is homogeneous, vanishing of `F` at a
representative does not depend on the chosen representative (see
`Frontier.mem_projPoints_fermatForm_iff` for the case used below). -/

theorem mem_projPoints_fermatForm_iff (n : ℕ) (v : Fin 3 → ℚ) (hv : v ≠ 0) :
    Projectivization.mk ℚ v hv ∈ projPoints (fermatForm n) ↔
      v 0 ^ n + v 1 ^ n - v 2 ^ n = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℚ v hv
  have hrep : (Projectivization.mk ℚ v hv).rep = (a : ℚ) • v := by
    rw [← ha]; rfl
  simp only [projPoints, Set.mem_setOf_eq, hrep, eval_fermatForm, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    have ha' : ((a : ℚ)) ^ n ≠ 0 := pow_ne_zero _ a.ne_zero
    have : ((a : ℚ)) ^ n * (v 0 ^ n + v 1 ^ n - v 2 ^ n) = 0 := by
      rw [← h]; ring
    exact (mul_eq_zero.mp this).resolve_left ha'
  · intro h
    have : ((a : ℚ) * v 0) ^ n + ((a : ℚ) * v 1) ^ n - ((a : ℚ) * v 2) ^ n
        = ((a : ℚ)) ^ n * (v 0 ^ n + v 1 ^ n - v 2 ^ n) := by ring
    rw [this, h, mul_zero]

/-! ### Smoothness of the Fermat curve -/

