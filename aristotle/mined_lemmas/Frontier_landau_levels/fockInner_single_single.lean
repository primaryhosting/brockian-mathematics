import Mathlib
import RequestProject.Fock
/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
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

open scoped InnerProductSpace

/-- The cyclotron frequency `ω_c = q B / m` of a particle of charge `q` and mass `m`
in a uniform magnetic field of strength `B`. -/

theorem fockInner_single_single (m k : ℕ) (c d : ℂ) :
    fockInner (Finsupp.single m c) (Finsupp.single k d)
      = if m = k then (m ! : ℂ) * conj c * d else 0 := by
  rw [fockInner_eq_sum (s := {m}) Finsupp.support_single_subset]
  simp only [Finset.sum_singleton, Finsupp.single_apply]
  by_cases h : m = k <;> simp [h, eq_comm]

noncomputable instance : Inner ℂ (ℕ →₀ ℂ) := ⟨fockInner⟩

/-- The Bargmann inner product makes `ℕ →₀ ℂ` an inner product space. -/
