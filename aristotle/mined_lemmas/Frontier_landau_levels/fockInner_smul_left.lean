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

theorem fockInner_smul_left (p q : ℕ →₀ ℂ) (r : ℂ) :
    fockInner (r • p) q = conj r * fockInner p q := by
  rw [fockInner_eq_sum (p := r • p) (q := q) (s := p.support) Finsupp.support_smul,
    fockInner_eq_sum (p := p) (q := q) (s := p.support) subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [Finsupp.smul_apply]
  ring

