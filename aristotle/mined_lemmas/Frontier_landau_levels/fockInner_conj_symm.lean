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

theorem fockInner_conj_symm (p q : ℕ →₀ ℂ) : conj (fockInner q p) = fockInner p q := by
  rw [fockInner_eq_sum (q := p) (s := p.support ∪ q.support) Finset.subset_union_right,
    fockInner_eq_sum (q := q) (s := p.support ∪ q.support) Finset.subset_union_left, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [mul_comm, mul_left_comm]

