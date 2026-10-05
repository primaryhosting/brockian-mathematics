/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open MulAction Subgroup

/-- From an element whose order is divisible by `p` we get an element of order exactly `p`. -/

theorem exists_orderOf_eq_of_dvd_orderOf {G : Type*} [Group G] [Finite G] {p : ℕ}
    (x : G) (hdvd : p ∣ orderOf x) : ∃ g : G, orderOf g = p :=
  ⟨x ^ (orderOf x / p), orderOf_pow_orderOf_div (orderOf_pos x).ne' hdvd⟩

/-- The size of the conjugacy class of `g` times the size of its centralizer is `|G|`. -/
