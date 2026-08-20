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

import Mathlib

/-!
# Admissible tuples and positivity of the singular series

An `H : Finset ℕ` (thought of as a set of *gaps* / offsets of a prime constellation
`n + h`, `h ∈ H`) is **admissible** when, for every prime `p`, the reductions of `H`
modulo `p` do not cover all residue classes.  This is exactly the condition under which
the local factors of the Hardy–Littlewood singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p) (1 - 1/p)^(-|H|)` are all positive.

This file develops the basic theory and a general criterion producing admissible sets:
a set of size at most `m`, all of whose elements are coprime to `m !`, is admissible.
-/

open scoped BigOperators Nat

namespace Brockian

/-- The number of residue classes mod `p` occupied by `H`, i.e. `ν_H(p)`. -/

theorem admissible_image_add {H : Finset ℕ} (hH : Admissible H) (t : ℕ) :
    Admissible (H.image (· + t)) := by
  intro p hp
  obtain ⟨r, hr, hmiss⟩ := hH p hp
  refine ⟨(r + t) % p, Nat.mod_lt _ hp.pos, ?_⟩
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  intro hcon
  have hmod : a ≡ r [MOD p] := Nat.ModEq.add_right_cancel' t hcon
  exact hmiss a ha (by rwa [Nat.ModEq, Nat.mod_eq_of_lt hr] at hmod)

/-- **Main criterion.**  A set of at most `m` natural numbers, each coprime to `m !`,
is admissible. -/
