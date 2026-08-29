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
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math2

/-! ## The singular plane curves `y ^ n = x ^ (n + 1)` and their normalization -/

/-- The plane affine curve `C_n : y ^ n = x ^ (n + 1)` over a field `k`.
For `n ≥ 2` this curve has a single singular point, at the origin
(for `n = 2` it is the classical cuspidal cubic `y ^ 2 = x ^ 3`). -/

lemma cuspCurve_snd_ne_zero {k : Type*} [Field k] {n : ℕ} (hn : 1 ≤ n)
    {p : k × k} (hp : p ∈ cuspCurve k n) (hp0 : p ≠ (0, 0)) : p.2 ≠ 0 := by
  intro h
  have hx : p.1 ≠ 0 := cuspCurve_fst_ne_zero hn hp hp0
  have hx' : p.1 ^ (n + 1) = 0 := by
    have hp' : p.2 ^ n = p.1 ^ (n + 1) := hp
    rw [h, zero_pow (by omega : n ≠ 0)] at hp'
    exact hp'.symm
  exact hx ((pow_eq_zero_iff (by omega : n + 1 ≠ 0)).1 hx')

