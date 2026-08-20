/-
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace ConeLine

/-- The `n`-th triangular number, `T n = n(n+1)/2` (natural-number division,
which is exact since `n(n+1)` is even). -/

lemma T_add_ten_mod_five (n : ℕ) : T (n + 10) % 5 = T n % 5 := by
  have hx : (n + 10) * (n + 10 + 1) = n * (n + 1) + 20 * n + 110 := by ring
  have h2 : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
  unfold T
  rw [hx]
  omega

/-- Modulo `5`, a triangular number is `0`, `1` or `3`. -/
