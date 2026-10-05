/-!
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann
namespace Method

/-- Expansion of `(k + 1) ^ 2`, stated with `Nat` multiplication so that `omega`
can treat `k * k` as an atom. -/

private theorem sq_succ_expand (k : Nat) : (k + 1) ^ 2 = k * k + 2 * k + 1 := by
  simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add]
  omega

/-- `k ≤ k * k` for every natural number `k`. -/
