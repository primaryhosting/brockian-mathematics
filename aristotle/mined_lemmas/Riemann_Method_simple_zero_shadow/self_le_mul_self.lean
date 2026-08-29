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

private theorem self_le_mul_self (k : Nat) : k ≤ k * k := by
  rcases k with _ | j
  · exact Nat.le_refl 0
  · exact Nat.le_mul_of_pos_left _ (Nat.succ_pos j)

/-- **Simple zero shadow.**  For every natural number `m` with `1 ≤ m` we have
`2 * m ≤ m ^ 2 + 1`, and equality holds precisely when `m = 1`.
This is the integrality step `(m - 1) ^ 2 ≥ 0` that separates simple zeros in
Montgomery's two-thirds argument. -/
