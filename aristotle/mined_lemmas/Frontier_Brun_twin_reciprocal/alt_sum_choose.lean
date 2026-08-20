import Mathlib
import RequestProject.Brun.Final

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the required header comment appears immediately after the imports.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The summand is `1/n` whenever `n` and `n + 2` are both prime, and `0` otherwise; the value of
its sum is Brun's constant.  Convergence is proved from scratch by a Brun pure sieve; see the
development in `RequestProject/Brun/`. -/

lemma alt_sum_choose (s K : ℕ) :
    ∑ j ∈ range (K+1), (-1:ℤ)^j * ((s+1).choose j) = (-1)^K * (s.choose K) := by
  induction K with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hpascal : ((s+1).choose (m+1) : ℤ) = s.choose m + s.choose (m+1) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.choose_succ_succ s m)
    rw [hpascal]
    ring

/-- Rewriting a sum over small subsets as a sum over cardinalities. -/
