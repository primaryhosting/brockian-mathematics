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

theorem sifted_bound (hQ : ∀ p ∈ Q, p.Prime ∧ p ≠ 2) (N K : ℕ) (hK : Even K)
    (hKS : Real.exp 1 * (∑ p ∈ Q, 2/(p:ℝ)) + (∑ p ∈ Q, 2/(p:ℝ)) ≤ K + 1) :
    (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℝ)
      ≤ 2 * N * Real.exp (-(∑ p ∈ Q, 2/(p:ℝ))) + (K+1) * (2*Q.card + 2)^K := by
  classical
  have hQ3 : ∀ p ∈ Q, 3 ≤ p := by
    intro p hp
    have := (hQ p hp).1.two_le
    have := (hQ p hp).2
    omega
  set S := ∑ p ∈ Q, 2/(p:ℝ) with hS
  have h1 := sieve_main Q hQ N K hK
  have h2 := main_term_le Q hQ3 K
  have h3 := error_le Q K
  have htail : Real.exp (Real.exp 1 * S - (K+1)) ≤ Real.exp (-S) := by
    apply Real.exp_le_exp.2
    linarith
  have hNnn : (0:ℝ) ≤ N := by positivity
  calc (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℝ)
      ≤ N * (∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K),
              (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ)))
        + ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (2:ℝ)^T.card := h1
    _ ≤ N * (Real.exp (-S) + Real.exp (Real.exp 1 * S - (K+1))) + (K+1) * (2*Q.card + 2)^K := by
        gcongr
    _ ≤ N * (Real.exp (-S) + Real.exp (-S)) + (K+1) * (2*Q.card + 2)^K := by
        gcongr
    _ = 2 * N * Real.exp (-S) + (K+1) * (2*Q.card + 2)^K := by ring

end Brun

import Mathlib

/-!
# A Mertens-type lower bound for the sum of reciprocals of primes

We prove `∑_{p < N} 1/p ≥ log log N - log 2` for `N ≥ 3`, by the classical argument
`log N ≤ H_N ≤ (∑_{a ≤ N squarefree} 1/a) * (∑_b 1/b²) ≤ 2 ∏_{p < N} (1 + 1/p) ≤ 2 exp(∑ 1/p)`.
-/

open Finset

namespace Brun

/-- The sum of `1/b²` for `1 ≤ b ≤ n` is at most `2 - 1/n`. -/
