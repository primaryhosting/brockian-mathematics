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

theorem sieve_main (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ p ≠ 2) (N K : ℕ) (hK : Even K) :
    (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℝ)
      ≤ N * (∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K),
              (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ)))
        + ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (2:ℝ)^T.card := by
  have hint := sifted_le Q N K hK
  have hcast : (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℝ)
      ≤ ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (-1:ℝ)^T.card *
          #((range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2))) := by
    exact_mod_cast hint
  refine hcast.trans ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun T hT => ?_
  have hTQ : T ⊆ Q := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
  have hTodd : ∀ p ∈ T, p.Prime ∧ p ≠ 2 := fun p hp => hQ p (hTQ hp)
  have happrox := card_divisible_approx T hTodd N
  have hprod : (N : ℝ) * 2 ^ T.card / (∏ p ∈ T, (p:ℕ) : ℕ) = N * ∏ p ∈ T, (2/(p:ℝ)) := by
    rw [Finset.prod_div_distrib, Finset.prod_const]
    push_cast
    ring
  rw [hprod] at happrox
  rw [abs_le] at happrox
  set A := (#((range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2))) : ℝ) with hA
  set M := (N : ℝ) * ∏ p ∈ T, (2/(p:ℝ)) with hM
  have key : (-1:ℝ)^T.card * A ≤ (-1:ℝ)^T.card * M + 2^T.card := by
    rcases Nat.even_or_odd T.card with h | h
    · rw [h.neg_one_pow]; linarith [happrox.2]
    · rw [h.neg_one_pow]; linarith [happrox.1]
  refine key.trans ?_
  rw [hM]
  ring_nf
  exact le_rfl

end Brun

