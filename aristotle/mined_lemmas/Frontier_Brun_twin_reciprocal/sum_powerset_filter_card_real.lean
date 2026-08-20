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

lemma sum_powerset_filter_card_real (R : Finset ℕ) (K : ℕ) (f : ℕ → ℝ) :
    ∑ T ∈ R.powerset.filter (fun T => T.card ≤ K), f T.card
      = ∑ j ∈ range (K+1), (R.card.choose j : ℝ) * f j := by
  classical
  have hset : R.powerset.filter (fun T => T.card ≤ K)
      = (range (K+1)).biUnion (fun j => R.powersetCard j) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Nat.lt_succ_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨T.card, h2, h1, rfl⟩
    · rintro ⟨a, ha, h1, rfl⟩
      exact ⟨h1, ha⟩
  rw [hset, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (fun T hT => by rw [(Finset.mem_powersetCard.1 hT).2] :
      ∀ T ∈ R.powersetCard j, f T.card = f j)]
    rw [Finset.sum_const, Finset.card_powersetCard]
    simp [mul_comm]
  · intro i _ j _ hij
    simp only [Finset.disjoint_left]
    intro T hT hT'
    exact hij ((Finset.mem_powersetCard.1 hT).2 ▸ (Finset.mem_powersetCard.1 hT').2 ▸ rfl)

/-- The error term of the sieve. -/
