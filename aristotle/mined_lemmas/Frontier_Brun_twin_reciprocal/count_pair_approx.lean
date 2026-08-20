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

lemma count_pair_approx (a b N : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    |(#((range N).filter (fun n => a ∣ n ∧ b ∣ n + 2)) : ℝ) - N / (a*b)| ≤ 1 := by
  classical
  have hper : ∀ n : ℕ, (a ∣ n + a*b ∧ b ∣ (n + a*b) + 2) ↔ (a ∣ n ∧ b ∣ n + 2) := by
    intro n
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(Nat.dvd_add_iff_left (⟨b, rfl⟩ : a ∣ a*b)).2 h1, ?_⟩
      have h3 : n + a*b + 2 = (n + 2) + a*b := by ring
      rw [h3] at h2
      exact (Nat.dvd_add_iff_left (⟨a, by ring⟩ : b ∣ a*b)).2 h2
    · rintro ⟨h1, h2⟩
      refine ⟨Dvd.dvd.add h1 ⟨b, rfl⟩, ?_⟩
      have h3 : n + a*b + 2 = (n + 2) + a*b := by ring
      rw [h3]
      exact Dvd.dvd.add h2 ⟨a, by ring⟩
  have := count_periodic_approx (fun n => a ∣ n ∧ b ∣ n + 2) (a*b) (by positivity) hper N
  rw [crt_count_one a b ha hb hab] at this
  simpa using this


/-- The decomposition of the counted set according to which primes divide `n` (rather
than `n + 2`). -/
