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

lemma count_periodic_approx (M : ℕ) (hM : 0 < M) (hper : ∀ n, P (n + M) ↔ P n) (N : ℕ) :
    |(#((range N).filter P) : ℝ) - N * (#((range M).filter P) : ℝ) / M| ≤
      #((range M).filter P) := by
  set ρ := #((range M).filter P) with hρ
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < M ∧ N = q * M + s :=
    ⟨N / M, N % M, Nat.mod_lt _ hM, by rw [Nat.mul_comm]; exact (Nat.div_add_mod N M).symm⟩
  rw [count_mul_period P M hper]
  have hle : #((range s).filter P) ≤ ρ := count_mono P s M hs.le
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hsM : (s:ℝ) ≤ M := by exact_mod_cast hs.le
  have hle' : ((#((range s).filter P) : ℕ) : ℝ) ≤ (ρ:ℝ) := by exact_mod_cast hle
  have hnn : (0:ℝ) ≤ ((#((range s).filter P) : ℕ) : ℝ) := by positivity
  have hρ0 : (0:ℝ) ≤ (ρ:ℝ) := by positivity
  have key : (((q:ℝ) * M + s)) * (ρ:ℝ) / M = q * ρ + s * ρ / M := by field_simp
  push_cast
  rw [key]
  have hb1 : (0:ℝ) ≤ (s:ℝ) * ρ / M := by positivity
  have hb2 : (s:ℝ) * ρ / M ≤ ρ := by
    rw [div_le_iff₀ hM']
    nlinarith
  rw [abs_le]
  constructor <;> linarith

end Periodic

/-- There is exactly one `n < a b` with `a ∣ n` and `b ∣ n + 2`, when `a` and `b` are coprime. -/
