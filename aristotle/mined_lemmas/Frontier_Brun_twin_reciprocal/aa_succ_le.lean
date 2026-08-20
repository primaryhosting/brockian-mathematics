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

lemma aa_succ_le (j : ℕ) : 4 * (aa (j+1) : ℝ) * Real.exp (-(j:ℝ)) ≤ vv j := by
  have hnat : E (j+1) ≤ 116 * (j+1) * 2^j := by
    have hx : 1 ≤ (2:ℕ)^j := Nat.one_le_two_pow
    have hE : E (j+1) = (2*2^j + 2) * (4*j + 14) + 4*j + 15 := by
      unfold E
      rw [pow_succ]
      ring
    rw [hE]
    nlinarith
  have hR : (aa (j+1) : ℝ) ≤ 232 * ((j:ℝ)+1) * 2^j := by
    have haa : (aa (j+1) : ℝ) = 2 * (E (j+1) : ℝ) := by unfold aa; push_cast; ring
    rw [haa]
    have h2 : ((E (j+1) : ℕ) : ℝ) ≤ 116 * ((j:ℝ)+1) * 2^j := by
      exact_mod_cast hnat
    linarith
  have hexp : (0:ℝ) < Real.exp (-(j:ℝ)) := Real.exp_pos _
  have hgeom : (2/Real.exp 1 : ℝ)^j = 2^j * Real.exp (-(j:ℝ)) := by
    rw [div_pow, ← Real.exp_nat_mul]
    rw [Real.exp_neg]
    field_simp
  unfold vv
  rw [hgeom]
  nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) j]

/-- The tail sum bound. -/
