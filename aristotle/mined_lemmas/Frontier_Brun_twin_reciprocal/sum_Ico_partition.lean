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

lemma sum_Ico_partition (h : ℕ → ℝ) {m J : ℕ} (hmJ : m ≤ J) :
    ∑ i ∈ Ico (aa m) (aa J), h i = ∑ j ∈ Ico m J, ∑ i ∈ Ico (aa j) (aa (j+1)), h i := by
  induction J, hmJ using Nat.le_induction with
  | base => simp
  | succ J hJ ih =>
    rw [Finset.sum_Ico_succ_top hJ, ← ih,
      Finset.sum_Ico_consecutive _ (aa_mono hJ) (aa_mono (Nat.le_succ J))]

/-- The comparison series. -/
