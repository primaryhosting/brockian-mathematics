import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean 4 requires `import` to precede every command, including module docstrings,
so the required header is reproduced verbatim as a module docstring just below
the import as well.)
-/

import Mathlib

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian
namespace GoldbachComb

/-! ## Averages and covariance over a finite sample -/

/-- The empirical mean of `f` over a finite set `S` of naturals. -/

theorem cov_goldbach_eq_zero {S : Finset ℕ} (hS : S.Nonempty) (g : ℕ → ℝ)
    (hgold : ∀ n ∈ S, IsGoldbach n) : cov S goldbachIndicator g = 0 := by
  have hz : ∀ n ∈ S, exceptionIndicator n = 0 := fun n hn => exceptionIndicator_eq_zero (hgold n hn)
  have m1 : mean S exceptionIndicator = 0 := by
    rw [mean, Finset.sum_congr rfl hz]; simp
  have m2 : mean S (fun n => exceptionIndicator n * g n) = 0 := by
    rw [mean, Finset.sum_congr rfl (fun n hn => by rw [hz n hn, zero_mul])]; simp
  rw [cov_goldbach_eq hS, m1, m2]; ring

end GoldbachComb
end Brockian

