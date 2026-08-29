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

lemma cov_goldbach_eq {S : Finset ℕ} (hS : S.Nonempty) (g : ℕ → ℝ) :
    cov S goldbachIndicator g =
      mean S exceptionIndicator * mean S g - mean S (fun n => exceptionIndicator n * g n) := by
  have hχ : goldbachIndicator = fun n => (1 : ℝ) - exceptionIndicator n := by
    funext n; simp [exceptionIndicator]
  have m1 : mean S goldbachIndicator = 1 - mean S exceptionIndicator := by
    rw [hχ, mean_sub, mean_const_one hS]
  have m2 : mean S (fun n => goldbachIndicator n * g n)
      = mean S g - mean S (fun n => exceptionIndicator n * g n) := by
    have hfun : (fun n => goldbachIndicator n * g n)
        = fun n => g n - exceptionIndicator n * g n := by
      funext n; rw [hχ]; ring
    rw [hfun, mean_sub]
  rw [cov, m1, m2]; ring

/--
**Goldbach Covariance Transfer.**

For any finite sample `S` of naturals and any weight `g` bounded by `M` on `S`,
the empirical covariance of the Goldbach indicator with `g` is controlled by the empirical
density of Goldbach exceptions in `S`:
`|cov S goldbachIndicator g| ≤ 2 * (density of exceptions) * M`.

In particular, if the Goldbach conjecture holds on `S`, the covariance vanishes identically
(see `cov_goldbach_eq_zero`).
-/
