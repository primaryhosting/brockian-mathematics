/-!
# Succ Mul Catalan Eq Choose
Category: Brockian External
Target: Brockian.CatalanClosed.succ_mul_catalan_eq_choose
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Lean Elab Command in
run_cmd do
  unless (← getEnv).contains `Nat.catalan do
    elabCommand (← `(command| abbrev $(mkIdent `Nat.catalan) : ℕ → ℕ := _root_.catalan))

namespace Brockian.CatalanClosed
/-- Closed form for the Catalan numbers: (n+1)·Cₙ = C(2n, n). -/
theorem succ_mul_catalan_eq_choose (n : ℕ) :
    (n + 1) * Nat.catalan n = Nat.choose (2 * n) n := by
  have h : (n + 1) * Nat.catalan n = Nat.centralBinom n := by
    first
      | exact Nat.succ_mul_catalan_eq_centralBinom n
      | exact _root_.succ_mul_catalan_eq_centralBinom n
  simpa [Nat.centralBinom] using h
end Brockian.CatalanClosed

