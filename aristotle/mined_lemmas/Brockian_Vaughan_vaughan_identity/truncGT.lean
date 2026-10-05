/-
# Vaughan Identity
Category: B Brockian Frontier
Target: Brockian.Vaughan.vaughan_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Vaughan Identity
Category: B Brockian Frontier
Target: Brockian.Vaughan.vaughan_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

namespace Brockian
namespace Vaughan

open ArithmeticFunction

/-- The truncation of an arithmetic function to arguments `≤ U`. -/

def truncGT (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

