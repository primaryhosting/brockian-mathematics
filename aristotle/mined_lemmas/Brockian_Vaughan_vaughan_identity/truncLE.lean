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

def truncLE (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- The truncation of an arithmetic function to arguments `> U`. -/
