/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Ordinal

/-! ## Elementary facts about base-`b` digits -/


noncomputable def hord (b : ℕ) (n : ℕ) : Ordinal.{0} :=
  hval b (fun a => (Ordinal.omega0.{0}) ^ a) (fun a k => a * (k : Ordinal.{0})) n

/-- The natural number obtained from the hereditary base-`b` representation of `n` by
replacing each occurrence of `b` by `b + 1`. -/
