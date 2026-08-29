/-
/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

namespace Frontier

open Filter Set

/-- A fixed nonprincipal ultrafilter on `ℕ`: an ultrafilter refining the cofinite filter. -/

lemma ramseyUF_le_cofinite : (ramseyUF : Filter ℕ) ≤ Filter.cofinite :=
  Ultrafilter.of_le _

