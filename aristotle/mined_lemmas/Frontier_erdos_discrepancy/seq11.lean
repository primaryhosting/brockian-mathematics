/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header above
-- is written as a plain comment and repeated as a module docstring after the import.)

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A sequence `f : ℕ → ℤ` is a `±1` sequence if `f n ∈ {1, -1}` for every `n ≥ 1`
(the value `f 0` is irrelevant, since homogeneous arithmetic progressions only use
indices `i * d` with `i, d ≥ 1`). -/

def seq11 : ℕ → ℤ := fun n => ([0, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1] : List ℤ).getD n 1

