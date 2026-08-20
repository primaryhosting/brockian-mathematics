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

theorem erdos_discrepancy_one (f : ℕ → ℤ) (hf : IsPMOne f) :
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ (1 : ℤ) < |hapSum f n d| := by
  obtain ⟨n, d, hn, hd, _, h⟩ := erdos_discrepancy f hf
  exact ⟨n, d, hn, hd, by omega⟩

/-- An explicit `±1` sequence whose first `11` entries are `+ - - + - + + - - + +`.
It witnesses the sharpness of the bound `12` in `Frontier.erdos_discrepancy`. -/
