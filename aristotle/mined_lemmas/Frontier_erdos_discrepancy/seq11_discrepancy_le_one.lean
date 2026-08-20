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

theorem seq11_discrepancy_le_one (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hnd : n * d ≤ 11) :
    |hapSum seq11 n d| ≤ 1 := by
  have key : ∀ n ∈ Finset.Icc 1 11, ∀ d ∈ Finset.Icc 1 11, n * d ≤ 11 →
      |hapSum seq11 n d| ≤ 1 := by decide
  have hn' : n ≤ 11 := le_trans (Nat.le_mul_of_pos_right n hd) hnd
  have hd' : d ≤ 11 := le_trans (Nat.le_mul_of_pos_left d hn) hnd
  exact key n (Finset.mem_Icc.mpr ⟨hn, hn'⟩) d (Finset.mem_Icc.mpr ⟨hd, hd'⟩) hnd

/-- A Lean-checked reduction: to prove the full Erdős discrepancy statement it suffices to
prove it for natural-number bounds `C`, since the discrepancy bound is monotone in `C`. -/
