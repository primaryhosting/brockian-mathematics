/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a module docstring: Lean 4 requires `import` lines to come
first, so the very first comment of the file cannot be a module docstring.)

This file develops space bounded machines, proves Savitch's theorem
`NSPACE f ⊆ DSPACE (f ^ 2)` and deduces `PSPACE = NPSPACE`.
-/

set_option autoImplicit false

namespace CS

/-! ## Languages -/

/-- A language is a predicate on binary strings. -/
abbrev Language := List Bool → Prop

/-- The bit of `x` at position `i` (`false` beyond the end of `x`). -/

theorem sstep_some_false_false (hk : F.k ≠ 0) (hm : ¬ N < F.m) (hph : F.ph = false)
    (hc : c = false) :
    sstep N edge b (some c, F :: rest) = (none, ⟨F.u, F.v, F.k, F.m + 1, false⟩ :: rest) := by
  simp [sstep, hk, hm, hph, hc]

end StepEqs

/-- The graph explored by the simulator, once the input bits are fixed. -/
