import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` lines to come first in a module, so the
required header block is placed immediately after the single `import Mathlib` line.
-/

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-! ### Codimension-one subsets -/

/-- Subsets of `S` of cardinality `S.card - 1` are exactly the sets `S.erase x` for `x ∈ S`;
hence counting them amounts to counting the vertices `x ∈ S` with the corresponding property. -/

theorem rainbow_cells_odd :
    Odd ((T 2).filter (fun S => S.image color = Finset.range 3)).card := by
  refine Math.sperner_lemma 2 color T ?_ ?_ ?_ ?_
  · intro k hk
    interval_cases k <;> decide
  · intro k hk
    interval_cases k <;> decide
  · exact ⟨0, by decide, by decide⟩
  · intro k hk
    have hk' : k ≤ 1 := by omega
    interval_cases k <;> (intro G; revert G; decide)

/-- There is exactly one rainbow `2`-cell in this triangulation. -/
