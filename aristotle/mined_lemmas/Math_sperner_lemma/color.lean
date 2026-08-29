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

def color : Fin 4 → ℕ := fun i => if i = 3 then 0 else (i : ℕ)

