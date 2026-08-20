/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Mathlib currently contains no development of framed cobordism or of the
-- Kervaire invariant (a search of the library turns up no relevant declaration), so
-- nothing in the library closes this goal.  The file also carries no `import` line,
-- because the required header above is a module doc comment and Lean only allows
-- `import` commands before any other command; the proof below uses core Lean only.

set_option autoImplicit false

namespace Math2

/-- The dimensions in which a framed manifold of Kervaire invariant one exists,
described arithmetically: `n = 2 ^ (j + 2) - 2` for some `j ≤ 5`. -/

def IsKervaireDim (n : Nat) : Prop := ∃ j, j ≤ 5 ∧ n + 2 = 2 ^ (j + 2)

/-- Explicit description of the Kervaire dimensions: `2, 6, 14, 30, 62, 126`. -/
