/-!
# Priv Is Escape
Category: Proof-Carrying Apps (Lean)
Target: PCA.priv_is_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: the required header comment above is a module docstring, so no `import`
-- command may follow it (Lean requires imports to come first in a file).
-- The development below therefore uses only the Lean 4 core prelude; it is
-- imported by `RequestProject.Main`, which does `import Mathlib`, so the
-- results are available in the full Mathlib environment.

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- A caller `c` may access resource `r` when `r` is in `c`'s scope, or `c` is
privileged (the admin bypass), or `r` is unowned. -/

def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- A privileged caller always has access: privilege is an escape hatch.
The proof is disjunction introduction, `Or.inr`/`Or.inl`. -/
