/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps (Lean)
Target: PCA.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- A principal `c` can access resource `r` if `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/

def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- If a clean-isolation proof exists (every access is in scope), then no escape
can fire out of scope. -/
