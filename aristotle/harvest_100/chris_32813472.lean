/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps (Lean)
Target: PCA.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 forbids `import` commands after a module doc comment, and the
-- required header above must be the very first thing in the file, so this
-- module is stated with no imports.  The development below is self-contained
-- and uses no results from Mathlib.

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- Access predicate for a row-level security policy: a principal `c` can access
a row `r` if the row is in scope for `c`, or `c` is privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- A `WITH CHECK true` write policy admits any row (models forge-any):
with `canWrite := fun _ _ => True`, every principal may write every row. -/
theorem with_check_true_admits_forge :
    let canWrite : P → R → Prop := fun (_ : P) (_ : R) => True
    ∀ (c : P) (r : R), canWrite c r := by
  intro canWrite c r
  trivial

end PCA

end PCA

