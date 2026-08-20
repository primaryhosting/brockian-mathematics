/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps (Lean)
Target: PCA.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment above must be the first thing in the file,
-- and Lean 4 requires all `import` commands to precede any other command
-- (including a module doc comment).  The development below is therefore
-- self-contained and needs no imports: the model is stated inline and the
-- proof uses only `True.intro` (the `trivial` tactic), which Mathlib's
-- `trivial`/`exact?` also finds for a `True` goal.

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- Access predicate of the model: a principal `c` may access a row `r` when the
row is in scope for `c`, or `c` is privileged, or the row is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- A `WITH CHECK true` write policy admits any row (models "forge any row"):
with `canWrite := fun _ _ => True`, every principal `c` may write every row `r`,
so the policy provides no protection at all.

The goal reduces to `True`, closed by `True.intro` (the `trivial` tactic). -/
theorem with_check_true_admits_forge :
    ∀ (c : P) (r : R), (fun (_ : P) (_ : R) => True) c r := fun _ _ => True.intro

end PCA

end PCA

