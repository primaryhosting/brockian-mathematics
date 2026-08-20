/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 requires every `import` command to precede all other
commands in a file, so no `import Mathlib` line may appear after the module
docstring above.  The development below is therefore self-contained in core
Lean 4; the sets of the model are represented as predicates `R → Prop`, which
is exactly Mathlib's `Set R` unfolded (`Set.ext` / `Set.mem_compl_iff`
correspond here to `funext`/`propext` and `PCA.Policy.decide_eq_deny_iff`).
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

universe u

/-- The outcome of consulting the isolation engine on a request. -/
inductive Decision
  | allow : Decision
  | deny : Decision
  deriving DecidableEq, Repr

/-- A collection of requests, i.e. a set of `R` represented as a predicate. -/

def Requests.univ (R : Type u) : Requests R := fun _ => True

/-- A *default-deny* policy for requests of type `R`: it carries an allowlist,
and everything not on that allowlist is denied. -/
structure Policy (R : Type u) where
  /-- The set of explicitly allowed requests. -/
  allowlist : Requests R

variable {R : Type u} (P : Policy R) (r : R)

open Classical in
/-- The decision procedure of a default-deny policy: allow exactly the requests
on the allowlist, deny everything else. -/
