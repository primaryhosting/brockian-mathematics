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

theorem Policy.decide_allow_or_deny :
    P.decide r = Decision.allow ∨ P.decide r = Decision.deny := by
  unfold Policy.decide
  by_cases h : P.allowlist r
  · simp [h]
  · simp [h]

namespace Invariant

/-- **Default deny excludes only the allowlist.**

For a default-deny isolation policy, the collection of denied requests is
exactly the complement of the allowlist: nothing on the allowlist is denied
(soundness) and everything off the allowlist is denied (completeness). -/
