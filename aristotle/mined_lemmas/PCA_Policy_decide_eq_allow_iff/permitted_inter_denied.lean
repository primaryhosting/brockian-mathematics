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

theorem permitted_inter_denied {R : Type u} (P : Policy R) :
    P.permitted.inter P.denied = Requests.empty R := by
  funext x
  refine propext ⟨fun h => ?_, fun h => h.elim⟩
  have h1 : P.decide x = Decision.allow := h.1
  have h2 : P.decide x = Decision.deny := h.2
  rw [h1] at h2
  exact Decision.noConfusion h2

/-- With an empty allowlist, everything is denied: the engine is closed by default. -/
