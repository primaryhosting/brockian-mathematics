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

theorem denied_of_empty_allowlist {R : Type u} (P : Policy R)
    (h : P.allowlist = Requests.empty R) :
    P.denied = Requests.univ R := by
  rw [default_deny_excludes_only_allowlist, h]
  funext x
  exact propext ⟨fun _ => trivial, fun _ hx => hx.elim⟩

end Invariant

end PCA

#print axioms PCA.Invariant.default_deny_excludes_only_allowlist

