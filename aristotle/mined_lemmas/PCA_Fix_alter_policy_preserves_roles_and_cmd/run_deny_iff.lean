import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# A formal model of a policy-controlled isolation engine (`PCA`)

This file develops a small but complete formal model of an *isolation engine*:
a component that decides whether a command may be executed on behalf of a set of
roles under a capability policy, and, if so, produces the sandbox in which the
command is to be run.

The main results are

* `PCA.run_allow_iff` : soundness **and** completeness of the engine with respect
  to the declarative specification `PCA.Permits`;
* `PCA.run_sound`, `PCA.run_complete`, `PCA.run_deny_iff` : the two directions and
  the corresponding characterisation of denials;
* `PCA.allow_least_privilege` : the produced sandbox carries exactly the
  capabilities the command needs, and every one of them is actually granted;
* `PCA.run_congr` : the verdict only depends on the grants for the roles of the
  request and the capabilities needed by the command (an isolation / non-interference
  property);
* `PCA.Fix.alter_policy_preserves_roles_and_cmd` and the surrounding lemmas: the
  policy-repair operation changes nothing but the policy, only ever adds grants,
  adds only grants that are needed, and does repair the request.
-/

namespace PCA

/-- Capabilities that a command may require and a policy may grant. -/
inductive Cap where
  | read | write | net | exec
  deriving DecidableEq, Repr

/-- Principals are identified by a numeric role identifier. -/
abbrev Role := ℕ

/-- A policy records, for every role and capability, whether the capability is granted. -/
structure Policy where
  grants : Role → Cap → Bool

/-- A policy `p` is weaker than `q` if every grant of `p` is also a grant of `q`. -/

theorem run_deny_iff (r : Request) : (∃ c, run r = .deny c) ↔ ¬ Permits r := by
  constructor
  · rintro ⟨c, hc⟩ hp
    rw [run_complete hp] at hc
    exact absurd hc (by simp)
  · intro hp
    unfold run
    cases hf : r.cmd.needs.find? (fun c => !r.granted c) with
    | some c => exact ⟨c, rfl⟩
    | none =>
        exact absurd (fun c hc => by simpa using List.find?_eq_none.mp hf c hc) hp

/-- A denial always names a capability that the command genuinely needs and that the
caller genuinely lacks. -/
