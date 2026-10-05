/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA

/-- A principal of the isolation engine: either a root identity, or a principal
obtained by delegating from a parent principal under some capability name. -/
inductive Principal where
  | root : String → Principal
  | delegate : Principal → String → Principal
  deriving DecidableEq

namespace Principal

/-- `InChain q p` says that `q` occurs on the delegation chain of `p`, i.e. `q`
is `p` itself or one of its ancestors. -/
def InChain : Principal → Principal → Prop
  | q, root n => q = root n
  | q, delegate p n => q = delegate p n ∨ InChain q p

@[simp] theorem inChain_root (q : Principal) (n : String) :
    InChain q (root n) ↔ q = root n := Iff.rfl

@[simp] theorem inChain_delegate (q p : Principal) (n : String) :
    InChain q (delegate p n) ↔ (q = delegate p n ∨ InChain q p) := Iff.rfl

theorem inChain_self (p : Principal) : InChain p p := by
  cases p with
  | root n => rfl
  | delegate q n => exact Or.inl rfl

end Principal

namespace Invariant

open Principal

/-- An allowlist is a predicate on principals; the isolation engine's policy is
*default deny*, so anything not explicitly covered below is denied. -/
abbrev Allowlist := Principal → Prop

/-- The default-deny access decision: a principal is permitted only if it is
explicitly on the allowlist `A`, and (for a delegated principal) its parent is
permitted as well.  Every principal not covered by this rule is denied. -/
def Permits (A : Allowlist) : Principal → Prop
  | root n => A (root n)
  | delegate p n => A (delegate p n) ∧ Permits A p

@[simp] theorem permits_root (A : Allowlist) (n : String) :
    Permits A (root n) ↔ A (root n) := Iff.rfl

@[simp] theorem permits_delegate (A : Allowlist) (p : Principal) (n : String) :
    Permits A (delegate p n) ↔ (A (delegate p n) ∧ Permits A p) := Iff.rfl

/-- An allowlist is *delegation closed* when granting a delegated principal
requires its parent to be granted too. -/
def DelegationClosed (A : Allowlist) : Prop :=
  ∀ (p : Principal) (n : String), A (delegate p n) → A p

/-- Soundness of default deny: nothing off the allowlist is ever permitted. -/
theorem permits_mem_allowlist (A : Allowlist) : ∀ p : Principal, Permits A p → A p := by
  intro p hp
  cases p with
  | root n => exact hp
  | delegate q n => exact hp.1

/-- The permitted principals are exactly those whose whole delegation chain is
on the allowlist. -/
theorem permits_iff_chain_subset (A : Allowlist) (p : Principal) :
    Permits A p ↔ ∀ q : Principal, InChain q p → A q := by
  induction p with
  | root n =>
      constructor
      · intro hp q hq; exact hq ▸ hp
      · intro h; exact h _ rfl
  | delegate q n ih =>
      constructor
      · intro h r hr
        cases hr with
        | inl heq => exact heq ▸ h.1
        | inr hr => exact (ih.mp h.2) r hr
      · intro h
        exact ⟨h _ (Or.inl rfl), ih.mpr fun r hr => h r (Or.inr hr)⟩

/-- Completeness of default deny for a delegation-closed allowlist: every
allowlisted principal is indeed permitted. -/
theorem mem_allowlist_permits (A : Allowlist) (hA : DelegationClosed A) :
    ∀ p : Principal, A p → Permits A p := by
  intro p
  induction p with
  | root n => intro hp; exact hp
  | delegate q n ih => intro hp; exact ⟨hp, ih (hA q n hp)⟩

/-- **Default deny excludes only the allowlist.**  For a delegation-closed
allowlist `A`, the principals excluded (denied) by the default-deny engine are
exactly those that are not on the allowlist: no allowlisted principal is
excluded, and every non-allowlisted principal is. -/
theorem default_deny_excludes_only_allowlist
    (A : Allowlist) (hA : DelegationClosed A) (p : Principal) :
    ¬ Permits A p ↔ ¬ A p :=
  not_congr ⟨permits_mem_allowlist A p, mem_allowlist_permits A hA p⟩

/-- Set-style restatement: the denial predicate coincides with the complement of
the allowlist. -/
theorem denied_eq_compl_allowlist (A : Allowlist) (hA : DelegationClosed A) :
    (fun p => ¬ Permits A p) = fun p => ¬ A p := by
  funext p
  exact propext (default_deny_excludes_only_allowlist A hA p)

/-- Sanity check: the delegation-closure hypothesis is satisfiable by a
non-trivial allowlist, e.g. the one granting exactly the root principal `"app"`
and its direct delegation under the capability `"net"`. -/
example : DelegationClosed
    (fun p => p = Principal.root "app" ∨
      p = Principal.delegate (Principal.root "app") "net") := by
  intro p n h
  cases h with
  | inl h => exact Principal.noConfusion h
  | inr h =>
      injection h with h1 _
      exact Or.inl h1

end Invariant
end PCA

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

