/-
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA.Isolation

/-- An isolation policy over a type of capabilities `Cap`.

A rule `(pre, c) ∈ rules` says: a sandboxed component that already holds every
capability in the precondition set `pre` can additionally obtain `c`. -/
structure Policy (Cap : Type*) where
  /-- The derivation rules of the policy. -/
  rules : Set (Set Cap × Cap)

variable {Cap : Type*}

/-- `Reach P G c` : starting from the initially granted capabilities `G`, the
isolation engine's model allows the component to obtain capability `c`. -/
inductive Reach (P : Policy Cap) (G : Set Cap) : Cap → Prop
  /-- Anything initially granted is reachable. -/
  | base {c : Cap} (hc : c ∈ G) : Reach P G c
  /-- A rule fires once all of its preconditions are reachable. -/
  | step {pre : Set Cap} {c : Cap} (hr : (pre, c) ∈ P.rules)
      (hpre : ∀ d ∈ pre, Reach P G d) : Reach P G c

/-- The set of capabilities reachable from the initial grant set `G`. -/
def reachable (P : Policy Cap) (G : Set Cap) : Set Cap := {c | Reach P G c}

/-- A set `S` of capabilities is *closed* under the policy `P`: whenever all
preconditions of a rule lie in `S`, so does its conclusion. -/
def Closed (P : Policy Cap) (S : Set Cap) : Prop :=
  ∀ pre : Set Cap, ∀ c : Cap, (pre, c) ∈ P.rules → (∀ d ∈ pre, d ∈ S) → c ∈ S

/-- A *privilege escape* occurs from the grant set `G` when some privileged
capability (an element of `priv`, i.e. one outside the sandbox's intended
authority) is reachable. -/
def PrivEscape (P : Policy Cap) (priv : Set Cap) (G : Set Cap) : Prop :=
  ∃ c ∈ priv, c ∈ reachable P G

/-! ### Soundness and completeness of `reachable` as a least fixpoint -/

/-- The initial grants are reachable. -/
theorem subset_reachable (P : Policy Cap) (G : Set Cap) : G ⊆ reachable P G :=
  fun _ hc => Reach.base hc

/-- Soundness: the reachable set is closed under the policy rules. -/
theorem closed_reachable (P : Policy Cap) (G : Set Cap) : Closed P (reachable P G) :=
  fun _ _ hr hpre => Reach.step hr hpre

/-- Completeness: the reachable set is contained in every closed superset of the
initial grants, i.e. `reachable P G` is the *least* such set. -/
theorem reachable_least (P : Policy Cap) (G S : Set Cap) (hGS : G ⊆ S)
    (hS : Closed P S) : reachable P G ⊆ S := by
  intro c hc
  induction hc with
  | base hd => exact hGS hd
  | step hr _ ih => exact hS _ _ hr ih

/-! ### Monotonicity -/

/-- Enlarging the initial grant set can only enlarge the reachable set. -/
theorem reachable_mono (P : Policy Cap) {G₁ G₂ : Set Cap} (h : G₁ ⊆ G₂) :
    reachable P G₁ ⊆ reachable P G₂ :=
  reachable_least P G₁ (reachable P G₂) (h.trans (subset_reachable P G₂))
    (closed_reachable P G₂)

/-- **Privilege escape is monotone in the initial grant set.**

If a sandbox configured with the capabilities `G₁` admits a privilege escape,
then so does any configuration granting at least those capabilities. -/
theorem priv_escape_monotone (P : Policy Cap) (priv : Set Cap) {G₁ G₂ : Set Cap}
    (hG : G₁ ⊆ G₂) (h : PrivEscape P priv G₁) : PrivEscape P priv G₂ := by
  obtain ⟨c, hcpriv, hcreach⟩ := h
  exact ⟨c, hcpriv, reachable_mono P hG hcreach⟩

/-- Privilege escape is also monotone in the set of privileged capabilities. -/
theorem priv_escape_mono_priv (P : Policy Cap) {priv₁ priv₂ : Set Cap} (G : Set Cap)
    (hp : priv₁ ⊆ priv₂) (h : PrivEscape P priv₁ G) : PrivEscape P priv₂ G := by
  obtain ⟨c, hcpriv, hcreach⟩ := h
  exact ⟨c, hp hcpriv, hcreach⟩

/-- Contrapositive form: an isolation proof (absence of escape) for a larger
grant set transfers to every smaller one. -/
theorem no_priv_escape_antitone (P : Policy Cap) (priv : Set Cap) {G₁ G₂ : Set Cap}
    (hG : G₁ ⊆ G₂) (h : ¬ PrivEscape P priv G₂) : ¬ PrivEscape P priv G₁ :=
  fun h₁ => h (priv_escape_monotone P priv hG h₁)

/-! ### A concrete instance: the model is not vacuous

A toy sandbox over three capabilities `0, 1, 2`, where `2` is privileged and the
single policy rule says that holding `0` lets a component derive `2`.
Granting nothing is safe; granting `0` produces a genuine privilege escape,
which `priv_escape_monotone` then propagates to every larger grant set. -/

/-- The toy policy: `{0} ⊢ 2`. -/
def toyPolicy : Policy (Fin 3) := ⟨{(({0} : Set (Fin 3)), (2 : Fin 3))}⟩

/-- Granting capability `0` really does let the sandbox escape. -/
theorem toy_escape_from_zero : PrivEscape toyPolicy {2} ({0} : Set (Fin 3)) :=
  ⟨2, rfl, Reach.step (by simp [toyPolicy]) fun _ hd => Reach.base hd⟩

/-- With no capabilities granted, the toy sandbox is safe: no escape occurs.
Hence `priv_escape_monotone` is not vacuously true. -/
theorem toy_no_escape_from_empty : ¬ PrivEscape toyPolicy {2} (∅ : Set (Fin 3)) := by
  rintro ⟨c, -, hcr⟩
  have hsub : reachable toyPolicy ∅ ⊆ (∅ : Set (Fin 3)) := by
    refine reachable_least _ _ _ Set.Subset.rfl ?_
    intro pre c hr hpre
    have hpre' : pre = ({0} : Set (Fin 3)) := by
      simp only [toyPolicy, Set.mem_singleton_iff, Prod.mk.injEq] at hr
      exact hr.1
    exact absurd (hpre 0 (by simp [hpre'])) (by simp)
  exact hsub hcr

/-- Monotonicity, instantiated: any configuration granting `0` escapes. -/
theorem toy_escape_of_grants_zero (G : Set (Fin 3)) (h : (0 : Fin 3) ∈ G) :
    PrivEscape toyPolicy {2} G :=
  priv_escape_monotone toyPolicy {2} (by simpa using h) toy_escape_from_zero

end PCA.Isolation

#print axioms PCA.Isolation.priv_escape_monotone
#print axioms PCA.Isolation.toy_no_escape_from_empty

