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
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace PCA
namespace Isolation

/-- A set of capabilities, represented by its membership predicate. -/
abbrev CapSet (Cap : Type u) : Type u := Cap → Prop

/-- `g₁ ≼ g₂` : every capability granted by `g₁` is also granted by `g₂`. -/
def CapSubset {Cap : Type u} (g₁ g₂ : CapSet Cap) : Prop := ∀ c, g₁ c → g₂ c

@[inherit_doc] scoped infix:50 " ≼ " => CapSubset

/-- A *derivation rule* of the isolation engine: holding all capabilities in the
premise set `r.1` lets an application obtain the capability `r.2`. -/
abbrev Rule (Cap : Type u) : Type u := CapSet Cap × Cap

/-- `Reach rules g c` says that an application initially granted the capabilities
`g` can, using the engine's derivation `rules`, come to hold the capability `c`. -/
inductive Reach {Cap : Type u} (rules : Rule Cap → Prop) (g : CapSet Cap) : Cap → Prop
  /-- Every granted capability is held. -/
  | base {c : Cap} (hc : g c) : Reach rules g c
  /-- A rule fires once all of its premises are held. -/
  | step {pre : CapSet Cap} {c : Cap} (hr : rules (pre, c))
      (hpre : ∀ x, pre x → Reach rules g x) : Reach rules g c

/-- The set of capabilities an application with grants `g` can end up holding. -/
def closure {Cap : Type u} (rules : Rule Cap → Prop) (g : CapSet Cap) : CapSet Cap :=
  fun c => Reach rules g c

/-- A *privilege escape*: the privileged capability `p` is obtainable from the
grants `g` under the engine's rules. -/
def Escapes {Cap : Type u} (rules : Rule Cap → Prop) (g : CapSet Cap) (p : Cap) : Prop :=
  Reach rules g p

/-- Reachability is monotone in the initial grants. -/
theorem reach_mono {Cap : Type u} {rules : Rule Cap → Prop} {g₁ g₂ : CapSet Cap}
    (hg : g₁ ≼ g₂) {c : Cap} (h : Reach rules g₁ c) : Reach rules g₂ c := by
  induction h with
  | base hc => exact Reach.base (hg _ hc)
  | step hr _ ih => exact Reach.step hr ih

/-- **Privilege escape is monotone in the granted capabilities.**  Enlarging the
set of capabilities handed to an application can only enlarge the set of
privileges it can escape to: isolation is never gained by granting more. -/
theorem priv_escape_monotone {Cap : Type u} {rules : Rule Cap → Prop} {g₁ g₂ : CapSet Cap}
    (hg : g₁ ≼ g₂) {p : Cap} (h : Escapes rules g₁ p) : Escapes rules g₂ p :=
  reach_mono hg h

/-- Contrapositive form: an application that cannot escape to `p` with the larger
grant set cannot escape to `p` with the smaller one either. -/
theorem not_escapes_of_subset {Cap : Type u} {rules : Rule Cap → Prop} {g₁ g₂ : CapSet Cap}
    (hg : g₁ ≼ g₂) {p : Cap} (h : ¬ Escapes rules g₂ p) : ¬ Escapes rules g₁ p :=
  fun h₁ => h (priv_escape_monotone hg h₁)

/-- The reachable-capability closure operator is monotone. -/
theorem closure_mono {Cap : Type u} {rules : Rule Cap → Prop} {g₁ g₂ : CapSet Cap}
    (hg : g₁ ≼ g₂) : closure rules g₁ ≼ closure rules g₂ :=
  fun _ hc => reach_mono hg hc

/-- Grants are always held: the closure operator is extensive. -/
theorem subset_closure {Cap : Type u} (rules : Rule Cap → Prop) (g : CapSet Cap) :
    g ≼ closure rules g :=
  fun _ hc => Reach.base hc

/-- Reachability is also monotone in the rule set: adding derivation rules can
only add escapes. -/
theorem reach_mono_rules {Cap : Type u} {rules₁ rules₂ : Rule Cap → Prop}
    (hr : ∀ r, rules₁ r → rules₂ r) {g : CapSet Cap} {c : Cap} (h : Reach rules₁ g c) :
    Reach rules₂ g c := by
  induction h with
  | base hc => exact Reach.base hc
  | step hrule _ ih => exact Reach.step (hr _ hrule) ih

/-- Soundness/completeness of the closure as the least fixed point: `closure rules g`
is contained in every grant set that contains `g` and is closed under the rules. -/
theorem closure_least {Cap : Type u} {rules : Rule Cap → Prop} {g s : CapSet Cap}
    (hgs : g ≼ s) (hclosed : ∀ pre c, rules (pre, c) → (∀ x, pre x → s x) → s c) :
    closure rules g ≼ s := by
  intro c hc
  induction hc with
  | base h => exact hgs _ h
  | step hr _ ih => exact hclosed _ _ hr ih

end Isolation
end PCA

import Mathlib
import RequestProject.PCA.Isolation

/-!
# Priv Escape Monotone — Mathlib (`Set` / `Monotone`) interface

Companion to `RequestProject/PCA/Isolation.lean`, which contains the target
theorem `PCA.Isolation.priv_escape_monotone`.  That file must begin with a fixed
header comment, which Lean requires to precede any `import`, so it is written
against Lean core only.  Here we repackage the same isolation model in Mathlib's
`Set` language and phrase monotonicity with `Monotone`, deriving everything from
the core results.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace PCA
namespace Isolation

open scoped PCA.Isolation

variable {Cap : Type u}

/-- A derivation rule of the isolation engine, in `Set` language. -/
abbrev SetRule (Cap : Type u) : Type u := Set Cap × Cap

/-- Reachability of a capability from a `Set`-valued grant set. -/
def SetReach (rules : Set (SetRule Cap)) (g : Set Cap) (c : Cap) : Prop :=
  Reach (fun r => r ∈ rules) (fun x => x ∈ g) c

/-- The set of capabilities an application with grants `g` can end up holding. -/
def setClosure (rules : Set (SetRule Cap)) (g : Set Cap) : Set Cap :=
  {c | SetReach rules g c}

/-- Privilege escape to `p`, in `Set` language. -/
def SetEscapes (rules : Set (SetRule Cap)) (g : Set Cap) (p : Cap) : Prop :=
  SetReach rules g p

theorem setReach_base {rules : Set (SetRule Cap)} {g : Set Cap} {c : Cap} (hc : c ∈ g) :
    SetReach rules g c :=
  Reach.base hc

theorem setReach_step {rules : Set (SetRule Cap)} {g : Set Cap} {pre : Set Cap} {c : Cap}
    (hr : (pre, c) ∈ rules) (hpre : ∀ x ∈ pre, SetReach rules g x) :
    SetReach rules g c :=
  Reach.step hr hpre

/-- **Privilege escape is monotone in the granted capabilities** (`Set` form). -/
theorem setEscapes_of_subset {rules : Set (SetRule Cap)} {g₁ g₂ : Set Cap} {p : Cap}
    (hg : g₁ ⊆ g₂) (h : SetEscapes rules g₁ p) : SetEscapes rules g₂ p :=
  priv_escape_monotone (fun _ hc => hg hc) h

/-- **Privilege escape is monotone in the granted capabilities**, stated with
Mathlib's `Monotone` (using the `→` order on `Prop`). -/
theorem setEscapes_monotone (rules : Set (SetRule Cap)) (p : Cap) :
    Monotone (fun g : Set Cap => SetEscapes rules g p) :=
  fun _ _ hg h => setEscapes_of_subset hg h

/-- The reachable-capability closure operator is monotone. -/
theorem setClosure_monotone (rules : Set (SetRule Cap)) :
    Monotone (setClosure rules) :=
  fun _ _ hg _ hc => setEscapes_of_subset hg hc

/-- The closure operator is extensive. -/
theorem subset_setClosure (rules : Set (SetRule Cap)) (g : Set Cap) :
    g ⊆ setClosure rules g :=
  fun _ hc => setReach_base hc

/-- A grant set is closed under the engine's rules. -/
def RuleClosed (rules : Set (SetRule Cap)) (s : Set Cap) : Prop :=
  ∀ pre c, (pre, c) ∈ rules → pre ⊆ s → c ∈ s

theorem ruleClosed_setClosure (rules : Set (SetRule Cap)) (g : Set Cap) :
    RuleClosed rules (setClosure rules g) :=
  fun _ _ hr hpre => setReach_step hr fun _ hx => hpre hx

/-- Least-fixed-point property: the closure is contained in every rule-closed
superset of the grants. -/
theorem setClosure_least {rules : Set (SetRule Cap)} {g s : Set Cap}
    (hgs : g ⊆ s) (hs : RuleClosed rules s) : setClosure rules g ⊆ s :=
  closure_least (fun _ hc => hgs hc) (fun _ _ hr hpre => hs _ _ hr hpre)

/-- The reachable set is exactly the least rule-closed superset of the grants. -/
theorem setClosure_eq_sInf (rules : Set (SetRule Cap)) (g : Set Cap) :
    setClosure rules g = sInf {s : Set Cap | g ⊆ s ∧ RuleClosed rules s} := by
  apply le_antisymm
  · intro c hc s hs
    exact setClosure_least hs.1 hs.2 hc
  · intro c hc
    exact hc (setClosure rules g) ⟨subset_setClosure rules g, ruleClosed_setClosure rules g⟩

/-- Escapes are also monotone in the rule set: adding derivation rules can only
add escapes. -/
theorem setEscapes_of_rules_subset {rules₁ rules₂ : Set (SetRule Cap)} {g : Set Cap} {p : Cap}
    (hr : rules₁ ⊆ rules₂) (h : SetEscapes rules₁ g p) : SetEscapes rules₂ g p :=
  reach_mono_rules (fun _ hx => hr hx) h

/-- Contrapositive safety form: if the larger grant set cannot escape to `p`,
neither can the smaller one. -/
theorem not_setEscapes_of_subset {rules : Set (SetRule Cap)} {g₁ g₂ : Set Cap} {p : Cap}
    (hg : g₁ ⊆ g₂) (h : ¬ SetEscapes rules g₂ p) : ¬ SetEscapes rules g₁ p :=
  fun h₁ => h (setEscapes_of_subset hg h₁)

end Isolation
end PCA

