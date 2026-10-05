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
