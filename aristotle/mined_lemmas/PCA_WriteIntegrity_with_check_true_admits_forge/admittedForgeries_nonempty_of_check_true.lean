import Mathlib
import RequestProject.Main

/-!
# Mathlib-flavoured corollary of `with_check_true_admits_forge`

`RequestProject/Main.lean` must begin with a mandated module doc comment, which
forces that module to be import-free (Lean rejects `import` after a doc comment).
This companion module imports Mathlib and restates the main result in terms of
the *set* of admitted forgeries.
-/

set_option autoImplicit false

namespace PCA
namespace WriteIntegrity

/-- The set of requests that the engine admits even though they are forged. -/

theorem admittedForgeries_nonempty_of_check_true
    (E : Engine) (hE : ∀ r : Request, E.check r = true)
    (auth : Policy) (hgap : ∃ p k : Nat, ¬ auth p k) :
    (admittedForgeries E auth).Nonempty ∧ ¬ Sound E auth := by
  obtain ⟨⟨r, hr⟩, hns⟩ := with_check_true_admits_forge E hE auth hgap
  exact ⟨⟨r, hr⟩, hns⟩

end WriteIntegrity
end PCA

/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: this module is deliberately self-contained (Lean core only), because the
-- required header comment above must be the very first thing in the file and Lean
-- forbids `import` commands after a module doc comment.  Nothing below needs
-- Mathlib; the development uses only core `Nat` and logic.

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

namespace PCA
namespace WriteIntegrity

/-- A write request submitted to the isolation engine: a principal asks to store
`value` at storage location `key`. -/
structure Request where
  /-- The principal (subject) issuing the write. -/
  principal : Nat
  /-- The storage location being written. -/
  key : Nat
  /-- The value to be written. -/
  value : Nat
  deriving DecidableEq

/-- The reference (ground-truth) write policy: `auth p k` says that principal `p`
is authorized to write location `k`. -/
abbrev Policy := Nat → Nat → Prop

/-- An isolation engine is modelled by the boolean guard it runs on each request
before performing the write. -/
structure Engine where
  /-- The guard: the engine performs the write exactly when `check` returns `true`. -/
  check : Request → Bool

/-- The engine *admits* (actually performs) a request when its guard accepts it. -/
