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
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace WriteIntegrity

/-- A write request submitted to the isolation engine: it targets a memory
`region`, carries a `payload`, and presents a capability `token` that is meant
to justify the access. -/
structure Write where
  region : Nat
  payload : Nat
  token : Nat
  deriving DecidableEq, Repr

/-- A write policy: `pol r t = true` means capability token `t` authorizes
writes to region `r`. -/
abbrev Policy := Nat → Nat → Bool

/-- A checker is the (decidable) admission test the engine actually runs on a
write request. -/
abbrev Checker := Write → Bool

/-- A write is *genuine* under `pol` when the token it presents really does
authorize the region it targets. -/

theorem denyAll_forge_exists : ∃ w, Forged (fun _ _ => false) w :=
  ⟨⟨0, 0, 0⟩, by simp [Forged, Genuine]⟩

