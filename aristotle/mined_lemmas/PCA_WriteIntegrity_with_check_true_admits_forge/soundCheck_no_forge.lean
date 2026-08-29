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

namespace PCA.WriteIntegrity

/-- Memory addresses. -/
abbrev Addr := Nat

/-- Memory values. -/
abbrev Val := Nat

/-- A memory image: a value at every address. -/
abbrev Mem := Addr → Val

/-- A write request issued by an application: an address, a value, and a
capability token that the application claims authorizes the write. -/
structure Write where
  addr : Addr
  val : Val
  cap : Nat
  deriving DecidableEq

/-- A write policy: the set (as a decidable predicate) of addresses the
application owns, together with the capability token required for a write. -/
structure Policy where
  owns : Addr → Bool
  token : Nat

/-- A write is *legitimate* for a policy when it targets an owned address and
carries the correct capability token. -/

theorem soundCheck_no_forge (p : Policy) : ¬ AdmitsForge p (soundCheck p) := by
  rintro ⟨m, w, hforge, hcheck, -⟩
  simp only [forged, Bool.not_eq_true'] at hforge
  rw [soundCheck, hforge] at hcheck
  exact Bool.noConfusion hcheck

/-- **Main result: the `true` check admits a forgery.**
If the reference monitor is replaced by the trivially-accepting check, then the
engine applies a write that violates the policy and thereby modifies memory —
write integrity fails. -/
