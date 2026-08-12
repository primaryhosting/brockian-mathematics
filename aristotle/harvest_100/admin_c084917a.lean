/-
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA

/-- An *artifact* is the piece of data that the isolation engine reasons about:
the code that is to be run inside the sandbox together with the policy that is
enforced on it.  Both are modelled as opaque byte strings. -/
structure Artifact where
  /-- The bytes of the isolated program. -/
  code : List Nat
  /-- The bytes of the isolation policy that the program was checked against. -/
  policy : List Nat
  deriving DecidableEq

/-- A *proof-carrying certificate*: it records the artifact that was actually
checked at build time, the digest that the engine computed for it, and the
verdict of the check. -/
structure Cert (D : Type*) where
  /-- The artifact that the certificate was issued for. -/
  source : Artifact
  /-- The digest of `source` recorded at issuing time. -/
  digest : D
  /-- The verdict recorded at issuing time. -/
  verdict : Bool

namespace Cert

variable {D : Type*}

/-- A certificate is *well-formed* for a digest function `dig` when its recorded
digest really is the digest of the artifact it was issued for.  This is what the
issuer guarantees. -/
def WellFormed (dig : Artifact → D) (c : Cert D) : Prop :=
  c.digest = dig c.source

/-- *Reproving* at load time: the engine recomputes the digest of the artifact
it is about to run and compares it against the digest stored in the certificate. -/
def Reprove (dig : Artifact → D) (a : Artifact) (c : Cert D) : Prop :=
  dig a = c.digest

/-- The artifact presented at load time is *untampered* exactly when it is the
very artifact the certificate was issued for. -/
def Untampered (a : Artifact) (c : Cert D) : Prop :=
  a = c.source

/-- **Soundness and completeness of certificate reproving.**

For a collision-free (injective) digest function `dig` and a well-formed
certificate `c`, recomputing the digest of the presented artifact `a` and
matching it against the stored digest succeeds *if and only if* `a` is exactly
the artifact the certificate was issued for.

The `←` direction is completeness (an untampered artifact always reproves) and
the `→` direction is soundness (a successful reprove rules out tampering).

The mathematical content is `Function.Injective.eq_iff` from Mathlib. -/
theorem reprove_matches_iff_untampered {D : Type*} {dig : Artifact → D}
    (hdig : Function.Injective dig) {a : Artifact} {c : Cert D}
    (hc : c.WellFormed dig) :
    c.Reprove dig a ↔ Untampered a c := by
  unfold Reprove Untampered
  rw [hc]
  exact hdig.eq_iff

/-- Decidable form: with a `DecidableEq` digest type, the boolean check that the
engine actually runs agrees with untamperedness. -/
theorem reprove_beq_iff_untampered {D : Type*} [DecidableEq D] {dig : Artifact → D}
    (hdig : Function.Injective dig) {a : Artifact} {c : Cert D}
    (hc : c.WellFormed dig) :
    (decide (dig a = c.digest) = true) ↔ a = c.source := by
  simpa using reprove_matches_iff_untampered hdig hc

end Cert

end PCA

