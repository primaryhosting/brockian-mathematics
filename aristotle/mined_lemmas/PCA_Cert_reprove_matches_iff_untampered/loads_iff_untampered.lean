/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Cert

/-- An *artifact* handled by the isolation engine: the app's code together with the
isolation policy it is supposed to run under. -/
structure Artifact where
  /-- The app's code, as a sequence of opcodes. -/
  code : List Nat
  /-- The isolation policy the app was certified against. -/
  policy : List Nat
  deriving DecidableEq, Repr

/-- A *certificate*, as shipped alongside a proof-carrying app: it binds the artifact
that was checked at issuance time to a digest value of type `D`. -/
structure Certificate (D : Type u) where
  /-- The digest of the artifact recorded when the certificate was issued. -/
  digest : D
  deriving Repr

/-- Issuing a certificate for an artifact: record its digest. -/

theorem loads_iff_untampered {D : Type u} [DecidableEq D] (dg : Artifact → D)
    (hdg : Function.Injective dg) (orig a : Artifact) :
    loads dg (issue dg orig) a ↔ Untampered orig a :=
  reprove_matches_iff_untampered dg hdg orig a

end PCA.Cert

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

