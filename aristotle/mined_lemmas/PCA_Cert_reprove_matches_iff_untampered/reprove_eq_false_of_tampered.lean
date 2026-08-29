/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Cert

/-- An *artifact* shipped by a proof-carrying app: a code segment together with a data
segment, both modelled as lists of machine words. -/
structure Artifact where
  code : List Nat
  data : List Nat
  deriving DecidableEq, Repr

/-- A *certificate* accompanying an artifact: the digest computed by the isolation engine's
prover at seal time. -/
structure Certificate where
  digest : List Nat
  deriving DecidableEq, Repr

/-- The (collision-free) digest of an artifact: the length of the code segment, followed by
the concatenation of the code and data segments.  The length prefix makes the encoding
uniquely decodable, so the digest determines the artifact. -/

theorem reprove_eq_false_of_tampered {orig recv : Artifact} (h : recv ≠ orig) :
    reprove recv (certify orig) = false := by
  have : ¬ (reprove recv (certify orig) = true) := by
    rw [reprove_matches_iff_untampered]
    exact h
  simpa using this

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

