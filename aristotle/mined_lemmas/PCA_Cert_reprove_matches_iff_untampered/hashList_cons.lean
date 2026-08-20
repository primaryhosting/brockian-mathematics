import Mathlib
import RequestProject.Main

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

/-- Re-export check: the target theorem is available in the Mathlib environment. -/
example (check : PCA.Artifact → Bool) (a₀ a : PCA.Artifact) (cert : PCA.Cert)
    (hcert : cert = PCA.prove check a₀) :
    PCA.prove check a = cert ↔ PCA.Untampered a₀ a :=
  PCA.Cert.reprove_matches_iff_untampered check a₀ a cert hcert

/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to precede every other syntactic item,
-- so this module (whose first item must be the header doc-comment above) carries
-- no imports.  The development below needs none: it uses only core Lean.
-- The original Mathlib preamble is preserved verbatim in `RequestProject.Preamble`,
-- which imports this module.

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

/-! ## The isolation engine's model

An *artifact* is a finite byte string (the code and data an app ships).  A
*certificate* records the digest of the artifact it was issued for, together
with the verdict of the isolation checker on that artifact.

The prover is deterministic: `prove check a` is a pure function of the
artifact.  An artifact is *untampered* (with respect to the original `a₀`) when
it is byte-for-byte the artifact the certificate was issued for.

The statement `PCA.Cert.reprove_matches_iff_untampered` says that re-running the
prover on an artifact reproduces the stored certificate **exactly when** the
artifact is untampered.  The `←` direction is completeness (determinism of the
prover: an honest artifact always re-certifies); the `→` direction is soundness
(collision-freeness of the digest: no tampered artifact can reproduce the
certificate).  Collision-freeness is not assumed — it is proved below for the
concrete base-`257` digest of byte strings.
-/

/-- A shipped artifact: a finite string of bytes. -/
structure Artifact where
  bytes : List (Fin 256)
deriving DecidableEq

/-- The concrete digest of a byte string: a base-`257` positional encoding, with
each byte offset by one so that the empty string is the only string of digest
`0`. -/

@[simp] theorem hashList_cons (x : Fin 256) (xs : List (Fin 256)) :
    hashList (x :: xs) = 257 * hashList xs + (x.val + 1) := rfl

/-- Only the empty byte string has digest `0`. -/
