/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This file is deliberately self-contained: the header comment above must be the
-- very first thing in the file, and Lean requires `import` commands to precede
-- any module doc comment.  Everything used below (`Function.Injective`,
-- `Function.Injective.eq_iff`, `simp`, `deriving DecidableEq`) is available in
-- the ambient prelude, so no imports are needed.

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

universe u v

namespace PCA

/-! ## A model of the isolation engine's proof-carrying certificates

An *artifact* is the complete, self-contained description of what the isolation
engine ran: the code image, the configuration it was launched with, and the
input it was fed.  A *digest* is whatever opaque summary the engine's prover
emits; the only structural assumption we make about the digesting function is
that it is injective, i.e. the idealised collision-freeness assumption.

A *certificate* records the digest of the artifact it was produced from.
Re-proving an artifact `a'` against a certificate `c` means recomputing the
digest of `a'` and comparing it with the one stored in `c`.

The theorem `PCA.Cert.reprove_matches_iff_untampered` states soundness and
completeness of this check simultaneously: for a certificate sealed from an
artifact `a`, re-proving succeeds on `a'` exactly when `a'` is untampered,
i.e. `a' = a`.
-/

/-- A code image, configuration and input triple: everything the isolation
engine's run is determined by. -/
structure Artifact (Code Config Input : Type u) where
  code : Code
  config : Config
  input : Input
  deriving DecidableEq

/-- A proof-carrying certificate: the digest produced by the engine's prover. -/
structure Cert (Digest : Type v) where
  digest : Digest
  deriving DecidableEq

namespace Cert

variable {Code Config Input : Type u} {Digest : Type v}

/-- Sealing an artifact into a certificate: run the prover (`h`) on it. -/

theorem reprove_seal (h : Artifact Code Config Input → Digest)
    (a : Artifact Code Config Input) : Reprove h (certify h a) a := rfl

/-- Soundness, spelled out: if a tampered artifact re-proves, the prover has a
collision. -/
