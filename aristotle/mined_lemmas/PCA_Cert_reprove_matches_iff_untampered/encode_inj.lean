/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

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

/-- An *artifact* handed to the isolation engine: a piece of code (a list of opcodes,
encoded as natural numbers) together with the policy (the list of opcodes the code is
permitted to use). -/
structure Artifact where
  /-- The opcodes making up the application code. -/
  code : List Nat
  /-- The whitelist of opcodes permitted by the isolation policy. -/
  policy : List Nat
  deriving DecidableEq

namespace Artifact

/-- A prefix-free serialisation of an artifact: the length of the code section, followed
by the code section, followed by the policy section.  Recording the length of the first
section makes the concatenation unambiguous, hence the encoding injective. -/

@[simp] theorem encode_inj {a b : Artifact} : encode a = encode b ↔ a = b :=
  encode_injective.eq_iff

/-- The isolation check performed by the engine: every opcode used by the code is
permitted by the policy. -/
