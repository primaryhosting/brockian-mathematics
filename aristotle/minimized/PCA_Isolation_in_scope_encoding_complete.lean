/-
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA
namespace Isolation

/-- A resource the isolation engine may be asked to mediate access to:
a domain (the isolation boundary it lives behind) together with a path inside it. -/
structure Resource where
  domain : String
  path : List String
  deriving DecidableEq, Repr

/-- An isolation scope: a list of permitted domains together with a maximal path depth. -/
structure Scope where
  allowed : List String
  maxDepth : Nat
  deriving Repr

/-- A resource is *in scope* when its domain is permitted and its path is not too deep. -/

def InScope (sc : Scope) (r : Resource) : Prop :=
  r.domain ∈ sc.allowed ∧ r.path.length ≤ sc.maxDepth

instance (sc : Scope) (r : Resource) : Decidable (InScope sc r) := by
  unfold InScope; infer_instance

/-- The engine's wire encoding: an in-scope resource is encoded as the flat token list
`domain :: path`; an out-of-scope resource has no encoding at all. -/

def encode (sc : Scope) (r : Resource) : Option (List String) :=
  if InScope sc r then some (r.domain :: r.path) else none

/-- Decoding a token list back into a resource. The empty list is not a valid encoding. -/

def decode : List String → Option Resource
  | [] => none
  | d :: p => some ⟨d, p⟩

/-- Decoding inverts encoding on every value the encoder actually produces. -/

theorem in_scope_encoding_complete (sc : Scope) (r : Resource) :
    InScope sc r ↔ ∃ c, encode sc r = some c ∧ decode c = some r := by
  constructor
  · intro hs
    refine ⟨r.domain :: r.path, ?_, ?_⟩
    · simp [encode, if_pos hs]
    · cases r; rfl
  · rintro ⟨c, hc, -⟩
    by_contra hs
    rw [encode, if_neg hs] at hc
    exact absurd hc (by simp)

/-- Encoding is injective on in-scope resources: distinct in-scope resources never
collide on the wire. -/
