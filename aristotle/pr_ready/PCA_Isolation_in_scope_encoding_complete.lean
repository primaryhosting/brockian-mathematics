/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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
theorem decode_encode (sc : Scope) (r : Resource) (c : List String)
    (h : encode sc r = some c) : decode c = some r := by
  unfold encode at h
  by_cases hs : InScope sc r
  · rw [if_pos hs] at h
    -- `Option.some.inj` turns `some x = some y` into `x = y`.
    obtain rfl := Option.some.inj h
    cases r
    rfl
  · rw [if_neg hs] at h
    exact absurd h (by simp)

/-- The encoder is defined exactly on the in-scope resources: it succeeds if and only if
the resource is in scope, and in that case the encoding faithfully determines the resource.

This is the completeness (every in-scope resource is representable) and soundness
(nothing out of scope is representable) statement for the isolation engine's model. -/
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
theorem encode_injOn (sc : Scope) {r₁ r₂ : Resource} {c : List String}
    (h₁ : encode sc r₁ = some c) (h₂ : encode sc r₂ = some c) : r₁ = r₂ := by
  have d₁ := decode_encode sc r₁ c h₁
  have d₂ := decode_encode sc r₂ c h₂
  have : some r₁ = some r₂ := d₁ ▸ d₂ ▸ rfl
  exact Option.some.inj this

/-- Out-of-scope resources have no encoding. -/
theorem encode_eq_none_of_not_inScope (sc : Scope) (r : Resource) (h : ¬ InScope sc r) :
    encode sc r = none := by
  simp [encode, if_neg h]

end Isolation
end PCA

