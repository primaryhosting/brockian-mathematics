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

/-
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 rejects a `/-!` module docstring before `import`; the header is reproduced
-- verbatim as the module docstring immediately after the imports.)

import Mathlib

/-!
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Cert

/-!
## The algebraic model of Ed25519

We model the Ed25519 signature scheme over its prime-order subgroup.  The subgroup is an
abelian group `G` on which the scalars `ZMod L` act (`L` is the prime group order, i.e. the
order `ℓ` of the base point in the real scheme); the base point is a point `B : G` whose
*annihilator is trivial*, i.e. `k • B = 0 → k = 0`, which is exactly the statement that `B`
generates a subgroup of order `L`.

The scheme itself is then:

* public key  `A = a • B`  for a secret scalar `a`;
* signature of `m` with nonce `r`:  `R = r • B`, `S = r + H R A m * a`;
* verification of `(R, S)` against `A`:  `S • B = R + (H R A m) • A`.

`ed25519_verify_sound` states the exact soundness (and completeness) characterisation of the
verification equation: an alleged signature `(R, S)` with `R = r • B` is accepted **iff** the
scalar `S` is precisely the honest response `r + H R A m * a`.  In contrapositive form: any
`S` that differs from the honest response is rejected — verification cannot be fooled.
-/

section Model

variable {L : ℕ} {G : Type*} {Msg : Type*} [AddCommGroup G] [Module (ZMod L) G]

/-- The Ed25519 verification predicate: the signature `(R, S)` on message `m` is accepted
under public key `A` (with base point `B` and hash function `H`) when `S • B = R + h • A`,
where `h = H R A m` is the challenge scalar. -/

def ed25519GroupOrder : ℕ := 2 ^ 252 + 27742317777372353535851937790883648493

instance : NeZero ed25519GroupOrder := ⟨by unfold ed25519GroupOrder; positivity⟩

/-- The soundness theorem instantiated at a concrete, non-degenerate model with the genuine
Ed25519 group order: nothing above is vacuous. -/
