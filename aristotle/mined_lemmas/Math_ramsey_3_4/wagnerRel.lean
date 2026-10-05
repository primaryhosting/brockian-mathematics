import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open SimpleGraph Finset

/-- `RamseyProp n k l` says that every simple graph on `n` vertices contains either a clique
of size `k` or an independent set (a clique of its complement) of size `l`. -/

def wagnerRel : Fin 8 → Fin 8 → Prop :=
  fun i j => (i.val + 1) % 8 = j.val ∨ (i.val + 4) % 8 = j.val

instance : DecidableRel wagnerRel := fun i j =>
  inferInstanceAs (Decidable ((i.val + 1) % 8 = j.val ∨ (i.val + 4) % 8 = j.val))

/-- The Wagner graph (Möbius–Kantor graph `V₈`), i.e. the circulant graph `C₈(1,4)`.
It is triangle-free and has independence number `3`, hence it witnesses `R(3,4) > 8`. -/
