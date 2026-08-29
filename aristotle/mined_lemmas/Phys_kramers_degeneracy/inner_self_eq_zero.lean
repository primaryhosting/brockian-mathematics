import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
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


namespace Phys

/-- An **antiunitary time-reversal operator** on a complex inner product space `V`:
an additive, conjugate-linear map preserving the inner product up to conjugation. -/
structure TimeReversal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- The underlying map. -/
  toFun : V → V
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (c : ℂ) (x : V), toFun (c • x) = (starRingEnd ℂ) c • toFun x
  inner_map' : ∀ x y, inner ℂ (toFun x) (toFun y) = inner ℂ y x

namespace TimeReversal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

instance : CoeFun (TimeReversal V) (fun _ => V → V) := ⟨TimeReversal.toFun⟩

/-- For a half-integer-spin time reversal (`Θ² = -1`), every vector is orthogonal to its
time-reverse. -/

theorem inner_self_eq_zero (Θ : TimeReversal V) (hsq : ∀ x, Θ (Θ x) = -x) (x : V) :
    inner ℂ (Θ x) x = 0 := by
  have h := Θ.inner_map' x (Θ x)
  rw [hsq x] at h
  rw [inner_neg_right] at h
  have : (2 : ℂ) * inner ℂ (Θ x) x = 0 := by linear_combination -h
  simpa using this

end TimeReversal

/-- **Kramers degeneracy.**  Let `H` be a Hamiltonian on a complex inner product space `V`
which is invariant under an antiunitary time-reversal operator `Θ` satisfying `Θ² = -1`
(the half-integer-spin case).  Then every energy level `E` of `H` is (at least) doubly
degenerate: the eigenspace of `H` for `E` has rank at least `2`, spanned in part by the
orthogonal pair `ψ`, `Θψ`. -/
