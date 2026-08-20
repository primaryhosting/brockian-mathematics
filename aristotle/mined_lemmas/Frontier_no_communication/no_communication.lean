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

/-!
# No-communication theorem (finite-dimensional Kraus form)

We model a bipartite quantum system with Alice's Hilbert space indexed by a finite
type `A` and Bob's by a finite type `B`, so that joint states are matrices indexed
by `A × B`.  A local operation performed by Alice is a quantum channel given by
Kraus operators `K i` acting on Alice's factor only, i.e. `K i ⊗ 1` on the joint
space, with `∑ i, (K i)ᴴ * (K i) = 1` (trace preservation).

The main result `Frontier.no_communication` says that Bob's reduced state
(the partial trace over Alice's subsystem) is completely unaffected by such an
operation, for *every* joint state `ρ` — in particular for entangled ones.
Consequently (`Frontier.no_communication_expectation`) the expectation value of
every observable measured by Bob alone is unchanged, so no information can be
transmitted.
-/

namespace Frontier

open scoped Matrix Kronecker

variable {A B ι : Type*} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq A] [DecidableEq B]

/-- The partial trace over Alice's subsystem: Bob's reduced density matrix. -/

theorem no_communication (K : ι → Matrix A A ℂ) (hK : ∑ i : ι, (K i)ᴴ * K i = 1)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    ptraceA (localChannelA K ρ) = ptraceA ρ := by
  ext b b'
  simp only [ptraceA, localChannelA, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, apply_ite (Star.star (R := ℂ)),
    star_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
  have key : ∀ a1 a2 : A,
      ∑ i : ι, ∑ x : A, Star.star (K i x a2) * K i x a1 = if a2 = a1 then 1 else 0 := by
    intro a1 a2
    have h := congrFun (congrFun hK a2) a1
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
      using h
  rw [sum_swap4 (fun (x : A) (i : ι) (a2 : A) (a1 : A) =>
    K i x a1 * ρ (a1, b) (a2, b') * Star.star (K i x a2))]
  have step : ∀ a2 a1 : A,
      ∑ i : ι, ∑ x : A, K i x a1 * ρ (a1, b) (a2, b') * Star.star (K i x a2)
        = (if a2 = a1 then 1 else 0) * ρ (a1, b) (a2, b') := by
    intro a2 a1
    rw [← key a1 a2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [step, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [DecidableEq B] in
/-- Bob's expectation values are computed from his reduced state. -/
