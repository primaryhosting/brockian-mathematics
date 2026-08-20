/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A *time-reversal operator* on a complex inner product space: an antiunitary map `T`
(additive, conjugate-homogeneous, and inner-product reversing) which squares to `-1`.
The condition `T (T a) = -a` is exactly what holds for half-integer spin
(for integer spin one has `T² = +1`). -/
structure IsTimeReversal (T : V → V) : Prop where
  /-- `T` is additive. -/
  map_add : ∀ a b, T (a + b) = T a + T b
  /-- `T` is conjugate-homogeneous. -/
  map_smul : ∀ (c : ℂ) (a : V), T (c • a) = (starRingEnd ℂ) c • T a
  /-- `T` is antiunitary: it conjugates inner products. -/
  inner_map : ∀ a b, ⟪T a, T b⟫_ℂ = ⟪b, a⟫_ℂ
  /-- Half-integer spin: `T² = -1`. -/
  sq_eq_neg : ∀ a, T (T a) = -a

/-- For a half-integer-spin time reversal, `T x` is orthogonal to `x`. -/

lemma IsTimeReversal.linearIndependent {T : V → V} (hT : IsTimeReversal T) {x : V} (hx : x ≠ 0) :
    LinearIndependent ℂ ![x, T x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hxT : ⟪x, T x⟫_ℂ = 0 := by
    simpa using congrArg (starRingEnd ℂ) (hT.inner_apply_self x)
  constructor
  · have := congrArg (fun v => ⟪x, v⟫_ℂ) hst
    simp [hxT] at this
    rcases this with h | h
    · exact h
    · exact absurd h hx
  · have := congrArg (fun v => ⟪T x, v⟫_ℂ) hst
    simp [hT.inner_apply_self x] at this
    rcases this with h | h
    · exact h
    · exact absurd h (hT.apply_ne_zero hx)

/-- **Kramers degeneracy.** Let `H` be the Hamiltonian (a symmetric, i.e. self-adjoint,
operator) of a finite-dimensional quantum system with half-integer spin, meaning that it
admits a time-reversal symmetry `T` with `T² = -1` commuting with `H`. Then every energy
level of `H` is (at least) doubly degenerate: its eigenspace has dimension at least `2`.

The proof: an eigenvector `x` with eigenvalue `μ` has `μ` real
(`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`), so `T x` lies in the same eigenspace,
and antiunitarity together with `T² = -1` forces `⟪T x, x⟫ = 0`, so `x` and `T x` are
linearly independent. -/
