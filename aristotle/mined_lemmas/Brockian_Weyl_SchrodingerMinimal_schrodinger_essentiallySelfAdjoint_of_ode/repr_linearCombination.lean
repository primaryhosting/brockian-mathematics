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

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate Real
open LinearPMap Submodule

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Essential self-adjointness -/

section Abstract

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A densely defined operator `A` is *essentially self-adjoint* when it is symmetric and its
adjoint is self-adjoint (equivalently, its closure is self-adjoint; equivalently, it has a
unique self-adjoint extension, see `unique_selfAdjoint_extension`). -/

theorem repr_linearCombination (f : ι → ℂ) (c : ι →₀ ℂ) (i : ι) :
    b.repr (Finsupp.linearCombination ℂ (fun j => f j • b j) c) i = f i * c i := by
  classical
  rw [b.repr_apply_apply, Finsupp.linearCombination_apply, Finsupp.sum, inner_sum]
  have h : ∀ j ∈ c.support, (inner ℂ (b i) (c j • (f j • b j)) : ℂ)
      = if i = j then f i * c i else 0 := by
    intro j _
    rw [inner_smul_right, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i j]
    by_cases hij : i = j
    · subst hij; simp; ring
    · simp [hij]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq c.support i (fun _ => f i * c i)]
  by_cases hi : i ∈ c.support
  · simp [hi]
  · have hci : c i = 0 := by simpa using hi
    simp [hi, hci]

omit [CompleteSpace E] in
