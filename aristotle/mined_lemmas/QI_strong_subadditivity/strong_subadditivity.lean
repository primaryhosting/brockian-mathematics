import RequestProject.SSA.PartialTrace

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to follow the `import` line: Lean requires `import` commands to
come first in a file.)

The von Neumann entropy `S(A) = -Tr (A log A)` of a positive definite matrix on a threefold
tensor product `α ⊗ β ⊗ γ` satisfies the Lieb–Ruskai inequality

`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

The proof goes through Lindblad's joint convexity of the Umegaki relative entropy
(itself deduced from Ando's joint concavity of the operator geometric mean) and the
resulting monotonicity of the relative entropy under partial traces.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-! ### Relative entropy against `1 ⊗ Y` -/


theorem strong_subadditivity [Nonempty α] [Nonempty γ]
    {ρ : Matrix (α × β × γ) (α × β × γ) ℂ} (hρ : ρ.PosDef) :
    vnEnt ρ + vnEnt (ptR (ptA ρ)) ≤ vnEnt (ptC ρ) + vnEnt (ptA ρ) := by
  classical
  set e := assocEquiv α β γ with he
  set rBC : Matrix (β × γ) (β × γ) ℂ := ptA ρ with hrBC
  set rAB : Matrix (α × β) (α × β) ℂ := ptC ρ with hrAB
  set rB : Matrix β β ℂ := ptR rBC with hrB
  have hBC : rBC.PosDef := ptA_posDef hρ
  have hAB : rAB.PosDef := ptC_posDef hρ
  have hB : rB.PosDef := ptR_posDef hBC
  have hK : ((1 : Matrix α α ℂ) ⊗ₖ rBC).PosDef := Matrix.PosDef.one.kronecker hBC
  -- the partial trace of the reference state
  have hptK : ptR ((((1 : Matrix α α ℂ) ⊗ₖ rBC)).submatrix e.symm e.symm)
      = (1 : Matrix α α ℂ) ⊗ₖ rB := ptR_submatrix_kronL rBC
  have hptrho : ptR (ρ.submatrix e.symm e.symm) = rAB := rfl
  -- monotonicity of the relative entropy under tracing out the third factor
  have hmono := relEnt_ptR_le (PosDef.submatrix_equiv hρ e)
    (PosDef.submatrix_equiv hK e)
  rw [hptK, hptrho, relEnt_submatrix_equiv hρ hK e] at hmono
  -- identify both sides
  have hL : relEnt rAB ((1 : Matrix α α ℂ) ⊗ₖ rB) = -vnEnt rAB + vnEnt rB := by
    have hEq : ptL rAB = rB := by rw [hrAB, hrB, hrBC, ptL_ptC]
    rw [← hEq] at hB ⊢
    exact relEnt_kronL_self hB
  have hR : relEnt ρ ((1 : Matrix α α ℂ) ⊗ₖ rBC) = -vnEnt ρ + vnEnt rBC := by
    have hEq : ptL ρ = rBC := rfl
    rw [← hEq] at hBC ⊢
    exact relEnt_kronL_self hBC
  rw [hL, hR] at hmono
  linarith

end QI

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

import RequestProject.SSA.GeometricMean

/-!
# Iterated geometric means

`gpow m A B` is the `2⁻ᵐ`-weighted geometric mean of `A` and `B`, defined by iterating the
(balanced) geometric mean: `gpow 0 A B = B` and `gpow (m+1) A B = gmean A (gpow m A B)`.
For commuting `A`, `B` this is `A ^ (1 - 2⁻ᵐ) * B ^ (2⁻ᵐ)`.

Since `gmean` is jointly concave and monotone in its second variable, each `gpow m` is
jointly concave.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
open Matrix

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The iterated geometric mean: `gpow m A B` is the `2⁻ᵐ`-weighted geometric mean. -/
