/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- A pure state of three qubits, written in the computational basis indexed by
`Bool × Bool × Bool` (`false = |0⟩`, `true = |1⟩`). -/
abbrev State := Bool × Bool × Bool → ℂ

/-- Pauli `X` acting on the first qubit. -/
def X₁ (f : State) : State := fun p => f (!p.1, p.2.1, p.2.2)

/-- Pauli `X` acting on the second qubit. -/
def X₂ (f : State) : State := fun p => f (p.1, !p.2.1, p.2.2)

/-- Pauli `X` acting on the third qubit. -/
def X₃ (f : State) : State := fun p => f (p.1, p.2.1, !p.2.2)

/-- Pauli `Y` acting on the first qubit. -/
def Y₁ (f : State) : State :=
  fun p => (if p.1 then Complex.I else -Complex.I) * f (!p.1, p.2.1, p.2.2)

/-- Pauli `Y` acting on the second qubit. -/
def Y₂ (f : State) : State :=
  fun p => (if p.2.1 then Complex.I else -Complex.I) * f (p.1, !p.2.1, p.2.2)

/-- Pauli `Y` acting on the third qubit. -/
def Y₃ (f : State) : State :=
  fun p => (if p.2.2 then Complex.I else -Complex.I) * f (p.1, p.2.1, !p.2.2)

/-- The GHZ state `(|000⟩ + |111⟩)/√2`. -/
noncomputable def ghz : State :=
  fun p => if p = (false, false, false) ∨ p = (true, true, true)
           then (Real.sqrt 2 : ℂ)⁻¹ else 0

/-- The GHZ state is a unit vector. -/
theorem ghz_normalized : ∑ p : Bool × Bool × Bool, ‖ghz p‖ ^ 2 = 1 := by
  have hnorm : ‖((Real.sqrt 2 : ℂ))⁻¹‖ ^ 2 = 1 / 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ghz, Prod.mk.injEq]
  norm_num [hnorm]

/-- `X ⊗ Y ⊗ Y` has eigenvalue `-1` on the GHZ state. -/
theorem ghz_XYY : X₁ (Y₂ (Y₃ ghz)) = -ghz := by
  funext p
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;>
    simp [X₁, Y₂, Y₃, ghz, Complex.ext_iff]

/-- `Y ⊗ X ⊗ Y` has eigenvalue `-1` on the GHZ state. -/
theorem ghz_YXY : Y₁ (X₂ (Y₃ ghz)) = -ghz := by
  funext p
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;>
    simp [Y₁, X₂, Y₃, ghz, Complex.ext_iff]

/-- `Y ⊗ Y ⊗ X` has eigenvalue `-1` on the GHZ state. -/
theorem ghz_YYX : Y₁ (Y₂ (X₃ ghz)) = -ghz := by
  funext p
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;>
    simp [Y₁, Y₂, X₃, ghz, Complex.ext_iff]

/-- `X ⊗ X ⊗ X` has eigenvalue `+1` on the GHZ state. -/
theorem ghz_XXX : X₁ (X₂ (X₃ ghz)) = ghz := by
  funext p
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;> simp [X₁, X₂, X₃, ghz]

/-- **Mermin's GHZ argument, local part.**  No assignment of definite outcomes
`±1` to the six local observables (`X` and `Y` for each of the three qubits) can
reproduce the four deterministic quantum predictions
`XYY = YXY = YYX = -1` and `XXX = +1`. -/
theorem no_local_hidden_variables
    (aX aY bX bY cX cY : ℤ)
    (haX : aX = 1 ∨ aX = -1) (haY : aY = 1 ∨ aY = -1)
    (hbX : bX = 1 ∨ bX = -1) (hbY : bY = 1 ∨ bY = -1)
    (hcX : cX = 1 ∨ cX = -1) (hcY : cY = 1 ∨ cY = -1) :
    ¬ (aX * bY * cY = -1 ∧ aY * bX * cY = -1 ∧ aY * bY * cX = -1 ∧
       aX * bX * cX = 1) := by
  rcases haX with h1 | h1 <;> rcases haY with h2 | h2 <;>
    rcases hbX with h3 | h3 <;> rcases hbY with h4 | h4 <;>
    rcases hcX with h5 | h5 <;> rcases hcY with h6 | h6 <;>
    subst h1 <;> subst h2 <;> subst h3 <;> subst h4 <;> subst h5 <;> subst h6 <;>
    decide

/-- **GHZ nonlocality (Mermin's paradox).**

The three-qubit GHZ state is a simultaneous eigenstate of `XYY`, `YXY`, `YYX`
with eigenvalue `-1`, and of `XXX` with eigenvalue `+1`; yet no local
hidden-variable model — i.e. no assignment of definite `±1` outcomes to the six
local observables — can reproduce these four deterministic predictions. -/
theorem ghz_nonlocal :
    (X₁ (Y₂ (Y₃ ghz)) = -ghz ∧ Y₁ (X₂ (Y₃ ghz)) = -ghz ∧
     Y₁ (Y₂ (X₃ ghz)) = -ghz ∧ X₁ (X₂ (X₃ ghz)) = ghz) ∧
    ∀ aX aY bX bY cX cY : ℤ,
      (aX = 1 ∨ aX = -1) → (aY = 1 ∨ aY = -1) →
      (bX = 1 ∨ bX = -1) → (bY = 1 ∨ bY = -1) →
      (cX = 1 ∨ cX = -1) → (cY = 1 ∨ cY = -1) →
      ¬ (aX * bY * cY = -1 ∧ aY * bX * cY = -1 ∧ aY * bY * cX = -1 ∧
         aX * bX * cX = 1) :=
  ⟨⟨ghz_XYY, ghz_YXY, ghz_YYX, ghz_XXX⟩, no_local_hidden_variables⟩

end QC

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

