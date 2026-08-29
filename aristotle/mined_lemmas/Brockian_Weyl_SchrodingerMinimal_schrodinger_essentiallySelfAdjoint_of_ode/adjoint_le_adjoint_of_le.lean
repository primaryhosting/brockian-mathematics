import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.Weyl.SchrodingerMinimal

open LinearPMap

open scoped LinearPMap ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A densely defined operator `T` on a complex Hilbert space is *essentially self-adjoint* if
its adjoint is self-adjoint; equivalently, `T` has a unique self-adjoint extension, namely the
closure `T†† = T̄` of `T`. -/

theorem adjoint_le_adjoint_of_le {S T : H →ₗ.[ℂ] H} (hS : Dense (S.domain : Set H)) (h : S ≤ T) :
    T† ≤ S† := by
  have hT : Dense (T.domain : Set H) := hS.mono fun x hx => h.1 hx
  have hfa : S.IsFormalAdjoint T† := by
    intro x y
    have hx : (x : H) ∈ T.domain := h.1 x.2
    have h1 : ⟪T (⟨(x : H), hx⟩ : T.domain), (y : H)⟫ = ⟪(x : H), T† y⟫ :=
      (adjoint_isFormalAdjoint hT).symm ⟨(x : H), hx⟩ y
    rwa [← h.2 (rfl : ((x : H)) = ((⟨(x : H), hx⟩ : T.domain) : H))] at h1
  exact hfa.le_adjoint hS

/-- A densely defined symmetric operator is contained in its adjoint. -/
