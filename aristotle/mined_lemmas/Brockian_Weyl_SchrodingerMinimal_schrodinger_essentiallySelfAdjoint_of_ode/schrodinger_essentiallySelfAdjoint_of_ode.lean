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

theorem schrodinger_essentiallySelfAdjoint_of_ode (T : L2R →ₗ.[ℂ] L2R)
    (hdense : Dense (T.domain : Set L2R)) (hsymm : T.IsFormalAdjoint T)
    (hode_pos : ∀ (u : L2R) (hu : u ∈ (T†).domain), T† ⟨u, hu⟩ = Complex.I • u → u = 0)
    (hode_neg : ∀ (u : L2R) (hu : u ∈ (T†).domain), T† ⟨u, hu⟩ = -Complex.I • u → u = 0) :
    EssentiallySelfAdjoint T :=
  essentiallySelfAdjoint_of_deficiency hdense hsymm hode_pos hode_neg

end Brockian.Weyl.SchrodingerMinimal

