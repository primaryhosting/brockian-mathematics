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

theorem norm_shift_sq {A : H →ₗ.[ℂ] H} (hsymm : A.IsFormalAdjoint A) {z : ℂ}
    (hz : conj z = -z) (x : A.domain) :
    ‖A x + z • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + ‖z • (x : H)‖ ^ 2 := by
  have hc : conj (⟪A x, (x : H)⟫) = ⟪A x, (x : H)⟫ := by
    rw [inner_conj_symm]
    exact (hsymm x x).symm
  have hzc : conj (z * ⟪A x, (x : H)⟫) = -(z * ⟪A x, (x : H)⟫) := by
    rw [map_mul, hz, hc]; ring
  have hre : Complex.re (z * ⟪A x, (x : H)⟫) = 0 := by
    have h2 := Complex.add_conj (z * ⟪A x, (x : H)⟫)
    rw [hzc] at h2
    simp only [add_neg_cancel] at h2
    have : ((2 * Complex.re (z * ⟪A x, (x : H)⟫) : ℝ) : ℂ) = 0 := h2.symm
    have : (2 : ℝ) * Complex.re (z * ⟪A x, (x : H)⟫) = 0 := by exact_mod_cast this
    linarith
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right]
  simp only [RCLike.re_to_complex, hre]
  ring

/-- For a closed symmetric operator `A` and unit purely imaginary `z` with `Ran (A + z)` dense,
the operator `A + z` is surjective. -/
