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

theorem mem_orthogonal_range_shiftMap_iff {T : H →ₗ.[ℂ] H} (hdense : Dense (T.domain : Set H))
    (z : ℂ) (v : H) :
    v ∈ (LinearMap.range (shiftMap T z))ᗮ ↔
      ∃ hv : v ∈ (T†).domain, T† ⟨v, hv⟩ = conj (-z) • v := by
  constructor
  · intro hv
    have key : ∀ x : T.domain, ⟪conj (-z) • v, (x : H)⟫ = ⟪v, T x⟫ := by
      intro x
      have h0 : ⟪shiftMap T z x, v⟫ = 0 := (Submodule.mem_orthogonal _ v).mp hv _ ⟨x, rfl⟩
      have h0' : ⟪v, T x + z • (x : H)⟫ = 0 := by
        rw [← inner_conj_symm]
        simp only [shiftMap_apply] at h0
        rw [h0, map_zero]
      rw [inner_add_right, inner_smul_right] at h0'
      rw [inner_smul_left, RingHomCompTriple.comp_apply, RingHom.id_apply]
      simp only [map_neg, RingHomCompTriple.comp_apply, RingHom.id_apply,
        Complex.conj_conj]
      linear_combination h0'
    have hv' : v ∈ (T†).domain := mem_adjoint_domain_of_exists _ ⟨conj (-z) • v, key⟩
    exact ⟨hv', adjoint_apply_eq hdense ⟨v, hv'⟩ key⟩
  · rintro ⟨hv, hval⟩
    rw [Submodule.mem_orthogonal]
    rintro u ⟨x, rfl⟩
    have h1 : ⟪T† (⟨v, hv⟩ : (T†).domain), (x : H)⟫ = ⟪v, T x⟫ :=
      adjoint_isFormalAdjoint hdense ⟨v, hv⟩ x
    rw [hval, inner_smul_left] at h1
    simp only [map_neg, RingHomCompTriple.comp_apply, RingHom.id_apply, Complex.conj_conj] at h1
    have h2 : ⟪v, T x + z • (x : H)⟫ = 0 := by
      rw [inner_add_right, inner_smul_right, ← h1]
      ring
    have := congrArg (starRingEnd ℂ) h2
    rw [inner_conj_symm, map_zero] at this
    simpa using this

/-- Key estimate: for a symmetric operator and purely imaginary `z`,
`‖A x + z • x‖² = ‖A x‖² + ‖z • x‖²`. -/
