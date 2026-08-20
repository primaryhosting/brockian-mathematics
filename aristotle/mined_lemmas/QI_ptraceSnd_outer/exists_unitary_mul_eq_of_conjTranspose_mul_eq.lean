import Mathlib

/-!
# Purification of mixed states

A *mixed state* on a finite-dimensional system with index type `n` is a positive semidefinite
matrix `rho : Matrix n n ℂ` of trace `1`.  A *purification* of `rho` with ancilla index type `m`
is a vector `v : n × m → ℂ` in the tensor product whose density matrix `|v⟩⟨v|` has partial
trace over the ancilla equal to `rho`.

The main result `QI.purification_exists` states that every mixed state admits a purification
(with ancilla of the same dimension), and that any two purifications with the same ancilla
differ by a unitary acting on the ancilla alone.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder

set_option synthInstance.maxHeartbeats 1000000

namespace QI

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The density matrix `|v⟩⟨v|` of the vector `v`. -/

theorem exists_unitary_mul_eq_of_conjTranspose_mul_eq {A B : Matrix m n ℂ}
    (h : Aᴴ * A = Bᴴ * B) : ∃ W ∈ Matrix.unitaryGroup m ℂ, W * A = B := by
  classical
  set f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m := Matrix.toEuclideanLin A with hfdef
  set g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m := Matrix.toEuclideanLin B with hgdef
  have hinner : ∀ x y : EuclideanSpace ℂ n, ⟪f x, f y⟫_ℂ = ⟪g x, g y⟫_ℂ := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm, dotProduct_comm ((g y).ofLp)]
    simp only [hfdef, hgdef, ofLp_toEuclideanLin]
    rw [dotProduct_conj_mulVec, dotProduct_conj_mulVec, h]
  have hnorm : ∀ x : EuclideanSpace ℂ n, ‖g x‖ = ‖f x‖ := by
    intro x
    have h1 := hinner x x
    have h3 : ‖f x‖ ^ 2 = ‖g x‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h1]
    rw [← Real.sqrt_sq (norm_nonneg (g x)), ← h3, Real.sqrt_sq (norm_nonneg (f x))]
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have hx' := hnorm x
    rw [hx, norm_zero] at hx'
    exact norm_eq_zero.mp hx'
  set L0 : (LinearMap.range f) →ₗ[ℂ] EuclideanSpace ℂ m :=
    ((LinearMap.ker f).liftQ g hker).comp
      (LinearMap.quotKerEquivRange f).symm.toLinearMap with hL0def
  have hL0 : ∀ x : EuclideanSpace ℂ n,
      L0 ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
    intro x
    have he : (LinearMap.quotKerEquivRange f).symm ⟨f x, LinearMap.mem_range_self f x⟩
        = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk f x).symm
    simp [hL0def, he]
  have hL0norm : ∀ s : LinearMap.range f, ‖L0 s‖ = ‖(s : EuclideanSpace ℂ m)‖ := by
    rintro ⟨s, x, rfl⟩
    rw [hL0 x]
    exact hnorm x
  set L : (LinearMap.range f) →ₗᵢ[ℂ] EuclideanSpace ℂ m := ⟨L0, hL0norm⟩ with hLdef
  set Lext : EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ m := L.extend with hLextdef
  set W : Matrix m m ℂ := Matrix.toEuclideanLin.symm Lext.toLinearMap with hWdef
  have hWapply : ∀ v : EuclideanSpace ℂ m, W *ᵥ v.ofLp = (Lext v).ofLp := by
    intro v
    rw [← ofLp_toEuclideanLin]
    congr 1
    rw [hWdef, LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨W, ?_, ?_⟩
  · refine mem_unitaryGroup_of_dotProduct W ?_
    intro x y
    have hx := hWapply (WithLp.toLp 2 x)
    have hy := hWapply (WithLp.toLp 2 y)
    have hinn : ⟪Lext (WithLp.toLp 2 x), Lext (WithLp.toLp 2 y)⟫_ℂ
        = ⟪(WithLp.toLp 2 x : EuclideanSpace ℂ m), WithLp.toLp 2 y⟫_ℂ :=
      Lext.inner_map_map _ _
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at hinn
    rw [hx, hy, dotProduct_comm, hinn]
    exact dotProduct_comm _ _
  · refine matrix_ext_of_mulVec ?_
    intro x
    have hfx : f (WithLp.toLp 2 x) = WithLp.toLp 2 (A *ᵥ x) :=
      Matrix.toLpLin_toLp 2 2 A x
    have hgx : g (WithLp.toLp 2 x) = WithLp.toLp 2 (B *ᵥ x) :=
      Matrix.toLpLin_toLp 2 2 B x
    have hext : Lext (f (WithLp.toLp 2 x)) = g (WithLp.toLp 2 x) := by
      have h2 : Lext ((⟨f (WithLp.toLp 2 x), LinearMap.mem_range_self f _⟩ :
          LinearMap.range f) : EuclideanSpace ℂ m)
          = L ⟨f (WithLp.toLp 2 x), LinearMap.mem_range_self f _⟩ :=
        LinearIsometry.extend_apply L _
      simpa [hLdef, hL0] using h2
    rw [← Matrix.mulVec_mulVec]
    have hWA : W *ᵥ (A *ᵥ x) = (Lext (WithLp.toLp 2 (A *ᵥ x))).ofLp := by
      simpa using hWapply (WithLp.toLp 2 (A *ᵥ x))
    rw [hWA, ← hfx, hext, hgx]

/-- Unitary freedom for purifications, in the form `ψ ψᴴ = φ φᴴ`. -/
