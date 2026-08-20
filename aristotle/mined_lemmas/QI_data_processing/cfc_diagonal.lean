import RequestProject.Kron

/-!
# Vectorization, the modular operator and relative entropy

We vectorize matrices, express the relative entropy `Tr ρ log ρ - Tr ρ log σ` as (minus) a
quadratic form of `log (σ ⊗ (ρ⁻¹)ᵀ)` at the vectorization of `√ρ`, and record the
variational ("completing the square") characterization of resolvent quadratic forms.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m N : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype N] [DecidableEq N]

/-! ### Vectorization -/

/-- Vectorization of a matrix: the vector of all its entries, indexed by pairs. -/

theorem cfc_diagonal (f : ℝ → ℝ) (d : n → ℝ) :
    cfc f (diagonal fun i => ((d i : ℝ) : ℂ)) = diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  have key : ∀ i : n, spectrum ℝ ((d i : ℝ) : ℂ) = {d i} := fun i =>
    spectrum.scalar_eq (𝕜 := ℝ) (A := ℂ) (d i)
  have hd : IsSelfAdjoint (fun i => ((d i : ℝ) : ℂ)) := by ext i; simp
  have hsp : spectrum ℝ (fun i => ((d i : ℝ) : ℂ)) = Set.range d := by
    rw [Pi.spectrum_eq]
    ext r
    simp only [Set.mem_iUnion, key, Set.mem_singleton_iff, Set.mem_range]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  have hcont : ContinuousOn f (spectrum ℝ (fun i => ((d i : ℝ) : ℂ))) := by
    rw [hsp]; exact (Set.finite_range d).continuousOn f
  have hcd : Continuous (diagSAH : (n → ℂ) → Matrix n n ℂ) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun v : n → ℂ => Matrix.diagonal v i j
    simp only [Matrix.diagonal_apply]
    split <;> fun_prop
  have hself : IsSelfAdjoint (diagSAH (fun i => ((d i : ℝ) : ℂ))) := by
    rw [IsSelfAdjoint, ← map_star, hd.star_eq]
  have h := (diagSAH (n := n)).map_cfc f (fun i => ((d i : ℝ) : ℂ)) hcont hcd hd hself
  have hpi : (cfc f (fun i => ((d i : ℝ) : ℂ))) = fun i => ((f (d i) : ℝ) : ℂ) := by
    rw [cfc_map_pi (S := ℂ) f _ (by
      rw [show (⋃ i, spectrum ℝ ((d i : ℝ) : ℂ)) = Set.range d from by
        rw [← Pi.spectrum_eq]; exact hsp]
      exact (Set.finite_range d).continuousOn f) hd (fun i => by rw [IsSelfAdjoint]; simp)]
    funext i
    rw [show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl, cfc_algebraMap]
    rfl
  have hdd : diagSAH (fun i => ((d i : ℝ) : ℂ)) = diagonal (fun i => ((d i : ℝ) : ℂ)) := rfl
  rw [← hdd, ← h, hpi]
  rfl

/-- The continuous functional calculus commutes with unitary conjugation. -/
