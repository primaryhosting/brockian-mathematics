import Mathlib
import RequestProject.Classical

/-!
# Quantum relative entropy

Definitions of the matrix logarithm (via the continuous functional calculus), the Umegaki
relative entropy of two density matrices, and quantum channels in Kraus form.
-/

open Matrix Unitary
open scoped BigOperators ComplexOrder

namespace QI

variable {m n ι : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype ι]

/-- The matrix logarithm of a Hermitian matrix, defined through the continuous functional
calculus (with the convention `log 0 = 0`, so that vanishing eigenvalues contribute nothing). -/

theorem cfc_diagonal (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal fun i => (d i : ℂ)) = diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  have hA : IsSelfAdjoint (diagonal fun i => (d i : ℂ)) := isSelfAdjoint_diagonal d
  set s : Finset ℝ := Finset.image d Finset.univ with hs
  set P : Polynomial ℝ := Lagrange.interpolate s id f with hP
  have hnode : ∀ i : n, P.eval (d i) = f (d i) := by
    intro i
    have hmem : d i ∈ s := by simp [hs]
    have := Lagrange.eval_interpolate_at_node (F := ℝ) (ι := ℝ) (s := s) (v := id) f
      (Set.injOn_id _) hmem
    simpa [hP] using this
  have h1 : cfc f (diagonal fun i => (d i : ℂ))
      = cfc (fun x => P.eval x) (diagonal fun i => (d i : ℂ)) := by
    refine cfc_congr ?_
    intro r hr
    obtain ⟨i, rfl⟩ := spectrum_real_diagonal d hr
    exact (hnode i).symm
  rw [h1, cfc_polynomial P _ hA, aeval_diagonal d P]
  simp only [hnode]

/-- The continuous functional calculus commutes with conjugation by a unitary. -/
