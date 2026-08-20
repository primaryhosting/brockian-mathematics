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


theorem tendsto_vnEnt {X : Type*} {l : Filter X} {F : X → Matrix n n ℂ} {A : Matrix n n ℂ}
    (hF : ∀ x, (F x).IsHermitian) (hA : A.IsHermitian) (h : Tendsto F l (𝓝 A)) :
    Tendsto (fun x => vnEnt (F x)) l (𝓝 (vnEnt A)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hzero : ∀ M : Matrix n n ℂ, vnEnt M = 0 := by
      intro M; rw [vnEnt]; simp
    simp only [hzero]
    exact tendsto_const_nhds
  · set r : ℝ := ‖A‖ + 1 with hr
    have hcomp : IsCompact (Set.Icc (-r) r) := isCompact_Icc
    have hnorm : Tendsto (fun x => ‖F x‖) l (𝓝 ‖A‖) := h.norm
    have hev : ∀ᶠ x in l, spectrum ℝ (F x) ⊆ Set.Icc (-r) r := by
      have hlt : ∀ᶠ x in l, ‖F x‖ < ‖A‖ + 1 := hnorm.eventually_lt_const (by linarith)
      filter_upwards [hlt] with x hx
      exact spectrum_subset_Icc hx.le
    have hspecA : spectrum ℝ A ⊆ Set.Icc (-r) r := spectrum_subset_Icc (by simp [hr])
    have hcfc := Filter.Tendsto.cfc (𝕜 := ℝ) hcomp Real.negMulLog h hev
      (Filter.Eventually.of_forall (fun x => (hF x : IsSelfAdjoint (F x))))
      hspecA (hA : IsSelfAdjoint A) Real.continuous_negMulLog.continuousOn
    have hcont : Continuous (fun M : Matrix n n ℂ => M.trace.re) := by fun_prop
    have hres := (hcont.continuousAt (x := cfc Real.negMulLog A)).tendsto.comp hcfc
    rw [vnEnt_eq_trace_cfc hA]
    refine hres.congr fun x => ?_
    rw [vnEnt_eq_trace_cfc (hF x)]
    rfl

end QI

import RequestProject.SSA.Entropy

/-!
# Star algebra homomorphisms of matrix algebras

Conjugation by a unitary, reindexing along an equivalence, and the two Kronecker embeddings
`X ↦ X ⊗ 1`, `Y ↦ 1 ⊗ Y` are unital star algebra homomorphisms, hence commute with the
continuous functional calculus.  This gives the transformation rules for `CFC.log` that are
needed to manipulate relative entropies.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-! ### Conjugation by a unitary -/

/-- Conjugation by a unitary, as a star algebra homomorphism. -/
