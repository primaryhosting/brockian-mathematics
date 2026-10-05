import Mathlib

/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Module Module.End Submodule

namespace QPhys

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A nonzero vector in the `μ`-eigenspace of a symmetric (Hermitian) operator witnesses that `μ`
is a genuine eigenvalue, and hence that `μ` is real. -/

lemma eigenvalue_eq_re_of_isSymmetric {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {μ : 𝕜} {x : E}
    (hx : x ≠ 0) (hxμ : A x = μ • x) : ((RCLike.re μ : ℝ) : 𝕜) = μ := by
  have hev : Module.End.HasEigenvalue A μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hxμ, hx⟩
  exact RCLike.conj_eq_iff_re.mp (hA.conj_eigenvalue_eq_self hev)

variable [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}

/-- The nontrivial joint eigenspaces of two operators on a finite-dimensional space are indexed by
a finite set of pairs of scalars. -/
