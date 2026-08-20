/-
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the header above
-- is written as a plain block comment; its text is otherwise verbatim.)

import Mathlib

/-!
## Overview

The Atiyah–Singer index theorem states that for an elliptic (pseudo)differential operator
`D : Γ(E) → Γ(F)` on a closed manifold `M`, the *analytic index*

  `ind_a(D) = dim ker D - dim coker D`

equals the *topological index*, a quantity computed purely from the symbol data of `D`
(via characteristic classes).

Full pseudodifferential theory on manifolds is not available in Mathlib, so we formalize the

theorem finrank_cohomologyAt {A B C : Type*} [AddCommGroup A] [Module 𝕜 A] [AddCommGroup B]
    [Module 𝕜 B] [FiniteDimensional 𝕜 B] [AddCommGroup C] [Module 𝕜 C]
    (f : A →ₗ[𝕜] B) (g : B →ₗ[𝕜] C) (hfg : g.comp f = 0) :
    (finrank 𝕜 (cohomologyAt f g) : ℤ)
      = (finrank 𝕜 (LinearMap.ker g) : ℤ) - (finrank 𝕜 (LinearMap.range f) : ℤ) := by
  have hle : LinearMap.range f ≤ LinearMap.ker g := by
    rintro x ⟨y, rfl⟩
    have := congrArg (fun (h : A →ₗ[𝕜] C) => h y) hfg
    simpa [LinearMap.mem_ker] using this
  have hiso := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have h2 := Submodule.finrank_quotient_add_finrank
      ((LinearMap.range f).comap (LinearMap.ker g).subtype)
  rw [hiso] at h2
  simp only [cohomologyAt]
  omega

variable {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  [∀ i, FiniteDimensional 𝕜 (V i)]

/-- Telescoping identity used for the Euler–Poincaré computation. -/
