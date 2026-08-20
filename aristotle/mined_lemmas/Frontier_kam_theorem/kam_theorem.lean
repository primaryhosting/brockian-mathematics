/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Setting

We work with the standard "conjugacy" formulation of KAM theory.  The phase space is an
arbitrary type `P`, the `n`-dimensional torus is modelled by its universal cover
`Fin n → ℝ` (all objects below are invariant under the choice of representative, so
nothing is lost), and a *torus with rotation vector `ω`* for a dynamical system
`f : P → P` is an embedding `Ψ : (Fin n → ℝ) → P` satisfying the conjugacy equation

  `f (Ψ θ) = Ψ (θ + ω)`  for all `θ`,

i.e. `f` restricted to the image of `Ψ` is the rigid rotation by `ω`.
-/

/-- `IsInvariantTorus n f ω Ψ` : the parametrised torus `Ψ` is invariant under the
dynamics `f` and the induced motion on it is the rigid rotation by the frequency
vector `ω`. -/

theorem kam_theorem {P : Type*} {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → P → P) (ω : Fin n → ℝ) (Ψ : E → ((Fin n → ℝ) → P))
    (T : ℝ → E → E) (K : NNReal) (C : ℝ) [CompleteSpace E]
    (hK : K < 1)
    (hlip : ∀ ε : ℝ, LipschitzWith K (T ε))
    (hfix : ∀ (ε : ℝ) (u : E), T ε u = u → IsInvariantTorus (f ε) ω (Ψ u))
    (hzero : T 0 0 = 0)
    (hpert : ∀ (ε : ℝ) (u : E), ‖T ε u - T 0 u‖ ≤ C * |ε|) :
    ∀ ε : ℝ, ∃ u : E, IsInvariantTorus (f ε) ω (Ψ u) ∧ ‖u‖ ≤ C * |ε| / (1 - K) := by
  intro ε
  have hcon : ContractingWith K (T ε) := ⟨hK, hlip ε⟩
  set u := hcon.fixedPoint
  have hufix : T ε u = u := hcon.fixedPoint_isFixedPt
  refine ⟨u, hfix ε u hufix, ?_⟩
  have h0 : dist (0 : E) u ≤ dist (0 : E) (T ε 0) / (1 - K) := hcon.dist_fixedPoint_le 0
  have hnum : dist (0 : E) (T ε 0) ≤ C * |ε| := by
    have := hpert ε 0
    rw [hzero, sub_zero] at this
    simpa [dist_eq_norm, norm_sub_rev] using this
  have hK' : (0 : ℝ) < 1 - K := by
    have : (K : ℝ) < 1 := by exact_mod_cast hK
    linarith
  calc ‖u‖ = dist (0 : E) u := by simp [dist_eq_norm]
    _ ≤ dist (0 : E) (T ε 0) / (1 - K) := h0
    _ ≤ C * |ε| / (1 - K) := by
        gcongr

/-! ## Small divisors

The hypothesis `hlip` above is exactly what the classical KAM scheme establishes, and its
crucial ingredient is the solvability of the *homological equation* with control on the
small divisors `⟨k, ω⟩`.  We record the corresponding elementary estimate for a Diophantine
frequency vector. -/

/-- The `ℓ¹`-norm of an integer frequency multi-index, as a real number. -/
