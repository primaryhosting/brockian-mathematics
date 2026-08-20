/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Real Minkowski space `ℝ^{1,3}`. -/
abbrev Spacetime := Fin 4 → ℝ

/-- Complexified Minkowski space `ℂ^4`, the domain of the analytically continued
Wightman functions. -/
abbrev CSpace := Fin 4 → ℂ

/-- The Minkowski bilinear form on real Minkowski space (signature `+ - - -`). -/

theorem exists_jostPoint : ∃ x : Fin 2 → Spacetime, IsJostPoint x := by
  refine ⟨![0, ![0, 1, 0, 0]], ?_⟩
  intro lam _ hpos
  obtain ⟨k, hk⟩ := hpos
  have hk0 : k = 0 := Subsingleton.elim _ _
  subst hk0
  have hv : (∑ k : Fin 1, lam k •
      ((![0, ![0, 1, 0, 0]] : Fin 2 → Spacetime) k.castSucc
        - (![0, ![0, 1, 0, 0]] : Fin 2 → Spacetime) k.succ))
      = ![0, -lam 0, 0, 0] := by
    funext mu
    fin_cases mu <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hv]
  have : mform ![0, -lam 0, 0, 0] ![0, -lam 0, 0, 0] = -(lam 0 * lam 0) := by
    simp [mform]
  rw [this]
  nlinarith [hk]

/-! ## Wightman theories and the CPT theorem -/

/-- A (scalar, hermitian) Wightman quantum field theory, described through its analytically
continued Wightman functions `W n : (Fin n → ℂ^4) → ℂ` on complexified Minkowski space.

The three axioms are:

* `bhw_covariance`: Lorentz invariance in the form supplied by the Bargmann–Hall–Wightman
  theorem — the analytic Wightman functions are invariant under every complex Lorentz
  transformation that can be reached from the identity by a continuous path inside the
  complex Lorentz group.  (For real proper orthochronous transformations this is ordinary
  Lorentz invariance; the extension to the complex group is the analytic input.)
* `hermiticity`: the hermiticity relation for the Wightman functions of a hermitian field,
  `conj W_n(x₁,…,x_n) = W_n(x_n,…,x₁)`.
* `weak_locality`: locality, in the form of weak local commutativity at Jost points,
  `W_n(x_n,…,x₁) = W_n(x₁,…,x_n)`. -/
structure WightmanTheory where
  /-- The analytic `n`-point Wightman functions. -/
  W : (n : ℕ) → (Fin n → CSpace) → ℂ
  bhw_covariance : ∀ L : ℝ → Matrix (Fin 4) (Fin 4) ℂ, Continuous L → L 0 = 1 →
    (∀ t, IsComplexLorentz (L t)) → ∀ (n : ℕ) (z : Fin n → CSpace),
      W n (fun i => L 1 *ᵥ z i) = W n z
  hermiticity : ∀ (n : ℕ) (x : Fin n → Spacetime),
    (starRingEnd ℂ) (W n fun i => emb (x i)) = W n fun i => emb (x i.rev)
  weak_locality : ∀ (m : ℕ) (x : Fin (m + 1) → Spacetime), IsJostPoint x →
    (W (m + 1) fun i => emb (x i.rev)) = W (m + 1) fun i => emb (x i)

/-- Invariance of the Wightman functions under total spacetime inversion `x ↦ -x`,
obtained from Lorentz invariance by continuing along a path in the complex Lorentz group. -/
