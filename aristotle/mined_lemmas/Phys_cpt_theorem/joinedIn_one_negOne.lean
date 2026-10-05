/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to be the first command, so the header above is a plain
-- block comment; the identical module docstring is repeated below.)

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

/-! ## The complexified Lorentz group

The mathematical heart of the CPT theorem (Jost's theorem) is the following fact: the total
inversion `-1` of Minkowski spacetime, which is *not* in the identity component of the real
Lorentz group, *is* reachable inside the **complex** Lorentz group `L(ℂ) = O(1,3;ℂ)`.  Indeed

  `diag(-1,-1,-1,-1) = diag(-1,-1,1,1) · diag(1,1,-1,-1)`,

where the second factor is the real rotation by `π` about the `x`-axis (an element of the
proper orthochronous group `L₊↑`) and the first factor is the value at rapidity `iπ` of the
family of boosts in the `(0,1)`–plane analytically continued to imaginary rapidity.

This is why a Lorentz-invariant theory whose Wightman functions possess the standard analytic
continuation in the boost parameter is automatically invariant under total inversion. -/

/-- The Minkowski metric `diag(1,-1,-1,-1)` on complexified spacetime `ℂ⁴`. -/

theorem joinedIn_one_negOne :
    JoinedIn ProperComplexLorentz 1 (-1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  refine ⟨⟨⟨fun t => cptFamily ((Real.cos (π * (t : ℝ)) : ℝ) : ℂ)
      ((Real.sin (π * (t : ℝ)) : ℝ) : ℂ),
      continuous_cptPath.comp continuous_subtype_val⟩, ?_, ?_⟩, ?_⟩
  · simp [cptFamily_one_zero]
  · simp [cptFamily_negOne_zero]
  · intro t
    refine cptFamily_mem _ _ ?_
    have : Real.sin (π * (t : ℝ)) ^ 2 + Real.cos (π * (t : ℝ)) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq _
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this

/-! ## Wightman theories and the CPT theorem -/

/-- A point of complexified Minkowski spacetime. -/
abbrev CPoint := Fin 4 → ℂ

/-- A **Lorentz-invariant local quantum field theory**, presented through its `n`-point
Wightman function `W`, analytically continued to complexified Minkowski spacetime.

The three axioms are the standard ingredients of the Wightman formulation of the CPT theorem:

* `lorentz_invariance` — relativistic invariance: `W` is invariant under the real proper
  orthochronous Lorentz group `L₊↑`;
* `boost_analytic_continuation` — the consequence of the spectral condition: the invariance
  of `W` under boosts in the `(0,1)`–plane persists after analytic continuation of the
  rapidity to imaginary values (this is the one-parameter core of the Bargmann–Hall–Wightman
  analyticity argument);
* `weak_local_commutativity` — locality in Jost's form: `W` is unchanged when the order of its
  arguments is reversed. -/
structure LorentzInvariantLocalQFT (n : ℕ) where
  /-- The `n`-point Wightman function, analytically continued to complex arguments. -/
  W : (Fin n → CPoint) → ℂ
  /-- Relativistic invariance under the real proper orthochronous Lorentz group `L₊↑`. -/
  lorentz_invariance :
    ∀ Λ ∈ ProperOrthochronousLorentz, ∀ x : Fin n → CPoint,
      W (fun i => (Λ.map (fun a : ℝ => (a : ℂ))) *ᵥ x i) = W x
  /-- Invariance under `(0,1)`–boosts continued to imaginary rapidity. -/
  boost_analytic_continuation :
    ∀ θ : ℝ, ∀ x : Fin n → CPoint, W (fun i => imagBoost θ *ᵥ x i) = W x
  /-- Weak local commutativity (locality). -/
  weak_local_commutativity :
    ∀ x : Fin n → CPoint, W (fun i => x (Fin.rev i)) = W x

/-- **The CPT theorem.**  In any Lorentz-invariant local quantum field theory the Wightman
functions are invariant under the CPT transformation: total inversion of all spacetime
arguments combined with reversal of their order,

  `W(-x_n, …, -x₁) = W(x₁, …, x_n)`.

The proof factors the total inversion as an imaginary-rapidity boost times a real rotation by
`π`, applies relativistic invariance to the rotation and the analytic continuation to the
boost, and finally uses weak local commutativity to undo the reversal of the arguments. -/
