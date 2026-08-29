/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

open Complex

/-!
## Bloch's theorem

A one-dimensional Hamiltonian `H = -d²/dx² + V` with a potential `V` of period `a`
commutes with the translation `x ↦ x + a`.  Consequently, if `ψ` is an eigenstate of `H`
belonging to a non-degenerate energy level, then the translate of `ψ` is again an
eigenstate for the same energy, hence a multiple `λ` of `ψ`; unitarity of the translation
(equivalently, boundedness of `ψ`) forces `‖λ‖ = 1`.  Writing `λ = e^{i k a}` one obtains
the Bloch form `ψ(x) = e^{i k x} u(x)` with `u` periodic of period `a`.

`Phys.bloch_theorem` is the main step: a function obeying `ψ(x + a) = λ ψ(x)` with
`‖λ‖ = 1` is a Bloch wave.  The auxiliary results below supply the physical input,
and `Phys.bloch_theorem_of_periodic_hamiltonian` assembles the whole argument.
-/

/-- **Bloch's theorem.**  If a wave function `ψ` satisfies `ψ(x + a) = λ ψ(x)` for all `x`,
where `λ` is a unimodular constant and `a ≠ 0` is the lattice period, then `ψ` is a Bloch
wave: there is a crystal momentum `k` and an `a`-periodic function `u` with
`ψ(x) = e^{i k x} u(x)`. -/
theorem bloch_theorem (a : ℝ) (ha : a ≠ 0) (ψ : ℝ → ℂ) (lam : ℂ) (hlam : ‖lam‖ = 1)
    (hshift : ∀ x : ℝ, ψ (x + a) = lam * ψ x) :
    ∃ (k : ℝ) (u : ℝ → ℂ),
      (∀ x : ℝ, u (x + a) = u x) ∧ (∀ x : ℝ, ψ x = Complex.exp (Complex.I * k * x) * u x) := by
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff lam).mp hlam
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  refine ⟨θ / a, fun x => Complex.exp (-(Complex.I * ((θ : ℂ) / (a : ℂ)) * (x : ℂ))) * ψ x, ?_, ?_⟩
  · intro x
    simp only
    have hxa : ((x + a : ℝ) : ℂ) = (x : ℂ) + (a : ℂ) := by push_cast; ring
    have key : Complex.exp (-(Complex.I * ((θ : ℂ) / (a : ℂ)) * (((x : ℝ) + a : ℝ) : ℂ)))
        = Complex.exp (-(Complex.I * ((θ : ℂ) / (a : ℂ)) * (x : ℂ))) *
          Complex.exp (-((θ : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add, hxa]
      congr 1
      field_simp
      ring
    rw [key, hshift x, ← hθ]
    have hcancel : Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    calc Complex.exp (-(Complex.I * ((θ : ℂ) / (a : ℂ)) * (x : ℂ))) *
            Complex.exp (-((θ : ℂ) * Complex.I)) * (Complex.exp ((θ : ℂ) * Complex.I) * ψ x)
        = Complex.exp (-(Complex.I * ((θ : ℂ) / (a : ℂ)) * (x : ℂ))) *
          (Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I)) * ψ x := by
          ring
      _ = _ := by rw [hcancel]; ring
  · intro x
    simp only
    rw [← mul_assoc, ← Complex.exp_add]
    push_cast
    rw [show Complex.I * ((θ : ℂ) / (a : ℂ)) * (x : ℂ) + -(Complex.I * ((θ : ℂ) / (a : ℂ)) * (x : ℂ))
        = 0 by ring]
    simp

/-- Translating a solution of the stationary Schrödinger equation
`-ψ'' + V ψ = E ψ` by a period `a` of the potential yields again a solution
for the same energy `E`. -/
theorem schrodinger_translate (a E : ℝ) (V ψ ψ' ψ'' : ℝ → ℂ)
    (hV : ∀ x : ℝ, V (x + a) = V x)
    (h1 : ∀ x : ℝ, HasDerivAt ψ (ψ' x) x)
    (h2 : ∀ x : ℝ, HasDerivAt ψ' (ψ'' x) x)
    (heq : ∀ x : ℝ, -ψ'' x + V x * ψ x = (E : ℂ) * ψ x) :
    (∀ x : ℝ, HasDerivAt (fun y : ℝ => ψ (y + a)) (ψ' (x + a)) x) ∧
      (∀ x : ℝ, HasDerivAt (fun y : ℝ => ψ' (y + a)) (ψ'' (x + a)) x) ∧
      (∀ x : ℝ, -ψ'' (x + a) + V x * ψ (x + a) = (E : ℂ) * ψ (x + a)) := by
  refine ⟨fun x => HasDerivAt.comp_add_const x a (h1 (x + a)),
    fun x => HasDerivAt.comp_add_const x a (h2 (x + a)), fun x => ?_⟩
  have := heq (x + a)
  rwa [hV x] at this

/-- **Bloch's theorem for a periodic Hamiltonian.**  Let `V` be a potential of period `a ≠ 0`
and let `ψ` be an eigenstate of `H = -d²/dx² + V` with energy `E`.  Assume the energy level
is non-degenerate (every solution of the same eigenvalue equation is a scalar multiple of
`ψ`) and that the resulting translation eigenvalue is unimodular (as it must be for a
non-vanishing bounded state).  Then `ψ` is a Bloch wave `ψ(x) = e^{i k x} u(x)` with `u`
periodic of period `a`. -/
theorem bloch_theorem_of_periodic_hamiltonian (a E : ℝ) (ha : a ≠ 0) (V ψ ψ' ψ'' : ℝ → ℂ)
    (hV : ∀ x : ℝ, V (x + a) = V x)
    (h1 : ∀ x : ℝ, HasDerivAt ψ (ψ' x) x)
    (h2 : ∀ x : ℝ, HasDerivAt ψ' (ψ'' x) x)
    (heq : ∀ x : ℝ, -ψ'' x + V x * ψ x = (E : ℂ) * ψ x)
    (hnondeg : ∀ f f' f'' : ℝ → ℂ,
      (∀ x : ℝ, HasDerivAt f (f' x) x) → (∀ x : ℝ, HasDerivAt f' (f'' x) x) →
      (∀ x : ℝ, -f'' x + V x * f x = (E : ℂ) * f x) → ∃ c : ℂ, ∀ x : ℝ, f x = c * ψ x)
    (hunit : ∀ c : ℂ, (∀ x : ℝ, ψ (x + a) = c * ψ x) → ‖c‖ = 1) :
    ∃ (k : ℝ) (u : ℝ → ℂ),
      (∀ x : ℝ, u (x + a) = u x) ∧ (∀ x : ℝ, ψ x = Complex.exp (Complex.I * k * x) * u x) := by
  obtain ⟨d1, d2, deq⟩ := schrodinger_translate a E V ψ ψ' ψ'' hV h1 h2 heq
  obtain ⟨c, hc⟩ := hnondeg (fun y => ψ (y + a)) (fun y => ψ' (y + a)) (fun y => ψ'' (y + a))
    d1 d2 deq
  exact bloch_theorem a ha ψ c (hunit c hc) hc

end Phys

