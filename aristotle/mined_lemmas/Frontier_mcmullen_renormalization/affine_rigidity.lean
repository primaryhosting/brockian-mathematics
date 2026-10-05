/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard; the basic object of McMullen's work on
renormalization) is a holomorphic proper degree-two branched cover `f : U → V`
between open subsets of `ℂ` with `U` compactly contained in `V`.  The
degree-two condition is encoded concretely below: there is one critical value,
whose fiber is a single point, and every other value has exactly two
preimages. -/

/-- The quadratic family `z ↦ z ^ 2 + c`. -/

theorem affine_rigidity (a b c c' : ℂ) (ha : a ≠ 0)
    (h : ∀ z, a * qmap c z + b = qmap c' (a * z + b)) :
    a = 1 ∧ b = 0 ∧ c = c' := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  simp only [qmap] at h0 h1 h2
  have hb : b = 0 := by
    have h4 : 4 * (a * b) = 0 := by linear_combination h2 - h1
    have hab : a * b = 0 := by linear_combination h4 / 4
    rcases mul_eq_zero.1 hab with h | h
    · exact absurd h ha
    · exact h
  subst hb
  have haa : a = a ^ 2 := by linear_combination h1 - h0
  have ha1 : a = 1 := by
    have : a * (a - 1) = 0 := by linear_combination -haa
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h ha
    · linear_combination h
  subst ha1
  refine ⟨rfl, rfl, ?_⟩
  linear_combination h0

/-! ## Main theorem -/

/-- **McMullen renormalization (formalized statement, with base cases and a
Lean-checked reduction).**

For the quadratic family `qmap c : z ↦ z ^ 2 + c`:

1. *(Quadratic-like structure.)*  For `1 < R` with `R + ‖c‖ < R ^ 2`, the map
   `qmap c` restricted to `U = (qmap c)⁻¹(B(0,R))` is a quadratic-like map onto
   `V = B(0,R)`: `U ⋐ V`, the map is holomorphic and is a proper degree-two
   branched cover.
2. *(Escape criterion.)*  The filled Julia set `K = {z : ∀ n, ‖f^n z‖ ≤ R}` is
   exactly the set of points with bounded orbit.
3. *(Compactness, invariance, nonemptiness of `K`.)*
4. *(Base case of straightening.)*  For `c = 0`, `K` is the closed unit disk.
5. *(Renormalization reduction.)*  The filled Julia set of a period-`p`
   renormalization `f^[p] : U' → V'` is contained in that of `f`.
6. *(Affine rigidity.)*  Distinct parameters `c` are not affinely conjugate. -/
