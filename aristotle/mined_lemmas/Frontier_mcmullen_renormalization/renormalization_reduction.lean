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

theorem renormalization_reduction (f : ℂ → ℂ) (U U' : Set ℂ) (p : ℕ) (hp : 0 < p)
    (h : ∀ k < p, Set.MapsTo (f^[k]) U' U) :
    {z | ∀ n, (f^[p])^[n] z ∈ U'} ⊆ {z | ∀ n, f^[n] z ∈ U} := by
  intro z hz n
  have hkey : f^[n] z = f^[n % p] ((f^[p])^[n / p] z) := by
    rw [← Function.iterate_mul, ← Function.iterate_add_apply]
    congr 1
    exact (Nat.mod_add_div n p).symm
  rw [hkey]
  exact h (n % p) (Nat.mod_lt _ hp) (hz (n / p))

/-! ## Rigidity: distinct parameters are not affinely conjugate -/

/-- **Affine rigidity of the quadratic family.**  If an affine map
`z ↦ a * z + b` (with `a ≠ 0`) conjugates `z ↦ z ^ 2 + c` to `z ↦ z ^ 2 + c'`,
then the conjugacy is the identity and `c = c'`. -/
