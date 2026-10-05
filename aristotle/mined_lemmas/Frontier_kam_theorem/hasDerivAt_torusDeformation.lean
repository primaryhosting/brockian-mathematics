import Mathlib
/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

variable {n : ℕ}

/-- The Euclidean pairing `⟨c, x⟩ = ∑ⱼ cⱼ xⱼ` on `Fin n → ℝ`. -/

lemma hasDerivAt_torusDeformation {ω : Fin n → ℝ} {γ τ : ℝ} (hγ : 0 < γ)
    (hω : Diophantine ω γ τ) (ε : ℝ) (s : Finset (Fin n → ℤ)) (hs : (0 : Fin n → ℤ) ∉ s)
    (a : (Fin n → ℤ) → ℝ) (θ₀ : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => torusDeformation ω ε s a (fun i => θ₀ i + u * ω i) j)
      (2 * Real.pi * ε *
        ∑ k ∈ s, a k * (k j : ℝ) *
          Real.sin (2 * Real.pi * dotZR k (fun i => θ₀ i + t * ω i))) t := by
  have key : ∀ k ∈ s, HasDerivAt
      (fun u : ℝ => -ε * (a k * (k j : ℝ) *
          Real.cos (2 * Real.pi * dotZR k (fun i => θ₀ i + u * ω i)) / dotZR k ω))
      (2 * Real.pi * ε * (a k * (k j : ℝ) *
          Real.sin (2 * Real.pi * dotZR k (fun i => θ₀ i + t * ω i)))) t := by
    intro k hk
    have hk0 : k ≠ 0 := fun h => hs (h ▸ hk)
    have hd : dotZR k ω ≠ 0 := dotZR_ne_zero hγ hω hk0
    have hinner : HasDerivAt
        (fun u : ℝ => 2 * Real.pi * (dotZR k θ₀ + u * dotZR k ω))
        (2 * Real.pi * dotZR k ω) t := by
      have h1 : HasDerivAt (fun u : ℝ => dotZR k θ₀ + u * dotZR k ω) (dotZR k ω) t := by
        simpa using ((hasDerivAt_id t).mul_const (dotZR k ω)).const_add (dotZR k θ₀)
      simpa [mul_assoc] using h1.const_mul (2 * Real.pi)
    have hcos := hinner.cos
    have hfun : (fun u : ℝ => -ε * (a k * (k j : ℝ) *
          Real.cos (2 * Real.pi * dotZR k (fun i => θ₀ i + u * ω i)) / dotZR k ω))
        = fun u : ℝ => (-ε * a k * (k j : ℝ) / dotZR k ω) *
          Real.cos (2 * Real.pi * (dotZR k θ₀ + u * dotZR k ω)) := by
      funext u
      rw [dotZR_linear]
      field_simp
    rw [hfun]
    have hd2 := hcos.const_mul (-ε * a k * (k j : ℝ) / dotZR k ω)
    convert hd2 using 1
    rw [dotZR_linear]
    field_simp
  have hsum := HasDerivAt.sum key
  have hfun2 : (fun u : ℝ => torusDeformation ω ε s a (fun i => θ₀ i + u * ω i) j)
      = ∑ k ∈ s, (fun u : ℝ => -ε * (a k * (k j : ℝ) *
          Real.cos (2 * Real.pi * dotZR k (fun i => θ₀ i + u * ω i)) / dotZR k ω)) := by
    funext u
    simp only [torusDeformation, Finset.sum_apply, Finset.mul_sum]
  rw [hfun2, Finset.mul_sum]
  exact hsum

/-! ### The main theorem -/

/--
**KAM theorem (exactly solvable case).**

For a Hamiltonian `H(I, x) = ⟨ω, I⟩ + ε f(x)` in action–angle variables, with `ω` a
Diophantine frequency vector and `f` a zero-mean trigonometric polynomial perturbation of
the angles, the unperturbed invariant torus `{I = I₀}` persists for *every* value of the
perturbation parameter `ε`: it is deformed into the graph `I = I₀ + W(x)`, where the
deformation `W` is obtained by solving the cohomological (homological) equation, the small
divisors `⟨k, ω⟩` being controlled by the Diophantine condition.

The conclusions are:
1. the explicit curve `t ↦ (I₀ + W(x₀ + tω), x₀ + tω)` solves Hamilton's equations for the
   perturbed Hamiltonian;
2. the orbit stays on the deformed torus `𝒯 = {(I, x) | I = I₀ + W x}`, i.e. `𝒯` is invariant;
3. `W` is `ℤⁿ`-periodic, so `𝒯` really is an embedded `n`-torus in action–angle space;
4. the deformed torus is `O(ε/γ)`-close to the unperturbed one, quantitatively;
5. the induced motion on the torus is the quasi-periodic linear flow with the *unperturbed*
   frequency vector `ω`.
-/
