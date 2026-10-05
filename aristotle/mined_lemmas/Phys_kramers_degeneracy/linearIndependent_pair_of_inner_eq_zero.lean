/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A *time-reversal operator* on a complex inner product space `V`: an antiunitary
(antilinear, inner-product-conjugating) involution-up-to-sign with `Θ ∘ Θ = -1`,
which is the situation of a half-integer-spin system. -/
structure TimeReversal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- The underlying map. -/
  toFun : V → V
  /-- Additivity. -/
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- Antilinearity. -/
  map_smul' : ∀ (c : ℂ) (x : V), toFun (c • x) = (starRingEnd ℂ) c • toFun x
  /-- Antiunitarity: `⟪Θ x, Θ y⟫ = conj ⟪x, y⟫ = ⟪y, x⟫`. -/
  inner_map' : ∀ x y, ⟪toFun x, toFun y⟫_ℂ = ⟪y, x⟫_ℂ
  /-- Half-integer spin: `Θ² = -1`. -/
  sq_eq_neg' : ∀ x, toFun (toFun x) = -x

namespace TimeReversal

instance : CoeFun (TimeReversal V) (fun _ => V → V) := ⟨TimeReversal.toFun⟩

variable (Θ : TimeReversal V)


lemma linearIndependent_pair_of_inner_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ⟪x, y⟫_ℂ = 0) : LinearIndependent ℂ ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : ⟪x, s • x + t • y⟫_ℂ = 0 := by rw [hst]; simp
  have h2 : ⟪y, s • x + t • y⟫_ℂ = 0 := by rw [hst]; simp
  rw [inner_add_right, inner_smul_right, inner_smul_right, h] at h1
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    show ⟪y, x⟫_ℂ = 0 by rw [← inner_conj_symm, h]; simp] at h2
  simp only [mul_zero, add_zero, zero_add] at h1 h2
  have hx' : (⟪x, x⟫_ℂ) ≠ 0 := by simpa [inner_self_eq_zero] using hx
  have hy' : (⟪y, y⟫_ℂ) ≠ 0 := by simpa [inner_self_eq_zero] using hy
  exact ⟨by simpa [hx', hx] using h1, by simpa [hy', hy] using h2⟩

/--
**Kramers degeneracy.**  Let `H` be the Hamiltonian of a system with a time-reversal
symmetry `Θ` satisfying `Θ² = -1` (half-integer total spin), i.e. `Θ ∘ H = H ∘ Θ`.
Then every (real) energy level `E` of `H` is at least doubly degenerate: the eigenspace
of `H` for `E` has rank at least `2`.  Concretely, an eigenvector `ψ` and its time
reverse `Θ ψ` are nonzero, orthogonal, linearly independent eigenvectors for the same
energy.
-/
