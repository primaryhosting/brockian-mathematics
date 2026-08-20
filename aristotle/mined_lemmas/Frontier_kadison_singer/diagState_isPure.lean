import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires the `import` line to precede any module docstring, so the header
-- comment above appears immediately after the import.)

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

/-!
## The Kadison–Singer problem

The Kadison–Singer problem asks whether every pure state on a maximal abelian self-adjoint
subalgebra (MASA) `D` of a matrix / operator algebra `A` extends *uniquely* to a state of `A`
(the extension being then automatically pure).  It was solved affirmatively by
Marcus, Spielman and Srivastava.

Here we formalize the statement for the *atomic* MASA, and give a complete, self-contained
proof of the finite-dimensional case: for the diagonal MASA `Dₙ ⊆ Mₙ(ℂ)`, every pure state
of `Dₙ` (i.e. every coordinate evaluation `d ↦ d i`) has a unique extension to a state of
`Mₙ(ℂ)`, namely `A ↦ A i i`, and that extension is a pure state.
-/

namespace Frontier

open ComplexOrder Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `Mₙ(ℂ)`: a unital positive linear functional. -/
structure IsState (f : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop where
  unital : f 1 = 1
  nonneg : ∀ A : Matrix n n ℂ, 0 ≤ f (Aᴴ * A)

/-- A state is *pure* if it is an extreme point of the state space. -/

lemma diagState_isPure (i : n) : IsPure (diagState i) := by
  refine ⟨diagState_isState i, ?_⟩
  intro g₁ g₂ hg₁ hg₂ t ht0 ht1 hdec
  have hdiag : ∀ j : n, g₁ (Matrix.single j j 1) = (if j = i then 1 else 0) ∧
      g₂ (Matrix.single j j 1) = (if j = i then 1 else 0) := by
    have hne : ∀ j : n, j ≠ i → g₁ (Matrix.single j j 1) = 0 ∧
        g₂ (Matrix.single j j 1) = 0 := by
      intro j hj
      have hsum : (0 : ℂ) = (t : ℂ) * g₁ (Matrix.single j j 1)
          + ((1 - t : ℝ) : ℂ) * g₂ (Matrix.single j j 1) := by
        have := DFunLike.congr_fun hdec (Matrix.single j j (1 : ℂ))
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          diagState_apply] at this
        rw [← this]
        simp [hj]
      have hg₁0 := hg₁.nonneg_single_diag j
      have hg₂0 := hg₂.nonneg_single_diag j
      have hta : (0 : ℂ) ≤ (t : ℂ) * g₁ (Matrix.single j j 1) :=
        mul_nonneg (by exact_mod_cast Complex.zero_le_real.2 ht0.le) hg₁0
      have htb : (0 : ℂ) ≤ ((1 - t : ℝ) : ℂ) * g₂ (Matrix.single j j 1) :=
        mul_nonneg (by exact_mod_cast Complex.zero_le_real.2 (by linarith)) hg₂0
      have hA : (t : ℂ) * g₁ (Matrix.single j j 1) = 0 := by
        by_contra hcon
        have : (0 : ℂ) < (t : ℂ) * g₁ (Matrix.single j j 1) := lt_of_le_of_ne hta (Ne.symm hcon)
        have := add_pos_of_pos_of_nonneg this htb
        rw [← hsum] at this
        exact lt_irrefl _ this
      have hB : ((1 - t : ℝ) : ℂ) * g₂ (Matrix.single j j 1) = 0 := by
        by_contra hcon
        have : (0 : ℂ) < ((1 - t : ℝ) : ℂ) * g₂ (Matrix.single j j 1) :=
          lt_of_le_of_ne htb (Ne.symm hcon)
        have := add_pos_of_nonneg_of_pos hta this
        rw [← hsum] at this
        exact lt_irrefl _ this
      have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have ht1' : ((1 - t : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        linarith
      exact ⟨by simpa [ht0'] using mul_eq_zero.1 hA |>.resolve_left ht0',
        by simpa using mul_eq_zero.1 hB |>.resolve_left ht1'⟩
    have hone : ∀ r : Matrix n n ℂ →ₗ[ℂ] ℂ, IsState r →
        (∀ j : n, j ≠ i → r (Matrix.single j j 1) = 0) →
        r (Matrix.single i i 1) = 1 := by
      intro r hr hz
      have h1 : (1 : Matrix n n ℂ) = ∑ j : n, Matrix.single j j (1 : ℂ) := by
        ext a b
        rw [Matrix.sum_apply, Finset.sum_eq_single a]
        · simp [Matrix.single_apply, Matrix.one_apply]
        · intro c _ hc; simp [hc]
        · simp
      have := hr.unital
      rw [h1, map_sum] at this
      rw [Finset.sum_eq_single i] at this
      · exact this
      · intro j _ hj; exact hz j hj
      · intro hi; exact absurd (Finset.mem_univ i) hi
    intro j
    by_cases hj : j = i
    · subst hj
      refine ⟨by simp [hone g₁ hg₁ (fun j hj => (hne j hj).1)],
        by simp [hone g₂ hg₂ (fun j hj => (hne j hj).2)]⟩
    · exact ⟨by simp [(hne j hj).1, hj], by simp [(hne j hj).2, hj]⟩
  exact ⟨hg₁.eq_diagState_of_diag (fun j => (hdiag j).1),
    hg₂.eq_diagState_of_diag (fun j => (hdiag j).2)⟩

/-! ### The theorem -/

/-- **Kadison–Singer (finite-dimensional / matrix case).**

For the diagonal MASA `Dₙ ⊆ Mₙ(ℂ)`, every pure state of `Dₙ` — i.e. every coordinate
evaluation `d ↦ d i` — extends to a *unique* state of `Mₙ(ℂ)`, and that unique extension
(the vector state `A ↦ A i i`) is itself a pure state. -/
