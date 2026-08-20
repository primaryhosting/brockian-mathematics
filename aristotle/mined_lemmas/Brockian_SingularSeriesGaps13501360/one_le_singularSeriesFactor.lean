import Mathlib

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

namespace Brockian

/-! # Admissible gap ranges and the Hardy–Littlewood singular series for prime pairs

For a gap `g` we consider the two–element pattern `{0, g}`.  Such a pattern is
*admissible* when, for every prime `p`, its residues do not cover all of `ZMod p`.
The Hardy–Littlewood singular series of the pattern `{0, g}` is
`𝔖(g) = 2 C₂ ∏_{p ∣ g, p odd} (p-1)/(p-2)` for even `g`, and `0` for odd `g`;
here we work with the arithmetic factor `∏_{p ∣ g, p odd} (p-1)/(p-2)` and with the
convention that the factor vanishes for odd `g` (matching the vanishing of `𝔖`).
-/

/-- A finite pattern `H ⊆ ℤ` is *admissible* if for every prime `p` some residue class
mod `p` is missed by `H`. -/

lemma one_le_singularSeriesFactor {g : ℕ} (hg : Even g) : 1 ≤ singularSeriesFactor g := by
  rw [singularSeriesFactor, if_pos hg]
  have key : ∀ p ∈ g.primeFactors.filter (fun p => p ≠ 2),
      (1 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := ?_
  · simpa using Finset.prod_le_prod (f := fun _ : ℕ => (1 : ℝ))
      (g := fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) - 2)) (fun i _ => zero_le_one) key
  intro p hp
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
  obtain ⟨⟨hpp, _, _⟩, hp2⟩ := hp
  have hp3 : 3 ≤ p := by
    have := hpp.two_le
    omega
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The singular series factor is positive exactly on the even gaps. -/
