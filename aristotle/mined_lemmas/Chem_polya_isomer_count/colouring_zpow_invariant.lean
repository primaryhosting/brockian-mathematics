/-
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean requires all module
-- docstrings to appear *after* the `import` lines; the text is otherwise verbatim.)
import Mathlib

/-!
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open MulAction

attribute [local instance] arrowAction

/-- If a colouring `f` of the skeleton positions is invariant under the symmetry `g`,
then it is invariant under every integer power of `g`. -/

private lemma colouring_zpow_invariant {G : Type*} {α : Type*} {β : Type*} [Group G]
    [MulAction G α] (g : G) (f : α → β) (hf : ∀ a, f (g • a) = f a) (n : ℤ) (a : α) :
    f (g ^ n • a) = f a := by
  have hinv : ∀ a : α, f (g⁻¹ • a) = f a := by
    intro a
    have h := hf (g⁻¹ • a)
    rw [smul_inv_smul] at h
    exact h.symm
  induction n using Int.induction_on generalizing a with
  | zero => simp
  | succ k ih =>
      have h1 : g ^ ((k : ℤ) + 1) • a = g ^ (k : ℤ) • (g • a) := by
        rw [zpow_add_one, mul_smul]
      rw [h1, ih, hf]
  | pred k ih =>
      have h1 : g ^ (-(k : ℤ) - 1) • a = g ^ (-(k : ℤ)) • (g⁻¹ • a) := by
        rw [zpow_sub_one, mul_smul]
      rw [h1, ih, hinv]

/-- Colourings fixed by a symmetry `g` are exactly the colourings that are constant on the
cycles (orbits of `⟨g⟩`) of `g`. -/
