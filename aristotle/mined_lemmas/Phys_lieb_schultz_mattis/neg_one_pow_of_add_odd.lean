/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede every command, including module doc comments,
-- so the header above is written as a plain block comment and repeated below.)
import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

/-!
## The algebraic core of the Lieb–Schultz–Mattis argument

If a Hamiltonian commutes with two symmetries that *anticommute* with each other, then
every energy level is (at least) two-fold degenerate.  This is the finite-volume mechanism
behind the Lieb–Schultz–Mattis theorem: on a half-integer-spin chain of odd length the two
π-rotations about the `x`- and `z`-axes anticommute, so no energy level — in particular no
ground level — can be a simple eigenvalue.
-/

/-- **Degeneracy from anticommuting symmetries.**
Let `A` be an operator on a finite-dimensional complex vector space, and let `S`, `K` be two
operators commuting with `A` such that `S` is an involution, `K` is injective and `S`, `K`
anticommute.  Then every eigenvalue of `A` has an eigenspace of dimension at least `2`. -/

lemma neg_one_pow_of_add_odd {a b L : ℕ} (h : a + b = L) (hL : Odd L) :
    (-1 : ℂ) ^ a = -((-1 : ℂ) ^ b) := by
  have h1 : (-1 : ℂ) ^ a * (-1 : ℂ) ^ b = -1 := by
    rw [← pow_add, h, hL.neg_one_pow]
  have h2 : (-1 : ℂ) ^ b * (-1 : ℂ) ^ b = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc (-1 : ℂ) ^ a = (-1 : ℂ) ^ a * ((-1 : ℂ) ^ b * (-1 : ℂ) ^ b) := by rw [h2]; ring
    _ = ((-1 : ℂ) ^ a * (-1 : ℂ) ^ b) * (-1 : ℂ) ^ b := by ring
    _ = -1 * (-1 : ℂ) ^ b := by rw [h1]
    _ = -((-1 : ℂ) ^ b) := by ring

/-- On a chain of **odd** length the two π-rotations `∏ᵢ σᶻᵢ` and `∏ᵢ σˣᵢ` anticommute.
This is exactly the half-integer-spin obstruction underlying Lieb–Schultz–Mattis. -/
