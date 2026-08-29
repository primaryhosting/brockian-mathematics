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

lemma spinFlipX_injective (L : ℕ) : Function.Injective (spinFlipX L) := by
  intro ψ φ h
  have : (spinFlipX L) ((spinFlipX L) ψ) = (spinFlipX L) ((spinFlipX L) φ) := by rw [h]
  have hid := spinFlipX_involutive L
  have h1 : (spinFlipX L ∘ₗ spinFlipX L) ψ = (spinFlipX L ∘ₗ spinFlipX L) φ := this
  rw [hid] at h1
  simpa using h1

