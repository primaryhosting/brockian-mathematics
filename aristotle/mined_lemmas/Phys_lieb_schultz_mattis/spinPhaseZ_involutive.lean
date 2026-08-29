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

lemma spinPhaseZ_involutive (L : ℕ) : spinPhaseZ L ∘ₗ spinPhaseZ L = LinearMap.id := by
  ext ψ s
  have : ((-1 : ℂ) ^ zWeight s) * ((-1 : ℂ) ^ zWeight s) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  simp only [LinearMap.coe_comp, Function.comp_apply, spinPhaseZ, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.id_coe, id_eq]
  rw [← mul_assoc, this, one_mul]

