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

def Gapless {L : ℕ} (A : Chain L →ₗ[ℂ] Chain L) (E₀ ε : ℝ) : Prop :=
  ∃ E : ℝ, E ≠ E₀ ∧ Module.End.HasEigenvalue A (E : ℂ) ∧ |E - E₀| < ε

/-- **Lieb–Schultz–Mattis.**
Consider a chain of `L` half-integer-spin (spin-1/2) sites with `L` odd, and a Hamiltonian `A`
that is translation invariant and invariant under the two π-rotations `∏ᵢ σˣᵢ`, `∏ᵢ σᶻᵢ`.
If `E₀` is a ground energy of `A` (a real eigenvalue, minimal among the real eigenvalues), then
for every `ε` the system is gapless at scale `ε` or its ground level is degenerate.

The proof establishes the second alternative: the two π-rotations anticommute on an odd-length
half-integer-spin chain, so every energy level of a symmetric Hamiltonian — in particular the
ground level — is at least two-fold degenerate.  (Consequently the translation-invariance
hypothesis `hTrans` and the minimality hypothesis `hmin`, which are part of the physical setting
requested, are not needed for the conclusion.) -/
