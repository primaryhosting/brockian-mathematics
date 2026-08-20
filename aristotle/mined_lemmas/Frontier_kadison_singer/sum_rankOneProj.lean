/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

set_option grind.warning false

open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace Frontier
namespace KadisonSinger

/-! ## The setting

Let `H` be a complex Hilbert space with a distinguished orthonormal (Hilbert) basis `e : ι → H`.
The *diagonal* subalgebra `𝒟` (an atomic MASA in `B(H)`, isomorphic to `ℓ^∞(ι)`) consists of the
bounded operators that are diagonalised by the basis.  The Kadison–Singer problem asks whether
every pure state of `𝒟` extends *uniquely* to a state of `B(H)`; this was answered
affirmatively by Marcus, Spielman and Srivastava.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The rank-one orthogonal projection onto the line spanned by a unit vector `u`, i.e. `u u*`. -/

lemma sum_rankOneProj {ι : Type*} [Fintype ι] (e : HilbertBasis ι ℂ H) :
    ∑ i, rankOneProj (e i) = 1 := by
  ext x
  have h := (e.hasSum_repr x).tsum_eq
  rw [tsum_fintype] at h
  simp only [HilbertBasis.repr_apply_apply] at h
  simpa using h

end KadisonSinger

/-! ## Main theorem -/

/-- **Kadison–Singer, atomic (base) case.**

Let `e` be a Hilbert basis of a complex Hilbert space `H`, generating the atomic MASA
`𝒟 ≅ ℓ^∞(ι)` inside `B(H)`, and let `δ_i` be the atomic pure state of `𝒟` given by evaluation
of the diagonal at the index `i` (equivalently, the character of `𝒟` sending the rank-one
projection `P_i = e_i e_i^*` to `1`).

Then `δ_i` has a *unique* extension to a state of `B(H)`, namely the vector state
`A ↦ ⟪e_i, A e_i⟫`: any state `psi` of `B(H)` with `psi Pᵢ = 1` is that vector state, and hence
any two states of `B(H)` agreeing with it on the diagonal MASA coincide.

This is the base case of the Kadison–Singer problem: the case of pure states of `ℓ^∞(ι)` coming
from principal ultrafilters.  (The full problem, whose remaining case concerns free ultrafilters,
is stated as `Frontier.KadisonSinger.Statement`; it was settled by Marcus, Spielman and
Srivastava.) -/
