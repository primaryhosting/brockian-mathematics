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

theorem kadison_singer_reduction :
    KadisonSinger.Statement ↔ KadisonSinger.StatementNonatomic := by
  constructor
  · intro h H _ _ _ e psi hs hp _
    exact h H ‹_› ‹_› ‹_› e psi hs hp
  · intro h H _ _ _ e psi hs hp
    by_cases hatom : ∃ i, psi (KadisonSinger.rankOneProj (e i)) = 1
    · obtain ⟨i, hi⟩ := hatom
      exact (kadison_singer e i psi hs hi).2
    · refine h H ‹_› ‹_› ‹_› e psi hs hp fun i => ?_
      rcases KadisonSinger.apply_rankOneProj_eq_zero_or_one hp i with h0 | h1
      · exact h0
      · exact absurd ⟨i, h1⟩ hatom

/-- **Kadison–Singer in finite dimensions.**

When the index set of the Hilbert basis is finite (so that `H` is finite-dimensional and the
diagonal MASA is `ℂ^n`), every pure state of the diagonal MASA extends uniquely to a state of
`B(H)`: every pure state of the diagonal is atomic, and `Frontier.kadison_singer` applies. -/
