import Mathlib

/-!
# Szemeredi Regularity
Category: Frontier Abel
Target: Frontier.szemeredi_regularity
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

namespace Frontier

open Finset

/-- The density of edges of `G` between two finsets of vertices `s` and `t`:
the number of pairs `(a, b) ∈ s × t` with `a` adjacent to `b`, divided by `#s * #t`. -/

lemma isUniform_iff_isRegularPair (ε : ℝ) (s t : Finset α) :
    G.IsUniform ε s t ↔ IsRegularPair G ε s t := by
  constructor
  · intro h s' hs' t' ht' hs ht
    have := h hs' ht' (by rwa [mul_comm]) (by rwa [mul_comm])
    rw [density_eq_edgeDensity, density_eq_edgeDensity]
    simpa using this
  · intro h s' hs' t' ht' hs ht
    have := h s' hs' t' ht' (by rwa [mul_comm]) (by rwa [mul_comm])
    rw [density_eq_edgeDensity, density_eq_edgeDensity] at this
    simpa using this

end aux

/-- **Szemerédi's Regularity Lemma**.

For every `ε > 0` and every `l`, there is a bound `M` (depending only on `ε` and `l`, not on the
graph) such that every finite graph `G` on at least `l` vertices admits a partition of its vertex
set into between `l` and `M` nonempty parts, which is an equipartition (any two parts differ in
size by at most one), and for which the number of ordered pairs of distinct parts that fail to be
`ε`-regular is at most `ε` times the square of the number of parts. -/
