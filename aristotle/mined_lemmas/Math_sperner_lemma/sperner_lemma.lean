import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Auxiliary counting lemmas -/

/-- Parity translated into `ZMod 2`. -/

theorem sperner_lemma : Odd (spernerRainbow carrier T c Finset.univ).card :=
  spernerRainbow_card_odd carrier T c hdown hT0 hpm hc n Finset.univ (by simp)

end Sperner

/-! ## Non-vacuity: the hypotheses of `sperner_lemma` are satisfiable

Two instances are provided: the trivial (unsubdivided) triangulation of the `n`-simplex in
every dimension, and a genuinely subdivided one-dimensional triangulation, in which the
`2` branch of the pseudomanifold condition really occurs. -/

namespace TrivialTriangulation

variable (n : ℕ)

/-- The vertices of the unsubdivided `n`-simplex, each carried by its own vertex face. -/
