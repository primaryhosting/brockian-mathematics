import Mathlib
/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-! ## The abstract mechanism: an anomalous (projective) commutation relation
forces every energy level to be degenerate. -/

/-- **Anomaly ⇒ degeneracy.**  If a Hamiltonian `H` commutes with two injective
symmetries `A` and `B` which fail to commute with each other by a phase `ω ≠ 1`
(`B ∘ A = ω • (A ∘ B)`), then no eigenvector of `H` spans its own eigenspace:
each eigenspace of `H` has dimension at least `2`. -/

lemma sgn_flip {n : ℕ} (s : Config n) :
    sgn (fun j => !(s j)) = (-1 : ℂ) ^ n * sgn s := by
  classical
  have hset : (Finset.univ.filter fun j => (!(s j)) = true)
      = (Finset.univ.filter fun j => ¬ (s j = true)) := by
    apply Finset.filter_congr
    intro j _
    simp
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun j => s j = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  unfold sgn
  rw [hset]
  exact neg_one_pow_compl _ _ _ hcard

/-- On a chain of odd length the two π-rotations anticommute. -/
