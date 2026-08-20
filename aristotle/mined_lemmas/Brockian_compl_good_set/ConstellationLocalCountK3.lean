/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

For a finite set of integer shifts `H = {h₁, …, h_k}` (a *constellation pattern*) and a
modulus `p`, the *local count* is the number of residue classes `a` mod `p` such that all
the shifted values `a + hᵢ` are nonzero mod `p`; this is the local factor appearing in the
Hardy–Littlewood singular series for prime constellations.

The general formula `localCount p H = p - #(H mod p)` is proved as `Brockian.localCount_eq`
(via `Finset.card_compl`, `Finset.card_image_of_injective` and `neg_injective`), and the
main result specialises it to `k = 3`.
-/

namespace Brockian

open Finset

/-- The local count of an integer constellation `H = {h₁, …, h_k}` at the modulus `p`:
the number of residues `a` modulo `p` for which none of the shifted values `a + hᵢ`
vanishes modulo `p`. -/

theorem ConstellationLocalCountK3 (p : ℕ) [NeZero p] (h₁ h₂ h₃ : ℤ)
    (h12 : ¬ h₁ ≡ h₂ [ZMOD (p : ℤ)]) (h13 : ¬ h₁ ≡ h₃ [ZMOD (p : ℤ)])
    (h23 : ¬ h₂ ≡ h₃ [ZMOD (p : ℤ)]) :
    localCount p {h₁, h₂, h₃} = p - 3 := by
  rw [localCount_eq, card_image_triple p h₁ h₂ h₃ h12 h13 h23]

/-- A concrete instance, confirming the hypotheses of `ConstellationLocalCountK3` are
satisfiable: the pattern `{0, 2, 6}` leaves exactly `5 - 3 = 2` admissible residues mod `5`. -/
example : localCount 5 {0, 2, 6} = 5 - 3 :=
  ConstellationLocalCountK3 5 0 2 6 (by decide) (by decide) (by decide)

end Brockian

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

