/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace CS

/-! ### Basic probabilistic vocabulary

All probabilities are uniform probabilities over finite types, expressed as expectations
of `{0,1}`-valued indicator functions. -/

/-- The `{0,1}`-valued indicator of a boolean. -/

theorem nisan_wigderson_prg {n m ℓ d : ℕ} (hm : 0 < m)
    {S : Fin m → Fin n → Fin ℓ} (hSinj : ∀ i, Function.Injective (S i))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      (univ.filter fun k : Fin n => ∃ k', S j k' = S i k).card ≤ d)
    (f : (Fin n → Bool) → Bool) (D : (Fin m → Bool) → Bool) (eps : ℝ)
    (hard : ∀ t : ℕ, ∀ g : (Fin n → Bool) → Bool, IsNWPredictor d D t g →
      (pr fun z => g z == f z) < 1 / 2 + eps / m) :
    |(pr fun x => D (nwGen S f x)) - pr D| < eps := by
  rw [← hybProb_card S f D, ← hybProb_zero S f D]
  refine telescope_bound S f D eps hm ?_
  intro t ht
  obtain ⟨g, hg, hadv⟩ := exists_predictor hSinj hdesign f D ht
  have := hard t g hg
  linarith

end CS

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

