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

/-
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Brockian
namespace GoldbachSchema

/-- The binary Goldbach property: `n` is a sum of two primes. -/

noncomputable def Model.ofGoldbachBeyond (B : ℕ)
    (h : ∀ n : ℕ, B ≤ n → Even n → Goldbach2 n) : Model where
  bound := B
  witness := fun n => if hb : B ≤ n then (if he : Even n then (h n hb he).choose else 0) else 0
  witness_le := by
    intro n hb he
    obtain ⟨q, _, _, hsum⟩ := (h n hb he).choose_spec
    simp only [dif_pos hb, dif_pos he]
    omega
  witness_prime := by
    intro n hb he
    obtain ⟨q, hp, _, _⟩ := (h n hb he).choose_spec
    simpa only [dif_pos hb, dif_pos he] using hp
  cowitness_prime := by
    intro n hb he
    obtain ⟨q, _, hq, hsum⟩ := (h n hb he).choose_spec
    simp only [dif_pos hb, dif_pos he]
    have : n - (h n hb he).choose = q := by omega
    rw [this]
    exact hq

/-- The named hypothesis of the schema: the *ternary descent* principle, stating that every odd
number `n ≥ 3` whose predecessor-by-three satisfies binary Goldbach is a sum of three primes. -/
