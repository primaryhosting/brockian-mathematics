import Mathlib

/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- **Rice's theorem.** If a set `A` of indices (codes) of partial recursive functions is
*semantic* (extensional: membership depends only on the partial function computed by the code)
and *nontrivial* (some code belongs to `A` and some code does not), then `A` is not recursive,
i.e. membership in `A` is not a computable predicate. -/
theorem rice_extended {A : Set Code}
    (hext : ∀ c c' : Code, eval c = eval c' → (c ∈ A ↔ c' ∈ A))
    (ha : ∃ a : Code, a ∈ A) (hb : ∃ b : Code, b ∉ A) :
    ¬ ComputablePred (fun c : Code => c ∈ A) := by
  rintro ⟨inst, hcomp⟩
  obtain ⟨a, haA⟩ := ha
  obtain ⟨b, hbA⟩ := hb
  -- The "diagonal" map: send a code in `A` to `b`, and a code not in `A` to `a`.
  have hf : Computable fun c : Code => if c ∈ A then b else a := by
    have : Computable fun c : Code => cond (decide (c ∈ A)) b a :=
      Computable.cond hcomp (Computable.const b) (Computable.const a)
    simpa [Bool.cond_decide] using this
  obtain ⟨c, hc⟩ := fixed_point hf
  by_cases hcA : c ∈ A
  · rw [if_pos hcA] at hc
    exact hbA ((hext b c hc).mpr hcA)
  · rw [if_neg hcA] at hc
    exact hcA ((hext a c hc).mp haA)

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

