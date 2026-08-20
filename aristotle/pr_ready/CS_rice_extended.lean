/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Statement: The set of indices of a nontrivial semantic property is not recursive (Rice).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

open Nat.Partrec Nat.Partrec.Code

namespace CS

/-- **Rice's theorem** (extended / general form).

Let `C` be an arbitrary *semantic* property of partial functions, i.e. a set
`C : Set (ℕ →. ℕ)` of partial functions (so membership depends only on the
function computed by a program, never on the program text).  Assume `C` is
*nontrivial* for the class of partial recursive functions: some code `c₁` computes
a function in `C`, and some code `c₀` computes a function not in `C`.

Then the index set `{c | eval c ∈ C}` is not recursive (not decidable). -/
theorem rice_extended (C : Set (ℕ →. ℕ)) (c₁ c₀ : Code)
    (h₁ : eval c₁ ∈ C) (h₀ : eval c₀ ∉ C) :
    ¬ ComputablePred (fun c : Code => eval c ∈ C) := by
  rintro ⟨inst, hcomp⟩
  -- The "diagonal" program transformer: swap membership.
  have hf : Computable fun c : Code => if eval c ∈ C then c₀ else c₁ := by
    have := Computable.cond (c := fun c : Code => decide (eval c ∈ C))
      hcomp (Computable.const c₀) (Computable.const c₁)
    refine this.of_eq fun c => ?_
    by_cases h : eval c ∈ C <;> simp [h]
  obtain ⟨c, hc⟩ := fixed_point hf
  by_cases h : eval c ∈ C
  · rw [if_pos h] at hc
    exact h₀ (hc ▸ h)
  · rw [if_neg h] at hc
    exact h (hc ▸ h₁)

/-- The index set of a nontrivial semantic property, viewed as a set of natural
number indices, is not recursive. -/
theorem rice_extended_nat (C : Set (ℕ →. ℕ)) (c₁ c₀ : Code)
    (h₁ : eval c₁ ∈ C) (h₀ : eval c₀ ∉ C) :
    ¬ ComputablePred (fun n : ℕ => eval (Denumerable.ofNat Code n) ∈ C) := by
  intro h
  refine rice_extended C c₁ c₀ h₁ h₀ ?_
  have := ComputablePred.computable_iff.1 h
  obtain ⟨g, hg, hgc⟩ := this
  refine ComputablePred.computable_iff.2 ⟨fun c => g (Encodable.encode c), hg.comp
    (Computable.encode), ?_⟩
  funext c
  simpa using congrFun hgc (Encodable.encode c)

end CS

