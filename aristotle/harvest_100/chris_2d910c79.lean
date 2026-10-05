import Mathlib

/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat.Partrec Nat.Partrec.Code

namespace CS

/-- **Rice's theorem.**  Let `P` be any property of partial functions `ℕ →. ℕ`
(a *semantic* property: it depends only on the function computed, not on the
program).  If `P` is nontrivial, i.e. it holds of some computable partial
function and fails for some computable partial function, then the set of
indices (codes) of programs whose semantics satisfy `P` is not recursive.

The proof is the standard one via Kleene's recursion (fixed point) theorem. -/
theorem rice_extended {P : (ℕ →. ℕ) → Prop}
    (h₀ : ∃ c : Code, P c.eval) (h₁ : ∃ c : Code, ¬ P c.eval) :
    ¬ ComputablePred (fun c : Code => P c.eval) := by
  rintro ⟨D, hc⟩
  obtain ⟨c₀, hc₀⟩ := h₀
  obtain ⟨c₁, hc₁⟩ := h₁
  -- `f c` diagonalises: it returns a program violating `P c.eval`.
  have hf : Computable (fun c : Code => bif (decide (P c.eval)) then c₁ else c₀) :=
    hc.cond (Computable.const _) (Computable.const _)
  obtain ⟨c, hcc⟩ := Code.fixed_point hf
  by_cases h : P c.eval
  · simp only [h, decide_true, cond_true] at hcc
    exact hc₁ (hcc ▸ h)
  · simp only [h, decide_false, cond_false] at hcc
    exact h (hcc ▸ hc₀)

/-- Rice's theorem for a set of codes: if `A` is a set of programs that is
*semantic* (membership depends only on the partial function computed) and
nontrivial (neither empty nor everything), then `A` is not recursive. -/
theorem rice_extended_set {A : Set Code}
    (hsem : ∀ c d : Code, c.eval = d.eval → c ∈ A → d ∈ A)
    (h₀ : ∃ c : Code, c ∈ A) (h₁ : ∃ c : Code, c ∉ A) :
    ¬ ComputablePred (fun c : Code => c ∈ A) := by
  set P : (ℕ →. ℕ) → Prop := fun f => ∃ c : Code, c ∈ A ∧ c.eval = f with hP
  have key : ∀ c : Code, P c.eval ↔ c ∈ A := by
    intro c
    constructor
    · rintro ⟨d, hd, hde⟩
      exact hsem d c hde hd
    · intro hc
      exact ⟨c, hc, rfl⟩
  have h₀' : ∃ c : Code, P c.eval := by
    obtain ⟨c, hc⟩ := h₀; exact ⟨c, (key c).2 hc⟩
  have h₁' : ∃ c : Code, ¬ P c.eval := by
    obtain ⟨c, hc⟩ := h₁; exact ⟨c, fun h => hc ((key c).1 h)⟩
  intro hcomp
  refine rice_extended h₀' h₁' ?_
  have : (fun c : Code => P c.eval) = (fun c : Code => c ∈ A) := by
    funext c; exact propext (key c)
  rw [this]
  exact hcomp

/-- Rice's theorem phrased for the index set of natural numbers: the set of
natural-number indices `n` of programs whose semantics satisfy a nontrivial
property `P` is not recursive. -/
theorem rice_extended_nat {P : (ℕ →. ℕ) → Prop}
    (h₀ : ∃ c : Code, P c.eval) (h₁ : ∃ c : Code, ¬ P c.eval) :
    ¬ ComputablePred (fun n : ℕ => P (Denumerable.ofNat Code n).eval) := by
  intro hcomp
  refine rice_extended h₀ h₁ ?_
  have hcode : Computable (fun c : Code => (Encodable.encode c)) := Computable.encode
  have := ComputablePred.computable_iff.1 hcomp
  obtain ⟨f, hf, hfe⟩ := this
  refine ComputablePred.computable_iff.2 ⟨fun c => f (Encodable.encode c), hf.comp hcode, ?_⟩
  funext c
  simpa using congrFun hfe (Encodable.encode c)

end CS

