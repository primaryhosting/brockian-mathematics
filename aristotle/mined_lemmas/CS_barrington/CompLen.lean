/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Barrington's theorem

We formalise Barrington's theorem: the class of Boolean function families computed by
logarithmic-depth fan-in-two Boolean circuits (`NC¹`) coincides with the class of families
computed by polynomial-length width-`5` permutation branching programs.

* `CS.Barrington.Circuit` : fan-in two Boolean circuits over `{¬, ∧, ∨}` and constants.
* `CS.Barrington.Instr`, `CS.Barrington.run` : width-5 permutation branching programs,
  i.e. lists of instructions, each of which multiplies the running value in `S₅` by a
  permutation depending on (at most) one input bit.
* `CS.Barrington.NC1` and `CS.Barrington.W5BP` : the two classes.
* `CS.barrington` : the two classes are equal.
-/

namespace CS
namespace Barrington

open Equiv

/-- The symmetric group on five points. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-! ### Boolean circuits -/

/-- Fan-in two Boolean circuits (formulas) on `n` inputs. -/
inductive Circuit (n : ℕ) where
  | var : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n

/-- The Boolean function computed by a circuit. -/

lemma CompLen.commutator {n : ℕ} {f g : (Fin n → Bool) → Bool} {A B : Perm5} {N M : ℕ}
    (h₁ : CompLen f A N) (h₂ : CompLen g B M)
    (h₃ : CompLen f A⁻¹ N) (h₄ : CompLen g B⁻¹ M) :
    CompLen (fun x => f x && g x) (A * B * A⁻¹ * B⁻¹) (N + M + N + M) := by
  obtain ⟨P₁, hP₁, l₁⟩ := h₁
  obtain ⟨P₂, hP₂, l₂⟩ := h₂
  obtain ⟨P₃, hP₃, l₃⟩ := h₃
  obtain ⟨P₄, hP₄, l₄⟩ := h₄
  refine ⟨P₁ ++ P₂ ++ P₃ ++ P₄, fun x => ?_, ?_⟩
  · simp only [run_append, hP₁ x, hP₂ x, hP₃ x, hP₄ x]
    by_cases hf : f x <;> by_cases hg : g x <;> simp [hf, hg]
  · simp only [List.length_append]
    omega

/-- **Barrington's construction**: a circuit of depth `d` is simulated by a width-5
permutation branching program of length at most `4 ^ d`, computing the given conjugate
of the 5-cycle `c5`. -/
