import Mathlib

/-!
# Further Diophantine functions: binomial coefficients and factorials

Mathlib's `Mathlib/NumberTheory/Dioph.lean` develops the basic theory of Diophantine sets and
functions and culminates in Matiyasevich's theorem that exponentiation is Diophantine
(`Dioph.pow_dioph`).  Two further classical steps on the way to the MRDP theorem are formalized
here, both unconditionally:

* `CS.choose_dioph`: the binomial coefficient `(n, k) ↦ n.choose k` is a Diophantine function.
  This follows from `Dioph.pow_dioph` because `n.choose k` is the `k`-th digit of `(u + 1) ^ n`
  in base `u := 2 ^ n + 1`, and division and remainder are Diophantine.
* `CS.factorial_dioph`: the factorial `r ↦ r !` is a Diophantine function.  This follows from
  `CS.choose_dioph` because `r ! = u ^ r / u.choose r` as soon as `u` is large enough compared
  to `r`, and `u := (2 * r) ^ (r + 2) + 2 * r + 1` is large enough.
-/

set_option autoImplicit false

namespace CS

open Finset Nat

/-! ## Digits in base `u` -/

/-- A number with all digits `< u` and at most `k` digits is `< u ^ k`. -/

theorem isPoly_computable {γ A : Type} [Primcodable A] (φ : A → γ → ℕ)
    (hφ : ∀ i, Computable fun x => φ x i) {f : (γ → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ g h : A → ℕ, Computable g ∧ Computable h ∧ ∀ x, f (φ x) = (g x : ℤ) - (h x : ℤ) := by
  induction hf with
  | proj i => exact ⟨fun x => φ x i, fun _ => 0, hφ i, Computable.const 0, fun x => by simp⟩
  | const n =>
      exact ⟨fun _ => n.toNat, fun _ => (-n).toNat, Computable.const _, Computable.const _,
        fun x => by dsimp only; omega⟩
  | sub _ _ ih₁ ih₂ =>
      obtain ⟨g₁, h₁, hg₁, hh₁, e₁⟩ := ih₁
      obtain ⟨g₂, h₂, hg₂, hh₂, e₂⟩ := ih₂
      refine ⟨fun x => g₁ x + h₂ x, fun x => h₁ x + g₂ x,
        (Primrec₂.to_comp Primrec.nat_add).comp hg₁ hh₂,
        (Primrec₂.to_comp Primrec.nat_add).comp hh₁ hg₂, fun x => ?_⟩
      dsimp only
      rw [e₁, e₂]; push_cast; ring
  | mul _ _ ih₁ ih₂ =>
      obtain ⟨g₁, h₁, hg₁, hh₁, e₁⟩ := ih₁
      obtain ⟨g₂, h₂, hg₂, hh₂, e₂⟩ := ih₂
      refine ⟨fun x => g₁ x * g₂ x + h₁ x * h₂ x, fun x => g₁ x * h₂ x + h₁ x * g₂ x,
        (Primrec₂.to_comp Primrec.nat_add).comp
          ((Primrec₂.to_comp Primrec.nat_mul).comp hg₁ hg₂)
          ((Primrec₂.to_comp Primrec.nat_mul).comp hh₁ hh₂),
        (Primrec₂.to_comp Primrec.nat_add).comp
          ((Primrec₂.to_comp Primrec.nat_mul).comp hg₁ hh₂)
          ((Primrec₂.to_comp Primrec.nat_mul).comp hh₁ hg₂), fun x => ?_⟩
      dsimp only
      rw [e₁, e₂]; push_cast; ring

/-- A predicate of the form `∃ L : List ℕ, g (a, L) = h (a, L)` with `g`, `h` computable is
recursively enumerable. -/
