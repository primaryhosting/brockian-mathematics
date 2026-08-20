/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-! ## Boolean circuits (straight-line programs) -/

/-- A single gate of a straight-line Boolean program.  Arguments refer to positions in the
current environment (first the input bits, then the values of the previously computed gates).
Out-of-range references evaluate to `false`. -/
inductive Gate
  | const (b : Bool)
  | not (a : ℕ)
  | and (a b : ℕ)
  | or (a b : ℕ)
deriving DecidableEq

/-- A Boolean circuit is a straight-line program, i.e. a list of gates. -/
abbrev Circuit := List Gate

/-- Value of a single gate in a given environment. -/

lemma exists_hard_function (n s : ℕ)
    (h : (gateSet (n + s)).card ^ s * (s + 1) < 2 ^ 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, ∀ C : Circuit, C.length ≤ s →
      ∃ y : Fin n → Bool, C.eval (List.ofFn y) ≠ f y := by
  set N := n + s with hN
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- degenerate case: no inputs and no gates
    have hn : n = 0 := by omega
    have hs : s = 0 := by omega
    subst hn; subst hs
    refine ⟨fun _ => true, ?_⟩
    intro C hC
    have : C = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨fun i => i.elim0, by simp [Circuit.eval, evalAux]⟩
  · classical
    set G := {g : Gate // g ∈ gateSet N}
    set Φ : ((Fin s → G) × Fin (s + 1)) → ((Fin n → Bool) → Bool) :=
      fun t y => Circuit.eval ((List.ofFn (fun i => (t.1 i : Gate))).take (t.2 : ℕ))
        (List.ofFn y) with hΦ
    have hcardT : Fintype.card ((Fin s → G) × Fin (s + 1))
        = (gateSet N).card ^ s * (s + 1) := by
      simp [Fintype.card_prod, G]
    have hcardB : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ 2 ^ n := by
      simp
    have hnotsurj : ¬ Function.Surjective Φ := by
      intro hsurj
      have := Fintype.card_le_of_surjective Φ hsurj
      rw [hcardT, hcardB] at this
      omega
    simp only [Function.Surjective, not_forall] at hnotsurj
    obtain ⟨f, hf⟩ := hnotsurj
    refine ⟨f, ?_⟩
    intro C hC
    by_contra hcon
    push_neg at hcon
    -- the clamped circuit
    set C' := C.map (Gate.clamp N) with hC'
    have hlen : C'.length = C.length := by simp [hC']
    have hmem : ∀ i, ∀ hi : i < C'.length, C'[i] ∈ gateSet N := by
      intro i hi
      have hi' : i < C.length := by simpa [hC'] using hi
      have heq : C'[i] = Gate.clamp N (C[i]'hi') := by simp [hC']
      rw [heq]
      exact clamp_mem_gateSet hNpos _
    set g : Fin s → G := fun i =>
      if hi : (i : ℕ) < C'.length then ⟨C'[(i : ℕ)], hmem _ hi⟩
      else ⟨Gate.const false, const_false_mem_gateSet N⟩ with hg
    have hlen' : C'.length ≤ s := by omega
    have htake : (List.ofFn (fun i => (g i : Gate))).take C'.length = C' := by
      apply List.ext_getElem
      · simp [hlen']
      · intro i h1 h2
        have hi : i < C'.length := by simpa [hlen'] using h1
        simp [List.getElem_take, hg, hi]
    have hΦt : Φ (g, ⟨C'.length, by omega⟩) = f := by
      funext y
      rw [hΦ]
      simp only [htake]
      have hev : Circuit.eval C' (List.ofFn y) = C.eval (List.ofFn y) :=
        Circuit.eval_clamp C (List.ofFn y) (by simp [hN]; omega)
      rw [hev, hcon y]
    exact hf ⟨_, hΦt⟩

/-! ### Existence of exponentially hard Boolean functions -/

/-- A list-valued version of Shannon's counting bound. -/
