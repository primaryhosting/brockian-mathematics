/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Savitch.Model
import RequestProject.Savitch.Reach
import RequestProject.Savitch.Interp
import RequestProject.Savitch.BigStep
import RequestProject.Savitch.Invariant
import RequestProject.Savitch.Encode

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

`NSPACE(f) ⊆ DSPACE(f²)`, and consequently `PSPACE = NPSPACE` (Savitch's theorem).

The model of computation is the standard configuration-graph model, set up in
`RequestProject.Savitch.Model`: configurations are natural numbers (binary strings), a machine
runs in space `f` on input `x` if all configurations reachable on `x` are `< 2 ^ f |x|`, and
one step may depend on the current configuration together with the single input symbol scanned
by the input head, whose position is determined by the configuration.  The initial
configuration may depend on the input length (the usual assumption that the space bound is
constructible).  No computability assumption is imposed on the transition functions.

The deterministic simulator is built explicitly: it performs the depth-first evaluation of
Savitch's divide-and-conquer recursion, its states are recursion stacks of depth at most `s`,
each frame holding boundedly many numbers `< 2 ^ s`, and the whole state is encoded as a
natural number `< 2 ^ (42 * (s + 1) ^ 2)`.  Hence a nondeterministic machine running in space
`f` is simulated deterministically in space `42 * (f + 1) ^ 2`.
-/

namespace CS

open Classical

variable {Γ : Type}

/-! ### Deterministic machines are nondeterministic machines -/

/-- A deterministic machine, viewed as a nondeterministic one. -/

theorem good_nums_lt {st : St} (h : Good st) :
    ∀ a ∈ stNums st, a < 2 ^ st.s + st.s + 4 := by
  obtain ⟨ha₀, hrest⟩ := h
  intro a ha
  simp only [stNums, List.mem_cons, List.mem_append] at ha
  have hstack : ∀ fr ∈ st.stack, fr.k < st.s ∧ fr.a < 2 ^ st.s ∧ fr.b < 2 ^ st.s ∧
      fr.m < 2 ^ st.s := by
    revert hrest
    cases hc : st.ctrl with
    | init => intro h; rw [h.1]; simp
    | eval a b k => intro h; exact GoodStack_mem k st.stack h.2.2.2
    | ret v => intro h; obtain ⟨-, k, hk⟩ := h; exact GoodStack_mem k st.stack hk
    | halt v => intro h; rw [h.1]; simp
  have htarget : st.target ≤ 2 ^ st.s := by
    revert hrest
    cases hc : st.ctrl with
    | init => intro h; exact h.2
    | eval a b k => intro h; exact le_of_lt h.2.2.1
    | ret v => intro h; exact le_of_lt h.1
    | halt v => intro h; exact h.2
  have hctrl : ∀ a ∈ ctrlNums st.ctrl, a < 2 ^ st.s + st.s + 4 := by
    revert hrest
    cases hc : st.ctrl with
    | init => intro h a ha; simp only [ctrlNums, List.mem_cons, List.not_mem_nil] at ha
              rcases ha with rfl | rfl | rfl | rfl | h' <;> first | positivity | exact h'.elim
    | eval a' b' k =>
        intro h a ha
        have hlen : k ≤ st.s := by
          have := GoodStack_length k st.stack h.2.2.2
          omega
        simp only [ctrlNums, List.mem_cons, List.not_mem_nil] at ha
        rcases ha with rfl | rfl | rfl | rfl | h' 
        · have : (0:ℕ) < 2 ^ st.s := Nat.two_pow_pos _
          omega
        · have := h.1; omega
        · have := h.2.1; omega
        · omega
        · exact h'.elim
    | ret v =>
        intro h a ha
        simp only [ctrlNums, List.mem_cons, List.not_mem_nil] at ha
        have : (0:ℕ) < 2 ^ st.s := Nat.two_pow_pos _
        rcases ha with rfl | rfl | rfl | rfl | h'
        · omega
        · split <;> omega
        · omega
        · omega
        · exact h'.elim
    | halt v =>
        intro h a ha
        simp only [ctrlNums, List.mem_cons, List.not_mem_nil] at ha
        have : (0:ℕ) < 2 ^ st.s := Nat.two_pow_pos _
        rcases ha with rfl | rfl | rfl | rfl | h'
        · omega
        · split <;> omega
        · omega
        · omega
        · exact h'.elim
  rcases ha with rfl | rfl | ha | ha
  · omega
  · omega
  · exact hctrl a ha
  · obtain ⟨fr, hfr, hmem⟩ := List.mem_flatMap.mp ha
    obtain ⟨h1, h2, h3, h4⟩ := hstack fr hfr
    simp only [frameNums, List.mem_cons, List.not_mem_nil] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | h'
    · omega
    · omega
    · omega
    · omega
    · split <;> omega
    · exact h'.elim

