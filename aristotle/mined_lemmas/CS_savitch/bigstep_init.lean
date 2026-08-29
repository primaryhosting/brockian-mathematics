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

theorem bigstep_init (N : NMachine Γ) (x : List Γ) (s a₀ : ℕ) :
    ∀ (j tg : ℕ), 2 ^ s - tg ≤ j →
      ∃ (t : ℕ) (v : Bool) (tg' : ℕ),
        iter N x t ⟨s, a₀, tg, .init, []⟩ = ⟨s, a₀, tg', .halt v, []⟩ ∧
          (v = true ↔ ∃ c, tg ≤ c ∧ c < 2 ^ s ∧ N.accept c ∧
            Reach s (N.stepRel x) s a₀ c) := by
  intro j
  induction j with
  | zero =>
      intro tg hj
      have htg : ¬ tg < 2 ^ s := by omega
      refine ⟨1, false, tg, ?_, ?_⟩
      · rw [iter_one, stepx_init, if_neg htg]
      · simp only [Bool.false_eq_true, false_iff]
        rintro ⟨c, hc1, hc2, -, -⟩
        omega
  | succ j ihj =>
      intro tg hj
      by_cases htg : tg < 2 ^ s
      · by_cases hacc : N.accept tg
        · have e1 : iter N x 1 ⟨s, a₀, tg, .init, []⟩ =
              ⟨s, a₀, tg, .eval a₀ tg s, []⟩ := by
            rw [iter_one, stepx_init, if_pos htg, if_pos hacc]
          obtain ⟨t1, v1, ht1, hv1⟩ := bigstep_eval N x s a₀ s a₀ tg tg []
          have e2 : iter N x (1 + t1) ⟨s, a₀, tg, .init, []⟩ =
              ⟨s, a₀, tg, .ret v1, []⟩ := iter_trans N x e1 ht1
          by_cases hR : Reach s (N.stepRel x) s a₀ tg
          · have hv1t : v1 = true := hv1.mpr hR
            subst hv1t
            refine ⟨1 + t1 + 1, true, tg, ?_, ?_⟩
            · rw [iter_succ_of N x e2, stepx_ret_nil]; simp
            · simp only [true_iff]
              exact ⟨tg, le_rfl, htg, hacc, hR⟩
          · have hv1f : v1 = false := by
              by_contra hcon
              exact hR (hv1.mp (by simpa using hcon))
            subst hv1f
            have e3 : iter N x (1 + t1 + 1) ⟨s, a₀, tg, .init, []⟩ =
                ⟨s, a₀, tg + 1, .init, []⟩ := by
              rw [iter_succ_of N x e2, stepx_ret_nil]; simp
            obtain ⟨t2, v2, tg', ht2, hv2⟩ := ihj (tg + 1) (by omega)
            refine ⟨1 + t1 + 1 + t2, v2, tg', iter_trans N x e3 ht2, ?_⟩
            rw [hv2]
            constructor
            · rintro ⟨c, hc1, hc2, hc3, hc4⟩; exact ⟨c, by omega, hc2, hc3, hc4⟩
            · rintro ⟨c, hc1, hc2, hc3, hc4⟩
              rcases eq_or_lt_of_le hc1 with h | h
              · exact absurd (h ▸ hc4) hR
              · exact ⟨c, by omega, hc2, hc3, hc4⟩
        · have e1 : iter N x 1 ⟨s, a₀, tg, .init, []⟩ = ⟨s, a₀, tg + 1, .init, []⟩ := by
            rw [iter_one, stepx_init, if_pos htg, if_neg hacc]
          obtain ⟨t2, v2, tg', ht2, hv2⟩ := ihj (tg + 1) (by omega)
          refine ⟨1 + t2, v2, tg', iter_trans N x e1 ht2, ?_⟩
          rw [hv2]
          constructor
          · rintro ⟨c, hc1, hc2, hc3, hc4⟩; exact ⟨c, by omega, hc2, hc3, hc4⟩
          · rintro ⟨c, hc1, hc2, hc3, hc4⟩
            rcases eq_or_lt_of_le hc1 with h | h
            · exact absurd (h ▸ hc3) hacc
            · exact ⟨c, by omega, hc2, hc3, hc4⟩
      · refine ⟨1, false, tg, ?_, ?_⟩
        · rw [iter_one, stepx_init, if_neg htg]
        · simp only [Bool.false_eq_true, false_iff]
          rintro ⟨c, hc1, hc2, -, -⟩
          omega

/-- The simulator, started in its initial state, halts with the verdict "some accepting
configuration below `2 ^ s` is `Reach`-able from `a₀`". -/
