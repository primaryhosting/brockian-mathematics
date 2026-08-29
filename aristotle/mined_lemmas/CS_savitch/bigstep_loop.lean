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

theorem bigstep_loop (N : NMachine Γ) (x : List Γ) (s a₀ k : ℕ)
    (ih : ∀ (a b tg : ℕ) (S : List Frame), ∃ (t : ℕ) (v : Bool),
      iter N x t ⟨s, a₀, tg, .eval a b k, S⟩ = ⟨s, a₀, tg, .ret v, S⟩ ∧
        (v = true ↔ Reach s (N.stepRel x) k a b)) :
    ∀ (j a b tg m : ℕ) (S : List Frame), m < 2 ^ s → 2 ^ s - m ≤ j →
      ∃ (t : ℕ) (v : Bool),
        iter N x t ⟨s, a₀, tg, .eval a m k, ⟨a, b, k, m, false⟩ :: S⟩ =
            ⟨s, a₀, tg, .ret v, S⟩ ∧
          (v = true ↔ ∃ m', m ≤ m' ∧ m' < 2 ^ s ∧
              Reach s (N.stepRel x) k a m' ∧ Reach s (N.stepRel x) k m' b) := by
  intro j
  induction j with
  | zero => intro a b tg m S hm hj; omega
  | succ j ihj =>
    intro a b tg m S hm hj
    obtain ⟨t1, v1, ht1, hv1⟩ := ih a m tg (⟨a, b, k, m, false⟩ :: S)
    by_cases hR1 : Reach s (N.stepRel x) k a m
    · -- the first half succeeded; go on to the second half
      have hv1t : v1 = true := hv1.mpr hR1
      subst hv1t
      have e2 : iter N x (t1 + 1) ⟨s, a₀, tg, .eval a m k, ⟨a, b, k, m, false⟩ :: S⟩ =
          ⟨s, a₀, tg, .eval m b k, ⟨a, b, k, m, true⟩ :: S⟩ := by
        rw [iter_succ_of N x ht1, stepx_ret_cons]; simp
      obtain ⟨t2, v2, ht2, hv2⟩ := ih m b tg (⟨a, b, k, m, true⟩ :: S)
      have e3 : iter N x (t1 + 1 + t2) ⟨s, a₀, tg, .eval a m k, ⟨a, b, k, m, false⟩ :: S⟩ =
          ⟨s, a₀, tg, .ret v2, ⟨a, b, k, m, true⟩ :: S⟩ := iter_trans N x e2 ht2
      by_cases hR2 : Reach s (N.stepRel x) k m b
      · have hv2t : v2 = true := hv2.mpr hR2
        subst hv2t
        refine ⟨t1 + 1 + t2 + 1, true, ?_, ?_⟩
        · rw [iter_succ_of N x e3, stepx_ret_cons]; simp
        · simp only [true_iff]
          exact ⟨m, le_rfl, hm, hR1, hR2⟩
      · have hv2f : v2 = false := by
          by_contra hcon
          exact hR2 (hv2.mp (by simpa using hcon))
        subst hv2f
        by_cases hnext : m + 1 < 2 ^ s
        · have e4 : iter N x (t1 + 1 + t2 + 1)
              ⟨s, a₀, tg, .eval a m k, ⟨a, b, k, m, false⟩ :: S⟩ =
              ⟨s, a₀, tg, .eval a (m + 1) k, ⟨a, b, k, m + 1, false⟩ :: S⟩ := by
            rw [iter_succ_of N x e3, stepx_ret_cons]; simp [hnext]
          obtain ⟨t3, v3, ht3, hv3⟩ := ihj a b tg (m + 1) S hnext (by omega)
          refine ⟨t1 + 1 + t2 + 1 + t3, v3, iter_trans N x e4 ht3, ?_⟩
          rw [hv3]
          constructor
          · rintro ⟨m', hm1, hm2, hm3, hm4⟩; exact ⟨m', by omega, hm2, hm3, hm4⟩
          · rintro ⟨m', hm1, hm2, hm3, hm4⟩
            rcases eq_or_lt_of_le hm1 with h | h
            · exact absurd (h ▸ hm4) hR2
            · exact ⟨m', by omega, hm2, hm3, hm4⟩
        · refine ⟨t1 + 1 + t2 + 1, false, ?_, ?_⟩
          · rw [iter_succ_of N x e3, stepx_ret_cons]; simp [hnext]
          · simp only [Bool.false_eq_true, false_iff]
            rintro ⟨m', hm1, hm2, hm3, hm4⟩
            have : m' = m := by omega
            exact absurd (this ▸ hm4) hR2
    · -- the first half failed; move to the next midpoint
      have hv1f : v1 = false := by
        by_contra hcon
        exact hR1 (hv1.mp (by simpa using hcon))
      subst hv1f
      by_cases hnext : m + 1 < 2 ^ s
      · have e2 : iter N x (t1 + 1) ⟨s, a₀, tg, .eval a m k, ⟨a, b, k, m, false⟩ :: S⟩ =
            ⟨s, a₀, tg, .eval a (m + 1) k, ⟨a, b, k, m + 1, false⟩ :: S⟩ := by
          rw [iter_succ_of N x ht1, stepx_ret_cons]; simp [hnext]
        obtain ⟨t3, v3, ht3, hv3⟩ := ihj a b tg (m + 1) S hnext (by omega)
        refine ⟨t1 + 1 + t3, v3, iter_trans N x e2 ht3, ?_⟩
        rw [hv3]
        constructor
        · rintro ⟨m', hm1, hm2, hm3, hm4⟩; exact ⟨m', by omega, hm2, hm3, hm4⟩
        · rintro ⟨m', hm1, hm2, hm3, hm4⟩
          rcases eq_or_lt_of_le hm1 with h | h
          · exact absurd (h ▸ hm3) hR1
          · exact ⟨m', by omega, hm2, hm3, hm4⟩
      · refine ⟨t1 + 1, false, ?_, ?_⟩
        · rw [iter_succ_of N x ht1, stepx_ret_cons]; simp [hnext]
        · simp only [Bool.false_eq_true, false_iff]
          rintro ⟨m', hm1, hm2, hm3, hm4⟩
          have : m' = m := by omega
          exact absurd (this ▸ hm3) hR1

/-- Big-step correctness of the recursive evaluation: from a state asking for
`Reach s edge k a b`, the simulator returns the right boolean, leaving the stack intact. -/
