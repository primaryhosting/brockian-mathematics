import RequestProject.QueryProg
import RequestProject.Aux

/-!
# An oracle `A` with `P^A = NP^A`

The oracle answers questions about its own relativized nondeterministic
computations.  This is well defined because the query `encodeQ i x t` is *longer*
than any string that can be queried during a computation of cost at most `t` on
input `x`, so the definition can be made by recursion on the length of the query.
-/

namespace CS

open Prog

/-- `AAux n z` is the value of the oracle at `z`, where `n` is the length of `z`;
the recursive calls are only made at strictly shorter strings. -/

theorem exec_guessProg_sound (O : Oracle) (x cert : Str) {cfg : Cfg} {n : ℕ} {qs : List Str}
    (h : Exec O guessProg (initCfg x cert) cfg n qs) (hacc : cfg.regs 1 = [true]) :
    ∃ w : Str, w.length = x.length ∧ O w := by
  obtain ⟨c1, _, _, _, _, h1, hr1, _, _⟩ := h.seq_inv
  obtain ⟨rfl, _, _⟩ := h1.clear_inv
  obtain ⟨c2, _, _, _, _, h2, hr2, _, _⟩ := hr1.seq_inv
  obtain ⟨rfl, _, _⟩ := h2.appendReg_inv
  obtain ⟨c3, _, _, _, _, h3, hr3, _, _⟩ := hr2.seq_inv
  obtain ⟨rfl, _, _⟩ := h3.clear_inv
  obtain ⟨c4, _, _, _, _, hloop, hquery, _, _⟩ := hr3.seq_inv
  set rr : Regs := Function.update
      (Function.update (Function.update (initCfg x cert).regs 3 [])
        3 ((Function.update (initCfg x cert).regs 3 []) 3 ++
           (Function.update (initCfg x cert).regs 3 []) 0)) 2 [] with hrr
  have h33 : rr 3 = x := by simp [hrr, initCfg, Function.update_apply]
  obtain ⟨_, w, hwlen, hw2, hwo⟩ := guessLoop_inv O x rr cert c4 _ _ h33 hloop
  have hc32 : rr 2 = [] := by simp [hrr, initCfg, Function.update_apply]
  have hc31 : rr 1 = [] := by simp [hrr, initCfg, Function.update_apply]
  have hc42 : c4.regs 2 = w := by rw [hw2, hc32]; simp
  have hc41 : c4.regs 1 = [] := by rw [hwo 1 (by decide) (by decide), hc31]
  obtain ⟨b, rfl, hb, _⟩ := hquery.query_inv
  refine ⟨w, hwlen, ?_⟩
  have hbtrue : b = true := by
    by_contra hbf
    have : b = false := by cases b <;> simp_all
    subst this
    simp [Function.update_apply, hc41] at hacc
  subst hbtrue
  have := hb.1 rfl
  rwa [hc42] at this

end CS

import RequestProject.Model

/-!
# Auxiliary facts

A counting lemma (there are `2 ^ n` strings of length `n`) and an enumeration of
all programs.
-/

namespace CS

/-- If a list of strings is shorter than `2 ^ n`, some string of length `n` is
missing from it. -/
