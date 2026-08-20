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

import Mathlib
import RequestProject.Savitch.Enc

/-!
# The Savitch simulator and its correctness

We build, from a nondeterministic machine `M` and a recursion depth `K`, a
deterministic machine `savitchDM M K` which decides, by Savitch's recursive midpoint
search, whether the sink vertex `none` of the configuration graph of `M` is reachable
from the start vertex within `2 ^ K` steps.  If `cV M ≤ 2 ^ K` this is exactly
acceptance by `M`.
-/

namespace CS
namespace Savitch

variable {Sigma : Type}


theorem trace_loop (i : ℕ)
    (hA : ∀ (u v : Vert M) (st : List (Frame M)), ∃ k, (rawNext M x)^[k] (Mode.call u v i, st)
      = (Mode.ret (toBool (reachIn (edgeX M x) i u v)), st)) :
    ∀ (d j : ℕ), cV M - j ≤ d → j < cV M → ∀ (u v : Vert M) (st : List (Frame M)),
      ∃ k, (rawNext M x)^[k] (Mode.call u (mid M j) i, (u, v, i, j, false) :: st)
        = (Mode.ret (toBool (∃ j', j ≤ j' ∧ j' < cV M ∧
            reachIn (edgeX M x) i u (mid M j') ∧ reachIn (edgeX M x) i (mid M j') v)), st) := by
  intro d
  induction d with
  | zero => intro j hd hj; omega
  | succ d ih =>
    intro j hd hj u v st
    -- the continuation which tries the next midpoint
    have hadv : ¬ (reachIn (edgeX M x) i u (mid M j) ∧ reachIn (edgeX M x) i (mid M j) v) →
        ∃ k, (rawNext M x)^[k] (advance M u v i j st)
          = (Mode.ret (toBool (∃ j', j ≤ j' ∧ j' < cV M ∧
              reachIn (edgeX M x) i u (mid M j') ∧ reachIn (edgeX M x) i (mid M j') v)), st) := by
      intro hfail
      unfold advance
      by_cases hnext : j + 1 < cV M
      · rw [if_pos hnext]
        obtain ⟨k, hk⟩ := ih (j + 1) (by omega) hnext u v st
        refine ⟨k, ?_⟩
        rw [hk]
        congr 1
        refine congrArg Mode.ret (toBool_congr ⟨?_, ?_⟩)
        · rintro ⟨j', hj1, hj2, hj3, hj4⟩
          exact ⟨j', by omega, hj2, hj3, hj4⟩
        · rintro ⟨j', hj1, hj2, hj3, hj4⟩
          rcases Nat.eq_or_lt_of_le hj1 with heq | hlt
          · subst heq
            exact absurd ⟨hj3, hj4⟩ hfail
          · exact ⟨j', by omega, hj2, hj3, hj4⟩
      · rw [if_neg hnext]
        refine ⟨0, ?_⟩
        simp only [Function.iterate_zero, id_eq]
        congr 1
        refine congrArg Mode.ret ?_
        symm
        rw [toBool_eq_false]
        rintro ⟨j', hj1, hj2, hj3, hj4⟩
        have : j' = j := by omega
        exact hfail (this ▸ ⟨hj3, hj4⟩)
    -- first recursive call: is `mid j` reachable from `u`?
    obtain ⟨k1, hk1⟩ := hA u (mid M j) ((u, v, i, j, false) :: st)
    by_cases h1 : reachIn (edgeX M x) i u (mid M j)
    · -- yes; now check the second half
      obtain ⟨k2, hk2⟩ := hA (mid M j) v ((u, v, i, j, true) :: st)
      by_cases h2 : reachIn (edgeX M x) i (mid M j) v
      · refine ⟨k1 + 1 + k2 + 1, ?_⟩
        refine iterate_trans M x (iterate_trans M x (iterate_trans M x hk1 ?_) hk2) ?_
        · rw [Function.iterate_one, rawNext_ret_cons]
          rw [if_neg (by simp), if_pos (by simp [h1])]
        · rw [Function.iterate_one, rawNext_ret_cons]
          rw [if_pos (by simp), if_pos (by simp [h2])]
          congr 1
          exact congrArg Mode.ret (by
            symm
            rw [toBool_eq_true]
            exact ⟨j, le_rfl, hj, h1, h2⟩)
      · obtain ⟨k3, hk3⟩ := hadv (by tauto)
        refine ⟨k1 + 1 + k2 + 1 + k3, ?_⟩
        refine iterate_trans M x (iterate_trans M x (iterate_trans M x
          (iterate_trans M x hk1 ?_) hk2) ?_) hk3
        · rw [Function.iterate_one, rawNext_ret_cons]
          rw [if_neg (by simp), if_pos (by simp [h1])]
        · rw [Function.iterate_one, rawNext_ret_cons]
          rw [if_pos (by simp), if_neg (by simp [h2])]
    · obtain ⟨k3, hk3⟩ := hadv (by tauto)
      refine ⟨k1 + 1 + k3, ?_⟩
      refine iterate_trans M x (iterate_trans M x hk1 ?_) hk3
      rw [Function.iterate_one, rawNext_ret_cons]
      rw [if_neg (by simp), if_neg (by simp [h1])]

/-- Correctness of the recursive procedure: a `call u v i` returns exactly whether `v`
is reachable from `u` within `2 ^ i` steps, leaving the stack unchanged. -/
