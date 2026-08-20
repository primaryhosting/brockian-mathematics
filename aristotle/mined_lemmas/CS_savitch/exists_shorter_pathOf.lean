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


theorem exists_shorter_pathOf {u v : V} {l a b : ℕ} {p : ℕ → V}
    (hp0 : p 0 = u) (hpl : p l = v) (hstep : ∀ j < l, E (p j) (p (j + 1)))
    (hab : a < b) (hbl : b ≤ l) (heq : p a = p b) : ∃ l' < l, PathOf E l' u v := by
  refine ⟨l - (b - a), by omega, fun j => if j ≤ a then p j else p (j + (b - a)), ?_, ?_, ?_⟩
  · simp [hp0]
  · show (if l - (b - a) ≤ a then p (l - (b - a)) else p (l - (b - a) + (b - a))) = v
    rcases Nat.eq_or_lt_of_le (show a ≤ l - (b - a) by omega) with hcase | hcase
    · rw [if_pos (by omega), ← hcase, heq]
      have hb : b = l := by omega
      rw [hb, hpl]
    · rw [if_neg (by omega)]
      have h3 : l - (b - a) + (b - a) = l := by omega
      rw [h3, hpl]
  · intro j hj
    show E (if j ≤ a then p j else p (j + (b - a)))
      (if j + 1 ≤ a then p (j + 1) else p (j + 1 + (b - a)))
    rcases Nat.lt_or_ge j a with h1 | h1
    · rw [if_pos (by omega), if_pos (by omega)]
      exact hstep j (by omega)
    rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · -- j = a : we jump from `p a = p b` to `p (b+1)`
      rw [if_pos (by omega), if_neg (by omega)]
      have hpj : p j = p b := by rw [← h2]; exact heq
      have hbj : j + 1 + (b - a) = b + 1 := by omega
      rw [hpj, hbj]
      exact hstep b (by omega)
    · rw [if_neg (by omega), if_neg (by omega)]
      have h4 : j + 1 + (b - a) = (j + (b - a)) + 1 := by omega
      rw [h4]
      exact hstep (j + (b - a)) (by omega)

/-- In a finite vertex set, reachability is witnessed by a walk of length at most
`card V`. -/
