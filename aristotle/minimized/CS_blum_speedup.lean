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

import RequestProject.Blum.Cost

/-!
# The Blum speedup construction

We build, by the recursion theorem, a code `blumCode` computing a two-parameter family of
functions `f i t` (`i` an index bound, `t` a patch threshold) with the following features.

At stage `x`, the function `f i 0` diagonalises against every program `j ≥ i` which is
*cheap at stage `x`*, meaning that `cost j x ≤ M j x + x` where `M j x` is the maximal cost of
the programs `curry blumCode ⟨j+1, t⟩` (`t ≤ x`) on input `x`.  Each program is diagonalised
against at the first stage at which it becomes cheap, so `f i 0` and `f 0 0` differ at only
finitely many arguments; the parameter `t` lets one patch those finitely many arguments,
so that `f (j+1) t = f 0 0` for a suitable `t`.
-/

set_option maxHeartbeats 1000000

namespace CS

open Nat.Partrec Nat.Partrec.Code Primrec

/-! ### Generic form of the construction, parameterised by a cost function -/

/-- Maximal cost, according to `cf`, of the auxiliary programs with parameters `(j+1, t)`,
`t ≤ y`, on input `y`. -/

noncomputable def cost (c : Code) (n : ℕ) : ℕ := sInf {k | (evaln k c n).isSome}

theorem cost_le {c : Code} {n k : ℕ} (h : (evaln k c n).isSome) : cost c n ≤ k :=
  Nat.sInf_le h

theorem halts_iff {c : Code} {n : ℕ} : (eval c n).Dom ↔ ∃ k, (evaln k c n).isSome := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := evaln_complete.1 (Part.get_mem h)
    exact ⟨k, by rw [Option.mem_def] at hk; simp [hk]⟩
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
    exact Part.dom_iff_mem.2 ⟨x, evaln_sound (by simpa using hx)⟩

theorem isSome_evaln_cost {c : Code} {n : ℕ} (h : (eval c n).Dom) :
    (evaln (cost c n) c n).isSome :=
  Nat.sInf_mem (halts_iff.1 h)

theorem evaln_const (m x k : ℕ) (hx : x < k) (hm : m < k) :
    evaln k (Code.const m) x = some m := by
  induction m with
  | zero =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [Code.const, evaln, Nat.lt_succ_iff.1 hx]
  | succ m ih =>
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hm' : m < k' + 1 := by omega
    simp [Code.const, evaln, Nat.lt_succ_iff.1 hx, ih hm', Nat.lt_succ_iff.1 hm']

theorem evaln_id {x k : ℕ} (hx : x < k) : evaln k Code.id x = some x := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [Code.id, evaln, Nat.lt_succ_iff.1 hx, Seq.seq]

theorem evaln_curry {e : Code} {a x k : ℕ} (hk : Nat.pair a x < k) :
    evaln k (curry e a) x = evaln k e (Nat.pair a x) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hx : x < k' + 1 := lt_of_le_of_lt (Nat.right_le_pair a x) hk
  have ha : a < k' + 1 := lt_of_le_of_lt (Nat.left_le_pair a x) hk
  simp [curry, evaln, Nat.lt_succ_iff.1 hx, evaln_const a x _ hx ha, evaln_id hx, Seq.seq]

theorem cost_curry_le {e : Code} {a x : ℕ} (h : (eval e (Nat.pair a x)).Dom) :
    cost (curry e a) x ≤ cost e (Nat.pair a x) := by
  have hs : (evaln (cost e (Nat.pair a x)) e (Nat.pair a x)).isSome := isSome_evaln_cost h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
  have hb : Nat.pair a x < cost e (Nat.pair a x) := evaln_bound (by simpa using hv)
  exact cost_le (by rw [evaln_curry hb]; simp [hv])

end CS
