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


theorem encRaw_inj {M : NMachine Sigma} {K : ℕ} {s t : Raw M}
    (hs : WFraw M K s) (ht : WFraw M K t) (h : encRaw M K s = encRaw M K t) : s = t := by
  obtain ⟨m, st⟩ := s
  obtain ⟨m', st'⟩ := t
  have hm : encMode M K m = encMode M K m' := congrArg Prod.fst h
  have hst : (fun idx : Fin (K + 1) => (st[idx.val]?).map (encFrame M K))
      = (fun idx : Fin (K + 1) => (st'[idx.val]?).map (encFrame M K)) := congrArg Prod.snd h
  have hstacks : st = st' := by
    have hlen : st.length ≤ K := by
      cases m <;> exact WFstack.length_le (by first | exact hs.2 | exact hs)
    have hlen' : st'.length ≤ K := by
      cases m' <;> exact WFstack.length_le (by first | exact ht.2 | exact ht)
    have hwf : WFstack M K st := by cases m <;> first | exact hs.2 | exact hs
    have hwf' : WFstack M K st' := by cases m' <;> first | exact ht.2 | exact ht
    apply List.ext_getElem?
    intro n
    by_cases hn : n ≤ K
    · have := congrFun hst ⟨n, by omega⟩
      simp only at this
      rcases hx : st[n]? with _ | f <;> rcases hy : st'[n]? with _ | g <;>
        rw [hx, hy] at this
      · simp at this
      · simp at this
      · simp only [Option.map_some, Option.some.injEq] at this
        exact congrArg some (encFrame_inj (wfstack_mem_bounds hwf n f hx)
          (wfstack_mem_bounds hwf' n g hy) this)
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  subst hstacks
  have : m = m' := by
    cases m with
    | call u v i =>
      cases m' with
      | call u' v' i' =>
        simp only [encMode, Sum.inl.injEq, Prod.mk.injEq, Fin.mk.injEq] at hm
        obtain ⟨h1, h2, h3⟩ := hm
        have hi : i ≤ K := by have := hs.1; omega
        have hi' : i' ≤ K := by have := ht.1; omega
        have : i = i' := by omega
        simp_all
      | ret b => simp [encMode] at hm
      | done b => simp [encMode] at hm
    | ret b =>
      cases m' with
      | call u' v' i' => simp [encMode] at hm
      | ret b' => simpa [encMode] using hm
      | done b' => simp [encMode] at hm
    | done b =>
      cases m' with
      | call u' v' i' => simp [encMode] at hm
      | ret b' => simp [encMode] at hm
      | done b' => simpa [encMode] using hm
  rw [this]

/-- The (finite) state space of the Savitch simulator. -/
noncomputable instance instFintypeWF (M : NMachine Sigma) (K : ℕ) :
    Fintype {s : Raw M // WFraw M K s} :=
  Fintype.ofInjective (fun s => encRaw M K s.1)
    (fun s t h => Subtype.ext (encRaw_inj s.2 t.2 h))

