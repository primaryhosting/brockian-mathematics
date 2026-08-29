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

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open SimpleGraph Finset

/-- `Arrows N s t` says that every simple graph on at least `N` vertices contains
either a clique of size `s` or an independent set of size `t`
(i.e. `N → (s, t)` in the arrow notation for Ramsey numbers). -/

lemma arrows_step {m n s t : ℕ} (hpos : 0 < m + n)
    (hm : Arrows m s (t + 1)) (hn : Arrows n (s + 1) t) :
    Arrows (m + n) (s + 1) (t + 1) := by
  rintro V _ G hcard ⟨h1, h2⟩
  classical
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  set A : Finset V := univ.filter (fun x => G.Adj v x) with hAdef
  set B : Finset V := univ.filter (fun x => x ≠ v ∧ ¬ G.Adj v x) with hBdef
  have hsplit : A.card + B.card + 1 = Fintype.card V := by
    have h0 : A.card + (univ.filter (fun x => ¬ G.Adj v x)).card = Fintype.card V := by
      rw [hAdef]
      simpa using Finset.card_filter_add_card_filter_not
        (s := (univ : Finset V)) (p := fun x => G.Adj v x)
    have h1' : (univ.filter (fun x => ¬ G.Adj v x)) = insert v B := by
      ext x
      by_cases hx : x = v
      · subst hx; simp [hBdef]
      · simp [hBdef, hx]
    have h2' : v ∉ B := by simp [hBdef]
    rw [h1', Finset.card_insert_of_notMem h2'] at h0
    omega
  by_cases hA : m ≤ A.card
  · exact red_extend hm G v A (fun x hx => by simpa [hAdef] using hx) hA h1 h2
  · refine blue_extend hn G v B (fun x hx => by simpa [hBdef] using hx) (by omega) h1 h2

/-! ### `R(3,3) ≤ 6` -/

