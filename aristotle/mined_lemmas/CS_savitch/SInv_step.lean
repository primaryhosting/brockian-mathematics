/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede every declaration, including module
docstrings, so the header above is a plain block comment.)
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Walk
import RequestProject.Savitch.Sim
import RequestProject.Savitch.Semantics
import RequestProject.Savitch.Space

/-!
The space-bounded machine model, the classes `CS.NSPACE`, `CS.DSPACE`,
`CS.PSPACE` and `CS.NPSPACE`, and the simulator used in the proof are defined in
the files `RequestProject/Savitch/*.lean`.

A machine reads its input through a head whose position is determined by its
memory value, and it works in space `g` if on inputs of length `n` all reachable
memory values lie in a set of at most `2 ^ g n` values depending only on `n`
(the standard correspondence between `s` tape cells and `2 ^ O(s)`
configurations).  The classes `NSPACE g` and `DSPACE g` are closed under
constant factors by definition, as usual for space classes.

Savitch's theorem is proved for space bounds `f` with `n + 1 ≤ 2 ^ f n`
(i.e. `f n ≥ log₂ (n+1)`), the standard hypothesis `f (n) ≥ log n`.
-/

namespace CS

/-- **Savitch's theorem**: a language recognized by a nondeterministic machine in
space `f` (with `f n ≥ log₂ (n + 1)`) is recognized by a deterministic machine in
space `O(f²)`, i.e. `NSPACE f ⊆ DSPACE (f²)`. -/

theorem SInv_step {x : List Bool} {n : ℕ} (hn : x.length = n) (m : SMem N.Mem)
    (h : SInv N S g n m) : SInv N S g n (dstep N S g x m) := by
  cases m with
  | scan i =>
    have hi : i ≤ n := h
    cases hx : x[i]? with
    | some c =>
      have hlt : i < x.length := by
        by_contra hc
        push_neg at hc
        rw [List.getElem?_eq_none hc] at hx
        simp at hx
      rw [dstep_scan_some (by rw [hx]; simp)]
      show i + 1 ≤ n
      omega
    | none =>
      have hge : x.length ≤ i := by
        by_contra hc
        push_neg at hc
        rw [List.getElem?_eq_getElem hc] at hx
        simp at hx
      have : i = n := by omega
      subst this
      rw [dstep_scan_none hx]
      exact ⟨rfl, List.suffix_rfl⟩
  | outer m todo =>
    obtain ⟨rfl, hsuf⟩ := h
    cases todo with
    | nil => rw [dstep_outer_nil]; exact ⟨rfl, hsuf⟩
    | cons b bs =>
      have hbs : bs <:+ cands N S m := (List.suffix_cons b bs).trans hsuf
      by_cases hb : N.acc b
      · rw [dstep_outer_cons_acc hb]
        exact ⟨rfl, hbs, Finset.mem_insert_self _ _,
          mem_Bset_of_suffix hsuf List.mem_cons_self, rfl⟩
      · rw [dstep_outer_cons_not_acc hb]
        exact ⟨rfl, hbs⟩
  | call m todo a b k st =>
    obtain ⟨rfl, hsuf, ha, hb, hst⟩ := h
    cases k with
    | zero =>
      rw [dstep_call_zero]
      exact ⟨rfl, hsuf, 0, hst⟩
    | succ k =>
      cases hc : cands N S m with
      | nil =>
        rw [dstep_call_succ_nil hc]
        exact ⟨rfl, hsuf, k + 1, hst⟩
      | cons m0 ms =>
        rw [dstep_call_succ_cons hc]
        have hm0 : m0 ∈ Bset N S m := mem_Bset_of_mem_cands (by rw [hc]; exact List.mem_cons_self)
        have hms : ms <:+ cands N S m := by
          rw [hc]; exact List.suffix_cons m0 ms
        exact ⟨rfl, hsuf, ha, hm0, rfl, ⟨ha, hb, hm0, hms⟩, hst⟩
  | ret m todo v st =>
    obtain ⟨rfl, hsuf, k, hst⟩ := h
    cases st with
    | nil =>
      cases v with
      | true => rw [dstep_ret_nil_true]; trivial
      | false => rw [dstep_ret_nil_false]; exact ⟨rfl, hsuf⟩
    | cons fr st' =>
      obtain ⟨hk, hok, hst'⟩ := hst
      cases v with
      | true =>
        cases hs : fr.second with
        | true =>
          rw [dstep_ret_true_second hs]
          exact ⟨rfl, hsuf, k + 1, hst'⟩
        | false =>
          rw [dstep_ret_true_first hs]
          refine ⟨rfl, hsuf, hok.2.2.1, hok.2.1, rfl, ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2⟩, ?_⟩
          rw [hk]
          exact hst'
      | false =>
        cases hr : fr.rest with
        | nil =>
          rw [dstep_ret_false_nil hr]
          exact ⟨rfl, hsuf, k + 1, hst'⟩
        | cons m0 ms =>
          rw [dstep_ret_false_cons hr]
          have hm0 : m0 ∈ Bset N S m :=
            mem_Bset_of_suffix hok.2.2.2 (by rw [hr]; exact List.mem_cons_self)
          have hms : ms <:+ cands N S m := (List.suffix_cons m0 ms).trans (by rw [← hr]; exact hok.2.2.2)
          refine ⟨rfl, hsuf, hok.1, hm0, rfl, ⟨hok.1, hok.2.1, hm0, hms⟩, ?_⟩
          rw [hk]
          exact hst'
  | acc => trivial

