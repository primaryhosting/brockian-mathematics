import Mathlib

/-!
# Further Diophantine functions: binomial coefficients and factorials

Mathlib's `Mathlib/NumberTheory/Dioph.lean` develops the basic theory of Diophantine sets and
functions and culminates in Matiyasevich's theorem that exponentiation is Diophantine
(`Dioph.pow_dioph`).  Two further classical steps on the way to the MRDP theorem are formalized
here, both unconditionally:

* `CS.choose_dioph`: the binomial coefficient `(n, k) ↦ n.choose k` is a Diophantine function.
  This follows from `Dioph.pow_dioph` because `n.choose k` is the `k`-th digit of `(u + 1) ^ n`
  in base `u := 2 ^ n + 1`, and division and remainder are Diophantine.
* `CS.factorial_dioph`: the factorial `r ↦ r !` is a Diophantine function.  This follows from
  `CS.choose_dioph` because `r ! = u ^ r / u.choose r` as soon as `u` is large enough compared
  to `r`, and `u := (2 * r) ^ (r + 2) + 2 * r + 1` is large enough.
-/

set_option autoImplicit false

namespace CS

open Finset Nat

/-! ## Digits in base `u` -/

/-- A number with all digits `< u` and at most `k` digits is `< u ^ k`. -/

theorem dioph_rePred {S : Set ℕ} (hS : Dioph {v : Fin 1 → ℕ | S (v 0)}) : REPred S := by
  classical
  obtain ⟨β, p, hp⟩ := hS
  obtain ⟨l, hl⟩ := isPoly_support p.isPoly
  set lb : List β := l.filterMap Sum.getRight? with hlbdef
  set assign : ℕ × List ℕ → (Fin 1 ⊕ β → ℕ) := fun x =>
    Sum.elim (fun _ => x.1)
      (fun b => if hb : ∃ i : Fin lb.length, lb.get i = b then x.2.getD (hb.choose : ℕ) 0 else 0)
    with hassign
  have hcoord : ∀ c : Fin 1 ⊕ β, Computable fun x => assign x c := by
    intro c
    cases c with
    | inl i => exact Computable.fst
    | inr b =>
        by_cases hb : ∃ i : Fin lb.length, lb.get i = b
        · simp only [hassign, Sum.elim_inr, dif_pos hb]
          exact (Primrec₂.to_comp (Primrec.list_getD 0)).comp Computable.snd (Computable.const _)
        · simp only [hassign, Sum.elim_inr, dif_neg hb]
          exact Computable.const 0
  obtain ⟨g, h, hg, hh, e⟩ := isPoly_computable assign hcoord p.isPoly
  refine rePred_of_exists_list g h hg hh fun a => ?_
  have key : S a ↔ ∃ L : List ℕ, p (assign (a, L)) = 0 := by
    have h1 : S a ↔ ∃ t : β → ℕ, p (Sum.elim (fun _ => a) t) = 0 := by
      have := hp (fun _ => a); simpa using this
    rw [h1]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨lb.map t, ?_⟩
      rw [← ht]
      refine hl _ _ fun c hc => ?_
      cases c with
      | inl i => simp [hassign]
      | inr b =>
          have hbmem : b ∈ lb := by
            rw [hlbdef, List.mem_filterMap]
            exact ⟨Sum.inr b, hc, rfl⟩
          have hb : ∃ i : Fin lb.length, lb.get i = b := List.mem_iff_get.1 hbmem
          simp only [hassign, Sum.elim_inr, dif_pos hb]
          have hlen : (hb.choose : ℕ) < (lb.map t).length := by simp
          rw [List.getD_eq_getElem _ _ hlen, List.getElem_map]
          congr 1
          simpa [List.get_eq_getElem] using hb.choose_spec
    · rintro ⟨L, hL⟩
      exact ⟨fun b => assign (a, L) (Sum.inr b), by
        rw [show Sum.elim (fun _ : Fin 1 => a) (fun b => assign (a, L) (Sum.inr b))
            = assign (a, L) from funext fun c => by cases c <;> simp [hassign]]
        exact hL⟩
  rw [key]
  exact exists_congr fun L => by rw [e (a, L)]; omega

/-- Assuming MRDP, the Diophantine subsets of `ℕ` are exactly the recursively enumerable ones. -/
