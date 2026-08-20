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

theorem rePred_of_exists_list {S : Set ℕ} (g h : ℕ × List ℕ → ℕ) (hg : Computable g)
    (hh : Computable h) (key : ∀ a : ℕ, S a ↔ ∃ L : List ℕ, g (a, L) = h (a, L)) : REPred S := by
  have hcomp : Computable fun q : ℕ × ℕ => decide
      (g (q.1, Denumerable.ofNat (List ℕ) q.2) = h (q.1, Denumerable.ofNat (List ℕ) q.2)) :=
    (Primrec₂.to_comp (Primrec.eq (α := ℕ)).decide).comp
      (hg.comp (Computable.fst.pair ((Computable.ofNat (List ℕ)).comp Computable.snd)))
      (hh.comp (Computable.fst.pair ((Computable.ofNat (List ℕ)).comp Computable.snd)))
  have hq : Partrec₂ (fun a n => (Part.some (decide
      (g (a, Denumerable.ofNat (List ℕ) n) = h (a, Denumerable.ofNat (List ℕ) n))) : Part Bool)) :=
    Computable₂.partrec₂ hcomp
  refine ((Partrec.rfind hq).dom_re).of_eq fun a => ?_
  rw [Nat.rfind_dom, key]
  constructor
  · rintro ⟨n, hn, -⟩
    exact ⟨Denumerable.ofNat (List ℕ) n, by simpa using hn⟩
  · rintro ⟨L, hL⟩
    exact ⟨Encodable.encode L, by simp [hL], fun {m} _ => trivial⟩

/-- **Every Diophantine subset of `ℕ` is recursively enumerable** (the easy half of MRDP). -/
