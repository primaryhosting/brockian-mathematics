/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat.Partrec Nat.Partrec.Code

namespace CS

deriving instance DecidableEq for Nat.Partrec.Code

/-! ## Blum complexity measures -/

/-- A *Blum complexity measure* for the standard numbering `Nat.Partrec.Code.eval` of the
partial computable functions.  `cost c x` is the amount of resource used by the program `c`
on input `x`.  Blum's two axioms are:

* `dom_eq`: `cost c x` is defined exactly when the program `c` halts on `x`;
* the graph of `cost` is decidable, witnessed here by a computable `Bool`-valued `graph`. -/
structure BlumMeasure where
  cost : Code → ℕ →. ℕ
  graph : Code → ℕ → ℕ → Bool
  graph_computable : Computable fun p : (Code × ℕ) × ℕ => graph p.1.1 p.1.2 p.2
  graph_spec : ∀ c x m, graph c x m = true ↔ m ∈ cost c x
  dom_eq : ∀ c x, (cost c x).Dom ↔ (c.eval x).Dom

/-! ## The step-counting measure -/


theorem blum_speedup_padding_measure (r : ℕ → ℕ) (hr : Computable r) :
    ∃ (M : BlumMeasure) (f : ℕ → ℕ), Computable f ∧
      ∀ e : Code, e.eval = (fun x => Part.some (f x)) →
        ∃ e' : Code, e'.eval = (fun x => Part.some (f x)) ∧
          ∀ᶠ x in Filter.atTop, ∃ a ∈ M.cost e' x, ∃ b ∈ M.cost e x, r a ≤ b := by
  refine ⟨speedMeasure r hr, fun _ => 0, Computable.const 0, ?_⟩
  intro e he
  by_cases hpad : ∃ n, e = padCode n
  · obtain ⟨n, rfl⟩ := hpad
    refine ⟨padCode (n + 1), funext fun x => eval_padCode _ _, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (n + 1)] with x hx
    refine ⟨costA r (n + 1) x, ?_, costA r n x, ?_, ?_⟩
    · show costA r (n + 1) x ∈ speedCost r (padCode (n + 1)) x
      rw [speedCost_pad r (n + 1) x hx]
      simp
    · show costA r n x ∈ speedCost r (padCode n) x
      rw [speedCost_pad r n x (by omega)]
      simp
    · rw [costA_step r n x hx]
  · push_neg at hpad
    refine ⟨padCode 0, funext fun x => eval_padCode _ _, ?_⟩
    filter_upwards with x
    have hdom : (stepCost e x).Dom := by
      refine (stepCost_dom e x).mpr ?_
      rw [he]
      trivial
    obtain ⟨s, hs⟩ := Part.dom_iff_mem.mp hdom
    refine ⟨costA r 0 x, ?_, s + bigB r x, ?_, ?_⟩
    · show costA r 0 x ∈ speedCost r (padCode 0) x
      rw [speedCost_pad r 0 x (Nat.zero_le x)]
      simp
    · show s + bigB r x ∈ speedCost r e x
      rw [speedCost_not_pad r hpad x]
      exact Part.mem_map_iff _ |>.mpr ⟨s, hs, rfl⟩
    · rw [bigB_eq r x]
      omega

/-- **There are problems with no fastest algorithm** (Blum's speedup theorem).

Fix any Blum complexity measure `M` (a cost function for the standard numbering of the partial
computable functions satisfying Blum's axioms) and any computable "speedup factor" `r`.  Then
there is a computable function `f` such that *every* program `e` computing `f` is beaten by
another program `e'` computing the very same function: on almost every input `x`, the cost of
`e` is at least `r` applied to the cost of `e'`.

Thus no program for `f` is optimal: each one can be sped up by the factor `r` on almost all
inputs. -/
