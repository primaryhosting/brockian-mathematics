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

theorem card_Dset_le {n : ℕ} (hS : (S n).card ≤ 2 ^ g n) (hn : n + 1 ≤ 2 ^ g n) :
    (Dset N S g n).card ≤ 2 ^ (5 * g n * g n + 10 * g n + 6) := by
  set K := g n with hK
  set E := 5 * K * K + 10 * K + 3 with hE
  have hB := card_Bset_le (N := N) (S := S) (g := g) (n := n) hS
  have hL := card_LSset_le (N := N) (S := S) (g := g) (n := n) hS
  have hSTK := card_STKset_le (N := N) (S := S) (g := g) (n := n) hS
  have hR : (Finset.range (K + 1)).card ≤ 2 ^ K := by
    rw [Finset.card_range]
    exact Nat.lt_two_pow_self
  have hBool : ({false, true} : Finset Bool).card ≤ 2 ^ 1 := by decide
  -- the five pieces
  have p1 : ((Finset.range (n + 1)).image (SMem.scan : ℕ → SMem N.Mem)).card ≤ 2 ^ E := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_range]
    exact le_trans hn (Nat.pow_le_pow_right (by omega) (by omega))
  have p2 : ((LSset N S n).image (fun todo => SMem.outer n todo)).card ≤ 2 ^ E := by
    refine le_trans Finset.card_image_le ?_
    exact le_trans hL (Nat.pow_le_pow_right (by omega) (by omega))
  have p3 : (((LSset N S n) ×ˢ (Bset N S n) ×ˢ (Bset N S n) ×ˢ (Finset.range (K + 1)) ×ˢ
      (STKset N S g n)).image
      (fun p => SMem.call n p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).card ≤ 2 ^ E := by
    refine le_trans Finset.card_image_le ?_
    have e : E = (K + 1) + ((K + 1) + ((K + 1) + (K + (5 * K * K + 6 * K)))) := by
      rw [hE]; ring
    rw [e]
    simp only [Finset.card_product]
    exact mul_le_two_pow hL (mul_le_two_pow hB (mul_le_two_pow hB
      (mul_le_two_pow hR hSTK)))
  have p4 : (((LSset N S n) ×ˢ ({false, true} : Finset Bool) ×ˢ (STKset N S g n)).image
      (fun p => SMem.ret n p.1 p.2.1 p.2.2)).card ≤ 2 ^ E := by
    refine le_trans Finset.card_image_le ?_
    have hle : (K + 1) + (1 + (5 * K * K + 6 * K)) ≤ E := by rw [hE]; omega
    refine le_trans ?_ (Nat.pow_le_pow_right (by omega) hle)
    simp only [Finset.card_product]
    exact mul_le_two_pow hL (mul_le_two_pow hBool hSTK)
  have p5 : ({SMem.acc} : Finset (SMem N.Mem)).card ≤ 2 ^ E := by
    rw [Finset.card_singleton]
    exact Nat.one_le_two_pow
  have hunion : (Dset N S g n).card ≤
      ((Finset.range (n + 1)).image (SMem.scan : ℕ → SMem N.Mem)).card +
      ((LSset N S n).image (fun todo => SMem.outer n todo)).card +
      (((LSset N S n) ×ˢ (Bset N S n) ×ˢ (Bset N S n) ×ˢ (Finset.range (K + 1)) ×ˢ
        (STKset N S g n)).image
        (fun p => SMem.call n p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).card +
      (((LSset N S n) ×ˢ ({false, true} : Finset Bool) ×ˢ (STKset N S g n)).image
        (fun p => SMem.ret n p.1 p.2.1 p.2.2)).card +
      ({SMem.acc} : Finset (SMem N.Mem)).card := by
    refine le_trans (Finset.card_union_le _ _) ?_
    gcongr
    refine le_trans (Finset.card_union_le _ _) ?_
    gcongr
    refine le_trans (Finset.card_union_le _ _) ?_
    gcongr
    exact Finset.card_union_le _ _
  have hfin : 2 ^ (5 * K * K + 10 * K + 6) = 8 * 2 ^ E := by
    rw [hE, pow_add]
    ring
  omega

end

end CS

/-
# Walks in a relation, and the elementary distance bound

If every vertex reachable from `a` lies in a finite set `S`, then any vertex
reachable from `a` is reachable by a walk of length `< S.card`.
-/
import Mathlib

namespace CS

variable {α : Type}

/-- `Walk r t a b` : there is a walk of length exactly `t` from `a` to `b`. -/
