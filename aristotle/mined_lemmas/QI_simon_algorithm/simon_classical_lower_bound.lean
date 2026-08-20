import Mathlib
import RequestProject.QI.Spanning
import RequestProject.QI.Classical

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/--
**Simon's problem is solved with `O(n)` quantum queries but needs `Ω(2 ^ (n / 2))`
classical queries.**

The four conjuncts are:

1. *One quantum query.*  For every Simon function `f` with secret `s`, one run of the
   circuit `H ∘ U_f ∘ H` applied to `|0,0⟩` — which uses exactly one oracle query — yields
   a measurement outcome that is uniformly distributed over the hyperplane
   `s^⊥ = {y | ⟪y, s⟫ = 0}` (probability `2 / 2 ^ n` on it, `0` off it).

2. *`m` quantum queries.*  With `m` runs of the circuit (`m` queries in total), the
   outcomes determine `s` uniquely — i.e. `s` is the only nonzero solution of the linear
   system they define, so Gaussian elimination recovers it — with probability at least
   `1 - 2 ^ n / 2 ^ m`.

3. *`O(n)` queries suffice.*  Taking `m = 2 n` queries, the algorithm succeeds with
   probability at least `1 - 2 ^ (-n)`.

4. *Classical lower bound.*  Any deterministic classical query algorithm (decision tree)
   that outputs the correct secret for every Simon function on `n ≥ 2` bits has depth at
   least `2 ^ (n / 2)`, i.e. makes `Ω(2 ^ (n / 2))` queries in the worst case.
-/

theorem simon_classical_lower_bound {n : ℕ} (hn : 2 ≤ n) (t : DTree n)
    (hcorrect : ∀ (f : V n → V n) (s : V n), IsSimon f s → t.run f = s) :
    2 ^ (n / 2) ≤ t.depth := by
  classical
  set Q : Finset (V n) := t.queries id with hQdef
  set D : Finset (V n) := insert 0 ((Q ×ˢ Q).image (fun p => p.1 + p.2)) with hDdef
  have hDcard : D.card ≤ 1 + Q.card * Q.card := by
    calc D.card ≤ ((Q ×ˢ Q).image (fun p => p.1 + p.2)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (Q ×ˢ Q).card + 1 := Nat.add_le_add_right (Finset.card_image_le) 1
      _ = Q.card * Q.card + 1 := by rw [Finset.card_product]
      _ = 1 + Q.card * Q.card := by ring
  have key : ∀ s ∈ (Finset.univ \ D), t.run id = s := by
    intro s hsD
    rw [Finset.mem_sdiff] at hsD
    have hsD := hsD.2
    have hs0 : s ≠ 0 := by
      intro hz
      exact hsD (by rw [hDdef, hz]; exact Finset.mem_insert_self _ _)
    have hQs : ∀ x ∈ Q, x + s ∉ Q := by
      intro x hx hxs
      apply hsD
      rw [hDdef]
      refine Finset.mem_insert_of_mem ?_
      refine Finset.mem_image.mpr ⟨(x, x + s), Finset.mem_product.mpr ⟨hx, hxs⟩, ?_⟩
      simp only
      rw [← add_assoc, add_self_V, zero_add]
    have hsim := repQ_isSimon hs0 hQs
    have h1 : t.run (repQ Q s) = s := hcorrect _ _ hsim
    have h2 : t.run (repQ Q s) = t.run id :=
      DTree.run_congr t id (repQ Q s) (fun x hx => repQ_eq_of_mem (by rw [hQdef]; exact hx))
    rw [← h2, h1]
  have h1 : (Finset.univ \ D).card ≤ 1 :=
    Finset.card_le_one.mpr (fun a ha b hb => (key a ha).symm.trans (key b hb))
  have h2 : (Finset.univ \ D).card + D.card = 2 ^ n := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)]
    simp
  have h3 : 2 ^ n ≤ 2 + Q.card * Q.card := by omega
  have h4 : Q.card ≤ t.depth := DTree.card_queries_le_depth t id
  have h5 : 2 ^ n ≤ 2 + t.depth * t.depth :=
    h3.trans (Nat.add_le_add_left (Nat.mul_le_mul h4 h4) 2)
  by_contra hcon
  push_neg at hcon
  have hq : 2 ^ (n / 2) * 2 ^ (n / 2) ≤ 2 ^ n := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : (t.depth + 1) * (t.depth + 1) ≤ 2 ^ (n / 2) * 2 ^ (n / 2) :=
    Nat.mul_le_mul hcon hcon
  have h4n : (4:ℕ) ≤ 2 ^ n := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  nlinarith [h5, hsq, hq, h4n]

end QI

