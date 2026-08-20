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

lemma badSet_card_le {n m : ℕ} (s : V n) (hs : s ≠ 0) :
    (badSet n m s).card * 4 ^ m ≤ (2 ^ n - 2) * (2 ^ n) ^ m := by
  classical
  set I : Finset (V n) := Finset.univ.filter (fun t : V n => t ≠ 0 ∧ t ≠ s) with hI
  set Bt : V n → Finset (Fin m → V n) := fun t =>
    Fintype.piFinset (fun _ : Fin m =>
      Finset.univ.filter (fun y : V n => dot y s = 0 ∧ dot y t = 0)) with hBt
  have hsub : badSet n m s ⊆ I.biUnion Bt := by
    intro v hv
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨hv1, hv2⟩ := hv
    unfold Determines at hv2
    push_neg at hv2
    obtain ⟨t, ht, ht0, hts⟩ := hv2
    refine Finset.mem_biUnion.mpr ⟨t, ?_, ?_⟩
    · simp [hI, ht0, hts]
    · simp only [hBt, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun i => ⟨hv1 i, ht i⟩
  have hcardI : I.card ≤ 2 ^ n - 2 := by
    have h1 : I ⊆ (Finset.univ : Finset (V n)) \ {0, s} := by
      intro t ht
      simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      simp [Finset.mem_sdiff, ht.1, ht.2]
    have h2 := Finset.card_le_card h1
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_pair (Ne.symm hs)] at h2
    simpa using h2
  have hcardBt : ∀ t ∈ I, (Bt t).card * 4 ^ m = (2 ^ n) ^ m := by
    intro t ht
    simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have hc : 4 * (Finset.univ.filter (fun y : V n => dot y s = 0 ∧ dot y t = 0)).card = 2 ^ n :=
      card_perp_two s t hs ht.1 (Ne.symm ht.2)
    have hcard : (Bt t).card
        = ((Finset.univ.filter (fun y : V n => dot y s = 0 ∧ dot y t = 0)).card) ^ m := by
      simp [hBt, Fintype.card_piFinset]
    rw [hcard, ← mul_pow, mul_comm, hc]
  calc (badSet n m s).card * 4 ^ m ≤ (I.biUnion Bt).card * 4 ^ m :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ t ∈ I, (Bt t).card) * 4 ^ m := Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ t ∈ I, ((Bt t).card * 4 ^ m) := by rw [Finset.sum_mul]
    _ = ∑ t ∈ I, (2 ^ n) ^ m := Finset.sum_congr rfl hcardBt
    _ = I.card * (2 ^ n) ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 ^ n - 2) * (2 ^ n) ^ m := Nat.mul_le_mul_right _ hcardI

/-- **Simon's algorithm succeeds with `m` queries except with probability `2 ^ n / 2 ^ m`.** -/
