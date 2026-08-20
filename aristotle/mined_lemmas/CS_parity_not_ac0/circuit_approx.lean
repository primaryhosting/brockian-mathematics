import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

theorem circuit_approx (c : Circuit n) (d ℓ : ℕ) (hℓ : 0 < ℓ) (hd : c.DepthLe d) :
    ∃ q : Cube n → ZMod 3, q ∈ Deg n ((2 * ℓ) ^ d) ∧ ∃ B : Finset (Cube n),
      2 ^ ℓ * B.card ≤ c.size * 2 ^ n ∧ ∀ x, x ∉ B → q x = bit (c.value x c.out) := by
  classical
  obtain ⟨lev, hlevd, hlev⟩ := hd
  -- one gate at a time
  have hstep : ∀ (ik : Fin c.size) (p : Fin c.size → Cube n → ZMod 3) (B : Finset (Cube n)),
      (∀ j : Fin c.size, (j : ℕ) < (ik : ℕ) → p j ∈ Deg n ((2 * ℓ) ^ (lev j))) →
      (∀ j : Fin c.size, (j : ℕ) < (ik : ℕ) → ∀ x, x ∉ B → p j x = bit (c.value x j)) →
      ∃ q : Cube n → ZMod 3, q ∈ Deg n ((2 * ℓ) ^ (lev ik)) ∧ ∃ E : Finset (Cube n),
        2 ^ ℓ * E.card ≤ 2 ^ n ∧ ∀ x, x ∉ B → x ∉ E → q x = bit (c.value x ik) := by
    intro ik p B hpdeg hpval
    rcases hg : c.gate ik with b | i | j | s | s
    · -- constant gate
      refine ⟨fun _ => bit b, const_mem_Deg _ _, ∅, by simp, ?_⟩
      intro x _ _
      rw [c.value_eq x ik, hg]
      rfl
    · -- input variable
      have hq : (fun x : Cube n => bit (x i)) = mon ({i} : Finset (Fin n)) - (fun _ => 1) := by
        funext x
        have := sgn_eq_one_add_bit (x i)
        simp only [Pi.sub_apply, mon, Finset.prod_singleton]
        rw [this]; ring
      have hmem : (fun x : Cube n => bit (x i)) ∈ Deg n 1 := by
        rw [hq]
        exact Submodule.sub_mem _ (mon_mem_Deg (by simp)) (const_mem_Deg _ _)
      refine ⟨fun x => bit (x i), ?_, ∅, by simp, ?_⟩
      · exact Deg_mono (Nat.one_le_pow _ _ (by omega)) hmem
      · intro x _ _
        rw [c.value_eq x ik, hg]
        rfl
    · -- negation
      have hjref : j ∈ (c.gate ik).refs := by rw [hg]; simp [Gate.refs]
      have hjlt : (j : ℕ) < (ik : ℕ) := c.wf ik j hjref
      have hjlev : lev j ≤ lev ik := by
        have := hlev ik j hjref
        rw [hg] at this
        simpa [Gate.cost] using this
      refine ⟨1 - p j, Submodule.sub_mem _ (one_mem_Deg _) ?_, ∅, by simp, ?_⟩
      · refine Deg_mono ?_ (hpdeg j hjlt)
        exact Nat.pow_le_pow_right (by omega) hjlev
      · intro x hxB _
        rw [c.value_eq x ik, hg]
        simp only [Gate.eval, Pi.sub_apply, Pi.one_apply, hpval j hjlt x hxB]
        rw [bit_not]
    · -- AND gate
      by_cases hlev0 : lev ik = 0
      · have hempty : s = ∅ := by
          by_contra hne
          obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          have hjref : j ∈ (c.gate ik).refs := by rw [hg]; exact hj
          have := hlev ik j hjref
          rw [hg] at this
          simp only [Gate.cost] at this
          omega
        refine ⟨fun _ => 1, const_mem_Deg _ _, ∅, by simp, ?_⟩
        intro x _ _
        rw [c.value_eq x ik, hg, hempty]
        simp [Gate.eval, bit]
      · have hpow : 2 * ℓ * ((2 * ℓ) ^ (lev ik - 1)) = (2 * ℓ) ^ (lev ik) := by
          have h1 : lev ik - 1 + 1 = lev ik := by omega
          calc 2 * ℓ * ((2 * ℓ) ^ (lev ik - 1)) = (2 * ℓ) ^ (lev ik - 1 + 1) := by
                rw [pow_succ]; ring
            _ = (2 * ℓ) ^ (lev ik) := by rw [h1]
        have hchild : ∀ j ∈ s, (j : ℕ) < (ik : ℕ) ∧ lev j ≤ lev ik - 1 := by
          intro j hj
          have hjref : j ∈ (c.gate ik).refs := by rw [hg]; exact hj
          have hc := hlev ik j hjref
          rw [hg] at hc
          simp only [Gate.cost] at hc
          exact ⟨c.wf ik j hjref, by omega⟩
        obtain ⟨q, hqd, E, hE, hqv⟩ := and_approx (n := n) ℓ ((2 * ℓ) ^ (lev ik - 1))
          (Finset.univ \ B) s p (fun x j => c.value x j)
          (fun j hj => Deg_mono (Nat.pow_le_pow_right (by omega) (hchild j hj).2)
            (hpdeg j (hchild j hj).1))
          (fun j hj x hx => hpval j (hchild j hj).1 x (by
            simpa using (Finset.mem_sdiff.mp hx).2))
        rw [hpow] at hqd
        refine ⟨q, hqd, E, hE, ?_⟩
        intro x hxB hxE
        rw [c.value_eq x ik, hg]
        exact hqv x (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxB⟩) hxE
    · -- OR gate
      by_cases hlev0 : lev ik = 0
      · have hempty : s = ∅ := by
          by_contra hne
          obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          have hjref : j ∈ (c.gate ik).refs := by rw [hg]; exact hj
          have := hlev ik j hjref
          rw [hg] at this
          simp only [Gate.cost] at this
          omega
        refine ⟨fun _ => 0, Submodule.zero_mem _, ∅, by simp, ?_⟩
        intro x _ _
        rw [c.value_eq x ik, hg, hempty]
        simp [Gate.eval, bit]
      · have hpow : 2 * ℓ * ((2 * ℓ) ^ (lev ik - 1)) = (2 * ℓ) ^ (lev ik) := by
          have h1 : lev ik - 1 + 1 = lev ik := by omega
          calc 2 * ℓ * ((2 * ℓ) ^ (lev ik - 1)) = (2 * ℓ) ^ (lev ik - 1 + 1) := by
                rw [pow_succ]; ring
            _ = (2 * ℓ) ^ (lev ik) := by rw [h1]
        have hchild : ∀ j ∈ s, (j : ℕ) < (ik : ℕ) ∧ lev j ≤ lev ik - 1 := by
          intro j hj
          have hjref : j ∈ (c.gate ik).refs := by rw [hg]; exact hj
          have hc := hlev ik j hjref
          rw [hg] at hc
          simp only [Gate.cost] at hc
          exact ⟨c.wf ik j hjref, by omega⟩
        obtain ⟨q, hqd, E, hE, hqv⟩ := or_approx (n := n) ℓ ((2 * ℓ) ^ (lev ik - 1))
          (Finset.univ \ B) s p (fun x j => c.value x j)
          (fun j hj => Deg_mono (Nat.pow_le_pow_right (by omega) (hchild j hj).2)
            (hpdeg j (hchild j hj).1))
          (fun j hj x hx => hpval j (hchild j hj).1 x (by
            simpa using (Finset.mem_sdiff.mp hx).2))
        rw [hpow] at hqd
        refine ⟨q, hqd, E, hE, ?_⟩
        intro x hxB hxE
        rw [c.value_eq x ik, hg]
        exact hqv x (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxB⟩) hxE
  -- induction over the gates
  have main : ∀ k : ℕ, k ≤ c.size → ∃ (p : Fin c.size → Cube n → ZMod 3) (B : Finset (Cube n)),
      (∀ i : Fin c.size, (i : ℕ) < k → p i ∈ Deg n ((2 * ℓ) ^ (lev i))) ∧
      2 ^ ℓ * B.card ≤ k * 2 ^ n ∧
      (∀ i : Fin c.size, (i : ℕ) < k → ∀ x, x ∉ B → p i x = bit (c.value x i)) := by
    intro k
    induction k with
    | zero =>
        intro _
        exact ⟨fun _ _ => 0, ∅, by intro i hi; omega, by simp, by intro i hi; omega⟩
    | succ k ih =>
        intro hk
        obtain ⟨p, B, hpd, hB, hpv⟩ := ih (by omega)
        have hks : k < c.size := by omega
        obtain ⟨q, hqd, E, hE, hqv⟩ := hstep ⟨k, hks⟩ p B (fun j hj => hpd j hj)
          (fun j hj => hpv j hj)
        refine ⟨Function.update p ⟨k, hks⟩ q, B ∪ E, ?_, ?_, ?_⟩
        · intro i hi
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
          · rw [Function.update_of_ne (by simp only [ne_eq, Fin.ext_iff]; omega)]
            exact hpd i h
          · have : i = ⟨k, hks⟩ := Fin.ext h
            rw [this, Function.update_self]
            exact hqd
        · have hcard : (B ∪ E).card ≤ B.card + E.card := Finset.card_union_le B E
          have : 2 ^ ℓ * (B ∪ E).card ≤ 2 ^ ℓ * B.card + 2 ^ ℓ * E.card := by
            calc 2 ^ ℓ * (B ∪ E).card ≤ 2 ^ ℓ * (B.card + E.card) :=
                  Nat.mul_le_mul_left _ hcard
              _ = 2 ^ ℓ * B.card + 2 ^ ℓ * E.card := by ring
          have h2 : k * 2 ^ n + 2 ^ n = (k + 1) * 2 ^ n := by ring
          omega
        · intro i hi x hx
          have hxB : x ∉ B := fun h => hx (Finset.mem_union_left _ h)
          have hxE : x ∉ E := fun h => hx (Finset.mem_union_right _ h)
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
          · rw [Function.update_of_ne (by simp only [ne_eq, Fin.ext_iff]; omega)]
            exact hpv i h x hxB
          · have hik : i = ⟨k, hks⟩ := Fin.ext h
            rw [hik, Function.update_self]
            exact hqv x hxB hxE
  obtain ⟨p, B, hpd, hB, hpv⟩ := main c.size (le_refl _)
  refine ⟨p c.out, ?_, B, hB, fun x hx => hpv c.out c.out.2 x hx⟩
  exact Deg_mono (Nat.pow_le_pow_right (by omega) (hlevd c.out)) (hpd c.out c.out.2)

end CS

import RequestProject.Circuits

/-!
# Completeness of the circuit model

Every Boolean function on `n` bits is computed by a circuit of depth `2`
(its DNF, of exponential size).  In particular parity *is* computable in this
model, so `CS.parity_not_ac0` is a genuine statement about the *size* of
constant-depth circuits, and the semantics `Circuit.Computes` is not vacuous.
-/

namespace CS

open Finset

namespace DNF

variable {n : ℕ}

/-- Index of the gate carrying the literal `k` of the conjunction at `a`. -/
