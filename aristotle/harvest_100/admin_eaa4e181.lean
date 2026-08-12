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
noncomputable def Circuit.value (c : Circuit n) (x : Cube n) : Fin c.size → Bool :=
  (c.exists_vals x).choose

lemma Circuit.value_spec (c : Circuit n) (x : Cube n) : c.Vals x (c.value x) :=
  (c.exists_vals x).choose_spec

lemma Circuit.value_eq (c : Circuit n) (x : Cube n) (i : Fin c.size) :
    c.value x i = (c.gate i).eval x (c.value x) := c.value_spec x i

lemma Circuit.computes_value (c : Circuit n) {f : Cube n → Bool} (h : c.Computes f)
    (x : Cube n) : c.value x c.out = f x := by
  obtain ⟨v, hv, hvo⟩ := h x
  rw [c.vals_unique x (c.value_spec x) hv]
  exact hvo

/-- **Approximation of an AND gate**, by De Morgan from `or_approx`. -/
theorem and_approx {m : ℕ} (ℓ D : ℕ) (G : Finset (Cube n))
    (s : Finset (Fin m)) (p : Fin m → Cube n → ZMod 3) (w : Cube n → Fin m → Bool)
    (hp : ∀ j ∈ s, p j ∈ Deg n D)
    (hpw : ∀ j ∈ s, ∀ x ∈ G, p j x = bit (w x j)) :
    ∃ q : Cube n → ZMod 3, q ∈ Deg n (2 * ℓ * D) ∧ ∃ E : Finset (Cube n),
      2 ^ ℓ * E.card ≤ 2 ^ n ∧
      ∀ x ∈ G, x ∉ E → q x = bit (decide (∀ j ∈ s, w x j = true)) := by
  obtain ⟨q, hq, E, hE, hqval⟩ := or_approx ℓ D G s (fun j => 1 - p j) (fun x j => !(w x j))
    (fun j hj => Submodule.sub_mem _ (one_mem_Deg D) (hp j hj))
    (fun j hj x hx => by
      simp only [Pi.sub_apply, Pi.one_apply, hpw j hj x hx]
      rw [bit_not])
  refine ⟨1 - q, Submodule.sub_mem _ (one_mem_Deg _) hq, E, hE, ?_⟩
  intro x hxG hxE
  simp only [Pi.sub_apply, Pi.one_apply, hqval x hxG hxE]
  by_cases hall : ∀ j ∈ s, w x j = true
  · have hnex : ¬ ∃ j ∈ s, (!(w x j)) = true := by
      rintro ⟨j, hj, h⟩
      rw [hall j hj] at h
      exact absurd h (by decide)
    rw [decide_eq_false hnex, decide_eq_true hall]
    simp only [bit_false, bit_true]
    decide
  · push_neg at hall
    obtain ⟨j, hj, hjv⟩ := hall
    have hex : ∃ j ∈ s, (!(w x j)) = true := by
      refine ⟨j, hj, ?_⟩
      cases hw : w x j
      · rfl
      · exact absurd hw hjv
    have hnall : ¬ ∀ j ∈ s, w x j = true := by
      intro h
      exact hjv (h j hj)
    rw [decide_eq_true hex, decide_eq_false hnall]
    simp only [bit_false, bit_true]
    decide

/-- **Approximation of a whole circuit.** -/
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
def litIdx (a : Cube n) (k : Fin n) : ℕ := if a k then (k : ℕ) else n + (k : ℕ)

lemma litIdx_lt (a : Cube n) (k : Fin n) : litIdx a k < 2 * n := by
  have := k.2; unfold litIdx; split <;> omega

/-- The literal gate `k` of the conjunction at `a`. -/
def lit (a : Cube n) (k : Fin n) : Fin (2 * n + 2 ^ n + 1) :=
  ⟨litIdx a k, by have h := litIdx_lt a k; have h2 : 0 ≤ 2 ^ n := Nat.zero_le _; omega⟩

@[simp] lemma coe_lit (a : Cube n) (k : Fin n) :
    ((lit a k : Fin (2 * n + 2 ^ n + 1)) : ℕ) = litIdx a k := rfl

/-- The literal gates of the conjunction at `a`. -/
def lits (a : Cube n) : Finset (Fin (2 * n + 2 ^ n + 1)) :=
  Finset.univ.filter (fun j => ∃ k : Fin n, (j : ℕ) = litIdx a k)

lemma lit_mem (a : Cube n) (k : Fin n) : lit a k ∈ lits a :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨k, rfl⟩⟩

lemma mem_lits {a : Cube n} {j : Fin (2 * n + 2 ^ n + 1)} (h : j ∈ lits a) :
    ∃ k : Fin n, j = lit a k := by
  obtain ⟨k, hk⟩ := (Finset.mem_filter.mp h).2
  exact ⟨k, Fin.ext hk⟩

/-- The gate index of the `k`-th conjunction. -/
def term (k : Fin (2 ^ n)) : Fin (2 * n + 2 ^ n + 1) := ⟨2 * n + (k : ℕ), by have := k.2; omega⟩

@[simp] lemma coe_term (k : Fin (2 ^ n)) :
    ((term k : Fin (2 * n + 2 ^ n + 1)) : ℕ) = 2 * n + (k : ℕ) := rfl

variable (f : Cube n → Bool) (e : Cube n ≃ Fin (2 ^ n))

/-- The conjunctions appearing in the final disjunction. -/
def terms : Finset (Fin (2 * n + 2 ^ n + 1)) :=
  (Finset.univ.filter (fun k : Fin (2 ^ n) => f (e.symm k) = true)).image term

/-- The gates of the DNF circuit for `f`. -/
def dgate (i : Fin (2 * n + 2 ^ n + 1)) : Gate n (2 * n + 2 ^ n + 1) :=
  if h1 : (i : ℕ) < n then Gate.var ⟨i, h1⟩
  else if h2 : (i : ℕ) < 2 * n then Gate.not ⟨(i : ℕ) - n, by omega⟩
  else if h3 : (i : ℕ) < 2 * n + 2 ^ n then
    Gate.and (lits (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩))
  else Gate.or (terms f e)

lemma dgate_var (i : Fin (2 * n + 2 ^ n + 1)) (h1 : (i : ℕ) < n) :
    dgate f e i = Gate.var ⟨i, h1⟩ := by
  rw [dgate, dif_pos h1]

lemma dgate_not (i : Fin (2 * n + 2 ^ n + 1)) (h1 : ¬ (i : ℕ) < n) (h2 : (i : ℕ) < 2 * n) :
    dgate f e i = Gate.not ⟨(i : ℕ) - n, by omega⟩ := by
  rw [dgate, dif_neg h1, dif_pos h2]

lemma dgate_and (i : Fin (2 * n + 2 ^ n + 1)) (h1 : ¬ (i : ℕ) < n) (h2 : ¬ (i : ℕ) < 2 * n)
    (h3 : (i : ℕ) < 2 * n + 2 ^ n) :
    dgate f e i = Gate.and (lits (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩)) := by
  rw [dgate, dif_neg h1, dif_neg h2, dif_pos h3]

lemma dgate_or (i : Fin (2 * n + 2 ^ n + 1)) (h1 : ¬ (i : ℕ) < n) (h2 : ¬ (i : ℕ) < 2 * n)
    (h3 : ¬ (i : ℕ) < 2 * n + 2 ^ n) :
    dgate f e i = Gate.or (terms f e) := by
  rw [dgate, dif_neg h1, dif_neg h2, dif_neg h3]

/-- The values of the gates of the DNF circuit on input `x`. -/
def dval (x : Cube n) (j : Fin (2 * n + 2 ^ n + 1)) : Bool :=
  if h1 : (j : ℕ) < n then x ⟨j, h1⟩
  else if h2 : (j : ℕ) < 2 * n then !(x ⟨(j : ℕ) - n, by omega⟩)
  else if h3 : (j : ℕ) < 2 * n + 2 ^ n then
    decide (x = e.symm ⟨(j : ℕ) - 2 * n, by omega⟩)
  else f x

lemma dval_var (x : Cube n) (j : Fin (2 * n + 2 ^ n + 1)) (h1 : (j : ℕ) < n) :
    dval f e x j = x ⟨j, h1⟩ := by
  rw [dval, dif_pos h1]

lemma dval_not (x : Cube n) (j : Fin (2 * n + 2 ^ n + 1)) (h1 : ¬ (j : ℕ) < n)
    (h2 : (j : ℕ) < 2 * n) : dval f e x j = !(x ⟨(j : ℕ) - n, by omega⟩) := by
  rw [dval, dif_neg h1, dif_pos h2]

lemma dval_and (x : Cube n) (j : Fin (2 * n + 2 ^ n + 1)) (h1 : ¬ (j : ℕ) < n)
    (h2 : ¬ (j : ℕ) < 2 * n) (h3 : (j : ℕ) < 2 * n + 2 ^ n) :
    dval f e x j = decide (x = e.symm ⟨(j : ℕ) - 2 * n, by omega⟩) := by
  rw [dval, dif_neg h1, dif_neg h2, dif_pos h3]

lemma dval_or (x : Cube n) (j : Fin (2 * n + 2 ^ n + 1)) (h1 : ¬ (j : ℕ) < n)
    (h2 : ¬ (j : ℕ) < 2 * n) (h3 : ¬ (j : ℕ) < 2 * n + 2 ^ n) : dval f e x j = f x := by
  rw [dval, dif_neg h1, dif_neg h2, dif_neg h3]

lemma dval_lit (x a : Cube n) (k : Fin n) :
    dval f e x (lit a k) = (if a k then x k else !(x k)) := by
  have hk := k.2
  by_cases hak : a k
  · have h1 : ((lit a k : Fin (2 * n + 2 ^ n + 1)) : ℕ) = (k : ℕ) := by simp [litIdx, hak]
    simp only [dval, h1, dif_pos hk, hak, if_true, Fin.eta]
  · have h1 : ((lit a k : Fin (2 * n + 2 ^ n + 1)) : ℕ) = n + (k : ℕ) := by simp [litIdx, hak]
    have h2 : ¬ (n + (k : ℕ) < n) := by omega
    have h3 : n + (k : ℕ) < 2 * n := by omega
    simp only [dval, h1, dif_neg h2, dif_pos h3, hak, Bool.false_eq_true, if_false]
    congr 2
    exact Fin.ext (by simp)

lemma dval_term (x : Cube n) (k : Fin (2 ^ n)) :
    dval f e x (term k) = decide (x = e.symm k) := by
  have hk := k.2
  have h1 : ¬ (2 * n + (k : ℕ) < n) := by omega
  have h2 : ¬ (2 * n + (k : ℕ) < 2 * n) := by omega
  have h3 : 2 * n + (k : ℕ) < 2 * n + 2 ^ n := by omega
  simp only [dval, coe_term, dif_neg h1, dif_neg h2, dif_pos h3]
  congr 3
  exact Fin.ext (by simp)

end DNF

open DNF in
open DNF in
/-- **Every Boolean function is computed by a circuit of depth 2.** -/
theorem exists_depth_two_circuit (n : ℕ) (f : Cube n → Bool) :
    ∃ c : Circuit n, c.DepthLe 2 ∧ c.Computes f := by
  classical
  have hcard : Fintype.card (Cube n) = 2 ^ n := by simp [Cube]
  set e : Cube n ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq hcard with he
  have hout : 2 * n + 2 ^ n < 2 * n + 2 ^ n + 1 := by omega
  -- the gates a gate refers to come earlier, and sit in an earlier layer
  have hrefs : ∀ i : Fin (2 * n + 2 ^ n + 1), ∀ j ∈ (dgate f e i).refs,
      (j : ℕ) < (i : ℕ) := by
    intro i j hj
    by_cases h1 : (i : ℕ) < n
    · rw [dgate_var f e i h1] at hj; simp [Gate.refs] at hj
    · by_cases h2 : (i : ℕ) < 2 * n
      · rw [dgate_not f e i h1 h2] at hj
        simp only [Gate.refs, Finset.mem_singleton] at hj
        subst hj
        show (i : ℕ) - n < (i : ℕ)
        omega
      · by_cases h3 : (i : ℕ) < 2 * n + 2 ^ n
        · rw [dgate_and f e i h1 h2 h3] at hj
          simp only [Gate.refs] at hj
          obtain ⟨k, rfl⟩ := mem_lits hj
          have hlt := litIdx_lt (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩) k
          show litIdx _ k < (i : ℕ)
          omega
        · rw [dgate_or f e i h1 h2 h3] at hj
          simp only [Gate.refs, terms, Finset.mem_image, Finset.mem_filter] at hj
          obtain ⟨k, -, rfl⟩ := hj
          have hk := k.2
          have hi : (i : ℕ) = 2 * n + 2 ^ n := by have := i.2; omega
          show 2 * n + (k : ℕ) < (i : ℕ)
          omega
  refine ⟨⟨2 * n + 2 ^ n + 1, dgate f e, ⟨2 * n + 2 ^ n, hout⟩, hrefs⟩, ?_, ?_⟩
  · -- depth 2
    refine ⟨fun i => if (i : ℕ) < 2 * n then 0 else if (i : ℕ) < 2 * n + 2 ^ n then 1 else 2,
      fun i => by dsimp only; split <;> [omega; split] <;> omega, ?_⟩
    intro i j hj
    have hj0 : j ∈ (dgate f e i).refs := hj
    have hji := hrefs i j hj0
    dsimp only
    by_cases h1 : (i : ℕ) < n
    · rw [dgate_var f e i h1] at hj0; simp [Gate.refs] at hj0
    · by_cases h2 : (i : ℕ) < 2 * n
      · have e1 : (if (j : ℕ) < 2 * n then 0 else
            if (j : ℕ) < 2 * n + 2 ^ n then 1 else 2) = 0 := if_pos (by omega)
        have e2 : (if (i : ℕ) < 2 * n then 0 else
            if (i : ℕ) < 2 * n + 2 ^ n then 1 else 2) = 0 := if_pos h2
        rw [dgate_not f e i h1 h2]
        simp only [Gate.cost]
        omega
      · by_cases h3 : (i : ℕ) < 2 * n + 2 ^ n
        · rw [dgate_and f e i h1 h2 h3] at hj0 ⊢
          simp only [Gate.refs] at hj0
          obtain ⟨k, rfl⟩ := mem_lits hj0
          have hlt := litIdx_lt (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩) k
          have hcoe : ((lit (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩) k :
              Fin (2 * n + 2 ^ n + 1)) : ℕ) = litIdx (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩) k := rfl
          have e1 : (if ((lit (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩) k :
              Fin (2 * n + 2 ^ n + 1)) : ℕ) < 2 * n then 0 else
              if ((lit (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩) k :
                Fin (2 * n + 2 ^ n + 1)) : ℕ) < 2 * n + 2 ^ n then 1 else 2) = 0 :=
            if_pos (by rw [hcoe]; omega)
          have e2 : (if (i : ℕ) < 2 * n then 0 else
              if (i : ℕ) < 2 * n + 2 ^ n then 1 else 2) = 1 := by
            rw [if_neg h2, if_pos h3]
          simp only [Gate.cost]
          omega
        · rw [dgate_or f e i h1 h2 h3] at hj0 ⊢
          simp only [Gate.refs, terms, Finset.mem_image, Finset.mem_filter] at hj0
          obtain ⟨k, -, rfl⟩ := hj0
          have hk := k.2
          have hcoe : ((term k : Fin (2 * n + 2 ^ n + 1)) : ℕ) = 2 * n + (k : ℕ) := rfl
          have e1 : (if ((term k : Fin (2 * n + 2 ^ n + 1)) : ℕ) < 2 * n then 0 else
              if ((term k : Fin (2 * n + 2 ^ n + 1)) : ℕ) < 2 * n + 2 ^ n then 1 else 2) = 1 := by
            rw [if_neg (by rw [hcoe]; omega), if_pos (by rw [hcoe]; omega)]
          have e2 : (if (i : ℕ) < 2 * n then 0 else
              if (i : ℕ) < 2 * n + 2 ^ n then 1 else 2) = 2 := by
            rw [if_neg h2, if_neg h3]
          simp only [Gate.cost]
          omega
  · -- semantics
    intro x
    refine ⟨dval f e x, ?_, ?_⟩
    · intro i
      show dval f e x i = Gate.eval x (dval f e x) (dgate f e i)
      by_cases h1 : (i : ℕ) < n
      · rw [dgate_var f e i h1, dval_var f e x i h1]
        rfl
      · by_cases h2 : (i : ℕ) < 2 * n
        · rw [dgate_not f e i h1 h2, dval_not f e x i h1 h2]
          simp only [Gate.eval]
          rw [dval_var f e x ⟨(i : ℕ) - n, by omega⟩ (by show (i : ℕ) - n < n; omega)]
        · by_cases h3 : (i : ℕ) < 2 * n + 2 ^ n
          · rw [dgate_and f e i h1 h2 h3, dval_and f e x i h1 h2 h3]
            set a : Cube n := e.symm ⟨(i : ℕ) - 2 * n, by omega⟩ with ha
            simp only [Gate.eval]
            congr 1
            simp only [eq_iff_iff]
            constructor
            · rintro rfl j hj
              obtain ⟨k, rfl⟩ := mem_lits hj
              rw [dval_lit]
              by_cases hak : a k <;> simp [hak]
            · intro h
              funext k
              have hk := h (lit a k) (lit_mem a k)
              rw [dval_lit] at hk
              by_cases hak : a k <;> simp [hak] at hk <;> simp [hak, hk]
          · rw [dgate_or f e i h1 h2 h3, dval_or f e x i h1 h2 h3]
            simp only [Gate.eval]
            by_cases hfx : f x = true
            · have hmem : term (e x) ∈ terms f e :=
                Finset.mem_image.mpr ⟨e x, by simp [hfx], rfl⟩
              have hex : ∃ j ∈ terms f e, dval f e x j = true := by
                refine ⟨term (e x), hmem, ?_⟩
                rw [dval_term]
                simp
              rw [hfx, decide_eq_true hex]
            · have hno : ¬ ∃ j ∈ terms f e, dval f e x j = true := by
                rintro ⟨j, hjmem, hjval⟩
                simp only [terms, Finset.mem_image, Finset.mem_filter] at hjmem
                obtain ⟨k, ⟨-, hk⟩, rfl⟩ := hjmem
                rw [dval_term] at hjval
                have hxk : x = e.symm k := by simpa using hjval
                rw [← hxk] at hk
                exact hfx hk
              simp only [Bool.not_eq_true] at hfx
              rw [hfx, decide_eq_false hno]
    · show dval f e x ⟨2 * n + 2 ^ n, hout⟩ = f x
      rw [dval_or f e x ⟨2 * n + 2 ^ n, hout⟩ (by show ¬ (2 * n + 2 ^ n < n); omega)
        (by show ¬ (2 * n + 2 ^ n < 2 * n); omega) (by show ¬ (2 * n + 2 ^ n < 2 * n + 2 ^ n); omega)]

/-- Parity is computed by a (large) depth-2 circuit; the lower bound
`CS.parity_not_ac0` is therefore genuinely about circuit *size*. -/
theorem parity_computable (n : ℕ) : ∃ c : Circuit n, c.DepthLe 2 ∧ c.Computes (parity n) :=
  exists_depth_two_circuit n (parity n)

/-- `AC⁰` is not empty: the constantly false family belongs to it. -/
theorem const_false_in_ac0 : InAC0 (fun _ _ => false) := by
  refine ⟨0, 0, fun n => ⟨⟨1, fun _ => Gate.const false, ⟨0, by omega⟩, ?_⟩, ?_, ?_, ?_⟩⟩
  · intro i j hj
    simp [Gate.refs] at hj
  · simp
  · exact ⟨fun _ => 0, fun _ => le_refl 0, fun i j hj => by simp [Gate.refs] at hj⟩
  · exact fun x => ⟨fun _ => false, fun i => rfl, rfl⟩

end CS

import RequestProject.Circuits

/-!
# Low degree functions on the Boolean cube over `ZMod 3`

We encode a bit `b` by `sgn b = ±1 ∈ ZMod 3` and consider the monomial functions
`mon S x = ∏ i ∈ S, sgn (x i)`.  Since `sgn b ^ 2 = 1`, these `2 ^ n` functions
span the whole space of functions `Cube n → ZMod 3`, and multiplication of
monomials corresponds to symmetric difference of index sets.

`Deg n D` is the space of functions spanned by monomials of degree at most `D`;
it plays the role of "polynomials of total degree ≤ D" over the cube.
-/

namespace CS

open Finset

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

variable {n : ℕ}

/-- The `±1` encoding of a bit inside `ZMod 3`. -/
def sgn (b : Bool) : ZMod 3 := if b then -1 else 1

/-- The `0/1` encoding of a bit inside `ZMod 3`. -/
def bit (b : Bool) : ZMod 3 := if b then 1 else 0

@[simp] lemma sgn_false : sgn false = 1 := rfl
@[simp] lemma sgn_true : sgn true = -1 := rfl
@[simp] lemma bit_false : bit false = 0 := rfl
@[simp] lemma bit_true : bit true = 1 := rfl

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> decide

lemma sgn_eq_one_add_bit (b : Bool) : sgn b = 1 + bit b := by cases b <;> decide

lemma bit_not (b : Bool) : bit (!b) = 1 - bit b := by cases b <;> decide

lemma bit_eq_zero_or_one (b : Bool) : bit b = 0 ∨ bit b = 1 := by cases b <;> simp

/-- The monomial function attached to a set of coordinates. -/
def mon (S : Finset (Fin n)) : Cube n → ZMod 3 := fun x => ∏ i ∈ S, sgn (x i)

@[simp] lemma mon_empty : mon (∅ : Finset (Fin n)) = 1 := by
  funext x; simp [mon]

/-- Functions of degree at most `D` on the cube. -/
def Deg (n D : ℕ) : Submodule (ZMod 3) (Cube n → ZMod 3) :=
  Submodule.span (ZMod 3) {f | ∃ S : Finset (Fin n), S.card ≤ D ∧ f = mon S}

lemma mon_mem_Deg {S : Finset (Fin n)} {D : ℕ} (h : S.card ≤ D) : mon S ∈ Deg n D :=
  Submodule.subset_span ⟨S, h, rfl⟩

lemma Deg_mono {D E : ℕ} (h : D ≤ E) : Deg n D ≤ Deg n E := by
  refine Submodule.span_mono ?_
  rintro f ⟨S, hS, rfl⟩
  exact ⟨S, hS.trans h, rfl⟩

lemma one_mem_Deg (D : ℕ) : (1 : Cube n → ZMod 3) ∈ Deg n D := by
  simpa using mon_mem_Deg (S := (∅ : Finset (Fin n))) (D := D) (by simp)

lemma const_mem_Deg (a : ZMod 3) (D : ℕ) : (fun _ => a : Cube n → ZMod 3) ∈ Deg n D := by
  have : (fun _ => a : Cube n → ZMod 3) = a • (1 : Cube n → ZMod 3) := by
    funext x; simp
  rw [this]
  exact Submodule.smul_mem _ _ (one_mem_Deg D)

lemma mon_mul (S T : Finset (Fin n)) : mon S * mon T = mon (symmDiff S T) := by
  funext x
  have hsub : S ∩ T ⊆ S ∪ T := inter_subset_union
  have h1 : ((S ∪ T) \ (S ∩ T)) = symmDiff S T := (symmDiff_eq_sup_sdiff_inf S T).symm
  have h2 : (∏ i ∈ symmDiff S T, sgn (x i)) * (∏ i ∈ S ∩ T, sgn (x i))
      = ∏ i ∈ S ∪ T, sgn (x i) := by
    rw [← h1]; exact Finset.prod_sdiff hsub
  have h3 := Finset.prod_union_inter (s₁ := S) (s₂ := T) (f := fun i => sgn (x i))
  simp only [mon, Pi.mul_apply]
  rw [← h3, ← h2]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  simp [sgn_mul_self]

lemma card_symmDiff_le (S T : Finset (Fin n)) :
    (symmDiff S T).card ≤ S.card + T.card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le S T)
  exact (symmDiff_le_sup : symmDiff S T ≤ S ⊔ T)

lemma Deg_mul {D E : ℕ} {p q : Cube n → ZMod 3} (hp : p ∈ Deg n D) (hq : q ∈ Deg n E) :
    p * q ∈ Deg n (D + E) := by
  induction hp using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, rfl⟩ := hf
      induction hq using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨T, hT, rfl⟩ := hg
          rw [mon_mul]
          exact mon_mem_Deg (le_trans (card_symmDiff_le S T) (Nat.add_le_add hS hT))
      | zero => simp
      | add g1 g2 _ _ ih1 ih2 => rw [mul_add]; exact Submodule.add_mem _ ih1 ih2
      | smul a g _ ih =>
          have : mon S * (a • g) = a • (mon S * g) := by
            funext x; simp [mul_comm, mul_left_comm]
          rw [this]; exact Submodule.smul_mem _ _ ih
  | zero => simp
  | add f1 f2 _ _ ih1 ih2 => rw [add_mul]; exact Submodule.add_mem _ ih1 ih2
  | smul a f _ ih =>
      have : (a • f) * q = a • (f * q) := by funext x; simp [mul_assoc]
      rw [this]; exact Submodule.smul_mem _ _ ih

lemma Deg_prod {ι : Type*} (s : Finset ι) (f : ι → Cube n → ZMod 3) (D : ℕ)
    (h : ∀ i ∈ s, f i ∈ Deg n D) : (∏ i ∈ s, f i) ∈ Deg n (s.card * D) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one_mem_Deg 0
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_mul, one_mul, add_comm]
      exact Deg_mul (h a (by simp)) (ih (fun i hi => h i (by simp [hi])))

/-- The delta function at a point of the cube. -/
def delta (a : Cube n) : Cube n → ZMod 3 := fun x => ∏ i, (2 + 2 * sgn (a i) * sgn (x i))

lemma delta_apply (a x : Cube n) : delta a x = if x = a then 1 else 0 := by
  unfold delta
  by_cases h : x = a
  · subst h
    rw [if_pos rfl]
    refine Finset.prod_eq_one (fun i _ => ?_)
    have := sgn_mul_self (x i)
    calc 2 + 2 * sgn (x i) * sgn (x i) = 2 + 2 * (sgn (x i) * sgn (x i)) := by ring
    _ = 1 := by rw [this]; decide
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ a i := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have : sgn (a i) * sgn (x i) = -1 := by
      cases hxa : a i <;> cases hxx : x i <;> simp_all
    calc 2 + 2 * sgn (a i) * sgn (x i) = 2 + 2 * (sgn (a i) * sgn (x i)) := by ring
    _ = 0 := by rw [this]; decide

lemma delta_mem_Deg (a : Cube n) : delta a ∈ Deg n n := by
  have h : ∀ i : Fin n, (fun x : Cube n => 2 + 2 * sgn (a i) * sgn (x i)) ∈ Deg n 1 := by
    intro i
    have : (fun x : Cube n => 2 + 2 * sgn (a i) * sgn (x i))
        = (fun _ => (2 : ZMod 3)) + (2 * sgn (a i)) • mon ({i} : Finset (Fin n)) := by
      funext x; simp [mon, mul_assoc]
    rw [this]
    exact Submodule.add_mem _ (const_mem_Deg _ _)
      (Submodule.smul_mem _ _ (mon_mem_Deg (by simp)))
  have heq : delta a = ∏ i : Fin n, (fun x : Cube n => 2 + 2 * sgn (a i) * sgn (x i)) := by
    funext x; rw [Finset.prod_apply]; rfl
  rw [heq]
  have := Deg_prod (Finset.univ : Finset (Fin n)) _ 1 (fun i _ => h i)
  simpa [Finset.card_univ] using this

lemma Deg_top_eq : Deg n n = ⊤ := by
  refine eq_top_iff.mpr (fun f _ => ?_)
  have hf : f = ∑ a : Cube n, f a • delta a := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, delta_apply, smul_eq_mul]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [hf]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (delta_mem_Deg a))

/-- The full monomial computes the parity of the input in the `±1` encoding. -/
lemma mon_univ_eq_sgn_parity (x : Cube n) :
    mon (Finset.univ : Finset (Fin n)) x = sgn (parity n x) := by
  classical
  have h1 : mon (Finset.univ : Finset (Fin n)) x
      = ∏ i ∈ Finset.univ.filter (fun i => x i = true), sgn (x i) := by
    unfold mon
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => x i = true)]
    have : ∏ i ∈ Finset.univ.filter (fun i => ¬ (x i = true)), sgn (x i) = 1 := by
      refine Finset.prod_eq_one (fun i hi => ?_)
      simp only [Finset.mem_filter, Bool.not_eq_true] at hi
      simp [hi.2]
    rw [this, mul_one]
  rw [h1]
  have h2 : ∏ i ∈ Finset.univ.filter (fun i => x i = true), sgn (x i)
      = (-1 : ZMod 3) ^ (Finset.univ.filter (fun i => x i = true)).card := by
    rw [Finset.prod_congr rfl (fun i hi => ?_), Finset.prod_const]
    simp only [Finset.mem_filter] at hi
    simp [hi.2]
  rw [h2]
  unfold parity sgn
  by_cases h : Odd (Finset.univ.filter (fun i => x i = true)).card
  · simp [h, h.neg_one_pow]
  · rw [Nat.not_odd_iff_even] at h
    simp [Nat.not_odd_iff_even.mpr h, h.neg_one_pow]

end CS

import RequestProject.Degree

/-!
# Approximating an OR gate by a low degree polynomial

Razborov–Smolensky's probabilistic construction: an unbounded fan-in OR of
inputs `z_j ∈ {0,1}` is approximated over `ZMod 3` by

  `1 - ∏_{r < ℓ} (1 - (∑_{j ∈ s ∩ T r} z_j)^2)`

for random subsets `T r`.  This is exact when all `z_j = 0`, and fails with
probability at most `2^{-ℓ}` otherwise.  Everything is done by counting.
-/

namespace CS

open Finset

variable {n m : ℕ}

lemma zmod3_one_sub_sq_of_ne_zero (a : ZMod 3) (h : a ≠ 0) : 1 - a ^ 2 = 0 := by
  revert h; revert a; decide

lemma zmod3_one_sub_sq_of_eq_zero (a : ZMod 3) (h : a = 0) : 1 - a ^ 2 = 1 := by
  subst h; norm_num

/-- Halving lemma: if some coefficient in `s` equals `1`, then at most half of
all subsets `U` make `∑_{j ∈ s ∩ U} z j` vanish. -/
lemma card_subsets_sum_zero_le (s : Finset (Fin m)) (z : Fin m → ZMod 3)
    (j₀ : Fin m) (hj₀ : j₀ ∈ s) (hz : z j₀ = 1) :
    2 * ((Finset.univ : Finset (Finset (Fin m))).filter
      (fun U => ∑ j ∈ s ∩ U, z j = 0)).card ≤ 2 ^ m := by
  classical
  set F0 := (Finset.univ : Finset (Finset (Fin m))).filter (fun U => ∑ j ∈ s ∩ U, z j = 0) with hF0
  set F1 := (Finset.univ : Finset (Finset (Fin m))).filter (fun U => ¬ (∑ j ∈ s ∩ U, z j = 0))
    with hF1
  have hsum : F0.card + F1.card = 2 ^ m := by
    rw [hF0, hF1, Finset.card_filter_add_card_filter_not]
    simp [Finset.card_univ, Fintype.card_finset]
  have hinj : F0.card ≤ F1.card := by
    refine Finset.card_le_card_of_injOn (fun U => symmDiff U {j₀}) ?_ ?_
    · intro U hU
      simp only [Finset.mem_coe, hF0, Finset.mem_filter, Finset.mem_univ, true_and] at hU
      simp only [Finset.mem_coe, hF1, Finset.mem_filter, Finset.mem_univ, true_and]
      show ¬ (∑ j ∈ s ∩ symmDiff U {j₀}, z j = 0)
      by_cases hjU : j₀ ∈ U
      · have hset : s ∩ symmDiff U {j₀} = (s ∩ U).erase j₀ := by
          ext i
          simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton,
            Finset.mem_erase]
          constructor
          · rintro ⟨his, h⟩
            rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨h2, his, h1⟩
            · exact absurd hjU (h1 ▸ h2)
          · rintro ⟨hne, his, hiU⟩
            exact ⟨his, Or.inl ⟨hiU, hne⟩⟩
        rw [hset]
        have hmem : j₀ ∈ s ∩ U := Finset.mem_inter.mpr ⟨hj₀, hjU⟩
        have := Finset.add_sum_erase _ z hmem
        rw [hU, hz] at this
        intro hc
        rw [hc, add_zero] at this
        exact absurd this.symm (by decide)
      · have hset : s ∩ symmDiff U {j₀} = insert j₀ (s ∩ U) := by
          ext i
          simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton,
            Finset.mem_insert]
          constructor
          · rintro ⟨his, h⟩
            rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inr ⟨his, h1⟩
            · exact Or.inl h1
          · rintro (rfl | ⟨his, hiU⟩)
            · exact ⟨hj₀, Or.inr ⟨rfl, hjU⟩⟩
            · exact ⟨his, Or.inl ⟨hiU, by rintro rfl; exact hjU hiU⟩⟩
        rw [hset, Finset.sum_insert (by simp [hjU]), hU, hz, add_zero]
        decide
    · intro U _ V _ h
      have h' : symmDiff U {j₀} = symmDiff V {j₀} := h
      have h2 : symmDiff (symmDiff U {j₀}) {j₀} = symmDiff (symmDiff V {j₀}) {j₀} := by rw [h']
      simpa [symmDiff_assoc] using h2
  omega

/-- The number of tuples all of whose entries satisfy `P`. -/
lemma card_filter_pi {ℓ : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin ℓ → α)).filter (fun T => ∀ r, P (T r))).card
      = ((Finset.univ : Finset α).filter P).card ^ ℓ := by
  classical
  have : ((Finset.univ : Finset (Fin ℓ → α)).filter (fun T => ∀ r, P (T r)))
      = Fintype.piFinset (fun _ : Fin ℓ => (Finset.univ : Finset α).filter P) := by
    ext T
    simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]
  simp

lemma card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]

/-- **Approximation of an OR gate.**  Given low degree approximations `p j` of
the inputs `w · j` which are correct on `G`, there is a low degree function `q`
correct on `G` outside an exceptional set `E` of density at most `2^{-ℓ}`. -/
theorem or_approx (ℓ D : ℕ) (G : Finset (Cube n))
    (s : Finset (Fin m)) (p : Fin m → Cube n → ZMod 3) (w : Cube n → Fin m → Bool)
    (hp : ∀ j ∈ s, p j ∈ Deg n D)
    (hpw : ∀ j ∈ s, ∀ x ∈ G, p j x = bit (w x j)) :
    ∃ q : Cube n → ZMod 3, q ∈ Deg n (2 * ℓ * D) ∧ ∃ E : Finset (Cube n),
      2 ^ ℓ * E.card ≤ 2 ^ n ∧
      ∀ x ∈ G, x ∉ E → q x = bit (decide (∃ j ∈ s, w x j = true)) := by
  classical
  set Q : (Fin ℓ → Finset (Fin m)) → Cube n → ZMod 3 :=
    fun T => 1 - ∏ r : Fin ℓ, (1 - (∑ j ∈ s ∩ T r, p j) ^ 2) with hQ
  -- degree bound
  have hQdeg : ∀ T, Q T ∈ Deg n (2 * ℓ * D) := by
    intro T
    have h1 : ∀ r : Fin ℓ, (1 - (∑ j ∈ s ∩ T r, p j) ^ 2 : Cube n → ZMod 3) ∈ Deg n (2 * D) := by
      intro r
      have hsum : (∑ j ∈ s ∩ T r, p j) ∈ Deg n D :=
        Submodule.sum_mem _ (fun j hj => hp j (Finset.mem_of_mem_inter_left hj))
      have hsq : ((∑ j ∈ s ∩ T r, p j) ^ 2 : Cube n → ZMod 3) ∈ Deg n (D + D) := by
        rw [sq]; exact Deg_mul hsum hsum
      have h := Submodule.sub_mem _ (one_mem_Deg (D + D)) hsq
      rwa [← two_mul] at h
    have h2 := Deg_prod (Finset.univ : Finset (Fin ℓ))
      (fun r => 1 - (∑ j ∈ s ∩ T r, p j) ^ 2) (2 * D) (fun r _ => h1 r)
    have hc : (Finset.univ : Finset (Fin ℓ)).card * (2 * D) = 2 * ℓ * D := by
      rw [Finset.card_univ, Fintype.card_fin]; ring
    rw [hc] at h2
    exact Submodule.sub_mem _ (one_mem_Deg _) h2
  -- value on `G`
  have hQval : ∀ T, ∀ x ∈ G,
      Q T x = 1 - ∏ r : Fin ℓ, (1 - (∑ j ∈ s ∩ T r, bit (w x j)) ^ 2) := by
    intro T x hx
    simp only [hQ, Pi.sub_apply, Pi.one_apply, Finset.prod_apply, Pi.pow_apply,
      Finset.sum_apply]
    congr 1
    refine Finset.prod_congr rfl (fun r _ => ?_)
    congr 2
    exact Finset.sum_congr rfl (fun j hj => hpw j (Finset.mem_of_mem_inter_left hj) x hx)
  set Bad : (Fin ℓ → Finset (Fin m)) → Finset (Cube n) := fun T =>
    G.filter (fun x => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)
    with hBad
  have hgood : ∀ T, ∀ x ∈ G, x ∉ Bad T → Q T x = bit (decide (∃ j ∈ s, w x j = true)) := by
    intro T x hxG hxB
    rw [hQval T x hxG]
    by_cases hex : ∃ j ∈ s, w x j = true
    · have hne : ∃ r, (∑ j ∈ s ∩ T r, bit (w x j)) ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hxB (Finset.mem_filter.mpr ⟨hxG, hex, hc⟩)
      obtain ⟨r, hr⟩ := hne
      have hzero : ∏ r : Fin ℓ, (1 - (∑ j ∈ s ∩ T r, bit (w x j)) ^ 2) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ r) (zmod3_one_sub_sq_of_ne_zero _ hr)
      rw [hzero, sub_zero]
      simp [hex, bit]
    · have hz : ∀ r : Fin ℓ, (∑ j ∈ s ∩ T r, bit (w x j)) = 0 := by
        intro r
        refine Finset.sum_eq_zero (fun j hj => ?_)
        have hne : w x j ≠ true := fun h => hex ⟨j, Finset.mem_of_mem_inter_left hj, h⟩
        simp only [ne_eq, Bool.not_eq_true] at hne
        simp [hne, bit]
      have hone : ∏ r : Fin ℓ, (1 - (∑ j ∈ s ∩ T r, bit (w x j)) ^ 2) = 1 :=
        Finset.prod_eq_one (fun r _ => zmod3_one_sub_sq_of_eq_zero _ (hz r))
      rw [hone, sub_self]
      simp [hex, bit]
  -- counting: some `T` has a small bad set
  have hswap : ∑ T : (Fin ℓ → Finset (Fin m)), (Bad T).card
      = ∑ x ∈ G, ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
          (fun T => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)).card := by
    simp only [hBad, Finset.card_filter]
    rw [Finset.sum_comm]
  have hpt : ∀ x : Cube n, 2 ^ ℓ * ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
      (fun T => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)).card
      ≤ (2 ^ m) ^ ℓ := by
    intro x
    by_cases hex : ∃ j ∈ s, w x j = true
    · obtain ⟨j₀, hj₀s, hj₀⟩ := hex
      have hfe : ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
          (fun T => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0))
          = ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
          (fun T => ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)) := by
        apply Finset.filter_congr
        intro T _
        simp only [and_iff_right_iff_imp]
        exact fun _ => ⟨j₀, hj₀s, hj₀⟩
      have hcf : ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
          (fun T => ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)).card
          = ((Finset.univ : Finset (Finset (Fin m))).filter
            (fun U => ∑ j ∈ s ∩ U, bit (w x j) = 0)).card ^ ℓ :=
        card_filter_pi (fun U => ∑ j ∈ s ∩ U, bit (w x j) = 0)
      rw [hfe, hcf]
      have hhalf := card_subsets_sum_zero_le s (fun j => bit (w x j)) j₀ hj₀s (by simp [hj₀])
      calc 2 ^ ℓ * ((Finset.univ : Finset (Finset (Fin m))).filter
              (fun U => ∑ j ∈ s ∩ U, bit (w x j) = 0)).card ^ ℓ
          = (2 * ((Finset.univ : Finset (Finset (Fin m))).filter
              (fun U => ∑ j ∈ s ∩ U, bit (w x j) = 0)).card) ^ ℓ := by rw [mul_pow]
        _ ≤ (2 ^ m) ^ ℓ := Nat.pow_le_pow_left hhalf ℓ
    · have : ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
          (fun T => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr (fun T _ => ?_)
        simp only [not_and]
        exact fun h => absurd h hex
      simp [this]
  have hcard : ∑ T : (Fin ℓ → Finset (Fin m)), 2 ^ ℓ * (Bad T).card
      ≤ ∑ _T : (Fin ℓ → Finset (Fin m)), 2 ^ n := by
    rw [← Finset.mul_sum, hswap, Finset.mul_sum, Finset.sum_const, Finset.card_univ]
    have h1 : ∑ x ∈ G, 2 ^ ℓ * ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
        (fun T => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)).card
        ≤ ∑ _x ∈ G, (2 ^ m) ^ ℓ := Finset.sum_le_sum (fun x _ => hpt x)
    have h2 : G.card ≤ 2 ^ n := by
      have := Finset.card_le_card (Finset.subset_univ G)
      simpa [Finset.card_univ, card_cube] using this
    have h3 : Fintype.card (Fin ℓ → Finset (Fin m)) = (2 ^ m) ^ ℓ := by
      simp [Fintype.card_finset]
    rw [Finset.sum_const, smul_eq_mul] at h1
    rw [h3, smul_eq_mul]
    calc ∑ x ∈ G, 2 ^ ℓ * ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
        (fun T => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)).card
        ≤ G.card * (2 ^ m) ^ ℓ := h1
      _ ≤ 2 ^ n * (2 ^ m) ^ ℓ := Nat.mul_le_mul_right _ h2
      _ = (2 ^ m) ^ ℓ * 2 ^ n := by ring
  obtain ⟨T, -, hT⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty (α := Fin ℓ → Finset (Fin m))) hcard
  exact ⟨Q T, hQdeg T, Bad T, hT, hgood T⟩

end CS

import RequestProject.Degree

/-!
# The dimension argument

If a function of degree at most `D` agrees with the parity monomial
`mon univ` on a set `A ⊆ Cube n` (with `n = 2 * N`), then

  `|A| ≤ ∑_{k ≤ N + D} C(n, k)`.

This is the standard linear-algebraic step of Smolensky's argument: on `A`,
every monomial can be replaced by one of degree at most `N + D`, so the
`|A|`-dimensional space of all functions on `A` is spanned by that many
monomials.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The number of subsets of `Fin n` of size at most `K`. -/
lemma card_filter_card_le (n K : ℕ) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ K)).card
      ≤ ∑ k ∈ Finset.range (K + 1), n.choose k := by
  classical
  have hsub : (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ K)
      ⊆ (Finset.range (K + 1)).biUnion
          (fun k => Finset.powersetCard k (Finset.univ : Finset (Fin n))) := by
    intro S hS
    simp only [Finset.mem_filter] at hS
    refine Finset.mem_biUnion.mpr ⟨S.card, ?_, ?_⟩
    · simp only [Finset.mem_range]; omega
    · simp [Finset.mem_powersetCard]
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [Finset.card_powersetCard]
  simp

lemma finrank_Deg_le (n K : ℕ) :
    Module.finrank (ZMod 3) (Deg n K) ≤ ∑ k ∈ Finset.range (K + 1), n.choose k := by
  classical
  set gen : Finset (Cube n → ZMod 3) :=
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ K)).image mon with hgen
  have hset : (gen : Set (Cube n → ZMod 3)) = {f | ∃ S : Finset (Fin n), S.card ≤ K ∧ f = mon S} := by
    ext f
    simp only [hgen, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, hS, rfl⟩; exact ⟨S, hS, rfl⟩
    · rintro ⟨S, hS, rfl⟩; exact ⟨S, hS, rfl⟩
  have hspan : Deg n K = Submodule.span (ZMod 3) (gen : Set (Cube n → ZMod 3)) := by
    rw [Deg, hset]
  rw [hspan]
  refine le_trans (finrank_span_finset_le_card gen) ?_
  refine le_trans (Finset.card_image_le) (card_filter_card_le n K)

/-- **Smolensky's dimension bound.** -/
theorem card_le_of_approximates_parity {N D : ℕ} {n : ℕ} (hn : n = 2 * N)
    (A : Finset (Cube n)) (R : Cube n → ZMod 3) (hR : R ∈ Deg n D)
    (hA : ∀ x ∈ A, R x = mon (Finset.univ : Finset (Fin n)) x) :
    A.card ≤ ∑ k ∈ Finset.range (N + D + 1), n.choose k := by
  classical
  set K := N + D with hK
  set res : (Cube n → ZMod 3) →ₗ[ZMod 3] (↥A → ZMod 3) :=
    LinearMap.funLeft (ZMod 3) (ZMod 3) (fun a : ↥A => (a : Cube n)) with hres
  -- every monomial restricts into the image of `Deg n K`
  have hmon : ∀ S : Finset (Fin n), res (mon S) ∈ Submodule.map res (Deg n K) := by
    intro S
    by_cases hS : S.card ≤ K
    · exact Submodule.mem_map_of_mem (mon_mem_Deg hS)
    · push_neg at hS
      have hcompl : (Sᶜ).card ≤ N := by
        have hc : (Sᶜ).card = n - S.card := by
          rw [Finset.card_compl]; simp
        have hle : S.card ≤ n := by
          simpa using Finset.card_le_card (Finset.subset_univ S)
        omega
      have hmem : R * mon Sᶜ ∈ Deg n K := by
        refine Deg_mono (?_ : D + (Sᶜ).card ≤ K) (Deg_mul hR (mon_mem_Deg (le_refl _)))
        omega
      refine ⟨R * mon Sᶜ, hmem, ?_⟩
      funext a
      have ha : (a : Cube n) ∈ A := a.2
      simp only [hres, LinearMap.funLeft_apply, Pi.mul_apply]
      rw [hA _ ha]
      have : mon (Finset.univ : Finset (Fin n)) * mon Sᶜ = mon S := by
        rw [mon_mul]
        congr 1
        ext i
        simp [Finset.mem_symmDiff]
      calc mon (Finset.univ : Finset (Fin n)) (a : Cube n) * mon Sᶜ (a : Cube n)
          = (mon (Finset.univ : Finset (Fin n)) * mon Sᶜ) (a : Cube n) := rfl
        _ = mon S (a : Cube n) := by rw [this]
  -- hence the restriction map is surjective from `Deg n K`
  have htop : Submodule.map res (Deg n K) = ⊤ := by
    refine eq_top_iff.mpr (fun g hg => ?_)
    clear hg
    obtain ⟨f, rfl⟩ : ∃ f, res f = g := by
      refine ⟨fun x => if h : ∃ a : ↥A, (a : Cube n) = x then g h.choose else 0, ?_⟩
      funext a
      have hex : ∃ b : ↥A, (b : Cube n) = (a : Cube n) := ⟨a, rfl⟩
      simp only [hres, LinearMap.funLeft_apply, dif_pos hex]
      congr 1
      exact Subtype.ext hex.choose_spec
    have hfmem : f ∈ Deg n n := by rw [Deg_top_eq]; trivial
    clear_value res
    induction hfmem using Submodule.span_induction with
    | mem h hh =>
        obtain ⟨S, _, rfl⟩ := hh
        exact hmon S
    | zero => simp
    | add f1 f2 _ _ ih1 ih2 => rw [map_add]; exact Submodule.add_mem _ ih1 ih2
    | smul a f _ ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih
  -- dimension count
  have h1 : Module.finrank (ZMod 3) (↥A → ZMod 3) = A.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have h2 : Module.finrank (ZMod 3) (Submodule.map res (Deg n K))
      ≤ Module.finrank (ZMod 3) (Deg n K) := Submodule.finrank_map_le _ _
  rw [htop] at h2
  rw [finrank_top] at h2
  rw [h1] at h2
  exact le_trans h2 (finrank_Deg_le n K)

end CS

import Mathlib
import RequestProject.Approx
import RequestProject.Smolensky
import RequestProject.Binomial
import RequestProject.Universality

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
`PARITY ∉ AC⁰`.

The proof is the polynomial method of Razborov and Smolensky: every `AC⁰`
circuit of depth `d` and size `s` agrees, outside a set of at most `s · 2^{n-ℓ}`
inputs, with a function of degree `(2ℓ)^d` over `ZMod 3`
(`CS.circuit_approx`); but a function of degree `D` can agree with parity only
on a set of at most `∑_{k ≤ n/2 + D} C(n,k)` inputs (`CS.card_le_of_approximates_parity`).
Choosing `ℓ` polylogarithmically in `n` makes these two facts contradictory.

Note: the module docstring required by the task statement is placed just below
the `import` lines, since Lean 4 requires `import` commands to come first in a
file.
-/

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

set_option grind.warning false

namespace CS

open Finset

/-- **Quantitative lower bound.** No circuit of depth `d` and size `s ≤ 2^ℓ / 4`
computes parity on `2N` bits, as soon as `64 · ((2ℓ)^d + 1)^2 ≤ 3N + 1`. -/
theorem parity_lower_bound (N ℓ d : ℕ) (hℓ : 0 < ℓ)
    (hbig : 64 * ((2 * ℓ) ^ d + 1) ^ 2 ≤ 3 * N + 1)
    (c : Circuit (2 * N)) (hd : c.DepthLe d) (hcomp : c.Computes (parity (2 * N)))
    (hsize : 4 * c.size ≤ 2 ^ ℓ) : False := by
  classical
  set D := (2 * ℓ) ^ d with hDdef
  obtain ⟨q, hqd, B, hB, hqv⟩ := circuit_approx c d ℓ hℓ hd
  set A : Finset (Cube (2 * N)) := Finset.univ \ B with hA
  have hBsub : B ⊆ Finset.univ := Finset.subset_univ B
  have hAcard : A.card = 2 ^ (2 * N) - B.card := by
    rw [hA, Finset.card_univ_diff, card_cube]
  have hBle : B.card ≤ 2 ^ (2 * N) := by
    have := Finset.card_le_card hBsub
    rwa [Finset.card_univ, card_cube] at this
  -- the low degree function agreeing with parity on `A`
  set R : Cube (2 * N) → ZMod 3 := (fun _ => 1) + q with hR
  have hRd : R ∈ Deg (2 * N) D := Submodule.add_mem _ (const_mem_Deg _ _) hqd
  have hRA : ∀ x ∈ A, R x = mon (Finset.univ : Finset (Fin (2 * N))) x := by
    intro x hx
    have hxB : x ∉ B := (Finset.mem_sdiff.mp hx).2
    have hval := hqv x hxB
    rw [c.computes_value hcomp x] at hval
    simp only [hR, Pi.add_apply, hval]
    rw [mon_univ_eq_sgn_parity, sgn_eq_one_add_bit]
  have hsmol := card_le_of_approximates_parity (N := N) (D := D) rfl A R hRd hRA
  -- the exceptional set is small
  have h1 : 4 * B.card ≤ 2 ^ (2 * N) := by
    have hpos : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc 2 ^ ℓ * (4 * B.card) = 4 * (2 ^ ℓ * B.card) := by ring
      _ ≤ 4 * (c.size * 2 ^ (2 * N)) := Nat.mul_le_mul_left _ hB
      _ = (4 * c.size) * 2 ^ (2 * N) := by ring
      _ ≤ 2 ^ ℓ * 2 ^ (2 * N) := Nat.mul_le_mul_right _ hsize
  -- the central binomial coefficient is small
  have h2 : 8 * ((D + 1) * (2 * N).choose N) ≤ 2 ^ (2 * N) := by
    have hcb : ((2 * N).choose N) ^ 2 * (3 * N + 1) ≤ 16 ^ N := centralBinom_sq_mul_le N
    have hsq : (8 * ((D + 1) * (2 * N).choose N)) ^ 2 ≤ (2 ^ (2 * N)) ^ 2 := by
      have e1 : (8 * ((D + 1) * (2 * N).choose N)) ^ 2
          = (64 * (D + 1) ^ 2) * ((2 * N).choose N) ^ 2 := by ring
      have e2 : (16 : ℕ) ^ N = (2 ^ (2 * N)) ^ 2 := by
        rw [← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
        ring_nf
      calc (8 * ((D + 1) * (2 * N).choose N)) ^ 2
          = (64 * (D + 1) ^ 2) * ((2 * N).choose N) ^ 2 := e1
        _ ≤ (3 * N + 1) * ((2 * N).choose N) ^ 2 := Nat.mul_le_mul_right _ hbig
        _ = ((2 * N).choose N) ^ 2 * (3 * N + 1) := by ring
        _ ≤ 16 ^ N := hcb
        _ = (2 ^ (2 * N)) ^ 2 := e2
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hsq
  have h3 := sum_range_choose_le N D
  have h4 : 0 < 2 ^ (2 * N) := Nat.two_pow_pos _
  omega

/-- If `ℓ ^ k` is eventually dominated by `2 ^ ℓ`. -/
lemma exists_pow_lt_two_pow (k : ℕ) : ∃ L : ℕ, ∀ ℓ, L ≤ ℓ → ℓ ^ k < 2 ^ ℓ := by
  have h2 := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k (r := 2) (by norm_num)).def
    (c := 1 / 2) (by norm_num)
  rw [Filter.eventually_atTop] at h2
  obtain ⟨L, hL⟩ := h2
  refine ⟨L, fun l hl => ?_⟩
  have hl' := hL l hl
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ k),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ l)] at hl'
  have : ((l : ℝ) ^ k) < 2 ^ l := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) l]
  exact_mod_cast this

/-- **PARITY is not in `AC⁰`.** -/
theorem parity_not_ac0 : ¬ InAC0 parity := by
  rintro ⟨d, cx, hfam⟩
  -- choose ℓ large enough
  obtain ⟨L, hL⟩ := exists_pow_lt_two_pow (2 * d * cx + 1)
  set K : ℕ := 4 * 514 ^ cx * 2 ^ (2 * d * cx) with hK
  set ℓ : ℕ := max (max L 1) K with hℓdef
  have hℓ1 : 0 < ℓ := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right L 1) (le_max_left _ _))
  have hℓL : L ≤ ℓ := le_trans (le_max_left L 1) (le_max_left _ _)
  have hℓK : K ≤ ℓ := le_max_right _ _
  set D : ℕ := (2 * ℓ) ^ d with hD
  have hD1 : 1 ≤ D := Nat.one_le_pow _ _ (by omega)
  set N : ℕ := 64 * (D + 1) ^ 2 with hN
  obtain ⟨c, hcsize, hcd, hccomp⟩ := hfam (2 * N)
  refine parity_lower_bound N ℓ d hℓ1 (by rw [← hD, hN]; omega) c hcd hccomp ?_
  -- the size bound is much smaller than `2 ^ ℓ`
  have hstep1 : 2 * N + 2 ≤ 514 * D ^ 2 := by
    have : (D + 1) ^ 2 ≤ 4 * D ^ 2 := by nlinarith
    have h2 : 1 ≤ D ^ 2 := Nat.one_le_pow _ _ (by omega)
    simp only [hN]
    nlinarith
  have hstep2 : (2 * N + 2) ^ cx ≤ 514 ^ cx * (2 ^ (2 * d * cx) * ℓ ^ (2 * d * cx)) := by
    have hDsq : D ^ 2 = 2 ^ (2 * d) * ℓ ^ (2 * d) := by
      rw [hD, ← pow_mul, mul_pow]
      rw [show d * 2 = 2 * d by ring]
    calc (2 * N + 2) ^ cx ≤ (514 * D ^ 2) ^ cx := Nat.pow_le_pow_left hstep1 cx
      _ = 514 ^ cx * (D ^ 2) ^ cx := by rw [mul_pow]
      _ = 514 ^ cx * ((2 ^ (2 * d)) ^ cx * (ℓ ^ (2 * d)) ^ cx) := by rw [hDsq, mul_pow]
      _ = 514 ^ cx * (2 ^ (2 * d * cx) * ℓ ^ (2 * d * cx)) := by
            rw [← pow_mul, ← pow_mul]
  have hfin : 4 * c.size ≤ ℓ ^ (2 * d * cx + 1) := by
    calc 4 * c.size ≤ 4 * (2 * N + 2) ^ cx := Nat.mul_le_mul_left _ hcsize
      _ ≤ 4 * (514 ^ cx * (2 ^ (2 * d * cx) * ℓ ^ (2 * d * cx))) := Nat.mul_le_mul_left _ hstep2
      _ = K * ℓ ^ (2 * d * cx) := by rw [hK]; ring
      _ ≤ ℓ * ℓ ^ (2 * d * cx) := Nat.mul_le_mul_right _ hℓK
      _ = ℓ ^ (2 * d * cx + 1) := by rw [pow_succ]; ring
  exact le_of_lt (lt_of_le_of_lt hfin (hL ℓ hℓL))

end CS

import Mathlib

/-!
# Binomial coefficient estimates

Two elementary estimates used to bound the number of low degree monomials:

* `CS.centralBinom_sq_mul_le`: `C(2N, N)^2 * (3N+1) ≤ 16^N`, i.e.
  `C(2N,N) ≤ 4^N / √(3N+1)`, proved by induction;
* `CS.two_mul_sum_range_choose_le`: `2 * ∑_{k < N} C(2N, k) ≤ 4^N`.
-/

namespace CS

open Finset

lemma centralBinom_sq_mul_le (N : ℕ) :
    (Nat.centralBinom N) ^ 2 * (3 * N + 1) ≤ 16 ^ N := by
  induction N with
  | zero => simp [Nat.centralBinom]
  | succ N ih =>
    have hrec := Nat.succ_mul_centralBinom_succ N
    set a := Nat.centralBinom N with ha
    set b := Nat.centralBinom (N + 1) with hb
    have hpos : 0 < (N + 1) ^ 2 := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    have key : (N + 1) ^ 2 * (b ^ 2 * (3 * (N + 1) + 1))
        = ((N + 1) * b) ^ 2 * (3 * N + 4) := by ring
    rw [key, hrec]
    have h1 : (2 * (2 * N + 1) * a) ^ 2 * (3 * N + 4)
        = ((2 * N + 1) ^ 2 * (3 * N + 4)) * (4 * a ^ 2) := by ring
    have h2 : (2 * N + 1) ^ 2 * (3 * N + 4) ≤ 4 * (N + 1) ^ 2 * (3 * N + 1) := by nlinarith
    calc (2 * (2 * N + 1) * a) ^ 2 * (3 * N + 4)
        = ((2 * N + 1) ^ 2 * (3 * N + 4)) * (4 * a ^ 2) := h1
      _ ≤ (4 * (N + 1) ^ 2 * (3 * N + 1)) * (4 * a ^ 2) := Nat.mul_le_mul_right _ h2
      _ = 16 * (N + 1) ^ 2 * (a ^ 2 * (3 * N + 1)) := by ring
      _ ≤ 16 * (N + 1) ^ 2 * 16 ^ N := Nat.mul_le_mul_left _ ih
      _ = (N + 1) ^ 2 * 16 ^ (N + 1) := by ring

lemma two_mul_sum_range_choose_le (N : ℕ) :
    2 * (∑ k ∈ Finset.range N, (2 * N).choose k) ≤ 4 ^ N := by
  classical
  have hsymm : (∑ k ∈ Finset.range N, (2 * N).choose k)
      = ∑ k ∈ Finset.Ico (N + 1) (2 * N + 1), (2 * N).choose k := by
    refine Finset.sum_nbij' (fun k => 2 * N - k) (fun k => 2 * N - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ico]
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      show 2 * N - (2 * N - k) = k
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      show 2 * N - (2 * N - k) = k
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      rw [Nat.choose_symm (by omega)]
  have htot : ∑ k ∈ Finset.range (2 * N + 1), (2 * N).choose k = 2 ^ (2 * N) :=
    Nat.sum_range_choose (2 * N)
  have hsplit : ∑ k ∈ Finset.range (2 * N + 1), (2 * N).choose k
      = (∑ k ∈ Finset.range N, (2 * N).choose k) + (2 * N).choose N
        + ∑ k ∈ Finset.Ico (N + 1) (2 * N + 1), (2 * N).choose k := by
    have h1 : Finset.range (2 * N + 1) = Finset.range (N + 1) ∪ Finset.Ico (N + 1) (2 * N + 1) := by
      ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range (N + 1)) (Finset.Ico (N + 1) (2 * N + 1)) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ico] at hk'
      omega
    rw [h1, Finset.sum_union hdisj, Finset.sum_range_succ]
  have h4 : (4 : ℕ) ^ N = 2 ^ (2 * N) := by
    rw [pow_mul]; norm_num
  omega

/-- The number of subsets of a `2N`-element set of size at most `N + D`,
bounded via the central binomial coefficient. -/
lemma sum_range_choose_le (N D : ℕ) :
    (∑ k ∈ Finset.range (N + D + 1), (2 * N).choose k)
      ≤ 2 ^ (2 * N) / 2 + (D + 1) * (2 * N).choose N := by
  classical
  have hsplit : ∑ k ∈ Finset.range (N + D + 1), (2 * N).choose k
      = (∑ k ∈ Finset.range N, (2 * N).choose k)
        + ∑ k ∈ Finset.Ico N (N + D + 1), (2 * N).choose k := by
    have h1 : Finset.range (N + D + 1) = Finset.range N ∪ Finset.Ico N (N + D + 1) := by
      ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range N) (Finset.Ico N (N + D + 1)) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ico] at hk'
      omega
    rw [h1, Finset.sum_union hdisj]
  have hlow : 2 * (∑ k ∈ Finset.range N, (2 * N).choose k) ≤ 2 ^ (2 * N) := by
    have := two_mul_sum_range_choose_le N
    have h4 : (4 : ℕ) ^ N = 2 ^ (2 * N) := by rw [pow_mul]; norm_num
    omega
  have hhigh : (∑ k ∈ Finset.Ico N (N + D + 1), (2 * N).choose k)
      ≤ (D + 1) * (2 * N).choose N := by
    have hb : ∀ k ∈ Finset.Ico N (N + D + 1), (2 * N).choose k ≤ (2 * N).choose N := by
      intro k _
      have := Nat.choose_le_middle k (2 * N)
      simpa [Nat.mul_div_cancel_left] using this
    have h := Finset.sum_le_card_nsmul (Finset.Ico N (N + D + 1)) _ ((2 * N).choose N) hb
    rw [Nat.card_Ico, smul_eq_mul] at h
    have hc : N + D + 1 - N = D + 1 := by omega
    rwa [hc] at h
  omega

end CS

import Mathlib

/-!
# Boolean circuits of bounded depth (AC⁰)

A circuit over `n` input variables is a directed acyclic graph of gates.  We
represent it as a finite list of gates `gate : Fin size → Gate n size`, where the
gate at index `i` may only refer to gates at strictly smaller indices (`wf`).
Gates are `const`, `var`, `not`, unbounded fan-in `and` and unbounded fan-in `or`.

The semantics is given by the fixed-point predicate `Circuit.Vals`, which has a
unique solution for every input (`Circuit.vals_unique`, `Circuit.exists_vals`).

The depth of a circuit is measured by *AND/OR gates only* (negations are free),
via the existence of a level labelling; this is the standard notion, and gives
the strongest form of the lower bound.
-/

namespace CS

/-- The Boolean cube: assignments of the `n` input variables. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- A gate of a circuit with `n` inputs, whose predecessors are among `Fin m`. -/
inductive Gate (n m : ℕ) where
  | const (b : Bool)
  | var (i : Fin n)
  | not (j : Fin m)
  | and (s : Finset (Fin m))
  | or (s : Finset (Fin m))

/-- The set of gates a gate refers to. -/
def Gate.refs {n m : ℕ} : Gate n m → Finset (Fin m)
  | .const _ => ∅
  | .var _ => ∅
  | .not j => {j}
  | .and s => s
  | .or s => s

/-- The depth cost of a gate: `1` for AND/OR gates, `0` for negations,
constants and variables. -/
def Gate.cost {n m : ℕ} : Gate n m → ℕ
  | .const _ => 0
  | .var _ => 0
  | .not _ => 0
  | .and _ => 1
  | .or _ => 1

/-- The value of a gate, given the input `x` and the values `v` of all gates. -/
def Gate.eval {n m : ℕ} (x : Cube n) (v : Fin m → Bool) : Gate n m → Bool
  | .const b => b
  | .var i => x i
  | .not j => !(v j)
  | .and s => decide (∀ j ∈ s, v j = true)
  | .or s => decide (∃ j ∈ s, v j = true)

lemma Gate.eval_congr {n m : ℕ} (x : Cube n) (v w : Fin m → Bool) (g : Gate n m)
    (h : ∀ j ∈ g.refs, v j = w j) : g.eval x v = g.eval x w := by
  cases g with
  | const b => rfl
  | var i => rfl
  | not j => simp [Gate.eval, h j (by simp [Gate.refs])]
  | and s =>
      simp only [Gate.eval]
      congr 1
      exact propext ⟨fun H j hj => (h j hj) ▸ H j hj, fun H j hj => (h j hj).symm ▸ H j hj⟩
  | or s =>
      simp only [Gate.eval]
      congr 1
      refine propext ⟨fun ⟨j, hj, H⟩ => ⟨j, hj, (h j hj) ▸ H⟩,
        fun ⟨j, hj, H⟩ => ⟨j, hj, (h j hj).symm ▸ H⟩⟩

/-- A Boolean circuit with `n` inputs: `size` gates, topologically ordered. -/
structure Circuit (n : ℕ) where
  size : ℕ
  gate : Fin size → Gate n size
  out : Fin size
  wf : ∀ i j, j ∈ (gate i).refs → (j : ℕ) < (i : ℕ)

variable {n : ℕ}

/-- `v` is *the* vector of gate values of `c` on input `x`. -/
def Circuit.Vals (c : Circuit n) (x : Cube n) (v : Fin c.size → Bool) : Prop :=
  ∀ i, v i = (c.gate i).eval x v

/-- The values of all gates are uniquely determined. -/
lemma Circuit.vals_unique (c : Circuit n) (x : Cube n) {v w : Fin c.size → Bool}
    (hv : c.Vals x v) (hw : c.Vals x w) : v = w := by
  have key : ∀ k : ℕ, ∀ i : Fin c.size, (i : ℕ) < k → v i = w i := by
    intro k
    induction k with
    | zero => intro i hi; omega
    | succ k ih =>
      intro i hi
      rw [hv i, hw i]
      refine Gate.eval_congr x v w _ (fun j hj => ih j ?_)
      have := c.wf i j hj
      omega
  funext i
  exact key (i + 1) i (by omega)

lemma Circuit.exists_vals (c : Circuit n) (x : Cube n) : ∃ v, c.Vals x v := by
  suffices h : ∀ k : ℕ, ∃ v : Fin c.size → Bool,
      ∀ i : Fin c.size, (i : ℕ) < k → v i = (c.gate i).eval x v by
    obtain ⟨v, hv⟩ := h c.size
    exact ⟨v, fun i => hv i i.2⟩
  intro k
  induction k with
  | zero => exact ⟨fun _ => false, by intro i hi; omega⟩
  | succ k ih =>
    obtain ⟨v, hv⟩ := ih
    by_cases hk : k < c.size
    · refine ⟨Function.update v ⟨k, hk⟩ ((c.gate ⟨k, hk⟩).eval x v), ?_⟩
      intro i hi
      have key : ∀ (i : Fin c.size), (i : ℕ) ≤ k →
          (c.gate i).eval x (Function.update v ⟨k, hk⟩ ((c.gate ⟨k, hk⟩).eval x v))
            = (c.gate i).eval x v := by
        intro i hik
        refine Gate.eval_congr _ _ _ _ (fun j hj => ?_)
        have : (j : ℕ) < k := lt_of_lt_of_le (c.wf i j hj) hik
        exact Function.update_of_ne (by simp only [ne_eq, Fin.ext_iff]; omega) _ _
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
      · rw [Function.update_of_ne (by simp only [ne_eq, Fin.ext_iff]; omega), key i (le_of_lt h)]
        exact hv i h
      · have hik : i = ⟨k, hk⟩ := Fin.ext h
        rw [hik, Function.update_self, key ⟨k, hk⟩ (le_refl k)]
    · refine ⟨v, fun i hi => hv i ?_⟩
      have := i.2; omega

/-- The circuit `c` computes the Boolean function `f`. -/
def Circuit.Computes (c : Circuit n) (f : Cube n → Bool) : Prop :=
  ∀ x, ∃ v, c.Vals x v ∧ v c.out = f x

/-- The circuit has depth at most `d`, counting AND/OR gates only. -/
def Circuit.DepthLe (c : Circuit n) (d : ℕ) : Prop :=
  ∃ lev : Fin c.size → ℕ, (∀ i, lev i ≤ d) ∧
    ∀ i j, j ∈ (c.gate i).refs → lev j + (c.gate i).cost ≤ lev i

/-- The parity function on `n` bits. -/
def parity (n : ℕ) (x : Cube n) : Bool :=
  decide (Odd (Finset.univ.filter (fun i => x i = true)).card)

/-- A family of Boolean functions is in `AC⁰` if it is computed by circuits of
constant depth and polynomial size. -/
def InAC0 (f : ∀ n, Cube n → Bool) : Prop :=
  ∃ d c : ℕ, ∀ n : ℕ, ∃ C : Circuit n,
    C.size ≤ (n + 2) ^ c ∧ C.DepthLe d ∧ C.Computes (f n)

end CS

