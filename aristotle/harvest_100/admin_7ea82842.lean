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

/-
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module docstring, so the header above is
-- written as a plain block comment and repeated verbatim as a module docstring below.)

import RequestProject.RS.CircuitApprox
import RequestProject.RS.Smolensky
import RequestProject.RS.Binomial
import RequestProject.RS.Aux
import RequestProject.RS.Sanity

/-!
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Razborov–Smolensky theorem: for distinct primes `p` and `q`, the Boolean function `MOD p`
(which tests whether the number of `1`s in the input is divisible by `p`) is not computed by any
family of constant-depth, polynomial-size circuits with unbounded fan-in AND, OR, NOT and
`MOD q` gates, i.e. `MOD p ∉ AC⁰[q]`.

The proof combines
* `CS.RS.Circuit.exists_approx`: every `AC⁰[q]` circuit is approximated, on all but a small
  fraction of the inputs, by a low-degree function over a field of characteristic `q`;
* `CS.RS.smolensky_bound`: a low-degree function can agree with `x ↦ ζ^(weight x)` (for `ζ` a
  primitive `p`-th root of unity) only on a set of inputs of size at most
  `∑_{i ≤ n/2 + D} C(n,i)`;
* `CS.RS.modq_mem_AC0q`: a non-vacuity check, exhibiting `MOD q` itself as a depth-one,
  linear-size circuit family of this kind;
* binomial estimates showing that this is less than the number of inputs left over by the
  approximation step.
-/

namespace CS

open Finset CS.RS

/-- Shifting the weight by `(p - r) % p` detects the residue `r` modulo `p`. -/
lemma dvd_shift (p t r : ℕ) (hp : 0 < p) (hr : r < p) :
    p ∣ (t + (p - r) % p) ↔ r = t % p := by
  have hu : t % p < p := Nat.mod_lt _ hp
  have hdvd : ∀ v : ℕ, (p ∣ t + v) ↔ (p ∣ t % p + v) := by
    intro v
    have ht : t + v = p * (t / p) + (t % p + v) := by
      rw [← Nat.add_assoc, Nat.div_add_mod]
    rw [ht]
    exact Nat.dvd_add_right ⟨t / p, rfl⟩
  have hsmall : ∀ s : ℕ, s < 2 * p → (p ∣ s ↔ (s = 0 ∨ s = p)) := by
    intro s hs
    constructor
    · rintro ⟨k, rfl⟩
      have hk : k < 2 := by
        by_contra hcon
        push_neg at hcon
        have : p * 2 ≤ p * k := Nat.mul_le_mul_left _ hcon
        omega
      interval_cases k <;> simp
    · rintro (rfl | rfl) <;> simp
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp only [Nat.sub_zero, Nat.mod_self, Nat.add_zero]
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  · rw [Nat.mod_eq_of_lt (show p - r < p by omega), hdvd (p - r),
      hsmall (t % p + (p - r)) (by omega)]
    omega

/-- Summing the shifted indicators against powers of `ζ` reconstructs `ζ ^ t`. -/
lemma zeta_sum {K : Type*} [Field K] (zeta : K) (p : ℕ) (hp : 0 < p) (hzp : zeta ^ p = 1)
    (t : ℕ) :
    ∑ r ∈ Finset.range p, zeta ^ r * ind K (decide (p ∣ t + (p - r) % p)) = zeta ^ t := by
  classical
  have hu : t % p < p := Nat.mod_lt _ hp
  rw [Finset.sum_eq_single (t % p)]
  · have hd : p ∣ t + (p - t % p) % p := (dvd_shift p t (t % p) hp hu).2 rfl
    rw [decide_eq_true hd]
    simp only [ind_true, mul_one]
    conv_rhs => rw [show t = p * (t / p) + t % p from (Nat.div_add_mod t p).symm]
    rw [pow_add, pow_mul, hzp, one_pow, one_mul]
  · intro r hr hrne
    have hnd : ¬ (p ∣ t + (p - r) % p) := by
      intro hd
      exact hrne ((dvd_shift p t r hp (Finset.mem_range.1 hr)).1 hd)
    rw [decide_eq_false hnd]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 hu) h

/-- **Razborov–Smolensky theorem.**  For distinct primes `p` and `q`, the function `MOD p`
is not computed by any family of polynomial-size, constant-depth circuits with unbounded
fan-in AND, OR, NOT and `MOD q` gates; that is, `MOD p ∉ AC⁰[q]`. -/
theorem razborov_smolensky {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ ∃ (d c N : ℕ) (C : (n : ℕ) → Circuit n),
        (∀ n, N ≤ n → (C n).depth ≤ d) ∧
        (∀ n, N ≤ n → (C n).size ≤ n ^ c + c) ∧
        (∀ n, N ≤ n → ∀ x : Cube n, (C n).eval q x = MODp p x) := by
  classical
  rintro ⟨d, c, N, C, hdepth, hsize, hcorrect⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 := hq.two_le
  have hp2 := hp.two_le
  obtain ⟨zeta, hzp, hz1⟩ := exists_root_of_unity q p hp hpq
  -- choice of the parameters
  set A₀ := p * (2^c + 1) * 2^(p+3) with hA₀
  set a := Nat.log 2 A₀ + 1 with ha
  set A₁ := 16 * ((q-1) * (a + c + 1))^(2*d) with hA₁
  obtain ⟨m₀, hm₀⟩ := log_poly_le A₁ (2*d)
  set m := max m₀ (N + p + c + 1) with hmdef
  set n := 2*m + 1 with hndef
  set L := Nat.log 2 n + 1 with hLdef
  set l := a + (c+1)*L with hldef
  set D := ((q-1)*l)^d with hDdef
  set Ms := (n+p)^c + c with hMs
  have hm1 : 1 ≤ m := le_trans (by omega) (le_max_right m₀ (N + p + c + 1))
  have hmN : N + p + c + 1 ≤ m := le_max_right _ _
  have hnN : N ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hnp : p ≤ n := by omega
  have hnc : c ≤ n := by omega
  have hL1 : 1 ≤ L := by omega
  have ha1 : 1 ≤ a := by omega
  have hl1 : 1 ≤ l := by
    have : 1 ≤ a := ha1
    omega
  have hql1 : 1 ≤ (q-1)*l := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  -- the error parameter is large enough
  have hF2 : p * Ms * 2^(p+3) ≤ 2^l := by
    have hA0 : A₀ ≤ 2^a := le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) A₀)
    have hnL : n ≤ 2^L := le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n)
    have hMsle : Ms ≤ (2^c + 1) * n^(c+1) := by
      have h1 : (n+p)^c ≤ (2*n)^c := Nat.pow_le_pow_left (by omega) c
      have h2 : (2*n)^c = 2^c * n^c := by rw [mul_pow]
      have h3 : n^c ≤ n^(c+1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : c ≤ n^(c+1) := le_trans hnc (Nat.le_self_pow (by omega) n)
      calc Ms = (n+p)^c + c := rfl
        _ ≤ 2^c * n^c + c := by rw [← h2]; omega
        _ ≤ 2^c * n^(c+1) + n^(c+1) := by
            exact Nat.add_le_add (Nat.mul_le_mul_left _ h3) h4
        _ = (2^c + 1) * n^(c+1) := by ring
    calc p * Ms * 2^(p+3) ≤ p * ((2^c+1) * n^(c+1)) * 2^(p+3) := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hMsle)
      _ = A₀ * n^(c+1) := by rw [hA₀]; ring
      _ ≤ 2^a * (2^L)^(c+1) := by
          exact Nat.mul_le_mul hA0 (Nat.pow_le_pow_left hnL _)
      _ = 2^l := by rw [← pow_mul, mul_comm L (c+1), ← pow_add, hldef]
  -- the degree is small enough
  have hF3 : 16 * D^2 ≤ m := by
    have hlL : l ≤ (a + c + 1) * L := by
      have : a ≤ a * L := Nat.le_mul_of_pos_right a (by omega)
      rw [hldef]
      calc a + (c+1)*L ≤ a * L + (c+1)*L := by omega
        _ = (a + c + 1) * L := by ring
    have hDle : D ≤ ((q-1)*(a+c+1))^d * L^d := by
      rw [hDdef]
      calc ((q-1)*l)^d ≤ ((q-1)*((a+c+1)*L))^d :=
            Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hlL) d
        _ = ((q-1)*(a+c+1))^d * L^d := by rw [← mul_pow]; ring_nf
    have hLlog : L ≤ Nat.log 2 m + 3 := by
      have h1 : Nat.log 2 n ≤ Nat.log 2 (m*2*2) := by
        refine Nat.log_mono_right ?_
        omega
      have h2 : Nat.log 2 (m*2*2) = Nat.log 2 m + 2 := by
        rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega)]
      omega
    calc 16 * D^2 ≤ 16 * (((q-1)*(a+c+1))^d * L^d)^2 := by
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hDle 2)
      _ = A₁ * (L^(2*d)) := by rw [hA₁]; ring
      _ ≤ A₁ * ((Nat.log 2 m + 3)^(2*d)) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLlog _)
      _ ≤ m := hm₀ m (le_max_left _ _)
  -- approximations of the shifted MOD_p functions
  have hex : ∀ r : ℕ, ∃ f : Fn (AlgebraicClosure (ZMod q)) n, r < p →
      (f ∈ Deg (AlgebraicClosure (ZMod q)) n D ∧
        2^l * ((univ : Finset (Cube n)).filter
          (fun x => f x ≠ ind (AlgebraicClosure (ZMod q)) (decide (p ∣ wt x + (p - r) % p)))).card ≤ Ms * 2^(n+p)) := by
    intro r
    by_cases hr : r < p
    · set j := (p - r) % p with hj
      have hjp : j < p := Nat.mod_lt _ (by omega)
      have hn'N : N ≤ n + j := by omega
      obtain ⟨g, hgdeg, hgerr⟩ := Circuit.exists_approx q (K := AlgebraicClosure (ZMod q)) (C (n+j)) l hl1
      refine ⟨fun x => g (ext n j x), fun _ => ⟨?_, ?_⟩⟩
      · have hdle : ((q-1)*l)^((C (n+j)).depth) ≤ D := by
          rw [hDdef]
          exact Nat.pow_le_pow_right hql1 (hdepth _ hn'N)
        exact (Deg_le hdle) (Deg_comp_ext hgdeg)
      · have hmapsto : ∀ x ∈ ((univ : Finset (Cube n)).filter
            (fun x => g (ext n j x) ≠ ind (AlgebraicClosure (ZMod q)) (decide (p ∣ wt x + j)))),
            ext n j x ∈ ((univ : Finset (Cube (n+j))).filter
              (fun y => g y ≠ ind (AlgebraicClosure (ZMod q)) ((C (n+j)).eval q y))) := by
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hcorrect _ hn'N, MODp_eq, wt_ext]
          exact hx.2
        have hcard : ((univ : Finset (Cube n)).filter
            (fun x => g (ext n j x) ≠ ind (AlgebraicClosure (ZMod q)) (decide (p ∣ wt x + j)))).card
            ≤ ((univ : Finset (Cube (n+j))).filter
              (fun y => g y ≠ ind (AlgebraicClosure (ZMod q)) ((C (n+j)).eval q y))).card :=
          Finset.card_le_card_of_injOn (ext n j) hmapsto (fun x _ y _ h => ext_injective h)
        have hsz : (C (n+j)).size ≤ Ms := by
          refine le_trans (hsize _ hn'N) ?_
          rw [hMs]
          have : (n+j)^c ≤ (n+p)^c := Nat.pow_le_pow_left (by omega) c
          omega
        calc 2^l * ((univ : Finset (Cube n)).filter
              (fun x => g (ext n j x) ≠ ind (AlgebraicClosure (ZMod q)) (decide (p ∣ wt x + j)))).card
            ≤ 2^l * ((univ : Finset (Cube (n+j))).filter
              (fun y => g y ≠ ind (AlgebraicClosure (ZMod q)) ((C (n+j)).eval q y))).card := Nat.mul_le_mul_left _ hcard
          _ ≤ (C (n+j)).size * 2^(n+j) := hgerr
          _ ≤ Ms * 2^(n+p) := Nat.mul_le_mul hsz (Nat.pow_le_pow_right (by norm_num) (by omega))
    · exact ⟨0, fun h => absurd h hr⟩
  choose F hF using hex
  -- the combined approximation
  set g : Fn (AlgebraicClosure (ZMod q)) n := ∑ r ∈ Finset.range p, zeta ^ r • F r with hgdef
  have hgdeg : g ∈ Deg (AlgebraicClosure (ZMod q)) n D :=
    Submodule.sum_mem _ (fun r hr =>
      Submodule.smul_mem _ _ ((hF r (Finset.mem_range.1 hr)).1))
  set E : ℕ → Finset (Cube n) := fun r => (univ : Finset (Cube n)).filter
      (fun x => F r x ≠ ind (AlgebraicClosure (ZMod q)) (decide (p ∣ wt x + (p - r) % p))) with hEdef
  set G := (univ : Finset (Cube n)).filter
      (fun x => ∀ r ∈ Finset.range p, F r x = ind (AlgebraicClosure (ZMod q)) (decide (p ∣ wt x + (p - r) % p))) with hGdef
  have hGval : ∀ x ∈ G, g x = zeta ^ (wt x) := by
    intro x hx
    have hx2 := (Finset.mem_filter.1 hx).2
    have h1 : g x = ∑ r ∈ Finset.range p, zeta ^ r * F r x := by
      simp only [hgdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, Finset.sum_congr rfl (fun r hr => by rw [hx2 r hr])]
    exact zeta_sum zeta p (by omega) hzp (wt x)
  -- Smolensky's bound
  have hGle : G.card ≤ ∑ i ∈ Finset.range (n/2 + D + 1), n.choose i :=
    smolensky_bound zeta p (by omega) hzp hz1 D g hgdeg G hGval
  have hnhalf : n / 2 = m := by omega
  have hGle2 : G.card ≤ 4^m + D * ((2*m+1).choose m) := by
    rw [hnhalf] at hGle
    have hsum : ∑ i ∈ Finset.range (m + D + 1), n.choose i
        = ∑ i ∈ Finset.range (m + D + 1), (2*m+1).choose i := by rw [hndef]
    rw [hsum] at hGle
    exact le_trans hGle (sum_choose_le m D)
  have hGle3 : G.card ≤ 4^m + 2^(2*m-1) :=
    le_trans hGle2 (Nat.add_le_add_left (mul_choose_le m D hm1 hF3) _)
  -- lower bound on the good set
  have hEsum : ∑ r ∈ Finset.range p, (E r).card ≤ 2^(n-3) := by
    have h1 : 2^l * ∑ r ∈ Finset.range p, (E r).card ≤ p * (Ms * 2^(n+p)) := by
      rw [Finset.mul_sum]
      calc ∑ r ∈ Finset.range p, 2^l * (E r).card
          ≤ ∑ _r ∈ Finset.range p, Ms * 2^(n+p) :=
            Finset.sum_le_sum (fun r hr => (hF r (Finset.mem_range.1 hr)).2)
        _ = p * (Ms * 2^(n+p)) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h2 : p * (Ms * 2^(n+p)) ≤ 2^l * 2^(n-3) := by
      have hsplit : (2:ℕ)^(n+p) = 2^(p+3) * 2^(n-3) := by
        rw [← pow_add]; congr 1; omega
      calc p * (Ms * 2^(n+p)) = (p * Ms * 2^(p+3)) * 2^(n-3) := by rw [hsplit]; ring
        _ ≤ 2^l * 2^(n-3) := Nat.mul_le_mul_right _ hF2
    have h3 : 2^l * ∑ r ∈ Finset.range p, (E r).card ≤ 2^l * 2^(n-3) := le_trans h1 h2
    exact Nat.le_of_mul_le_mul_left h3 (Nat.two_pow_pos l)
  have hcover : (univ : Finset (Cube n)) ⊆ G ∪ (Finset.range p).biUnion E := by
    intro x _
    by_cases hx : ∀ r ∈ Finset.range p, F r x = ind (AlgebraicClosure (ZMod q)) (decide (p ∣ wt x + (p - r) % p))
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)
    · push_neg at hx
      obtain ⟨r, hr, hne⟩ := hx
      refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨r, hr, ?_⟩)
      exact Finset.mem_filter.2 ⟨Finset.mem_univ x, hne⟩
  have hcard2n : (2:ℕ)^n ≤ G.card + ∑ r ∈ Finset.range p, (E r).card := by
    have h1 : Fintype.card (Cube n) ≤ (G ∪ (Finset.range p).biUnion E).card := by
      have := Finset.card_le_card hcover
      simpa using this
    have h2 : (G ∪ (Finset.range p).biUnion E).card
        ≤ G.card + ((Finset.range p).biUnion E).card := Finset.card_union_le _ _
    have h3 : ((Finset.range p).biUnion E).card ≤ ∑ r ∈ Finset.range p, (E r).card :=
      Finset.card_biUnion_le
    have h4 : Fintype.card (Cube n) = 2^n := by simp
    omega
  -- final contradiction
  have hK3pos : 0 < (2:ℕ)^(n-3) := Nat.two_pow_pos _
  have e1 : (2:ℕ)^n = 8 * 2^(n-3) := by
    have h8 : (8:ℕ) * 2^(n-3) = 2^(n-3+3) := by rw [pow_add]; ring
    rw [h8]; congr 1; omega
  have e2 : (4:ℕ)^m = 4 * 2^(n-3) := by
    have h4 : (4:ℕ) * 2^(n-3) = 2^(n-3+2) := by rw [pow_add]; ring
    have hm4 : (4:ℕ)^m = 2^(2*m) := by rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul]
    rw [h4, hm4]; congr 1; omega
  have e3 : (2:ℕ)^(2*m-1) = 2 * 2^(n-3) := by
    have h2 : (2:ℕ) * 2^(n-3) = 2^(n-3+1) := by rw [pow_add]; ring
    rw [h2]; congr 1; omega
  omega

end CS

import RequestProject.RS.Aux

/-!
# Non-vacuity of the circuit model

This file checks that the circuit model of `RequestProject.RS.Circuit` is not degenerate:
the `MOD q` function itself *is* computed by a family of depth-`1`, size-`(n+1)` circuits
with `MOD q` gates.  Together with the main theorem (which says that `MOD p` is *not*
computed by any constant-depth polynomial-size family) this shows that the class of
functions described by the existential statement of `CS.razborov_smolensky` is a genuine,
non-trivial class.
-/

namespace CS
namespace RS

open Finset

/-- The depth-one circuit consisting of `n` input gates feeding a single `MOD q` gate. -/
def modqCircuit (n : ℕ) : Circuit n where
  size := n + 1
  gates := fun i => if h : i < n then .inp ⟨i, h⟩ else .modq (List.range n)
  acyclic := by
    intro i hi j hj
    by_cases h : i < n
    · simp [h, Gate.children] at hj
    · simp only [h, Gate.children] at hj
      have := List.mem_range.1 hj
      omega
  out := n
  out_lt := by omega

@[simp] lemma modqCircuit_size (n : ℕ) : (modqCircuit n).size = n + 1 := rfl

@[simp] lemma modqCircuit_out (n : ℕ) : (modqCircuit n).out = n := rfl

lemma modqCircuit_gates_out (n : ℕ) :
    (modqCircuit n).gates n = Gate.modq (List.range n) := by
  simp [modqCircuit]

lemma modqCircuit_gates_lt {n j : ℕ} (h : j < n) :
    (modqCircuit n).gates j = Gate.inp ⟨j, h⟩ := by
  simp [modqCircuit, h]

lemma modqCircuit_evalAt_inp (q n : ℕ) (x : Cube n) {j : ℕ} (h : j < n) :
    (modqCircuit n).evalAt q x j = x ⟨j, h⟩ := by
  rw [Circuit.evalAt_eq, modqCircuit_gates_lt h]
  rfl

private lemma length_filter_range (n : ℕ) (f : ℕ → Bool) :
    ((List.range n).filter f).length = ∑ j ∈ Finset.range n, (if f j then 1 else 0) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
      by_cases h : f k <;> simp [h]

private lemma foldr_max_le {l : List ℕ} {b : ℕ} (h : ∀ a ∈ l, a ≤ b) : l.foldr max 0 ≤ b := by
  induction l with
  | nil => simp
  | cons c t ih =>
      simp only [List.foldr_cons, max_le_iff]
      exact ⟨h c (by simp), ih (fun a ha => h a (by simp [ha]))⟩

lemma modqCircuit_eval (q n : ℕ) (x : Cube n) :
    (modqCircuit n).eval q x = decide (¬ q ∣ wt x) := by
  rw [Circuit.eval, Circuit.evalAt_eq, modqCircuit_out, modqCircuit_gates_out]
  have hcongr : (List.range n).filter
        (fun j => if _h : j < n then (modqCircuit n).evalAt q x j else false)
      = (List.range n).filter (fun j => if h : j < n then x ⟨j, h⟩ else false) := by
    refine List.filter_congr (fun j hj => ?_)
    have hjn : j < n := List.mem_range.1 hj
    simp [hjn, modqCircuit_evalAt_inp q n x hjn]
  have hlen : ((List.range n).filter (fun j => if h : j < n then x ⟨j, h⟩ else false)).length
      = wt x := by
    rw [length_filter_range, wt_eq_sum,
      ← Fin.sum_univ_eq_sum_range
        (fun j => if (if h : j < n then x ⟨j, h⟩ else false) then 1 else 0) n]
    exact Finset.sum_congr rfl (fun i _ => by simp [i.isLt])
  simp only [Gate.value, hcongr, hlen]

lemma modqCircuit_depth (n : ℕ) : (modqCircuit n).depth ≤ 1 := by
  have hdep0 : ∀ j, j < n → (modqCircuit n).dep j = 0 := by
    intro j hj
    rw [Circuit.dep_eq, modqCircuit_gates_lt hj]
    simp [Gate.children]
  rw [Circuit.depth, modqCircuit_out, Circuit.dep_eq, modqCircuit_gates_out]
  refine foldr_max_le (fun a ha => ?_)
  simp only [Gate.children, List.mem_map] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  have hjn : j < n := List.mem_range.1 hj
  simp [hjn, hdep0 j hjn]

/-- **Non-vacuity check.**  The `MOD q` function is computed by a family of depth-`1`,
size-`(n+1)` circuits with `MOD q` gates, so the class of functions quantified over in
`CS.razborov_smolensky` is non-trivial. -/
theorem modq_mem_AC0q (q : ℕ) :
    ∃ (d c N : ℕ) (C : (n : ℕ) → Circuit n),
      (∀ n, N ≤ n → (C n).depth ≤ d) ∧
      (∀ n, N ≤ n → (C n).size ≤ n ^ c + c) ∧
      (∀ n, N ≤ n → ∀ x : Cube n, (C n).eval q x = decide (¬ q ∣ wt x)) :=
  ⟨1, 1, 0, modqCircuit, fun n _ => modqCircuit_depth n,
    fun n _ => by simp, fun n _ x => modqCircuit_eval q n x⟩

end RS
end CS

import RequestProject.RS.Degree
import RequestProject.RS.Circuit

/-!
# Auxiliary lemmas

* a polynomial is eventually dominated by an exponential;
* existence of a primitive `p`-th root of unity in characteristic `q ≠ p`;
* restricting a function on the cube `{0,1}^(n+j)` to the subcube where the last `j`
  coordinates are `1` does not increase the degree.
-/

namespace CS
namespace RS

open Finset Filter

/-- Polynomials are eventually dominated by exponentials. -/
lemma poly_le_exp (A k : ℕ) : ∃ j₀ : ℕ, ∀ j ≥ j₀, A * (j+3)^k ≤ 2^j := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt k (r := (2:ℝ)) (by norm_num)
  have hpos : (0:ℝ) < 1 / (A * 4^k + 1) := by positivity
  have hev : ∀ᶠ j : ℕ in atTop, ((j:ℝ)^k / 2^j) < 1 / (A * 4^k + 1) :=
    hlim.eventually_lt_const hpos
  obtain ⟨j1, hj1⟩ := (Filter.eventually_atTop.1 hev)
  refine ⟨max j1 1, fun j hj => ?_⟩
  have hj1' : j ≥ j1 := le_trans (le_max_left _ _) hj
  have hjpos : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hreal := hj1 j hj1'
  have h2pos : (0:ℝ) < 2^j := by positivity
  have hb : (0:ℝ) < (A:ℝ)*4^k+1 := by positivity
  have hstep : ((A:ℝ) * 4^k + 1) * (j:ℝ)^k < 2^j := by
    rw [div_lt_iff₀ h2pos] at hreal
    calc ((A:ℝ) * 4^k + 1) * (j:ℝ)^k = (j:ℝ)^k * ((A:ℝ)*4^k+1) := by ring
      _ < (1 / ((A:ℝ) * 4^k + 1)) * 2^j * ((A:ℝ)*4^k+1) := (mul_lt_mul_iff_of_pos_right hb).2 hreal
      _ = 2^j := by field_simp
  have hfinal : ((A:ℝ) * ((j:ℝ)+3)^k) ≤ (A:ℝ) * 4^k * (j:ℝ)^k := by
    have h34 : ((j:ℝ)+3) ≤ 4 * j := by
      have h1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hjpos
      linarith
    have hp : ((j:ℝ)+3)^k ≤ (4*(j:ℝ))^k := pow_le_pow_left₀ (by positivity) h34 k
    calc (A:ℝ) * ((j:ℝ)+3)^k ≤ (A:ℝ) * (4*(j:ℝ))^k :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (A:ℝ) * 4^k * (j:ℝ)^k := by rw [mul_pow]; ring
  have hlt : ((A:ℝ) * ((j:ℝ)+3)^k) < 2^j := by
    calc (A:ℝ) * ((j:ℝ)+3)^k ≤ (A:ℝ)*4^k*(j:ℝ)^k := hfinal
      _ ≤ ((A:ℝ)*4^k+1) * (j:ℝ)^k := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ < 2^j := hstep
  have hcast : ((A * (j+3)^k : ℕ) : ℝ) < ((2^j : ℕ) : ℝ) := by push_cast; exact hlt
  exact le_of_lt (by exact_mod_cast hcast)

/-- A power of a logarithm is eventually dominated by the identity. -/
lemma log_poly_le (A k : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, A * (Nat.log 2 m + 3)^k ≤ m := by
  obtain ⟨j₀, hj₀⟩ := poly_le_exp A k
  refine ⟨2^j₀, fun m hm => ?_⟩
  have hm0 : m ≠ 0 := by
    have : 0 < 2^j₀ := Nat.two_pow_pos j₀
    omega
  have hlog : j₀ ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by norm_num) hm
  calc A * (Nat.log 2 m + 3)^k ≤ 2^(Nat.log 2 m) := hj₀ _ hlog
    _ ≤ m := Nat.pow_log_le_self 2 hm0

open Polynomial in
/-- In characteristic `q` there is a primitive `p`-th root of unity for every prime `p ≠ q`. -/
lemma exists_root_of_unity (q p : ℕ) [hq : Fact (Nat.Prime q)] (hp : Nat.Prime p) (hpq : p ≠ q) :
    ∃ zeta : AlgebraicClosure (ZMod q), zeta ^ p = 1 ∧ zeta ≠ 1 := by
  have hp2 := hp.two_le
  set K := AlgebraicClosure (ZMod q)
  have hpK : (p : K) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff K q p).1 h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp).1 hd).symm
  set g : K[X] := ∑ i ∈ Finset.range p, X ^ i with hg
  have hcoef : g.coeff (p-1) = 1 := by
    rw [hg, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single (p-1)]
    · simp
    · intro b _ hbne
      rw [Polynomial.coeff_X_pow]
      exact if_neg (by omega)
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  have hdeg : g.degree ≠ 0 := by
    intro h0
    have hle : p - 1 ≤ g.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hcoef]; exact one_ne_zero)
    have hnd : g.natDegree = 0 :=
      Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 (le_of_eq h0)
    omega
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root g hdeg
  have hzval : ∑ i ∈ Finset.range p, z ^ i = 0 := by
    have h := hz
    rw [Polynomial.IsRoot, hg] at h
    simpa using h
  refine ⟨z, ?_, ?_⟩
  · have h := geom_sum_mul z p
    rw [hzval, zero_mul] at h
    linear_combination -h
  · intro h1
    rw [h1] at hzval
    simp at hzval
    exact hpK (by exact_mod_cast hzval)

section Extension

variable {K : Type*} [Field K] {n j : ℕ}

/-- Extend an input of length `n` by `j` coordinates equal to `true`. -/
def ext (n j : ℕ) (x : Cube n) : Cube (n + j) := Fin.append x (fun _ : Fin j => true)

lemma ext_left (x : Cube n) (a : Fin n) : ext n j x (Fin.castAdd j a) = x a := by
  rw [ext, Fin.append_left]

lemma ext_injective : Function.Injective (ext n j) := by
  intro x y hxy
  funext a
  have := congrArg (fun z => z (Fin.castAdd j a)) hxy
  simpa [ext_left] using this

lemma wt_eq_sum (x : Cube n) : wt x = ∑ i, (if x i = true then 1 else 0) := by
  rw [wt, Finset.card_filter]

lemma wt_ext (x : Cube n) : wt (ext n j x) = wt x + j := by
  rw [wt_eq_sum, wt_eq_sum, Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl (fun a _ => by rw [ext_left])
  · simp [ext, Fin.append_right]

lemma mono_comp_ext (T : Finset (Fin (n+j))) (x : Cube n) :
    mono K T (ext n j x)
      = mono K (univ.filter (fun a : Fin n => Fin.castAdd j a ∈ T)) x := by
  classical
  set y : Cube (n+j) := ext n j x with hy
  set T'' := (univ.filter (fun a : Fin n => Fin.castAdd j a ∈ T)).image (Fin.castAdd j) with hT''
  have hsub : T'' ⊆ T := by
    intro i hi
    rw [hT''] at hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
    exact (Finset.mem_filter.1 ha).2
  have h1 : mono K T y = ∏ i ∈ T, ind K (y i) := rfl
  rw [h1, ← Finset.prod_sdiff hsub]
  have hrest : ∏ i ∈ T \ T'', ind K (y i) = 1 := by
    refine Finset.prod_eq_one (fun i hi => ?_)
    rw [Finset.mem_sdiff] at hi
    refine Fin.addCases (motive := fun i => i ∈ T → i ∉ T'' → ind K (y i) = 1) ?_ ?_ i hi.1 hi.2
    · intro a haT haT''
      exact absurd (Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ a, haT⟩, rfl⟩) haT''
    · intro b _ _
      rw [hy, ext, Fin.append_right]
      simp [ind]
  rw [hrest, one_mul, hT'', Finset.prod_image (fun a _ b _ h => Fin.castAdd_injective _ _ h)]
  show ∏ a ∈ univ.filter (fun a : Fin n => Fin.castAdd j a ∈ T), ind K (y (Fin.castAdd j a))
      = ∏ a ∈ univ.filter (fun a : Fin n => Fin.castAdd j a ∈ T), ind K (x a)
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [hy, ext_left]

/-- Restricting to the subcube where the last `j` coordinates are `1` preserves low degree. -/
lemma Deg_comp_ext {D : ℕ} {F : Fn K (n+j)} (hF : F ∈ Deg K (n+j) D) :
    (fun x : Cube n => F (ext n j x)) ∈ Deg K n D := by
  classical
  set L : Fn K (n+j) →ₗ[K] Fn K n := LinearMap.funLeft K K (ext n j) with hL
  have hmap : Submodule.map L (Deg K (n+j) D) ≤ Deg K n D := by
    rw [Deg, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨⟨T, hT⟩, rfl⟩, rfl⟩
    have hval : L (mono K T) = mono K (univ.filter (fun a : Fin n => Fin.castAdd j a ∈ T)) := by
      funext x
      exact mono_comp_ext T x
    rw [hval]
    refine mono_mem_Deg (le_trans ?_ hT)
    refine Finset.card_le_card_of_injOn (Fin.castAdd j) ?_ (fun a _ b _ h => Fin.castAdd_injective _ _ h)
    intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
    exact ha.2
  exact hmap ⟨F, hF, rfl⟩

end Extension

end RS
end CS

import RequestProject.RS.Degree

/-!
# Boolean circuits with unbounded fan-in AND, OR, NOT and MOD_q gates

A circuit on `n` inputs is a finite indexed family of gates, where gate `i` may only refer to
gates with smaller index (`acyclic`).  Gates are: inputs, constants, negations, unbounded fan-in
conjunctions and disjunctions, and unbounded fan-in `MOD q` gates (which output `true` iff the
number of `true` inputs is *not* divisible by `q`).

`Circuit.evalAt q C x i` is the Boolean value of gate `i` on input `x`, and `C.depth` is the
depth of the cone of the output gate.
-/

namespace CS
namespace RS

open Finset

/-- A gate of a circuit on `n` inputs.  Non-input gates refer to other gates by index. -/
inductive Gate (n : ℕ) : Type
  | inp : Fin n → Gate n
  | cst : Bool → Gate n
  | neg : ℕ → Gate n
  | conj : List ℕ → Gate n
  | disj : List ℕ → Gate n
  | modq : List ℕ → Gate n

/-- The list of gates feeding into a gate. -/
def Gate.children {n : ℕ} : Gate n → List ℕ
  | .inp _ => []
  | .cst _ => []
  | .neg j => [j]
  | .conj l => l
  | .disj l => l
  | .modq l => l

/-- The Boolean value of a gate, given the values `v` of the other gates. -/
def Gate.value {n : ℕ} (q : ℕ) (g : Gate n) (x : Cube n) (v : ℕ → Bool) : Bool :=
  match g with
  | .inp k => x k
  | .cst b => b
  | .neg j => !(v j)
  | .conj l => l.all v
  | .disj l => l.any v
  | .modq l => decide (¬ q ∣ (l.filter v).length)

/-- A circuit on `n` inputs: `size` gates, indexed by naturals, each referring only to
gates of smaller index, together with a designated output gate. -/
structure Circuit (n : ℕ) where
  /-- the number of gates -/
  size : ℕ
  /-- the gate at each index -/
  gates : ℕ → Gate n
  /-- gates only refer to gates of smaller index -/
  acyclic : ∀ i < size, ∀ j ∈ (gates i).children, j < i
  /-- the index of the output gate -/
  out : ℕ
  /-- the output gate is one of the gates -/
  out_lt : out < size

/-- The value of gate `i` of the circuit `C` on input `x`. -/
def Circuit.evalAt {n : ℕ} (q : ℕ) (C : Circuit n) (x : Cube n) : ℕ → Bool
  | i => Gate.value q (C.gates i) x (fun j => if _h : j < i then C.evalAt q x j else false)

/-- The depth of gate `i` (the length of the longest path from `i` down to an input). -/
def Circuit.dep {n : ℕ} (C : Circuit n) : ℕ → ℕ
  | i => ((C.gates i).children.map (fun j => if _h : j < i then C.dep j + 1 else 0)).foldr max 0

/-- The depth of a circuit: the depth of its output gate. -/
def Circuit.depth {n : ℕ} (C : Circuit n) : ℕ := C.dep C.out

/-- The Boolean function computed by a circuit. -/
def Circuit.eval {n : ℕ} (q : ℕ) (C : Circuit n) (x : Cube n) : Bool := C.evalAt q x C.out

lemma Circuit.evalAt_eq {n q : ℕ} (C : Circuit n) (x : Cube n) (i : ℕ) :
    C.evalAt q x i =
      Gate.value q (C.gates i) x (fun j => if _h : j < i then C.evalAt q x j else false) := by
  rw [Circuit.evalAt]

lemma Circuit.dep_eq {n : ℕ} (C : Circuit n) (i : ℕ) :
    C.dep i = ((C.gates i).children.map (fun j => if _h : j < i then C.dep j + 1 else 0)).foldr
      max 0 := by
  rw [Circuit.dep]

private lemma le_foldr_max : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro a ha; simp at ha
  | cons b t ih =>
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha'
      · simp
      · exact le_trans (ih ha') (by simp)

/-- Children of a gate have strictly smaller depth. -/
lemma Circuit.dep_child_lt {n : ℕ} (C : Circuit n) {i j : ℕ} (hj : j ∈ (C.gates i).children)
    (hji : j < i) : C.dep j < C.dep i := by
  rw [C.dep_eq i]
  have hmem : C.dep j + 1 ∈
      ((C.gates i).children.map (fun k => if _h : k < i then C.dep k + 1 else 0)) := by
    have := List.mem_map_of_mem (f := fun k => if _h : k < i then C.dep k + 1 else 0) hj
    simpa [hji] using this
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_foldr_max hmem)

/-- The `MOD p` function: `true` iff the number of `true` coordinates is divisible by `p`. -/
def MODp (p : ℕ) {n : ℕ} (x : Cube n) : Bool :=
  decide (p ∣ (Finset.univ.filter (fun i => x i = true)).card)

/-- The number of `true` coordinates of `x`. -/
def wt {n : ℕ} (x : Cube n) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

lemma MODp_eq (p : ℕ) {n : ℕ} (x : Cube n) : MODp p x = decide (p ∣ wt x) := rfl

end RS
end CS

import RequestProject.RS.Circuit

/-!
# Razborov–Smolensky approximation of `AC⁰[q]` circuits by low-degree polynomials

The main result of this file is `Circuit.exists_approx`: any circuit of size `s` and depth `d`
is computed, outside of a set of at most `s * 2^n / 2^ℓ` inputs, by a function of degree at most
`((q-1) * ℓ)^d` over any field of characteristic `q`.
-/

namespace CS
namespace RS

open Finset
open scoped Classical

/-- In characteristic `q`, `m^(q-1)` is `0` or `1` according to divisibility by `q`. -/
lemma natCast_pow_q_sub_one (K : Type*) [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] (m : ℕ) :
    ((m : K))^(q-1) = if q ∣ m then 0 else 1 := by
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  by_cases h : q ∣ m
  · have h0 : (m : K) = 0 := (CharP.cast_eq_zero_iff K q m).2 h
    rw [if_pos h, h0, zero_pow (by omega)]
  · have h0 : (m : K) ≠ 0 := fun hc => h ((CharP.cast_eq_zero_iff K q m).1 hc)
    have hmod : m ^ q ≡ m [MOD q] := by
      have hz : ((m ^ q : ℕ) : ZMod q) = ((m : ℕ) : ZMod q) := by
        push_cast; exact ZMod.pow_card _
      exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hz
    have hle : m ≤ m ^ q := Nat.le_self_pow (by omega) m
    have hdvd : q ∣ m ^ q - m := (Nat.modEq_iff_dvd' hle).1 hmod.symm
    have hzero : ((m ^ q - m : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K q _).2 hdvd
    rw [Nat.cast_sub hle] at hzero
    have hf : ((m : K))^q = (m : K) := by
      rw [← Nat.cast_pow]; exact sub_eq_zero.1 hzero
    rw [if_neg h]
    have hq : q = (q - 1) + 1 := by omega
    rw [hq, pow_succ] at hf
    exact mul_right_cancel₀ h0 (hf.trans (one_mul _).symm)

lemma sum_ind_eq_card {K : Type*} [Field K] {m : ℕ} (T : Finset (Fin m)) (c : Fin m → Bool) :
    ∑ t ∈ T, ind K (c t) = ((T.filter (fun t => c t = true)).card : K) := by
  classical
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun t _ => ?_)
  cases h : c t <;> simp [ind]

/-- At most half of all subsets have vanishing sum, provided one summand is nonzero. -/
lemma card_sum_zero_le {K : Type*} [Field K] {m : ℕ} (u : Fin m → K) (t₀ : Fin m) (h0 : u t₀ ≠ 0) :
    2 * ((univ : Finset (Finset (Fin m))).filter (fun S => ∑ t ∈ S, u t = 0)).card
      ≤ Fintype.card (Finset (Fin m)) := by
  classical
  set B := (univ : Finset (Finset (Fin m))).filter (fun S => ∑ t ∈ S, u t = 0) with hB
  set phi : Finset (Fin m) → Finset (Fin m) :=
    fun S => if t₀ ∈ S then S.erase t₀ else insert t₀ S with hphi
  have hinv : ∀ S, phi (phi S) = S := by
    intro S
    by_cases h : t₀ ∈ S
    · simp [hphi, h, Finset.insert_erase h]
    · simp [hphi, h, Finset.erase_insert h]
  have hmaps : ∀ S ∈ B, phi S ∈ Bᶜ := by
    intro S hS
    have hsum : ∑ t ∈ S, u t = 0 := (mem_filter.1 hS).2
    simp only [Finset.mem_compl, hB, mem_filter, mem_univ, true_and]
    intro hc
    by_cases h : t₀ ∈ S
    · have hs : ∑ t ∈ S.erase t₀, u t + u t₀ = ∑ t ∈ S, u t := Finset.sum_erase_add _ _ h
      rw [hsum] at hs
      simp only [hphi, if_pos h] at hc
      rw [hc, zero_add] at hs
      exact h0 hs
    · have hs : ∑ t ∈ insert t₀ S, u t = u t₀ + ∑ t ∈ S, u t := Finset.sum_insert h
      rw [hsum, add_zero] at hs
      simp only [hphi, if_neg h] at hc
      rw [hc] at hs
      exact h0 hs.symm
  have hinj : Set.InjOn phi B := by
    intro a _ b _ hab
    have h := congrArg phi hab
    rwa [hinv, hinv] at h
  have hcard : B.card ≤ Bᶜ.card := Finset.card_le_card_of_injOn phi hmaps hinj
  have hc2 : Bᶜ.card = Fintype.card (Finset (Fin m)) - B.card := Finset.card_compl B
  have hble : B.card ≤ Fintype.card (Finset (Fin m)) := Finset.card_le_univ B
  omega

/-- At most a `2^(-ℓ)` fraction of the `ℓ`-tuples of subsets have all sums vanishing. -/
lemma card_badseed_le {K : Type*} [Field K] {m l : ℕ} (u : Fin m → K) (t₀ : Fin m)
    (h0 : u t₀ ≠ 0) :
    2^l * ((univ : Finset (Fin l → Finset (Fin m))).filter
        (fun S => ∀ k, ∑ t ∈ S k, u t = 0)).card
      ≤ Fintype.card (Fin l → Finset (Fin m)) := by
  classical
  have hB := card_sum_zero_le u t₀ h0
  set B := (univ : Finset (Finset (Fin m))).filter (fun S => ∑ t ∈ S, u t = 0) with hBdef
  have hset : ((univ : Finset (Fin l → Finset (Fin m))).filter
      (fun S => ∀ k, ∑ t ∈ S k, u t = 0)) = Fintype.piFinset (fun _ : Fin l => B) := by
    ext S
    simp [hBdef, Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Fintype.card_fun, Fintype.card_fin]
  calc 2 ^ l * B.card ^ l = (2 * B.card)^l := by rw [mul_pow]
    _ ≤ (Fintype.card (Finset (Fin m)))^l := Nat.pow_le_pow_left hB l

variable {K : Type*} [Field K] {n : ℕ}

/-- The randomized low-degree approximation of an unbounded fan-in OR. -/
def orPoly (q : ℕ) {K : Type*} [Field K] {n m l : ℕ} (S : Fin l → Finset (Fin m))
    (u : Fin m → Fn K n) : Fn K n :=
  fun x => 1 - ∏ k : Fin l, (1 - (∑ t ∈ S k, u t x)^(q-1))

/-- Existence of a good choice of subsets for the OR approximation. -/
lemma or_approx (q : ℕ) [Fact q.Prime] {K : Type*} [Field K] [CharP K q] {n m l : ℕ}
    (u : Fin m → Fn K n) (b : Fin m → Cube n → Bool) (A : Finset (Cube n))
    (hu : ∀ x ∈ A, ∀ t, u t x = ind K (b t x)) :
    ∃ S : Fin l → Finset (Fin m),
      2^l * (A.filter (fun x => orPoly q S u x ≠ ind K (decide (∃ t, b t x = true)))).card
        ≤ 2^n := by
  classical
  set Om := (univ : Finset (Fin l → Finset (Fin m))) with hOm
  set N := Fintype.card (Fin l → Finset (Fin m)) with hN
  -- for each good input, few seeds are bad
  have hx : ∀ x ∈ A,
      2^l * (Om.filter (fun S => orPoly q S u x ≠ ind K (decide (∃ t, b t x = true)))).card ≤ N := by
    intro x hxA
    by_cases hex : ∃ t, b t x = true
    · obtain ⟨t₀, ht₀⟩ := hex
      have h1 : u t₀ x ≠ 0 := by
        rw [hu x hxA t₀, ht₀]; simp [ind]
      have hsub : (Om.filter (fun S => orPoly q S u x ≠ ind K (decide (∃ t, b t x = true))))
          ⊆ Om.filter (fun S => ∀ k, ∑ t ∈ S k, u t x = 0) := by
        intro S hS
        rw [mem_filter] at hS ⊢
        refine ⟨hS.1, ?_⟩
        intro k
        by_contra hne
        -- if some sum is nonzero, the corresponding factor vanishes, so orPoly = 1
        have hc : ∑ t ∈ S k, u t x = (((S k).filter (fun t => b t x = true)).card : K) := by
          rw [show (fun t => u t x) = (fun t => ind K (b t x)) from funext (fun t => hu x hxA t)]
          exact sum_ind_eq_card _ _
        have hnd : ¬ q ∣ ((S k).filter (fun t => b t x = true)).card := by
          intro hd
          apply hne
          rw [hc, (CharP.cast_eq_zero_iff K q _).2 hd]
        have hfac : (1 : K) - (∑ t ∈ S k, u t x)^(q-1) = 0 := by
          rw [hc, natCast_pow_q_sub_one K q, if_neg hnd, sub_self]
        have hprod : ∏ k : Fin l, (1 - (∑ t ∈ S k, u t x)^(q-1)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) hfac
        have : orPoly q S u x = ind K (decide (∃ t, b t x = true)) := by
          simp only [orPoly, hprod, sub_zero]
          rw [decide_eq_true (⟨t₀, ht₀⟩ : ∃ t, b t x = true)]
          simp [ind]
        exact hS.2 this
      calc 2^l * (Om.filter (fun S => orPoly q S u x ≠ ind K (decide (∃ t, b t x = true)))).card
          ≤ 2^l * (Om.filter (fun S => ∀ k, ∑ t ∈ S k, u t x = 0)).card := by
            exact Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
        _ ≤ N := card_badseed_le (fun t => u t x) t₀ h1
    · -- all children are false: the approximation is exact
      have hz : ∀ t, u t x = 0 := by
        intro t
        rw [hu x hxA t]
        cases hbt : b t x
        · simp [ind]
        · exact absurd ⟨t, hbt⟩ hex
      have hempty : (Om.filter (fun S => orPoly q S u x ≠ ind K (decide (∃ t, b t x = true))))
          = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro S _
        simp only [not_not]
        have hsum : ∀ k, ∑ t ∈ S k, u t x = 0 := by
          intro k; exact Finset.sum_eq_zero (fun t _ => hz t)
        have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
        have : ∀ k : Fin l, (1 : K) - (∑ t ∈ S k, u t x)^(q-1) = 1 := by
          intro k; rw [hsum k, zero_pow (by omega), sub_zero]
        simp only [orPoly, this, Finset.prod_const_one, sub_self]
        rw [decide_eq_false hex]
        simp [ind]
      rw [hempty]
      simp
  -- sum over all seeds
  have hswap : ∑ S ∈ Om, (A.filter (fun x => orPoly q S u x
        ≠ ind K (decide (∃ t, b t x = true)))).card
      = ∑ x ∈ A, (Om.filter (fun S => orPoly q S u x
        ≠ ind K (decide (∃ t, b t x = true)))).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hAcard : A.card ≤ 2^n := by
    have h1 : A.card ≤ Fintype.card (Cube n) := Finset.card_le_univ A
    simpa [Fintype.card_fun] using h1
  have htotal : 2^l * ∑ S ∈ Om, (A.filter (fun x => orPoly q S u x
      ≠ ind K (decide (∃ t, b t x = true)))).card ≤ N * 2^n := by
    rw [hswap, Finset.mul_sum]
    calc ∑ x ∈ A, 2^l * (Om.filter (fun S => orPoly q S u x
            ≠ ind K (decide (∃ t, b t x = true)))).card
        ≤ ∑ _x ∈ A, N := Finset.sum_le_sum hx
      _ = A.card * N := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2^n * N := Nat.mul_le_mul_right _ hAcard
      _ = N * 2^n := mul_comm _ _
  have hNe : Om.Nonempty := by
    refine ⟨fun _ => ∅, Finset.mem_univ _⟩
  have hsumle : ∑ S ∈ Om, (2^l * (A.filter (fun x => orPoly q S u x
      ≠ ind K (decide (∃ t, b t x = true)))).card) ≤ ∑ _S ∈ Om, 2^n := by
    rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul, hOm]
    have : (univ : Finset (Fin l → Finset (Fin m))).card = N := by
      rw [hN, Finset.card_univ]
    rw [this]
    exact htotal
  obtain ⟨S, _, hS⟩ := Finset.exists_le_of_sum_le hNe hsumle
  exact ⟨S, hS⟩

/-- A gate with no children has depth zero. -/
lemma Circuit.dep_eq_zero {n : ℕ} (C : Circuit n) {i : ℕ} (h : (C.gates i).children = []) :
    C.dep i = 0 := by
  rw [C.dep_eq i, h]
  simp

lemma listSum_mem_Deg {K : Type*} [Field K] {n : ℕ} (lst : List ℕ) (f : ℕ → Fn K n) (E : ℕ)
    (hf : ∀ j ∈ lst, f j ∈ Deg K n E) :
    (fun x => (lst.map (fun j => f j x)).sum) ∈ Deg K n E := by
  induction lst with
  | nil =>
      have h0 : (fun x : Cube n => (([] : List ℕ).map (fun j => f j x)).sum) = (0 : Fn K n) := by
        funext x; simp
      rw [h0]; exact (Deg K n E).zero_mem
  | cons a t ih =>
      have hrw : (fun x => ((a :: t).map (fun j => f j x)).sum)
          = f a + (fun x => (t.map (fun j => f j x)).sum) := by
        funext x; simp
      rw [hrw]
      exact Submodule.add_mem _ (hf a (by simp)) (ih (fun j hj => hf j (by simp [hj])))

lemma list_map_ind_sum {K : Type*} [Field K] (lst : List ℕ) (c : ℕ → Bool) :
    (lst.map (fun j => ind K (c j))).sum = (((lst.filter c).length : ℕ) : K) := by
  induction lst with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, ih]
      by_cases h : c a = true
      · rw [List.filter_cons_of_pos h, List.length_cons]
        rw [show ind K (c a) = 1 from by rw [h]; rfl]
        push_cast
        ring
      · simp only [Bool.not_eq_true] at h
        rw [List.filter_cons_of_neg (by simp [h])]
        rw [show ind K (c a) = 0 from by rw [h]; rfl]
        ring

lemma orPoly_mem_Deg (q : ℕ) {K : Type*} [Field K] {n m l E : ℕ} (S : Fin l → Finset (Fin m))
    (u : Fin m → Fn K n) (hu : ∀ t, u t ∈ Deg K n E) :
    orPoly q S u ∈ Deg K n (l * ((q - 1) * E)) := by
  classical
  have hfac : ∀ k : Fin l,
      (fun x => (1 : K) - (∑ t ∈ S k, u t x)^(q-1)) ∈ Deg K n ((q-1) * E) := by
    intro k
    have hsum : (fun x => ∑ t ∈ S k, u t x) ∈ Deg K n E := by
      have : (fun x => ∑ t ∈ S k, u t x) = ∑ t ∈ S k, u t := by
        funext x; rw [Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ (fun t _ => hu t)
    have hpow : (fun x => (∑ t ∈ S k, u t x)^(q-1)) ∈ Deg K n ((q-1) * E) := by
      have := pow_mem_Deg (q-1) hsum
      have hrw : (fun x => ∑ t ∈ S k, u t x)^(q-1) = (fun x => (∑ t ∈ S k, u t x)^(q-1)) := by
        funext x; rw [Pi.pow_apply]
      rwa [hrw] at this
    exact Submodule.sub_mem _ (const_mem_Deg 1 _) hpow
  have hprod : (fun x => ∏ k : Fin l, ((1 : K) - (∑ t ∈ S k, u t x)^(q-1)))
      ∈ Deg K n (l * ((q-1) * E)) := by
    have hrw : (fun x => ∏ k : Fin l, ((1 : K) - (∑ t ∈ S k, u t x)^(q-1)))
        = ∏ k : Fin l, (fun x => (1 : K) - (∑ t ∈ S k, u t x)^(q-1)) := by
      funext x; rw [Finset.prod_apply]
    rw [hrw]
    have := prod_mem_Deg' (Finset.univ : Finset (Fin l))
      (fun k => (fun x => (1 : K) - (∑ t ∈ S k, u t x)^(q-1))) ((q-1)*E) (fun k _ => hfac k)
    simpa using this
  have : orPoly q S u = (fun _ => (1:K)) - (fun x => ∏ k : Fin l, ((1 : K) - (∑ t ∈ S k, u t x)^(q-1))) := by
    funext x; simp [orPoly]
  rw [this]
  exact Submodule.sub_mem _ (const_mem_Deg 1 _) hprod

end RS
end CS

import Mathlib

/-!
# Low-degree functions on the Boolean cube

We work with functions from the Boolean cube `Fin n → Bool` to a field `K`, and define
the submodule `Deg K n D` of functions of "degree at most `D`", namely the `K`-span of the
multilinear monomials `x ↦ ∏ i ∈ T, x i` with `#T ≤ D`.
-/

namespace CS
namespace RS

open Finset

/-- The Boolean cube on `n` coordinates. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Functions from the Boolean cube to `K`. -/
abbrev Fn (K : Type*) (n : ℕ) := Cube n → K

variable {K : Type*} [Field K] {n : ℕ}

/-- The indicator of a Boolean value inside a field. -/
def ind (K : Type*) [Field K] (b : Bool) : K := if b then 1 else 0

@[simp] lemma ind_true : ind K true = 1 := rfl
@[simp] lemma ind_false : ind K false = 0 := rfl

lemma ind_not (b : Bool) : ind K (!b) = 1 - ind K b := by
  cases b <;> simp [ind]

/-- The monomial function attached to a set `T` of coordinates. -/
def mono (K : Type*) [Field K] {n : ℕ} (T : Finset (Fin n)) : Fn K n :=
  fun x => ∏ i ∈ T, ind K (x i)

lemma mono_apply_eq (T : Finset (Fin n)) (x : Cube n) :
    mono K T x = if (∀ i ∈ T, x i = true) then 1 else 0 := by
  unfold mono
  split
  · rename_i h
    exact Finset.prod_eq_one (fun i hi => by rw [h i hi]; simp)
  · rename_i h
    push_neg at h
    obtain ⟨i, hi, hxi⟩ := h
    refine Finset.prod_eq_zero hi ?_
    simp [ind, Bool.eq_false_iff.mpr, hxi]

@[simp] lemma mono_empty : mono K (∅ : Finset (Fin n)) = 1 := by
  funext x; simp [mono]

lemma mono_mul (T U : Finset (Fin n)) : mono K T * mono K U = mono K (T ∪ U) := by
  funext x
  simp only [Pi.mul_apply, mono_apply_eq]
  by_cases h : ∀ i ∈ T ∪ U, x i = true
  · have hT : ∀ i ∈ T, x i = true := fun i hi => h i (mem_union_left _ hi)
    have hU : ∀ i ∈ U, x i = true := fun i hi => h i (mem_union_right _ hi)
    rw [if_pos hT, if_pos hU, if_pos h, one_mul]
  · have hcopy := h
    push_neg at hcopy
    obtain ⟨i, hi, hxi⟩ := hcopy
    rw [if_neg h]
    rcases mem_union.1 hi with hi' | hi'
    · have h1 : ¬ (∀ j ∈ T, x j = true) := fun hc => hxi (hc i hi')
      rw [if_neg h1, zero_mul]
    · have h1 : ¬ (∀ j ∈ U, x j = true) := fun hc => hxi (hc i hi')
      rw [if_neg h1, mul_zero]

/-- The set of monomials of degree at most `D`. -/
def monoSet (K : Type*) [Field K] (n D : ℕ) : Set (Fn K n) :=
  Set.range (fun T : {T : Finset (Fin n) // T.card ≤ D} => mono K T.1)

/-- The submodule of functions of degree at most `D`. -/
def Deg (K : Type*) [Field K] (n D : ℕ) : Submodule K (Fn K n) :=
  Submodule.span K (monoSet K n D)

lemma mono_mem_Deg {T : Finset (Fin n)} {D : ℕ} (h : T.card ≤ D) : mono K T ∈ Deg K n D :=
  Submodule.subset_span ⟨⟨T, h⟩, rfl⟩

lemma Deg_le {D E : ℕ} (h : D ≤ E) : Deg K n D ≤ Deg K n E := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨T, hT⟩, rfl⟩
  exact mono_mem_Deg (hT.trans h)

lemma one_mem_Deg (D : ℕ) : (1 : Fn K n) ∈ Deg K n D := by
  have := mono_mem_Deg (K := K) (T := (∅ : Finset (Fin n))) (D := D) (by simp)
  simpa using this

lemma const_mem_Deg (c : K) (D : ℕ) : (fun _ : Cube n => c) ∈ Deg K n D := by
  have h := Submodule.smul_mem (Deg K n D) c (one_mem_Deg (K := K) (n := n) D)
  simpa [Pi.smul_def] using h

lemma mul_mem_Deg {f g : Fn K n} {a b : ℕ} (hf : f ∈ Deg K n a) (hg : g ∈ Deg K n b) :
    f * g ∈ Deg K n (a + b) := by
  have hmul := Submodule.mul_mem_mul hf hg
  rw [Deg, Deg, Submodule.span_mul_span] at hmul
  refine (Submodule.span_le.2 ?_) hmul
  rintro h ⟨f', ⟨⟨T, hT⟩, rfl⟩, g', ⟨⟨U, hU⟩, rfl⟩, rfl⟩
  show mono K T * mono K U ∈ Deg K n (a + b)
  rw [mono_mul]
  exact mono_mem_Deg (le_trans (card_union_le T U) (Nat.add_le_add hT hU))

lemma prod_mem_Deg {ι : Type*} (s : Finset ι) (f : ι → Fn K n) (d : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ Deg K n (d i)) : (∏ i ∈ s, f i) ∈ Deg K n (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one_mem_Deg (K := K) (n := n) 0
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact mul_mem_Deg (hf a (mem_insert_self a s))
        (ih (fun i hi => hf i (mem_insert_of_mem hi)))

lemma prod_mem_Deg' {ι : Type*} (s : Finset ι) (f : ι → Fn K n) (D : ℕ)
    (hf : ∀ i ∈ s, f i ∈ Deg K n D) : (∏ i ∈ s, f i) ∈ Deg K n (s.card * D) := by
  have := prod_mem_Deg s f (fun _ => D) hf
  simpa [Finset.sum_const, mul_comm, smul_eq_mul] using this

lemma pow_mem_Deg {f : Fn K n} {a : ℕ} (k : ℕ) (hf : f ∈ Deg K n a) : f ^ k ∈ Deg K n (k * a) := by
  induction k with
  | zero => simpa using one_mem_Deg (K := K) (n := n) 0
  | succ k ih =>
      have h := mul_mem_Deg ih hf
      have h2 : k * a + a = (k + 1) * a := by ring
      rw [pow_succ]
      rwa [h2] at h

lemma coord_mem_Deg (i : Fin n) : (fun x : Cube n => ind K (x i)) ∈ Deg K n 1 := by
  have h := mono_mem_Deg (K := K) (T := ({i} : Finset (Fin n))) (D := 1) (by simp)
  have he : mono K ({i} : Finset (Fin n)) = (fun x : Cube n => ind K (x i)) := by
    funext x; simp [mono]
  rwa [he] at h

/-- Every function on the cube has degree at most `n`. -/
lemma Deg_top : Deg K n n = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro f -
  have hdelta : ∀ y : Cube n, (fun x : Cube n => if x = y then (1 : K) else 0) ∈ Deg K n n := by
    intro y
    have hfac : (fun x : Cube n => if x = y then (1 : K) else 0)
        = ∏ i : Fin n, (fun x : Cube n => if x i = y i then (1 : K) else 0) := by
      funext x
      rw [Finset.prod_apply]
      by_cases hx : x = y
      · subst hx; simp
      · have hex : ∃ i, x i ≠ y i := by
          by_contra hc
          push_neg at hc
          exact hx (funext hc)
        obtain ⟨i, hi⟩ := hex
        rw [if_neg hx]
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
    rw [hfac]
    have hcoord : ∀ i : Fin n, (fun x : Cube n => if x i = y i then (1 : K) else 0) ∈ Deg K n 1 := by
      intro i
      cases hyi : y i
      · have he : (fun x : Cube n => if x i = false then (1 : K) else 0)
            = (fun _ => (1:K)) - (fun x : Cube n => ind K (x i)) := by
          funext x; cases hxi : x i <;> simp [ind, hxi]
        rw [he]
        exact Submodule.sub_mem _ (const_mem_Deg 1 1) (coord_mem_Deg i)
      · have he : (fun x : Cube n => if x i = true then (1 : K) else 0)
            = (fun x : Cube n => ind K (x i)) := by
          funext x; cases x i <;> simp [ind]
        rw [he]
        exact coord_mem_Deg i
    have hp := prod_mem_Deg' (Finset.univ : Finset (Fin n))
      (fun i => (fun x : Cube n => if x i = y i then (1 : K) else 0)) 1 (fun i _ => hcoord i)
    simpa using hp
  have hf : f = ∑ y : Cube n, (f y) • (fun x : Cube n => if x = y then (1 : K) else 0) := by
    funext x
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [hf]
  exact Submodule.sum_mem _ (fun y _ => Submodule.smul_mem _ _ (hdelta y))

end RS
end CS

import RequestProject.RS.Approx

/-!
# Gate-by-gate approximation of a circuit

`gate_step` shows that, given approximations of all gates below gate `i` which are correct on a
set `A` of inputs, gate `i` itself can be approximated by a function of degree `((q-1)*ℓ)^(depth)`
which is wrong on at most `2^n / 2^ℓ` of the inputs in `A`.
-/

namespace CS
namespace RS

open Finset
open scoped Classical

variable {K : Type*} [Field K] {n : ℕ}

theorem gate_step (q : ℕ) [Fact q.Prime] {K : Type*} [Field K] [CharP K q] {n : ℕ}
    (C : Circuit n) (l : ℕ) (hl : 1 ≤ l) (i : ℕ) (hi : i < C.size) (f : ℕ → Fn K n)
    (hdeg : ∀ j, j < i → f j ∈ Deg K n (((q-1)*l)^(C.dep j)))
    (A : Finset (Cube n)) (hA : ∀ x ∈ A, ∀ j, j < i → f j x = ind K (C.evalAt q x j)) :
    ∃ g : Fn K n, g ∈ Deg K n (((q-1)*l)^(C.dep i)) ∧
      2^l * (A.filter (fun x => g x ≠ ind K (C.evalAt q x i))).card ≤ 2^n := by
  classical
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  set Aq := (q-1)*l with hAqdef
  have hAq1 : 1 ≤ Aq := by
    rw [hAqdef]
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hchild : ∀ j ∈ (C.gates i).children, j < i := C.acyclic i hi
  have hchild_dep : ∀ j ∈ (C.gates i).children, C.dep j < C.dep i :=
    fun j hj => C.dep_child_lt hj (hchild j hj)
  set E := (if (C.gates i).children = [] then 0 else Aq^(C.dep i - 1)) with hEdef
  have hmemE : ∀ j ∈ (C.gates i).children, f j ∈ Deg K n E := by
    intro j hj
    have hne : (C.gates i).children ≠ [] := by
      intro h; rw [h] at hj; simp at hj
    rw [hEdef, if_neg hne]
    exact (Deg_le (Nat.pow_le_pow_right hAq1
      (by have := hchild_dep j hj; omega))) (hdeg j (hchild j hj))
  have hEbound : l * ((q-1) * E) ≤ Aq^(C.dep i) := by
    by_cases hne : (C.gates i).children = []
    · rw [hEdef, if_pos hne]; simp
    · obtain ⟨j, hj⟩ : ∃ j, j ∈ (C.gates i).children := by
        cases h : (C.gates i).children with
        | nil => exact absurd h hne
        | cons a t => exact ⟨a, by simp⟩
      have hdp : 1 ≤ C.dep i := by have := hchild_dep j hj; omega
      rw [hEdef, if_neg hne]
      have : l * ((q-1) * Aq^(C.dep i - 1)) = Aq^(C.dep i - 1 + 1) := by
        rw [pow_succ, hAqdef]; ring
      rw [this]
      exact le_of_eq (by congr 1; omega)
  have hEbound2 : (q-1) * E ≤ Aq^(C.dep i) := by
    refine le_trans ?_ hEbound
    calc (q-1) * E = 1 * ((q-1) * E) := by ring
      _ ≤ l * ((q-1) * E) := Nat.mul_le_mul_right _ hl
  have hEbound3 : E ≤ Aq^(C.dep i) := by
    refine le_trans ?_ hEbound2
    calc E = 1 * E := by ring
      _ ≤ (q-1) * E := Nat.mul_le_mul_right _ (by omega)
  -- a perfectly correct approximation has no error at all
  have hexact : ∀ g : Fn K n, (∀ x ∈ A, g x = ind K (C.evalAt q x i)) →
      2^l * (A.filter (fun x => g x ≠ ind K (C.evalAt q x i))).card ≤ 2^n := by
    intro g hg
    have hemp : A.filter (fun x => g x ≠ ind K (C.evalAt q x i)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx
      simpa using hg x hx
    rw [hemp]
    simp
  -- the value function used inside gate `i`
  set v : Cube n → ℕ → Bool := fun x j => if _h : j < i then C.evalAt q x j else false with hvdef
  have heval : ∀ x : Cube n, C.evalAt q x i = Gate.value q (C.gates i) x (v x) := by
    intro x
    rw [C.evalAt_eq x i]
  have hv : ∀ x, ∀ j ∈ (C.gates i).children, v x j = C.evalAt q x j := by
    intro x j hj
    rw [hvdef]
    simp [hchild j hj]
  clear_value E
  rcases hgate : C.gates i with k | b | j | lst | lst | lst
  · -- input gate
    refine ⟨fun x => ind K (x k), ?_, ?_⟩
    · have hd0 : C.dep i = 0 := C.dep_eq_zero (by rw [hgate]; rfl)
      rw [hd0, pow_zero]
      exact coord_mem_Deg k
    · refine hexact _ (fun x _ => ?_)
      rw [heval x, hgate]
      rfl
  · -- constant gate
    refine ⟨fun _ => ind K b, ?_, ?_⟩
    · exact const_mem_Deg _ _
    · refine hexact _ (fun x _ => ?_)
      rw [heval x, hgate]
      rfl
  · -- negation gate
    have hjc : j ∈ (C.gates i).children := by rw [hgate]; simp [Gate.children]
    refine ⟨(1 : Fn K n) - f j, ?_, ?_⟩
    · refine Submodule.sub_mem _ (one_mem_Deg _) ?_
      exact (Deg_le (Nat.pow_le_pow_right hAq1 (le_of_lt (hchild_dep j hjc)))) (hdeg j (hchild j hjc))
    · refine hexact _ (fun x hx => ?_)
      rw [heval x, hgate]
      have : Gate.value q (Gate.neg j) x (v x) = !(C.evalAt q x j) := by
        simp [Gate.value, hv x j hjc]
      rw [this, ind_not]
      simp only [Pi.sub_apply, Pi.one_apply]
      rw [hA x hx j (hchild j hjc)]
  · -- conjunction gate
    have hlst : ∀ t : Fin lst.length, lst.get t ∈ (C.gates i).children := by
      intro t; rw [hgate]; exact List.get_mem lst t
    set u : Fin lst.length → Fn K n := fun t => (1 : Fn K n) - f (lst.get t) with hudef
    set bb : Fin lst.length → Cube n → Bool := fun t x => !(C.evalAt q x (lst.get t)) with hbbdef
    have hu : ∀ x ∈ A, ∀ t, u t x = ind K (bb t x) := by
      intro x hx t
      rw [hudef, hbbdef]
      simp only [Pi.sub_apply, Pi.one_apply]
      rw [ind_not, hA x hx (lst.get t) (hchild _ (hlst t))]
    obtain ⟨S, hS⟩ := or_approx (l := l) q u bb A hu
    refine ⟨(1 : Fn K n) - orPoly q S u, ?_, ?_⟩
    · refine Submodule.sub_mem _ (one_mem_Deg _) ?_
      refine (Deg_le hEbound) (orPoly_mem_Deg q S u ?_)
      intro t
      exact Submodule.sub_mem _ (one_mem_Deg _) (hmemE _ (hlst t))
    · -- the target values agree
      have htarget : ∀ x, ind K (C.evalAt q x i)
          = 1 - ind K (decide (∃ t, bb t x = true)) := by
        intro x
        rw [heval x, hgate]
        have hval : Gate.value q (Gate.conj lst) x (v x) = lst.all (v x) := rfl
        rw [hval]
        by_cases hall : lst.all (v x) = true
        · have hnex : ¬ ∃ t, bb t x = true := by
            rintro ⟨t, ht⟩
            rw [hbbdef] at ht
            simp only [Bool.not_eq_true'] at ht
            have hmem : v x (lst.get t) = true := by
              rw [List.all_eq_true] at hall
              exact hall _ (List.get_mem lst t)
            rw [hv x _ (hlst t)] at hmem
            rw [hmem] at ht
            exact absurd ht (by simp)
          rw [hall, decide_eq_false hnex]
          simp [ind]
        · simp only [Bool.not_eq_true] at hall
          have hex : ∃ t, bb t x = true := by
            rw [List.all_eq_false] at hall
            obtain ⟨a, ha, hfa⟩ := hall
            obtain ⟨t, ht⟩ := List.mem_iff_get.1 ha
            refine ⟨t, ?_⟩
            rw [hbbdef]
            simp only
            rw [← hv x _ (hlst t), ht]
            simp [hfa]
          rw [hall, decide_eq_true hex]
          simp [ind]
      have hsets : (A.filter (fun x => ((1 : Fn K n) - orPoly q S u) x
            ≠ ind K (C.evalAt q x i)))
          = A.filter (fun x => orPoly q S u x ≠ ind K (decide (∃ t, bb t x = true))) := by
        refine Finset.filter_congr (fun x _ => ?_)
        rw [htarget x]
        simp only [Pi.sub_apply, Pi.one_apply, ne_eq, sub_right_inj]
      rw [hsets]
      exact hS
  · -- disjunction gate
    have hlst : ∀ t : Fin lst.length, lst.get t ∈ (C.gates i).children := by
      intro t; rw [hgate]; exact List.get_mem lst t
    set u : Fin lst.length → Fn K n := fun t => f (lst.get t) with hudef
    set bb : Fin lst.length → Cube n → Bool := fun t x => C.evalAt q x (lst.get t) with hbbdef
    have hu : ∀ x ∈ A, ∀ t, u t x = ind K (bb t x) := by
      intro x hx t
      rw [hudef, hbbdef]
      exact hA x hx (lst.get t) (hchild _ (hlst t))
    obtain ⟨S, hS⟩ := or_approx (l := l) q u bb A hu
    refine ⟨orPoly q S u, ?_, ?_⟩
    · refine (Deg_le hEbound) (orPoly_mem_Deg q S u ?_)
      intro t
      exact hmemE _ (hlst t)
    · have htarget : ∀ x, ind K (C.evalAt q x i) = ind K (decide (∃ t, bb t x = true)) := by
        intro x
        rw [heval x, hgate]
        have hval : Gate.value q (Gate.disj lst) x (v x) = lst.any (v x) := rfl
        rw [hval]
        by_cases hany : lst.any (v x) = true
        · have hex : ∃ t, bb t x = true := by
            rw [List.any_eq_true] at hany
            obtain ⟨a, ha, hfa⟩ := hany
            obtain ⟨t, ht⟩ := List.mem_iff_get.1 ha
            refine ⟨t, ?_⟩
            rw [hbbdef]
            simp only
            rw [← hv x _ (hlst t), ht]
            exact hfa
          rw [hany, decide_eq_true hex]
        · simp only [Bool.not_eq_true] at hany
          have hnex : ¬ ∃ t, bb t x = true := by
            rintro ⟨t, ht⟩
            rw [hbbdef] at ht
            simp only at ht
            rw [← hv x _ (hlst t)] at ht
            rw [List.any_eq_false] at hany
            exact absurd ht (by simpa using hany _ (List.get_mem lst t))
          rw [hany, decide_eq_false hnex]
      have hsets : (A.filter (fun x => orPoly q S u x ≠ ind K (C.evalAt q x i)))
          = A.filter (fun x => orPoly q S u x ≠ ind K (decide (∃ t, bb t x = true))) := by
        refine Finset.filter_congr (fun x _ => ?_)
        rw [htarget x]
      rw [hsets]
      exact hS
  · -- MOD q gate
    have hlst : ∀ j ∈ lst, j ∈ (C.gates i).children := by
      intro j hj; rw [hgate]; exact hj
    refine ⟨fun x => ((lst.map (fun j => f j x)).sum)^(q-1), ?_, ?_⟩
    · have hsum : (fun x => (lst.map (fun j => f j x)).sum) ∈ Deg K n E :=
        listSum_mem_Deg lst f E (fun j hj => hmemE j (hlst j hj))
      have hpow := pow_mem_Deg (q-1) hsum
      have hrw : (fun x => (lst.map (fun j => f j x)).sum)^(q-1)
          = (fun x => ((lst.map (fun j => f j x)).sum)^(q-1)) := by
        funext x; rw [Pi.pow_apply]
      rw [hrw] at hpow
      exact (Deg_le hEbound2) hpow
    · refine hexact _ (fun x hx => ?_)
      have hmapeq : (lst.map (fun j => f j x)) = lst.map (fun j => ind K (C.evalAt q x j)) := by
        refine List.map_congr_left (fun j hj => ?_)
        exact hA x hx j (hchild j (hlst j hj))
      rw [hmapeq, list_map_ind_sum, natCast_pow_q_sub_one K q]
      rw [heval x, hgate]
      have hval : Gate.value q (Gate.modq lst) x (v x)
          = decide (¬ q ∣ (lst.filter (v x)).length) := rfl
      rw [hval]
      have hfil : lst.filter (v x) = lst.filter (fun j => C.evalAt q x j) := by
        refine List.filter_congr (fun j hj => ?_)
        rw [hv x j (hlst j hj)]
      rw [hfil]
      by_cases hd : q ∣ (lst.filter (fun j => C.evalAt q x j)).length
      · rw [if_pos hd, decide_eq_false (by simpa using hd)]
        rfl
      · rw [if_neg hd, decide_eq_true (by simpa using hd)]
        rfl

/-- Gate-by-gate approximation: after processing the first `i` gates there are approximating
functions of the right degree whose total error set has size at most `i * 2^n / 2^ℓ`. -/
theorem Circuit.approx_upto (q : ℕ) [Fact q.Prime] {K : Type*} [Field K] [CharP K q] {n : ℕ}
    (C : Circuit n) (l : ℕ) (hl : 1 ≤ l) :
    ∀ i, i ≤ C.size → ∃ f : ℕ → Fn K n,
      (∀ j, j < i → f j ∈ Deg K n (((q-1)*l)^(C.dep j))) ∧
      2^l * ((univ : Finset (Cube n)).filter
        (fun x => ∃ j, j < i ∧ f j x ≠ ind K (C.evalAt q x j))).card ≤ i * 2^n := by
  classical
  intro i
  induction i with
  | zero =>
      intro _
      exact ⟨fun _ => 0, fun j hj => absurd hj (by omega), by simp⟩
  | succ i ih =>
      intro hi1
      have hi : i < C.size := by omega
      obtain ⟨f, hdeg, hbad⟩ := ih (by omega)
      set Bad := ((univ : Finset (Cube n)).filter
        (fun x => ∃ j, j < i ∧ f j x ≠ ind K (C.evalAt q x j))) with hBad
      set A := (univ : Finset (Cube n)) \ Bad with hAdef
      have hA : ∀ x ∈ A, ∀ j, j < i → f j x = ind K (C.evalAt q x j) := by
        intro x hx j hj
        rw [hAdef, Finset.mem_sdiff] at hx
        have := hx.2
        rw [hBad, Finset.mem_filter] at this
        push_neg at this
        exact this (Finset.mem_univ x) j hj
      obtain ⟨g, hgdeg, hgerr⟩ := gate_step q C l hl i hi f hdeg A hA
      refine ⟨Function.update f i g, ?_, ?_⟩
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
        · rw [Function.update_of_ne (by omega)]
          exact hdeg j hj'
        · rw [Function.update_self]
          exact hgdeg
      · have hsub : ((univ : Finset (Cube n)).filter
            (fun x => ∃ j, j < i + 1 ∧ (Function.update f i g) j x ≠ ind K (C.evalAt q x j)))
            ⊆ Bad ∪ A.filter (fun x => g x ≠ ind K (C.evalAt q x i)) := by
          intro x hx
          rw [Finset.mem_filter] at hx
          by_cases hxB : x ∈ Bad
          · exact Finset.mem_union_left _ hxB
          · refine Finset.mem_union_right _ ?_
            have hxA : x ∈ A := by
              rw [hAdef, Finset.mem_sdiff]
              exact ⟨Finset.mem_univ x, hxB⟩
            rw [Finset.mem_filter]
            refine ⟨hxA, ?_⟩
            obtain ⟨j, hj, hne⟩ := hx.2
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
            · rw [Function.update_of_ne (by omega)] at hne
              exact absurd (hA x hxA j hj') hne
            · rwa [Function.update_self] at hne
        have hcard := Finset.card_le_card hsub
        have hcard2 := Finset.card_union_le Bad (A.filter (fun x => g x ≠ ind K (C.evalAt q x i)))
        have h1 : 2^l * ((univ : Finset (Cube n)).filter
            (fun x => ∃ j, j < i + 1 ∧ (Function.update f i g) j x
              ≠ ind K (C.evalAt q x j))).card
            ≤ 2^l * (Bad.card + (A.filter (fun x => g x ≠ ind K (C.evalAt q x i))).card) :=
          Nat.mul_le_mul_left _ (le_trans hcard hcard2)
        have h2 : 2^l * (Bad.card + (A.filter (fun x => g x ≠ ind K (C.evalAt q x i))).card)
            ≤ i * 2^n + 2^n := by
          rw [Nat.mul_add]
          exact Nat.add_le_add hbad hgerr
        calc 2^l * ((univ : Finset (Cube n)).filter
              (fun x => ∃ j, j < i + 1 ∧ (Function.update f i g) j x
                ≠ ind K (C.evalAt q x j))).card ≤ i * 2^n + 2^n := le_trans h1 h2
          _ = (i + 1) * 2^n := by ring

/-- **Approximation lemma.** Every circuit of size `s` and depth `d` agrees with a function of
degree at most `((q-1)*ℓ)^d` outside a set of at most `s * 2^n / 2^ℓ` inputs. -/
theorem Circuit.exists_approx (q : ℕ) [Fact q.Prime] {K : Type*} [Field K] [CharP K q] {n : ℕ}
    (C : Circuit n) (l : ℕ) (hl : 1 ≤ l) :
    ∃ g : Fn K n, g ∈ Deg K n (((q-1)*l)^C.depth) ∧
      2^l * ((univ : Finset (Cube n)).filter (fun x => g x ≠ ind K (C.eval q x))).card
        ≤ C.size * 2^n := by
  classical
  obtain ⟨f, hdeg, hbad⟩ := C.approx_upto (K := K) q l hl C.size le_rfl
  refine ⟨f C.out, hdeg C.out C.out_lt, le_trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
    hbad⟩
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, ⟨C.out, C.out_lt, hx.2⟩⟩

end RS
end CS

import RequestProject.RS.Dimension
import RequestProject.RS.Circuit

/-!
# Smolensky's dimension argument

If a low-degree function `g` computes `x ↦ ζ^(weight x)` on a set `G` of inputs, where `ζ` is a
root of unity different from `1`, then `G` cannot be much bigger than half of the cube.
-/

namespace CS
namespace RS

open Finset

theorem smolensky_bound {K : Type*} [Field K] {n : ℕ} (zeta : K) (p : ℕ) (hp : 1 ≤ p)
    (hz : zeta ^ p = 1) (hz1 : zeta ≠ 1) (D : ℕ) (g : Fn K n) (hg : g ∈ Deg K n D)
    (G : Finset (Cube n)) (hG : ∀ x ∈ G, g x = zeta ^ (wt x)) :
    G.card ≤ ∑ i ∈ Finset.range (n/2 + D + 1), n.choose i := by
  classical
  have hz10 : zeta - 1 ≠ 0 := sub_ne_zero.2 hz1
  -- the two families of "linear" functions
  set z : Fin n → Fn K n := fun i x => if x i then zeta else 1 with hzdef
  set w : Fin n → Fn K n := fun i x => if x i then zeta ^ (p-1) else 1 with hwdef
  have hzmem : ∀ i, z i ∈ Deg K n 1 := by
    intro i
    have he : z i = (1 : Fn K n) + (zeta - 1) • (fun x : Cube n => ind K (x i)) := by
      funext x
      rw [hzdef]
      cases h : x i <;> simp [ind, h]
    rw [he]
    exact Submodule.add_mem _ (one_mem_Deg 1) (Submodule.smul_mem _ _ (coord_mem_Deg i))
  have hwmem : ∀ i, w i ∈ Deg K n 1 := by
    intro i
    have he : w i = (1 : Fn K n) + (zeta ^ (p-1) - 1) • (fun x : Cube n => ind K (x i)) := by
      funext x
      rw [hwdef]
      cases h : x i <;> simp [ind, h]
    rw [he]
    exact Submodule.add_mem _ (one_mem_Deg 1) (Submodule.smul_mem _ _ (coord_mem_Deg i))
  have hpowz : zeta * zeta ^ (p-1) = 1 := by
    calc zeta * zeta ^ (p-1) = zeta ^ (p - 1 + 1) := by rw [pow_succ]; ring
      _ = zeta ^ p := by congr 1; omega
      _ = 1 := hz
  have hzw : ∀ i x, z i x * w i x = 1 := by
    intro i x
    rw [hzdef, hwdef]
    simp only
    cases h : x i <;> simp [hpowz]
  have hprodz : ∀ x : Cube n, ∏ i : Fin n, z i x = zeta ^ (wt x) := by
    intro x
    rw [hzdef]
    simp only
    rw [Finset.prod_ite]
    simp [wt, Finset.prod_const]
  -- the multiplicative characters
  set chi : Finset (Fin n) → Fn K n := fun S => ∏ i ∈ S, z i with hchidef
  have hchimem : ∀ S : Finset (Fin n), chi S ∈ Deg K n S.card := by
    intro S
    have h := prod_mem_Deg' S z 1 (fun i _ => hzmem i)
    simpa [hchidef] using h
  -- restriction to `G`
  set R : Fn K n →ₗ[K] ({x : Cube n // x ∈ G} → K) :=
    LinearMap.funLeft K K (fun y : {x : Cube n // x ∈ G} => (y : Cube n)) with hRdef
  have hRapply : ∀ (F : Fn K n) (y : {x : Cube n // x ∈ G}), R F y = F (y : Cube n) := by
    intro F y; rfl
  have hRsurj : Function.Surjective R := by
    intro h
    refine ⟨fun x => if hx : x ∈ G then h ⟨x, hx⟩ else 0, ?_⟩
    funext y
    rw [hRapply]
    simp [y.2]
  set W := Deg K n (n/2 + D) with hWdef
  -- every character restricts into the image of `W`
  have hkey : ∀ S : Finset (Fin n), R (chi S) ∈ Submodule.map R W := by
    intro S
    by_cases hS : S.card ≤ n/2
    · exact ⟨chi S, (Deg_le (by omega)) (hchimem S), rfl⟩
    · push_neg at hS
      refine ⟨g * (∏ i ∈ univ \ S, w i), ?_, ?_⟩
      · have h1 : (∏ i ∈ univ \ S, w i) ∈ Deg K n (univ \ S).card := by
          have h := prod_mem_Deg' (univ \ S) w 1 (fun i _ => hwmem i)
          simpa using h
        have h2 := mul_mem_Deg hg h1
        refine (Deg_le ?_) h2
        have hcard : (univ \ S).card = n - S.card := by
          rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
          simp
        rw [hcard]
        omega
      · funext y
        obtain ⟨x, hx⟩ := y
        rw [hRapply, hRapply]
        show g x * (∏ i ∈ univ \ S, w i) x = chi S x
        rw [Finset.prod_apply, hchidef]
        simp only
        rw [Finset.prod_apply, hG x hx, ← hprodz x]
        rw [← Finset.prod_sdiff (Finset.subset_univ S)]
        rw [mul_comm ((∏ i ∈ univ \ S, z i x)) (∏ i ∈ S, z i x), mul_assoc,
          ← Finset.prod_mul_distrib]
        rw [Finset.prod_congr rfl (fun i _ => hzw i x)]
        simp
  -- the characters span everything
  have hspanchi : Submodule.span K (Set.range chi) = ⊤ := by
    rw [eq_top_iff, ← Deg_top (K := K) (n := n)]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨T, -⟩, rfl⟩
    show mono K T ∈ Submodule.span K (Set.range chi)
    -- `mono K T` is a combination of characters
    have hmonoeq : mono K T = ((zeta - 1)⁻¹) ^ T.card • ∏ i ∈ T, (z i - 1) := by
      funext x
      rw [Pi.smul_apply, Finset.prod_apply, smul_eq_mul]
      have hfac : ∀ i ∈ T, (z i - 1) x = (zeta - 1) * ind K (x i) := by
        intro i _
        rw [Pi.sub_apply, hzdef]
        cases h : x i <;> simp [ind, h]
      rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const]
      rw [mono, ← mul_assoc, ← mul_pow]
      rw [inv_mul_cancel₀ hz10, one_pow, one_mul]
    rw [hmonoeq]
    refine Submodule.smul_mem _ _ ?_
    have hexp : (∏ i ∈ T, (z i - 1)) = ∑ S ∈ T.powerset, (chi S) * ∏ _i ∈ T \ S, (-1 : Fn K n) := by
      have := Finset.prod_add (fun i => z i) (fun _ => (-1 : Fn K n)) T
      simpa [sub_eq_add_neg, hchidef] using this
    rw [hexp]
    refine Submodule.sum_mem _ (fun S _ => ?_)
    have hconst : (chi S) * ∏ _i ∈ T \ S, (-1 : Fn K n) = ((-1 : K) ^ (T \ S).card) • chi S := by
      funext x
      simp [Finset.prod_const, mul_comm]
    rw [hconst]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)
  -- hence the restriction of `W` is everything
  have hmap : Submodule.map R W = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Submodule K ({x : Cube n // x ∈ G} → K))
        = LinearMap.range R := (LinearMap.range_eq_top.2 hRsurj).symm
      _ = Submodule.map R ⊤ := (Submodule.map_top R).symm
      _ = Submodule.map R (Submodule.span K (Set.range chi)) := by rw [hspanchi]
      _ = Submodule.span K (R '' (Set.range chi)) := Submodule.map_span R _
      _ ≤ Submodule.map R W := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨_, ⟨S, rfl⟩, rfl⟩
          exact hkey S
  -- dimension count
  have hcardG : G.card = Module.finrank K ({x : Cube n // x ∈ G} → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  calc G.card = Module.finrank K ({x : Cube n // x ∈ G} → K) := hcardG
    _ = Module.finrank K (⊤ : Submodule K ({x : Cube n // x ∈ G} → K)) :=
        (finrank_top K _).symm
    _ = Module.finrank K (Submodule.map R W) := by rw [hmap]
    _ ≤ Module.finrank K W := Submodule.finrank_map_le R W
    _ ≤ ∑ i ∈ Finset.range (n/2 + D + 1), n.choose i := finrank_Deg_le K n (n/2 + D)

end RS
end CS

import RequestProject.RS.Degree

/-!
# The dimension of the space of low-degree functions
-/

namespace CS
namespace RS

open Finset

lemma card_subtype_card_le (n D : ℕ) :
    Fintype.card {T : Finset (Fin n) // T.card ≤ D} = ∑ i ∈ Finset.range (D+1), n.choose i := by
  classical
  rw [Fintype.card_subtype]
  have hsplit : (univ.filter (fun T : Finset (Fin n) => T.card ≤ D))
      = (Finset.range (D+1)).biUnion (fun i => Finset.powersetCard i univ) := by
    ext T
    simp only [mem_filter, mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Finset.subset_univ, true_and, Nat.lt_succ_iff]
    constructor
    · intro h; exact ⟨T.card, h, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact hi
  rw [hsplit, Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.card_powersetCard]
    simp
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_powersetCard]
    rintro T ⟨-, hTi⟩ ⟨-, hTj⟩
    exact hij (hTi ▸ hTj ▸ rfl)

lemma finrank_Deg_le (K : Type*) [Field K] (n D : ℕ) :
    Module.finrank K (Deg K n D) ≤ ∑ i ∈ Finset.range (D+1), n.choose i := by
  classical
  have h1 : Deg K n D = LinearMap.range (Fintype.linearCombination K
      (fun T : {T : Finset (Fin n) // T.card ≤ D} => mono K T.1)) := by
    rw [Fintype.range_linearCombination]
    rfl
  rw [h1]
  calc Module.finrank K (LinearMap.range (Fintype.linearCombination K
        (fun T : {T : Finset (Fin n) // T.card ≤ D} => mono K T.1)))
      ≤ Module.finrank K ({T : Finset (Fin n) // T.card ≤ D} → K) :=
        LinearMap.finrank_range_le _
    _ = Fintype.card {T : Finset (Fin n) // T.card ≤ D} :=
        Module.finrank_fintype_fun_eq_card K
    _ = ∑ i ∈ Finset.range (D+1), n.choose i := card_subtype_card_le n D

end RS
end CS

import Mathlib

/-!
# Binomial estimates

The counting estimates needed for the Razborov–Smolensky theorem: the sum of the binomial
coefficients `C(n,i)` for `i ≤ n/2 + D` is at most `2^(n-1) + D * C(n, n/2)`, and the central
binomial coefficient is small compared to `2^n / √n`.
-/

namespace CS
namespace RS

open Finset

/-- A sharp form of `C(2m,m) ≤ 4^m / √(3m+1)`. -/
lemma central_binom_sq (m : ℕ) : (3*m+1) * (Nat.centralBinom m)^2 ≤ 16^m := by
  induction m with
  | zero => simp [Nat.centralBinom]
  | succ m ih =>
      have hkey : (m+1) * (m+1).centralBinom = 2 * (2*m+1) * m.centralBinom :=
        Nat.succ_mul_centralBinom_succ m
      have hsq : ((m+1) * (m+1).centralBinom)^2 = (2 * (2*m+1))^2 * (m.centralBinom)^2 := by
        rw [hkey]; ring
      -- multiply the goal by `(m+1)^2`
      have hgoal : (3*(m+1)+1) * ((m+1) * (m+1).centralBinom)^2 ≤ 16^(m+1) * (m+1)^2 := by
        rw [hsq]
        have harith : (3*(m+1)+1) * (2 * (2*m+1))^2 ≤ 16 * (m+1)^2 * (3*m+1) := by
          nlinarith [sq_nonneg m, Nat.zero_le m]
        calc (3*(m+1)+1) * ((2 * (2*m+1))^2 * (m.centralBinom)^2)
            = ((3*(m+1)+1) * (2 * (2*m+1))^2) * (m.centralBinom)^2 := by ring
          _ ≤ (16 * (m+1)^2 * (3*m+1)) * (m.centralBinom)^2 :=
              Nat.mul_le_mul_right _ harith
          _ = (16 * (m+1)^2) * ((3*m+1) * (m.centralBinom)^2) := by ring
          _ ≤ (16 * (m+1)^2) * 16^m := Nat.mul_le_mul_left _ ih
          _ = 16^(m+1) * (m+1)^2 := by ring
      have hpos : 0 < (m+1)^2 := by positivity
      have hfinal : ((3*(m+1)+1) * ((m+1).centralBinom)^2) * (m+1)^2 ≤ 16^(m+1) * (m+1)^2 := by
        calc ((3*(m+1)+1) * ((m+1).centralBinom)^2) * (m+1)^2
            = (3*(m+1)+1) * ((m+1) * (m+1).centralBinom)^2 := by ring
          _ ≤ 16^(m+1) * (m+1)^2 := hgoal
      exact Nat.le_of_mul_le_mul_right hfinal hpos

lemma choose_odd_middle (m : ℕ) : (2*m+2).choose (m+1) = 2 * ((2*m+1).choose m) := by
  have h1 : (2*m+2).choose (m+1) = (2*m+1).choose m + (2*m+1).choose (m+1) := by
    rw [show 2*m+2 = (2*m+1)+1 by ring, Nat.choose_succ_succ]
  have h2 : (2*m+1).choose (m+1) = (2*m+1).choose m := by
    rw [show m+1 = (2*m+1) - m by omega]
    exact Nat.choose_symm (by omega)
  omega

/-- If `D` is small compared to `√m`, then `D * C(2m+1, m)` is at most a quarter of `2^(2m+1)`. -/
lemma mul_choose_le (m D : ℕ) (hm : 1 ≤ m) (h : 16 * D^2 ≤ m) :
    D * ((2*m+1).choose m) ≤ 2^(2*m-1) := by
  set c1 := (2*m+1).choose m with hc1
  have hcb : (m+1).centralBinom = 2 * c1 := by
    rw [Nat.centralBinom, hc1, show 2*(m+1) = 2*m+2 by ring]
    exact choose_odd_middle m
  have hsq := central_binom_sq (m+1)
  rw [hcb] at hsq
  -- hsq : (3*(m+1)+1) * (2*c1)^2 ≤ 16^(m+1)
  -- work with squares
  have h4 : 4 * (3*m+4) * (D * c1)^2 ≤ 4 * (3*m+4) * (2^(2*m-1))^2 := by
    have hstep1 : 4 * (3*m+4) * (D * c1)^2 = D^2 * ((3*m+4) * (2*c1)^2) := by ring
    have hstep2 : D^2 * ((3*m+4) * (2*c1)^2) ≤ D^2 * 16^(m+1) := by
      refine Nat.mul_le_mul_left _ ?_
      calc (3*m+4) * (2*c1)^2 = (3*(m+1)+1) * (2*c1)^2 := by ring
        _ ≤ 16^(m+1) := hsq
    have hstep3 : D^2 * 16^(m+1) ≤ 4 * (3*m+4) * (2^(2*m-1))^2 := by
      have hex : (2:ℕ)^(2*m-1) * 2^(2*m-1) = 2^(4*m-2) := by
        rw [← pow_add]; congr 1; omega
      have h16 : (16:ℕ)^(m+1) = 16 * 16^m := by ring
      have h16m : (16:ℕ)^m = 4 * 2^(4*m-2) := by
        have h2 : (16:ℕ)^m = 2^(4*m) := by
          rw [show (16:ℕ) = 2^4 by norm_num, ← pow_mul, Nat.mul_comm]
        rw [h2, show 4*m = 2 + (4*m-2) by omega, pow_add]
        norm_num
      have hD : 16 * D^2 ≤ 3*m+4 := by omega
      calc D^2 * 16^(m+1) = (16 * D^2) * 16^m := by rw [h16]; ring
        _ ≤ (3*m+4) * 16^m := Nat.mul_le_mul_right _ hD
        _ = (3*m+4) * (4 * 2^(4*m-2)) := by rw [h16m]
        _ = 4 * (3*m+4) * (2^(2*m-1))^2 := by rw [← hex]; ring
    exact le_trans (le_of_eq hstep1) (le_trans hstep2 hstep3)
  have hpos : 0 < 4 * (3*m+4) := by omega
  have hsq2 : (D * c1)^2 ≤ (2^(2*m-1))^2 := Nat.le_of_mul_le_mul_left h4 hpos
  exact (Nat.pow_le_pow_iff_left (n := 2) (by norm_num)).1 hsq2

/-- The sum of binomial coefficients up to `m + D` where `n = 2m+1`. -/
lemma sum_choose_le (m D : ℕ) :
    ∑ i ∈ Finset.range (m + D + 1), (2*m+1).choose i ≤ 4^m + D * ((2*m+1).choose m) := by
  have hsplit : ∑ i ∈ Finset.range (m + D + 1), (2*m+1).choose i
      = (∑ i ∈ Finset.range (m + 1), (2*m+1).choose i)
        + ∑ i ∈ Finset.Ico (m+1) (m + D + 1), (2*m+1).choose i := by
    simp only [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le (m+1)) (by omega : m+1 ≤ m + D + 1)]
  rw [hsplit, Nat.sum_range_choose_halfway m]
  refine Nat.add_le_add_left ?_ _
  calc ∑ i ∈ Finset.Ico (m+1) (m + D + 1), (2*m+1).choose i
      ≤ ∑ _i ∈ Finset.Ico (m+1) (m + D + 1), ((2*m+1).choose m) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have := Nat.choose_le_middle i (2*m+1)
        rwa [show (2*m+1)/2 = m by omega] at this
    _ = D * ((2*m+1).choose m) := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
        congr 1
        omega

end RS
end CS

