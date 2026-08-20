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
