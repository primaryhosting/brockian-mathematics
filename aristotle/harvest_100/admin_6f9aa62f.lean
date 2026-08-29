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
Isolation (Valiant–Vazirani) lemma over `GF(2)`, in the counting form needed for
Toda's theorem.
-/
import Mathlib

namespace CS.Toda

open Finset

/-- Bit vectors of length `m`, as vectors over `GF(2)`. -/
abbrev Vec (m : ℕ) := Fin m → ZMod 2

/-- The standard `GF(2)`-bilinear form. -/
def ip {m : ℕ} (u v : Vec m) : ZMod 2 := ∑ i, u i * v i

lemma ip_comm {m : ℕ} (u v : Vec m) : ip u v = ip v u := by simp [ip, mul_comm]

lemma ip_add {m : ℕ} (u v w : Vec m) : ip u (v + w) = ip u v + ip u w := by
  simp [ip, mul_add, Finset.sum_add_distrib]

lemma ip_single {m : ℕ} (u : Vec m) (i0 : Fin m) : ip u (Pi.single i0 1) = u i0 := by
  simp [ip, Pi.single_apply]

lemma zmod2_ne_zero {z : ZMod 2} (h : z ≠ 0) : z = 1 := by revert h; revert z; decide

lemma single_add_single {m : ℕ} (i0 : Fin m) :
    (Pi.single i0 1 : Vec m) + Pi.single i0 1 = 0 := by
  funext j; simp [Pi.single_apply]; split <;> decide

/-- A nonzero linear form over `GF(2)` vanishes on exactly half of the space. -/
lemma card_ip_zero {m : ℕ} {u : Vec m} (hu : u ≠ 0) :
    2 * (univ.filter (fun v : Vec m => ip u v = 0)).card = 2 ^ m := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i, u i ≠ 0 := by
    by_contra h; push_neg at h; exact hu (funext h)
  have hu1 : u i0 = 1 := zmod2_ne_zero hi0
  have hbij : (univ.filter (fun v : Vec m => ip u v = 0)).card
      = (univ.filter (fun v : Vec m => ip u v = 1)).card := by
    apply Finset.card_nbij' (fun v => v + Pi.single i0 1) (fun v => v + Pi.single i0 1)
    · intro v hv
      simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hv ⊢
      rw [ip_add, ip_single, hv, hu1]; ring
    · intro v hv
      simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hv ⊢
      rw [ip_add, ip_single, hv, hu1]; decide
    · intro v _; simp [add_assoc, single_add_single]
    · intro v _; simp [add_assoc, single_add_single]
  have htot : (univ.filter (fun v : Vec m => ip u v = 0)).card
      + (univ.filter (fun v : Vec m => ip u v = 1)).card = 2 ^ m := by
    have h2 : (univ.filter (fun v : Vec m => ip u v = 1))
        = (univ.filter (fun v : Vec m => ¬ (ip u v = 0))) := by
      apply Finset.filter_congr
      intro v _
      exact ⟨fun h => by rw [h]; decide, fun h => zmod2_ne_zero h⟩
    rw [h2, Finset.card_filter_add_card_filter_not]
    simp
  omega

/-- The space of hash functions: `m+1` linear forms together with `m+1` constants. -/
abbrev Hsp (m : ℕ) := Fin (m+1) → (Vec m × ZMod 2)

/-- `y` survives the hash `h` cut down to its first `k` rows. -/
def survives {m : ℕ} (h : Hsp m) (k : ℕ) (y : Vec m) : Prop :=
  ∀ i : Fin (m+1), (i:ℕ) < k → ip (h i).1 y = (h i).2

instance {m : ℕ} (h : Hsp m) (k : ℕ) : DecidablePred (survives h k) :=
  fun _ => by unfold survives; infer_instance

lemma card_filter_lt {m k : ℕ} (hk : k ≤ m+1) :
    ((univ : Finset (Fin (m+1))).filter (fun i : Fin (m+1) => (i:ℕ) < k)).card = k := by
  classical
  rw [show ((univ : Finset (Fin (m+1))).filter (fun i : Fin (m+1) => (i:ℕ) < k))
      = (Finset.range k).attachFin (by intro x hx; simp at hx; omega) from ?_]
  · simp
  · ext i; simp [Finset.mem_attachFin]

lemma prod_ite_lt {M : Type*} [CommMonoid M] {m k : ℕ} (hk : k ≤ m+1) (a b : M) :
    ∏ i : Fin (m+1), (if (i:ℕ) < k then a else b) = a^k * b^(m+1-k) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [card_filter_lt hk]
  congr 1
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (m+1))))
      (p := fun i : Fin (m+1) => (i:ℕ) < k)
  rw [card_filter_lt hk] at this
  simp only [Finset.card_univ, Fintype.card_fin] at this
  congr 1
  omega

lemma card_pair_single {m : ℕ} (y : Vec m) :
    (univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2)).card = 2^m := by
  classical
  rw [show (univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2)).card
      = (univ : Finset (Vec m)).card from ?_]
  · simp
  · apply Finset.card_nbij' (fun p => p.1) (fun r => (r, ip r y)) <;>
      intro p hp <;> simp_all

lemma card_pair_double {m : ℕ} {y y' : Vec m} (hne : y ≠ y') :
    2 * (univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2 ∧ ip p.1 y' = p.2)).card
      = 2^m := by
  classical
  have hu : y + y' ≠ 0 := by
    intro h
    exact hne (funext fun j =>
      (by decide : ∀ a b : ZMod 2, a + b = 0 → a = b) (y j) (y' j) (congrFun h j))
  rw [show (univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2 ∧ ip p.1 y' = p.2)).card
      = (univ.filter (fun r : Vec m => ip (y+y') r = 0)).card from ?_]
  · exact card_ip_zero hu
  · apply Finset.card_nbij' (fun p => p.1) (fun r => (r, ip r y))
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hp ⊢
      rw [ip_comm, ip_add, hp.1, hp.2]
      exact (by decide : ∀ z : ZMod 2, z + z = 0) _
    · intro r hr
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hr ⊢
      rw [ip_comm, ip_add] at hr
      have h2 : ip r y' = ip r y := by
        have h3 : ip r y' = - ip r y := by linear_combination (norm := abel_nf) hr
        rw [h3]; exact (by decide : ∀ z : ZMod 2, -z = z) _
      exact h2
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hp
      simp [hp.1]
    · intro r _; rfl

lemma card_Hsp (m : ℕ) : Fintype.card (Hsp m) = (2^(m+1))^(m+1) := by
  simp [Hsp, Fintype.card_fun, pow_succ]

/-- The number of hashes under which a fixed `y` survives. -/
lemma card_surv_single {m k : ℕ} (hk : k ≤ m+1) (y : Vec m) :
    2^k * (univ.filter (fun h : Hsp m => survives h k y)).card = (2^(m+1))^(m+1) := by
  classical
  have hset : (univ.filter (fun h : Hsp m => survives h k y))
      = Fintype.piFinset (fun i : Fin (m+1) =>
          if (i:ℕ) < k then univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2) else univ) := by
    ext h
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, survives]
    constructor
    · intro hh i
      by_cases hi : (i:ℕ) < k <;> simp [hi, hh i]
    · intro hh i hi
      have := hh i
      simp [hi] at this
      exact this
  rw [hset, Fintype.card_piFinset]
  rw [show (∏ i : Fin (m+1),
      (if (i:ℕ) < k then univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2) else univ).card)
      = ∏ i : Fin (m+1), (if (i:ℕ) < k then 2^m else 2^(m+1)) from ?_]
  · rw [prod_ite_lt hk]
    rw [← mul_assoc]
    rw [show (2:ℕ)^k * (2^m)^k = (2^(m+1))^k by rw [← mul_pow, ← pow_succ']]
    rw [← pow_add]
    congr 1
    omega
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hi : (i:ℕ) < k <;> simp [hi, card_pair_single y, pow_succ]

/-- The number of hashes under which two distinct `y, y'` both survive. -/
lemma card_surv_double {m k : ℕ} (hk : k ≤ m+1) {y y' : Vec m} (hne : y ≠ y') :
    4^k * (univ.filter (fun h : Hsp m => survives h k y ∧ survives h k y')).card
      = (2^(m+1))^(m+1) := by
  classical
  set c := (univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2 ∧ ip p.1 y' = p.2)).card with hc
  have hc2 : 2 * c = 2^m := card_pair_double hne
  have hset : (univ.filter (fun h : Hsp m => survives h k y ∧ survives h k y'))
      = Fintype.piFinset (fun i : Fin (m+1) =>
          if (i:ℕ) < k then
            univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2 ∧ ip p.1 y' = p.2)
          else univ) := by
    ext h
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, survives]
    constructor
    · intro hh i
      by_cases hi : (i:ℕ) < k <;> simp [hi, hh.1 i, hh.2 i]
    · intro hh
      constructor <;>
      · intro i hi
        have := hh i
        simp [hi] at this
        tauto
  rw [hset, Fintype.card_piFinset]
  rw [show (∏ i : Fin (m+1),
      (if (i:ℕ) < k then
        univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2 ∧ ip p.1 y' = p.2)
       else univ).card)
      = ∏ i : Fin (m+1), (if (i:ℕ) < k then c else 2^(m+1)) from ?_]
  · rw [prod_ite_lt hk]
    rw [← mul_assoc]
    rw [show (4:ℕ)^k * c^k = (2^(m+1))^k by
      rw [← mul_pow]
      congr 1
      have h4 : (4:ℕ) * c = 2 * (2 * c) := by ring
      rw [h4, hc2, pow_succ]
      ring]
    rw [← pow_add]
    congr 1
    omega
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hi : (i:ℕ) < k <;> simp [hi, hc, pow_succ]

/-- Isolation for a fixed, well chosen number `k` of hash rows. -/
lemma isolation_fixed_k {m k : ℕ} (hk : k ≤ m+1) (A : Finset (Vec m))
    (h1 : 2 * A.card ≤ 2^k) (h2 : 2^k < 4 * A.card) :
    8 * ((univ : Finset (Hsp m)).filter
        (fun h => (A.filter (survives h k)).card = 1)).card ≥ (2^(m+1))^(m+1) := by
  classical
  set HC := (2^(m+1))^(m+1) with hHC
  set a := A.card with ha
  set D := fun (p : Vec m × Vec m) =>
    ((univ : Finset (Hsp m)).filter (fun h => survives h k p.1 ∧ survives h k p.2)).card with hD
  set N := fun (y : Vec m) => ((univ : Finset (Hsp m)).filter (fun h => survives h k y)).card with hN
  set S := ((univ : Finset (Hsp m)).filter (fun h => (A.filter (survives h k)).card = 1)).card with hS
  have hsum1 : ∑ h : Hsp m, (A.filter (survives h k)).card = ∑ y ∈ A, N y := by
    simp only [hN, Finset.card_filter]
    rw [Finset.sum_comm]
  have hsum2 : ∑ h : Hsp m, ((A.filter (survives h k)).card * ((A.filter (survives h k)).card - 1))
      = ∑ p ∈ A.offDiag, D p := by
    have hoff : ∀ h : Hsp m,
        (A.filter (survives h k)).card * ((A.filter (survives h k)).card - 1)
          = (A.offDiag.filter (fun p => survives h k p.1 ∧ survives h k p.2)).card := by
      intro h
      rw [← Finset.offDiag_card]
      congr 1
      ext p
      simp only [Finset.mem_offDiag, Finset.mem_filter]
      tauto
    simp only [hoff, hD, Finset.card_filter]
    rw [Finset.sum_comm]
  have hpoint : ∀ h : Hsp m,
      (A.filter (survives h k)).card
        ≤ (if (A.filter (survives h k)).card = 1 then 1 else 0)
        + (A.filter (survives h k)).card * ((A.filter (survives h k)).card - 1) := by
    intro h
    rcases Nat.lt_or_ge (A.filter (survives h k)).card 2 with hlt | hge
    · interval_cases hh : (A.filter (survives h k)).card <;> simp
    · have : (A.filter (survives h k)).card * 1
          ≤ (A.filter (survives h k)).card * ((A.filter (survives h k)).card - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  have hkey : ∑ y ∈ A, N y ≤ S + ∑ p ∈ A.offDiag, D p := by
    have hSsum : S = ∑ h : Hsp m, (if (A.filter (survives h k)).card = 1 then 1 else 0) := by
      rw [hS, Finset.card_filter]
    rw [hSsum, ← hsum1, ← hsum2, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun h _ => hpoint h)
  have hAne : A.Nonempty := by
    rcases Finset.eq_empty_or_nonempty A with rfl | h
    · simp at h2
    · exact h
  obtain ⟨y0, hy0⟩ := hAne
  have hDval : ∀ p ∈ A.offDiag, 4^k * D p = HC := by
    intro p hp
    simp only [Finset.mem_offDiag] at hp
    exact card_surv_double hk hp.2.2
  have hNval : ∀ y : Vec m, 2^k * N y = HC := fun y => card_surv_single hk y
  rcases Finset.eq_empty_or_nonempty A.offDiag with hoffE | hoffN
  · have hcard1 : a = 1 := by
      have hc := Finset.offDiag_card (s := A)
      rw [hoffE] at hc
      simp only [Finset.card_empty] at hc
      have h1' : 1 ≤ a := Finset.card_pos.mpr ⟨y0, hy0⟩
      nlinarith [hc]
    have hk1 : 2^k = 2 := by omega
    have hsum : ∑ y ∈ A, N y = N y0 := by
      rw [Finset.sum_eq_single y0]
      · intro b hb hbne
        exfalso
        have hmem : (b, y0) ∈ A.offDiag := by
          simp only [Finset.mem_offDiag]
          exact ⟨hb, hy0, hbne⟩
        rw [hoffE] at hmem
        simp at hmem
      · intro h; exact absurd hy0 h
    have hN0 : 2 * N y0 = HC := by rw [← hk1]; exact hNval y0
    rw [hoffE] at hkey
    simp only [Finset.sum_empty, add_zero, hsum] at hkey
    omega
  · obtain ⟨p0, hp0⟩ := hoffN
    have hDsum : ∑ p ∈ A.offDiag, D p = A.offDiag.card * D p0 := by
      rw [Finset.sum_congr rfl (fun p hp => ?_), Finset.sum_const, smul_eq_mul]
      have h1' := hDval p hp
      have h2' := hDval p0 hp0
      have hpow : (0:ℕ) < 4^k := by positivity
      exact Nat.eq_of_mul_eq_mul_left hpow (by omega)
    have hNsum : ∑ y ∈ A, N y = a * N y0 := by
      rw [Finset.sum_congr rfl (fun y hy => ?_), Finset.sum_const, smul_eq_mul, ha]
      have h1' := hNval y
      have h2' := hNval y0
      have hpow : (0:ℕ) < 2^k := by positivity
      exact Nat.eq_of_mul_eq_mul_left hpow (by omega)
    have hoffcard : A.offDiag.card = a * a - a := Finset.offDiag_card A
    have hNv : 2^k * N y0 = HC := hNval y0
    have hDv' : 4^k * D p0 = HC := hDval p0 hp0
    have h4 : (4:ℕ)^k = 2^k * 2^k := by
      rw [show (4:ℕ) = 2*2 by norm_num, mul_pow]
    have hND : N y0 = 2^k * D p0 := by
      have hpos : (0:ℕ) < 2^k := by positivity
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [hNv, ← hDv', h4, mul_assoc]
    have ha1 : 1 ≤ a := Finset.card_pos.mpr ⟨y0, hy0⟩
    obtain ⟨b, hb⟩ : ∃ b, a + b = 2^k := ⟨2^k - a, by omega⟩
    have hb2 : a + b ≤ 2 * b := by omega
    have hb3 : a + b + 1 ≤ 4 * a := by omega
    have haa : a * a - a + a = a * a := by
      have : a ≤ a * a := Nat.le_mul_of_pos_left a ha1
      omega
    have hstep : (a+b) * (a+b) + 8 * (a*a - a) ≤ 8 * (a * (a+b)) := by
      nlinarith [hb2, hb3, ha1, haa]
    have harith : 4^k * D p0 + 8 * ((a*a - a) * D p0) ≤ 8 * (a * (2^k * D p0)) := by
      rw [h4, ← hb]
      calc (a+b) * (a+b) * D p0 + 8 * ((a*a-a) * D p0)
          = ((a+b) * (a+b) + 8 * (a*a - a)) * D p0 := by ring
        _ ≤ (8 * (a * (a+b))) * D p0 := Nat.mul_le_mul_right _ hstep
        _ = 8 * (a * ((a+b) * D p0)) := by ring
    rw [hDsum, hNsum, hND, hoffcard] at hkey
    omega

/-- For every nonempty `A ⊆ GF(2)^m` there is a suitable number of hash rows. -/
lemma exists_good_k {m a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ 2^m) :
    ∃ k, 1 ≤ k ∧ k ≤ m+1 ∧ 2 * a ≤ 2^k ∧ 2^k < 4 * a := by
  induction m with
  | zero =>
    simp only [pow_zero] at h2
    exact ⟨1, by norm_num, by norm_num, by norm_num; omega, by norm_num; omega⟩
  | succ n ih =>
    by_cases hle : a ≤ 2^n
    · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih h1 hle
      exact ⟨k, hk1, by omega, hk3, hk4⟩
    · push_neg at hle
      refine ⟨n+2, by omega, by omega, ?_, ?_⟩
      · have hp : (2:ℕ)^(n+2) = 2 * 2^(n+1) := by ring
        omega
      · have hp : (2:ℕ)^(n+2) = 4 * 2^n := by ring
        omega

/-- **Isolation lemma.**  For a nonempty set `A` of bit vectors, at least a `1/(8(m+2))`
fraction of the pairs `(k, h)` isolate exactly one element of `A`. -/
theorem isolation {m : ℕ} (A : Finset (Vec m)) (hA : A.Nonempty) :
    8 * (m+2) * ((univ : Finset (Fin (m+2) × Hsp m)).filter
        (fun p => (A.filter (survives p.2 (p.1 : ℕ))).card = 1)).card
      ≥ Fintype.card (Fin (m+2) × Hsp m) := by
  classical
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
    exists_good_k (a := A.card) (Finset.card_pos.mpr hA)
      (by simpa using Finset.card_le_univ A)
  have hkey := isolation_fixed_k (m := m) (k := k) hk2 A hk3 hk4
  set G := ((univ : Finset (Fin (m+2) × Hsp m)).filter
      (fun p => (A.filter (survives p.2 (p.1 : ℕ))).card = 1)) with hG
  set Gk := ((univ : Finset (Hsp m)).filter
      (fun h => (A.filter (survives h k)).card = 1)) with hGk
  have hsub : Gk.card ≤ G.card := by
    apply Finset.card_le_card_of_injOn (fun h => ((⟨k, by omega⟩ : Fin (m+2)), h))
    · intro h hh
      simp only [hGk, mem_filter, mem_univ, true_and] at hh
      simp only [hG, mem_filter, mem_univ, true_and]
      exact hh
    · intro x _ y _ hxy
      simpa using hxy
  have hcard : Fintype.card (Fin (m+2) × Hsp m) = (m+2) * (2^(m+1))^(m+1) := by
    simp [card_Hsp]
  rw [hcard]
  calc 8 * (m+2) * G.card = (m+2) * (8 * G.card) := by ring
    _ ≥ (m+2) * (8 * Gk.card) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsub)
    _ ≥ (m+2) * (2^(m+1))^(m+1) := Nat.mul_le_mul_left _ hkey

end CS.Toda

