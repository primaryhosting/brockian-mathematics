import Mathlib
import RequestProject.KahnKalai.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Expectation and threshold are within a log factor: a formalisation of the Park–Pham proof
of the Kahn–Kalai conjecture.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased measure of a family of subsets. -/
noncomputable def mu (p : ℝ) (F : Finset (Finset α)) : ℝ := ∑ U ∈ F, weight p U

/-- The up-closure `⟨H⟩` of a hypergraph. -/
noncomputable def upClosure (H : Finset (Finset α)) : Finset (Finset α) :=
  Finset.univ.filter (fun U => ∃ S ∈ H, S ⊆ U)

/-- A family is increasing (an up-set). -/
def Increasing (F : Finset (Finset α)) : Prop := ∀ A ∈ F, ∀ B : Finset α, A ⊆ B → B ∈ F

/-- The minimal elements of a family. -/
noncomputable def minimalElts (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter (fun S => ∀ T ∈ F, T ⊆ S → T = S)

/-- `ℓ(F)`: the maximum of `2` and the largest size of a minimal element of `F`. -/
noncomputable def ell (F : Finset (Finset α)) : ℕ := max 2 ((minimalElts F).sup Finset.card)

/-- The threshold of `F`: the least `p` at which `F` has probability at least `1/2`. -/
noncomputable def threshold (F : Finset (Finset α)) : ℝ :=
  sInf {p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧ 1 / 2 ≤ mu p F}

/-- The expectation-threshold of `F`: the largest `q` for which `F` is `q`-small. -/
noncomputable def expThreshold (F : Finset (Finset α)) : ℝ :=
  sSup {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ IsSmall q F}

/-! ### Elementary facts -/

lemma mu_add_muFail (p : ℝ) (H : Finset (Finset α)) :
    mu p (upClosure H) + muFail p H = 1 := by
  have hsplit : ∀ U : Finset α,
      (if U ∈ upClosure H then weight p U else 0) + weight p U * failInd H U = weight p U := by
    intro U
    by_cases hU : ∃ S ∈ H, S ⊆ U
    · have : U ∈ upClosure H := by simp only [upClosure, Finset.mem_filter, Finset.mem_univ]
                                   exact ⟨trivial, hU⟩
      rw [if_pos this, failInd, if_pos hU]
      ring
    · have : U ∉ upClosure H := by
        simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hU
      rw [if_neg this, failInd, if_neg hU]
      ring
  have h1 : (∑ U : Finset α, (if U ∈ upClosure H then weight p U else 0))
      + ∑ U : Finset α, weight p U * failInd H U = 1 := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun U _ => hsplit U)]
    exact sum_weight p
  rw [mu, muFail]
  rw [← h1]
  congr 1
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma upClosure_bounded_ne (H : Finset (Finset α)) : True := trivial

/-- Every element of an increasing family contains a minimal element. -/
lemma exists_minimal_subset {F : Finset (Finset α)} {A : Finset α} (hA : A ∈ F) :
    ∃ S ∈ minimalElts F, S ⊆ A := by
  classical
  have hne : (F.filter (fun T => T ⊆ A)).Nonempty :=
    ⟨A, Finset.mem_filter.2 ⟨hA, Finset.Subset.refl A⟩⟩
  obtain ⟨S, hS, hSmin⟩ := Finset.exists_min_image _ Finset.card hne
  obtain ⟨hSF, hSA⟩ := Finset.mem_filter.1 hS
  refine ⟨S, Finset.mem_filter.2 ⟨hSF, ?_⟩, hSA⟩
  intro T hT hTS
  have hTA : T ⊆ A := hTS.trans hSA
  have := hSmin T (Finset.mem_filter.2 ⟨hT, hTA⟩)
  exact Finset.eq_of_subset_of_card_le hTS this

lemma minimalElts_subset (F : Finset (Finset α)) : minimalElts F ⊆ F :=
  Finset.filter_subset _ _

lemma upClosure_minimalElts {F : Finset (Finset α)} (hinc : Increasing F) :
    upClosure (minimalElts F) = F := by
  ext U
  simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨S, hS, hSU⟩
    exact hinc S (minimalElts_subset F hS) U hSU
  · intro hU
    obtain ⟨S, hS, hSU⟩ := exists_minimal_subset hU
    exact ⟨S, hS, hSU⟩

lemma covers_minimalElts_iff {G F : Finset (Finset α)} :
    Covers G (minimalElts F) ↔ Covers G F := by
  constructor
  · intro h S hS
    obtain ⟨S₀, hS₀, hS₀S⟩ := exists_minimal_subset hS
    obtain ⟨T, hT, hTS₀⟩ := h S₀ hS₀
    exact ⟨T, hT, hTS₀.trans hS₀S⟩
  · intro h S hS
    exact h S (minimalElts_subset F hS)

lemma isSmall_minimalElts_iff {q : ℝ} {F : Finset (Finset α)} :
    IsSmall q (minimalElts F) ↔ IsSmall q F := by
  constructor
  · rintro ⟨G, hG, hc⟩; exact ⟨G, covers_minimalElts_iff.1 hG, hc⟩
  · rintro ⟨G, hG, hc⟩; exact ⟨G, covers_minimalElts_iff.2 hG, hc⟩

lemma minimalElts_bounded (F : Finset (Finset α)) :
    ∀ S ∈ minimalElts F, S.card ≤ ell F := fun S hS =>
  le_trans (Finset.le_sup (f := Finset.card) hS) (le_max_right _ _)

/-! ### From the iteration to the threshold -/

/-- If `H` is `ℓ`-bounded and not `q`-small, then a random set of density at least
`64 q * rounds ℓ` contains an edge of `H` with probability more than `1/2`. -/
theorem not_small_prob (H : Finset (Finset α)) (l : ℕ) (hb : ∀ S ∈ H, S.card ≤ l)
    (q : ℝ) (hq : 0 < q) (hq1 : 64 * q ≤ 1) (hns : ¬ IsSmall q H)
    (p : ℝ) (hp : 64 * q * (rounds l : ℝ) ≤ p) (hp1 : p ≤ 1) :
    1 / 2 < mu p (upClosure H) := by
  have hq0 : (0:ℝ) ≤ 64 * q := by positivity
  -- every cover of `H` costs more than `1/2`
  have hLB : ∀ G : Finset (Finset α), Covers G H → (1 / 2 : ℝ) ≤ cost q G := by
    intro G hG
    by_contra hlt
    push_neg at hlt
    exact hns ⟨G, hG, hlt.le⟩
  have hmain := main_bound q hq hq1 l H hb (1 / 2) hLB
  have hPf : Pfail (64 * q) (rounds l) H ≤ 1 / 15 := by
    have h16 : (0:ℝ) ≤ (1 / 16 : ℝ) ^ l := by positivity
    nlinarith
  set k := rounds l with hk
  set p₀ : ℝ := 1 - (1 - 64 * q) ^ k with hp₀
  have hbern : (1 : ℝ) - (k : ℝ) * (64 * q) ≤ (1 - 64 * q) ^ k := by
    have := one_add_mul_le_pow (a := -(64 * q)) (by linarith) k
    simpa using this
  have hp₀le : p₀ ≤ 64 * q * (k : ℝ) := by
    rw [hp₀]; nlinarith
  have hp₀0 : 0 ≤ p₀ := by
    have : (1 - 64 * q) ^ k ≤ 1 := by
      apply pow_le_one₀ (by linarith) (by linarith)
    rw [hp₀]; linarith
  have hp₀1 : p₀ ≤ 1 := by
    have : (0:ℝ) ≤ (1 - 64 * q) ^ k := by
      apply pow_nonneg; linarith
    rw [hp₀]; linarith
  have hmf : muFail p₀ H ≤ 1 / 15 := by
    rw [← Pfail_eq_muFail]
    exact hPf
  have hmono : muFail p H ≤ muFail p₀ H :=
    muFail_anti hp₀0 (le_trans hp₀le (by linarith)) hp1 H
  have := mu_add_muFail p H
  linarith

/-! ### The Kahn–Kalai theorem -/

lemma mu_one_of_univ_mem {F : Finset (Finset α)} (h : (Finset.univ : Finset α) ∈ F) :
    mu 1 F = 1 := by
  rw [mu, Finset.sum_eq_single (Finset.univ : Finset α)]
  · rw [weight_def]; simp
  · intro U _ hU
    rw [weight_def]
    have : Uᶜ ≠ ∅ := by
      intro hc
      exact hU (Finset.compl_eq_empty_iff.mp hc)
    have hcard : Uᶜ.card ≠ 0 := fun hc => this (Finset.card_eq_zero.1 hc)
    simp [zero_pow hcard]
  · intro hc; exact absurd h hc

lemma threshold_le_of_mem {F : Finset (Finset α)} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : 1 / 2 ≤ mu p F) : threshold F ≤ p := by
  refine csInf_le ⟨0, ?_⟩ ⟨hp0, hp1, h⟩
  rintro x ⟨hx, -, -⟩
  exact hx

lemma univ_mem_of_nonempty {F : Finset (Finset α)} (hinc : Increasing F) (hne : F.Nonempty) :
    (Finset.univ : Finset α) ∈ F := by
  obtain ⟨A, hA⟩ := hne
  exact hinc A hA Finset.univ (Finset.subset_univ A)

lemma threshold_le_one {F : Finset (Finset α)} (hinc : Increasing F) (hne : F.Nonempty) :
    threshold F ≤ 1 := by
  refine threshold_le_of_mem zero_le_one le_rfl ?_
  rw [mu_one_of_univ_mem (univ_mem_of_nonempty hinc hne)]
  norm_num

lemma expThreshold_nonneg {F : Finset (Finset α)} (hnu : F ≠ Finset.univ)
    (hinc : Increasing F) : 0 ≤ expThreshold F := by
  have hempty : (∅ : Finset α) ∉ F := by
    intro hmem
    exact hnu (Finset.eq_univ_of_forall fun U =>
      hinc ∅ hmem U (Finset.empty_subset U))
  have h0 : IsSmall (0 : ℝ) F := by
    refine ⟨F, Covers.refl F, ?_⟩
    have : cost (0 : ℝ) F = 0 := by
      rw [cost]
      refine Finset.sum_eq_zero fun S hS => ?_
      have hSne : S.card ≠ 0 := by
        intro hc
        exact hempty (Finset.card_eq_zero.1 hc ▸ hS)
      exact zero_pow hSne
    rw [this]; norm_num
  exact le_csSup ⟨1, fun x hx => hx.2.1⟩ ⟨le_rfl, zero_le_one, h0⟩

lemma not_isSmall_of_gt {F : Finset (Finset α)} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : expThreshold F < q) : ¬ IsSmall q F := by
  intro hs
  have : q ≤ expThreshold F := le_csSup ⟨1, fun x hx => hx.2.1⟩ ⟨hq0, hq1, hs⟩
  linarith

lemma one_le_logb_ell (F : Finset (Finset α)) : 1 ≤ Real.logb 2 (ell F) := by
  have h2 : (2:ℝ) ≤ (ell F : ℝ) := by
    have : 2 ≤ ell F := le_max_left _ _
    exact_mod_cast this
  calc (1:ℝ) = Real.logb 2 2 := by simp
    _ ≤ Real.logb 2 (ell F) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) h2

lemma rounds_le_logb (F : Finset (Finset α)) :
    (rounds (ell F) : ℝ) ≤ 2 * Real.logb 2 (ell F) := by
  have hL := one_le_logb_ell F
  have hnat : rounds (ell F) ≤ Nat.log 2 (ell F) + 1 := rounds_le _
  have h2 : 2 ≤ ell F := le_max_left _ _
  have hlog : (Nat.log 2 (ell F) : ℝ) ≤ Real.logb 2 (ell F) := by
    have h1 : (2:ℕ) ^ (Nat.log 2 (ell F)) ≤ ell F := Nat.pow_log_le_self 2 (by omega)
    have h2' : ((2:ℝ)) ^ (Nat.log 2 (ell F)) ≤ (ell F : ℝ) := by exact_mod_cast h1
    rw [show ((Nat.log 2 (ell F) : ℝ)) = Real.logb 2 ((2:ℝ) ^ (Nat.log 2 (ell F))) by
      rw [Real.logb_pow]; simp]
    exact Real.logb_le_logb_of_le (by norm_num) (by positivity) h2'
  have : (rounds (ell F) : ℝ) ≤ (Nat.log 2 (ell F) : ℝ) + 1 := by exact_mod_cast hnat
  linarith

/-- **The Kahn–Kalai conjecture** (Park–Pham). For every nontrivial increasing family `F` on a
finite set, the threshold is at most `128` times the expectation-threshold times
`log₂ ℓ(F)`. -/
theorem kahn_kalai (F : Finset (Finset α)) (hinc : Increasing F) (hne : F.Nonempty)
    (hnu : F ≠ Finset.univ) :
    threshold F ≤ 128 * expThreshold F * Real.logb 2 (ell F) := by
  set L : ℝ := Real.logb 2 (ell F) with hLdef
  have hL1 : 1 ≤ L := one_le_logb_ell F
  have hq₀0 : 0 ≤ expThreshold F := expThreshold_nonneg hnu hinc
  set q₀ : ℝ := expThreshold F with hq₀def
  have hthr1 : threshold F ≤ 1 := threshold_le_one hinc hne
  by_cases hbig : (1:ℝ) ≤ 128 * q₀ * L
  · linarith
  push_neg at hbig
  have hq₀small : q₀ < 1 / 128 := by nlinarith
  -- for every `q` slightly above `q₀` we get a bound
  have key : ∀ q : ℝ, q₀ < q → q ≤ 1 / 64 → threshold F ≤ 128 * q * L := by
    intro q hq hq64
    have hq0 : 0 < q := lt_of_le_of_lt hq₀0 hq
    have hq1 : 64 * q ≤ 1 := by linarith
    have hns : ¬ IsSmall q (minimalElts F) :=
      fun hs => not_isSmall_of_gt hq0.le (by linarith) hq (isSmall_minimalElts_iff.1 hs)
    set l := ell F with hl
    set p : ℝ := 64 * q * (rounds l : ℝ) with hpdef
    have hp0 : 0 ≤ p := by
      have : (0:ℝ) ≤ (rounds l : ℝ) := Nat.cast_nonneg _
      positivity
    have hple : p ≤ 128 * q * L := by
      have hr := rounds_le_logb F
      rw [hpdef, ← hl] at *
      nlinarith
    by_cases hp1 : p ≤ 1
    · have := not_small_prob (minimalElts F) l (minimalElts_bounded F) q hq0 hq1 hns p le_rfl hp1
      rw [upClosure_minimalElts hinc] at this
      exact le_trans (threshold_le_of_mem hp0 hp1 this.le) hple
    · push_neg at hp1
      linarith
  -- take the limit `q ↓ q₀`
  refine le_of_forall_pos_le_add ?_
  intro eps heps
  have hδ : 0 < min (1 / 128 - q₀) (eps / (128 * L)) := by
    have h1 : 0 < 1 / 128 - q₀ := by linarith
    have h2 : 0 < eps / (128 * L) := by positivity
    exact lt_min h1 h2
  set δ : ℝ := min (1 / 128 - q₀) (eps / (128 * L)) with hδdef
  have hq : q₀ < q₀ + δ := by linarith
  have hq64 : q₀ + δ ≤ 1 / 64 := by
    have : δ ≤ 1 / 128 - q₀ := min_le_left _ _
    linarith
  have hbound := key (q₀ + δ) hq hq64
  have hδ2 : δ ≤ eps / (128 * L) := min_le_right _ _
  have : 128 * (q₀ + δ) * L ≤ 128 * q₀ * L + eps := by
    have hLpos : (0:ℝ) < L := by linarith
    have hkey : δ * (128 * L) ≤ eps := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 128 * L)] at hδ2
      exact hδ2
    nlinarith
  linarith

end Math2

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

import Mathlib
import RequestProject.KahnKalai.KeyLemma

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The iteration of Park–Pham: the failure probability of the multi-round process.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Indicator of the event that `U` contains no edge of `H`. -/
noncomputable def failInd (H : Finset (Finset α)) (U : Finset α) : ℝ :=
  if ∃ S ∈ H, S ⊆ U then 0 else 1

omit [Fintype α] in
lemma failInd_nonneg (H : Finset (Finset α)) (U : Finset α) : 0 ≤ failInd H U := by
  unfold failInd; split <;> norm_num

omit [Fintype α] in
lemma failInd_le_one (H : Finset (Finset α)) (U : Finset α) : failInd H U ≤ 1 := by
  unfold failInd; split <;> norm_num

omit [Fintype α] in
lemma failInd_anti {H : Finset (Finset α)} {U V : Finset α} (h : U ⊆ V) :
    failInd H V ≤ failInd H U := by
  unfold failInd
  split_ifs with hV hU hU'
  · exact le_rfl
  · norm_num
  · obtain ⟨S, hS, hSU⟩ := hU'
    exact absurd ⟨S, hS, hSU.trans h⟩ hV
  · exact le_rfl

/-- The probability that the random set `U` (each element present independently with
probability `p`) contains no edge of `H`. -/
noncomputable def muFail (p : ℝ) (H : Finset (Finset α)) : ℝ :=
  ∑ U : Finset α, weight p U * failInd H U

/-- Failure probability of the `k`-round process. -/
noncomputable def Pfail (p : ℝ) : ℕ → Finset (Finset α) → ℝ
  | 0, H => failInd H ∅
  | (k + 1), H => ∑ W : Finset α, weight p W * Pfail p k (H.image (fun S => S \ W))

lemma Pfail_zero (p : ℝ) (H : Finset (Finset α)) : Pfail p 0 H = failInd H ∅ := rfl

lemma Pfail_succ (p : ℝ) (k : ℕ) (H : Finset (Finset α)) :
    Pfail p (k + 1) H = ∑ W : Finset α, weight p W * Pfail p k (H.image (fun S => S \ W)) := rfl

lemma Pfail_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) (H : Finset (Finset α)) :
    0 ≤ Pfail p k H := by
  induction k generalizing H with
  | zero => rw [Pfail_zero]; exact failInd_nonneg _ _
  | succ k ih =>
      rw [Pfail_succ]
      exact Finset.sum_nonneg fun W _ => mul_nonneg (weight_nonneg hp0 hp1 W) (ih _)

lemma Pfail_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) (H : Finset (Finset α)) :
    Pfail p k H ≤ 1 := by
  induction k generalizing H with
  | zero => rw [Pfail_zero]; exact failInd_le_one _ _
  | succ k ih =>
      rw [Pfail_succ]
      calc ∑ W : Finset α, weight p W * Pfail p k (H.image (fun S => S \ W))
          ≤ ∑ W : Finset α, weight p W * 1 := by
            refine Finset.sum_le_sum fun W _ => ?_
            exact mul_le_mul_of_nonneg_left (ih _) (weight_nonneg hp0 hp1 W)
        _ = 1 := by simpa using sum_weight (α := α) p

omit [Fintype α] in
lemma Covers.image_sdiff {A B : Finset (Finset α)} (h : Covers A B) (W : Finset α) :
    Covers (A.image (fun S => S \ W)) (B.image (fun S => S \ W)) := by
  intro S hS
  obtain ⟨S₀, hS₀, rfl⟩ := Finset.mem_image.1 hS
  obtain ⟨T, hT, hTS⟩ := h S₀ hS₀
  refine ⟨T \ W, Finset.mem_image.2 ⟨T, hT, rfl⟩, fun y hy => ?_⟩
  obtain ⟨hy1, hy2⟩ := Finset.mem_sdiff.1 hy
  exact Finset.mem_sdiff.2 ⟨hTS hy1, hy2⟩

lemma Pfail_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {A B : Finset (Finset α)}
    (hAB : Covers A B) (k : ℕ) : Pfail p k A ≤ Pfail p k B := by
  induction k generalizing A B with
  | zero =>
      rw [Pfail_zero, Pfail_zero]
      unfold failInd
      split_ifs with hA hB hB'
      · exact le_rfl
      · norm_num
      · obtain ⟨S, hS, hSe⟩ := hB'
        obtain ⟨T, hT, hTS⟩ := hAB S hS
        exact absurd ⟨T, hT, hTS.trans hSe⟩ hA
      · exact le_rfl
  | succ k ih =>
      rw [Pfail_succ, Pfail_succ]
      exact Finset.sum_le_sum fun W _ =>
        mul_le_mul_of_nonneg_left (ih (hAB.image_sdiff W)) (weight_nonneg hp0 hp1 W)

omit [Fintype α] in
lemma failInd_image_sdiff (H : Finset (Finset α)) (W V : Finset α) :
    failInd (H.image (fun S => S \ W)) V = failInd H (W ∪ V) := by
  unfold failInd
  congr 1
  apply propext
  constructor
  · rintro ⟨S, hS, hSV⟩
    obtain ⟨S₀, hS₀, rfl⟩ := Finset.mem_image.1 hS
    refine ⟨S₀, hS₀, fun y hy => ?_⟩
    by_cases hyW : y ∈ W
    · exact Finset.mem_union_left _ hyW
    · exact Finset.mem_union_right _ (hSV (Finset.mem_sdiff.2 ⟨hy, hyW⟩))
  · rintro ⟨S, hS, hSV⟩
    refine ⟨S \ W, Finset.mem_image.2 ⟨S, hS, rfl⟩, fun y hy => ?_⟩
    obtain ⟨hy1, hy2⟩ := Finset.mem_sdiff.1 hy
    rcases Finset.mem_union.1 (hSV hy1) with h | h
    · exact absurd h hy2
    · exact h

lemma weight_zero (U : Finset α) : weight (0 : ℝ) U = if U = ∅ then 1 else 0 := by
  rw [weight_def]
  by_cases hU : U = ∅
  · subst hU; simp
  · have : U.card ≠ 0 := fun h => hU (Finset.card_eq_zero.1 h)
    rw [if_neg hU, zero_pow this, zero_mul]

/-- The `k`-round process is the same as a single round with the union parameter. -/
lemma Pfail_eq_muFail (p : ℝ) (k : ℕ) (H : Finset (Finset α)) :
    Pfail p k H = muFail (1 - (1 - p) ^ k) H := by
  induction k generalizing H with
  | zero =>
      rw [Pfail_zero, muFail]
      simp only [pow_zero, sub_self]
      rw [Finset.sum_eq_single (∅ : Finset α)]
      · rw [weight_zero, if_pos rfl, one_mul]
      · intro U _ hU
        rw [weight_zero, if_neg hU, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
  | succ k ih =>
      rw [Pfail_succ]
      have h1 : ∀ W : Finset α, Pfail p k (H.image (fun S => S \ W))
          = ∑ V : Finset α, weight (1 - (1 - p) ^ k) V * failInd H (W ∪ V) := by
        intro W
        rw [ih, muFail]
        exact Finset.sum_congr rfl fun V _ => by rw [failInd_image_sdiff]
      calc ∑ W : Finset α, weight p W * Pfail p k (H.image (fun S => S \ W))
          = ∑ W : Finset α, ∑ V : Finset α,
              weight p W * weight (1 - (1 - p) ^ k) V * failInd H (W ∪ V) := by
            refine Finset.sum_congr rfl fun W _ => ?_
            rw [h1 W, Finset.mul_sum]
            exact Finset.sum_congr rfl fun V _ => by ring
        _ = ∑ U : Finset α,
              weight (1 - (1 - p) * (1 - (1 - (1 - p) ^ k))) U * failInd H U :=
            sum_union_weight _ _ _
        _ = muFail (1 - (1 - p) ^ (k + 1)) H := by
            have hpow : 1 - (1 - p) * (1 - (1 - (1 - p) ^ k)) = 1 - (1 - p) ^ (k + 1) := by
              ring
            rw [muFail, hpow]

/-- Monotonicity of the failure probability in `p`. -/
lemma muFail_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (H : Finset (Finset α)) :
    muFail b H ≤ muFail a H := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  have ha1 : a < 1 := lt_of_lt_of_le hlt hb
  set r : ℝ := (b - a) / (1 - a) with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by linarith)]
    linarith
  have hne : (1 : ℝ) - a ≠ 0 := by linarith
  have hkey : 1 - (1 - a) * (1 - r) = b := by
    rw [hr]
    field_simp
    ring
  have h1 : muFail b H = ∑ W : Finset α, ∑ V : Finset α,
      weight a W * weight r V * failInd H (W ∪ V) := by
    rw [sum_union_weight, hkey, muFail]
  rw [h1, muFail]
  calc ∑ W : Finset α, ∑ V : Finset α, weight a W * weight r V * failInd H (W ∪ V)
      ≤ ∑ W : Finset α, ∑ V : Finset α, weight a W * weight r V * failInd H W := by
        refine Finset.sum_le_sum fun W _ => Finset.sum_le_sum fun V _ => ?_
        refine mul_le_mul_of_nonneg_left (failInd_anti Finset.subset_union_left) ?_
        exact mul_nonneg (weight_nonneg ha (by linarith) W) (weight_nonneg hr0 hr1 V)
    _ = ∑ W : Finset α, weight a W * failInd H W := by
        refine Finset.sum_congr rfl fun W _ => ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_weight, mul_one]

/-- The number of halving rounds needed for an `ℓ`-bounded hypergraph. -/
def rounds : ℕ → ℕ
  | 0 => 0
  | (n + 1) => rounds ((n + 1) / 2) + 1
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

lemma rounds_zero : rounds 0 = 0 := by simp [rounds]

lemma rounds_of_pos {ℓ : ℕ} (h : 0 < ℓ) : rounds ℓ = rounds (ℓ / 2) + 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  rw [rounds]

lemma rounds_le (ℓ : ℕ) : rounds ℓ ≤ Nat.log 2 ℓ + 1 := by
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · simp [rounds_zero]
    · rw [rounds_of_pos hpos]
      rcases Nat.lt_or_ge ℓ 2 with h2 | h2
      · interval_cases ℓ
        · simp [rounds_zero]
      · have hdiv : ℓ / 2 < ℓ := Nat.div_lt_self hpos (by norm_num)
        have := ih (ℓ / 2) hdiv
        have hlog : Nat.log 2 (ℓ / 2) + 1 = Nat.log 2 ℓ := by
          rw [Nat.log_div_base]
          have : 1 ≤ Nat.log 2 ℓ := Nat.log_pos (by norm_num) h2
          omega
        omega

/-- **Main induction** (Park–Pham iteration). For an `ℓ`-bounded hypergraph `H`, if `c` is a
lower bound for the cost of every cover of `H`, then `c` times the probability that the
`rounds ℓ`-round process fails to cover `H` is at most `1/30`. -/
theorem main_bound (p : ℝ) (hp : 0 < p) (hq1 : 64 * p ≤ 1) (ℓ : ℕ) :
    ∀ H : Finset (Finset α), (∀ S ∈ H, S.card ≤ ℓ) →
      ∀ c : ℝ, (∀ G : Finset (Finset α), Covers G H → c ≤ cost p G) →
        c * Pfail (64 * p) (rounds ℓ) H ≤ (1 / 30) * (1 - (1 / 16 : ℝ) ^ ℓ) := by
  have hq0 : (0:ℝ) ≤ 64 * p := by positivity
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro H hb c hc
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · rw [rounds_zero, Pfail_zero]
      simp only [pow_zero, sub_self, mul_zero]
      unfold failInd
      split_ifs with hE
      · simp
      · have hHempty : H = ∅ := by
          by_contra hne
          obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.2 hne
          have hcard : S.card ≤ 0 := hb S hS
          have hSe : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
          exact hE ⟨S, hS, by rw [hSe]⟩
        have hcov : Covers (∅ : Finset (Finset α)) H := by
          intro S hS; rw [hHempty] at hS; exact absurd hS (Finset.notMem_empty S)
        have hc0 : c ≤ 0 := by simpa [cost] using hc ∅ hcov
        simpa using hc0
    · set h := ℓ / 2 with hh
      have hhlt : h < ℓ := Nat.div_lt_self hpos (by norm_num)
      have hle : ℓ ≤ 2 * h + 1 := by omega
      have hRHSnn : (0:ℝ) ≤ (1 / 30) * (1 - (1 / 16 : ℝ) ^ ℓ) := by
        have : (1/16:ℝ) ^ ℓ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith
      rcases lt_or_ge c 0 with hcneg | hcpos
      · have h1 := Pfail_nonneg hq0 hq1 (rounds ℓ) H
        nlinarith
      rw [rounds_of_pos hpos, Pfail_succ]
      have hstep : ∀ W : Finset α,
          c * Pfail (64 * p) (rounds h) (H.image (fun S => S \ W))
            ≤ (1 / 30) * (1 - (1 / 16 : ℝ) ^ h) + cost p (Ufam H h W) := by
        intro W
        have hmono : Pfail (64 * p) (rounds h) (H.image (fun S => S \ W))
            ≤ Pfail (64 * p) (rounds h) (Hfam H h W) :=
          Pfail_mono hq0 hq1 residual_covers_Hfam _
        have hLB : ∀ G : Finset (Finset α), Covers G (Hfam H h W) →
            c - cost p (Ufam H h W) ≤ cost p G := by
          intro G hG
          have h1 := hc (Ufam H h W ∪ G) (covers_union hG)
          have h2 := cost_union_le hp.le (Ufam H h W) G
          linarith
        have hIH := ih h hhlt (Hfam H h W) Hfam_bounded (c - cost p (Ufam H h W)) hLB
        have hP1 := Pfail_le_one hq0 hq1 (rounds h) (Hfam H h W)
        have hP0 := Pfail_nonneg hq0 hq1 (rounds h) (Hfam H h W)
        have hcu := cost_nonneg hp.le (Ufam H h W)
        have hA : c * Pfail (64 * p) (rounds h) (H.image (fun S => S \ W))
            ≤ c * Pfail (64 * p) (rounds h) (Hfam H h W) :=
          mul_le_mul_of_nonneg_left hmono hcpos
        have hB : cost p (Ufam H h W) * Pfail (64 * p) (rounds h) (Hfam H h W)
            ≤ cost p (Ufam H h W) := by
          calc cost p (Ufam H h W) * Pfail (64 * p) (rounds h) (Hfam H h W)
              ≤ cost p (Ufam H h W) * 1 := mul_le_mul_of_nonneg_left hP1 hcu
            _ = cost p (Ufam H h W) := mul_one _
        have e1 : (c - cost p (Ufam H h W)) * Pfail (64 * p) (rounds h) (Hfam H h W)
            = c * Pfail (64 * p) (rounds h) (Hfam H h W)
              - cost p (Ufam H h W) * Pfail (64 * p) (rounds h) (Hfam H h W) := by ring
        rw [e1] at hIH
        linarith
      have hsplit : ∀ W : Finset α,
          weight (64 * p) W * ((1 / 30) * (1 - (1 / 16 : ℝ) ^ h) + cost p (Ufam H h W))
            = weight (64 * p) W * ((1 / 30) * (1 - (1 / 16 : ℝ) ^ h))
              + weight (64 * p) W * cost p (Ufam H h W) := fun W => by ring
      have hnum : (1 / 30) * (1 - (1 / 16 : ℝ) ^ h) + (1 / 32) * (1 / 16 : ℝ) ^ h
          ≤ (1 / 30) * (1 - (1 / 16 : ℝ) ^ ℓ) := by
        have hy : (1 / 16 : ℝ) ^ ℓ ≤ (1 / 16 : ℝ) ^ (h + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        rw [pow_succ] at hy
        linarith
      calc c * ∑ W : Finset α,
            weight (64 * p) W * Pfail (64 * p) (rounds h) (H.image (fun S => S \ W))
          = ∑ W : Finset α, weight (64 * p) W
              * (c * Pfail (64 * p) (rounds h) (H.image (fun S => S \ W))) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun W _ => by ring
        _ ≤ ∑ W : Finset α, weight (64 * p) W
              * ((1 / 30) * (1 - (1 / 16 : ℝ) ^ h) + cost p (Ufam H h W)) :=
            Finset.sum_le_sum fun W _ =>
              mul_le_mul_of_nonneg_left (hstep W) (weight_nonneg hq0 hq1 W)
        _ = (1 / 30) * (1 - (1 / 16 : ℝ) ^ h)
              + ∑ W : Finset α, weight (64 * p) W * cost p (Ufam H h W) := by
            rw [Finset.sum_congr rfl (fun W _ => hsplit W), Finset.sum_add_distrib,
              ← Finset.sum_mul, sum_weight, one_mul]
        _ ≤ (1 / 30) * (1 - (1 / 16 : ℝ) ^ h) + (1 / 32) * (1 / 16 : ℝ) ^ h := by
            have := expected_cost_bound H ℓ h hb hle p hp hq1
            linarith
        _ ≤ (1 / 30) * (1 - (1 / 16 : ℝ) ^ ℓ) := hnum

end Math2

import Mathlib

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- The weight `p ^ |W| * (1-p) ^ |s \ W|` of a subset `W` of `s`, i.e. the probability that
the random subset of `s` including each element independently with probability `p` equals `W`. -/
noncomputable def pw (p : ℝ) (s W : Finset α) : ℝ := p ^ W.card * (1 - p) ^ (s \ W).card

lemma pw_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s W : Finset α) : 0 ≤ pw p s W :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

/-- The weights of subsets of `s` sum to `1`. -/
lemma sum_pw (p : ℝ) (s : Finset α) : ∑ W ∈ s.powerset, pw p s W = 1 := by
  have h := Finset.prod_add (fun _ : α => p) (fun _ : α => 1 - p) s
  simp only [Finset.prod_const] at h
  simp only [pw]
  rw [← h]
  simp

section Fintype
variable [Fintype α]

/-- The product-measure weight of `W ⊆ α`. -/
noncomputable def weight (p : ℝ) (W : Finset α) : ℝ := pw p univ W

lemma weight_def (p : ℝ) (W : Finset α) :
    weight p W = p ^ W.card * (1 - p) ^ Wᶜ.card := by
  rw [weight, pw, Finset.compl_eq_univ_sdiff]

lemma weight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset α) : 0 ≤ weight p W :=
  pw_nonneg hp0 hp1 _ _

lemma sum_weight (p : ℝ) : ∑ W : Finset α, weight p W = 1 := by
  have h := sum_pw p (univ : Finset α)
  rwa [Finset.powerset_univ] at h

end Fintype

/-- Auxiliary rewriting: for `W ⊆ s` and `x ∉ s`. -/
lemma pw_insert_ground {p : ℝ} {s W : Finset α} {x : α} (hx : x ∉ s) (hW : W ⊆ s) :
    pw p (insert x s) W = pw p s W * (1 - p) := by
  have hxW : x ∉ W := fun h => hx (hW h)
  have h : (insert x s) \ W = insert x (s \ W) := by
    ext y; simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, hxW⟩
      · exact ⟨Or.inr h1, h2⟩
  rw [pw, pw, h, Finset.card_insert_of_notMem (by simp [hx])]
  ring

lemma pw_insert_both {p : ℝ} {s W : Finset α} {x : α} (hx : x ∉ s) (hW : W ⊆ s) :
    pw p (insert x s) (insert x W) = pw p s W * p := by
  have hxW : x ∉ W := fun h => hx (hW h)
  have h1 : (insert x s) \ (insert x W) = s \ W := by
    ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
    constructor
    · rintro ⟨h1 | h1, h2, h3⟩
      · exact absurd h1 h2
      · exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      refine ⟨Or.inr h1, ?_, h2⟩
      rintro rfl; exact hx h1
  rw [pw, pw, h1, Finset.card_insert_of_notMem hxW]
  ring

/-- The union of two independent random subsets is again a random subset. -/
lemma sum_union_pw (a b : ℝ) (s : Finset α) (f : Finset α → ℝ) :
    ∑ W ∈ s.powerset, ∑ V ∈ s.powerset, pw a s W * pw b s V * f (W ∪ V)
      = ∑ U ∈ s.powerset, pw (1 - (1 - a) * (1 - b)) s U * f U := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp [pw]
  | insert x s hx ih =>
      set c : ℝ := 1 - (1 - a) * (1 - b) with hc
      have expand : ∀ g : Finset α → Finset α → ℝ,
          ∑ W ∈ (insert x s).powerset, ∑ V ∈ (insert x s).powerset, g W V
            = ∑ W ∈ s.powerset, ((∑ V ∈ s.powerset, g W V + ∑ V ∈ s.powerset, g W (insert x V))
                + (∑ V ∈ s.powerset, g (insert x W) V
                    + ∑ V ∈ s.powerset, g (insert x W) (insert x V))) := by
        intro g
        rw [Finset.sum_powerset_insert hx]
        simp_rw [Finset.sum_powerset_insert hx]
        rw [← Finset.sum_add_distrib]
      rw [expand, Finset.sum_powerset_insert hx]
      have hsub : ∀ W ∈ s.powerset, W ⊆ s := fun W hW => Finset.mem_powerset.1 hW
      have key : ∀ W ∈ s.powerset,
          (∑ V ∈ s.powerset, pw a (insert x s) W * pw b (insert x s) V * f (W ∪ V)
            + ∑ V ∈ s.powerset, pw a (insert x s) W * pw b (insert x s) (insert x V)
                * f (W ∪ insert x V))
          + (∑ V ∈ s.powerset, pw a (insert x s) (insert x W) * pw b (insert x s) V
                * f (insert x W ∪ V)
            + ∑ V ∈ s.powerset, pw a (insert x s) (insert x W) * pw b (insert x s) (insert x V)
                * f (insert x W ∪ insert x V))
          = (1 - c) * (∑ V ∈ s.powerset, pw a s W * pw b s V * f (W ∪ V))
            + c * (∑ V ∈ s.powerset, pw a s W * pw b s V * f (insert x (W ∪ V))) := by
        intro W hW
        have hWs := hsub W hW
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun V hV => ?_)
        have hVs := hsub V hV
        rw [pw_insert_ground hx hWs, pw_insert_ground hx hVs, pw_insert_both hx hWs,
          pw_insert_both hx hVs]
        have e1 : W ∪ insert x V = insert x (W ∪ V) := by
          ext y; simp only [Finset.mem_insert, Finset.mem_union]; tauto
        have e2 : insert x W ∪ V = insert x (W ∪ V) := by
          ext y; simp only [Finset.mem_insert, Finset.mem_union]; tauto
        have e3 : insert x W ∪ insert x V = insert x (W ∪ V) := by
          ext y; simp only [Finset.mem_insert, Finset.mem_union]; tauto
        rw [e1, e2, e3, hc]
        ring
      rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ih f, ih (fun U => f (insert x U))]
      have hcs : ∀ U ∈ s.powerset, pw c (insert x s) U = pw c s U * (1 - c) :=
        fun U hU => pw_insert_ground hx (hsub U hU)
      have hcs' : ∀ U ∈ s.powerset, pw c (insert x s) (insert x U) = pw c s U * c :=
        fun U hU => pw_insert_both hx (hsub U hU)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine congrArg₂ (· + ·) ?_ ?_ <;> refine Finset.sum_congr rfl (fun U hU => ?_)
      · rw [hcs U hU]; ring
      · rw [hcs' U hU]; ring

section Fintype2
variable [Fintype α]

lemma sum_union_weight (a b : ℝ) (f : Finset α → ℝ) :
    ∑ W : Finset α, ∑ V : Finset α, weight a W * weight b V * f (W ∪ V)
      = ∑ U : Finset α, weight (1 - (1 - a) * (1 - b)) U * f U := by
  have h := sum_union_pw a b (univ : Finset α) f
  rwa [Finset.powerset_univ] at h

end Fintype2

end Math2

import Mathlib
import RequestProject.KahnKalai.Fragment

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The key lemma of Park–Pham: the cover made of the large minimum fragments has small
expected cost.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Reweighting identity: adding a set `T` disjoint from `W` trades a factor `q ^ |T|`
for a factor `(1-q) ^ |T|`. -/
lemma weight_union_disjoint (q : ℝ) {W T : Finset α} (hd : Disjoint T W) :
    weight q W * q ^ T.card = weight q (W ∪ T) * (1 - q) ^ T.card := by
  have hTc : T ⊆ Wᶜ := by
    intro y hy
    simp only [Finset.mem_compl]
    exact fun hyW => (Finset.disjoint_left.1 hd) hy hyW
  have hcard : (W ∪ T).card = W.card + T.card := by
    rw [Finset.card_union_of_disjoint hd.symm]
  have hcompl : (W ∪ T)ᶜ = Wᶜ \ T := by
    ext y; simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff, not_or]
  have hc2 : (W ∪ T)ᶜ.card + T.card = Wᶜ.card := by
    rw [hcompl]
    exact Finset.card_sdiff_add_card_eq_card hTc
  rw [weight_def, weight_def, hcard, ← hc2, pow_add, pow_add]
  ring

/-- **Key Lemma** (Park–Pham, Lemma 2.1). If `H` is `ℓ`-bounded with `ℓ ≤ 2h+1`, then the
expected cost of the cover `Ufam H h W` formed by the large minimum fragments is at most
`(1/32) * (1/16) ^ h`, where `W` is a random subset with each element present independently
with probability `64 p`. -/
theorem expected_cost_bound (H : Finset (Finset α)) (ℓ h : ℕ)
    (hb : ∀ S ∈ H, S.card ≤ ℓ) (hle : ℓ ≤ 2 * h + 1)
    (p : ℝ) (hp : 0 < p) (hq1 : 64 * p ≤ 1) :
    ∑ W : Finset α, weight (64 * p) W * cost p (Ufam H h W) ≤ (1 / 32) * (1 / 16) ^ h := by
  classical
  set q : ℝ := 64 * p with hqdef
  have hq0 : 0 < q := by positivity
  have hwnn : ∀ W : Finset α, 0 ≤ weight q W := weight_nonneg hq0.le hq1
  set P : Finset (Finset α × Finset α) :=
    Finset.univ.filter (fun x => x.2 ∈ Ufam H h x.1) with hPdef
  set Q : Finset (Finset α × Finset α) :=
    Finset.univ.filter (fun y => (∃ S ∈ H, S ⊆ y.1) ∧ y.2 ⊆ edgeIn H y.1) with hQdef
  -- Step 0: rewrite the sum as a sum over pairs.
  have step1 : ∑ W : Finset α, weight q W * cost p (Ufam H h W)
      = ∑ x ∈ P, weight q x.1 * p ^ x.2.card := by
    rw [hPdef, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun W _ => ?_
    show weight q W * cost p (Ufam H h W)
        = ∑ T : Finset α, if T ∈ Ufam H h W then weight q W * p ^ T.card else 0
    rw [Finset.sum_ite_mem, Finset.univ_inter, cost, Finset.mul_sum]
  -- Step 1: the pointwise weight bound.
  have pointwise : ∀ x ∈ P,
      weight q x.1 * p ^ x.2.card ≤ (1 / 64 : ℝ) ^ (h + 1) * weight q (x.1 ∪ x.2) := by
    rintro ⟨W, T⟩ hx
    simp only [hPdef, Finset.mem_filter] at hx
    have hT : T ∈ Ufam H h W := hx.2
    have hd : Disjoint T W := Ufam_disjoint hT
    have hm : h + 1 ≤ T.card := Ufam_card_gt T hT
    have hid : weight q W * q ^ T.card = weight q (W ∪ T) * (1 - q) ^ T.card :=
      weight_union_disjoint q hd
    have hqpow : (0:ℝ) < q ^ T.card := pow_pos hq0 _
    rw [← mul_le_mul_iff_of_pos_right hqpow]
    have hlhs : weight q W * p ^ T.card * q ^ T.card
        = weight q (W ∪ T) * (1 - q) ^ T.card * p ^ T.card := by
      rw [show weight q W * p ^ T.card * q ^ T.card
            = (weight q W * q ^ T.card) * p ^ T.card by ring, hid]
    rw [hlhs]
    have hqp : q ^ T.card = 64 ^ T.card * p ^ T.card := by
      rw [hqdef, mul_pow]
    rw [hqp]
    have h1 : (1 - q) ^ T.card ≤ 1 := by
      apply pow_le_one₀ (by linarith) (by linarith)
    have h2 : (1:ℝ) ≤ (1 / 64 : ℝ) ^ (h + 1) * 64 ^ T.card := by
      have hstep : (1 / 64 : ℝ) ^ T.card ≤ (1 / 64 : ℝ) ^ (h + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      have : (1 / 64 : ℝ) ^ T.card * 64 ^ T.card = 1 := by
        rw [← mul_pow]; norm_num
      nlinarith [pow_pos (show (0:ℝ) < 64 by norm_num) T.card]
    have hppos : (0:ℝ) < p ^ T.card := pow_pos hp _
    have hwn := hwnn (W ∪ T)
    calc weight q (W ∪ T) * (1 - q) ^ T.card * p ^ T.card
        ≤ weight q (W ∪ T) * 1 * p ^ T.card := by
          apply mul_le_mul_of_nonneg_right _ hppos.le
          exact mul_le_mul_of_nonneg_left h1 hwn
      _ ≤ (1 / 64 : ℝ) ^ (h + 1) * weight q (W ∪ T) * (64 ^ T.card * p ^ T.card) := by
          have : weight q (W ∪ T) * 1 * p ^ T.card
              = weight q (W ∪ T) * p ^ T.card := by ring
          rw [this]
          have hgoal : weight q (W ∪ T) * p ^ T.card
              ≤ weight q (W ∪ T) * ((1 / 64 : ℝ) ^ (h + 1) * 64 ^ T.card) * p ^ T.card := by
            apply mul_le_mul_of_nonneg_right _ hppos.le
            nlinarith
          calc weight q (W ∪ T) * p ^ T.card
              ≤ weight q (W ∪ T) * ((1 / 64 : ℝ) ^ (h + 1) * 64 ^ T.card) * p ^ T.card := hgoal
            _ = (1 / 64 : ℝ) ^ (h + 1) * weight q (W ∪ T) * (64 ^ T.card * p ^ T.card) := by ring
  -- Step 2: the injection `(W,T) ↦ (W ∪ T, T)`.
  have hmaps : ∀ x ∈ P, ((x.1 ∪ x.2, x.2) : Finset α × Finset α) ∈ Q := by
    rintro ⟨W, T⟩ hx
    simp only [hPdef, Finset.mem_filter] at hx
    have hT : T ∈ Ufam H h W := hx.2
    simp only [hQdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Ufam_exists_edge hT, Ufam_subset_edgeIn hT⟩
  have hinj : ∀ x ∈ P, ∀ y ∈ P,
      ((x.1 ∪ x.2, x.2) : Finset α × Finset α) = (y.1 ∪ y.2, y.2) → x = y := by
    rintro ⟨W, T⟩ hx ⟨W', T'⟩ hy heq
    simp only [hPdef, Finset.mem_filter] at hx hy
    have hd : Disjoint T W := Ufam_disjoint hx.2
    have hd' : Disjoint T' W' := Ufam_disjoint hy.2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    subst h2
    have hW : W = (W ∪ T) \ T := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hyW; exact ⟨Or.inl hyW, fun hyT => (Finset.disjoint_left.1 hd) hyT hyW⟩
      · rintro ⟨hy1 | hy1, hy2⟩
        · exact hy1
        · exact absurd hy1 hy2
    have hW' : W' = (W' ∪ T) \ T := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hyW; exact ⟨Or.inl hyW, fun hyT => (Finset.disjoint_left.1 hd') hyT hyW⟩
      · rintro ⟨hy1 | hy1, hy2⟩
        · exact hy1
        · exact absurd hy1 hy2
    have : W = W' := by rw [hW, hW', h1]
    simp [this]
  have step2 : ∑ x ∈ P, weight q (x.1 ∪ x.2) ≤ ∑ y ∈ Q, weight q y.1 := by
    have himg : ∑ x ∈ P, weight q (x.1 ∪ x.2)
        = ∑ y ∈ P.image (fun x : Finset α × Finset α => (x.1 ∪ x.2, x.2)), weight q y.1 := by
      rw [Finset.sum_image hinj]
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun y _ _ => hwnn y.1)
    intro y hy
    obtain ⟨x, hxP, hxy⟩ := Finset.mem_image.1 hy
    exact hxy ▸ hmaps x hxP
  -- Step 3: bounding the sum over `Q`.
  have step3 : ∑ y ∈ Q, weight q y.1 ≤ 2 ^ ℓ := by
    have hQ : ∑ y ∈ Q, weight q y.1
        = ∑ Z : Finset α, ((Finset.univ.filter
            (fun T : Finset α => (∃ S ∈ H, S ⊆ Z) ∧ T ⊆ edgeIn H Z)).card : ℝ) * weight q Z := by
      rw [hQdef, Finset.sum_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun Z _ => ?_
      show (∑ T : Finset α, if (∃ S ∈ H, S ⊆ Z) ∧ T ⊆ edgeIn H Z then weight q Z else 0) = _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hQ]
    have hbound : ∀ Z : Finset α,
        ((Finset.univ.filter
          (fun T : Finset α => (∃ S ∈ H, S ⊆ Z) ∧ T ⊆ edgeIn H Z)).card : ℝ) ≤ 2 ^ ℓ := by
      intro Z
      by_cases hex : ∃ S ∈ H, S ⊆ Z
      · have hset : (Finset.univ.filter
            (fun T : Finset α => (∃ S ∈ H, S ⊆ Z) ∧ T ⊆ edgeIn H Z))
              = (edgeIn H Z).powerset := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
          exact ⟨fun hT => hT.2, fun hT => ⟨hex, hT⟩⟩
        rw [hset, Finset.card_powerset]
        have : (edgeIn H Z).card ≤ ℓ := hb _ (edgeIn_mem H hex)
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) this
      · have hset : (Finset.univ.filter
            (fun T : Finset α => (∃ S ∈ H, S ⊆ Z) ∧ T ⊆ edgeIn H Z)) = ∅ := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_and]
          exact fun hT => absurd hT hex
        rw [hset]
        simp
    calc ∑ Z : Finset α, ((Finset.univ.filter
            (fun T : Finset α => (∃ S ∈ H, S ⊆ Z) ∧ T ⊆ edgeIn H Z)).card : ℝ) * weight q Z
        ≤ ∑ Z : Finset α, (2 ^ ℓ : ℝ) * weight q Z := by
          refine Finset.sum_le_sum fun Z _ => ?_
          exact mul_le_mul_of_nonneg_right (hbound Z) (hwnn Z)
      _ = 2 ^ ℓ := by rw [← Finset.mul_sum, sum_weight]; ring
  -- Combine.
  rw [step1]
  have final : ∑ x ∈ P, weight q x.1 * p ^ x.2.card
      ≤ (1 / 64 : ℝ) ^ (h + 1) * ∑ y ∈ Q, weight q y.1 := by
    calc ∑ x ∈ P, weight q x.1 * p ^ x.2.card
        ≤ ∑ x ∈ P, (1 / 64 : ℝ) ^ (h + 1) * weight q (x.1 ∪ x.2) :=
          Finset.sum_le_sum pointwise
      _ = (1 / 64 : ℝ) ^ (h + 1) * ∑ x ∈ P, weight q (x.1 ∪ x.2) := by rw [Finset.mul_sum]
      _ ≤ (1 / 64 : ℝ) ^ (h + 1) * ∑ y ∈ Q, weight q y.1 := by
          apply mul_le_mul_of_nonneg_left step2 (by positivity)
  have hnum : (1 / 64 : ℝ) ^ (h + 1) * 2 ^ ℓ ≤ (1 / 32) * (1 / 16) ^ h := by
    have h2l : (2:ℝ) ^ ℓ ≤ 2 ^ (2 * h + 1) := by
      apply pow_le_pow_right₀ (by norm_num) hle
    have hcalc : (1 / 64 : ℝ) ^ (h + 1) * 2 ^ (2 * h + 1) = (1 / 32) * (1 / 16) ^ h := by
      rw [pow_succ, pow_succ, pow_mul]
      rw [show ((2:ℝ) ^ 2) = 4 by norm_num]
      rw [show (1 / 64 : ℝ) ^ h * (1/64) * (4 ^ h * 2) = ((1/64 : ℝ) * 4) ^ h * (1/32) by
        rw [mul_pow]; ring]
      rw [show (1 / 64 : ℝ) * 4 = 1 / 16 by norm_num]
      ring
    calc (1 / 64 : ℝ) ^ (h + 1) * 2 ^ ℓ
        ≤ (1 / 64 : ℝ) ^ (h + 1) * 2 ^ (2 * h + 1) := by
          apply mul_le_mul_of_nonneg_left h2l (by positivity)
      _ = (1 / 32) * (1 / 16) ^ h := hcalc
  calc ∑ x ∈ P, weight q x.1 * p ^ x.2.card
      ≤ (1 / 64 : ℝ) ^ (h + 1) * ∑ y ∈ Q, weight q y.1 := final
    _ ≤ (1 / 64 : ℝ) ^ (h + 1) * 2 ^ ℓ := by
        apply mul_le_mul_of_nonneg_left step3 (by positivity)
    _ ≤ (1 / 32) * (1 / 16) ^ h := hnum

end Math2

import Mathlib
import RequestProject.KahnKalai.Measure

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Covers, costs, smallness, and the *minimum fragments* of Park–Pham.
-/

open Finset

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- `G` covers `H`, i.e. `H ⊆ ⟨G⟩`: every edge of `H` contains an edge of `G`. -/
def Covers (G H : Finset (Finset α)) : Prop := ∀ S ∈ H, ∃ T ∈ G, T ⊆ S

omit [DecidableEq α] in
lemma Covers.refl (H : Finset (Finset α)) : Covers H H := fun S hS => ⟨S, hS, Finset.Subset.refl S⟩

omit [DecidableEq α] in
lemma Covers.trans {A B C : Finset (Finset α)} (h1 : Covers A B) (h2 : Covers B C) :
    Covers A C := by
  intro S hS
  obtain ⟨T, hT, hTS⟩ := h2 S hS
  obtain ⟨R, hR, hRT⟩ := h1 T hT
  exact ⟨R, hR, hRT.trans hTS⟩

/-- The cost `∑_{S ∈ G} p ^ |S|` of a family. -/
noncomputable def cost (p : ℝ) (G : Finset (Finset α)) : ℝ := ∑ S ∈ G, p ^ S.card

omit [DecidableEq α] in
lemma cost_nonneg {p : ℝ} (hp : 0 ≤ p) (G : Finset (Finset α)) : 0 ≤ cost p G :=
  Finset.sum_nonneg fun _ _ => pow_nonneg hp _

lemma cost_union_le {p : ℝ} (hp : 0 ≤ p) (G G' : Finset (Finset α)) :
    cost p (G ∪ G') ≤ cost p G + cost p G' := by
  classical
  have h1 : cost p (G ∪ G') ≤ cost p (G ∪ G') + cost p (G ∩ G') := by
    have := cost_nonneg hp (G ∩ G')
    linarith
  have h2 : cost p (G ∪ G') + cost p (G ∩ G') = cost p G + cost p G' := by
    simpa [cost] using
      Finset.sum_union_inter (s₁ := G) (s₂ := G') (f := fun S : Finset α => p ^ S.card)
  linarith [h1, h2]

/-- `H` is `p`-small if it has a cover of cost at most `1/2`. -/
def IsSmall (p : ℝ) (H : Finset (Finset α)) : Prop :=
  ∃ G : Finset (Finset α), Covers G H ∧ cost p G ≤ 1 / 2

section Fragment

variable (H : Finset (Finset α))

/-- The candidate fragments for the pair `(S, W)`: the sets `S' \ W` for edges `S' ⊆ W ∪ S`. -/
noncomputable def cand (W S : Finset α) : Finset (Finset α) :=
  (H.filter (fun S' => S' ⊆ W ∪ S)).image (fun S' => S' \ W)

lemma cand_nonempty {W S : Finset α} (hS : S ∈ H) : (cand H W S).Nonempty := by
  refine ⟨S \ W, ?_⟩
  simp only [cand, Finset.mem_image, Finset.mem_filter]
  exact ⟨S, ⟨hS, Finset.subset_union_right⟩, rfl⟩

/-- A minimum `(S, W)`-fragment: a smallest set of the form `S' \ W` with `S' ∈ H`,
`S' ⊆ W ∪ S`. -/
noncomputable def frag (W S : Finset α) : Finset α :=
  if h : (cand H W S).Nonempty then
    (Finset.exists_min_image (cand H W S) Finset.card h).choose
  else ∅

lemma frag_mem {W S : Finset α} (hS : S ∈ H) : frag H W S ∈ cand H W S := by
  have h := cand_nonempty H (W := W) hS
  rw [frag, dif_pos h]
  exact (Finset.exists_min_image (cand H W S) Finset.card h).choose_spec.1

lemma frag_min {W S : Finset α} (hS : S ∈ H) :
    ∀ x ∈ cand H W S, (frag H W S).card ≤ x.card := by
  have h := cand_nonempty H (W := W) hS
  rw [frag, dif_pos h]
  exact (Finset.exists_min_image (cand H W S) Finset.card h).choose_spec.2

lemma frag_spec {W S : Finset α} (hS : S ∈ H) :
    ∃ S' ∈ H, S' ⊆ W ∪ S ∧ frag H W S = S' \ W := by
  have h := frag_mem H (W := W) hS
  simp only [cand, Finset.mem_image, Finset.mem_filter] at h
  obtain ⟨S', ⟨hS', hsub⟩, heq⟩ := h
  exact ⟨S', hS', hsub, heq.symm⟩

lemma frag_subset {W S : Finset α} (hS : S ∈ H) : frag H W S ⊆ S := by
  obtain ⟨S', _, hsub, heq⟩ := frag_spec H hS
  rw [heq]
  intro y hy
  simp only [Finset.mem_sdiff] at hy
  rcases Finset.mem_union.1 (hsub hy.1) with h | h
  · exact absurd h hy.2
  · exact h

lemma frag_disjoint {W S : Finset α} (hS : S ∈ H) : Disjoint (frag H W S) W := by
  obtain ⟨S', _, _, heq⟩ := frag_spec H hS
  rw [heq]
  exact Finset.sdiff_disjoint

/-- The sub-hypergraph of `H` consisting of the (large) fragments that we pay for. -/
noncomputable def Ufam (h : ℕ) (W : Finset α) : Finset (Finset α) :=
  (H.filter (fun S => h < (frag H W S).card)).image (frag H W)

/-- The hypergraph carried to the next iteration: the small fragments. -/
noncomputable def Hfam (h : ℕ) (W : Finset α) : Finset (Finset α) :=
  (H.filter (fun S => (frag H W S).card ≤ h)).image (frag H W)

variable {H}

lemma mem_Ufam_iff {h : ℕ} {W T : Finset α} :
    T ∈ Ufam H h W ↔ ∃ S ∈ H, h < (frag H W S).card ∧ frag H W S = T := by
  simp only [Ufam, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨S, ⟨hS, hc⟩, heq⟩; exact ⟨S, hS, hc, heq⟩
  · rintro ⟨S, hS, hc, heq⟩; exact ⟨S, ⟨hS, hc⟩, heq⟩

lemma mem_Hfam_iff {h : ℕ} {W T : Finset α} :
    T ∈ Hfam H h W ↔ ∃ S ∈ H, (frag H W S).card ≤ h ∧ frag H W S = T := by
  simp only [Hfam, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨S, ⟨hS, hc⟩, heq⟩; exact ⟨S, hS, hc, heq⟩
  · rintro ⟨S, hS, hc, heq⟩; exact ⟨S, ⟨hS, hc⟩, heq⟩

lemma Hfam_bounded {h : ℕ} {W : Finset α} : ∀ T ∈ Hfam H h W, T.card ≤ h := by
  intro T hT
  obtain ⟨S, _, hc, heq⟩ := mem_Hfam_iff.1 hT
  exact heq ▸ hc

lemma Ufam_card_gt {h : ℕ} {W : Finset α} : ∀ T ∈ Ufam H h W, h < T.card := by
  intro T hT
  obtain ⟨S, _, hc, heq⟩ := mem_Ufam_iff.1 hT
  exact heq ▸ hc

/-- Every edge of `H` contains its fragment, which lies in `Ufam ∪ Hfam`. -/
lemma covers_union {h : ℕ} {W : Finset α} {G : Finset (Finset α)}
    (hG : Covers G (Hfam H h W)) : Covers (Ufam H h W ∪ G) H := by
  intro S hS
  by_cases hc : h < (frag H W S).card
  · exact ⟨frag H W S, Finset.mem_union_left _ (mem_Ufam_iff.2 ⟨S, hS, hc, rfl⟩),
      frag_subset H hS⟩
  · push_neg at hc
    obtain ⟨T, hT, hTsub⟩ := hG (frag H W S) (mem_Hfam_iff.2 ⟨S, hS, hc, rfl⟩)
    exact ⟨T, Finset.mem_union_right _ hT, hTsub.trans (frag_subset H hS)⟩

/-- Fragments are of the form `S' \ W`, so the residual family covers `Hfam`. -/
lemma residual_covers_Hfam {h : ℕ} {W : Finset α} :
    Covers (H.image (fun S => S \ W)) (Hfam H h W) := by
  intro T hT
  obtain ⟨S, hS, _, heq⟩ := mem_Hfam_iff.1 hT
  obtain ⟨S', hS', _, heq'⟩ := frag_spec H (W := W) hS
  exact ⟨S' \ W, Finset.mem_image.2 ⟨S', hS', rfl⟩, by rw [← heq', heq]⟩

variable (H)

/-- A choice of an edge of `H` inside `Z`, depending only on `Z`. -/
noncomputable def edgeIn (Z : Finset α) : Finset α :=
  if h : ∃ S ∈ H, S ⊆ Z then h.choose else ∅

lemma edgeIn_mem {Z : Finset α} (h : ∃ S ∈ H, S ⊆ Z) : edgeIn H Z ∈ H := by
  rw [edgeIn, dif_pos h]; exact h.choose_spec.1

lemma edgeIn_subset {Z : Finset α} (h : ∃ S ∈ H, S ⊆ Z) : edgeIn H Z ⊆ Z := by
  rw [edgeIn, dif_pos h]; exact h.choose_spec.2

variable {H}

/-- The set `W ∪ T(S,W)` contains an edge of `H`. -/
lemma frag_exists_edge {W S : Finset α} (hS : S ∈ H) : ∃ R ∈ H, R ⊆ W ∪ frag H W S := by
  obtain ⟨S', hS', _, heq⟩ := frag_spec H (W := W) hS
  refine ⟨S', hS', fun y hy => ?_⟩
  by_cases hyW : y ∈ W
  · exact Finset.mem_union_left _ hyW
  · refine Finset.mem_union_right _ ?_
    rw [heq]
    exact Finset.mem_sdiff.2 ⟨hy, hyW⟩

/-- The key property (16) of Park–Pham: the minimum fragment `T` is contained in the
canonical edge chosen inside `Z = W ∪ T`. -/
lemma frag_subset_edgeIn {W S : Finset α} (hS : S ∈ H) :
    frag H W S ⊆ edgeIn H (W ∪ frag H W S) := by
  have hex : ∃ R ∈ H, R ⊆ W ∪ frag H W S := frag_exists_edge hS
  set T := frag H W S with hTdef
  have hmem := edgeIn_mem H hex
  have hsub := edgeIn_subset H hex
  set Sh := edgeIn H (W ∪ T) with hSh
  have hTW : Disjoint T W := frag_disjoint H hS
  -- `Sh \ W ⊆ T`
  have h1 : Sh \ W ⊆ T := by
    intro y hy
    simp only [Finset.mem_sdiff] at hy
    rcases Finset.mem_union.1 (hsub hy.1) with h | h
    · exact absurd h hy.2
    · exact h
  -- `Sh \ W` is a candidate fragment, so `|T| ≤ |Sh \ W|`
  have h2 : Sh \ W ∈ cand H W S := by
    simp only [cand, Finset.mem_image, Finset.mem_filter]
    refine ⟨Sh, ⟨hmem, ?_⟩, rfl⟩
    intro y hy
    rcases Finset.mem_union.1 (hsub hy) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (frag_subset H hS h)
  have h3 : T.card ≤ (Sh \ W).card := frag_min H hS _ h2
  have h4 : Sh \ W = T := Finset.eq_of_subset_of_card_le h1 h3
  intro y hy
  have : y ∈ Sh \ W := by rw [h4]; exact hy
  exact (Finset.mem_sdiff.1 this).1

lemma Ufam_disjoint {h : ℕ} {W T : Finset α} (hT : T ∈ Ufam H h W) : Disjoint T W := by
  obtain ⟨S, hS, _, heq⟩ := mem_Ufam_iff.1 hT
  rw [← heq]; exact frag_disjoint H hS

lemma Ufam_exists_edge {h : ℕ} {W T : Finset α} (hT : T ∈ Ufam H h W) :
    ∃ R ∈ H, R ⊆ W ∪ T := by
  obtain ⟨S, hS, _, heq⟩ := mem_Ufam_iff.1 hT
  rw [← heq]; exact frag_exists_edge hS

lemma Ufam_subset_edgeIn {h : ℕ} {W T : Finset α} (hT : T ∈ Ufam H h W) :
    T ⊆ edgeIn H (W ∪ T) := by
  obtain ⟨S, hS, _, heq⟩ := mem_Ufam_iff.1 hT
  rw [← heq]; exact frag_subset_edgeIn hS

end Fragment

end Math2

