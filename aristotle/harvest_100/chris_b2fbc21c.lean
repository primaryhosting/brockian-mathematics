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

/-!
# Admissible tuples and positivity of the singular series

An `H : Finset ℕ` (thought of as a set of *gaps* / offsets of a prime constellation
`n + h`, `h ∈ H`) is **admissible** when, for every prime `p`, the reductions of `H`
modulo `p` do not cover all residue classes.  This is exactly the condition under which
the local factors of the Hardy–Littlewood singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p) (1 - 1/p)^(-|H|)` are all positive.

This file develops the basic theory and a general criterion producing admissible sets:
a set of size at most `m`, all of whose elements are coprime to `m !`, is admissible.
-/

open scoped BigOperators Nat

namespace Brockian

/-- The number of residue classes mod `p` occupied by `H`, i.e. `ν_H(p)`. -/
def residueCount (H : Finset ℕ) (p : ℕ) : ℕ := (H.image (· % p)).card

/-- `H` is an admissible set of gaps: for every prime `p` some residue class mod `p`
is missed by `H`. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- The local factor at `p` of the Hardy–Littlewood singular series of `H`. -/
noncomputable def singularFactor (H : Finset ℕ) (p : ℕ) : ℝ :=
  (1 - (residueCount H p : ℝ) / p) * (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ))

theorem residueCount_le_card (H : Finset ℕ) (p : ℕ) : residueCount H p ≤ H.card :=
  Finset.card_image_le

theorem image_mod_subset_range (H : Finset ℕ) {p : ℕ} (hp : 0 < p) :
    H.image (· % p) ⊆ Finset.range p := by
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨a, _, rfl⟩ := hx
  exact Finset.mem_range.2 (Nat.mod_lt _ hp)

/-- If some residue class `r < p` is missed by `H`, then `ν_H(p) < p`. -/
theorem residueCount_lt_of_miss {H : Finset ℕ} {p r : ℕ} (hp : 0 < p) (hr : r < p)
    (hmiss : ∀ h ∈ H, h % p ≠ r) : residueCount H p < p := by
  have hsub : H.image (· % p) ⊆ (Finset.range p).erase r := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact Finset.mem_erase.2 ⟨hmiss a ha, Finset.mem_range.2 (Nat.mod_lt _ hp)⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_range.2 hr), Finset.card_range] at hle
  exact lt_of_le_of_lt hle (Nat.sub_lt hp one_pos)

/-- Admissibility is equivalent to `ν_H(p) < p` for all primes `p`. -/
theorem admissible_iff_residueCount_lt {H : Finset ℕ} :
    Admissible H ↔ ∀ p : ℕ, p.Prime → residueCount H p < p := by
  constructor
  · rintro h p hp
    obtain ⟨r, hr, hmiss⟩ := h p hp
    exact residueCount_lt_of_miss hp.pos hr hmiss
  · intro h p hp
    have hlt := h p hp
    have hex : ∃ r ∈ Finset.range p, r ∉ H.image (· % p) := by
      by_contra hcon
      push_neg at hcon
      have hsub : Finset.range p ⊆ H.image (· % p) := fun r hr => hcon r hr
      have hle := Finset.card_le_card hsub
      rw [Finset.card_range] at hle
      exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)
    obtain ⟨r, hr, hrn⟩ := hex
    refine ⟨r, Finset.mem_range.1 hr, ?_⟩
    intro h' hh' hcon
    exact hrn (Finset.mem_image.2 ⟨h', hh', hcon⟩)

/-- For a prime `p`, positivity of the local factor of the singular series is exactly the
local admissibility condition at `p`. -/
theorem singularFactor_pos_iff {H : Finset ℕ} {p : ℕ} (hp : p.Prime) :
    0 < singularFactor H p ↔ residueCount H p < p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hbase : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
    have h1 : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp0]
      exact_mod_cast hp.one_lt
    linarith
  have hzpow : (0 : ℝ) < (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ)) := zpow_pos hbase _
  rw [singularFactor, mul_pos_iff]
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · have hdiv : (residueCount H p : ℝ) / p < 1 := by linarith
      rw [div_lt_one hp0] at hdiv
      exact_mod_cast hdiv
    · exact absurd h2 (not_lt.2 hzpow.le)
  · intro h
    refine Or.inl ⟨?_, hzpow⟩
    have hdiv : (residueCount H p : ℝ) / p < 1 := by
      rw [div_lt_one hp0]
      exact_mod_cast h
    linarith

/-- Admissibility is equivalent to positivity of every local factor of the singular
series. -/
theorem admissible_iff_singularFactor_pos {H : Finset ℕ} :
    Admissible H ↔ ∀ p : ℕ, p.Prime → 0 < singularFactor H p := by
  rw [admissible_iff_residueCount_lt]
  exact ⟨fun h p hp => (singularFactor_pos_iff hp).2 (h p hp),
    fun h p hp => (singularFactor_pos_iff hp).1 (h p hp)⟩

/-- Admissibility only depends on the set of gaps up to translation. -/
theorem admissible_image_add {H : Finset ℕ} (hH : Admissible H) (t : ℕ) :
    Admissible (H.image (· + t)) := by
  intro p hp
  obtain ⟨r, hr, hmiss⟩ := hH p hp
  refine ⟨(r + t) % p, Nat.mod_lt _ hp.pos, ?_⟩
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  intro hcon
  have hmod : a ≡ r [MOD p] := Nat.ModEq.add_right_cancel' t hcon
  exact hmiss a ha (by rwa [Nat.ModEq, Nat.mod_eq_of_lt hr] at hmod)

/-- **Main criterion.**  A set of at most `m` natural numbers, each coprime to `m !`,
is admissible. -/
theorem admissible_of_coprime_factorial {H : Finset ℕ} {m : ℕ} (hcard : H.card ≤ m)
    (hcop : ∀ n ∈ H, Nat.Coprime n (m !)) : Admissible H := by
  refine admissible_iff_residueCount_lt.2 fun p hp => ?_
  by_cases hpm : p ≤ m
  · refine residueCount_lt_of_miss hp.pos hp.pos ?_
    intro h hh hcon
    have hdvd : p ∣ h := Nat.dvd_of_mod_eq_zero hcon
    have hgcd : p ∣ Nat.gcd h (m !) := Nat.dvd_gcd hdvd (Nat.dvd_factorial hp.pos hpm)
    rw [hcop h hh] at hgcd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hgcd)
  · push_neg at hpm
    exact lt_of_le_of_lt (residueCount_le_card H p) (lt_of_le_of_lt hcard hpm)

/-- **Admissible gap ranges.**  Inside any window `[1, N]`, the integers with no prime
factor `≤ m` form an admissible set of gaps as soon as there are at most `m` of them. -/
theorem admissible_coprimeRange {m N : ℕ}
    (hcard : ((Finset.Icc 1 N).filter fun n => Nat.Coprime n (m !)).card ≤ m) :
    Admissible ((Finset.Icc 1 N).filter fun n => Nat.Coprime n (m !)) :=
  admissible_of_coprime_factorial hcard fun _ hn => (Finset.mem_filter.1 hn).2

end Brockian

import RequestProject.Brockian.SingularSeriesGaps

/-!
# A new family of admissible gap ranges inside a window of width `7280`

We exhibit an explicit set `gapSet7280` of `790` natural numbers contained in the interval
`[1, 7280]` and prove that it is admissible, i.e. for every prime `p` the reductions of the
set modulo `p` miss a residue class.  Equivalently every local factor of the
Hardy--Littlewood singular series is positive.

The set is the set of integers in `[1, 7280]` that are coprime to every prime `p ≤ 800`
(namely `1` together with the primes in `(800, 7280]`).  Since it has `790 ≤ 800` elements,
the general criterion `Brockian.admissible_of_coprime_factorial` applies.

Admissibility only depends on the gaps, so *every* translate of this set is admissible as
well; this yields a whole family of admissible gap ranges of width at most `7280`.
-/

open scoped Nat

set_option maxRecDepth 100000

namespace Brockian

/-- The `790` integers in `[1, 7280]` having no prime factor `≤ 800`, listed increasingly. -/
def gapList7280 : List ℕ :=
 [
  1, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919,
   929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033,
   1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129,
   1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249,
   1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367,
   1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481,
   1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579,
   1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693,
   1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801,
   1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931,
   1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039,
   2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143,
   2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281,
   2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383,
   2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521,
   2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657,
   2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731,
   2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851,
   2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971,
   2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119,
   3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253,
   3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361,
   3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499,
   3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607,
   3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719,
   3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851,
   3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967,
   3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093,
   4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229,
   4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349,
   4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483,
   4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621,
   4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733,
   4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889,
   4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999,
   5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113,
   5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273,
   5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413,
   5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519,
   5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653,
   5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783,
   5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879,
   5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047,
   6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173,
   6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299,
   6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397,
   6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569,
   6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701,
   6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829,
   6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961,
   6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079,
   7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229,
   7237, 7243, 7247, 7253]

/-- The explicit admissible set of gaps: the `790` integers in `[1, 7280]` with no prime
factor `≤ 800`. -/
def gapSet7280 : Finset ℕ := gapList7280.toFinset

theorem gapList7280_isChain : gapList7280.IsChain (· < ·) := by decide

theorem gapList7280_nodup : gapList7280.Nodup :=
  List.Pairwise.nodup (List.isChain_iff_pairwise.1 gapList7280_isChain)

theorem gapList7280_length : gapList7280.length = 790 := by rfl

/-- The set has `790` elements. -/
theorem gapSet7280_card : gapSet7280.card = 790 := by
  rw [gapSet7280, List.toFinset_card_of_nodup gapList7280_nodup, gapList7280_length]

/-- All gaps lie in the window `[1, 7280]`. -/
theorem gapSet7280_mem_Icc : ∀ n ∈ gapSet7280, 1 ≤ n ∧ n ≤ 7280 := by
  intro n hn
  rw [gapSet7280, List.mem_toFinset] at hn
  revert n hn
  decide

/-- Every element is coprime to `800 !`, i.e. has no prime factor `≤ 800`. -/
theorem gapSet7280_coprime : ∀ n ∈ gapSet7280, Nat.Coprime n (800 !) := by
  intro n hn
  rw [gapSet7280, List.mem_toFinset] at hn
  revert n hn
  decide

/-- The explicit set of gaps is admissible. -/
theorem admissible_gapSet7280 : Admissible gapSet7280 :=
  admissible_of_coprime_factorial (by rw [gapSet7280_card]; norm_num) gapSet7280_coprime

/-- **A new family of admissible gap ranges.**  For every shift `t`, the translated set
`gapSet7280 + t` is a set of `790` integers inside a window of width `7280` which is
admissible; equivalently, all local factors of its Hardy--Littlewood singular series are
positive. -/
theorem SingularSeriesGaps7280 :
    gapSet7280.card = 790 ∧ (∀ n ∈ gapSet7280, 1 ≤ n ∧ n ≤ 7280) ∧
      ∀ t : ℕ, (gapSet7280.image (· + t)).card = 790 ∧
        Admissible (gapSet7280.image (· + t)) ∧
        ∀ p : ℕ, p.Prime → 0 < singularFactor (gapSet7280.image (· + t)) p := by
  refine ⟨gapSet7280_card, gapSet7280_mem_Icc, fun t => ⟨?_, ?_, ?_⟩⟩
  · rw [Finset.card_image_of_injective _ (add_left_injective t), gapSet7280_card]
  · exact admissible_image_add admissible_gapSet7280 t
  · exact admissible_iff_singularFactor_pos.1 (admissible_image_add admissible_gapSet7280 t)

end Brockian

#print axioms Brockian.SingularSeriesGaps7280

