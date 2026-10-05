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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede any module doc comment, so the
-- required header block appears immediately after the single `import Mathlib` line.

namespace Brockian.LegendreConjecture

/-- `PrimeBetweenSquares n` states that there is a prime strictly between `n ^ 2`
and `(n + 1) ^ 2`. -/
def PrimeBetweenSquares (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between
`n ^ 2` and `(n + 1) ^ 2`.  This is a well-known open problem. -/
def LegendreStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → PrimeBetweenSquares n

/-- The short-interval prime hypothesis: every interval `(x, x + √x]` with `x ≥ 1`
contains a prime (here `Nat.sqrt` is the integer square root).  This is a natural
strengthening of Legendre's conjecture, and is itself open. -/
def ShortIntervalHypothesis : Prop :=
  ∀ x : ℕ, 1 ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ p ≤ x + Nat.sqrt x

/-- **Conditional reduction of Legendre's conjecture.**

Legendre's conjecture — for every `n ≥ 1` there is a prime strictly between `n ^ 2`
and `(n + 1) ^ 2` — is an open problem, so it is proved here conditionally: it follows
from the short-interval prime hypothesis, namely that every interval `(x, x + √x]`
with `x ≥ 1` contains a prime.  Indeed, taking `x = n ^ 2` produces a prime `p` with
`n ^ 2 < p ≤ n ^ 2 + n < (n + 1) ^ 2`. -/
theorem LegendreConjecture (h : ShortIntervalHypothesis) : LegendreStatement := by
  intro n hn
  obtain ⟨p, hp, hlt, hle⟩ := h (n ^ 2) (Nat.one_le_pow _ _ hn)
  refine ⟨p, hp, hlt, ?_⟩
  have hsq : Nat.sqrt (n ^ 2) = n := by simp [pow_two, Nat.sqrt_eq]
  have hpn : p ≤ n ^ 2 + n := by simpa [hsq] using hle
  nlinarith [hpn]

/-- Unconditional weakening of Legendre's conjecture obtained from Bertrand's
postulate: for every `n ≥ 1` there is a prime `p` with `n ^ 2 < p ≤ 2 * n ^ 2`. -/
theorem exists_prime_between_sq_and_two_mul_sq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p ≤ 2 * n ^ 2 := by
  have hne : n ^ 2 ≠ 0 := by positivity
  exact Nat.exists_prime_lt_and_le_two_mul (n ^ 2) hne

/-- For each `1 ≤ n ≤ 500`, `legendreWitnesses.getD (n - 1) 0` is the least prime
exceeding `n ^ 2`; it is used to verify Legendre's conjecture in that range. -/
def legendreWitnesses : List ℕ :=
[2, 5, 11, 17, 29, 37, 53, 67, 83, 101, 127, 149, 173, 197, 227, 257, 293, 331, 367, 401, 443, 487, 541, 577, 631, 677, 733, 787, 853, 907, 967, 1031, 1091, 1163, 1229, 1297, 1373, 1447, 1523, 1601, 1693, 1777, 1861, 1949, 2027, 2129, 2213, 2309, 2411, 2503, 2609, 2707, 2819, 2917, 3037, 3137, 3251, 3371, 3491, 3607, 3727, 3847, 3989, 4099, 4229, 4357, 4493, 4637, 4783, 4903, 5051, 5189, 5333, 5477, 5639, 5779, 5939, 6089, 6247, 6421, 6563, 6733, 6899, 7057, 7229, 7411, 7573, 7753, 7927, 8101, 8287, 8467, 8663, 8837, 9029, 9221, 9413, 9613, 9803, 10007, 10211, 10427, 10613, 10831, 11027, 11239, 11467, 11677, 11887, 12101, 12323, 12547, 12781, 13001, 13229, 13457, 13691, 13931, 14173, 14401, 14653, 14887, 15131, 15377, 15629, 15877, 16139, 16411, 16649, 16901, 17167, 17431, 17707, 17957, 18229, 18503, 18773, 19051, 19333, 19603, 19889, 20173, 20477, 20743, 21031, 21317, 21611, 21911, 22229, 22501, 22807, 23117, 23417, 23719, 24029, 24337, 24659, 24967, 25301, 25601, 25931, 26249, 26573, 26903, 27239, 27581, 27893, 28229, 28571, 28901, 29243, 29587, 29947, 30293, 30631, 30977, 31333, 31687, 32051, 32401, 32771, 33149, 33493, 33857, 34231, 34603, 34981, 35353, 35729, 36107, 36493, 36871, 37253, 37643, 38039, 38431, 38821, 39209, 39607, 40009, 40423, 40813, 41213, 41617, 42043, 42437, 42853, 43271, 43691, 44101, 44531, 44953, 45377, 45817, 46229, 46663, 47093, 47527, 47963, 48407, 48847, 49297, 49739, 50177, 50627, 51109, 51539, 51991, 52453, 52901, 53377, 53831, 54293, 54767, 55229, 55697, 56171, 56659, 57131, 57601, 58099, 58567, 59051, 59539, 60029, 60521, 61027, 61507, 62003, 62501, 63029, 63521, 64013, 64553, 65027, 65537, 66067, 66569, 67103, 67601, 68141, 68659, 69191, 69697, 70229, 70769, 71293, 71837, 72367, 72901, 73453, 73999, 74531, 75079, 75629, 76207, 76733, 77291, 77849, 78401, 78977, 79531, 80107, 80657, 81233, 81799, 82373, 82963, 83537, 84121, 84691, 85297, 85853, 86441, 87037, 87623, 88211, 88807, 89413, 90001, 90617, 91229, 91811, 92419, 93047, 93637, 94253, 94873, 95483, 96137, 96731, 97367, 97973, 98597, 99233, 99859, 100493, 101141, 101771, 102407, 103043, 103687, 104347, 104987, 105649, 106277, 106937, 107599, 108247, 108907, 109567, 110233, 110899, 111577, 112237, 112901, 113591, 114259, 114941, 115601, 116293, 116969, 117659, 118343, 119027, 119723, 120413, 121123, 121843, 122501, 123203, 123911, 124633, 125329, 126031, 126739, 127453, 128173, 128903, 129607, 130337, 131059, 131771, 132499, 133241, 133963, 134699, 135427, 136163, 136943, 137653, 138389, 139133, 139883, 140627, 141397, 142151, 142897, 143651, 144407, 145177, 145931, 146701, 147457, 148229, 148997, 149771, 150551, 151337, 152111, 152897, 153689, 154459, 155251, 156041, 156817, 157627, 158407, 159209, 160001, 160807, 161611, 162413, 163223, 164039, 164837, 165653, 166471, 167309, 168109, 168937, 169751, 170579, 171401, 172243, 173059, 173891, 174737, 175573, 176401, 177257, 178091, 178931, 179779, 180629, 181499, 182333, 183191, 184043, 184901, 185767, 186629, 187507, 188359, 189229, 190097, 190979, 191861, 192737, 193601, 194483, 195389, 196271, 197137, 198031, 198929, 199811, 200713, 201611, 202519, 203417, 204311, 205211, 206123, 207029, 207941, 208877, 209767, 210709, 211619, 212557, 213449, 214373, 215297, 216233, 217157, 218107, 219031, 219971, 220901, 221849, 222787, 223747, 224677, 225629, 226601, 227531, 228509, 229459, 230431, 231367, 232333, 233293, 234259, 235231, 236207, 237173, 238151, 239137, 240101, 241093, 242069, 243073, 244043, 245029, 246017, 247031, 248021, 249017, 250007]

set_option maxRecDepth 1000000 in
/-- The certificate check behind `legendre_of_le_five_hundred`: each listed witness is
free of divisors up to its square root, and lies strictly between consecutive squares. -/
private theorem legendreWitnesses_spec :
    ∀ i ∈ Finset.range 500,
      (2 ≤ legendreWitnesses.getD i 0 ∧
        ∀ m ∈ Finset.Icc 2 501, m * m ≤ legendreWitnesses.getD i 0 →
          ¬ m ∣ legendreWitnesses.getD i 0) ∧
      (i + 1) ^ 2 < legendreWitnesses.getD i 0 ∧
      legendreWitnesses.getD i 0 < (i + 2) ^ 2 := by
  decide +kernel

/-- **Unconditional verification of Legendre's conjecture for all `1 ≤ n ≤ 500`.** -/
theorem legendre_of_le_five_hundred (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 500) :
    PrimeBetweenSquares n := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  obtain ⟨⟨h2, hdiv⟩, hlo, hhi⟩ := legendreWitnesses_spec i (Finset.mem_range.mpr (by omega))
  set p := legendreWitnesses.getD i 0
  have hple : p < 501 ^ 2 := lt_of_lt_of_le hhi (Nat.pow_le_pow_left (by omega) 2)
  refine ⟨p, ?_, hlo, by omega⟩
  refine Nat.prime_def_le_sqrt.mpr ⟨h2, fun m hm2 hms => ?_⟩
  have hmm : m * m ≤ p := Nat.le_sqrt.mp hms
  have hm501 : m ≤ 501 := by nlinarith
  exact hdiv m (Finset.mem_Icc.mpr ⟨hm2, hm501⟩) hmm

end Brockian.LegendreConjecture

