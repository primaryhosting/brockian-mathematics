/-
/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- A finite set of integers `H` is *admissible* if for every prime `p` the reductions of the
elements of `H` modulo `p` omit at least one residue class.  Equivalently, the singular series
`𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}` of the Hardy–Littlewood prime `k`-tuple conjecture
is nonzero. -/

private lemma primeCount_Ico_251_1711 : ((Finset.Ico 251 1711).filter Nat.Prime).card = 214 := by
  have c1 : ((Finset.Ico 251 397).filter Nat.Prime).card = 24 := by decide +kernel
  have c2 : ((Finset.Ico 397 543).filter Nat.Prime).card = 23 := by decide +kernel
  have c3 : ((Finset.Ico 543 689).filter Nat.Prime).card = 24 := by decide +kernel
  have c4 : ((Finset.Ico 689 835).filter Nat.Prime).card = 21 := by decide +kernel
  have c5 : ((Finset.Ico 835 981).filter Nat.Prime).card = 20 := by decide +kernel
  have c6 : ((Finset.Ico 981 1127).filter Nat.Prime).card = 23 := by decide +kernel
  have c7 : ((Finset.Ico 1127 1273).filter Nat.Prime).card = 17 := by decide +kernel
  have c8 : ((Finset.Ico 1273 1419).filter Nat.Prime).card = 18 := by decide +kernel
  have c9 : ((Finset.Ico 1419 1565).filter Nat.Prime).card = 23 := by decide +kernel
  have c10 : ((Finset.Ico 1565 1711).filter Nat.Prime).card = 21 := by decide +kernel
  rw [primeCount_split (show (251:ℕ) ≤ 397 by norm_num) (show (397:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (397:ℕ) ≤ 543 by norm_num) (show (543:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (543:ℕ) ≤ 689 by norm_num) (show (689:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (689:ℕ) ≤ 835 by norm_num) (show (835:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (835:ℕ) ≤ 981 by norm_num) (show (981:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (981:ℕ) ≤ 1127 by norm_num) (show (1127:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (1127:ℕ) ≤ 1273 by norm_num) (show (1273:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (1273:ℕ) ≤ 1419 by norm_num) (show (1419:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (1419:ℕ) ≤ 1565 by norm_num) (show (1565:ℕ) ≤ 1711 by norm_num),
    c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]

