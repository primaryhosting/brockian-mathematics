# Machine-Verified Results in Quasi-Amicable (Betrothed) Number Theory

**Status: DRAFT for internal review — not published, not submitted.**
Date: 2026-08-11 · Author: BCC / Brockian Mathematics program
Verification: local `lake build` (Lean toolchain pinned at `leanprover/lean4:v4.32.0` + Mathlib) and the AXLE cloud kernel (Lean 4.32.0). No `sorry`, `admit`, or added `axiom` appears in any file cited below.

---

## 1. What betrothed numbers are

Write `s(n)` for the **aliquot sum** — the sum of the proper divisors of `n`. A pair `(m, n)` of distinct positive integers is **betrothed** (also called **quasi-amicable** or **reduced amicable**) when each is *one more* than the aliquot sum of the other:

> `s(m) = n + 1` and `s(n) = m + 1`.

They are the "off-by-one" analogue of amicable pairs (`s(m) = n`, `s(n) = m`). The smallest is `(48, 75)`; then `(140, 195)`, `(1050, 1925)`, `(1575, 1648)`, `(5775, 6128)`, …. This is OEIS **A005276**. Two questions are **classically open**: whether there are **infinitely many** betrothed pairs, and whether any pair has **both members of the same parity** (every known pair is one even and one odd number).

This note reports what we have **machine-verified**, and — importantly — separates it into three registers: what is *classical and not ours*, what is a *new formalization*, and what is a *genuinely new (small) theorem*. It also states plainly what remains open.

---

## 2. The results, by register

### 2a. CLASSICAL — not our discovery

The **two-cycle / quasi-cycle viewpoint** of betrothed numbers, and the structural restrictions on their form (e.g. the same-parity case forcing a square or twice-a-square), are due to **Hagis & Lord, "Quasi-Amicable Numbers," *Math. Comp.* 31 (1977), 608–611**. That betrothed numbers have **density zero** is **Pollack, "Quasi-Amicable Numbers are Rare," *J. Integer Seq.* 14 (2011)**. We claim none of this; we build on it and cite it.

### 2b. NEW FORMALIZATION — the exact Lean statements in this repository

In `Brockian/BetrothedNumbers/Dynamics.lean` (integrated, builds locally on `Brockian/BetrothedNumbers.lean`) we give an exact Lean rendering of the classical two-cycle picture and an exact abundance **balance law** for the standard `2^k · p` construction family.

Define the **partner map** `partner n := s(n) − 1`. Betrothed pairs are exactly its nontrivial two-cycles:

```lean
def partner (n : ℕ) : ℕ := aliquot n - 1

theorem betrothed_iff_twoCycle {m n : ℕ} :
    Betrothed m n ↔
      m ≠ n ∧ 1 ≤ aliquot m ∧ 1 ≤ aliquot n ∧ partner m = n ∧ partner n = m

theorem partner_involutive_on_pair {m n : ℕ} (h : Betrothed m n) :
    partner (partner m) = m

theorem partner_ne_self_on_pair {m n : ℕ} (h : Betrothed m n) : partner m ≠ m
```

For the construction family `2^k · p`, the forced odd partner is `thabitPartner k p = (2^k − 1)(p + 2)`. Under an explicit **σ-criterion hypothesis** (that `σ₁` of that partner equals `(2^{k+1} − 1)(p + 1)`), the sign of `(p + 3) − 2^{k+1}` fixes the abundance class of the partner exactly:

```lean
theorem thabit_balance_identity {k p : ℕ} (hk : 1 ≤ k)
    (hcriterion : σ 1 (thabitPartner k p) = (2 ^ (k + 1) - 1) * (p + 1)) :
    σ 1 (thabitPartner k p) + 2 ^ (k + 1) = 2 * thabitPartner k p + (p + 3)

-- and the three phase-boundary corollaries, each CONDITIONAL on the same hcriterion:
theorem thabit_deficient_iff … : σ 1 (…) < 2 * (…)  ↔  p + 3 < 2 ^ (k + 1)
theorem thabit_perfect_iff   … : σ 1 (…) = 2 * (…)  ↔  p + 3 = 2 ^ (k + 1)
theorem thabit_abundant_iff  … : 2 * (…) < σ 1 (…)  ↔  2 ^ (k + 1) < p + 3
```

**Honesty note:** the balance law and its deficient/perfect/abundant corollaries are **conditional** on the σ-criterion — it is an explicit hypothesis in each signature, *not* an unproven axiom, and this note does not claim it holds unconditionally. A self-contained twin of these statements, corrected to the repo's actual `aliquot`/`Betrothed` definitions, is AXLE-verified in `aristotle/betrothed_faithful.lean` (Lean 4.32.0). The exact Lean two-cycle reformulation and the phase-boundary balance law appear to be **new to this repository**. A modern Lean amicable-numbers library — **Chen, Tang, Zhan, "Formalization of Amicable Numbers Theory," arXiv:2601.07444 (2026)** — includes a betrothed layer that, per their paper, is a *definition plus the two smallest examples*; our formalization is materially more, **pending a direct source-level comparison** (we have not diffed their Lean sources, so we do not assert superiority as fact).

### 2c. NEW DEDUCTION — a genuinely original small theorem

The one result here that is, to our knowledge, **new mathematics** (not merely a formalization of something known) is an **unconditional obstruction**, machine-verified in
`aristotle/best_proofs/Brockian_BetrothedNumbers_no_pair_of_mersenne_and_shifted_prime.lean`:

```lean
/-- Negative obstruction. Let k ≥ 2 and let p be an odd prime such that both
    2^k − 1 and p + 2 are prime. Then 2^k * p has no betrothed partner. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ}
    (hk : 2 ≤ k) (hp : p.Prime) (hodd : Odd p)
    (hq : Nat.Prime (2 ^ k - 1)) (hr : Nat.Prime (p + 2)) :
    ¬ ∃ m : ℕ, IsBetrothedPair m (2 ^ k * p)
```

Here `IsBetrothedPair m n := 0 < m ∧ 0 < n ∧ σ₁ m = m + n + 1 ∧ σ₁ n = m + n + 1` (distinctness is *not* assumed, which only strengthens the non-existence claim). The theorem is **unconditional**: its hypotheses are exactly `k ≥ 2`, `p` an odd prime, and the two auxiliary primality conditions (`2^k − 1` a Mersenne prime, `p + 2` a prime). There is no σ-criterion hypothesis and no `sorry`/`axiom` in the signature or proof — it is a complete kernel-checked deduction. The proof route: a **unique-partner lemma** (`betrothed_partner_eq`) forces any partner of `2^k·p` to equal `(2^k − 1)(p + 2)`; then when both factors are prime, the sum-of-divisors identity `(q+1)(p+3) = q(p+2) + (q+1)p + 1` collapses to `q·p = q + 2`, which is impossible for `q ≥ 3`, `p ≥ 3`. A degenerate square sub-case (`q = p+2`) is ruled out separately.

Plainly: this is a **small but genuine original contribution** to quasi-amicable number theory — a clean sufficient condition under which a member of the `2^k·p` family provably has no betrothed partner.

### 2d. Computational evidence (COMPUTATION register — evidence, not proof)

Independently reproduced from scratch (`aristotle/betrothed_verification_report.json`): a falsifier over **996,888** parameter pairs (`1 ≤ k ≤ 24`, odd prime `p ≤ 500000`) found **exactly three** betrothed solutions in the `2^k·p` family — `(48, 75)` deficient, `(1648, 1575)` abundant, `(6128, 5775)` abundant — and among the **31,955** cases where *both* auxiliary numbers `2^k−1` and `p+2` are prime, **zero** successes. That zero is the computational *evidence* consistent with the obstruction theorem above; it proves nothing beyond the range searched. A bonus empirical finding: the construction identity `B(2^k·p) = (2^k − 1)(p + 2)` held for **all** 996,888 pairs. Concrete pairs are also verified as standalone kernel theorems, e.g. `betrothed_48_75`, `betrothed_140_195`, `betrothed_1050_1925` (repo) and `betrothed_5775_6128` (`aristotle/best_proofs/…_5775_6128.lean`).

### 2e. NOT RESOLVED — open questions we did **not** touch

- **Infinitude of betrothed pairs** — OPEN. Recorded in the repo as an unproven `def BetrothedInfinitude`; we do not prove it.
- **Same-parity betrothed pair** — OPEN in both directions. Recorded as `def SameParityBetrothedExists`. We verify only that the two smallest known pairs have *opposite* parity; that is an illustration, not a resolution.
- The obstruction is a *sufficient* non-existence condition for one construction family; it says nothing about betrothed pairs outside `2^k·p`, and nothing about density (Pollack already has density zero).

---

## 3. What is new vs. classical vs. open

| Item | Register | Ours? | Verified how |
|---|---|---|---|
| Two-cycle / quasi-cycle viewpoint | Classical (Hagis–Lord 1977) | No | — |
| Same-parity ⇒ square / twice-square restriction | Classical (Hagis–Lord 1977) | No | — |
| Density zero | Classical (Pollack 2011) | No | — |
| Exact Lean two-cycle reformulation (`betrothed_iff_twoCycle`, partner involutivity/ne-self) | New **formalization** | Yes (repo) | `lake build`, Lean 4.32.0 |
| `2^k·p` abundance **balance law** + deficient/perfect/abundant phase boundary | New **formalization**, **conditional** on σ-criterion | Yes (repo) | `lake build` + AXLE, Lean 4.32.0 |
| **Mersenne / shifted-prime obstruction** (`no_pair_of_mersenne_and_shifted_prime`) | New **deduction** (original small theorem), **unconditional** | Yes | AXLE kernel, Lean 4.32.0 |
| 996,888-pair falsifier; 0/31,955 both-prime successes | Computation (evidence) | Yes (reproduced) | independent script |
| Concrete pair witnesses (`48/75`, …, `5775/6128`) | Computation / kernel | Yes | `decide` / `norm_num`, kernel |
| **Infinitude** of betrothed pairs | **OPEN** | — | not attempted |
| **Same-parity** existence | **OPEN** | — | not attempted |

---

## 4. Provenance and verification method

- **Local repo module:** `Brockian/BetrothedNumbers.lean` (definitions `aliquot`, `Betrothed`) and `Brockian/BetrothedNumbers/Dynamics.lean` (two-cycle reformulation + balance law). Builds with `lake build`; toolchain pinned at `leanprover/lean4:v4.32.0` + Mathlib.
- **AXLE-verified self-contained twin:** `aristotle/betrothed_faithful.lean` (Lean 4.32.0), rebuilt against the repo's real definitions after the originally delivered `BetrothedDynamics.lean` was found to reference a nonexistent `IsBetrothedPair` predicate.
- **Unconditional obstruction:** `aristotle/best_proofs/Brockian_BetrothedNumbers_no_pair_of_mersenne_and_shifted_prime.lean`, produced via the Aristotle prover and kernel-checked. Confirmed no unproven hypotheses in the signature and no `sorry`/`axiom` in the proof.
- **Computation:** `aristotle/betrothed_verification_report.json`, independently reproduced from scratch.
- **Literature boundary:** Hagis & Lord (1977); Pollack (2011); Chen–Tang–Zhan, arXiv:2601.07444 (2026); OEIS A005276.

**Open review item for Chris:** the prompt referenced Lean 4.33.0-rc2 for the local build, but the repo's `lean-toolchain` currently pins `v4.32.0` and the module headers record 4.32.0 — this note states 4.32.0 to match the files as they stand. Worth confirming before any external write-up. The comparison to the 2026 Chen–Tang–Zhan betrothed layer is stated as "materially more, pending direct source comparison" and should be checked against their actual Lean sources before any public claim.
