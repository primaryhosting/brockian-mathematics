# Machine-Verified Structure Theorems for Zumkeller Numbers

**Christopher Brock**, with AI-assisted formalization (Aristotle prover fleet + AXLE kernel verification; see §6).

**Status: DRAFT for internal review — not published, not submitted.**
Date: 2026-08-27 · Brockian Mathematics program, `primaryhosting/brockian-mathematics`
Verification: every registered claim below is independently kernel-checked by AXLE (Axiom) at toolchain `lean-4.32.2`, axiom-clean (each proof depends only on `{propext, Classical.choice, Quot.sound}`). Local `lake build` on the pinned toolchain is **pending** for these modules, matching the registry's `lake_build: "pending"` posture. No `sorry`, `admit`, `native_decide`, or added `axiom` appears in any file cited below.

Source of truth: `registry/theorems.json` and the AXLE attestations
`registry/attestations/ZumkellerNumbers.json` and `registry/attestations/ZumkellerStructure.json`
(both `module_verified: true`, environment `lean-4.32.2`).

---

## 1. What Zumkeller numbers are

A positive integer `n` is a **Zumkeller number** if its set of divisors can be partitioned into two subsets with equal sums. The sequence begins 6, 12, 20, 24, 28, 30, 40, … (OEIS **A083207**, after Reinhard Zumkeller). Writing `σ(n)` for the sum of divisors, an equivalent *half-sum characterization* is immediate: `n` is Zumkeller iff some subset `S` of its divisors satisfies `2 · ∑S = σ(n)` — the complement of `S` inside the divisors is then the other half.

Why the divisor-partition lens matters:

- **It sits strictly between perfection and abundance.** Every perfect number (`σ(n) = 2n`) is Zumkeller — take `S = {n}` — and every Zumkeller number is perfect-or-abundant (`2n ≤ σ(n)`), while deficient numbers are excluded outright. So Zumkeller numbers are exactly the perfect-or-abundant numbers whose *excess* `σ(n) − 2n` is realizable by a genuinely balanced split; abundance is necessary but famously not sufficient (18 is abundant, `σ(18) = 39` is odd, so 18 is not Zumkeller).
- **It lives next door to the odd-perfect problem.** The smallest odd Zumkeller number is 945 = 3³·5·7 — the smallest odd abundant number (classical background; see Peng–Bhaskara Rao [2]). Structural constraints on odd Zumkeller numbers (e.g., that they cannot be perfect squares, proved below) are cousins of the parity and square-part constraints that drive the odd-perfect-number literature.
- **Parity obstructions are exact.** The parity of `σ(n)` is governed by a classical square/twice-a-square dichotomy, and Zumkeller numbers require `σ(n)` even; this makes the obstruction side of the theory fully mechanizable.

The general theory here — necessary conditions, closure under coprime multiplication, exclusion of prime powers — corresponds to results of Peng & Bhaskara Rao [2]. **We claim no priority for the mathematics of those statements**; what this note reports is their machine-verified formalization in Lean 4 + Mathlib inside the Brockian corpus, with per-declaration kernel attestation, plus one machine-found **disproof** of a queued conjecture (§5).

---

## 2. The formal definition

The definition used throughout, quoted exactly from `Brockian/ZumkellerNumbers.lean` (registry entry `Brockian.ZumkellerNumbers.Zumkeller`, register DEFINITION):

```lean
/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of σ(n). -/
def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d
```

`Brockian/ZumkellerStructure.lean` repeats this definition verbatim in its own namespace (`Brockian.ZumkellerStructure.Zumkeller`) so that the module is self-contained; the two definitions are syntactically identical. That the half-sum form is equivalent to the naïve equal-partition form is not left informal — it is itself a registered theorem (`zumkeller_iff_partition`, §3.2).

---

## 3. The theorems

Eighteen entries carry the Zumkeller name in `registry/theorems.json`: eleven in module `Brockian.ZumkellerNumbers` (1 definition, 9 theorems, 1 open marker) and seven theorems in `Brockian.ZumkellerStructure`. All theorem entries are register **PROVED**, AXLE verdict **verified**, axioms exactly `{propext, Classical.choice, Quot.sound}`. Each is stated below informally and in its exact Lean form.

### 3.1 Obstructions — what cannot be Zumkeller

**σ must be even** (`Brockian.ZumkellerNumbers.zumkeller_sigma_even`). If the divisors split into two equal halves, `σ(n)` is twice a half.

```lean
theorem zumkeller_sigma_even {n : ℕ} (h : Zumkeller n) :
    Even (∑ d ∈ n.divisors, d)
```

**Every positive Zumkeller number is perfect-or-abundant** (`Brockian.ZumkellerNumbers.zumkeller_two_mul_le_sigma` — the flagship of the first module). `n` is one of its own divisors; whichever half contains it has sum `≥ n`, and that half is `σ(n)/2`.

```lean
theorem zumkeller_two_mul_le_sigma {n : ℕ} (hn : 0 < n) (h : Zumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d
```

**No prime is Zumkeller** (`Brockian.ZumkellerNumbers.not_zumkeller_prime`). Primes are deficient (`σ(p) = 1 + p < 2p`), contradicting the previous theorem.

```lean
theorem not_zumkeller_prime {p : ℕ} (hp : p.Prime) : ¬ Zumkeller p
```

**No deficient number is Zumkeller** (`Brockian.ZumkellerStructure.not_zumkeller_of_deficient`) — the quantitative contrapositive of the flagship, proved directly: a candidate half-set can neither contain `n` nor omit it.

```lean
theorem not_zumkeller_of_deficient (n : ℕ) (hn : 0 < n)
    (h : ∑ d ∈ n.divisors, d < 2 * n) : ¬ Zumkeller n
```

**No prime power is Zumkeller** (`Brockian.ZumkellerStructure.not_zumkeller_prime_pow`). Prime powers are deficient: the geometric sum `1 + p + ⋯ + p^k` is `< 2·p^k` for `p ≥ 2` (a corresponding statement is in Peng–Bhaskara Rao [2]).

```lean
theorem not_zumkeller_prime_pow (p k : ℕ) (hp : p.Prime) : ¬ Zumkeller (p ^ k)
```

**Odd σ excludes** (`Brockian.ZumkellerStructure.not_zumkeller_of_sigma_odd`) — the usable converse-side form of `zumkeller_sigma_even`.

```lean
theorem not_zumkeller_of_sigma_odd (n : ℕ) (h : Odd (∑ d ∈ n.divisors, d)) : ¬ Zumkeller n
```

**An odd Zumkeller number is never a perfect square** (`Brockian.ZumkellerStructure.odd_zumkeller_not_square`). For odd `n`, every divisor is odd, so `σ(n) ≡ d(n) (mod 2)`; a nonzero square has an odd number of divisors, forcing `σ(n)` odd — contradiction with `zumkeller_sigma_even`. This is the module's sharpest structural statement about the odd case.

```lean
theorem odd_zumkeller_not_square {n : ℕ} (hodd : Odd n) (h : Zumkeller n) : ¬ IsSquare n
```

### 3.2 Constructions and closure — what must be Zumkeller

**Every perfect number is Zumkeller** (`Brockian.ZumkellerStructure.zumkeller_of_perfect`): take `S = {n}` (classical observation; formalized here against the half-sum definition).

```lean
theorem zumkeller_of_perfect {n : ℕ} (hn : 0 < n) (h : ∑ d ∈ n.divisors, d = 2 * n) :
    Zumkeller n
```

**Closure under coprime multiplication** (`Brockian.ZumkellerStructure.zumkeller_mul_coprime`). If `n` is Zumkeller and `gcd(n, m) = 1` with `m > 0`, then `n·m` is Zumkeller: the half-set `S` for `n` inflates to `{ d·e : d ∈ S, e ∣ m }`, and multiplicativity of `σ` does the rest. This is the engine that turns the six concrete witnesses of §3.3 into infinitely many Zumkeller numbers each (a corresponding closure result is in Peng–Bhaskara Rao [2]).

```lean
theorem zumkeller_mul_coprime {n m : ℕ} (h : Zumkeller n) (hm : 0 < m)
    (hco : n.Coprime m) : Zumkeller (n * m)
```

**The definition means what it says** (`Brockian.ZumkellerStructure.zumkeller_iff_partition`): the half-sum characterization is equivalent to the equal-partition form.

```lean
theorem zumkeller_iff_partition (n : ℕ) :
    Zumkeller n ↔ ∃ S ⊆ n.divisors, ∑ d ∈ S, d = ∑ d ∈ n.divisors \ S, d
```

### 3.3 Concrete witnesses

Six explicit Zumkeller numbers, each discharged by computation (`decide`) with an explicit half-set. All six are registry entries in `Brockian.ZumkellerNumbers`:

| Registry name | n | divisors | σ(n) | witnessing half-set S | ∑S |
|---|---|---|---|---|---|
| `zumkeller_six` | 6 | {1,2,3,6} | 12 | {1, 2, 3} | 6 |
| `zumkeller_twelve` | 12 | {1,2,3,4,6,12} | 28 | {12, 2} | 14 |
| `zumkeller_twenty` | 20 | {1,2,4,5,10,20} | 42 | {20, 1} | 21 |
| `zumkeller_twentyfour` | 24 | {1,2,3,4,6,8,12,24} | 60 | {24, 6} | 30 |
| `zumkeller_twentyeight` | 28 | {1,2,4,7,14,28} | 56 | {28} | 28 |
| `zumkeller_thirty` | 30 | {1,2,3,5,6,10,15,30} | 72 | {30, 6} | 36 |

Each has the uniform shape

```lean
theorem zumkeller_six : Zumkeller 6 := by
  refine ⟨{1, 2, 3}, ?_, ?_⟩
  · decide
  · decide
```

Note 28 is perfect, so `S = {28}` alone is a half-set — the smallest possible witness, and a concrete instance of `zumkeller_of_perfect`.

---

## 4. The open marker

Per program discipline, an open question is recorded as a `def` of a `Prop` — stated, registered, and deliberately **not** proved. The registry entry `Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure` (register CONJECTURE) is, exactly:

```lean
def OddZumkellerFrom3Structure : Prop :=
  ∀ n, Odd n → Zumkeller n → 3 ∣ n
```

i.e., "every odd Zumkeller number is divisible by 3." The next section reports what the agent pipeline did to this proposition.

---

## 5. A machine-found disproof

When the harvest pipeline was pointed at the target `odd_zumkeller_div_three` — the theorem-form of the proposition above — the prover did not prove it. It **refuted** it, producing a kernel-checked counterexample.

The artifact is `aristotle/best_proofs/Brockian_ZumkellerNumbers_odd_zumkeller_div_three.lean` (also staged in `aristotle/pr_ready/`), AXLE-verified at `lean-4.32.2` (`aristotle/axle_verify.json`: `verified: true`, hash `864d12259271a394`) and axiom-clean per `aristotle/best_proofs/manifest.json` (`axiom_clean: true`). Its main theorem, exactly:

```lean
/-- **The conjecture "every odd Zumkeller number is divisible by 3" is false.**
The counterexample is `5391411025 = 5^2 * 7 * 11 * 13 * 17 * 19 * 23 * 29`. -/
theorem not_odd_zumkeller_div_three : ¬ (∀ n : ℕ, Odd n → Zumkeller n → 3 ∣ n) := by
  intro h
  exact not_three_dvd_5391411025 (h 5391411025 odd_5391411025 zumkeller_5391411025)
```

The counterexample `N = 5391411025 = 5²·7·11·13·17·19·23·29` is odd, coprime to 3, and Zumkeller: the file proves `σ(N) = 10799308800` from multiplicativity of `σ`, and exhibits the six divisors `{1, 23, 391, 135575, 8107385, 5391411025}` summing to `5399654400 = σ(N)/2`, all discharged in-kernel. (Classical background: `5391411025` appears in the literature on abundant numbers coprime to small primes, cf. OEIS **A047802**; the *Zumkeller* property of this particular number, with an explicit half-set, is what the machine proof certifies here.)

Provenance caveats, stated plainly:

- `not_odd_zumkeller_div_three` is a **harvest artifact**, AXLE-verified but **not yet an entry in `registry/theorems.json`**; the harvest ledger (`aristotle/harvest_ledger.json`) records the run under target `Brockian.ZumkellerNumbers.odd_zumkeller_div_three` with verdict PROVED — the thing proved being the *negation* of the target.
- Consequently the registry's CONJECTURE entry `OddZumkellerFrom3Structure` (§4) is, as literally stated, **resolved negatively** by this artifact. The registry has not yet been updated to reflect the refutation; until it is, the honest status line is: *statement refuted by an AXLE-verified counterexample pending registry integration*. If a nontrivial structural question survives in this direction, it must be a restatement (e.g., excluding this construction family), and no such restatement is currently registered.

This is, to our knowledge, the cluster's first **banked disproof**: the pipeline treated "prove φ" and "prove ¬φ" symmetrically and returned the side that is true.

---

## 6. Verification methodology

The epistemic frame follows the program's standing discipline — *a picture cannot outrun its proof*, applied here to prose: every mathematical claim in this note is (a) a named registry entry, (b) an AXLE-verified harvest artifact identified as such (§5 only), (c) explicitly labeled classical background with citation, or (d) explicitly labeled open. See `docs/atlas/METHOD.md` for the program-wide separation of correctness, statement fidelity, and reactivation, and [1] for the underlying framework.

**Pipeline.** Formalization was AI-assisted end to end: statements were drafted and proved by the Aristotle prover fleet (multiple accounts, candidate proofs per target), harvested and minimized by the repository's agent pipeline (`aristotle/`), and the chosen artifacts merged into the `Brockian/` modules. Christopher Brock directs the program, selects targets, and signs off on statements; the AI systems wrote the Lean proofs. This division of labor is reported as a fact, not hidden.

**Kernel check.** Every declaration in both modules was independently re-elaborated and kernel-checked by AXLE (Axiom's cloud checker) at toolchain `lean-4.32.2`. Both module attestations report `module_verified: true` and a per-declaration verdict of `verified` — 11/11 declarations in `ZumkellerNumbers.json`, 7/7 in `ZumkellerStructure.json`.

**Axiom audit.** Each proof's axiom footprint was extracted and checked against the allowlist: every theorem here depends on exactly `{propext, Classical.choice, Quot.sound}` — the standard classical trio — with `axioms_ok: true`. No `sorry`, no `native_decide`, no bespoke axioms.

**Registry provenance.** `registry/theorems.json` is generated from the attestations and is the source of truth; `REGISTRY.md` mirrors it. Two posture flags are reported rather than smoothed over: (i) `lake_build: "pending"` for all 18 entries — AXLE attestation is the verification that exists today; a local pinned-toolchain `lake build` has not yet been run for these modules; (ii) the eleven `ZumkellerNumbers` entries carry the registry's `quarantine: true` flag from their frontier-swarm ingest run, while the seven `ZumkellerStructure` entries do not.

---

## 7. Honest limitations — what is NOT proved

- **No density or counting results.** Nothing here bounds how many Zumkeller numbers exist below `x`, their density, or the density of odd ones. The registry's own provenance note marks Zumkeller infinitude-with-density and odd-density questions OPEN. (Infinitude itself follows trivially from `zumkeller_six` + `zumkeller_mul_coprime` with coprime `m`, but no asymptotic statement is registered, and we claim none.)
- **The odd-Zumkeller frontier is essentially untouched.** We prove one obstruction (`odd_zumkeller_not_square`) and bank one disproof (§5). We do not characterize odd Zumkeller numbers, prove anything about their minimal element (945 is classical background, not a registered theorem), or touch the odd-perfect neighborhood beyond analogy.
- **Abundance is not proved sufficient — because it isn't.** The gap between "perfect-or-abundant" (necessary, proved) and "Zumkeller" is where the real difficulty lives; no registered result narrows it.
- **Half of the classical Peng–Bhaskara Rao theory is not formalized here.** In particular, the source file `Brockian/ZumkellerStructure.lean` contains two further theorems (`zumkeller_two_pow_mul_prime`, on `2^k·p` for odd primes `p < 2^{k+1}`, and `sigma_odd_iff_square_or_two_mul_square`, the Euler-style parity dichotomy for `σ`) that are **not** among the seven attested declarations in `registry/attestations/ZumkellerStructure.json` and are **not** registry entries. They are covered only by the attestation's module-level compile; this note therefore makes **no claim** about them, and they are excluded from every count above.
- **AXLE attestation is not a local `lake build`.** Per §6, the pinned-toolchain local build is pending across the corpus; the claims here are exactly as strong as the AXLE cloud check, no stronger.

---

## 8. Open targets

- **`OddZumkellerFrom3Structure`** — queued as the cluster's conjecture entry; per §5, its literal statement is refuted by an AXLE-verified counterexample awaiting registry integration. The live open work is: (i) integrate `not_odd_zumkeller_div_three` and its counterexample chain into the registry as PROVED entries; (ii) formulate and register whatever *survives* — e.g., structural constraints on odd Zumkeller numbers coprime to 3 (the counterexample has eight prime factors; is that forced to be large?). No such successor statement is currently registered, so it is listed here as open, not claimed.
- **Odd-Zumkeller structure beyond non-squareness** — combine `odd_zumkeller_not_square` with `sigma`-parity machinery toward registered constraints on the square part and prime signature of odd Zumkeller numbers.
- **Registering the `2^k·p` family** — promote `zumkeller_two_pow_mul_prime` from in-source to attested-and-registered, which would give the corpus its first infinite *even* family with an explicit construction.

---

## References

[1] C. Brock, *Mathematics in the Age of Mechanical Reproduction: Trace, cult, and what verification cannot certify*, 2026. (Program epistemic framework; see also `docs/atlas/METHOD.md`.)

[2] Y. Peng, K. P. S. Bhaskara Rao, *On Zumkeller numbers*, Journal of Number Theory 133 (2013), 1135–1155. (Classical source for the informal theory: necessary conditions, prime-power exclusion, coprime closure, `2^k·p` families, and the odd case including 945.)

[3] OEIS Foundation, *A083207: Zumkeller numbers* and *A047802: smallest abundant number not divisible by any of the first n primes*. (Classical background for §1 and §5.)

---

*Repository pointers: `Brockian/ZumkellerNumbers.lean` · `Brockian/ZumkellerStructure.lean` · `registry/theorems.json` · `registry/attestations/Zumkeller{Numbers,Structure}.json` · `aristotle/best_proofs/Brockian_ZumkellerNumbers_odd_zumkeller_div_three.lean`.*
