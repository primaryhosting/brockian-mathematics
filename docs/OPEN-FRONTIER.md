# The Open Frontier — formalized partial progress on unsolved problems

*This is the honest ledger of the frontier lane: machine-verified partial results toward
genuinely open problems, with the open boundary drawn precisely. Every theorem cited here
resolves to a green entry in `registry/theorems.json`; every "OPEN" line is a statement we
do **not** prove. Nothing here claims to solve a famous conjecture — the value is a sharply
drawn, independently AXLE-verified frontier.*

## How to read this

- **PROVED** — an unconditional theorem in the verified core (AXLE @ lean-4.32.0, axioms ⊆
  {propext, Classical.choice, Quot.sound}, no `sorry`/`native_decide`).
- **OPEN** — a precisely-stated claim we deliberately leave unproven; where possible we
  *characterize* the open set rather than gesture at it.
- Registered conjectures live in the CONJECTURE register as unproven `def`s, never theorems.

---

## Erdős–Straus conjecture (open since 1948)

**Claim.** For every integer n ≥ 2, `4/n = 1/x + 1/y + 1/z` in positive integers.
Module: `Brockian.ErdosStraus`, `Brockian.ErdosStrausResidues`.

**PROVED (unconditional):**
- Even n, and n divisible by 3, 5, or 7 — explicit verified Egyptian-fraction identities
  (`erdosStraus_even`, `erdosStraus_dvd_three`, `erdosStraus_dvd_five`, `erdosStraus_dvd_seven`).
- Residue classes n ≡ 3 (mod 4) and n ≡ 2 (mod 3) (`erdosStraus_mod4_three`, `erdosStraus_mod3_two`).
- **Multiplicativity** — solvability is inherited by multiples (`erdosStraus_of_dvd`), hence the
  whole conjecture **reduces to primes** (`erdosStraus_of_prime_case`).
- Consolidated coverage (`erdosStraus_covered`).

**OPEN, characterized sharply.** Any counterexample n must be odd, coprime to 3, and
≡ 1 (mod 4) — i.e. **n ≡ 1 (mod 12)**, equivalently n%24 ∈ {1, 13}
(`erdosStraus_open_reduces`, `erdosStraus_open_reduces_mod12`, `erdosStraus_open_frontier_mod24`).
This pins failure to the classes feeding the hard primes p ≡ 1, 121, 169, 289, 361, 529 (mod 840).
A computational search over many moduli found **no** linear parametric identity closing those
classes — consistent with the known theory that they are genuinely open. The full conjecture
`ErdosStrausConjecture` is recorded as an unproven `def`.

---

## Odd perfect numbers (open ~2000 years)

**Claim.** No odd perfect number exists (existence unknown). A perfect number satisfies σ(n) = 2n.
Module: `Brockian.OddPerfectConstraints`.

**PROVED (necessary conditions — "if one exists, then…"):**
- An odd perfect number is **not a perfect square** (`oddPerfect_not_square`): σ of an odd square is
  odd, but σ(n) = 2n is even.
- An odd perfect number is **not a prime power** (`oddPerfect_not_prime_pow`).
- Sanity: positive, odd, > 1.

**OPEN.** Existence itself; Euler's form n = p^k·m² with p ≡ k ≡ 1 (mod 4) (attempted, not yet
proved — a genuine formalization target for a later cycle).

---

## Lehmer's totient problem (open since 1932)

**Claim.** `φ(n) ∣ (n − 1)` implies n prime. Module: `Brockian.LehmerTotient`.
A "Lehmer number" is a composite n with φ(n) ∣ (n − 1); none are known.

**PROVED (necessary conditions on a hypothetical counterexample):**
- A Lehmer number is **odd** (`lehmer_odd`): φ(n) is even but n − 1 would be odd.
- A Lehmer number is **squarefree** (`lehmer_squarefree`, flagship): p² ∣ n gives p ∣ φ(n) ∣ (n−1)
  while p ∣ n, forcing p ∣ 1.
- A Lehmer number has **≥ 3 distinct prime factors** (`lehmer_three_primes`): the p·q case reduces to
  `ab ∣ (a+b)` with a, b ≥ 2, a ≠ b — impossible.

**OPEN.** Existence of any Lehmer number (equivalently, whether the implication holds).

---

## Collatz (3n+1) conjecture (open)

**Claim.** Every positive integer reaches 1 under n ↦ (n/2 if even, else 3n+1).
Module: `Brockian.CollatzPartial`. `CollatzConjecture` is an unproven `def` (CONJECTURE register).

**PROVED (unconditional partial results):**
- The trivial cycle 1 → 4 → 2 → 1 (`trivial_cycle`).
- **Powers of two reach 1** (`reaches1_pow_two`), via `collatz(2n) = n` (`collatz_two_mul`).
- Descent by halving: `Reaches1 n → Reaches1 (2^k · n)` (`reaches1_two_mul`, `reaches1_mul_pow_two`).
- **Terras-style descent** (`descent_mod4_one`): every n ≡ 1 (mod 4) with n > 1 reaches a value
  strictly below n in 3 steps (12m+4 → 6m+2 → 3m+1 < 4m+1).

**OPEN.** The conjecture itself; the absence of any nontrivial cycle; convergence of a general n.

---

## Sierpiński numbers (problem open since 1960)

**Claim.** Is 78557 the *smallest* Sierpiński number (odd k with k·2ⁿ+1 composite for all n ≥ 1)?
Module: `Brockian.SierpinskiCovering`. `SierpinskiProblem` is an unproven `def`.

**PROVED (a concrete verified membership):**
- **78557 IS a Sierpiński number** (`sierpinski_78557`): for every n ≥ 1, 78557·2ⁿ+1 is composite —
  proved via the covering set {3,5,7,13,19,37,73}. Supporting: `two_pow_periodic`
  (2ⁿ ≡ 2^(n mod 36) mod p, since 2³⁶ ≡ 1 mod each p), `covering_table` (all 36 residues covered,
  by `decide`), `composite_of` (divisibility transfer + primality exclusion).

**OPEN.** Whether 78557 is the *smallest* such k (the remaining candidates below it are unresolved).
This is a concrete verified membership in an open problem's exceptional set — not a resolution.

---

## Riesel numbers (problem open since 1956)

**Claim.** Is 509203 the *smallest* Riesel number (odd k with k·2ⁿ−1 composite for all n ≥ 1)?
Module: `Brockian.RieselCovering`. `RieselProblem` is an unproven `def`.

**PROVED (concrete verified membership):**
- **509203 IS a Riesel number** (`riesel_509203`): for every n ≥ 1, 509203·2ⁿ−1 is composite —
  via the covering set {3,5,7,13,17,241} (modulus 24). Mirror of the Sierpiński proof applied to
  the −1 family: `two_pow_periodic`, `covering_table`, `composite_of`.

**OPEN.** Whether 509203 is the *smallest* such k. A concrete verified membership, not a resolution.

---

## Amicable numbers (infinitude open)

**Claim.** Are there infinitely many amicable pairs (m ≠ n with s(m)=n, s(n)=m, where s is the
aliquot sum)? Module: `Brockian.AmicableNumbers`. `AmicableInfinitude` is an unproven `def`.

**PROVED (concrete verified instances + aliquot dynamics):**
- **(220, 284)** (`amicable_220_284`, Thābit ibn Qurra), **(1184, 1210)** (`amicable_1184_1210`,
  Paganini 1866), **(2620, 2924)** (`amicable_2620_2924`, Euler) — each verified by kernel
  computation of the aliquot sums.
- Aliquot dynamics: a perfect number is a fixed point of the aliquot map
  (`perfect_iff_aliquot_fixed`); amicability is symmetric (`amicable_symm`); an amicable number is
  not perfect (`amicable_not_perfect`) — a genuine 2-cycle is not a fixed point.

**OPEN.** Whether infinitely many amicable pairs exist.

---

## Giuga numbers (odd-Giuga existence open)

**Claim.** Does an *odd* Giuga number exist? (A Giuga number is a composite n > 1 with p ∣ (n/p − 1)
for every prime p ∣ n.) Open — exactly parallel to the odd perfect number problem.
Module: `Brockian.GiugaNumbers`. `OddGiugaExists` is an unproven `def`.

**PROVED:**
- **30 and 858 are Giuga numbers** (`giuga_30`, `giuga_858`) — concrete verified instances.
- **Every Giuga number is squarefree** (`giugaNumber_squarefree`): if p² ∣ n then p ∣ (n/p) and
  p ∣ (n/p − 1), forcing p ∣ 1.

**OPEN.** Whether any odd Giuga number exists.

---

## Carmichael numbers / Korselt's criterion (three-prime infinitude open)

**Claim.** Are there infinitely many Carmichael numbers with *exactly three* prime factors?
(*General* Carmichael infinitude is a **theorem** — Alford–Granville–Pomerance 1994 — not open.)
Module: `Brockian.CarmichaelKorselt`. `ThreePrimeCarmichaelInfinitude` is an unproven `def`.

**PROVED (concrete + structural):**
- **561, 1105, 1729 are Carmichael numbers** (`korselt_561`, `korselt_1105`, `korselt_1729`) via
  Korselt's criterion (squarefree + (p−1)∣(n−1) for all p∣n). 1729 is the Hardy–Ramanujan taxicab.
- **Every Carmichael number is odd** (`korselt_odd`).

**OPEN.** Whether infinitely many Carmichael numbers have exactly three prime factors (a genuine
refinement of a solved problem — the frontier marks only what is actually open).

---

## The discipline

The frontier lane never emits a solved famous conjecture. It emits four honest kinds of output:
unconditional partial results, conditional reductions (named-hypothesis, CONDITIONAL register),
refutation certificates, and precisely-stated open conjectures. Over many cycles this builds a
machine-checked map of *where the hard part actually lives* — which is itself a real contribution.
Regenerate and re-check: `python3 scripts/gen_registry.py && python3 scripts/verify_firewall.py`.
