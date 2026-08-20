# Guiding the Brockian program with Terry Tao's blog

*A working analysis of what to adopt, how to raise quality, and where we are genuinely different.
Grounded in a scrape of the full blog index (918 posts, 2007–2026; see
`docs/reference/tao-blog-index.md`) and close reads of the load-bearing posts. Honest throughout:
Tao produces new theorems; our contribution is verification + formalization + pedagogy, not new
frontier mathematics.*

---

## 0. Why Tao is the right lodestar

His blog is the reference corpus for exactly the mathematics our program touches: **sieve theory,
prime gaps, the parity problem, the singular series, additive combinatorics** — and, recently,
**Lean formalization** and **coding-agent visualizers**. He ran **Polymath8** (bounded gaps between
primes, after Zhang/Maynard), whose machinery — *admissible tuples* and the *Hardy–Littlewood
singular series* — is the same object our constellation-sieve counts. He is also scrupulous about
what is proved vs. heuristic vs. open, which is the discipline our register system encodes.

---

## 1. The single most important lesson — the **parity problem** is our exact ceiling

Tao, *Open question: the parity problem in sieve theory* (2007-06-05), and *A general parity problem
obstruction* (2014):

> "If A is a set whose elements are all products of an odd number of primes (or all products of an
> even number of primes), then sieve theory is unable to provide non-trivial lower bounds on the
> size of A."

The obstruction is orthogonality to the **Liouville function** λ: divisor-sum / smooth-weight
methods cannot see the parity of Ω(n), so they cannot separate primes from almost-primes — the
famous factor-of-2 barrier, and the reason twin/Sophie-Germain/Polignac resist pure sieves.

**What this means for us, precisely.** Our constellation-sieve is a *sieve-type exact count* of
admissible residues on the wheel ℤ/n. It therefore lives **entirely on the upper-bound / structural
side of the parity barrier** — which is exactly why our honest-scope disclaimer ("not a proof of
infinitude") is not just caution but a *theorem-level* fact. Action items:

- **Cite parity as the named ceiling** in the paper and lab, replacing the vaguer "we don't claim
  infinitude" with "sieve confinement is parity-bounded (Tao 2007/2014); crossing to infinitude
  requires Type-II/bilinear input our corpus does not contain."
- **A genuine formalization target:** state the parity obstruction itself in Lean —
  λ ⟂ (divisor sums), i.e. the Liouville function has negligible correlation with smooth residue
  weights. Even the finite/statement-level version would be a real contribution; Mathlib has no
  parity-problem infrastructure.

---

## 2. SUPPLEMENT — techniques and objects to adopt

| From Tao | What it is | How it plugs into our corpus |
|---|---|---|
| **Singular series 𝔖(H)** (Polymath8, Maynard posts) | `𝔖(H) = ∏_p (1 − ν_p/p)(1−1/p)^{−k}` | Our `∏(p − ν_p)` **is** the un-normalized singular series. Rename/relate it explicitly, and connect our verified `SingularSeriesConvergence.singular_series_pos'` to the Hardy–Littlewood constant. Instant expert legibility. |
| **Admissible tuples** | offset sets avoiding a full residue class mod every p | Our `admissibleU` / wheel counts are the admissibility predicate. State the GPY/Maynard admissibility lemmas as Lean targets. |
| **Maynard–Tao multidimensional sieve** | the weights behind bounded gaps | The frontier bridge: our exact wheel counts feed the sieve weights. A formalized fragment would be novel. |
| **Cramér random model** (*Gilbreath's conjecture…*, 2026-07-11) | probabilistic heuristic for prime statistics | We list **Gilbreath as open**; Tao just gave a Cramér model + deterministic analysis + a visualizer. Link our open node to his model; formalize the deterministic (finite) portion. |
| **Structure vs. randomness** dichotomy | his organizing frame for the primes | Perfect frame for our program: **structure** = exact confinement counts; **randomness** = the parity barrier / Cramér model. Adopt it as the paper's spine. |

---

## 3. BETTER GUIDED — methodology & exposition standard

- **The 254A/246B notes are the gold standard** (141 course-note posts). Their shape —
  *motivation → precise statement → informal discussion → rigorous proof → remarks/open problems* —
  should be the template for `brockian-verified-core.tex` and every lab explainer. We currently
  state-then-prove; add the motivation and informal-discussion layers.
- **The Lean companion model** (*A Lean companion to Analysis I*, 2025-05-31). Tao pairs each
  textbook definition/theorem with a formal Lean statement, **deprecates hand-built types once a
  Mathlib equivalent exists**, and is candid that not all exercises are verified ("I would be
  interested in having volunteers 'playtest'"). Two lessons: (a) our prose ↔ Lean ↔ certificate
  pairing (the ProofDrawer) is the right instinct — make it the primary reading mode, not an
  appendix; (b) prefer Mathlib primitives over bespoke constructions wherever we can.
- **Honesty as default, not disclaimer.** Tao never lets a conditional or heuristic read as a
  theorem. Our registers (PROVED / COMPUTATION / CONDITIONAL / CONJECTURE) already encode this; his
  practice is external validation that the discipline *is* the standard, and a mandate to keep the
  RH-scaffold / Goldbach-schema strictly CONDITIONAL forever.

---

## 4. DIFFERENTIATE — what is genuinely ours

Be precise about the edge; don't overclaim novelty of the mathematics.

1. **Verification at scale, with certificates.** Every theorem is independently kernel-checked by
   **AXLE @ lean-4.32.0**, axiom-clean, registry-backed, with a **public clickable proof drawer +
   certificate**. Tao's Lean companion is nascent and human-curated; nobody presents a *verified,
   inspectable* number-theory corpus at this scale. **This is the moat.**
2. **The honesty firewall as a first-class artifact** — registers that *reject* overclaims, an
   explicit open-conjecture ledger. That the machinery refuses to mark anything "solved" is itself
   the differentiator.
3. **Formalized sieve infrastructure.** Mathlib is thin on analytic sieve theory. The singular
   series, admissibility, the parity-obstruction statement, GPY/Maynard weights — formalizing even
   fragments makes us **the verified-sieve-theory reference**. This is where Tao's blog points and
   *no one has built it.*
4. **Proof + certificate + interactive visualization in one object.** Tao builds viz apps *and*
   Lean companions separately; we fuse them (residue-wheel lab ↔ proof-tree DAG ↔ ProofDrawer).

**Where we are honestly weaker (say so):** our "frontier" modules are formalizations of *known or
elementary* facts, not new theorems. The constellation five-point spectrum is a *verified
repackaging* of admissibility via graph spectra — new as **formalization/pedagogy**, not as
mathematics. Position it that way everywhere.

---

## 5. BETTER QUALITY — the coding-agent lesson, applied to our labs

*Old and new apps via modern coding agents* (2026-07-11): Tao "vibe-codes" visualizers, treats them
as **non-mission-critical secondary aids**, stresses that **domain expertise is what verifies
them**, and accepts subtle bugs *because the viz is not foundational to the argument*.

This both **validates** our Lovable-labs approach and sets the quality bar: the visualization is
illustrative; **the AXLE certificate in the ProofDrawer is the truth.** Our lab already enforces
this (the wheel/spectrum are decorative; the proof tree opens real verified source). Keep that
separation explicit — never let a pretty animation stand in for a certificate.

---

## 6. Prioritized actions

1. **Parity ceiling** — add the named parity-problem citation to the paper §scope, the lab "Scope,
   honestly" callout, and the ledger. *(low effort, high credibility)*
2. **Name the singular series** — relate `∏(p−ν_p)` and `singular_series_pos'` to 𝔖(H) in prose +
   registry provenance. *(low effort, high legibility)*
3. **Formalize a parity/sieve fragment** — the Liouville-orthogonality statement, or an admissibility
   lemma, as a fresh AXLE-verified module. *(the real research-flavored contribution)*
4. **Gilbreath** — link our open node to Tao's Cramér model; consider formalizing its deterministic
   finite core. *(overlaps our tracked conjectures)*
5. **Exposition pass** — restructure the paper and lab explainers to the 254A shape
   (motivation → statement → discussion → proof → open). *(quality)*
6. **Reference asset** — keep `docs/reference/tao-blog-index.md` current as a guidance map.

*Reminder, as always: everything here remains finite, verified structure. None of it is a proof of
twin-prime infinitude or any open conjecture — and the parity problem is the precise reason it
cannot be.*
