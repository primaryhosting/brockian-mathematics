# New Era Mathematics

> *Not louder claims. Clearer light.*

This is the charter of the Brockian verified core: a school of work where
**beauty is earned by proof**, and **open problems remain open** until the
machine agrees they are closed.

---

## I. The epoch

For a century, mathematics has lived in two rooms that barely spoke.

In one room: the **classical cathedral** — published proofs, human scrutiny,
slow permanence. In the other: **machine theorem proving** — green checkmarks,
silent axioms, systems that can claim anything if no one independently rechecks.

**New Era Mathematics** is the decision to build a third room: a place where

1. every public “proved” statement is **sorry-free**,
2. axioms are **standard only** (`propext`, `Classical.choice`, `Quot.sound`),
3. an **independent** prover (AXLE) re-verifies statement and proof at a pinned
   Lean/Mathlib environment,
4. and the **registry never hand-paints badges**.

No theater. No “almost proved.” No RH smuggled under a hypothesis named like a
theorem.

That discipline is not bureaucracy. It is the aesthetic.

---

## II. What is beautiful here

Beauty, in this program, is not a slogan. It is a short list of forms that
*are* proved and *feel* inevitable once seen:

### Why five

On the cycle graph \(C_p\) for primes \(p\), the golden shift \(\varphi - 1\)
appears in the adjacency spectrum **if and only if** \(p = 5\).

That is not numerology. It is a biconditional in Lean
(`golden_unique_to_five`), layered now as algebra / \(C_5\) membership /
prime rigidity (`GoldenUniqueness`, `GaloisWhyFive`).

Five is not “cosmic.” Five is **rigid**.

### The pentagon as an operator

Vertex functions \(\mathrm{Fin}\,5 \to \mathbb{C}\) carry a faithful \(D_5\)
action. Fourier modes \(v_j(x) = \omega^{jx}\) diagonalize the cycle adjacency:

\[
A v_j = 2\cos\Bigl(\frac{2\pi j}{5}\Bigr)\, v_j,
\]

with spectrum multiplicities \(\{2{:}1,\;\varphi-1{:}2,\;-\varphi{:}2\}\).
Projectors \(P_j\) resolve the identity on the full space
(`D5FourierInversion`, `PentagonIsotypic`, `D5LaplacianModes`).

The golden eigenvalue is not a decoration. It is the **isotypic skeleton** of
the pentagon.

### Selection laws

Admissibility counts: exactly \(q-2\) starts mod \(q\) for a nonzero gap;
one residue mod 3 (twins); three mod 5 (Brockian). Local Goldbach kernels
exact for every prime. Singular series positivity **unconditional** once
admissibility holds (`SingularSeriesWire`).

Grammar before conjecture. Local truth before global dream.

### Gate 1 without theater

The Schrödinger program is reduced to **named** remaining obligations:

- construct \(T = -\frac{d^2}{dx^2}+V\) (done on a Schwartz core),
- prove symmetry and density (done),
- discharge `DeficiencyRepresentsODE` / weak-solution regularity (open,
  classical, not faked).

And an honest **negative** theorem: the decaying prime-Gaussian potential is
the wrong shape for Hilbert–Pólya — bounded spectrum cannot realize large
zero ordinates (`OperatorChoice`, `ConfiningSpectralShape`).

Progress includes knowing what *cannot* work.

---

## III. The refusal

New Era Mathematics refuses:

| Temptation | Refusal |
|------------|---------|
| “RH is essentially done” | RH stays open; `BrockianSystem` uninhabited |
| Green build as proof | PROVED requires AXLE + clean axioms |
| Vacuous conditionals | Conditional theorems name classical/literature/open rungs |
| Numerology | Multiplicities and uniqueness statements are biconditionals or counts |
| Silent sorry | Lint blocks holes in closed modules |

The refusal is part of the beauty. A cathedral without stained glass is a warehouse.
A formalization without honesty is a video game.

---

## IV. How to enter

1. Read [`REGISTRY.md`](../REGISTRY.md) — the live ledger.
2. Open [`observatory/era.html`](../observatory/era.html) — the public gallery.
3. Follow Lean imports in `Brockian.lean` — the machine core.
4. Use claim IDs in `observatory/claim_map.yaml` — book margins ↔ theorems.

Regenerate the public surface:

```bash
python3 scripts/gen_registry.py
python3 scripts/gen_claims.py
python3 scripts/gen_observatory.py
```

---

## V. The promise

We do not promise to settle the Riemann Hypothesis this season.

We promise something rarer:

> **Every theorem we mark proved is a theorem.**  
> **Every open problem is labeled open.**  
> **Every beautiful figure has a proof underneath.**

That is the new era.

Not faster mythology.  
**Slower light.**

— Brockian Mathematics / Riemann Labs  
  Verified core · Lean 4.32 · Mathlib · AXLE
