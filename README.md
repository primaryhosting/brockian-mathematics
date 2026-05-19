# Verified Lean 4 Library: Fibonacci Fusion Algebra & Penrose Tiling Spectral Bounds

A Lean 4 formalization of the algebraic data underlying Fibonacci anyon models, Penrose tiling spectral theory, and D5 representation theory. All proofs are kernel-checked against Mathlib.

## What's here

This library provides verified Lean 4 proofs in several areas. Some results overlap with existing Mathlib content (golden ratio identities, Fibonacci numbers); others appear to be new formalizations (transition-count kernels on ZMod, Penrose tiling L2 operator bounds, explicit D5 representation with trace computation).

**We welcome feedback on what is and isn't already in Mathlib.** If you identify overlap, please open an issue — we'd like to contribute the genuinely new parts upstream.

## Contents

### Transition-count kernel on ZMod 5 (likely new)

A labeled dynamical system on Z/5Z with step `r -> r + 2`, domain `{1, 2, 4}`, and labels by quadratic residue character produces the transition matrix:

```
TK = [[1, 1],
      [1, 0]]
```

This is the Fibonacci matrix. The construction is elementary (three transitions, two bins), and we don't claim deep significance — many binary-classification systems produce this matrix (de Bruijn graphs, substitution tilings, etc.). But the formalization of the *counting framework* (labeled systems, transition kernels, row/column/total sum theorems) may be useful infrastructure.

| Lean Name | Statement |
|-----------|-----------|
| `Twin.TK'_table` | TK(0,0)=1, TK(0,1)=1, TK(1,0)=1, TK(1,1)=0 |
| `Twin.TK'_total` | sum TK(i,j) = 3 |
| `Kernel.row_sum` | Row sums equal domain count per label |
| `Kernel.col_sum` | Column sums equal codomain count per label |
| `Count.good_start_law` | \|GoodStarts(Gamma)\| = q - \|Gamma\| |
| `Count.card_badStarts` | \|BadStarts\| = \|Gamma\| (negation injective) |

### Golden ratio & Fibonacci (partially overlaps Mathlib)

Standard identities, formalized with the specific matrix M = [[1,1],[1,0]]:

| Lean Name | Statement | In Mathlib? |
|-----------|-----------|-------------|
| `phi_squared` | phi^2 = phi + 1 | Likely yes |
| `phi_sum_conjugate` | phi + psi = 1 | Likely yes |
| `phi_product_conjugate` | phi * psi = -1 | Likely yes |
| `phi_is_eigenvalue` | M * v = phi * v (explicit eigenvector) | Possibly no |
| `psi_is_eigenvalue` | M * w = psi * w | Possibly no |
| `M_charpoly` | det(xI - M) = x^2 - x - 1 | Possibly no |
| `binet_formula` | F(n) = (phi^n - psi^n) / sqrt(5) | Likely yes |
| `M_pow_fib` | M^n encodes Fibonacci numbers | Possibly no |
| `spectral_gap_identity` | phi - 1/phi = 1 | Trivial from phi^2 = phi + 1 |
| `psi_abs_lt_one` | \|psi\| < 1 | Likely yes |

### D5 dihedral group (partially overlaps Mathlib)

Explicit construction of D5 as a 10-element type with full multiplication table, plus a 2D matrix representation:

| Lean Name | Statement | In Mathlib? |
|-----------|-----------|-------------|
| `D5.card_eq_10` | \|D5\| = 10 | Yes (via DihedralGroup) |
| `D5.mul_assoc` | Associativity (all 1000 triples) | Yes |
| `r_pow_five` | r^5 = e | Yes |
| `s_squared` | s^2 = e | Yes |
| `rho_mul` | rho(g*h) = rho(g)*rho(h) | Possibly no (explicit 2x2 matrices) |
| `trace_rotation_eq_golden` | tr(rho(r)) = phi - 1 = 2*cos(2*pi/5) | Likely no |
| `cos_2pi_5` | cos(2*pi/5) = (sqrt(5)-1)/4 | Possibly yes |
| `charInner_golden` | <chi_golden, chi_golden> = 1 (irreducibility) | Likely no |

### Penrose tiling spectral theory (likely new)

L2 operator theory on a Penrose tiling vertex graph, defined via cut-and-project from Z^5. This appears to be new formalization territory:

| Lean Name | Statement |
|-----------|-----------|
| `degree_bound` | Every Penrose vertex has degree <= 10 |
| `adjacent_symm` | Adjacency is symmetric |
| `adjacent_loopless` | No self-loops |
| `A_raw_bound` | \|\|Af\|\|_{l2} <= 10 * \|\|f\|\|_{l2} |
| `D_raw_norm_bound` | \|\|Df\|\| <= 10 * \|\|f\|\| |
| `Delta_bounded` | \|\|Delta f\|\| <= 20 * \|\|f\|\| (Laplacian bounded) |
| `memLp_A_raw` | Adjacency preserves L2 membership |

### Ray structure on ZMod 5 (likely new)

Partition of (Z/5Z)* into quadratic residues {1,4} and non-residues {2,3}:

| Lean Name | Statement |
|-----------|-----------|
| `ray_partition` | Every nonzero residue is in Ray0 or Ray1 |
| `ray_disjoint` | Rays are disjoint |
| `neg_preserves_ray0` | Negation preserves ray classification |
| `twin_admissible` | Twin-admissible residues are {1, 2, 4} |

## Verification environment

- **Lean 4** v4.24.0
- **Mathlib** commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (v4.14.0)
- **Proof generation**: Aristotle (Harmonic), a Lean 4 automated theorem prover — [aristotle.harmonic.fun](https://aristotle.harmonic.fun)
- 171 independent verification projects
- 64,538 total lines of Lean 4 source

## File structure

```
Brockian/
  PerfectEdition.lean   -- Complete framework: rays, D5, kernel, golden ratio, eigenvalues (50 thm, 0 sorry)
  FullFramework.lean     -- Extended version with conjectures (76 thm, 1 sorry)
  PenroseTiling.lean     -- D5 Penrose tiling, L2 spectral theory (45 thm, 1 sorry)
  CoreFramework.lean     -- Foundations: rays, counting, kernel basics (24 thm, 0 sorry)
  DihedralSeed.lean      -- D5 geometric embedding, rotation/reflection (8 thm, 0 sorry)
  MarkovKernel.lean      -- Transition kernel computation (12 thm, 0 sorry)
catalog/
  brockian_theorem_catalog.json  -- Full catalog of 2,028 named declarations across all projects
paper/
  brockian-fibonacci-anyon.tex   -- Draft paper (needs revision before submission)
  brockian-fibonacci-anyon.pdf   -- Compiled PDF
```

## Building

```bash
# Requires Lean 4 and elan
lake build
```

Note: The individual `.lean` files are self-contained (each imports Mathlib directly). They were generated by Aristotle as independent projects. A unified lakefile that builds them as a coherent library is a planned next step.

## Status and known issues

- The theorem catalog includes helper lemmas, decidability instances, and definitions alongside substantive theorems. The headline "2,028 theorems" overstates the number of *named mathematical results*; a more honest count of non-trivial theorems is probably in the range of 200-400.
- Some Lean names use project-specific prefixes (e.g., `Brock.`, `HarmonicArch.`, `Golden.`) that should be unified.
- The `FullFramework.lean` file has 1 sorry in a helper lemma. The `PenroseTiling.lean` file has 1 sorry in an L2 construction.
- Self-referential naming (e.g., `brockian_spectral_gap` for the identity phi - 1/phi = 1) will be revised in a future cleanup.

## Contributing

Issues and PRs welcome. In particular:

1. **Mathlib overlap audit**: Which of these results already exist in Mathlib? We want to identify the genuine delta.
2. **Upstream candidates**: Which formalizations would be useful additions to Mathlib?
3. **Lean style**: The files were generated by an AI prover and don't follow Mathlib style conventions. Help refactoring is appreciated.
4. **Mathematical errors**: If any theorem statement is wrong or misleading, please flag it.

## License

MIT License. Copyright 2026 Christopher Brock.

## Acknowledgments

Proofs generated and verified using [Aristotle](https://aristotle.harmonic.fun) by Harmonic. Built on [Mathlib](https://github.com/leanprover-community/mathlib4) by the Lean community.
