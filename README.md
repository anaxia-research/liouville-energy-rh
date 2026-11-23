# Proof of the Riemann and Generalized Riemann Hypotheses

**DOI:** assigned by Zenodo at release v5.0.0 (see below)

**Deep Bhattacharjee**\* and **Ushashi Bhattacharya**

**Deep Bhattacharjee.** Formerly, Electro-Gravitational Space Propulsion
Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India; Formerly, University of
Calcutta (Heramba Chandra College), 23/49 Gariahat Road, Golpark, Kolkata
700029, West Bengal, India.
Email: d.bhattacharjee@erl-forschung.de, itsdeep@live.com, egspl@proton.me.
ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X).

**Ushashi Bhattacharya.** Formerly, National Taiwan University, Taipei 106319,
Taiwan. Email: rai.bhattacharya.in@gmail.com.
ORCID [0009-0002-2254-3914](https://orcid.org/0009-0002-2254-3914).

\*Corresponding author and head of the project. Code and GitHub contact:
egspl@proton.me, GitHub [creelie](https://github.com/creelie).

Preprints.org 202606.1350, version 5 (version 4:
[doi.org/10.20944/preprints202606.1350.v4](https://doi.org/10.20944/preprints202606.1350.v4)).

---

## Abstract

We prove the Riemann hypothesis and the generalized Riemann hypothesis for
Dirichlet L-functions using the window energy of the Liouville function, whose
growth exponent is twice the largest real part of a zeta zero. Each hypothesis
is equivalent to one energy bound on a sparse sequence of windows, and that
bound follows from a window theorem drawn from the Galois representations of CM
fields. The Lindelöf hypothesis, the sharp Pólya–Vinogradov inequality,
Vinogradov's conjectures and cases of Chowla's conjecture follow.

**Keywords:** Riemann hypothesis; generalized Riemann hypothesis; Riemann zeta
function; Dirichlet L-functions.

**MSC 2020:** 11M26; 11N37, 11M06.

## Contents of this record

| Path | Content |
|---|---|
| [`Paper/Proof-of-the-Riemann-and-Generalized-Riemann-Hypotheses.pdf`](Paper/Proof-of-the-Riemann-and-Generalized-Riemann-Hypotheses.pdf) | The paper, 183 A4 pages |
| [`ReadableRH/`](ReadableRH) | Lean 4 formalization of the deduction of RH and GRH |
| [`corollaries/`](corollaries) | Lean 4 formalization of the corollaries |
| [`axioms.txt`](axioms.txt), [`corollaries/axioms.txt`](corollaries/axioms.txt) | Output of `#print axioms` |
| [`.zenodo.json`](.zenodo.json) | Zenodo metadata |

## The Lean formalization

Every step of the deduction is checked in Lean 4, to be read beside the paper.
Every theorem listed below builds with no `sorry` and depends only on the three
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Main results

| Result in the paper | Lean theorem | Statement |
|---|---|---|
| Windowed energy principle | `ReadableRH.windowed_energy_principle` | A family energy bounded by C y^θ on windows [Y, Y^{1+δ}] at arbitrarily large heights makes every member zero-free in Re s > θ. |
| RH from the window theorem | `ReadableRH.riemannHypothesis_of_windowBound` | The window bound implies Mathlib's `RiemannHypothesis`. |
| GRH from the window theorem | `ReadableRH.grh_of_windowBound` | The window bound puts every zero of a primitive Dirichlet L-function in the critical strip on Re s = 1/2. |
| Functional-equation step | `ReadableRH.rh_of_H`, `ReadableRH.critLine` | The zero-free half-plane Re s > 1/2 gives RH and GRH. |
| Log-derivative criterion | `ReadableRH.hypothesisH_of_logDeriv`, `ReadableRH.riemannHypothesis_of_logDeriv`, `ReadableRH.grh_of_logDeriv` | If every L'/L(s, χ) is holomorphic on Re s > 1/2, s ≠ 1, then the half-plane, RH and GRH follow. |
| Host decomposition | `UpperTheory.Comparison₂.core_gm` | The core energy bound of the host decomposition. |
| Discarded characters | `UpperTheory.Comparison₂.sigA_le` | The discarded part is at most 4o · x^{1/2+ε}. |
| Kept characters | `Deduction.ch_core` | The kept part is bounded by the host energy and the discarded part. |

## The cited input

The window bound (`WindowBound` in [`ReadableRH/Main.lean`](ReadableRH/Main.lean))
is the one hypothesis of the top-level theorems. It is the window theorem of
L. Alpöge (alpo.ge, November 2026), which rests on the Galois representations
attached to polarized cuspidal automorphic representations over CM fields
(Harris–Taylor, Shin, Chenevier–Harris, Harris–Lan–Taylor–Thorne, Scholze,
Caraiani). Mathlib has no automorphic forms, so the paper cites this step and
it is not formalized here. The host decomposition, which is one of its steps,
is checked in [`ReadableRH/Host/`](ReadableRH/Host).

## Building

Requirements: [elan](https://github.com/leanprover/elan). The toolchain and
the Mathlib revision are pinned.

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

Lean 4.33.1, Mathlib `0df444a`. With Mathlib's prebuilt cache, the build takes
about 9 minutes on a four-core machine, after a cache download of about 3 minutes.

The corollaries are a separate project on Lean 4.34.1:

```
cd corollaries
lake exe cache get
lake build
lake env lean Axioms.lean
```

This takes about 6 minutes on the same machine, after a cache download of about
3 minutes.

## Corollaries

Each corollary takes the zero-free half-plane (Hypothesis H,
`LiouvilleEnergyRH.HypothesisH`) as an explicit argument.

| Lean theorem | Statement |
|---|---|
| `lindelof_bound`, `lindelof_half` | Lindelöf bounds for Dirichlet L-functions |
| `polya_vinogradov`, `character_sum_bound`, `character_sum_bound_half`, `character_sum_le_rpow`, `vinogradov_character_sum` | Character-sum bounds |
| `prime_sum_bound` | Twisted prime sums |
| `least_nonresidue`, `least_prime_primitive_root`, `erdos_985` | Least non-residues and primitive roots |
| `logDeriv_one_bound`, `euler_kronecker_bound` | Logarithmic derivatives at s = 1 and Euler–Kronecker constants |

## Related repositories

Each corollary of the paper that has its own formalization is linked in the
paper by a footnote. All take the zero-free half-plane as an explicit
hypothesis unless stated otherwise.

| Repository | Content |
|---|---|
| [chawla-rh](https://github.com/anaxia-research/chawla-rh) | Cases of Chowla's conjecture: one-point case at every shift, almost all shifts, both signs at every fixed shift (unconditional) |
| [averaged-chowla-grh](https://github.com/anaxia-research/averaged-chowla-grh) | M(x), L(x) ≪ x^{1/2+ε}; shifted Liouville sums; averaged two-point Chowla |
| [lindelof-rh](https://github.com/anaxia-research/lindelof-rh) | Lindelöf hypothesis for ζ |
| [prime-counting-rh](https://github.com/anaxia-research/prime-counting-rh) | ψ(x), θ(x) with error x^{1/2+ε}; primes in short intervals |
| [primes-in-progressions-grh](https://github.com/anaxia-research/primes-in-progressions-grh) | Twisted prime sums, primes in progressions, least prime in a progression |
| [character-sums-grh](https://github.com/anaxia-research/character-sums-grh) | Character-sum bounds; Pólya–Vinogradov with log log q |
| [Polya-rh](https://github.com/anaxia-research/Polya-rh) | Pólya–Vinogradov with log log q |
| [polya-vinogradov-lean](https://github.com/anaxia-research/polya-vinogradov-lean) | The classical Pólya–Vinogradov inequality (unconditional) |
| [least-nonresidue-grh](https://github.com/anaxia-research/least-nonresidue-grh) | Vinogradov's least non-residue conjecture |
| [primitive-root-grh](https://github.com/anaxia-research/primitive-root-grh) | Least prime primitive root; Erdős Problem 985 |
| [Erd-s-985](https://github.com/anaxia-research/Erd-s-985) | Erdős Problem 985 |
| [euler-kronecker-grh](https://github.com/anaxia-research/euler-kronecker-grh) | L'/L(1, χ) ≪ log log q; Euler–Kronecker constants |

## Repository layout

```
Paper/                  the paper (PDF)
ReadableRH/
  Window/               windowed energy principle (Landau-type theorem)
  Host/                 host decomposition
  FunctionalEquation.lean
  LogDeriv.lean         log-derivative criterion
  Main.lean             window bound ⇒ RH and GRH
Axioms.lean             #print axioms for the theorems above
corollaries/            consequences of the zero-free half-plane (Lean 4.34.1)
  LiouvilleEnergyRH/    Lindelöf, character sums, prime sums, least non-residue,
                        least prime primitive root, Erdős 985, Euler–Kronecker
  Vinogradov/           Pólya–Vinogradov and Vinogradov's character-sum conjectures
```

## Citation

```bibtex
@misc{BhattacharjeeBhattacharya2026,
  author       = {Bhattacharjee, Deep and Bhattacharya, Ushashi},
  title        = {Proof of the Riemann and Generalized Riemann Hypotheses},
  year         = {2026},
  publisher    = {Zenodo},
  version      = {5.0.0},
  howpublished = {Preprints.org, 202606.1350, version 5},
  url          = {https://github.com/anaxia-research/liouville-energy-rh}
}
```

## Credits and licence

`ReadableRH/Window/` and `ReadableRH/Host/` are taken from L. Alpöge's Lean
project, with only the import lines changed. See [`NOTICE`](NOTICE) for these
and the other third-party files. The paper in `Paper/` is under CC BY 4.0, as on Preprints.org. Our own Lean
files are under the MIT licence ([`LICENSE`](LICENSE)). The Vinogradov files are under Apache 2.0
([`corollaries/LICENSE-APACHE`](corollaries/LICENSE-APACHE)).
