# Proof of the Riemann and Generalized Riemann Hypotheses: Lean formalization

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

This repository holds Lean 4 files only. Every theorem listed below builds with
no `sorry` and depends only on the three standard axioms `propext`,
`Classical.choice` and `Quot.sound` (see [`axioms.txt`](axioms.txt) and
[`corollaries/axioms.txt`](corollaries/axioms.txt)).

## The conjectures and what is proved

### Riemann hypothesis and generalized Riemann hypothesis

| Conjecture | Lean theorem | What is proved |
|---|---|---|
| Riemann hypothesis | `ReadableRH.riemannHypothesis_of_windowBound` | The window bound implies Mathlib's `RiemannHypothesis`. |
| Generalized Riemann hypothesis for Dirichlet L-functions | `ReadableRH.grh_of_windowBound` | The window bound puts every zero of a primitive Dirichlet L-function in the critical strip on Re s = 1/2. |
| RH and GRH from the zero-free half-plane | `ReadableRH.rh_of_H`, `ReadableRH.critLine` | The zero-free half-plane Re s > 1/2 gives RH and GRH, through the functional equation. |
| RH and GRH from the logarithmic derivative | `ReadableRH.hypothesisH_of_logDeriv`, `ReadableRH.riemannHypothesis_of_logDeriv`, `ReadableRH.grh_of_logDeriv` | If every L'/L(s, χ) is holomorphic on Re s > 1/2, s ≠ 1, then the half-plane, RH and GRH follow. |
| Windowed energy principle | `ReadableRH.windowed_energy_principle` | A family energy bounded by C y^θ on windows [Y, Y^{1+δ}] at arbitrarily large heights makes every member zero-free in Re s > θ. |
| Host decomposition | `UpperTheory.Comparison₂.core_gm`, `UpperTheory.Comparison₂.sigA_le`, `Deduction.ch_core` | The core energy bound, the bound 4o · x^{1/2+ε} for the discarded characters, and the bound for the kept characters. |

The window bound (`WindowBound` in [`ReadableRH/Main.lean`](ReadableRH/Main.lean))
is the one hypothesis of the two top-level theorems. It is the window theorem of
L. Alpöge (alpo.ge, November 2026), which rests on the Galois representations
attached to polarized cuspidal automorphic representations over CM fields
(Harris–Taylor, Shin, Chenevier–Harris, Harris–Lan–Taylor–Thorne, Scholze,
Caraiani). Mathlib has no automorphic forms, so this step is not formalized
here. The host decomposition, which is one of its steps, is checked in
[`ReadableRH/Host/`](ReadableRH/Host).

### Consequences of the zero-free half-plane

Each theorem below takes the zero-free half-plane Re s > 1/2 for all Dirichlet
L-functions (`LiouvilleEnergyRH.HypothesisH`) as an explicit argument.

| Conjecture | Lean theorem | What is proved |
|---|---|---|
| Lindelöf hypothesis for Dirichlet L-functions | `lindelof_half`, `lindelof_bound` | \|L(s, χ)\| + \|L(s, χ)⁻¹\| ≤ C (q(3 + \|t\|))^w for Re s ≥ 1/2 + w, every w > 0. |
| Vinogradov's character-sum conjecture | `vinogradov_character_sum`, `character_sum_bound_half`, `character_sum_bound`, `character_sum_le_rpow` | \|Σ_{n≤x} χ(n)\| ≤ C x^θ for every θ > 1/2 once x ≥ q^η; and ≤ C q^w x^{1/2+w}. |
| Sharp Pólya–Vinogradov inequality | `polya_vinogradov` | \|Σ_{n≤T} χ(n)\| ≤ C √q log log q for primitive χ mod q ≥ 3. |
| Twisted prime sums | `prime_sum_bound` | \|Σ_{p≤x} χ(p) log p\| ≤ C x^{19/20} log(q + 2). |
| Vinogradov's least non-residue conjecture | `least_nonresidue` | Every nonprincipal χ mod p has χ(n) ≠ 1 for some n ≤ C p^ε. |
| Least prime primitive root | `least_prime_primitive_root` | Every prime p has a prime primitive root ℓ ≤ C p^ε. |
| Erdős Problem 985 | `erdos_985` | Every large prime p has a prime primitive root q < p. |
| Logarithmic derivative at s = 1 | `logDeriv_one_bound` | \|L'/L(1, χ)\| ≤ C log log(q + 2). |
| Euler–Kronecker constants of ℚ(ζ_q) | `euler_kronecker_bound` | For primes q ≥ 3, the sum of L'/L(1, χ) over nonprincipal χ lies in [−C log q log log q, C log q]. |

All names in this table are in the namespace `LiouvilleEnergyRH`.

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

The consequences are a separate project on Lean 4.34.1:

```
cd corollaries
lake exe cache get
lake build
lake env lean Axioms.lean
```

This takes about 6 minutes on the same machine, after a cache download of about
3 minutes.

## Repository layout

```
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

## Credits and licence

`ReadableRH/Window/` and `ReadableRH/Host/` are taken from L. Alpöge's Lean
project, with only the import lines changed. See [`NOTICE`](NOTICE) for these
and the other third-party files. Our own Lean files are under the MIT licence
([`LICENSE`](LICENSE)). The Vinogradov files are under Apache 2.0
([`corollaries/LICENSE-APACHE`](corollaries/LICENSE-APACHE)).
