# Results proved in this project

This file lists every theorem of
[`corollaries/LiouvilleEnergyRH/Unconditional.lean`](LiouvilleEnergyRH/Unconditional.lean),
[`corollaries/LiouvilleEnergyRH/TwoPointChowla.lean`](LiouvilleEnergyRH/TwoPointChowla.lean)
and the earlier corollary files. For each theorem it gives:

1. the result's name in plain words;
2. its mathematical statement;
3. its Lean name and file;
4. what it assumes;
5. the output of `#print axioms` for it.

The project builds with Lean 4.34.1 and Mathlib v4.34.1. The axiom lists below are copied from
[`corollaries/axioms.txt`](axioms.txt), which is the output of
`lake env lean Axioms.lean` in this directory. Each statement below describes the Lean statement
and claims nothing more.

## Conventions

- λ is the Liouville function, μ the Möbius function, Λ the von Mangoldt function and τ the
  divisor-counting function.
- ψ(x) = Σ_{n ≤ x} Λ(n), θ(x) = Σ_{p ≤ x} log p, M(N) = Σ_{1 ≤ n ≤ N} μ(n) and
  L(N) = Σ_{1 ≤ n ≤ N} λ(n).
- χ is a Dirichlet character modulo q ≥ 1, with values in ℂ. L(s, χ) is Mathlib's
  `DirichletCharacter.LFunction χ s`, which is defined on all of ℂ.
- "Principal" means χ = 1 in Mathlib. The character modulo 1 is principal, and its L-function is
  ζ.
- A sum over n ≤ x runs over 1 ≤ n ≤ ⌊x⌋.
- Constants: Lean states each bound as "∃ C, ∀ q, χ, x, …". So C depends only on the parameters
  quantified before it (ε, η, w, d, …). It is uniform in q, χ, x, N and the shift.

## What "assumes" means

- **Nothing.** The Lean theorem has no hypothesis argument. Its proof may use theorems of
  OpenAI's Lean library, which is vendored in `corollaries/OAI/` and is proved there, not
  assumed:
  - **(O1)** `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`, in
    `corollaries/OAI/NumberTheory/DirichletL/Nonvanishing.lean`: for every q ≥ 1, every χ mod q
    and every s with Re s > 7/8, L(s, χ) ≠ 0, except when χ is principal and s = 1.
  - **(O2)** `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, in the same file: ζ(s) ≠ 0 for
    Re s > 7/8.
  - **(O3)** `OAI.OrdinaryTwoPointCorrelations.liouville_log_saving`, in
    `corollaries/OAI/NumberTheory/TwoPointCorrelations/FinalMain.lean`. There is c > 0 such that
    for all natural numbers a₁, a₂ > 0 and b₁, b₂ with a₁b₂ ≠ a₂b₁, there is C > 0 with
    ‖Σ_{1 ≤ n ≤ ⌊X⌋} λ(a₁n + b₁) λ(a₂n + b₂)‖ ≤ C X / (log X)^c for every X ≥ 3.
- **HypothesisH.** `LiouvilleEnergyRH.HypothesisH`, in
  `corollaries/LiouvilleEnergyRH/Hypothesis.lean`, is an explicit argument. It states that for
  every q ≥ 1, every χ mod q and every s with Re s > 1/2, L(s, χ) ≠ 0 unless χ is principal and
  s = 1. This is the zero-free half-plane form of GRH for Dirichlet L-functions, including ζ.
- **ZeroFree.** `Vinogradov.Main.ZeroFree`, in `corollaries/Vinogradov/Main.lean`, is an
  explicit argument. It states that for every q ≥ 1, every nonprincipal χ mod q and every z with
  Re z > 7/8, L(z, χ) ≠ 0.
- **Half-plane at σa.** The generalized lemmas take a zero-free half-plane Re s > σa as an
  explicit argument, for ζ (excluding s = 1) or for nonprincipal L(s, χ), or both.
- **WindowBound.** `ReadableRH.WindowBound`, the hypothesis of the parent project
  (`ReadableRH/Main.lean`), is assumed by no theorem in this file. `corollaries/` does not import
  `ReadableRH`.

---

## 1. Unconditional results

Every theorem in this section is in the namespace `LiouvilleEnergyRH.Unconditional` and in
`corollaries/LiouvilleEnergyRH/Unconditional.lean`. It has no hypothesis argument.

### 1.1 The zero-free half-plane Re s > 7/8 for Dirichlet L-functions

- **Statement.** For every q ≥ 1, every χ mod q and every s ∈ ℂ with Re s > 7/8, if χ ≠ 1 or
  s ≠ 1, then L(s, χ) ≠ 0.
- **Lean.** `LiouvilleEnergyRH.Unconditional.LFunction_ne_zero`.
- **Assumes.** Nothing. Proof: (O1).
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.2 ζ has no zero with Re s > 7/8

- **Statement.** ζ(s) ≠ 0 for every s with Re s > 7/8. The variant `zeta_ne_zero_of_lt` adds
  the redundant hypothesis s ≠ 1, in the form the generalized lemmas expect.
- **Lean.** `LiouvilleEnergyRH.Unconditional.riemannZeta_ne_zero` and
  `LiouvilleEnergyRH.Unconditional.zeta_ne_zero_of_lt`.
- **Assumes.** Nothing. Proof: (O2).
- **Axioms.** `riemannZeta_ne_zero`: `[propext, Classical.choice, Quot.sound]`;
  `zeta_ne_zero_of_lt`: `[propext, Classical.choice, Quot.sound]`

### 1.3 The hypothesis `ZeroFree` of the Vinogradov library

- **Statement.** `Vinogradov.Main.ZeroFree` holds: no nonprincipal L(s, χ) vanishes for
  Re s > 7/8. `instFactZeroFree` registers it as the instance `Fact Vinogradov.Main.ZeroFree`.
  The files of `corollaries/Vinogradov/` take that instance as an argument.
- **Lean.** `LiouvilleEnergyRH.Unconditional.zeroFree` and
  `LiouvilleEnergyRH.Unconditional.instFactZeroFree`.
- **Assumes.** Nothing. Proof: (O1).
- **Axioms.** `zeroFree`: `[propext, Classical.choice, Quot.sound]`;
  `instFactZeroFree`: `[propext, Classical.choice, Quot.sound]`

### 1.4 Pólya–Vinogradov inequality with log log q

- **Statement.** There is C > 0 with the following property. For every q ≥ 3, every primitive χ
  mod q and every T ∈ ℕ, ‖Σ_{1 ≤ n ≤ T} χ(n)‖ ≤ C √q log log q.
- **Lean.** `LiouvilleEnergyRH.Unconditional.polya_vinogradov`.
- **Assumes.** Nothing. Proof: (O1), through `Vinogradov.PV.polya_vinogradov_loglog`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.5 The least character non-residue (Vinogradov's conjecture)

- **Statement.** For every ε > 0 there is C > 0 with the following property. For every prime p
  and every nonprincipal χ mod p, some n with 1 ≤ n ≤ C p^ε has χ(n) ≠ 1. With χ the Legendre
  symbol, the least quadratic non-residue mod p is at most C p^ε.
- **Lean.** `LiouvilleEnergyRH.Unconditional.least_nonresidue`.
- **Assumes.** Nothing. Proof: (O1), through `LiouvilleEnergyRH.least_nonresidue_of_zeroFree`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.6 The least prime primitive root, power bound

- **Statement.** For every ε > 0 there is C > 0 such that every prime p has a prime ℓ ≤ C p^ε
  whose multiplicative order mod p is p − 1.
- **Lean.** `LiouvilleEnergyRH.Unconditional.least_prime_primitive_root`.
- **Assumes.** Nothing. Proof: (O1), through `Vinogradov.Main.least_prime_primitive_root_le_rpow`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.7 The least prime primitive root, divisor bound

- **Statement.** For every η > 0 there is C > 0 such that every prime p has a prime primitive
  root ℓ mod p with ℓ ≤ C (τ(p − 1)² log(p + 2))^{8+η}.
- **Lean.** `LiouvilleEnergyRH.Unconditional.least_prime_primitive_root_bound`.
- **Assumes.** Nothing. Proof: (O1), through `Vinogradov.Main.least_prime_primitive_root_bound`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.8 Erdős Problem 985 for large primes

- **Statement.** There is p₀ such that every prime p ≥ p₀ has a prime q < p that is a primitive
  root mod p.
- **Lean.** `LiouvilleEnergyRH.Unconditional.erdos_985`.
- **Assumes.** Nothing. Proof: (O1), through `Vinogradov.Main.erdos_985_of_large`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.9 Character sums beyond q^η, exponent θ > 7/8

- **Statement.** For every η > 0 and θ > 7/8 there is C > 0 with
  ‖Σ_{n ≤ x} χ(n)‖ ≤ C x^θ for every q ≥ 1, every nonprincipal χ mod q and every x ≥ 1 with
  x ≥ q^η. Vinogradov's character-sum conjecture asks for this for every θ > 1/2; this theorem
  gives the range θ > 7/8.
- **Lean.** `LiouvilleEnergyRH.Unconditional.character_sum_le_rpow`.
- **Assumes.** Nothing. Proof: (O1), through `Vinogradov.CharSum.character_sum_le_rpow`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.10 Character sums, uniform bound

- **Statement.** For every w > 0 there is C > 0 with
  ‖Σ_{n ≤ x} χ(n)‖ ≤ C q^w x^{7/8+w} for every q ≥ 1, every nonprincipal χ mod q and every
  x ≥ 1.
- **Lean.** `LiouvilleEnergyRH.Unconditional.character_sum_bound`.
- **Assumes.** Nothing. Proof: (O1), through `Vinogradov.CharSum.character_sum_bound`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.11 Lindelöf-type bound for L(s, χ) to the right of 7/8

- **Statement.** For every w > 0 there is C > 0 with
  ‖L(s, χ)‖ + ‖L(s, χ)⁻¹‖ ≤ C (q (3 + |Im s|))^w for every q ≥ 1, every nonprincipal χ mod q
  and every s with Re s ≥ 7/8 + w. This is not the Lindelöf hypothesis, which concerns
  Re s = 1/2.
- **Lean.** `LiouvilleEnergyRH.Unconditional.lindelof_bound`.
- **Assumes.** Nothing. Proof: (O1), through `Vinogradov.CharSum.lindelof`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.12 Prime sums twisted by a character

- **Statement.** There is C > 0 with
  ‖Σ_{p ≤ x, p prime} χ(p) log p‖ ≤ C x^{19/20} log(q + 2) for every q ≥ 1, every nonprincipal
  χ mod q and every x ≥ 1.
- **Lean.** `LiouvilleEnergyRH.Unconditional.prime_sum_bound`.
- **Assumes.** Nothing. Proof: (O1), through `Vinogradov.PV.prime_sum_bound`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.13 The logarithmic derivative L′/L(1, χ)

- **Statement.** There is C > 0 with ‖L′(1, χ) / L(1, χ)‖ ≤ C log log(q + 2) for every q ≥ 1
  and every nonprincipal χ mod q. Here L′ is the complex derivative of s ↦ L(s, χ).
- **Lean.** `LiouvilleEnergyRH.Unconditional.logDeriv_one_bound`.
- **Assumes.** Nothing. Proof: (O1), through
  `Vinogradov.EulerKronecker.logDeriv_one_le_of_zeroFree`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.14 Euler–Kronecker constants of the cyclotomic fields ℚ(ζ_q)

- **Statement.** There is C > 0 with the following property. For every prime q ≥ 3, the sum r
  of L′(1, χ)/L(1, χ) over the nonprincipal χ mod q is real, and
  −C log q log log q ≤ r ≤ C log q.
- **Lean.** `LiouvilleEnergyRH.Unconditional.euler_kronecker_bound`.
- **Assumes.** Nothing. Proof: (O1), through
  `Vinogradov.EulerKronecker.sum_logDeriv_one_of_zeroFree`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.15 ζ in the strip 7/8 < σ < 1

- **Statement.** For every d > 0 and η > 0 there is K with |ζ(σ + it)| ≤ K (3 + |t|)^η for all
  real σ, t with 7/8 + d ≤ σ ≤ 1 − d.
- **Lean.** `LiouvilleEnergyRH.Unconditional.zeta_strip_bound`.
- **Assumes.** Nothing. Proof: (O2), through `LiouvilleEnergyRH.Lindelof.zeta_strip_bound` at
  σa = 7/8.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.16 1/ζ to the right of 7/8

- **Statement.** For every d > 0 and η > 0 there is K with |1/ζ(σ + it)| ≤ K (3 + |t|)^η for
  all real σ, t with 7/8 + d ≤ σ ≤ 2 and σ + it ≠ 1.
- **Lean.** `LiouvilleEnergyRH.Unconditional.zeta_inv_bound`.
- **Assumes.** Nothing. Proof: (O2), through `LiouvilleEnergyRH.Mertens.invZeta_bound` at
  σa = 7/8.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.17 The Mertens function, M(N) ≪ N^{7/8+ε}

- **Statement.** For every ε > 0 there is C with |M(N)| ≤ C N^{7/8+ε} for every N ∈ ℕ. In Lean
  this is `ChowlaRH.MertensBound (7/8 + ε)`.
- **Lean.** `LiouvilleEnergyRH.Unconditional.mertensBound`.
- **Assumes.** Nothing. Proof: (O2), through `LiouvilleEnergyRH.Mertens.mertens_bound` at
  σa = 7/8.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.18 M(N) = o(N)

- **Statement.** (1/N) Σ_{1 ≤ n ≤ N} μ(n) → 0 as N → ∞.
- **Lean.** `LiouvilleEnergyRH.Unconditional.moebius_mean_zero`.
- **Assumes.** Nothing. Proof: 1.17 with ε = 1/16.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.19 The prime number theorem with error x^{7/8+η}, for ψ

- **Statement.** For every η > 0 there is K with |ψ(x) − x| ≤ K x^{7/8+η} for every x ≥ 1.
- **Lean.** `LiouvilleEnergyRH.Unconditional.psi_bound`.
- **Assumes.** Nothing. Proof: (O2), through `LiouvilleEnergyRH.PrimeCount.psi_bound` at
  σa = 7/8.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.20 The prime number theorem with error x^{7/8+η}, for θ

- **Statement.** For every η > 0 there is K ≥ 0 with |θ(x) − x| ≤ K x^{7/8+η} for every
  x ≥ 1.
- **Lean.** `LiouvilleEnergyRH.Unconditional.theta_bound`.
- **Assumes.** Nothing. Proof: (O2), through `LiouvilleEnergyRH.PrimeCount.theta_bound` at
  σa = 7/8.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.21 The prime number theorem, ψ(x)/x → 1

- **Statement.** ψ(x)/x → 1 as x → ∞ (x real).
- **Lean.** `LiouvilleEnergyRH.Unconditional.psi_div_tendsto_one`.
- **Assumes.** Nothing. Proof: 1.19 with η = 1/16.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.22 Primes in short intervals (x, x + x^{7/8+η}]

- **Statement.** For every η with 0 < η ≤ 1/8 there is x₀ such that for every real x ≥ x₀
  there is a prime p with x < p ≤ x + x^{7/8+η}.
- **Lean.** `LiouvilleEnergyRH.Unconditional.prime_in_short_interval`.
- **Assumes.** Nothing. Proof: (O2), through `LiouvilleEnergyRH.PrimeCount.prime_in_short_interval`
  at σa = 7/8.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.23 Gaps between consecutive primes

- **Statement.** For every η with 0 < η ≤ 1/8 there is p₀ such that every prime p ≥ p₀ has a
  prime q with p < q ≤ p + p^{7/8+η}.
- **Lean.** `LiouvilleEnergyRH.Unconditional.prime_gap`.
- **Assumes.** Nothing. Proof: 1.22.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.24 Twisted von Mangoldt sums

- **Statement.** For every η > 0 there is K ≥ 0 with
  ‖Σ_{n ≤ x} χ(n) Λ(n)‖ ≤ K q^η x^{7/8+η} for every q ≥ 1, every nonprincipal χ mod q and every
  x ≥ 1.
- **Lean.** `LiouvilleEnergyRH.Unconditional.chi_psi_bound`.
- **Assumes.** Nothing. Proof: (O1), through `LiouvilleEnergyRH.Progressions.chi_psi_bound` at
  σa = 7/8.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.25 Primes in arithmetic progressions with a power saving

- **Statement.** For every η > 0 there is K ≥ 0 with the following property. For every q ≥ 1,
  every unit a of ℤ/qℤ and every x ≥ 1, |φ(q) ψ(x; q, a) − x| ≤ K q^{1+η} x^{7/8+η}, where
  ψ(x; q, a) = Σ_{n ≤ x, n ≡ a mod q} Λ(n).
- **Lean.** `LiouvilleEnergyRH.Unconditional.psiAP_bound`.
- **Assumes.** Nothing. Proof: (O1) and (O2), through `LiouvilleEnergyRH.Progressions.psiAP_bound`
  at σa = 7/8.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 1.26 The least prime in an arithmetic progression, p ≤ C q^{8+d}

- **Statement.** For every d with 0 < d ≤ 1 there is C with the following property. For every
  q ≥ 1 and every a ∈ ℕ coprime to q, there is a prime p ≡ a (mod q) with p ≤ C q^{8+d}.
- **Lean.** `LiouvilleEnergyRH.Unconditional.least_prime_in_AP`.
- **Assumes.** Nothing. Proof: (O1) and (O2), through
  `LiouvilleEnergyRH.Progressions.least_prime_in_AP_seven_eighths`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

---

## 2. Consequences of Hypothesis H (RH/GRH) and of explicit zero-free half-planes

### 2.1 Theorems that take `HypothesisH`

These are in the namespace `LiouvilleEnergyRH`. Each one takes `h : HypothesisH` as an explicit
argument.

The first ten use H only through `zeroFree_of_H`, which is the half-plane Re s > 7/8. Their
statements are identical to the unconditional theorems of the same name in Section 1. Only
`lindelof_half`, `character_sum_bound_half` and `vinogradov_character_sum` use the full
half-plane Re s > 1/2.

#### 2.1.0 H gives `ZeroFree`

- **Statement.** H implies `Vinogradov.Main.ZeroFree`.
- **Lean.** `LiouvilleEnergyRH.zeroFree_of_H`, `corollaries/LiouvilleEnergyRH/Corollaries.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.1 Pólya–Vinogradov with log log q, under H

- **Statement.** As 1.4.
- **Lean.** `LiouvilleEnergyRH.polya_vinogradov`, `corollaries/LiouvilleEnergyRH/Corollaries.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.2 The least character non-residue, under H

- **Statement.** As 1.5.
- **Lean.** `LiouvilleEnergyRH.least_nonresidue`, `corollaries/LiouvilleEnergyRH/NonResidue.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.3 The least prime primitive root, under H

- **Statement.** As 1.6.
- **Lean.** `LiouvilleEnergyRH.least_prime_primitive_root`,
  `corollaries/LiouvilleEnergyRH/Corollaries.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.4 Erdős Problem 985 for large primes, under H

- **Statement.** As 1.8.
- **Lean.** `LiouvilleEnergyRH.erdos_985`, `corollaries/LiouvilleEnergyRH/Corollaries.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.5 Character sums with θ > 7/8, under H

- **Statement.** As 1.9.
- **Lean.** `LiouvilleEnergyRH.character_sum_le_rpow`,
  `corollaries/LiouvilleEnergyRH/Corollaries.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.6 Lindelöf-type bound to the right of 7/8, under H

- **Statement.** As 1.11.
- **Lean.** `LiouvilleEnergyRH.lindelof_bound`, `corollaries/LiouvilleEnergyRH/MoreCorollaries.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.7 Character sums C q^w x^{7/8+w}, under H

- **Statement.** As 1.10.
- **Lean.** `LiouvilleEnergyRH.character_sum_bound`,
  `corollaries/LiouvilleEnergyRH/MoreCorollaries.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.8 Twisted prime sums, under H

- **Statement.** As 1.12.
- **Lean.** `LiouvilleEnergyRH.prime_sum_bound`, `corollaries/LiouvilleEnergyRH/MoreCorollaries.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.9 L′/L(1, χ), under H

- **Statement.** As 1.13.
- **Lean.** `LiouvilleEnergyRH.logDeriv_one_bound`,
  `corollaries/LiouvilleEnergyRH/MoreCorollaries.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.10 Euler–Kronecker constants of ℚ(ζ_q), under H

- **Statement.** As 1.14.
- **Lean.** `LiouvilleEnergyRH.euler_kronecker_bound`,
  `corollaries/LiouvilleEnergyRH/MoreCorollaries.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.11 Lindelöf-type bound to the right of 1/2

- **Statement.** For every w > 0 there is C > 0 with
  ‖L(s, χ)‖ + ‖L(s, χ)⁻¹‖ ≤ C (q (3 + |Im s|))^w for every q ≥ 1, every nonprincipal χ mod q
  and every s with Re s ≥ 1/2 + w.
- **Lean.** `LiouvilleEnergyRH.lindelof_half`, `corollaries/LiouvilleEnergyRH/VinogradovHalf.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.12 Character sums C q^w x^{1/2+w}

- **Statement.** For every w > 0 there is C > 0 with
  ‖Σ_{n ≤ x} χ(n)‖ ≤ C q^w x^{1/2+w} for every q ≥ 1, every nonprincipal χ mod q and every
  x ≥ 1.
- **Lean.** `LiouvilleEnergyRH.character_sum_bound_half`,
  `corollaries/LiouvilleEnergyRH/VinogradovHalf.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.13 Vinogradov's character-sum conjecture

- **Statement.** For every η > 0 and θ > 1/2 there is C > 0 with ‖Σ_{n ≤ x} χ(n)‖ ≤ C x^θ for
  every q ≥ 1, every nonprincipal χ mod q and every x ≥ 1 with x ≥ q^η.
- **Lean.** `LiouvilleEnergyRH.vinogradov_character_sum`,
  `corollaries/LiouvilleEnergyRH/VinogradovHalf.lean`.
- **Assumes.** HypothesisH.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.1.14 The least character non-residue from `ZeroFree`

- **Statement.** As 1.5, with the hypothesis `ZeroFree`.
- **Lean.** `LiouvilleEnergyRH.least_nonresidue_of_zeroFree`,
  `corollaries/LiouvilleEnergyRH/NonResidue.lean`.
- **Assumes.** `Vinogradov.Main.ZeroFree`. The unconditional 1.5 discharges it with 1.3.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 2.2 Lemmas with an explicit zero-free half-plane Re s > σa

These lemmas are in the generalized files. Each one takes the half-plane as an explicit argument,
in one or both of these forms:

- (Hζ) ζ(s) ≠ 0 for Re s > σa, s ≠ 1;
- (HL) L(z, χ) ≠ 0 for every q ≥ 1, every nonprincipal χ mod q and Re z > σa.

They also take 1/2 ≤ σa. With σa = 7/8, Section 1 discharges (Hζ) and (HL) by (O2) and (O1).
With σa = 1/2, (Hζ) and (HL) are what HypothesisH states. No theorem in the project derives the
σa = 1/2 cases from `HypothesisH`.

#### 2.2.1 1/ζ bound

- **Statement.** Assume 1/2 ≤ σa ≤ 1 and (Hζ). For e with 0 < e < 1/1000 and every ε > 0, there
  is D ≥ 0 with |1/ζ(σ + it)| ≤ D (2 (3 + |t|)²)^ε for σa + 8e ≤ σ ≤ 2. In Lean the bound is
  stated for `invZeta`, which equals 1/ζ away from s = 1.
- **Lean.** `LiouvilleEnergyRH.Mertens.invZeta_bound`,
  `corollaries/LiouvilleEnergyRH/Mertens/Main.lean`.
- **Assumes.** (Hζ) at σa.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.2.2 Mertens function

- **Statement.** Assume 1/2 ≤ σa ≤ 7/8 and (Hζ). For every η > 0 there is K with
  |Σ_{n ≤ x} μ(n)| ≤ K x^{σa+η} for x ≥ 1. With σa = 1/2 this is Littlewood's bound
  M(x) ≪ x^{1/2+η}.
- **Lean.** `LiouvilleEnergyRH.Mertens.mertens_bound`,
  `corollaries/LiouvilleEnergyRH/Mertens/Main.lean`.
- **Assumes.** (Hζ) at σa.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.2.3 ψ(x)

- **Statement.** Assume 1/2 ≤ σa ≤ 7/8 and (Hζ). For every η > 0 there is K with
  |ψ(x) − x| ≤ K x^{σa+η} for x ≥ 1.
- **Lean.** `LiouvilleEnergyRH.PrimeCount.psi_bound`,
  `corollaries/LiouvilleEnergyRH/PrimeCount/Psi.lean`.
- **Assumes.** (Hζ) at σa.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.2.4 θ(x)

- **Statement.** Assume 1/2 ≤ σa ≤ 7/8 and (Hζ). For every η > 0 there is K ≥ 0 with
  |θ(x) − x| ≤ K x^{σa+η} for x ≥ 1.
- **Lean.** `LiouvilleEnergyRH.PrimeCount.theta_bound`,
  `corollaries/LiouvilleEnergyRH/PrimeCount/Theta.lean`.
- **Assumes.** (Hζ) at σa.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.2.5 Primes in short intervals

- **Statement.** Assume 1/2 ≤ σa ≤ 7/8, (Hζ), η > 0 and σa + η ≤ 1. Then there is x₀ such that
  every x ≥ x₀ has a prime p with x < p ≤ x + x^{σa+η}.
- **Lean.** `LiouvilleEnergyRH.PrimeCount.prime_in_short_interval`,
  `corollaries/LiouvilleEnergyRH/PrimeCount/Theta.lean`.
- **Assumes.** (Hζ) at σa.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.2.6 Twisted von Mangoldt sums

- **Statement.** Assume 1/2 ≤ σa ≤ 7/8 and (HL). For every η > 0 there is K ≥ 0 with
  ‖Σ_{n ≤ x} χ(n) Λ(n)‖ ≤ K q^η x^{σa+η} for every q ≥ 1, every nonprincipal χ mod q and x ≥ 1.
- **Lean.** `LiouvilleEnergyRH.Progressions.chi_psi_bound`,
  `corollaries/LiouvilleEnergyRH/Progressions/ChiPsi.lean`.
- **Assumes.** (HL) at σa.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.2.7 Primes in progressions

- **Statement.** Assume 1/2 ≤ σa ≤ 7/8, (HL) and (Hζ). For every η > 0 there is K ≥ 0 with
  |φ(q) ψ(x; q, a) − x| ≤ K q^{1+η} x^{σa+η} for every q ≥ 1, every unit a mod q and x ≥ 1.
- **Lean.** `LiouvilleEnergyRH.Progressions.psiAP_bound`,
  `corollaries/LiouvilleEnergyRH/Progressions/AP.lean`.
- **Assumes.** (HL) and (Hζ) at σa.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.2.8 Least prime in a progression, p ≤ C q^{2+d}

- **Statement.** Assume (HL) and (Hζ) at σa = 1/2. For every d with 0 < d ≤ 1 there is C with a
  prime p ≡ a (mod q), p ≤ C q^{2+d}, for every q ≥ 1 and every a coprime to q.
- **Lean.** `LiouvilleEnergyRH.Progressions.least_prime_in_AP`,
  `corollaries/LiouvilleEnergyRH/Progressions/AP.lean`.
- **Assumes.** (HL) and (Hζ) at σa = 1/2.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.2.9 Least prime in a progression, p ≤ C q^{8+d}

- **Statement.** Assume (HL) and (Hζ) at σa = 7/8. For every d with 0 < d ≤ 1 there is C with a
  prime p ≡ a (mod q), p ≤ C q^{8+d}, for every q ≥ 1 and every a coprime to q.
- **Lean.** `LiouvilleEnergyRH.Progressions.least_prime_in_AP_seven_eighths`,
  `corollaries/LiouvilleEnergyRH/Progressions/AP.lean`.
- **Assumes.** (HL) and (Hζ) at σa = 7/8. Theorem 1.26 discharges both.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.2.10 ζ in a strip

- **Statement.** Assume 1/2 ≤ σa ≤ 1, b < 1 and (Hζ). For e with 0 < e < 1/1000 and every
  ε > 0, there is D ≥ 0 with |ζ(σ + it)| ≤ D (2 (3 + |t|)²)^ε for σa + 8e ≤ σ ≤ b.
- **Lean.** `LiouvilleEnergyRH.Lindelof.zeta_strip_bound`,
  `corollaries/LiouvilleEnergyRH/Lindelof/Strip.lean`.
- **Assumes.** (Hζ) at σa.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

#### 2.2.11 Contour bounds for coefficient sums

- **Statement.** Let F be holomorphic on Re z > σa and equal to the L-series of a on Re z > 1.
  Suppose the L-series converges at 2, and suppose ‖F(σ + it)‖ ≤ D (2q(3 + |t|)²)^ε for
  σ₀ ≤ σ ≤ 2, where 1/2 < σ₀ ≤ 1, σa < σ₀ and 0 < ε ≤ 1/8.
  - `sum_bound`: if ‖a(n)‖ ≤ 1 for all n, then ‖Σ_{n ≤ x} a(n)‖ ≤ C(D, ε) q^ε x^{σ₀+4ε} for
    x ≥ 1, with an explicit C(D, ε).
  - `sum_bound_B`: the same, assuming only ‖a(n)‖ ≤ B for n ≤ 2x, with 2B in place of 2 in the
    constant.
- **Lean.** `LiouvilleEnergyRH.Contour.sum_bound`, `corollaries/LiouvilleEnergyRH/Mertens/Contour.lean`;
  `LiouvilleEnergyRH.Contour.sum_bound_B`, `corollaries/LiouvilleEnergyRH/PrimeCount/ContourB.lean`.
- **Assumes.** Holomorphy of F on Re z > σa, as an explicit argument; no zero-free hypothesis.
- **Axioms.** `sum_bound`: `[propext, Classical.choice, Quot.sound]`;
  `sum_bound_B`: `[propext, Classical.choice, Quot.sound]`

---

## 3. Chowla-type results for the Liouville function

The theorems in 3.1–3.11 are in the namespace `LiouvilleEnergyRH.Unconditional` and have no
hypothesis argument. They use the definitions of `corollaries/ChowlaRH/`:

- `lam n = λ(n)`, as a real number;
- `corr H n = ∏_{h ∈ H} λ(n + h)`;
- `wavg w f N = (Σ_{1 ≤ n ≤ N} w(n) f(n)) / Σ_{1 ≤ n ≤ N} w(n)`, with `natW = 1` (natural
  density);
- `ChowlaAt w H`: `wavg w (corr H) N → 0`;
- `ChowlaOrder w k`: `ChowlaAt w H` for every set H of k shifts;
- `patternInd H ε n = 1` if λ(n + h) = ε(h) for all h ∈ H, and 0 otherwise.

### 3.1 The summatory Liouville function, L(N) ≪ N^{7/8+ε}

- **Statement.** For every ε > 0 there is C with |L(N)| ≤ C N^{7/8+ε} for every N ∈ ℕ
  (`ChowlaRH.LiouvilleBound (7/8 + ε)`).
- **Lean.** `LiouvilleEnergyRH.Unconditional.liouvilleBound`,
  `corollaries/LiouvilleEnergyRH/Unconditional.lean`.
- **Assumes.** Nothing. Proof: 1.17 and `ChowlaRH.liouvilleBound_of_mertensBound` (3.12).
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 3.2 L(N) = o(N)

- **Statement.** (1/N) Σ_{1 ≤ n ≤ N} λ(n) → 0 as N → ∞.
- **Lean.** `LiouvilleEnergyRH.Unconditional.liouville_mean_zero`,
  `corollaries/LiouvilleEnergyRH/Unconditional.lean`.
- **Assumes.** Nothing. Proof: 3.3 with H = {0}.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 3.3 One-point Chowla

- **Statement.** `ChowlaOrder natW 1`: for every h ∈ ℕ, (1/N) Σ_{1 ≤ n ≤ N} λ(n + h) → 0.
- **Lean.** `LiouvilleEnergyRH.Unconditional.chowla_one`,
  `corollaries/LiouvilleEnergyRH/Unconditional.lean`.
- **Assumes.** Nothing. Proof: 3.1 with ε = 1/16 and `ChowlaRH.chowlaAt_single_of_liouvilleBound`
  (3.13).
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 3.4 Each sign of λ has density 1/2

- **Statement.** For every k ∈ ℕ and e ∈ {1, −1},
  #{1 ≤ n ≤ N : λ(n + k) = e} / N → 1/2 (stated as `wavg natW (patternInd {k} (fun _ => e)) → 1/2`).
- **Lean.** `LiouvilleEnergyRH.Unconditional.sign_density`,
  `corollaries/LiouvilleEnergyRH/Unconditional.lean`.
- **Assumes.** Nothing. Proof: 3.3 and `ChowlaRH.tendsto_pattern` (3.14).
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 3.5 Shifted sums, uniform in the shift

- **Statement.** For every ε > 0 there is C with |Σ_{1 ≤ n ≤ N} λ(n + k)| ≤ C (N + k)^{7/8+ε}
  for all k, N ∈ ℕ.
- **Lean.** `LiouvilleEnergyRH.Unconditional.shifted_sum_bound`,
  `corollaries/LiouvilleEnergyRH/Unconditional.lean`.
- **Assumes.** Nothing. Proof: 3.1.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 3.6 |λ(n)| ≤ 1

- **Statement.** |λ(n)| ≤ 1 for every n ∈ ℕ (with λ(0) = 0 in Mathlib). This is a helper lemma.
- **Lean.** `LiouvilleEnergyRH.Unconditional.abs_lam_le`,
  `corollaries/LiouvilleEnergyRH/Unconditional.lean`.
- **Assumes.** Nothing.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 3.7 Two-point correlations averaged over the shift

- **Statement.** For every ε > 0 there is C ≥ 0 with
  |Σ_{1 ≤ h ≤ H} Σ_{1 ≤ n ≤ N} λ(n) λ(n + h)| ≤ C N (N + H)^{7/8+ε} for all N, H ∈ ℕ.
- **Lean.** `LiouvilleEnergyRH.Unconditional.two_point_shift_average`,
  `corollaries/LiouvilleEnergyRH/Unconditional.lean`.
- **Assumes.** Nothing. Proof: 3.5 and 3.6.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 3.8 Liouville correlations on two affine forms (OpenAI's theorem, restated)

- **Statement.** There is c > 0 with the following property. For all natural numbers a₁, a₂ > 0
  and b₁, b₂ with a₁b₂ ≠ a₂b₁, there is C > 0 such that for every real X ≥ 3,
  |Σ_{1 ≤ n ≤ ⌊X⌋} λ(a₁n + b₁) λ(a₂n + b₂)| ≤ C X / (log X)^c.
- **Lean.** `LiouvilleEnergyRH.Unconditional.liouville_affine_correlation`,
  `corollaries/LiouvilleEnergyRH/TwoPointChowla.lean`.
- **Assumes.** Nothing. Proof: (O3), restated with a real-valued sum and absolute value.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 3.9 Two-point Chowla

- **Statement.** For every h ≥ 1, (1/N) Σ_{1 ≤ n ≤ N} λ(n) λ(n + h) → 0 as N → ∞.
- **Lean.** `LiouvilleEnergyRH.Unconditional.liouville_two_point`,
  `corollaries/LiouvilleEnergyRH/TwoPointChowla.lean`.
- **Assumes.** Nothing. Proof: 3.8 with a₁ = a₂ = 1, b₁ = 0, b₂ = h.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 3.10 Two-point Chowla in the notation of `ChowlaRH`

- **Statement.** `ChowlaAt natW {0, h}` for every h ≥ 1.
- **Lean.** `LiouvilleEnergyRH.Unconditional.chowlaAt_pair`,
  `corollaries/LiouvilleEnergyRH/TwoPointChowla.lean`.
- **Assumes.** Nothing. Proof: 3.9.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 3.11 Two-point sign patterns of λ

- **Statement.** For every h ≥ 1 and all ε₁, ε₂ ∈ {1, −1}:
  - `liouville_sign_pair` (N ∈ ℕ):
    #{1 ≤ n ≤ N : λ(n) = ε₁, λ(n + h) = ε₂} / N → 1/4 as N → ∞;
  - `liouville_sign_pair_real` (x ∈ ℝ):
    #{1 ≤ n ≤ ⌊x⌋ : λ(n) = ε₁, λ(n + h) = ε₂} / x → 1/4 as x → ∞.
- **Lean.** `LiouvilleEnergyRH.Unconditional.liouville_sign_pair` and
  `LiouvilleEnergyRH.Unconditional.liouville_sign_pair_real`,
  `corollaries/LiouvilleEnergyRH/TwoPointChowla.lean`.
- **Assumes.** Nothing. Proof: `ChowlaRH.tendsto_pattern` (3.14) on H = {0, h}, with 3.3 for the
  one-element subsets and 3.10 for H itself.
- **Axioms.** `liouville_sign_pair`: `[propext, Classical.choice, Quot.sound]`;
  `liouville_sign_pair_real`: `[propext, Classical.choice, Quot.sound]`

### 3.12 From M(N) to L(N)

- **Statement.** If 1/2 < θ and |M(N)| ≤ C N^θ for all N, then |L(N)| ≤ C′ N^θ for all N.
- **Lean.** `ChowlaRH.liouvilleBound_of_mertensBound`, `corollaries/ChowlaRH/MertensTransfer.lean`.
- **Assumes.** `MertensBound θ`, as an explicit argument.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 3.13 One-point Chowla from a power bound for L(N)

- **Statement.** If 0 ≤ θ < 1 and |L(N)| ≤ C N^θ for all N, then `ChowlaAt natW {h}` holds for
  every h ∈ ℕ.
- **Lean.** `ChowlaRH.chowlaAt_single_of_liouvilleBound`, `corollaries/ChowlaRH/Chowla.lean`.
- **Assumes.** `LiouvilleBound θ`, as an explicit argument.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

### 3.14 Sign patterns from correlations

- **Statement.** Let w(n) > 0 for n > 0, let H be a finite set of shifts and let ε : H → {1, −1}.
  If `ChowlaAt w S` holds for every nonempty S ⊆ H, then the w-density of
  {n : λ(n + h) = ε(h) for all h ∈ H} is 2^{−|H|}.
- **Lean.** `ChowlaRH.tendsto_pattern`, `corollaries/ChowlaRH/SignPatterns.lean`.
- **Assumes.** `ChowlaAt w S` for the nonempty S ⊆ H, as an explicit argument.
- **Axioms.** `[propext, Classical.choice, Quot.sound]`

---

## 4. The cited OpenAI theorems

- (O1) `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`:
  `[propext, Classical.choice, Quot.sound]`
- (O2) `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`:
  `[propext, Classical.choice, Quot.sound]`
- (O3) `OAI.OrdinaryTwoPointCorrelations.liouville_log_saving`:
  `[propext, Classical.choice, Quot.sound]`

These theorems are proved in the vendored library. It contains 4,463 files from
https://github.com/openai/math, copied unchanged, and the 42 files it imports from
PrimeNumberTheoremAnd, StrongPNT and RellichKondrachov (see `NOTICE`). A text search of the
vendored files finds no `sorry`, `axiom`, `native_decide`, `ofReduceBool` or `implemented_by`.

## 5. The analytic core of the window theorem

The window theorem itself rests on Galois representations of CM fields and is not formalized
here. Its analytic steps are, in
[`LiouvilleEnergyRH/WindowBalance.lean`](LiouvilleEnergyRH/WindowBalance.lean), written
independently of the formal proof of the window theorem. Throughout, A = x^{1/2},
E = x^{ε/8} and W = x^{Cε}. None of these theorems assumes anything beyond its stated
inequalities, and each depends only on `propext`, `Classical.choice` and `Quot.sound`
(see [`axioms.txt`](axioms.txt)).

| Step | Lean name | Statement |
|---|---|---|
| Zhang's Lemma 6.1 (balancing) | `balance_core` | From the balancing inequality and the eight size conditions on the parameters, z ≤ 26 A W E²¹. |
| Zhang's Lemma 6.1, real-power form | `zhang_lemma_6_1` | For x ≥ 3, ε > 0, C ≥ 0: z ≤ 26 x^{1/2 + (C + 21/8) ε}. |
| Absorbing the constant | `balance_core_final` | If 26 ≤ E³, then z ≤ A W E²⁴, that is z ≤ x^{1/2 + (C+3) ε}. |
| Optimality, first step | `optimal_core` | A²/m + 2 m E⁸ ≤ 2B/Q, where B is the bracket on the right of the balancing inequality and Q = t m b, under A² b/2 ≤ a and t ≤ 2n. |
| Optimality, second step | `optimal_amgm` | 2√2 A E⁴ ≤ A²/m + 2 m E⁸ for every m > 0, so no choice of m beats the exponent 1/2. |
| Rate function of the gamma law | `rate_pos` | v − 1 − log v > 0 for v > 0, v ≠ 1. |
| Zhang's Lemma 2.2: the constant | `gamma_rate_pos` | c_δ = min(I(1/τ), I(b_δ)) > 0 for τ = 1 + δ/2, b_δ = (1+δ)/(1+3δ/4). |
| Zhang's Lemma 2.2: the integer k | `gamma_k_bounds` | k = ⌊q τ U⌋ satisfies U ≤ k ≤ q τ U when q τ ≥ 2 and U ≥ 1. |
| Zhang's Lemma 2.2: the window | `gamma_window` | (1+δ)/(τ + 1/(qU)) ≥ b_δ when U ≥ 4/(qδ). |
| Zhang's Lemma 2.2: the last step | `gamma_final` | 2 (q e^{c})^{−(k+1)} ≤ (q+2)^{−k} when q ≥ 2, c > 0 and q ≥ 2/(e^c − 1). |

All names in this table are in the namespace `LiouvilleEnergyRH.WindowBalance`.
