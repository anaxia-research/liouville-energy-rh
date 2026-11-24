import LiouvilleEnergyRH.Corollaries
import LiouvilleEnergyRH.NonResidue
import LiouvilleEnergyRH.MoreCorollaries
import LiouvilleEnergyRH.Progressions.AP
import LiouvilleEnergyRH.Lindelof.Strip
import ChowlaRH
import OAI.NumberTheory.DirichletL.Nonvanishing

/-!
# Unconditional corollaries of the zero-free half-plane `re s > 7/8`

OpenAI's theorem `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`
(the Lean library of https://github.com/openai/math, Apache 2.0) states that no Dirichlet
`L`-function vanishes in `re s > 7/8`, apart from the pole of `ζ` at `s = 1`. It discharges the
hypothesis `Vinogradov.Main.ZeroFree` of the library `Vinogradov`, and the zero-free half-plane
`re s > σa` assumed by the generalized files `LiouvilleEnergyRH/Mertens`, `PrimeCount`,
`Progressions`, `Lindelof/Strip` at `σa = 7/8`. Every theorem below is proved with no hypothesis.

* The half-plane: `LFunction_ne_zero`, `riemannZeta_ne_zero`, `zeroFree`.
* Character sums and primitive roots: `polya_vinogradov`, `least_nonresidue`,
  `least_prime_primitive_root`, `least_prime_primitive_root_bound`, `erdos_985`,
  `character_sum_le_rpow`, `character_sum_bound`, `lindelof_bound`, `prime_sum_bound`,
  `logDeriv_one_bound`, `euler_kronecker_bound`.
* `ζ` and the Möbius and Liouville functions: `zeta_strip_bound`, `zeta_inv_bound`,
  `mertensBound` (`M(N) ≪ N^{7/8+ε}`), `moebius_mean_zero`, `liouvilleBound`
  (`L(N) ≪ N^{7/8+ε}`),
  `liouville_mean_zero` (`∑_{n ≤ N} λ(n) = o(N)`), `chowla_one`, `sign_density`,
  `shifted_sum_bound`, `two_point_shift_average`.
* Primes: `psi_bound` (`ψ(x) = x + O(x^{7/8+η})`), `theta_bound`, `prime_in_short_interval`
  (a prime in `(x, x + x^{7/8+η}]`), `psi_div_tendsto_one`, `prime_gap`, `chi_psi_bound`, `psiAP_bound` (primes in progressions
  with a power saving), `least_prime_in_AP` (`p ≤ C q^{8+d}`).
-/

namespace LiouvilleEnergyRH.Unconditional

open Complex Filter Topology Finset ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction.Moebius

/-! ### The zero-free half-plane -/

/-- **The quasi-Riemann hypothesis** (OpenAI). No Dirichlet `L`-function vanishes in
`re s > 7/8`, apart from the pole of `ζ` at `s = 1`. -/
theorem LFunction_ne_zero (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : 7 / 8 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) : DirichletCharacter.LFunction χ s ≠ 0 :=
  OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs
    (fun h => hχs.elim (fun h' => h' h.1) (fun h' => h' h.2))

/-- `ζ(s) ≠ 0` for `re s > 7/8`. -/
theorem riemannZeta_ne_zero (s : ℂ) (hs : 7 / 8 < s.re) : riemannZeta s ≠ 0 :=
  OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

/-- The hypothesis `ZeroFree` of the library `Vinogradov`, proved. -/
theorem zeroFree : Vinogradov.Main.ZeroFree :=
  fun q _ χ hχ z hz => LFunction_ne_zero q χ z hz (Or.inl hχ)

instance instFactZeroFree : Fact Vinogradov.Main.ZeroFree := ⟨zeroFree⟩

theorem zeta_ne_zero_of_lt : ∀ s : ℂ, 7 / 8 < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
  fun s hs _ => riemannZeta_ne_zero s hs

/-! ### Character sums, primitive roots and `L'/L(1, χ)` -/

/-- **Pólya–Vinogradov with `log log q`**: `‖∑_{n ≤ T} χ(n)‖ ≤ C √q log log q` for every
primitive `χ` modulo `q ≥ 3`. -/
theorem polya_vinogradov :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      3 ≤ q → ∀ T : ℕ,
        ‖∑ n ∈ Finset.Ioc 0 T, (χ n : ℂ)‖ ≤ C * Real.sqrt q * Real.log (Real.log q) :=
  Vinogradov.PV.polya_vinogradov_loglog

/-- **The least character non-residue**: for every nonprincipal `χ` modulo a prime `p` some
`n ≤ C p^ε` has `χ(n) ≠ 1`. -/
theorem least_nonresidue {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p), χ ≠ 1 →
      ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ C * (p : ℝ) ^ ε ∧ χ n ≠ 1 :=
  least_nonresidue_of_zeroFree zeroFree hε

/-- **The least prime primitive root**: every prime `p` has a prime primitive root
`ℓ ≤ C p^ε`. -/
theorem least_prime_primitive_root {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∃ ℓ : ℕ, ℓ.Prime ∧ orderOf (ℓ : ZMod p) = p - 1 ∧
      (ℓ : ℝ) ≤ C * (p : ℝ) ^ ε :=
  Vinogradov.Main.least_prime_primitive_root_le_rpow zeroFree hε

/-- Every prime `p` has a prime primitive root `ℓ ≤ C (τ(p-1)² log (p + 2))^{8+η}`. -/
theorem least_prime_primitive_root_bound {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∃ ℓ : ℕ, ℓ.Prime ∧ orderOf (ℓ : ZMod p) = p - 1 ∧
      (ℓ : ℝ) ≤ C * (((p - 1).divisors.card : ℝ) ^ 2 * Real.log (p + 2)) ^ (8 + η) :=
  Vinogradov.Main.least_prime_primitive_root_bound zeroFree hη

/-- **Erdős Problem 985 for large primes**: every prime `p ≥ p₀` has a prime `q < p` that is a
primitive root modulo `p`. -/
theorem erdos_985 :
    ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p →
      ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 :=
  Vinogradov.Main.erdos_985_of_large zeroFree

/-- **Character sums**: for `θ > 7/8` and `η > 0`, `‖∑_{n ≤ x} χ(n)‖ ≤ C x^θ` for every
nonprincipal `χ` modulo `q` and every `x ≥ q^η`. -/
theorem character_sum_le_rpow {η θ : ℝ} (hη : 0 < η) (hθ : 7 / 8 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x → (q : ℝ) ^ η ≤ x →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n‖ ≤ C * x ^ θ :=
  Vinogradov.CharSum.character_sum_le_rpow hη hθ

/-- **Character sums**, `‖∑_{n ≤ x} χ(n)‖ ≤ C q^w x^{7/8 + w}`. -/
theorem character_sum_bound {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n‖ ≤ C * (q : ℝ) ^ w * x ^ (7 / 8 + w) :=
  Vinogradov.CharSum.character_sum_bound hw

/-- **Lindelöf bound to the right of `7/8`**: `‖L(s, χ)‖ + ‖L(s, χ)⁻¹‖ ≤ C (q (3 + |t|))^w`
for nonprincipal `χ` and `re s ≥ 7/8 + w`. -/
theorem lindelof_bound {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 7 / 8 + w ≤ s.re →
        ‖DirichletCharacter.LFunction χ s‖ + ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤
          C * ((q : ℝ) * (3 + |s.im|)) ^ w :=
  Vinogradov.CharSum.lindelof hw

/-- **Primes twisted by a character**, `‖∑_{p ≤ x} χ(p) log p‖ ≤ C x^{19/20} log (q + 2)`. -/
theorem prime_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m] (ξ : DirichletCharacter ℂ m), ξ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (ξ p : ℂ) * Real.log p‖ ≤
          C * x ^ (19 / 20 : ℝ) * Real.log (m + 2) :=
  Vinogradov.PV.prime_sum_bound

/-- **The logarithmic derivative at `s = 1`**, `|L'/L(1, χ)| ≤ C log log (q + 2)`. -/
theorem logDeriv_one_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
        C * Real.log (Real.log (q + 2)) :=
  Vinogradov.EulerKronecker.logDeriv_one_le_of_zeroFree zeroFree

/-- **Euler–Kronecker constants of `ℚ(ζ_q)`**: for primes `q ≥ 3`, the sum of `L'/L(1, χ)` over
the nonprincipal characters lies in `[-C log q log log q, C log q]`. -/
theorem euler_kronecker_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], q.Prime → 3 ≤ q → ∃ r : ℝ,
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 = r ∧
        -(C * Real.log q * Real.log (Real.log q)) ≤ r ∧ r ≤ C * Real.log q :=
  Vinogradov.EulerKronecker.sum_logDeriv_one_of_zeroFree zeroFree

/-! ### `ζ` to the right of `7/8` -/

/-- `ζ(σ + it) ≪ (3 + |t|)^η` uniformly on `7/8 + d ≤ σ ≤ 1 - d`. -/
theorem zeta_strip_bound {d η : ℝ} (hd : 0 < d) (hη : 0 < η) :
    ∃ K : ℝ, ∀ σ t : ℝ, 7 / 8 + d ≤ σ → σ ≤ 1 - d →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K * (3 + |t|) ^ η := by
  set e := min (d / 8) (1 / 2000) with he_def
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he' : e < 1 / 1000 := (min_le_right _ _).trans_lt (by norm_num)
  have he8 : 8 * e ≤ d := by have := min_le_left (d / 8) (1 / 2000); linarith
  obtain ⟨D, -, hD⟩ := Lindelof.zeta_strip_bound (σa := 7 / 8) (b := 1 - d) (by norm_num)
    (by norm_num) (by linarith) zeta_ne_zero_of_lt he he' (show 0 < η / 2 by linarith)
  refine ⟨D * 2 ^ (η / 2), fun σ t h1 h2 => ?_⟩
  have hb := hD σ t (by linarith) h2
  have h3 : (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ (η / 2) = 2 ^ (η / 2) * (3 + |t|) ^ η := by
    rw [Nat.cast_one, mul_one, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    congr 2
    push_cast
    ring
  calc _ ≤ D * (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ (η / 2) := hb
    _ = D * 2 ^ (η / 2) * (3 + |t|) ^ η := by rw [h3]; ring

/-- `1/ζ(σ + it) ≪ (3 + |t|)^η` uniformly on `7/8 + d ≤ σ ≤ 2`, `σ + it ≠ 1`. -/
theorem zeta_inv_bound {d η : ℝ} (hd : 0 < d) (hη : 0 < η) :
    ∃ K : ℝ, ∀ σ t : ℝ, 7 / 8 + d ≤ σ → σ ≤ 2 → (σ : ℂ) + (t : ℂ) * I ≠ 1 →
      ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ K * (3 + |t|) ^ η := by
  set e := min (d / 8) (1 / 2000) with he_def
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he' : e < 1 / 1000 := (min_le_right _ _).trans_lt (by norm_num)
  have he8 : 8 * e ≤ d := by have := min_le_left (d / 8) (1 / 2000); linarith
  obtain ⟨D, -, hD⟩ := Mertens.invZeta_bound (σa := 7 / 8) (by norm_num) (by norm_num)
    zeta_ne_zero_of_lt he he' (show 0 < η / 2 by linarith)
  refine ⟨D * 2 ^ (η / 2), fun σ t h1 h2 hne => ?_⟩
  have hb := hD σ t (by linarith) h2
  rw [Mertens.invZeta_eq hne] at hb
  have h3 : (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ (η / 2) = 2 ^ (η / 2) * (3 + |t|) ^ η := by
    rw [Nat.cast_one, mul_one, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    congr 2
    push_cast
    ring
  calc _ ≤ D * (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ (η / 2) := hb
    _ = D * 2 ^ (η / 2) * (3 + |t|) ^ η := by rw [h3]; ring

/-! ### The Möbius and Liouville functions -/

/-- **The Mertens function**: `|M(N)| ≤ C N^{7/8 + ε}`. -/
theorem mertensBound {ε : ℝ} (hε : 0 < ε) : ChowlaRH.MertensBound (7 / 8 + ε) := by
  obtain ⟨K, hK⟩ := Mertens.mertens_bound (σa := 7 / 8) (by norm_num) le_rfl
    zeta_ne_zero_of_lt hε
  refine ⟨max K 0, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [ChowlaRH.mertens, Ioc_self, sum_empty, Int.cast_zero, abs_zero, Nat.cast_zero]
    exact mul_nonneg (le_max_right _ _) (by positivity)
  · have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hb := hK N hx
    rw [Nat.floor_natCast] at hb
    have hcast : ‖∑ n ∈ Ioc 0 N, ((μ n : ℤ) : ℂ)‖ = |(ChowlaRH.mertens N : ℝ)| := by
      rw [ChowlaRH.mertens, ← Complex.norm_intCast]
      push_cast
      rfl
    have hp : 0 ≤ (N : ℝ) ^ (7 / 8 + ε) := by positivity
    calc |(ChowlaRH.mertens N : ℝ)| = ‖∑ n ∈ Ioc 0 N, ((μ n : ℤ) : ℂ)‖ := hcast.symm
      _ ≤ K * (N : ℝ) ^ (7 / 8 + ε) := hb
      _ ≤ max K 0 * (N : ℝ) ^ (7 / 8 + ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hp

/-- **`∑_{n ≤ N} μ(n) = o(N)`.** -/
theorem moebius_mean_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (μ n : ℝ)) / N) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := mertensBound (ε := 1 / 16) (by norm_num)
  have hlim : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(1 / 16 : ℝ))) atTop (𝓝 0) := by
    have h2 := ((tendsto_rpow_neg_atTop (y := 1 / 16) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul C
    rw [mul_zero] at h2
    exact h2
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hI : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  have hM : (∑ n ∈ Icc 1 N, (μ n : ℝ)) = (ChowlaRH.mertens N : ℝ) := by
    rw [hI, ChowlaRH.mertens]; push_cast; rfl
  rw [hM, Real.norm_eq_abs, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
  calc |(ChowlaRH.mertens N : ℝ)| ≤ C * (N : ℝ) ^ (7 / 8 + 1 / 16) := hC N
    _ = C * (N : ℝ) ^ (-(1 / 16 : ℝ)) * N := by
        rw [mul_assoc, ← Real.rpow_add_one hNpos.ne']; norm_num

/-- **The summatory Liouville function**: `|L(N)| ≤ C N^{7/8 + ε}`. -/
theorem liouvilleBound {ε : ℝ} (hε : 0 < ε) : ChowlaRH.LiouvilleBound (7 / 8 + ε) :=
  ChowlaRH.liouvilleBound_of_mertensBound (by linarith) (mertensBound hε)

/-- **One-point Chowla**: `(1/N) ∑_{n ≤ N} λ(n + h) → 0` for every shift `h`. -/
theorem chowla_one : ChowlaRH.ChowlaOrder ChowlaRH.natW 1 := by
  intro H hH
  obtain ⟨h, rfl⟩ := card_eq_one.mp hH
  exact ChowlaRH.chowlaAt_single_of_liouvilleBound (θ := 7 / 8 + 1 / 16) (by norm_num)
    (by norm_num) (liouvilleBound (by norm_num)) h

/-- **The prime number theorem for `λ`**: `(1/N) ∑_{n ≤ N} λ(n) → 0`. -/
theorem liouville_mean_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (liouville n : ℝ)) / N) atTop (𝓝 0) := by
  have h := chowla_one {0} (card_singleton 0)
  unfold ChowlaRH.ChowlaAt at h
  refine h.congr' (Eventually.of_forall fun N => ?_)
  have hI : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  simp only [ChowlaRH.wavg, ChowlaRH.natW, ChowlaRH.corr, prod_singleton, add_zero, one_mul,
    sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_one, hI, ChowlaRH.lam]

/-- **Signs of `λ`**: each value `λ(n + h) = ±1` has natural density `1/2`. -/
theorem sign_density (k : ℕ) {e : ℝ} (he : e = 1 ∨ e = -1) :
    Tendsto (ChowlaRH.wavg ChowlaRH.natW (ChowlaRH.patternInd {k} (fun _ => e))) atTop
      (𝓝 (1 / 2)) := by
  have := ChowlaRH.tendsto_pattern ChowlaRH.natW ChowlaRH.natW_pos {k} (ε := fun _ => e)
    (fun _ _ => he) fun S hS hne => by
      have : S = {k} := (subset_singleton_iff.mp hS).resolve_left (nonempty_iff_ne_empty.mp hne)
      subst this
      exact chowla_one {k} (card_singleton k)
  simpa using this

/-- **Shifted sums, uniformly in the shift**: `|∑_{1 ≤ n ≤ N} λ(n + h)| ≤ C (N + h)^{7/8 + ε}`.
(The proof is that of `shifted_sum_bound` in `AveragedChowla.lean` of
anaxia-research/averaged-chowla-grh, with `1/2` replaced by `7/8`.) -/
theorem shifted_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ k N : ℕ,
      |∑ n ∈ Ioc 0 N, ChowlaRH.lam (n + k)| ≤ C * ((N + k : ℕ) : ℝ) ^ (7 / 8 + ε) := by
  obtain ⟨C, hC⟩ := liouvilleBound hε
  refine ⟨2 * max C 0, fun k N => ?_⟩
  rw [ChowlaRH.sum_shift_eq]
  have hθ : 0 ≤ 7 / 8 + ε := by linarith
  have h1 := hC (N + k)
  have h2 := hC k
  have hmono : (k : ℝ) ^ (7 / 8 + ε) ≤ ((N + k : ℕ) : ℝ) ^ (7 / 8 + ε) :=
    Real.rpow_le_rpow (by positivity) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) N]) hθ
  have hp1 : 0 ≤ ((N + k : ℕ) : ℝ) ^ (7 / 8 + ε) := by positivity
  have hp2 : 0 ≤ (k : ℝ) ^ (7 / 8 + ε) := by positivity
  have hm : C ≤ max C 0 := le_max_left _ _
  have hm0 : 0 ≤ max C 0 := le_max_right _ _
  calc |(ChowlaRH.summatoryLiouville (N + k) : ℝ) - (ChowlaRH.summatoryLiouville k : ℝ)|
      ≤ |(ChowlaRH.summatoryLiouville (N + k) : ℝ)| + |(ChowlaRH.summatoryLiouville k : ℝ)| :=
        abs_sub _ _
    _ ≤ C * ((N + k : ℕ) : ℝ) ^ (7 / 8 + ε) + C * (k : ℝ) ^ (7 / 8 + ε) := add_le_add h1 h2
    _ ≤ max C 0 * ((N + k : ℕ) : ℝ) ^ (7 / 8 + ε) +
          max C 0 * ((N + k : ℕ) : ℝ) ^ (7 / 8 + ε) := by
        gcongr
    _ = 2 * max C 0 * ((N + k : ℕ) : ℝ) ^ (7 / 8 + ε) := by ring

theorem abs_lam_le (n : ℕ) : |ChowlaRH.lam n| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ChowlaRH.lam]
  · rcases ChowlaRH.lam_eq_or hn.ne' with h | h <;> simp [h]

/-- **Two-point correlations averaged over the shift**:
`|∑_{1 ≤ h ≤ H} ∑_{1 ≤ n ≤ N} λ(n) λ(n + h)| ≤ C N (N + H)^{7/8 + ε}`. (The proof is that of
`two_point_shift_average` in `AveragedChowla.lean` of anaxia-research/liouville-energy-rh, with
`1/2` replaced by `7/8`.) -/
theorem two_point_shift_average (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N H : ℕ,
      |∑ k ∈ Ioc 0 H, ∑ n ∈ Ioc 0 N, ChowlaRH.lam n * ChowlaRH.lam (n + k)|
        ≤ C * N * ((N + H : ℕ) : ℝ) ^ (7 / 8 + ε) := by
  obtain ⟨C, hC⟩ := shifted_sum_bound ε hε
  refine ⟨max C 0, le_max_right _ _, fun N H => ?_⟩
  have hθ : 0 ≤ 7 / 8 + ε := by linarith
  rw [Finset.sum_comm]
  have hterm : ∀ n ∈ Ioc 0 N,
      |∑ k ∈ Ioc 0 H, ChowlaRH.lam n * ChowlaRH.lam (n + k)| ≤
        max C 0 * ((N + H : ℕ) : ℝ) ^ (7 / 8 + ε) := by
    intro n hn
    have hnN : n ≤ N := (Finset.mem_Ioc.mp hn).2
    rw [← Finset.mul_sum, abs_mul]
    have hs : |∑ k ∈ Ioc 0 H, ChowlaRH.lam (n + k)| ≤ C * ((H + n : ℕ) : ℝ) ^ (7 / 8 + ε) := by
      have := hC n H
      simpa [add_comm] using this
    have hmono : ((H + n : ℕ) : ℝ) ^ (7 / 8 + ε) ≤ ((N + H : ℕ) : ℝ) ^ (7 / 8 + ε) :=
      Real.rpow_le_rpow (by positivity)
        (by push_cast; exact_mod_cast (by omega : H + n ≤ N + H)) hθ
    have hp : 0 ≤ ((H + n : ℕ) : ℝ) ^ (7 / 8 + ε) := by positivity
    calc |ChowlaRH.lam n| * |∑ k ∈ Ioc 0 H, ChowlaRH.lam (n + k)|
        ≤ 1 * |∑ k ∈ Ioc 0 H, ChowlaRH.lam (n + k)| :=
          mul_le_mul_of_nonneg_right (abs_lam_le n) (abs_nonneg _)
      _ ≤ C * ((H + n : ℕ) : ℝ) ^ (7 / 8 + ε) := by rw [one_mul]; exact hs
      _ ≤ max C 0 * ((H + n : ℕ) : ℝ) ^ (7 / 8 + ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hp
      _ ≤ max C 0 * ((N + H : ℕ) : ℝ) ^ (7 / 8 + ε) :=
          mul_le_mul_of_nonneg_left hmono (le_max_right _ _)
  calc |∑ n ∈ Ioc 0 N, ∑ k ∈ Ioc 0 H, ChowlaRH.lam n * ChowlaRH.lam (n + k)|
      ≤ ∑ n ∈ Ioc 0 N, |∑ k ∈ Ioc 0 H, ChowlaRH.lam n * ChowlaRH.lam (n + k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, max C 0 * ((N + H : ℕ) : ℝ) ^ (7 / 8 + ε) := Finset.sum_le_sum hterm
    _ = max C 0 * N * ((N + H : ℕ) : ℝ) ^ (7 / 8 + ε) := by
        rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]; ring

/-! ### Primes -/

/-- **`ψ(x) = x + O(x^{7/8 + η})`.** -/
theorem psi_bound {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x → |Chebyshev.psi x - x| ≤ K * x ^ (7 / 8 + η) :=
  PrimeCount.psi_bound (by norm_num) le_rfl zeta_ne_zero_of_lt hη

/-- **`θ(x) = x + O(x^{7/8 + η})`.** -/
theorem theta_bound {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → |Chebyshev.theta x - x| ≤ K * x ^ (7 / 8 + η) :=
  PrimeCount.theta_bound (by norm_num) le_rfl zeta_ne_zero_of_lt hη

/-- **Primes in short intervals**: for `0 < η ≤ 1/8`, every interval `(x, x + x^{7/8 + η}]`
with `x ≥ x₀(η)` contains a prime. -/
theorem prime_in_short_interval {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 8) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ (7 / 8 + η) :=
  PrimeCount.prime_in_short_interval (by norm_num) le_rfl zeta_ne_zero_of_lt hη (by linarith)

/-- **The prime number theorem**, `ψ(x) / x → 1`. -/
theorem psi_div_tendsto_one : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  obtain ⟨K, hK⟩ := psi_bound (η := 1 / 16) (by norm_num)
  have hlim : Tendsto (fun x : ℝ => K * x ^ (-(1 / 16 : ℝ))) atTop (𝓝 0) := by
    have h2 := (tendsto_rpow_neg_atTop (y := 1 / 16) (by norm_num)).const_mul K
    rw [mul_zero] at h2
    exact h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, show Chebyshev.psi x / x - 1 = (Chebyshev.psi x - x) / x by
    rw [sub_div, div_self hx0.ne'], abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
  calc |Chebyshev.psi x - x| ≤ K * x ^ (7 / 8 + 1 / 16) := hK x hx
    _ = K * x ^ (-(1 / 16 : ℝ)) * x := by
        rw [mul_assoc, ← Real.rpow_add_one hx0.ne']; norm_num

/-- **Gaps between primes**: for `0 < η ≤ 1/8`, every prime `p ≥ p₀(η)` is followed by a prime
`q ≤ p + p^{7/8 + η}`. -/
theorem prime_gap {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 8) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p →
      ∃ q : ℕ, q.Prime ∧ p < q ∧ (q : ℝ) ≤ p + (p : ℝ) ^ (7 / 8 + η) := by
  obtain ⟨x₀, hx₀⟩ := prime_in_short_interval hη hη1
  refine ⟨⌈x₀⌉₊, fun p _ hp => ?_⟩
  obtain ⟨q, hq, hpq, hqle⟩ := hx₀ p (Nat.ceil_le.mp hp)
  exact ⟨q, hq, by exact_mod_cast hpq, hqle⟩

/-- **Twisted von Mangoldt sums**: `‖∑_{n ≤ x} χ(n) Λ(n)‖ ≤ K q^η x^{7/8 + η}` for every
nonprincipal `χ` modulo `q`. -/
theorem chi_psi_bound {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * (vonMangoldt n : ℂ)‖ ≤ K * (q : ℝ) ^ η * x ^ (7 / 8 + η) :=
  Progressions.chi_psi_bound (by norm_num) le_rfl zeroFree hη

/-- **Primes in arithmetic progressions with a power saving**:
`|φ(q) ψ(x; q, a) - x| ≤ K q^{1 + η} x^{7/8 + η}` for `a` coprime to `q` and `x ≥ 1`, where
`ψ(x; q, a) = ∑_{n ≤ x, n ≡ a (mod q)} Λ(n)`. -/
theorem psiAP_bound {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a → ∀ x : ℝ, 1 ≤ x →
      |(q.totient : ℝ) *
          ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => (n : ZMod q) = a), vonMangoldt n - x| ≤
        K * (q : ℝ) ^ (1 + η) * x ^ (7 / 8 + η) :=
  Progressions.psiAP_bound (by norm_num) le_rfl zeroFree zeta_ne_zero_of_lt hη

/-- **The least prime in a progression**: for `0 < d ≤ 1` there is `C` with a prime
`p ≡ a (mod q)`, `p ≤ C q^{8 + d}`, whenever `gcd(a, q) = 1`. -/
theorem least_prime_in_AP {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ C * (q : ℝ) ^ (8 + d) :=
  Progressions.least_prime_in_AP_seven_eighths zeroFree zeta_ne_zero_of_lt hd hd1

end LiouvilleEnergyRH.Unconditional
