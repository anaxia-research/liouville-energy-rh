import Mathlib
import ReadableRH.Powers

/-!
# The least Mills constant

Corollary `GH:cor:powers` (ii) of the paper. Let `millsSeq 0 = 2` and let `millsSeq (k + 1)`
be the least prime larger than `millsSeq k ^ 3`; so `millsSeq k` is `Q_(k+1)` of the paper.
If every interval `(n ^ 3, (n + 1) ^ 3)` with `n ≥ 1` contains a prime, then the numbers
`millsLower k = (millsSeq k) ^ (1 / 3 ^ (k + 1))` increase to a limit `millsConst`, the floor of
`millsConst ^ 3 ^ (k + 1)` is `millsSeq k` for every `k`, and every real `A` for which the floor
of `A ^ 3 ^ (k + 1)` is prime for every `k` satisfies `millsConst ≤ A`. With the gap bound of
Carneiro, Milinovich and Soundararajan as hypothesis the condition on cubes is
`exists_prime_between_pow_of_gap` with `m = 3`.
-/

namespace ReadableRH

open Filter Topology

/-- The least prime larger than `n`. -/
noncomputable def nextPrime (n : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (n + 1))

theorem nextPrime_spec (n : ℕ) : n < nextPrime n ∧ (nextPrime n).Prime := by
  have h := Nat.find_spec (Nat.exists_infinite_primes (n + 1))
  exact ⟨Nat.lt_of_succ_le h.1, h.2⟩

theorem nextPrime_le {n p : ℕ} (hp : p.Prime) (hnp : n < p) : nextPrime n ≤ p :=
  Nat.find_min' (Nat.exists_infinite_primes (n + 1)) ⟨Nat.succ_le_of_lt hnp, hp⟩

/-- `millsSeq k` is `Q_(k+1)` of the paper: `2, 11, 1361, 2521008887, ...`. -/
noncomputable def millsSeq : ℕ → ℕ
  | 0 => 2
  | k + 1 => nextPrime (millsSeq k ^ 3)

theorem millsSeq_succ (k : ℕ) : millsSeq (k + 1) = nextPrime (millsSeq k ^ 3) := rfl

theorem millsSeq_prime (k : ℕ) : (millsSeq k).Prime := by
  cases k with
  | zero => exact Nat.prime_two
  | succ k => rw [millsSeq_succ]; exact (nextPrime_spec _).2

theorem millsSeq_two_le (k : ℕ) : 2 ≤ millsSeq k := (millsSeq_prime k).two_le

theorem millsSeq_pow_lt (k : ℕ) : millsSeq k ^ 3 < millsSeq (k + 1) := by
  rw [millsSeq_succ]; exact (nextPrime_spec _).1

/-- With a prime in every `(n ^ 3, (n + 1) ^ 3)`: `Q_(k+2) + 1 < (Q_(k+1) + 1) ^ 3`, because
`(Q + 1) ^ 3 - 1 = Q (Q ^ 2 + 3 Q + 3)` is not prime. -/
theorem millsSeq_succ_add_one_lt
    (hcube : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3) (k : ℕ) :
    millsSeq (k + 1) + 1 < (millsSeq k + 1) ^ 3 := by
  have hq2 : 2 ≤ millsSeq k := millsSeq_two_le k
  obtain ⟨p, hp, h1, h2⟩ := hcube (millsSeq k) (by omega)
  have hle : millsSeq (k + 1) ≤ p := by rw [millsSeq_succ]; exact nextPrime_le hp h1
  set q := millsSeq k with hq
  have hcube_id : (q + 1) ^ 3 = q * (q ^ 2 + 3 * q + 3) + 1 := by ring
  set N := (q + 1) ^ 3 with hN
  set M := q * (q ^ 2 + 3 * q + 3) with hM
  have h3 : q * 3 ≤ M := Nat.mul_le_mul le_rfl (by omega)
  have hne : p + 1 ≠ N := by
    intro heq
    have hfac : p = M := by omega
    have hdvd : q ∣ p := ⟨q ^ 2 + 3 * q + 3, hfac⟩
    rcases hp.eq_one_or_self_of_dvd q hdvd with h | h
    · omega
    · omega
  omega

theorem le_three_pow_succ (k : ℕ) : k ≤ 3 ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]
    omega

/-- `x ^ (1 / n)`, through `Real.rpow`. -/
noncomputable def nroot (n : ℕ) (x : ℝ) : ℝ := x ^ ((n : ℝ)⁻¹)

theorem nroot_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ nroot n x := Real.rpow_nonneg hx _

theorem nroot_pow {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 ≤ x) : nroot n x ^ n = x :=
  Real.rpow_inv_natCast_pow hx hn

/-- `Q_(k+1) ^ (1 / 3 ^ (k + 1))`. -/
noncomputable def millsLower (k : ℕ) : ℝ := nroot (3 ^ (k + 1)) (millsSeq k)

/-- `(Q_(k+1) + 1) ^ (1 / 3 ^ (k + 1))`. -/
noncomputable def millsUpper (k : ℕ) : ℝ := nroot (3 ^ (k + 1)) ((millsSeq k : ℝ) + 1)

/-- The least Mills constant, `lim Q_k ^ (1 / 3 ^ k)`. -/
noncomputable def millsConst : ℝ := ⨆ k, millsLower k

theorem three_pow_ne_zero (k : ℕ) : 3 ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)

theorem millsLower_nonneg (k : ℕ) : 0 ≤ millsLower k := nroot_nonneg _ (Nat.cast_nonneg _)

theorem millsUpper_nonneg (k : ℕ) : 0 ≤ millsUpper k := nroot_nonneg _ (by positivity)

theorem millsLower_pow (k : ℕ) : millsLower k ^ (3 ^ (k + 1)) = millsSeq k :=
  nroot_pow (three_pow_ne_zero k) (Nat.cast_nonneg _)

theorem millsUpper_pow (k : ℕ) : millsUpper k ^ (3 ^ (k + 1)) = (millsSeq k : ℝ) + 1 :=
  nroot_pow (three_pow_ne_zero k) (by positivity)

theorem millsLower_lt_millsUpper (k : ℕ) : millsLower k < millsUpper k := by
  apply lt_of_pow_lt_pow_left₀ (3 ^ (k + 1)) (millsUpper_nonneg k)
  rw [millsLower_pow, millsUpper_pow]
  linarith

theorem millsLower_lt_succ (k : ℕ) : millsLower k < millsLower (k + 1) := by
  apply lt_of_pow_lt_pow_left₀ (3 ^ (k + 1 + 1)) (millsLower_nonneg (k + 1))
  rw [millsLower_pow, pow_succ 3 (k + 1), pow_mul, millsLower_pow]
  exact_mod_cast millsSeq_pow_lt k

theorem millsUpper_succ_lt
    (hcube : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3) (k : ℕ) :
    millsUpper (k + 1) < millsUpper k := by
  apply lt_of_pow_lt_pow_left₀ (3 ^ (k + 1 + 1)) (millsUpper_nonneg k)
  rw [millsUpper_pow, pow_succ 3 (k + 1), pow_mul, millsUpper_pow]
  exact_mod_cast millsSeq_succ_add_one_lt hcube k

theorem millsLower_mono : Monotone millsLower :=
  monotone_nat_of_le_succ fun k => (millsLower_lt_succ k).le

theorem millsUpper_anti
    (hcube : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3) :
    Antitone millsUpper :=
  antitone_nat_of_succ_le fun k => (millsUpper_succ_lt hcube k).le

theorem millsLower_lt_millsUpper'
    (hcube : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3) (j k : ℕ) :
    millsLower j < millsUpper k :=
  calc millsLower j ≤ millsLower (max j k) := millsLower_mono (le_max_left j k)
    _ < millsUpper (max j k) := millsLower_lt_millsUpper _
    _ ≤ millsUpper k := millsUpper_anti hcube (le_max_right j k)

theorem millsLower_bddAbove
    (hcube : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3) :
    BddAbove (Set.range millsLower) := by
  refine ⟨millsUpper 0, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact (millsLower_lt_millsUpper' hcube j 0).le

/-- The floor of `millsConst ^ 3 ^ (k + 1)` is `Q_(k+1)`. -/
theorem floor_millsConst_pow
    (hcube : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3) (k : ℕ) :
    ⌊millsConst ^ (3 ^ (k + 1))⌋₊ = millsSeq k := by
  have hb := millsLower_bddAbove hcube
  have hlo : millsLower k ≤ millsConst := le_ciSup hb k
  have hup : millsConst < millsUpper k :=
    lt_of_le_of_lt (ciSup_le fun j => (millsLower_lt_millsUpper' hcube j (k + 1)).le)
      (millsUpper_succ_lt hcube k)
  have h0 : 0 ≤ millsConst := (millsLower_nonneg k).trans hlo
  rw [Nat.floor_eq_iff (pow_nonneg h0 _)]
  constructor
  · rw [← millsLower_pow k]
    exact pow_le_pow_left₀ (millsLower_nonneg k) hlo _
  · rw [← millsUpper_pow k]
    exact pow_lt_pow_left₀ hup h0 (three_pow_ne_zero k)

/-- If the floor of `A ^ 3 ^ (k + 1)` is prime for every `k`, it is at least `Q_(k+1)`. -/
theorem millsSeq_le_floor {A : ℝ} (hA : ∀ k, (⌊A ^ (3 ^ (k + 1))⌋₊).Prime) (k : ℕ) :
    millsSeq k ≤ ⌊A ^ (3 ^ (k + 1))⌋₊ := by
  induction k with
  | zero => exact (hA 0).two_le
  | succ k ih =>
    have hnn : 0 ≤ A ^ (3 ^ (k + 1)) := by
      by_contra h
      have h0 : ⌊A ^ (3 ^ (k + 1))⌋₊ = 0 := Nat.floor_of_nonpos (le_of_lt (not_le.mp h))
      exact Nat.not_prime_zero (h0 ▸ hA k)
    have hfl : ((⌊A ^ (3 ^ (k + 1))⌋₊ : ℕ) : ℝ) ≤ A ^ (3 ^ (k + 1)) := Nat.floor_le hnn
    have hcube : ((⌊A ^ (3 ^ (k + 1))⌋₊ ^ 3 : ℕ) : ℝ) ≤ A ^ (3 ^ (k + 1 + 1)) := by
      rw [pow_succ 3 (k + 1), pow_mul]
      push_cast
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hfl 3
    have hle : ⌊A ^ (3 ^ (k + 1))⌋₊ ^ 3 ≤ ⌊A ^ (3 ^ (k + 1 + 1))⌋₊ := Nat.le_floor hcube
    have hne : ⌊A ^ (3 ^ (k + 1))⌋₊ ^ 3 ≠ ⌊A ^ (3 ^ (k + 1 + 1))⌋₊ := by
      intro heq
      exact Nat.Prime.not_prime_pow (by norm_num) (heq ▸ hA (k + 1))
    have hlt : millsSeq k ^ 3 < ⌊A ^ (3 ^ (k + 1 + 1))⌋₊ :=
      lt_of_le_of_lt (Nat.pow_le_pow_left ih 3) (lt_of_le_of_ne hle hne)
    rw [millsSeq_succ]
    exact nextPrime_le (hA (k + 1)) hlt

/-- Minimality: every `A` with `⌊A ^ 3 ^ k⌋` prime for all `k ≥ 1` is at least `millsConst`. -/
theorem millsConst_le
    (hcube : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3)
    {A : ℝ} (hA : ∀ k, (⌊A ^ (3 ^ (k + 1))⌋₊).Prime) : millsConst ≤ A := by
  by_contra hge
  have hlt : A < millsConst := not_le.mp hge
  have hApos : 0 < A := by
    by_contra h
    have h1 : A ^ (3 ^ (0 + 1)) ≤ 0 := by
      norm_num
      nlinarith [sq_nonneg A, not_lt.mp h]
    have h0 : ⌊A ^ (3 ^ (0 + 1))⌋₊ = 0 := Nat.floor_of_nonpos h1
    exact Nat.not_prime_zero (h0 ▸ hA 0)
  set c := millsConst / A with hc
  have hc1 : 1 < c := by rw [hc, one_lt_div hApos]; exact hlt
  have hbound : ∀ k, c ^ (3 ^ (k + 1)) < 2 := by
    intro k
    have hX : (2 : ℝ) ≤ A ^ (3 ^ (k + 1)) := by
      have h1 : ((millsSeq k : ℕ) : ℝ) ≤ ((⌊A ^ (3 ^ (k + 1))⌋₊ : ℕ) : ℝ) :=
        by exact_mod_cast millsSeq_le_floor hA k
      have h2 : ((⌊A ^ (3 ^ (k + 1))⌋₊ : ℕ) : ℝ) ≤ A ^ (3 ^ (k + 1)) :=
        Nat.floor_le (pow_nonneg hApos.le _)
      have h3 : (2 : ℝ) ≤ ((millsSeq k : ℕ) : ℝ) := by exact_mod_cast millsSeq_two_le k
      linarith
    have hfl := floor_millsConst_pow hcube k
    have h0 : 0 ≤ millsConst := (le_trans hApos.le hlt.le)
    have hup : millsConst ^ (3 ^ (k + 1)) < (millsSeq k : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (millsConst ^ (3 ^ (k + 1)))
      rw [hfl] at this
      exact this
    have hQ : ((millsSeq k : ℕ) : ℝ) ≤ A ^ (3 ^ (k + 1)) :=
      le_trans (by exact_mod_cast millsSeq_le_floor hA k)
        (Nat.floor_le (pow_nonneg hApos.le _))
    have hmul : millsConst ^ (3 ^ (k + 1)) = c ^ (3 ^ (k + 1)) * A ^ (3 ^ (k + 1)) := by
      rw [← mul_pow, hc, div_mul_cancel₀ _ hApos.ne']
    have hlt2 : c ^ (3 ^ (k + 1)) * A ^ (3 ^ (k + 1)) < 2 * A ^ (3 ^ (k + 1)) := by
      rw [← hmul]; linarith
    exact lt_of_mul_lt_mul_right hlt2 (pow_nonneg hApos.le _)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hc1
  have hmono : c ^ n ≤ c ^ (3 ^ (n + 1)) := pow_le_pow_right₀ hc1.le (le_three_pow_succ n)
  linarith [hbound n]

/-- Corollary `GH:cor:powers` (ii): from a prime in every `(n ^ 3, (n + 1) ^ 3)`, the numbers
`Q_k ^ (1 / 3 ^ k)` converge to `millsConst`, the floor of `millsConst ^ 3 ^ k` is the prime
`Q_k` for every `k ≥ 1`, and `millsConst` is the least such real number. -/
theorem least_mills_constant
    (hcube : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3) :
    Tendsto millsLower atTop (𝓝 millsConst) ∧
      (∀ k, ⌊millsConst ^ (3 ^ (k + 1))⌋₊ = millsSeq k ∧ (millsSeq k).Prime) ∧
      ∀ A : ℝ, (∀ k, (⌊A ^ (3 ^ (k + 1))⌋₊).Prime) → millsConst ≤ A :=
  ⟨tendsto_atTop_ciSup millsLower_mono (millsLower_bddAbove hcube),
    fun k => ⟨floor_millsConst_pow hcube k, millsSeq_prime k⟩,
    fun _ hA => millsConst_le hcube hA⟩

/-- The same with the gap bound of Carneiro, Milinovich and Soundararajan as hypothesis. -/
theorem least_mills_constant_of_gap
    (hgap : ∀ x : ℝ, 4 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + 22 / 25 * Real.sqrt x * Real.log x) :
    Tendsto millsLower atTop (𝓝 millsConst) ∧
      (∀ k, ⌊millsConst ^ (3 ^ (k + 1))⌋₊ = millsSeq k ∧ (millsSeq k).Prime) ∧
      ∀ A : ℝ, (∀ k, (⌊A ^ (3 ^ (k + 1))⌋₊).Prime) → millsConst ≤ A :=
  least_mills_constant fun _ hn => exists_prime_between_pow_of_gap hgap le_rfl hn

end ReadableRH
