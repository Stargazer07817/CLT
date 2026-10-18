import LeanClt.Transfer.Depths
import LeanClt.Renewal.Theorem41

/-!
# The pinned kernel `𝒦_h` (proof of Theorem 6.10 [`thm:anticonc`]), stage 1 of the checkpoint-20 plan

Unconditional facts about the twisted renewal kernel at integer rewards, used by the Fourier
inversion of Theorem 5.10 [`thm:transfer`] over `s ∈ [0, 2π]` (route (b) of checkpoint 20).

* `pinnedK ρ η h u = ∑_t E[e^{Z_t - u} 1{0 ≤ Z_t - u ≤ ℓ} 1{ρ S_t + η t = h}]`: v8's `𝒦_h(u)` at
  the shortcut reward `(1,0)`, and the pinned kernels of v8's raw (`S_t + t = h`) and odd (`t = h`)
  cases at `(1,1)` and `(0,1)`. Since the phase of `R^{ρ,η}_s(u)` is `e^{-is(ρA+ηt)}`, `𝒦_h(u)` is
  the coefficient of `e^{-ihs}` in `s ↦ R^{ρ,η}_s(u)` (`renewalR_fourier`), as its docstring says.
* `lawS_le_inv_sqrt`: `P(S_t = A) ≤ C/√A` (in fact `C = 1/2`, `lawS_le_half_inv_sqrt`, which is
  the form the proofs use), from
  `P(S_t = A) = C(A-1, t-1) 2^{-A} ≤ C(A-1, ⌊(A-1)/2⌋) 2^{-A}` and `C(n, ⌊n/2⌋)² (n+1) ≤ 4^n`.
* `renewalR_fourier`: `(2π)⁻¹ ∫₀^{2π} e^{ihs} R^{ρ,η}_s(u) ds = 𝒦_h(u)`. The integral passes
  inside the double series by dominated convergence twice (`hasSum_integral_of_dominated_convergence`,
  with the `s`-free bounds `2 P(S_t = A)` and `2 pwin u t`), and each term is the orthogonality
  integral `∫₀^{2π} e^{iks} ds = 2π 1{k = 0}`.
* `pinnedK_le`, `pinnedK_le_two`: the pinning argument of v8. On `{ρ S_t + η t = h}` the window
  `0 ≤ Z_t - u ≤ ℓ` leaves at most one `t` for the rewards `(1,0)` (window length `ℓ/β < 1`) and
  `(1,1)` (length `ℓ/(ℓ+β) < 1`), and at most two values of `A` for `(0,1)`; a nonzero term has
  `ℓA ≥ u`, so it is at most `2 P(S_t = A) ≤ 1/√A ≤ 1/√u`. `pinnedK_le_two` is v8's bound
  `𝒦_h ≤ 2`, which v8 uses for the part `S_k > 3k`; it is proved but not used, because the Lean
  right side of (5.14) carries the cutoff `S ≤ 3m`.
* `continuous_renewalR`: `s ↦ R^{ρ,η}_s(u)` is continuous (a uniformly convergent double series).
* `uMS_ge_linear`: the kernel argument `u = log(Y/M) - Z_m` is at least `L/4000` for every coarse
  total `S ≤ 3m`, typical or not (v8's `u ≥ 0.000987 log x` on the retained event).
-/

open Real Filter Topology Finset Complex

noncomputable section

namespace CollatzCLT

/-! ## The pinned kernel -/

/-- The pinned kernel `𝒦_h(u)` of the proof of Theorem 6.10 [`thm:anticonc`], for an integer reward
`(ρ, η)`: `∑_{t ≥ 0} E[e^{Z_t - u} 1{0 ≤ Z_t - u ≤ ℓ} 1{ρ S_t + η t = h}]`, the coefficient of
`e^{-ihs}` in `s ↦ R^{ρ,η}_s(u)`, that is `(2π)⁻¹ ∫₀^{2π} e^{ihs} R^{ρ,η}_s(u) ds`
(`renewalR_fourier`). -/
def pinnedK (ρ η : ℕ) (h : ℤ) (u : ℝ) : ℝ :=
  ∑' t : ℕ, ∑' A : ℕ,
    if 0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell ∧ ((ρ * A + η * t : ℕ) : ℤ) = h then
      lawS t A * Real.exp (Zval t A - u)
    else 0

/-- The `(t, A)` summand of `pinnedK`. -/
def pterm (ρ η : ℕ) (h : ℤ) (u : ℝ) (t A : ℕ) : ℝ :=
  if 0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell ∧ ((ρ * A + η * t : ℕ) : ℤ) = h then
    lawS t A * Real.exp (Zval t A - u)
  else 0

lemma pinnedK_eq (ρ η : ℕ) (h : ℤ) (u : ℝ) :
    pinnedK ρ η h u = ∑' t : ℕ, ∑' A : ℕ, pterm ρ η h u t A := rfl

lemma pterm_nonneg (ρ η : ℕ) (h : ℤ) (u : ℝ) (t A : ℕ) : 0 ≤ pterm ρ η h u t A := by
  unfold pterm; split_ifs
  · exact mul_nonneg (lawS_nonneg _ _) (Real.exp_pos _).le
  · exact le_rfl

lemma pinnedK_nonneg (ρ η : ℕ) (h : ℤ) (u : ℝ) : 0 ≤ pinnedK ρ η h u :=
  tsum_nonneg fun t => tsum_nonneg fun A => pterm_nonneg ρ η h u t A

lemma pterm_le (ρ η : ℕ) (h : ℤ) (u : ℝ) (t A : ℕ) : pterm ρ η h u t A ≤ 2 * lawS t A := by
  unfold pterm; split_ifs with hw
  · rw [mul_comm 2]
    gcongr
    · exact lawS_nonneg _ _
    · rw [← exp_ell]; exact Real.exp_le_exp.mpr hw.2.1
  · have := lawS_nonneg t A; linarith

lemma pterm_ne_zero {ρ η : ℕ} {h : ℤ} {u : ℝ} {t A : ℕ} (hne : pterm ρ η h u t A ≠ 0) :
    0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell ∧ ((ρ * A + η * t : ℕ) : ℤ) = h := by
  unfold pterm at hne; split_ifs at hne with hw
  · exact hw
  · exact absurd rfl hne

lemma ell_lt_bet : ell < bet := Real.log_lt_log (by norm_num) (by norm_num)

/-- A nonzero term has `ℓA ≥ u`. -/
lemma pterm_ne_zero_le {ρ η : ℕ} {h : ℤ} {u : ℝ} {t A : ℕ} (hne : pterm ρ η h u t A ≠ 0) :
    u ≤ ell * A := by
  have hw := (pterm_ne_zero hne).1
  unfold Zval at hw
  have : 0 ≤ bet * (t : ℝ) := mul_nonneg bet_pos.le (Nat.cast_nonneg _)
  linarith

/-! ## The maximal binomial bound -/

/-- `C(2m, m)² (2m+1) ≤ 16^m`. -/
lemma centralBinom_sq_mul_le (m : ℕ) : m.centralBinom ^ 2 * (2 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Nat.succ_mul_centralBinom_succ m
    set b := m.centralBinom
    set b' := (m + 1).centralBinom
    have key : (m + 1) ^ 2 * (b' ^ 2 * (2 * (m + 1) + 1)) ≤ (m + 1) ^ 2 * 16 ^ (m + 1) := by
      have e : (m + 1) ^ 2 * (b' ^ 2 * (2 * (m + 1) + 1)) =
          (2 * (2 * m + 1) * b) ^ 2 * (2 * m + 3) := by
        rw [← h]; ring
      rw [e]
      have h2 : (2 * m + 1) * (2 * m + 3) ≤ 4 * (m + 1) ^ 2 := by nlinarith
      calc (2 * (2 * m + 1) * b) ^ 2 * (2 * m + 3)
          = 4 * b ^ 2 * (2 * m + 1) * ((2 * m + 1) * (2 * m + 3)) := by ring
        _ ≤ 4 * b ^ 2 * (2 * m + 1) * (4 * (m + 1) ^ 2) := Nat.mul_le_mul_left _ h2
        _ = 16 * (m + 1) ^ 2 * (b ^ 2 * (2 * m + 1)) := by ring
        _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := Nat.mul_le_mul_left _ ih
        _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- `C(n, ⌊n/2⌋)² (n+1) ≤ 4^n`. -/
lemma choose_middle_sq_mul_le (n : ℕ) : n.choose (n / 2) ^ 2 * (n + 1) ≤ 4 ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h := centralBinom_sq_mul_le m
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    rw [show 2 * m / 2 = m by omega, pow_mul, show (4 : ℕ) ^ 2 = 16 by norm_num]
    exact h
  · have h := centralBinom_sq_mul_le (m + 1)
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    have hc : (2 * (m + 1)).choose (m + 1) = 2 * (2 * m + 1).choose m := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.choose_succ_succ,
        Nat.choose_symm_of_eq_add (by ring : 2 * m + 1 = (m + 1) + m)]
      ring
    rw [hc] at h
    rw [show (2 * m + 1) / 2 = m by omega]
    have : 4 * ((2 * m + 1).choose m ^ 2 * (2 * m + 1 + 1)) ≤ 4 * 4 ^ (2 * m + 1) := by
      calc 4 * ((2 * m + 1).choose m ^ 2 * (2 * m + 1 + 1))
          ≤ (2 * (2 * m + 1).choose m) ^ 2 * (2 * (m + 1) + 1) := by nlinarith
        _ ≤ 16 ^ (m + 1) := h
        _ = 4 * 4 ^ (2 * m + 1) := by rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul]; ring
    omega

/-- `P(S_t = A) ≤ (1/2)/√A` for `A ≥ 1`. -/
lemma lawS_le_half_inv_sqrt (t A : ℕ) (hA : 1 ≤ A) : lawS t A ≤ 1 / 2 / √(A : ℝ) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hsq : 0 < √(A : ℝ) := Real.sqrt_pos.mpr hA0
  rcases Nat.lt_or_ge A t with htA | htA
  · rw [lawS_eq_zero_of_lt htA]; positivity
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    obtain ⟨A', rfl⟩ := Nat.exists_eq_add_of_le' hA
    rw [lawS_zero_succ]; positivity
  rw [lawS_eq_choose ht htA, le_div_iff₀ hsq]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hA
  rw [Nat.add_sub_cancel]
  set x := n.choose (n / 2)
  have hx : ((n.choose (t - 1) : ℕ) : ℝ) ≤ x := by exact_mod_cast Nat.choose_le_middle _ _
  have hxsq : ((x : ℝ)) ^ 2 * ((n : ℝ) + 1) ≤ 4 ^ n := by
    exact_mod_cast choose_middle_sq_mul_le n
  set v : ℝ := (x : ℝ) * (1 / 2) ^ (n + 1) with hv
  have hv0 : 0 ≤ v := by positivity
  have hvA : v ^ 2 * ((n + 1 : ℕ) : ℝ) ≤ (1 / 2) ^ 2 := by
    rw [hv, mul_pow, ← pow_mul]
    push_cast
    have h4 : ((1 / 2 : ℝ) ^ ((n + 1) * 2)) = (1 / 4) * (1 / 4) ^ n := by
      rw [show (n + 1) * 2 = 2 * n + 2 by ring, pow_add, pow_mul]; norm_num; ring
    rw [h4]
    have : ((x : ℝ)) ^ 2 * ((n : ℝ) + 1) * (1 / 4) ^ n ≤ 1 := by
      calc ((x : ℝ)) ^ 2 * ((n : ℝ) + 1) * (1 / 4) ^ n ≤ 4 ^ n * (1 / 4) ^ n := by gcongr
        _ = 1 := by rw [← mul_pow]; norm_num
    nlinarith
  have hs : v * √((n + 1 : ℕ) : ℝ) = √(v ^ 2 * ((n + 1 : ℕ) : ℝ)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hv0]
  calc ((n.choose (t - 1) : ℕ) : ℝ) * (1 / 2) ^ (n + 1) * √((n + 1 : ℕ) : ℝ)
      ≤ v * √((n + 1 : ℕ) : ℝ) := by gcongr; rw [hv]; gcongr
    _ = √(v ^ 2 * ((n + 1 : ℕ) : ℝ)) := hs
    _ ≤ √((1 / 2) ^ 2) := Real.sqrt_le_sqrt hvA
    _ = 1 / 2 := Real.sqrt_sq (by norm_num)

/-- The maximal-binomial bound behind `𝒦_h ≤ C/√h`: `P(S_t = A) ≤ C/√A` for all `t` and `A ≥ 1`. -/
theorem lawS_le_inv_sqrt : ∃ C : ℝ, ∀ t A : ℕ, 1 ≤ A → lawS t A ≤ C / √(A : ℝ) :=
  ⟨1 / 2, lawS_le_half_inv_sqrt⟩

/-- A nonzero term is at most `1/√u` (for `u > 0`). -/
lemma pterm_le_inv_sqrt (ρ η : ℕ) (h : ℤ) {u : ℝ} (hu : 0 < u) (t A : ℕ) :
    pterm ρ η h u t A ≤ 1 / √u := by
  by_cases hne : pterm ρ η h u t A = 0
  · rw [hne]; positivity
  have hA := pterm_ne_zero_le hne
  have hl := ell_pos; have hl1 := ell_lt_one
  have hA0 : (0 : ℝ) < A := by nlinarith
  have hA1 : 1 ≤ A := by exact_mod_cast hA0
  have huA : u ≤ A := by nlinarith
  calc pterm ρ η h u t A ≤ 2 * lawS t A := pterm_le ρ η h u t A
    _ ≤ 2 * (1 / 2 / √(A : ℝ)) := by gcongr; exact lawS_le_half_inv_sqrt t A hA1
    _ = 1 / √(A : ℝ) := by ring
    _ ≤ 1 / √u := by gcongr

/-! ## Series with at most one or two nonzero terms -/

/-- A real series with at most one nonzero term, each term `≤ B`, sums to at most `B`. -/
lemma tsum_le_of_atMostOne {f : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hle : ∀ t, f t ≤ B)
    (huniq : ∀ t t', f t ≠ 0 → f t' ≠ 0 → t = t') : ∑' t, f t ≤ B := by
  by_cases hex : ∃ t₀, f t₀ ≠ 0
  · obtain ⟨t₀, ht₀⟩ := hex
    rw [tsum_eq_single t₀ (fun t ht => by
      by_contra hne; exact ht (huniq t t₀ hne ht₀))]
    exact hle t₀
  · push Not at hex
    simp [hex, hB]

/-- The same for a double series with at most one nonzero term. -/
lemma tsum_tsum_le_of_atMostOne {F : ℕ → ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hle : ∀ t A, F t A ≤ B)
    (huniq : ∀ t A t' A', F t A ≠ 0 → F t' A' ≠ 0 → t = t' ∧ A = A') :
    ∑' t, ∑' A, F t A ≤ B := by
  have hin : ∀ t, ∑' A, F t A ≤ B := fun t =>
    tsum_le_of_atMostOne hB (hle t) (fun A A' h1 h2 => (huniq t A t A' h1 h2).2)
  have hne : ∀ t, ∑' A, F t A ≠ 0 → ∃ A, F t A ≠ 0 := by
    intro t ht
    by_contra hc; push Not at hc
    exact ht (by simp [hc])
  refine tsum_le_of_atMostOne hB hin (fun t t' h1 h2 => ?_)
  obtain ⟨A, hA⟩ := hne t h1
  obtain ⟨A', hA'⟩ := hne t' h2
  exact (huniq t A t' A' hA hA').1

/-- Two naturals whose `k`-multiples differ by at most `ℓ < k` are equal. -/
lemma eq_of_mul_close {k : ℝ} (hk : ell < k) {t t' : ℕ} (h1 : k * t ≤ k * t' + ell)
    (h2 : k * t' ≤ k * t + ell) : t = t' := by
  have hk0 : 0 < k := lt_trans ell_pos hk
  rcases lt_trichotomy t t' with h | h | h
  · have : (t : ℝ) + 1 ≤ t' := by exact_mod_cast h
    nlinarith
  · exact h
  · have : (t' : ℝ) + 1 ≤ t := by exact_mod_cast h
    nlinarith

/-- The pinning for the shortcut reward `(1, 0)`: `A = h`, and the window leaves one `t`. -/
lemma pterm_uniq_10 {h : ℤ} {u : ℝ} {t A t' A' : ℕ} (h1 : pterm 1 0 h u t A ≠ 0)
    (h2 : pterm 1 0 h u t' A' ≠ 0) : t = t' ∧ A = A' := by
  obtain ⟨w1, w1', p1⟩ := pterm_ne_zero h1
  obtain ⟨w2, w2', p2⟩ := pterm_ne_zero h2
  simp only [one_mul, zero_mul, add_zero] at p1 p2
  have hA : A = A' := by exact_mod_cast p1.trans p2.symm
  subst hA
  unfold Zval at w1 w1' w2 w2'
  exact ⟨eq_of_mul_close ell_lt_bet (by linarith) (by linarith), rfl⟩

/-- The pinning for the raw reward `(1, 1)`: `A + t = h`, and the window leaves one `t`. -/
lemma pterm_uniq_11 {h : ℤ} {u : ℝ} {t A t' A' : ℕ} (h1 : pterm 1 1 h u t A ≠ 0)
    (h2 : pterm 1 1 h u t' A' ≠ 0) : t = t' ∧ A = A' := by
  obtain ⟨w1, w1', p1⟩ := pterm_ne_zero h1
  obtain ⟨w2, w2', p2⟩ := pterm_ne_zero h2
  simp only [one_mul] at p1 p2
  have hAt : A + t = A' + t' := by exact_mod_cast p1.trans p2.symm
  have hAtR : (A : ℝ) + t = A' + t' := by exact_mod_cast hAt
  unfold Zval at w1 w1' w2 w2'
  have hk : ell < ell + bet := by linarith [bet_pos]
  have htt : t = t' := eq_of_mul_close hk (by nlinarith) (by nlinarith)
  subst htt
  exact ⟨rfl, by omega⟩

/-- The window in `A` at fixed `t` has at most two points. -/
lemma card_Awindow_le (u : ℝ) (t : ℕ) : (Icc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1)).card ≤ 2 := by
  rw [Nat.card_Icc]
  have := Nat.floor_le_ceil (hT u t)
  omega

/-- For the odd reward `(0, 1)` the pinning is `t = h`; the double series is a sum over the window
of `A` at `t = h`. -/
lemma pinnedK_01_eq (h : ℕ) (u : ℝ) :
    pinnedK 0 1 h u = ∑ A ∈ Icc ⌈hT u h⌉₊ (⌊hT u h⌋₊ + 1), pterm 0 1 h u h A := by
  rw [pinnedK_eq, tsum_eq_single h]
  · refine tsum_eq_sum fun A hA => ?_
    by_contra hne
    obtain ⟨w1, w2, -⟩ := pterm_ne_zero hne
    have hw := (window_iff u h A).mp ⟨w1, w2⟩
    exact hA (mem_Icc_of_window hw.1 hw.2)
  · intro t ht
    have hz : ∀ A, pterm 0 1 (h : ℤ) u t A = 0 := fun A => by
      by_contra hne
      have p := (pterm_ne_zero hne).2.2
      simp only [zero_mul, one_mul, zero_add, Nat.cast_inj] at p
      exact ht p
    simp [hz]

/-- For the odd reward and `h < 0` every term vanishes. -/
lemma pinnedK_01_neg {h : ℤ} (hh : h < 0) (u : ℝ) : pinnedK 0 1 h u = 0 := by
  have hz : ∀ t A, pterm 0 1 h u t A = 0 := fun t A => by
    by_contra hne
    have p := (pterm_ne_zero hne).2.2
    simp only [zero_mul, one_mul, zero_add] at p
    omega
  rw [pinnedK_eq]; simp [hz]

/-! ## The kernel bounds -/

/-- **The kernel bound of the proof of Theorem 6.10:** `𝒦_h(u) ≤ C/√u` for `u > 0`, for the three
clock rewards `(1,0)`, `(1,1)`, `(0,1)`, uniformly in the integer `h`. -/
theorem pinnedK_le : ∃ C : ℝ, ∀ ρ η : ℕ, (ρ = 1 ∧ η = 0) ∨ (ρ = 1 ∧ η = 1) ∨ (ρ = 0 ∧ η = 1) →
    ∀ (h : ℤ) (u : ℝ), 0 < u → pinnedK ρ η h u ≤ C / √u := by
  refine ⟨2, ?_⟩
  rintro ρ η (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) h u hu
  · have hB : (0 : ℝ) ≤ 1 / √u := by positivity
    refine (tsum_tsum_le_of_atMostOne hB (pterm_le_inv_sqrt 1 0 h hu)
      (fun t A t' A' h1 h2 => pterm_uniq_10 h1 h2)).trans ?_
    gcongr; norm_num
  · have hB : (0 : ℝ) ≤ 1 / √u := by positivity
    refine (tsum_tsum_le_of_atMostOne hB (pterm_le_inv_sqrt 1 1 h hu)
      (fun t A t' A' h1 h2 => pterm_uniq_11 h1 h2)).trans ?_
    gcongr; norm_num
  · rcases lt_or_ge h 0 with hneg | hpos
    · rw [pinnedK_01_neg hneg]; positivity
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
      rw [pinnedK_01_eq]
      calc ∑ A ∈ Icc ⌈hT u n⌉₊ (⌊hT u n⌋₊ + 1), pterm 0 1 n u n A
          ≤ ∑ A ∈ Icc ⌈hT u n⌉₊ (⌊hT u n⌋₊ + 1), 1 / √u :=
            Finset.sum_le_sum fun A _ => pterm_le_inv_sqrt 0 1 n hu n A
        _ = (Icc ⌈hT u n⌉₊ (⌊hT u n⌋₊ + 1)).card * (1 / √u) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 * (1 / √u) := by
            gcongr
            exact_mod_cast card_Awindow_le u n
        _ = 2 / √u := by ring

/-- `𝒦_h(u) ≤ 2` for all real `u` and integers `h`, for the three clock rewards (proof of
Theorem 6.10). -/
theorem pinnedK_le_two (ρ η : ℕ) (hρη : (ρ = 1 ∧ η = 0) ∨ (ρ = 1 ∧ η = 1) ∨ (ρ = 0 ∧ η = 1))
    (h : ℤ) (u : ℝ) : pinnedK ρ η h u ≤ 2 := by
  have h2 : ∀ ρ η t A, pterm ρ η h u t A ≤ 2 := fun ρ η t A =>
    (pterm_le ρ η h u t A).trans (by linarith [lawS_le_one t A])
  rcases hρη with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact tsum_tsum_le_of_atMostOne (by norm_num) (h2 1 0)
      (fun t A t' A' h1 h2 => pterm_uniq_10 h1 h2)
  · exact tsum_tsum_le_of_atMostOne (by norm_num) (h2 1 1)
      (fun t A t' A' h1 h2 => pterm_uniq_11 h1 h2)
  · rcases lt_or_ge h 0 with hneg | hpos
    · rw [pinnedK_01_neg hneg]; norm_num
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
      rw [pinnedK_01_eq]
      calc ∑ A ∈ Icc ⌈hT u n⌉₊ (⌊hT u n⌋₊ + 1), pterm 0 1 n u n A
          ≤ ∑ A ∈ Icc ⌈hT u n⌉₊ (⌊hT u n⌋₊ + 1), 2 * lawS n A :=
            Finset.sum_le_sum fun A _ => pterm_le 0 1 n u n A
        _ = 2 * ∑ A ∈ Icc ⌈hT u n⌉₊ (⌊hT u n⌋₊ + 1), lawS n A := by rw [Finset.mul_sum]
        _ ≤ 2 * ∑' A, lawS n A := by
            gcongr
            exact (summable_lawS n).sum_le_tsum _ (fun A _ => lawS_nonneg n A)
        _ = 2 := by rw [tsum_lawS, mul_one]

/-! ## Continuity in the frequency -/

lemma continuous_rterm (ρ η u : ℝ) (t A : ℕ) : Continuous (fun s => rterm ρ η s u t A) := by
  unfold rterm
  split_ifs
  · fun_prop
  · exact continuous_const

lemma continuous_rinner (ρ η u : ℝ) (t : ℕ) : Continuous (fun s => rinner ρ η s u t) :=
  continuous_tsum (fun A => continuous_rterm ρ η u t A) ((summable_lawS t).mul_left 2)
    (fun A s => norm_rterm_le ρ η s u t A)

/-- `s ↦ R^{ρ,η}_s(u)` is continuous: a uniformly convergent double series. -/
lemma continuous_renewalR (ρ η u : ℝ) : Continuous (fun s => renewalR ρ η s u) :=
  continuous_tsum (fun t => continuous_rinner ρ η u t) ((summable_pwin u).mul_left 2)
    (fun t s => norm_rinner_le ρ η s u t)

/-! ## The Fourier coefficients of the twisted kernel -/

/-- The orthogonality integral `∫₀^{2π} e^{iks} ds = 2π 1{k = 0}` for an integer `k`. -/
lemma integral_cexp_int (k : ℤ) :
    ∫ s in (0 : ℝ)..(2 * π), cexp ((((k : ℝ) * s : ℝ) : ℂ) * I) =
      if k = 0 then ((2 * π : ℝ) : ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hc : ((k : ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hk) I_ne_zero
    have e : ∀ s : ℝ, cexp ((((k : ℝ) * s : ℝ) : ℂ) * I) = cexp ((k : ℂ) * I * (s : ℂ)) := by
      intro s; congr 1; push_cast; ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : cexp ((k : ℂ) * I * (2 * (π : ℂ))) = 1 := by
      rw [show (k : ℂ) * I * (2 * (π : ℂ)) = (k : ℂ) * (2 * π * I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    push_cast
    simp [h1]

/-- One term: `∫₀^{2π} e^{ihs} · term_{t,A}(s) ds = 2π · pterm`. -/
lemma integral_phase_rterm (ρ η : ℕ) (h : ℤ) (u : ℝ) (t A : ℕ) :
    ∫ s in (0 : ℝ)..(2 * π), cexp ((((h : ℝ) * s : ℝ) : ℂ) * I) * rterm ρ η s u t A =
      ((2 * π : ℝ) : ℂ) * (pterm ρ η h u t A : ℂ) := by
  unfold rterm pterm
  by_cases hw : 0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell
  · have e : ∀ s : ℝ, cexp ((((h : ℝ) * s : ℝ) : ℂ) * I) *
        (if 0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell then
          (lawS t A : ℂ) * (Real.exp (Zval t A - u) : ℂ) *
            cexp (-(((s * ((ρ : ℝ) * A + (η : ℝ) * t)) : ℝ) : ℂ) * I) else 0) =
        ((lawS t A * Real.exp (Zval t A - u) : ℝ) : ℂ) *
          cexp (((((h - ((ρ * A + η * t : ℕ) : ℤ) : ℤ) : ℝ) * s : ℝ) : ℂ) * I) := by
      intro s
      rw [ite_eq_left hw, mul_comm, mul_assoc, ← Complex.exp_add]
      push_cast
      ring_nf
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_cexp_int]
    simp only [sub_eq_zero]
    by_cases hp : h = ((ρ * A + η * t : ℕ) : ℤ)
    · rw [ite_eq_left hp, ite_eq_left ⟨hw.1, hw.2, hp.symm⟩]; push_cast; ring
    · rw [ite_eq_right hp, ite_eq_right (fun h' => hp h'.2.2.symm)]; simp
  · rw [ite_eq_right (fun h' => hw ⟨h'.1, h'.2.1⟩)]
    simp only [ite_eq_right hw, mul_zero, intervalIntegral.integral_zero, Complex.ofReal_zero]

lemma norm_phase_mul (h : ℤ) (s : ℝ) (z : ℂ) :
    ‖cexp ((((h : ℝ) * s : ℝ) : ℂ) * I) * z‖ = ‖z‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma continuous_phase (h : ℤ) : Continuous (fun s : ℝ => cexp ((((h : ℝ) * s : ℝ) : ℂ) * I)) := by
  fun_prop

/-- The integral passes inside the `A`-series (dominated by `2 P(S_t = A)`). -/
lemma hasSum_integral_rterm (ρ η : ℕ) (h : ℤ) (u : ℝ) (t : ℕ) :
    HasSum (fun A => ∫ s in (0 : ℝ)..(2 * π), cexp ((((h : ℝ) * s : ℝ) : ℂ) * I) *
        rterm ρ η s u t A)
      (∫ s in (0 : ℝ)..(2 * π), cexp ((((h : ℝ) * s : ℝ) : ℂ) * I) * rinner ρ η s u t) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun A _ => 2 * lawS t A)
    (fun A => ((continuous_phase h).mul (continuous_rterm _ _ u t A)).aestronglyMeasurable)
    (fun A => MeasureTheory.ae_of_all _ fun s _ => by rw [norm_phase_mul]; exact norm_rterm_le _ _ _ _ _ _)
    (MeasureTheory.ae_of_all _ fun s _ => (summable_lawS t).mul_left 2)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun s _ => ?_)
  have hs : Summable (fun A => rterm ρ η s u t A) :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun A => norm_rterm_le ρ η s u t A)
      ((summable_lawS t).mul_left 2)).of_norm
  exact hs.hasSum.mul_left _

/-- The integral passes inside the `t`-series (dominated by `2 pwin u t`). -/
lemma hasSum_integral_rinner (ρ η : ℕ) (h : ℤ) (u : ℝ) :
    HasSum (fun t => ∫ s in (0 : ℝ)..(2 * π), cexp ((((h : ℝ) * s : ℝ) : ℂ) * I) *
        rinner ρ η s u t)
      (∫ s in (0 : ℝ)..(2 * π), cexp ((((h : ℝ) * s : ℝ) : ℂ) * I) * renewalR ρ η s u) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun t _ => 2 * pwin u t)
    (fun t => ((continuous_phase h).mul (continuous_rinner _ _ u t)).aestronglyMeasurable)
    (fun t => MeasureTheory.ae_of_all _ fun s _ => by rw [norm_phase_mul]; exact norm_rinner_le _ _ _ _ _)
    (MeasureTheory.ae_of_all _ fun s _ => (summable_pwin u).mul_left 2)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun s _ => (summable_rinner _ _ s u).hasSum.mul_left _)

/-- The pinned kernel is the Fourier coefficient of the twisted kernel: for integer rewards and
integer `h`, `(2π)⁻¹ ∫₀^{2π} e^{ihs} R^{ρ,η}_s(u) ds = 𝒦_h(u)`. -/
theorem renewalR_fourier (ρ η : ℕ) (h : ℤ) (u : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ s in (0 : ℝ)..(2 * π),
      cexp (((h : ℝ) * s : ℝ) * I) * renewalR ρ η s u = (pinnedK ρ η h u : ℂ) := by
  rw [← (hasSum_integral_rinner ρ η h u).tsum_eq]
  simp_rw [← (hasSum_integral_rterm ρ η h u _).tsum_eq, integral_phase_rterm, tsum_mul_left]
  rw [pinnedK_eq, Complex.ofReal_tsum]
  simp_rw [Complex.ofReal_tsum]
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  push_cast at hπ ⊢
  field_simp

/-! ## The kernel argument on the whole coarse range -/

/-- **The kernel argument for every coarse total `S ≤ 3m`.** From
`u = log Y - log M - ℓ(S - 2m) - cm`, `log M ≤ L + cm + L^{0.7}`, `log Y ≥ αL` and
`m ≤ 10⁻⁵ L`: `u ≥ 0.001 L - (5ℓ - 2β) m - L^{0.7} ≥ L/4000` once `L^{0.7} ≤ L/2000` (v8's
`u ≥ 0.000987 log x`). -/
lemma uMS_ge_linear {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y)
    (h7 : Lx x ^ (0.7 : ℝ) ≤ Lx x / 2000) {M : ℕ} (hM : M ∈ Mset x) {S : ℕ}
    (hS : S ≤ 3 * mT x) : Lx x / 4000 ≤ uMS Y M S (mT x) := by
  obtain ⟨hx0, -, -, hY0⟩ := large_facts hL hY1
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.1.pos
  have hY1' : alpha * Lx x ≤ Real.log Y := by
    rw [← log_rpow_Lx hx0]; exact Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hY1
  have hlM := (abs_le.mp (Mset_log hM)).2
  have hm := mT_le x (by linarith [hL.L_ge])
  have hl7 := ell_lt_07; have hceq := c_eq; have hl := ell_pos; have hb := bet_pos
  have hc3 := c_lt_third
  have hS' : (S : ℝ) ≤ 3 * mT x := by exact_mod_cast hS
  have hm0 : (0 : ℝ) ≤ mT x := Nat.cast_nonneg _
  have hL0 : 0 ≤ Lx x := by linarith [hL.L_ge]
  unfold uMS
  rw [Real.log_div hY0.ne' hM0.ne']
  have h1 : ell * (S : ℝ) ≤ ell * (3 * mT x) := mul_le_mul_of_nonneg_left hS' hl.le
  have h2 : (c + 3 * ell - bet) * (mT x : ℝ) ≤ 2 * mT x :=
    mul_le_mul_of_nonneg_right (by linarith) hm0
  have halpha : alpha = 1.001 := rfl
  rw [halpha] at hY1' hm
  nlinarith

end CollatzCLT
