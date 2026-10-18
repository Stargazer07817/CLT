import LeanClt.Renewal.LawS
import LeanClt.Renewal.StirlingError

/-!
# Lemma 2.2(iii): the local limit theorem for `S_n`

Write `A = 2n + d`, `x = d/n`, `m = A - n = n + d`. With `P(S_n = A) = (n/A)·A!/(n! m!)·2^{-A}`
and Stirling with error (`stirErr`),
  `log P(S_n = A) - log g = n φ(x) - ½ (log(1 + x/2) + log(1 + x)) + θ_A - θ_n - θ_m`,
where `g = (4πn)^{-1/2} e^{-d²/(4n)}` and `φ(x) = (2+x) log(1+x/2) - (1+x) log(1+x) + x²/4`.
The cubic log-Taylor bound gives `|φ(x)| ≤ 4|x|³`, so the right side is
`O(|d|³/n² + |d|/n + 1/n) = O(n^{-1/2} + |d|³/n²)`.
-/

open Real Finset

namespace CollatzCLT

/-- Cubic Taylor bound for `log(1+y)`. -/
lemma abs_log_one_add_sub_le {y : ℝ} (hy : |y| ≤ 1 / 2) :
    |Real.log (1 + y) - (y - y ^ 2 / 2)| ≤ 2 * |y| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -y) (by rw [abs_neg]; linarith) 2
  simp only [sum_range_succ, sum_range_zero, abs_neg, sub_neg_eq_add] at h
  have hden : (1 / 2 : ℝ) ≤ 1 - |y| := by linarith
  have h2 : |y| ^ (2 + 1) / (1 - |y|) ≤ 2 * |y| ^ 3 := by
    rw [div_le_iff₀ (by linarith), show (2 + 1 : ℕ) = 3 from rfl]
    have : 0 ≤ |y| ^ 3 := by positivity
    nlinarith
  have heq : Real.log (1 + y) - (y - y ^ 2 / 2) =
      (0 + (-y) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + (-y) ^ (1 + 1) / ((1 : ℕ) + 1 : ℝ) +
        Real.log (1 + y)) := by push_cast; ring
  rw [heq]
  exact h.trans h2

/-- `|log(1+y)| ≤ 2|y|` for `|y| ≤ 1/2`. -/
lemma abs_log_one_add_le {y : ℝ} (hy : |y| ≤ 1 / 2) : |Real.log (1 + y)| ≤ 2 * |y| := by
  have h := abs_log_one_add_sub_le hy
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have h1 : |y - y ^ 2 / 2| ≤ |y| + |y| ^ 2 / 2 := by
    calc |y - y ^ 2 / 2| ≤ |y| + |y ^ 2 / 2| := abs_sub _ _
      _ = |y| + |y| ^ 2 / 2 := by rw [abs_div, abs_pow]; norm_num
  calc |Real.log (1 + y)| ≤ |Real.log (1 + y) - (y - y ^ 2 / 2)| + |y - y ^ 2 / 2| := by
        have := abs_add_le (Real.log (1 + y) - (y - y ^ 2 / 2)) (y - y ^ 2 / 2)
        simpa using this
    _ ≤ 2 * |y| ^ 3 + (|y| + |y| ^ 2 / 2) := add_le_add h h1
    _ ≤ 2 * |y| := by nlinarith [pow_le_pow_left₀ hy0 hy 2]

/-- `φ(x) = (2+x) log(1+x/2) - (1+x) log(1+x) + x²/4` is cubically small. -/
lemma abs_phi_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |(2 + x) * Real.log (1 + x / 2) - (1 + x) * Real.log (1 + x) + x ^ 2 / 4| ≤ 4 * |x| ^ 3 := by
  have hx2 : |x / 2| ≤ 1 / 2 := by rw [abs_div]; norm_num; linarith [abs_nonneg x]
  set r1 := Real.log (1 + x / 2) - (x / 2 - (x / 2) ^ 2 / 2) with hr1
  set r2 := Real.log (1 + x) - (x - x ^ 2 / 2) with hr2
  have b1 : |r1| ≤ |x| ^ 3 / 4 := by
    have := abs_log_one_add_sub_le hx2
    rw [abs_div, abs_two] at this
    linarith [show 2 * (|x| / 2) ^ 3 = |x| ^ 3 / 4 by ring]
  have b2 : |r2| ≤ 2 * |x| ^ 3 := abs_log_one_add_sub_le hx
  have key : (2 + x) * Real.log (1 + x / 2) - (1 + x) * Real.log (1 + x) + x ^ 2 / 4 =
      3 * x ^ 3 / 8 + (2 + x) * r1 - (1 + x) * r2 := by
    rw [hr1, hr2]; ring
  have ha : |2 + x| ≤ 5 / 2 := by rw [abs_le] at hx ⊢; constructor <;> linarith
  have hb : |1 + x| ≤ 3 / 2 := by rw [abs_le] at hx ⊢; constructor <;> linarith
  rw [key]
  calc |3 * x ^ 3 / 8 + (2 + x) * r1 - (1 + x) * r2|
      ≤ |3 * x ^ 3 / 8| + |(2 + x) * r1| + |(1 + x) * r2| := by
        have h1 := abs_sub (3 * x ^ 3 / 8 + (2 + x) * r1) ((1 + x) * r2)
        have h2 := abs_add_le (3 * x ^ 3 / 8) ((2 + x) * r1)
        linarith
    _ ≤ 3 * |x| ^ 3 / 8 + 5 / 2 * (|x| ^ 3 / 4) + 3 / 2 * (2 * |x| ^ 3) := by
        rw [abs_mul, abs_mul]
        gcongr
        · rw [abs_div, abs_mul, abs_pow]; norm_num
    _ ≤ 4 * |x| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg x) 3]

/-- `P(S_n = A) = (n/A) · A!/(n! (A-n)!) · 2^{-A}` for `1 ≤ n ≤ A`. -/
lemma lawS_eq_factorial {n A : ℕ} (hn : 1 ≤ n) (hnA : n ≤ A) :
    lawS n A = ((n : ℝ) / A) * ((A.factorial : ℝ) / ((n.factorial : ℝ) * ((A - n).factorial : ℝ))) *
      (1 / 2 : ℝ) ^ A := by
  rw [lawS_eq_choose hn hnA]
  congr 1
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨A', rfl⟩ := Nat.exists_eq_add_of_le' (le_trans hn hnA)
  simp only [Nat.add_sub_cancel]
  -- `(A'+1) C(A', n') = C(A'+1, n'+1) (n'+1)` and `C(A,n) n! (A-n)! = A!`
  have h1 := Nat.add_one_mul_choose_eq A' n'
  have h2 := Nat.choose_mul_factorial_mul_factorial hnA
  have hA0 : ((A' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : ((n' + 1).factorial : ℝ) * ((A' + 1 - (n' + 1)).factorial : ℝ) ≠ 0 := by positivity
  have h1' : ((A' + 1 : ℕ) : ℝ) * (A'.choose n' : ℝ) = ((A' + 1).choose (n' + 1) : ℝ) * (n' + 1 : ℕ) := by
    exact_mod_cast h1
  have h2' : ((A' + 1).choose (n' + 1) : ℝ) * ((n' + 1).factorial : ℝ) *
      ((A' + 1 - (n' + 1)).factorial : ℝ) = ((A' + 1).factorial : ℝ) := by exact_mod_cast h2
  rw [← h2']
  field_simp
  push_cast at h1' ⊢
  nlinarith [h1']

/-- The last step of Lemma 2.2(iii): from a bound on `Δ = log P - log g` to the relative error. -/
lemma local_limit_final {N d Δ g : ℝ} (hN0 : 0 < N) (hN1 : 1 ≤ N) (hg : 0 < g)
    (hΔB : |Δ| ≤ 4 * (|d| ^ 3 / N ^ 2) + 3 / 2 * (|d| / N) + 1 / N) (hΔ1 : |Δ| ≤ 1) :
    |g * Real.exp Δ - g| ≤ 12 * g * (1 / √N + |d| ^ 3 / N ^ 2) := by
  have hexp := Real.abs_exp_sub_one_le hΔ1
  have hsqN : 0 < √N := Real.sqrt_pos.mpr hN0
  have hsqN2 : √N * √N = N := Real.mul_self_sqrt hN0.le
  have hd0 : 0 ≤ |d| := abs_nonneg d
  -- `|d|/N ≤ N^{-1/2} + |d|³/N²`
  have hq1 : |d| / N ≤ 1 / √N + |d| ^ 3 / N ^ 2 := by
    have hp : 0 ≤ |d| ^ 3 / N ^ 2 := by positivity
    have hp' : 0 ≤ 1 / √N := by positivity
    rcases le_or_gt |d| (√N) with h | h
    · have : |d| / N ≤ 1 / √N := by
        rw [div_le_div_iff₀ hN0 hsqN, one_mul]
        calc |d| * √N ≤ √N * √N := mul_le_mul_of_nonneg_right h hsqN.le
          _ = N := hsqN2
      linarith only [this, hp]
    · have hNd : N ≤ |d| ^ 2 := by
        rw [← hsqN2, sq]; exact mul_le_mul h.le h.le hsqN.le hd0
      have : |d| / N ≤ |d| ^ 3 / N ^ 2 := by
        rw [div_le_div_iff₀ hN0 (by positivity)]
        calc |d| * N ^ 2 = (|d| * N) * N := by ring
          _ ≤ (|d| * N) * |d| ^ 2 := mul_le_mul_of_nonneg_left hNd (by positivity)
          _ = |d| ^ 3 * N := by ring
      linarith only [this, hp']
  have hq2 : 1 / N ≤ 1 / √N := by
    apply one_div_le_one_div_of_le hsqN
    have h1 : 1 ≤ √N := by rw [Real.one_le_sqrt]; exact hN1
    calc √N = √N * 1 := by ring
      _ ≤ √N * √N := mul_le_mul_of_nonneg_left h1 hsqN.le
      _ = N := hsqN2
  calc |g * Real.exp Δ - g| = g * |Real.exp Δ - 1| := by
        rw [← mul_sub_one, abs_mul, abs_of_pos hg]
    _ ≤ g * (2 * |Δ|) := by gcongr
    _ ≤ g * (12 * (1 / √N + |d| ^ 3 / N ^ 2)) :=
        mul_le_mul_of_nonneg_left (by
          have hp : 0 ≤ |d| ^ 3 / N ^ 2 := by positivity
          have hp' : 0 ≤ 1 / √N := by positivity
          linarith only [hΔB, hq1, hq2, hp, hp']) hg.le
    _ = 12 * g * (1 / √N + |d| ^ 3 / N ^ 2) := by ring

set_option maxHeartbeats 1000000 in
/-- **Lemma 2.2(iii), local limit theorem.** Uniformly for `|A - 2n| ≤ n^{3/5}`,
`P(S_n = A) = g (1 + O(n^{-1/2}) + O(|A-2n|³/n²))`, `g = (4πn)^{-1/2} e^{-(A-2n)²/(4n)}`
(with `C = 12`, `n₀ = 8⁵`). -/
theorem lawS_local_limit_explicit (n : ℕ) (hn : (8 : ℝ) ^ 5 ≤ n) (A : ℕ)
    (hA : |(A : ℝ) - 2 * n| ≤ (n : ℝ) ^ ((3 : ℝ) / 5)) :
      |lawS n A - gaussApprox n A| ≤
        12 * gaussApprox n A * ((n : ℝ) ^ (-(1 : ℝ) / 2) + |(A : ℝ) - 2 * n| ^ 3 / (n : ℝ) ^ 2) := by
  set N : ℝ := (n : ℝ) with hN
  set d : ℝ := (A : ℝ) - 2 * N with hd
  have hN0 : 0 < N := by linarith [show (0 : ℝ) < 8 ^ 5 by norm_num]
  -- `s = N^{1/5} ≥ 8`, `N = s⁵`, `N^{3/5} = s³`
  set s : ℝ := N ^ ((1 : ℝ) / 5) with hs
  have hs8 : 8 ≤ s := by
    have : (8 : ℝ) = (8 ^ 5 : ℝ) ^ ((1 : ℝ) / 5) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this]; exact Real.rpow_le_rpow (by norm_num) hn (by norm_num)
  have hs0 : 0 < s := by linarith
  have hNs : N = s ^ 5 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hN35 : N ^ ((3 : ℝ) / 5) = s ^ 3 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hds : |d| ≤ s ^ 3 := by rw [← hN35]; exact hA
  -- the relative deviation `x = d/N`
  set x : ℝ := d / N with hx
  have hxs : |x| ≤ 1 / s ^ 2 := by
    rw [hx, abs_div, abs_of_pos hN0, hNs, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg d, pow_pos hs0 2]
  have hx2 : |x| ≤ 1 / 2 := by
    refine hxs.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hxh : |x / 2| ≤ 1 / 2 := by rw [abs_div, abs_two]; linarith [abs_nonneg x]
  -- integrality: `n < A`, and `m = A - n` with `(m : ℝ) = N + d ≥ N / 2`
  have hdN : |d| ≤ N / 2 := by
    have := hx2; rw [hx, abs_div, abs_of_pos hN0, div_le_iff₀ hN0] at this; linarith
  have hAN : (n : ℝ) + 1 ≤ A := by
    have := (abs_le.mp hdN).1
    have hN1 : (2 : ℝ) ≤ N := by linarith [show (2 : ℝ) ≤ 8 ^ 5 by norm_num]
    rw [hd] at this; linarith
  have hnA : n + 1 ≤ A := by exact_mod_cast hAN
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by linarith [show (1 : ℝ) ≤ 8 ^ 5 by norm_num]
    exact_mod_cast this
  set m : ℕ := A - n with hm
  have hmR : (m : ℝ) = N + d := by
    rw [hm, Nat.cast_sub (by omega), hd]; ring
  have hm1 : 1 ≤ m := by omega
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hAR : (A : ℝ) = 2 * N * (1 + x / 2) := by rw [hx]; field_simp; rw [hd]; ring
  have hmR' : (m : ℝ) = N * (1 + x) := by rw [hmR, hx]; field_simp
  -- `P` and `g` are positive
  have hP := lawS_eq_factorial hn1 (by omega : n ≤ A)
  rw [← hm] at hP
  have hPpos : 0 < lawS n A := by rw [hP]; positivity
  have hgpos : 0 < gaussApprox n A := by unfold gaussApprox; positivity
  -- Stirling: `log k! = k log k - k + ½ log(2πk) + θ_k`
  have st : ∀ k : ℕ, Real.log (k.factorial : ℝ) =
      k * Real.log k - k + Real.log (2 * π * k) / 2 + stirErr k := by
    intro k; unfold stirErr; ring
  obtain ⟨θA0, θA1⟩ := stirErr_bounds (n := A) (by omega)
  obtain ⟨θn0, θn1⟩ := stirErr_bounds hn1
  obtain ⟨θm0, θm1⟩ := stirErr_bounds hm1
  -- the logarithmic deviation `Δ = log P - log g`
  set a := Real.log (1 + x / 2) with ha
  set b := Real.log (1 + x) with hb
  have hlogA : Real.log A = Real.log N + Real.log 2 + a := by
    rw [hAR, Real.log_mul (by positivity) (by linarith [abs_le.mp hxh]),
      Real.log_mul (by norm_num) hN0.ne']; ring
  have hlogm : Real.log m = Real.log N + b := by
    rw [hmR', Real.log_mul hN0.ne' (by linarith [abs_le.mp hx2])]
  have hlogP : Real.log (lawS n A) = Real.log N - Real.log A + Real.log (A.factorial : ℝ) -
      Real.log (n.factorial : ℝ) - Real.log (m.factorial : ℝ) - A * Real.log 2 := by
    rw [hP, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_div hN0.ne' hA0.ne', Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, one_div, Real.log_inv]
    ring
  have hlogg : Real.log (gaussApprox n A) = -(Real.log (4 * π * N) / 2) - d ^ 2 / (4 * N) := by
    unfold gaussApprox
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_rpow (by positivity),
      Real.log_inv, Real.log_exp]
    ring
  have h2π : ∀ k : ℝ, 0 < k → Real.log (2 * π * k) = Real.log 2 + Real.log π + Real.log k := by
    intro k hk
    rw [Real.log_mul (by positivity) hk.ne', Real.log_mul (by norm_num) Real.pi_pos.ne']
  have h4π : Real.log (4 * π * N) = 2 * Real.log 2 + Real.log π + Real.log N := by
    rw [Real.log_mul (by positivity) hN0.ne', Real.log_mul (by norm_num) Real.pi_pos.ne',
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  -- the main term `A a - m b + d²/(4N)` equals `N φ(x)`
  have hphi : (A : ℝ) * a - m * b + d ^ 2 / (4 * N) =
      N * ((2 + x) * a - (1 + x) * b + x ^ 2 / 4) := by
    rw [hmR', hAR, hx]; field_simp
  have hΔ : Real.log (lawS n A) - Real.log (gaussApprox n A) =
      N * ((2 + x) * a - (1 + x) * b + x ^ 2 / 4) - (a + b) / 2 +
        (stirErr A - stirErr n - stirErr m) := by
    rw [hlogP, hlogg, st A, st n, st m, h2π A hA0, h2π N hN0, h2π m hm0, hlogA, hlogm, h4π,
      ← hphi]
    have : (A : ℝ) = 2 * N + d := by rw [hd]; ring
    rw [show ((n : ℕ) : ℝ) = N from rfl]
    rw [hmR, this]
    ring
  -- bounding `Δ`
  set Δ := Real.log (lawS n A) - Real.log (gaussApprox n A) with hΔdef
  have hphiB := abs_phi_le hx2
  have haB := abs_log_one_add_le hxh
  have hbB := abs_log_one_add_le hx2
  have hθ : |stirErr A - stirErr n - stirErr m| ≤ 1 / N := by
    have hA' : 1 / (12 * (A : ℝ)) ≤ 1 / (12 * N) := by
      apply one_div_le_one_div_of_le (by positivity); linarith
    have hm' : 1 / (12 * (m : ℝ)) ≤ 1 / (6 * N) := by
      apply one_div_le_one_div_of_le (by positivity); rw [hmR]; linarith [(abs_le.mp hdN).1]
    have e1 : 1 / (12 * N) ≤ 1 / (4 * N) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have e2 : 1 / (6 * N) ≤ 1 / (2 * N) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have e3 : 1 / (4 * N) + 1 / (4 * N) + 1 / (2 * N) = 1 / N := by field_simp; ring
    rw [abs_le]; constructor <;> linarith
  have hx3 : N * |x| ^ 3 = |d| ^ 3 / N ^ 2 := by
    rw [hx, abs_div, abs_of_pos hN0]; field_simp
  have hΔB : |Δ| ≤ 4 * (|d| ^ 3 / N ^ 2) + 3 / 2 * (|d| / N) + 1 / N := by
    rw [hΔ]
    have hxN : |x| = |d| / N := by rw [hx, abs_div, abs_of_pos hN0]
    have t1 : |N * ((2 + x) * a - (1 + x) * b + x ^ 2 / 4)| ≤ 4 * (|d| ^ 3 / N ^ 2) := by
      rw [abs_mul, abs_of_pos hN0, ← hx3]; nlinarith
    have t2 : |(a + b) / 2| ≤ 3 / 2 * (|d| / N) := by
      rw [abs_div, abs_two, ← hxN]
      have := abs_add_le a b
      rw [abs_div, abs_two] at haB
      linarith
    calc _ ≤ |N * ((2 + x) * a - (1 + x) * b + x ^ 2 / 4) - (a + b) / 2| +
          |stirErr A - stirErr n - stirErr m| := abs_add_le _ _
      _ ≤ |N * ((2 + x) * a - (1 + x) * b + x ^ 2 / 4)| + |(a + b) / 2| +
          |stirErr A - stirErr n - stirErr m| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  -- small parameters: `|d|³/N² ≤ 1/s`, `|d|/N ≤ 1/s²`, `1/N ≤ 1/s⁵`
  have hp1 : |d| ^ 3 / N ^ 2 ≤ 1 / s := by
    rw [div_le_div_iff₀ (by positivity) hs0, hNs]
    have : |d| ^ 3 ≤ (s ^ 3) ^ 3 := pow_le_pow_left₀ (abs_nonneg d) hds 3
    calc |d| ^ 3 * s ≤ (s ^ 3) ^ 3 * s := mul_le_mul_of_nonneg_right this hs0.le
      _ = 1 * (s ^ 5) ^ 2 := by ring
  have hp2 : |d| / N ≤ 1 / s ^ 2 := by
    rw [div_le_div_iff₀ hN0 (by positivity), hNs]
    calc |d| * s ^ 2 ≤ s ^ 3 * s ^ 2 := mul_le_mul_of_nonneg_right hds (by positivity)
      _ = 1 * s ^ 5 := by ring
  have hp3 : 1 / N ≤ 1 / s ^ 2 := by
    rw [hNs]; apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by linarith) (by norm_num)
  have hΔ1 : |Δ| ≤ 1 := by
    have h1s : 1 / s ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hs8
    have h1s2 : 1 / s ^ 2 ≤ 1 / 8 := by
      apply one_div_le_one_div_of_le (by norm_num); nlinarith
    linarith
  -- `|P - g| = g |e^Δ - 1| ≤ 2 g |Δ|`
  have hPg : lawS n A = gaussApprox n A * Real.exp Δ := by
    rw [hΔdef, Real.exp_sub, Real.exp_log hPpos, Real.exp_log hgpos]; field_simp
  have hsq : (N : ℝ) ^ (-(1 : ℝ) / 2) = 1 / √N := by
    rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg hN0.le, Real.sqrt_eq_rpow]
    exact (one_div _).symm
  rw [hPg, hsq]
  exact local_limit_final hN0 (by linarith only [hn]) hgpos hΔB hΔ1

/-- **Lemma 2.2(iii)**, existential form. -/
theorem lawS_local_limit : ∃ C n₀ : ℝ, ∀ n : ℕ, n₀ ≤ n → ∀ A : ℕ,
    |(A : ℝ) - 2 * n| ≤ (n : ℝ) ^ ((3 : ℝ) / 5) →
      |lawS n A - gaussApprox n A| ≤
        C * gaussApprox n A * ((n : ℝ) ^ (-(1 : ℝ) / 2) + |(A : ℝ) - 2 * n| ^ 3 / (n : ℝ) ^ 2) :=
  ⟨12, 8 ^ 5, fun n hn A hA => lawS_local_limit_explicit n hn A hA⟩

end CollatzCLT
