import LeanClt.Renewal.LawS

/-!
# Lemma 2.2(i): the Chernoff bound for `S_n`

* `lawS_le`: `P(S_n = A) ≤ (A+1)^n 2^{-A}` (crude, for summability).
* `mgf_lawS`: `∑_A P(S_n = A) x^A = (x/(2-x))^n` for `0 ≤ x < 2`, from the memorylessness
  recursion.
* `exp_ratio_le`: `e^{-v}/(2 - e^v) ≤ e^{3v²}` for `|v| ≤ 1/4`, the paper's
  "`log E e^{v(a-2)} ≤ 3v²`".
* `lawS_chernoff`: `P(|S_n - 2n| ≥ x) ≤ 2 exp(-min(x²/(12n), x/8))`.
-/

open Real Finset Filter Topology

namespace CollatzCLT

/-- `P(S_n = A) ≤ (A+1)^n 2^{-A}`. -/
lemma lawS_le (n A : ℕ) : lawS n A ≤ ((A : ℝ) + 1) ^ n * (1 / 2 : ℝ) ^ A := by
  rcases n with _ | t
  · unfold lawS
    split_ifs with h
    · subst h; simp
    · positivity
  rcases A with _ | A
  · simp
  · rw [lawS_succ_succ_eq]
    gcongr
    push_cast
    calc (A.choose t : ℝ) ≤ (A : ℝ) ^ t := by exact_mod_cast Nat.choose_le_pow A t
      _ ≤ ((A : ℝ) + 1 + 1) ^ t := by gcongr; linarith
      _ ≤ ((A : ℝ) + 1 + 1) ^ (t + 1) := pow_le_pow_right₀ (by linarith) (Nat.le_succ t)

/-- `∑ (A+1)^n r^A` converges for `0 ≤ r < 1`. -/
lemma summable_succ_pow_mul_geometric (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun A : ℕ => ((A : ℝ) + 1) ^ n * r ^ A) := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one n (r := r) (by rwa [Real.norm_of_nonneg hr0])
  have h2 := summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (fun A => by positivity) (fun A => ?_)
    ((h1.add h2).mul_left (2 ^ n))
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · have h := one_le_pow₀ (a := (2 : ℝ)) (n := n) (by norm_num)
    have h0 : (0 : ℝ) ≤ 0 ^ n := pow_nonneg le_rfl n
    simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one]
    nlinarith
  · have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
    calc ((A : ℝ) + 1) ^ n * r ^ A ≤ (2 * (A : ℝ)) ^ n * r ^ A := by
          gcongr; linarith
      _ = 2 ^ n * ((A : ℝ) ^ n * r ^ A) := by ring
      _ ≤ 2 ^ n * ((A : ℝ) ^ n * r ^ A + r ^ A) := by gcongr; linarith [pow_nonneg hr0 A]

/-- The power series `∑ P(S_n = A) x^A` converges for `0 ≤ x < 2`. -/
lemma summable_lawS_mul_pow (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x < 2) :
    Summable (fun A : ℕ => lawS n A * x ^ A) := by
  refine Summable.of_nonneg_of_le (fun A => mul_nonneg (lawS_nonneg n A) (pow_nonneg hx0 A))
    (fun A => ?_) (summable_succ_pow_mul_geometric n (r := x / 2) (by positivity) (by linarith))
  calc lawS n A * x ^ A ≤ ((A : ℝ) + 1) ^ n * (1 / 2 : ℝ) ^ A * x ^ A := by
        gcongr; exact lawS_le n A
    _ = ((A : ℝ) + 1) ^ n * (x / 2) ^ A := by rw [div_pow, one_pow, div_pow]; ring

/-- **Generating function.** `∑_A P(S_n = A) x^A = (x/(2-x))^n` for `0 ≤ x < 2`. -/
theorem mgf_lawS (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x < 2) :
    ∑' A : ℕ, lawS n A * x ^ A = (x / (2 - x)) ^ n := by
  induction n with
  | zero =>
    rw [tsum_eq_single 0]
    · simp
    · intro A hA; simp [lawS, hA]
  | succ n ih =>
    have hs := summable_lawS_mul_pow (n + 1) hx0 hx2
    have hsn := summable_lawS_mul_pow n hx0 hx2
    have hrec : ∑' A : ℕ, lawS (n + 1) A * x ^ A =
        x / 2 * (x / (2 - x)) ^ n + x / 2 * ∑' A : ℕ, lawS (n + 1) A * x ^ A := by
      have : ∀ A : ℕ, lawS (n + 1) (A + 1) * x ^ (A + 1) =
          x / 2 * (lawS n A * x ^ A) + x / 2 * (lawS (n + 1) A * x ^ A) := by
        intro A; rw [lawS_succ_succ, pow_succ]; ring
      conv_lhs => rw [hs.tsum_eq_zero_add, lawS_succ_zero, zero_mul, zero_add]
      simp_rw [this]
      rw [(hsn.mul_left _).tsum_add (hs.mul_left _), tsum_mul_left, tsum_mul_left, ih]
    have h2 : (2 : ℝ) - x ≠ 0 := by linarith
    rw [pow_succ]
    field_simp
    linarith [hrec]

/-- **The exponential inequality.** For `|v| ≤ 1/4`: `2 - e^v > 0` and
`e^{-v} / (2 - e^v) ≤ e^{3v²}`. -/
lemma exp_ratio_le {v : ℝ} (hv : |v| ≤ 1 / 4) :
    0 < 2 - Real.exp v ∧ Real.exp (-v) / (2 - Real.exp v) ≤ Real.exp (3 * v ^ 2) := by
  have h1 := abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := v) (by linarith [abs_le.mp hv]))
  have h2 := abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := -v)
    (by rw [abs_neg]; linarith [abs_le.mp hv]))
  have h3 := Real.add_one_le_exp (3 * v ^ 2)
  have hvb := abs_le.mp hv
  have hpos : 0 < 2 - Real.exp v := by nlinarith
  refine ⟨hpos, ?_⟩
  rw [div_le_iff₀ hpos]
  -- `e^{-v} ≤ 1 - v + v² ≤ (1 - v - v²)(1 + 3v²) ≤ (2 - e^v) e^{3v²}`
  have hA : (1 - v - v ^ 2) * (1 + 3 * v ^ 2) ≤ (2 - Real.exp v) * Real.exp (3 * v ^ 2) := by
    apply mul_le_mul (by nlinarith) (by linarith) (by positivity) hpos.le
  have hq : 0 ≤ 1 - 3 * v - 3 * v ^ 2 := by nlinarith
  have hp : 1 - v + v ^ 2 ≤ (1 - v - v ^ 2) * (1 + 3 * v ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg v) hq]
  have he : Real.exp (-v) ≤ 1 - v + v ^ 2 := by nlinarith [h2.2]
  nlinarith [hA, hp, he]

/-- **Centred generating function.** For `|w| ≤ 1/4`,
`E e^{w(S_n - 2n)} = (e^{-w}/(2 - e^w))^n`. -/
lemma centred_mgf (n : ℕ) {w : ℝ} (hw : |w| ≤ 1 / 4) :
    ∑' A : ℕ, lawS n A * Real.exp (w * ((A : ℝ) - 2 * n)) =
      (Real.exp (-w) / (2 - Real.exp w)) ^ n := by
  have hpos := (exp_ratio_le hw).1
  have hx2 : Real.exp w < 2 := by linarith
  have : ∀ A : ℕ, lawS n A * Real.exp (w * ((A : ℝ) - 2 * n)) =
      Real.exp (-(2 * n * w)) * (lawS n A * Real.exp w ^ A) := by
    intro A
    rw [← Real.exp_nat_mul]
    rw [show w * ((A : ℝ) - 2 * n) = -(2 * n * w) + A * w by ring, Real.exp_add]
    ring
  simp_rw [this]
  rw [tsum_mul_left, mgf_lawS n (Real.exp_pos w).le hx2, div_pow, div_pow,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_div_assoc', ← Real.exp_add]
  congr 2; ring

/-- **Markov bound.** If `P A` forces `y ≤ w (A - 2n)` with `|w| ≤ 1/4`, then
`P(P(S_n)) ≤ exp(3 n w² - y)`. -/
lemma tail_generic (n : ℕ) {w y : ℝ} (hw : |w| ≤ 1 / 4) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ A, P A → y ≤ w * ((A : ℝ) - 2 * n)) :
    ∑' A : ℕ, (if P A then lawS n A else 0) ≤ Real.exp (3 * n * w ^ 2 - y) := by
  obtain ⟨hpos, hratio⟩ := exp_ratio_le hw
  have hx2 : Real.exp w < 2 := by linarith
  have hsum : Summable (fun A : ℕ => lawS n A * Real.exp (w * ((A : ℝ) - 2 * n))) := by
    have := (summable_lawS_mul_pow n (Real.exp_pos w).le hx2).mul_left (Real.exp (-(2 * n * w)))
    refine this.congr (fun A => ?_)
    rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
    congr 2; ring
  calc ∑' A : ℕ, (if P A then lawS n A else 0)
      ≤ ∑' A : ℕ, Real.exp (-y) * (lawS n A * Real.exp (w * ((A : ℝ) - 2 * n))) := by
        refine Summable.tsum_le_tsum (fun A => ?_) ?_ (hsum.mul_left _)
        · split_ifs with h
          · rw [mul_left_comm, ← Real.exp_add]
            have : 0 ≤ -y + w * ((A : ℝ) - 2 * n) := by linarith [hP A h]
            nlinarith [Real.one_le_exp this, lawS_nonneg n A]
          · exact mul_nonneg (Real.exp_pos _).le
              (mul_nonneg (lawS_nonneg n A) (Real.exp_pos _).le)
        · refine Summable.of_nonneg_of_le (fun A => by split_ifs <;> simp [lawS_nonneg])
            (fun A => ?_) (summable_lawS_mul_pow n zero_le_one one_lt_two)
          split_ifs <;> simp [lawS_nonneg]
    _ = Real.exp (-y) * (Real.exp (-w) / (2 - Real.exp w)) ^ n := by
        rw [tsum_mul_left, centred_mgf n hw]
    _ ≤ Real.exp (-y) * Real.exp (3 * w ^ 2) ^ n := by gcongr
    _ = Real.exp (3 * n * w ^ 2 - y) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf

/-- **Lemma 2.2(i), Chernoff.** For `n ≥ 1` and `x ≥ 0`,
`P(|S_n - 2n| ≥ x) ≤ 2 exp(-min(x²/(12n), x/8))`. -/
theorem lawS_chernoff {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    ∑' A : ℕ, (if x ≤ |(A : ℝ) - 2 * n| then lawS n A else 0) ≤
      2 * Real.exp (-min (x ^ 2 / (12 * n)) (x / 8)) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set v := min (x / (6 * n)) (1 / 4) with hv
  have hv0 : 0 ≤ v := le_min (by positivity) (by norm_num)
  have hv1 : v ≤ 1 / 4 := min_le_right _ _
  have hvabs : |v| ≤ 1 / 4 := by rw [abs_of_nonneg hv0]; exact hv1
  have hvabs' : |-v| ≤ 1 / 4 := by rw [abs_neg]; exact hvabs
  -- the two one-sided tails
  have hup := tail_generic n hvabs (fun A => x ≤ (A : ℝ) - 2 * n) (y := v * x)
    (fun A h => by nlinarith)
  have hlo := tail_generic n hvabs' (fun A => x ≤ 2 * n - (A : ℝ)) (y := v * x)
    (fun A h => by nlinarith)
  -- the two-sided tail is at most their sum
  have hs1 : Summable (fun A : ℕ => if x ≤ (A : ℝ) - 2 * n then lawS n A else 0) :=
    Summable.of_nonneg_of_le (fun A => by split_ifs <;> simp [lawS_nonneg])
      (fun A => by split_ifs <;> simp [lawS_nonneg]) (summable_lawS_mul_pow n zero_le_one one_lt_two)
  have hs2 : Summable (fun A : ℕ => if x ≤ 2 * n - (A : ℝ) then lawS n A else 0) :=
    Summable.of_nonneg_of_le (fun A => by split_ifs <;> simp [lawS_nonneg])
      (fun A => by split_ifs <;> simp [lawS_nonneg]) (summable_lawS_mul_pow n zero_le_one one_lt_two)
  have hsplit : ∑' A : ℕ, (if x ≤ |(A : ℝ) - 2 * n| then lawS n A else 0) ≤
      ∑' A : ℕ, (if x ≤ (A : ℝ) - 2 * n then lawS n A else 0) +
        ∑' A : ℕ, (if x ≤ 2 * n - (A : ℝ) then lawS n A else 0) := by
    rw [← hs1.tsum_add hs2]
    refine Summable.tsum_le_tsum (fun A => ?_) ?_ (hs1.add hs2)
    · have h0 := lawS_nonneg n A
      by_cases h1 : x ≤ |(A : ℝ) - 2 * n|
      · rcases abs_cases ((A : ℝ) - 2 * n) with ⟨ha, _⟩ | ⟨ha, _⟩
        · have h2 : x ≤ (A : ℝ) - 2 * n := by rw [ha] at h1; exact h1
          simp only [h1, h2, ite_true]
          split_ifs <;> linarith
        · have h2 : x ≤ 2 * n - (A : ℝ) := by rw [ha] at h1; linarith
          simp only [h1, h2, ite_true]
          split_ifs <;> linarith
      · simp only [h1, ite_false]
        split_ifs <;> linarith
    · exact Summable.of_nonneg_of_le (fun A => by split_ifs <;> simp [lawS_nonneg])
        (fun A => by split_ifs <;> simp [lawS_nonneg])
        (summable_lawS_mul_pow n zero_le_one one_lt_two)
  -- the exponent: `3 n v² - v x ≤ -min(x²/(12n), x/8)`
  have hexp : 3 * n * v ^ 2 - v * x ≤ -min (x ^ 2 / (12 * n)) (x / 8) := by
    rcases le_total (x / (6 * n)) (1 / 4) with h | h
    · have : v = x / (6 * n) := min_eq_left h
      rw [this]
      have : 3 * n * (x / (6 * n)) ^ 2 - x / (6 * n) * x = -(x ^ 2 / (12 * n)) := by
        field_simp; ring
      rw [this, neg_le_neg_iff]
      exact min_le_left _ _
    · have : v = 1 / 4 := min_eq_right h
      rw [this]
      have hx' : 3 * n / 2 ≤ x := by
        have h' : 1 / 4 ≤ x / (6 * n) := h
        rw [le_div_iff₀ (by positivity)] at h'; linarith
      have : 3 * n * (1 / 4 : ℝ) ^ 2 - 1 / 4 * x ≤ -(x / 8) := by nlinarith
      exact this.trans (neg_le_neg (min_le_right _ _))
  calc _ ≤ _ := hsplit
    _ ≤ Real.exp (3 * n * v ^ 2 - v * x) + Real.exp (3 * n * (-v) ^ 2 - v * x) := add_le_add hup hlo
    _ = 2 * Real.exp (3 * n * v ^ 2 - v * x) := by rw [neg_sq]; ring
    _ ≤ 2 * Real.exp (-min (x ^ 2 / (12 * n)) (x / 8)) := by gcongr

end CollatzCLT
