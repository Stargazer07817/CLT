import LeanClt.Renewal.Rotation
import LeanClt.Renewal.LawS

/-!
# §4.1: the exact reduction and the rotation kernel `q_v`

* constants: `ℓ, β > 0`, `c = 2ℓ - β`, `1 < θ < 2`, `e^ℓ = 2`.
* `qv v x = exp((ℓ - i v)(⌈x⌉ - x))`, the kernel (4.5, `eq:q`); `‖qv‖ ≤ 2`, and `qv v - m_v` satisfies the
  hypotheses of Lemma 2.7 [`lem:rotation`] with `x₀ = 0`, `M = 4`, `L = 40` when `|v| ≤ 1`.
* `mv v = ∫₀¹ qv v = (2e^{-iv} - 1)/(ℓ - iv)` and `‖m_v - 1/ℓ‖ ≤ (2ℓ+1)/ℓ² |v|` (4.6, `eq:mean`).
* the window condition `0 ≤ Z_t - u ≤ ℓ` is `h_t ≤ A ≤ h_t + 1`, `h_t = (u + βt)/ℓ`, and the
  `A`-series is the finite sum over `[⌈h_t⌉₊, ⌊h_t⌋₊ + 1]` (exact reduction (4.4, `eq:exact`)); its first
  term is `P(S_t = A_t) e^{-iρsu/ℓ} e^{-is(ρθ+η)t} q_{ρs}(h_t)`.
-/

open Real Finset Complex MeasureTheory intervalIntegral

noncomputable section

namespace CollatzCLT

/-! ## Constants -/

lemma ell_pos : 0 < ell := Real.log_pos (by norm_num)

lemma bet_pos : 0 < bet := Real.log_pos (by norm_num)

lemma c_pos' : 0 < c := Real.log_pos (by norm_num)

lemma exp_ell : Real.exp ell = 2 := Real.exp_log (by norm_num)

lemma c_eq : c = 2 * ell - bet := by
  unfold c ell bet
  rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast; ring

lemma θ_eq : θ = bet / ell := rfl

lemma ell_lt_one : ell < 1 := by
  unfold ell; have := Real.log_two_lt_d9; linarith

lemma ell_gt : (0.69 : ℝ) < ell := by
  unfold ell; have := Real.log_two_gt_d9; linarith

lemma one_lt_θ : 1 < θ := by
  rw [θ_eq, one_lt_div ell_pos]
  exact Real.log_lt_log (by norm_num) (by norm_num)

lemma θ_lt_two : θ < 2 := by
  rw [θ_eq, div_lt_iff₀ ell_pos]
  have : bet < 2 * ell := by have := c_pos'; rw [c_eq] at this; linarith
  linarith

/-! ## The kernel `q_v` -/

/-- `q_v(x) = exp((ℓ - i v)(⌈x⌉ - x))`. -/
def qv (v x : ℝ) : ℂ := cexp (((ell : ℂ) - v * I) * (((⌈x⌉ : ℝ) - x : ℝ) : ℂ))

/-- `m_v = ∫₀¹ q_v`. -/
def mv (v : ℝ) : ℂ := ∫ x in (0 : ℝ)..1, qv v x

lemma qv_add_one (v x : ℝ) : qv v (x + 1) = qv v x := by
  unfold qv; rw [Int.ceil_add_one]; push_cast; ring_nf

lemma ceil_sub_mem (x : ℝ) : 0 ≤ (⌈x⌉ : ℝ) - x ∧ (⌈x⌉ : ℝ) - x < 1 := by
  constructor
  · linarith [Int.le_ceil x]
  · linarith [Int.ceil_lt_add_one x]

lemma norm_cexp_ell_mul {v r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖cexp (((ell : ℂ) - v * I) * (r : ℂ))‖ ≤ 2 := by
  rw [Complex.norm_exp]
  have : (((ell : ℂ) - v * I) * (r : ℂ)).re = ell * r := by simp
  rw [this, ← exp_ell]
  exact Real.exp_le_exp.mpr (by nlinarith [ell_pos])

lemma norm_qv_le (v x : ℝ) : ‖qv v x‖ ≤ 2 :=
  norm_cexp_ell_mul (ceil_sub_mem x).1 (ceil_sub_mem x).2.le

/-- On the cell `(0, 1]`, `q_v(x) = exp((ℓ - iv)(1 - x))`. -/
lemma qv_of_mem {v x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) :
    qv v x = cexp (((ell : ℂ) - v * I) * ((1 - x : ℝ) : ℂ)) := by
  have : ⌈x⌉ = 1 := by rw [Int.ceil_eq_iff]; norm_num; exact ⟨h0, h1⟩
  unfold qv; rw [this]; push_cast; ring_nf

lemma norm_cexp_sub_cexp_le' (z : ℂ) {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (hz : z.re = ell) :
    ‖cexp (z * a) - cexp (z * b)‖ ≤ 2 * ‖z‖ * Real.exp ‖z‖ * |a - b| := by
  have hsplit : cexp (z * a) - cexp (z * b) = cexp (z * b) * (cexp (z * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; push_cast; ring_nf
  have h1 : ‖cexp (z * b)‖ ≤ 2 := by
    rw [Complex.norm_exp]
    have : (z * (b : ℂ)).re = ell * b := by simp [hz]
    rw [this, ← exp_ell]; exact Real.exp_le_exp.mpr (by nlinarith [ell_pos])
  have h2 : ‖cexp (z * ((a - b : ℝ) : ℂ)) - 1‖ ≤ ‖z‖ * |a - b| * Real.exp ‖z‖ := by
    have := Complex.norm_exp_sub_sum_le_norm_mul_exp (z * ((a - b : ℝ) : ℂ)) 1
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      pow_one] at this
    refine this.trans ?_
    have hn : ‖z * ((a - b : ℝ) : ℂ)‖ = ‖z‖ * |a - b| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hab : |a - b| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    rw [hn]
    gcongr
    calc ‖z‖ * |a - b| ≤ ‖z‖ * 1 := by gcongr
      _ = ‖z‖ := mul_one _
  rw [hsplit, norm_mul]
  calc ‖cexp (z * b)‖ * ‖cexp (z * ((a - b : ℝ) : ℂ)) - 1‖
      ≤ 2 * (‖z‖ * |a - b| * Real.exp ‖z‖) := by gcongr
    _ = 2 * ‖z‖ * Real.exp ‖z‖ * |a - b| := by ring

lemma norm_ell_sub_le {v : ℝ} (hv : |v| ≤ 1) : ‖(ell : ℂ) - v * I‖ ≤ 2 := by
  calc ‖(ell : ℂ) - v * I‖ ≤ ‖(ell : ℂ)‖ + ‖(v : ℂ) * I‖ := norm_sub_le _ _
    _ = ell + |v| := by
        rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ell_pos]
    _ ≤ 2 := by linarith [ell_lt_one]

lemma norm_mv_le (v : ℝ) : ‖mv v‖ ≤ 2 := by
  unfold mv
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 2)
    (f := qv v) (fun x _ => norm_qv_le v x)
  simpa using this

/-- `q_v` is Lipschitz with constant `40` on `(0, 1]` when `|v| ≤ 1`. -/
lemma qv_lip {v : ℝ} (hv : |v| ≤ 1) (x y : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y)
    (hy1 : y ≤ 1) : ‖qv v x - qv v y‖ ≤ 40 * |x - y| := by
  rw [qv_of_mem hx0 hx1, qv_of_mem hy0 hy1]
  have hz : ((ell : ℂ) - v * I).re = ell := by simp
  have := norm_cexp_sub_cexp_le' ((ell : ℂ) - v * I) (a := 1 - x) (b := 1 - y)
    (by linarith) (by linarith) (by linarith) (by linarith) hz
  refine this.trans ?_
  have hn := norm_ell_sub_le hv
  have he : Real.exp ‖(ell : ℂ) - v * I‖ ≤ 9 := by
    calc Real.exp ‖(ell : ℂ) - v * I‖ ≤ Real.exp 2 := Real.exp_le_exp.mpr hn
      _ = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 3 * 3 := by
          have := Real.exp_one_lt_d9
          have h0 := Real.exp_pos 1
          nlinarith
      _ = 9 := by norm_num
  have hxy : |1 - x - (1 - y)| = |x - y| := by rw [show 1 - x - (1 - y) = -(x - y) by ring, abs_neg]
  rw [hxy]
  have h0 : 0 ≤ ‖(ell : ℂ) - v * I‖ := norm_nonneg _
  have := abs_nonneg (x - y)
  have : 2 * ‖(ell : ℂ) - v * I‖ * Real.exp ‖(ell : ℂ) - v * I‖ ≤ 40 := by
    have := Real.exp_pos ‖(ell : ℂ) - v * I‖
    nlinarith
  nlinarith

/-- **(4.6, `eq:mean`)** `m_v = (2e^{-iv} - 1)/(ℓ - iv)`. -/
lemma mv_eq (v : ℝ) : mv v = (2 * cexp (-(v * I)) - 1) / ((ell : ℂ) - v * I) := by
  set z : ℂ := (ell : ℂ) - v * I with hz
  have hz0 : z ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hz] at this; linarith [ell_pos]
  have h1 : mv v = ∫ x in (0 : ℝ)..1, cexp (z * ((1 - x : ℝ) : ℂ)) := by
    unfold mv
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hx
    exact qv_of_mem hx.1 hx.2
  have h2 : (∫ x in (0 : ℝ)..1, cexp (z * ((1 - x : ℝ) : ℂ))) = ∫ x in (0 : ℝ)..1, cexp (z * x) := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
      (fun x : ℝ => cexp (z * (x : ℂ))) 1
    simpa using this
  rw [h1, h2, integral_exp_mul_complex hz0]
  congr 1
  have : z * ((1 : ℝ) : ℂ) = (ell : ℂ) + (-(v * I)) := by rw [hz]; push_cast; ring
  rw [this, Complex.exp_add, ← Complex.ofReal_exp, exp_ell]
  simp

/-- **(4.6, `eq:mean`)** `‖m_v - 1/ℓ‖ ≤ (2ℓ+1)/ℓ² · |v|`. -/
lemma norm_mv_sub_le (v : ℝ) : ‖mv v - 1 / (ell : ℂ)‖ ≤ (2 * ell + 1) / ell ^ 2 * |v| := by
  have hl := ell_pos
  set z : ℂ := (ell : ℂ) - v * I with hz
  have hz0 : z ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hz] at this; linarith
  have hl0 : (ell : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hzn : ell ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    have hre : z.re = ell := by simp [hz]
    rw [hre, abs_of_pos hl] at this; exact this
  rw [mv_eq]
  have key : (2 * cexp (-(v * I)) - 1) / z - 1 / (ell : ℂ) =
      (2 * (ell : ℂ) * (cexp (I * ((-v : ℝ) : ℂ)) - 1) + v * I) / ((ell : ℂ) * z) := by
    field_simp
    rw [hz]; push_cast; ring_nf
  rw [key, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
  have hnum : ‖2 * (ell : ℂ) * (cexp (I * ((-v : ℝ) : ℂ)) - 1) + v * I‖ ≤ (2 * ell + 1) * |v| := by
    calc _ ≤ ‖2 * (ell : ℂ) * (cexp (I * ((-v : ℝ) : ℂ)) - 1)‖ + ‖(v : ℂ) * I‖ := norm_add_le _ _
      _ ≤ 2 * ell * |v| + |v| := by
          gcongr
          · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
            simp only [Complex.norm_ofNat]
            have := norm_exp_I_mul_ofReal_sub_one_le (x := -v)
            rw [Real.norm_eq_abs, abs_neg] at this
            nlinarith
          · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      _ = (2 * ell + 1) * |v| := by ring
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ (2 * ell + 1) * |v| := hnum
    _ = (2 * ell + 1) / ell ^ 2 * |v| * (ell * ell) := by field_simp
    _ ≤ (2 * ell + 1) / ell ^ 2 * |v| * (ell * ‖z‖) := by gcongr

/-- **Lemma 2.7 [`lem:rotation`] applies to `q_v - m_v`** with `x₀ = 0`, `M = 4`, `L = 40`, for `|v| ≤ 1`. -/
lemma piecewiseLip_qv {v : ℝ} (hv : |v| ≤ 1) :
    PiecewiseLip (fun x => qv v x - mv v) 4 40 0 where
  per x := by simp only [qv_add_one]
  bdd x := by
    calc ‖qv v x - mv v‖ ≤ ‖qv v x‖ + ‖mv v‖ := norm_sub_le _ _
      _ ≤ 2 + 2 := add_le_add (norm_qv_le v x) (norm_mv_le v)
      _ = 4 := by norm_num
  lip x y hx0 hx1 hy0 hy1 := by
    simp only [sub_sub_sub_cancel_right]
    exact qv_lip hv x y hx0 (by linarith) hy0 (by linarith)

lemma intervalIntegrable_qv {v : ℝ} (hv : |v| ≤ 1) (a b : ℝ) :
    IntervalIntegrable (qv v) volume a b := by
  have h := ((piecewiseLip_qv hv).intervalIntegrable a b).add
    (intervalIntegrable_const (c := mv v))
  simpa using h

/-- `q_v - m_v` has mean zero on `[0, 1]`. -/
lemma integral_qv_sub_mv {v : ℝ} (hv : |v| ≤ 1) :
    ∫ x in (0 : ℝ)..1, (qv v x - mv v) = 0 := by
  rw [intervalIntegral.integral_sub (intervalIntegrable_qv hv 0 1) intervalIntegrable_const]
  simp [mv]

/-! ## The exact reduction (4.4, `eq:exact`) -/

/-- `h_t = (u + βt)/ℓ`. -/
def hT (u : ℝ) (t : ℕ) : ℝ := (u + bet * t) / ell

/-- The `(t, A)` term of `R^{ρ,η}_s(u)`. -/
def rterm (ρ η s u : ℝ) (t A : ℕ) : ℂ :=
  if 0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell then
    (lawS t A : ℂ) * (Real.exp (Zval t A - u) : ℂ) * cexp (-(((s * (ρ * A + η * t)) : ℝ) : ℂ) * I)
  else 0

/-- The `t`-th term of `R^{ρ,η}_s(u)`. -/
def rinner (ρ η s u : ℝ) (t : ℕ) : ℂ := ∑' A : ℕ, rterm ρ η s u t A

lemma renewalR_eq (ρ η s u : ℝ) : renewalR ρ η s u = ∑' t : ℕ, rinner ρ η s u t := rfl

lemma Zval_sub (u : ℝ) (t A : ℕ) : Zval t A - u = ell * ((A : ℝ) - hT u t) := by
  unfold Zval hT; field_simp [ell_pos.ne']; ring

lemma window_iff (u : ℝ) (t A : ℕ) :
    (0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell) ↔ (hT u t ≤ A ∧ (A : ℝ) ≤ hT u t + 1) := by
  rw [Zval_sub]
  have hl := ell_pos
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

lemma mem_Icc_of_window {u : ℝ} {t A : ℕ} (h1 : hT u t ≤ A) (h2 : (A : ℝ) ≤ hT u t + 1) :
    A ∈ Icc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1) := by
  rw [Finset.mem_Icc]
  refine ⟨Nat.ceil_le.mpr h1, ?_⟩
  rcases Nat.eq_zero_or_pos A with hA | hA
  · omega
  · have : A - 1 ≤ ⌊hT u t⌋₊ := by
      apply Nat.le_floor
      rw [Nat.cast_sub hA]; push_cast; linarith
    omega

lemma rterm_eq_zero {ρ η s u : ℝ} {t A : ℕ} (hA : A ∉ Icc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1)) :
    rterm ρ η s u t A = 0 := by
  unfold rterm
  split_ifs with h
  · rw [window_iff] at h; exact absurd (mem_Icc_of_window h.1 h.2) hA
  · rfl

lemma rinner_eq_sum (ρ η s u : ℝ) (t : ℕ) :
    rinner ρ η s u t = ∑ A ∈ Icc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1), rterm ρ η s u t A :=
  tsum_eq_sum (fun _ hA => rterm_eq_zero hA)

/-- The reward-free term is real and nonnegative. -/
lemma rterm_zero (u : ℝ) (t A : ℕ) :
    rterm 0 0 0 u t A = ((if 0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell then
      lawS t A * Real.exp (Zval t A - u) else 0 : ℝ) : ℂ) := by
  unfold rterm
  split_ifs <;> simp

lemma norm_rterm_eq (ρ η s u : ℝ) (t A : ℕ) :
    ‖rterm ρ η s u t A‖ = (if 0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell then
      lawS t A * Real.exp (Zval t A - u) else 0) := by
  unfold rterm
  split_ifs with h
  · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (lawS_nonneg _ _), abs_of_pos (Real.exp_pos _)]
    have : ‖cexp (-(((s * (ρ * A + η * t)) : ℝ) : ℂ) * I)‖ = 1 := by
      rw [show -(((s * (ρ * A + η * t)) : ℝ) : ℂ) * I = ((-(s * (ρ * A + η * t)) : ℝ) : ℂ) * I by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [this, mul_one]
  · simp

lemma norm_rterm_le (ρ η s u : ℝ) (t A : ℕ) : ‖rterm ρ η s u t A‖ ≤ 2 * lawS t A := by
  rw [norm_rterm_eq]
  split_ifs with h
  · rw [mul_comm 2]
    gcongr
    · exact lawS_nonneg _ _
    · rw [← exp_ell]; exact Real.exp_le_exp.mpr h.2
  · have := lawS_nonneg t A; linarith

/-- **(4.4, `eq:exact`), the first window term.** For `h_t ≥ 0` the term at `A_t = ⌈h_t⌉₊` is
`P(S_t = A_t) e^{-iρsu/ℓ} e^{-is(ρθ+η)t} q_{ρs}(h_t)`. -/
lemma rterm_ceil (ρ η s u : ℝ) (t : ℕ) (hh : 0 ≤ hT u t) :
    rterm ρ η s u t ⌈hT u t⌉₊ = (lawS t ⌈hT u t⌉₊ : ℂ) *
      (cexp (-(((ρ * s * u / ell) : ℝ) : ℂ) * I) *
        cexp (-(((s * (ρ * θ + η) * t) : ℝ) : ℂ) * I) * qv (ρ * s) (hT u t)) := by
  set h := hT u t with hhdef
  have hc : ((⌈h⌉₊ : ℕ) : ℝ) = ((⌈h⌉ : ℤ) : ℝ) := by
    rw [← Int.natCast_ceil_eq_ceil hh]; rfl
  have hw : 0 ≤ Zval t ⌈h⌉₊ - u ∧ Zval t ⌈h⌉₊ - u ≤ ell := by
    rw [window_iff]
    exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one hh).le⟩
  unfold rterm qv
  simp only [hw, and_self, ↓reduceIte]
  rw [mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [← hc]
  have hl : (ell : ℂ) ≠ 0 := by exact_mod_cast ell_pos.ne'
  unfold Zval
  rw [hhdef]; unfold hT θ
  simp only [ell, bet] at hl ⊢
  push_cast
  field_simp
  ring

/-! ## The extra endpoint -/

/-- The `t`-th term splits as the `A_t` term plus the extra endpoint sum (over `Ioc`). -/
lemma rinner_eq_add (ρ η s u : ℝ) (t : ℕ) :
    rinner ρ η s u t = rterm ρ η s u t ⌈hT u t⌉₊ +
      ∑ A ∈ Ioc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1), rterm ρ η s u t A := by
  rw [rinner_eq_sum, Finset.add_sum_Ioc_eq_sum_Icc (Nat.ceil_le_floor_add_one _)]

/-- The extra endpoint occurs only when `h_t` is an integer. -/
lemma eq_floor_of_extra {h : ℝ} (hh : 0 ≤ h) (hne : (Ioc ⌈h⌉₊ (⌊h⌋₊ + 1)).Nonempty) :
    h = ⌊h⌋₊ := by
  obtain ⟨A, hA⟩ := hne
  rw [Finset.mem_Ioc] at hA
  have h1 : ⌈h⌉₊ ≤ ⌊h⌋₊ := by omega
  have h2 : h ≤ ⌈h⌉₊ := Nat.le_ceil h
  have h3 : (⌊h⌋₊ : ℝ) ≤ h := Nat.floor_le hh
  have h4 : (⌈h⌉₊ : ℝ) ≤ ⌊h⌋₊ := by exact_mod_cast h1
  linarith

/-- Each window term is bounded by `2B` when `P(S_t = A) ≤ B` on the window. -/
lemma norm_rterm_le_of {ρ η s u : ℝ} {t A : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : hT u t ≤ A → (A : ℝ) ≤ hT u t + 1 → lawS t A ≤ B) :
    ‖rterm ρ η s u t A‖ ≤ 2 * B := by
  by_cases hw : 0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell
  · rw [window_iff] at hw
    exact (norm_rterm_le ρ η s u t A).trans (by linarith [hB hw.1 hw.2])
  · unfold rterm; simp only [hw, ↓reduceIte, norm_zero]; linarith

/-- The extra endpoint sum has at most one term, bounded by `2B` if `P(S_t = A) ≤ B` on the
window. -/
lemma norm_extra_le (ρ η s u : ℝ) (t : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ A : ℕ, hT u t ≤ A → (A : ℝ) ≤ hT u t + 1 → lawS t A ≤ B) :
    ‖∑ A ∈ Ioc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1), rterm ρ η s u t A‖ ≤ 2 * B := by
  set h := hT u t
  have hcard : (Ioc ⌈h⌉₊ (⌊h⌋₊ + 1)).card ≤ 1 := by
    rw [Nat.card_Ioc]; have := Nat.floor_le_ceil h; omega
  calc _ ≤ ∑ A ∈ Ioc ⌈h⌉₊ (⌊h⌋₊ + 1), ‖rterm ρ η s u t A‖ := norm_sum_le _ _
    _ ≤ ∑ A ∈ Ioc ⌈h⌉₊ (⌊h⌋₊ + 1), 2 * B :=
        Finset.sum_le_sum fun A _ => norm_rterm_le_of hB0 (hB A)
    _ = (Ioc ⌈h⌉₊ (⌊h⌋₊ + 1)).card * (2 * B) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * (2 * B) := by gcongr; exact_mod_cast hcard
    _ = 2 * B := one_mul _

/-- **Uniqueness of the extra endpoint.** Under Rhin's measure `θ` is irrational, so `h_t` is an
integer for at most one `t`. -/
lemma extra_unique {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) {u : ℝ} {t t' : ℕ} {n n' : ℤ}
    (ht : hT u t = n) (ht' : hT u t' = n') : t = t' := by
  obtain ⟨hd, -, hrhin⟩ := hθ
  have key : ∀ a b : ℕ, ∀ m m' : ℤ, hT u a = m → hT u b = m' → b < a → False := by
    intro a b m m' ha hb hab
    have hk : 1 ≤ a - b := by omega
    have hdiff : ((a - b : ℕ) : ℝ) * θ = ((m - m' : ℤ) : ℝ) := by
      rw [Nat.cast_sub hab.le]; push_cast; rw [← ha, ← hb]; unfold hT; rw [θ_eq]
      field_simp [ell_pos.ne']; ring
    have h1 := hrhin (a - b) hk
    have h2 : distZ (((a - b : ℕ) : ℝ) * θ) = 0 := by
      rw [hdiff]; unfold distZ; rw [round_intCast]; simp
    rw [h2] at h1
    have : 0 < d * (((a - b : ℕ) : ℝ)) ^ (-ϰ) := by
      have : (0 : ℝ) < ((a - b : ℕ) : ℝ) := by exact_mod_cast (show 0 < a - b by omega)
      positivity
    linarith
  rcases lt_trichotomy t t' with h | h | h
  · exact (key t' t n' n ht' ht h).elim
  · exact h
  · exact (key t t' n n' ht ht' h).elim

/-- A finite sum with at most one nonzero term. -/
lemma norm_sum_le_of_unique {W : Finset ℕ} {f : ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ W, ‖f t‖ ≤ B) (huniq : ∀ t ∈ W, ∀ t' ∈ W, f t ≠ 0 → f t' ≠ 0 → t = t') :
    ‖∑ t ∈ W, f t‖ ≤ B := by
  by_cases hex : ∃ t ∈ W, f t ≠ 0
  · obtain ⟨t0, ht0, hf0⟩ := hex
    rw [Finset.sum_eq_single_of_mem t0 ht0 (fun t ht hne => by
      by_contra hft; exact hne (huniq t ht t0 ht0 hft hf0))]
    exact hB t0 ht0
  · push Not at hex
    rw [Finset.sum_eq_zero hex, norm_zero]; exact hB0

end CollatzCLT
