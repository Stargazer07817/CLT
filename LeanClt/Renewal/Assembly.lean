import LeanClt.Renewal.Poisson
import LeanClt.Renewal.Abel

/-!
# Theorem 4.1: the explicit (non-asymptotic) error bound

For `u` in the regime of the Gaussian window with window half-width `X`, and `|ρ s| ≤ 1`,
`|s(ρθ + η)| ≤ 1`, the twisted renewal kernel differs from the main term
`(1/c) exp(-i(2ρ+η)su/c - (ρβ+ηℓ)²s²u/c³)` by at most a sum of seven explicit error terms:
the tail outside the window, the extra endpoint, the Gaussian replacement, Abel summation against
the rotation, the Gaussian tail and the Poisson dual terms, and `m_v - 1/ℓ`.
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-! ## Generic helpers -/

lemma tsum_eq_sum_add_tsum_ite {ι : Type*} [DecidableEq ι] {f : ι → ℂ} (hf : Summable f)
    (S : Finset ι) : ∑' i, f i = ∑ i ∈ S, f i + ∑' i, (if i ∈ S then 0 else f i) := by
  rw [← hf.sum_add_tsum_compl (s := S), tsum_subtype ((↑S : Set ι)ᶜ) f]
  congr 1
  refine tsum_congr fun i => ?_
  by_cases hi : i ∈ S <;> simp [hi, Set.indicator]

lemma norm_cexp_I_sub_le (a b : ℝ) :
    ‖cexp (-((a : ℝ) : ℂ) * I) - cexp (-((b : ℝ) : ℂ) * I)‖ ≤ |a - b| := by
  have h : cexp (-((a : ℝ) : ℂ) * I) - cexp (-((b : ℝ) : ℂ) * I) =
      cexp (-((b : ℝ) : ℂ) * I) * (cexp (I * ((-(a - b) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [h, norm_mul, norm_cexp_neg_real_mul_I, one_mul]
  refine norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_neg]

/-! ## The window as a finset -/

/-- The window `{t : |t - t₀| ≤ X}`. -/
def Wset (u X : ℝ) : Finset ℕ := Icc ⌈t0 u - X⌉₊ ⌊t0 u + X⌋₊

lemma mem_Wset {u X : ℝ} (hX : 0 ≤ X) (h : X ≤ t0 u) (t : ℕ) :
    t ∈ Wset u X ↔ |(t : ℝ) - t0 u| ≤ X := by
  rw [Wset, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (by linarith), abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma card_Wset_le {u X : ℝ} (hX : 0 ≤ X) (h : X ≤ t0 u) :
    ((Wset u X).card : ℝ) ≤ 2 * X + 1 := by
  rw [Wset, Nat.card_Icc]
  have h1 : (⌊t0 u + X⌋₊ : ℝ) ≤ t0 u + X := Nat.floor_le (by linarith)
  have h2 : t0 u - X ≤ (⌈t0 u - X⌉₊ : ℝ) := Nat.le_ceil _
  rcases le_or_gt (⌊t0 u + X⌋₊ + 1) ⌈t0 u - X⌉₊ with hle | hlt
  · rw [Nat.sub_eq_zero_of_le hle]; simp; linarith
  · rw [Nat.cast_sub hlt.le]; push_cast; linarith

/-- Reindexing `[a, b]` as `a - 1 + [1, b + 1 - a]`. -/
lemma sum_Icc_reindex {M : Type*} [AddCommMonoid M] (F : ℕ → M) (a b : ℕ) :
    ∑ t ∈ Icc a b, F t = ∑ j ∈ Icc 1 (b + 1 - a), F (a + j - 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  rw [show b + 1 - a + 1 - 1 = b + 1 - a by omega]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1; omega

/-! ## The weights `w_t = g_u(t) e^{-iαt}` -/

/-- `w(t) = g_u(t) e^{-iαt}`. -/
def wR (u α t : ℝ) : ℂ := (gU u t : ℂ) * cexp (-((α * t : ℝ) : ℂ) * I)

lemma norm_wR (u α t : ℝ) : ‖wR u α t‖ = gU u t := norm_gU_mul_cexp u α t

lemma Kg_le {u : ℝ} (hu : 0 < u) : Kg u ≤ 1 / u := by
  unfold Kg
  rw [div_le_div_iff₀ (by have := ell_pos; positivity) hu]
  have h1 : c ^ 3 ≤ 1 := pow_le_one₀ c_pos'.le (by linarith [c_lt_third])
  have h2 : (1 : ℝ) ≤ 4 * ell ^ 2 := by nlinarith [ell_gt]
  nlinarith

lemma prefactor_le {u : ℝ} (hu : 0 < u) : (Real.sqrt (4 * π * t0 u))⁻¹ ≤ (Real.sqrt u)⁻¹ := by
  apply inv_sqrt_anti hu
  unfold t0
  have : u ≤ u / c := by rw [le_div_iff₀ c_pos']; nlinarith [c_lt_third]
  nlinarith [Real.pi_gt_three]

/-- **Discrete Lipschitz bound for the weights.** -/
lemma norm_wR_succ_sub_le {u X α t : ℝ} (hu : 0 < u) (ht : |t - t0 u| ≤ X + 1) :
    ‖wR u α (t + 1) - wR u α t‖ ≤ (Real.sqrt u)⁻¹ * ((2 * X + 3) / u + |α|) := by
  have hK := Kg_pos hu
  have hP := prefactor_le hu
  set P := (Real.sqrt (4 * π * t0 u))⁻¹
  have hP0 : 0 ≤ P := by positivity
  have hg : |gU u (t + 1) - gU u t| ≤ (Real.sqrt u)⁻¹ * ((2 * X + 3) / u) := by
    unfold gU
    rw [← mul_sub, abs_mul, abs_of_nonneg hP0]
    have he := abs_exp_neg_sub_le (a := Kg u * (t + 1 - t0 u) ^ 2) (b := Kg u * (t - t0 u) ^ 2)
      (by positivity) (by positivity)
    have hdiff : |Kg u * (t + 1 - t0 u) ^ 2 - Kg u * (t - t0 u) ^ 2| ≤ (2 * X + 3) / u := by
      rw [show Kg u * (t + 1 - t0 u) ^ 2 - Kg u * (t - t0 u) ^ 2 =
        Kg u * (2 * (t - t0 u) + 1) by ring, abs_mul, abs_of_pos hK]
      have h1 : |2 * (t - t0 u) + 1| ≤ 2 * X + 3 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two, abs_one]; linarith
      calc Kg u * |2 * (t - t0 u) + 1| ≤ 1 / u * (2 * X + 3) :=
            mul_le_mul (Kg_le hu) h1 (abs_nonneg _) (by positivity)
        _ = (2 * X + 3) / u := by ring
    exact mul_le_mul hP (he.trans hdiff) (abs_nonneg _) (by positivity)
  have hgt : gU u t ≤ (Real.sqrt u)⁻¹ := gU_le hu t
  unfold wR
  have e : (gU u (t + 1) : ℂ) * cexp (-((α * (t + 1) : ℝ) : ℂ) * I) -
      (gU u t : ℂ) * cexp (-((α * t : ℝ) : ℂ) * I) =
      ((gU u (t + 1) - gU u t : ℝ) : ℂ) * cexp (-((α * (t + 1) : ℝ) : ℂ) * I) +
        (gU u t : ℂ) * (cexp (-((α * (t + 1) : ℝ) : ℂ) * I) - cexp (-((α * t : ℝ) : ℂ) * I)) := by
    push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_cexp_neg_real_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gU_nonneg u t)]
  have h3 := norm_cexp_I_sub_le (α * (t + 1)) (α * t)
  rw [show α * (t + 1) - α * t = α by ring] at h3
  calc |gU u (t + 1) - gU u t| + gU u t *
        ‖cexp (-((α * (t + 1) : ℝ) : ℂ) * I) - cexp (-((α * t : ℝ) : ℂ) * I)‖
      ≤ (Real.sqrt u)⁻¹ * ((2 * X + 3) / u) + (Real.sqrt u)⁻¹ * |α| := by
        gcongr
    _ = (Real.sqrt u)⁻¹ * ((2 * X + 3) / u + |α|) := by ring

/-! ## The error terms -/

/-- **Tail outside the window.** -/
lemma err_tail (ρ η s : ℝ) {u X : ℝ} (hu : 0 < u) (hX1 : 2 * ell / c ≤ X) (hX2 : X ≤ u)
    (hXT : X ≤ t0 u) :
    ‖∑' t : ℕ, (if t ∈ Wset u X then 0 else rinner ρ η s u t)‖ ≤
      8 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u)) := by
  have hX0 : 0 ≤ X := le_trans (by have := c_pos'; have := ell_pos; positivity) hX1
  obtain ⟨hs, hle⟩ := window_tail hu hX1 hX2
  have hpt : ∀ t : ℕ, ‖(if t ∈ Wset u X then 0 else rinner ρ η s u t)‖ ≤
      2 * (if X ≤ |(t : ℝ) - u / c| then pwin u t else 0) := by
    intro t
    by_cases ht : t ∈ Wset u X
    · simp only [ht, ↓reduceIte, norm_zero]
      have := pwin_nonneg u t; split_ifs <;> linarith
    · simp only [ht, ↓reduceIte]
      have hX : X ≤ |(t : ℝ) - u / c| := by
        rw [mem_Wset hX0 hXT] at ht; push Not at ht; exact ht.le
      simp only [hX, ↓reduceIte]
      exact norm_rinner_le ρ η s u t
  have hs2 := hs.mul_left 2
  have hsn : Summable (fun t : ℕ => ‖(if t ∈ Wset u X then 0 else rinner ρ η s u t)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hs2
  calc _ ≤ ∑' t : ℕ, ‖(if t ∈ Wset u X then 0 else rinner ρ η s u t)‖ :=
        norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' t : ℕ, 2 * (if X ≤ |(t : ℝ) - u / c| then pwin u t else 0) :=
        Summable.tsum_le_tsum hpt hsn hs2
    _ = 2 * ∑' t : ℕ, (if X ≤ |(t : ℝ) - u / c| then pwin u t else 0) := tsum_mul_left
    _ ≤ 2 * (4 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u))) := by gcongr
    _ = _ := by ring

lemma hT_pos {u : ℝ} (hu : 0 < u) (t : ℕ) : 0 < hT u t := by
  unfold hT; have := bet_pos; have := ell_pos; positivity

lemma hT_eq (u : ℝ) (t : ℝ) : (u + bet * t) / ell = u / ell + θ * t := by
  rw [θ_eq]; field_simp [ell_pos.ne']

/-- **The extra endpoint.** -/
lemma err_extra {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (ρ η s : ℝ) {u X : ℝ} (hR : Regime u X)
    (hXT : X ≤ t0 u) :
    ‖∑ t ∈ Wset u X, ∑ A ∈ Ioc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1), rterm ρ η s u t A‖ ≤
      50 * (Real.sqrt u)⁻¹ := by
  have hu := hR.u_pos
  have hX0 := hR.X_pos.le
  have hs0 : 0 ≤ (Real.sqrt u)⁻¹ := by positivity
  refine norm_sum_le_of_unique (by positivity) (fun t ht => ?_) (fun t ht t' ht' h1 h2 => ?_)
  · rw [mem_Wset hX0 hXT] at ht
    have := norm_extra_le ρ η s u t (B := 25 * (Real.sqrt u)⁻¹) (by positivity)
      (fun A h1 h2 => lawS_le_window hR ht (by rw [abs_le]; constructor <;> linarith))
    linarith
  · have hne1 := Finset.nonempty_of_sum_ne_zero h1
    have hne2 := Finset.nonempty_of_sum_ne_zero h2
    have e1 := eq_floor_of_extra (hT_pos hu t).le hne1
    have e2 := eq_floor_of_extra (hT_pos hu t').le hne2
    exact extra_unique hθ (n := (⌊hT u t⌋₊ : ℤ)) (n' := (⌊hT u t'⌋₊ : ℤ))
      (by rw [e1]; simp) (by rw [e2]; simp)

/-- **Gaussian replacement.** -/
lemma err_gauss (ρ η s : ℝ) {u X : ℝ} (hR : Regime u X) (hXT : X ≤ t0 u) :
    ‖∑ t ∈ Wset u X, rterm ρ η s u t ⌈hT u t⌉₊ -
      cexp (-(((ρ * s * u / ell) : ℝ) : ℂ) * I) *
        ∑ t ∈ Wset u X, wR u (s * (ρ * θ + η)) t * qv (ρ * s) (hT u t)‖ ≤
      ((Wset u X).card : ℝ) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) := by
  have hu := hR.u_pos
  have hX0 := hR.X_pos.le
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun t ht => ?_
  rw [mem_Wset hX0 hXT] at ht
  rw [rterm_ceil ρ η s u t (hT_pos hu t).le]
  unfold wR
  set Φ := cexp (-(((ρ * s * u / ell) : ℝ) : ℂ) * I) *
    cexp (-(((s * (ρ * θ + η) * t) : ℝ) : ℂ) * I) * qv (ρ * s) (hT u t)
  have e : (lawS t ⌈hT u t⌉₊ : ℂ) * Φ - cexp (-(((ρ * s * u / ell) : ℝ) : ℂ) * I) *
      ((gU u t : ℂ) * cexp (-((s * (ρ * θ + η) * t : ℝ) : ℂ) * I) * qv (ρ * s) (hT u t)) =
      ((lawS t ⌈hT u t⌉₊ - gU u t : ℝ) : ℂ) * Φ := by
    simp only [Φ]; push_cast; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hΦ : ‖Φ‖ ≤ 2 := by
    simp only [Φ]
    rw [norm_mul, norm_mul, norm_cexp_neg_real_mul_I, norm_cexp_neg_real_mul_I, one_mul, one_mul]
    exact norm_qv_le _ _
  have hA : |((⌈hT u t⌉₊ : ℕ) : ℝ) - hT u t| ≤ 1 := by
    have h1 := Nat.le_ceil (hT u t)
    have h2 := Nat.ceil_lt_add_one (hT_pos hu t).le
    rw [abs_le]; constructor <;> linarith
  have hb := lawS_sub_gU_le hR ht hA
  calc |lawS t ⌈hT u t⌉₊ - gU u t| * ‖Φ‖ ≤ (33 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) * 2 :=
        mul_le_mul hb hΦ (norm_nonneg _) (by have := hR.sqrt_pos; positivity)
    _ = 66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹ := by ring

/-- **Abel summation against the rotation, on the window.** -/
lemma err_rot {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v α u X : ℝ), Regime u X → |v| ≤ 1 →
      ‖∑ t ∈ Wset u X, wR u α t * (qv v (hT u t) - mv v)‖ ≤
        C * ((Wset u X).card : ℝ) ^ (1 - 1 / (ϰ + 1)) *
          ((Real.sqrt u)⁻¹ * (1 + (Wset u X).card * ((2 * X + 3) / u + |α|))) := by
  obtain ⟨C, hC0, hC⟩ := rotation_abel hθ
  refine ⟨C, hC0, fun v α u X hR hv => ?_⟩
  have hu := hR.u_pos
  have hXu := hR.X_le_u
  have hT3 := hR.t0_ge
  set a := ⌈t0 u - X⌉₊ with ha
  set b := ⌊t0 u + X⌋₊ with hb
  set N := b + 1 - a with hN
  have hcard : (Wset u X).card = N := by rw [Wset, Nat.card_Icc]
  have ha1 : 1 ≤ a := by
    rw [ha, Nat.one_le_ceil_iff]; linarith
  have haR : t0 u - X ≤ (a : ℝ) := Nat.le_ceil _
  have haR2 : (a : ℝ) < t0 u - X + 1 := Nat.ceil_lt_add_one (by linarith)
  have hbR : (b : ℝ) ≤ t0 u + X := Nat.floor_le (by linarith [hR.X_pos])
  set γ' : ℝ := u / ell + θ * ((a : ℝ) - 1)
  set w' : ℕ → ℂ := fun j => wR u α ((a + j - 1 : ℕ) : ℝ)
  have hcast : ∀ j : ℕ, ((a + j - 1 : ℕ) : ℝ) = (a : ℝ) + j - 1 := by
    intro j; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hsum : ∑ t ∈ Wset u X, wR u α t * (qv v (hT u t) - mv v) =
      ∑ j ∈ Icc 1 N, w' j * (qv v (γ' + j * θ) - mv v) := by
    rw [Wset, sum_Icc_reindex]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w']
    congr 3
    rw [hT, hT_eq, hcast]; ring
  rw [hsum, hcard]
  refine (hC v hv γ' w' N).trans ?_
  have hs0 : 0 ≤ (Real.sqrt u)⁻¹ := by have := hR.sqrt_pos; positivity
  have hwN : ‖w' N‖ ≤ (Real.sqrt u)⁻¹ := by
    simp only [w']; rw [norm_wR]; exact gU_le hu _
  have hdiff : ∀ j ∈ range N, ‖w' (j + 1) - w' j‖ ≤
      (Real.sqrt u)⁻¹ * ((2 * X + 3) / u + |α|) := by
    intro j hj
    have hjN := Finset.mem_range.mp hj
    simp only [w']
    rw [hcast, hcast, show (a : ℝ) + ((j + 1 : ℕ) : ℝ) - 1 = ((a : ℝ) + j - 1) + 1 by
      push_cast; ring]
    apply norm_wR_succ_sub_le hu
    have hjb : (a : ℝ) + j ≤ b := by
      have : a + j ≤ b := by omega
      exact_mod_cast this
    rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hsumd : ∑ j ∈ range N, ‖w' (j + 1) - w' j‖ ≤
      N * ((Real.sqrt u)⁻¹ * ((2 * X + 3) / u + |α|)) := by
    calc _ ≤ ∑ j ∈ range N, (Real.sqrt u)⁻¹ * ((2 * X + 3) / u + |α|) :=
          Finset.sum_le_sum hdiff
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hNp : 0 ≤ C * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) := by positivity
  calc C * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) * (‖w' N‖ + ∑ j ∈ range N, ‖w' (j + 1) - w' j‖)
      ≤ C * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) *
          ((Real.sqrt u)⁻¹ + N * ((Real.sqrt u)⁻¹ * ((2 * X + 3) / u + |α|))) := by
        gcongr
    _ = C * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) *
          ((Real.sqrt u)⁻¹ * (1 + N * ((2 * X + 3) / u + |α|))) := by ring

/-- **Gaussian tail:** extending the window sum of `w` to all of `ℤ`. -/
lemma err_gtail (α : ℝ) {u X : ℝ} (hR : Regime u X) (hXT : X ≤ t0 u) :
    ‖∑' z : ℤ, wR u α z - ∑ t ∈ Wset u X, wR u α t‖ ≤
      (Real.sqrt u)⁻¹ * (2 * Real.exp (-(Kg u * X * X / 2)) * (1 + 2 / (Kg u * X))) := by
  classical
  have hu := hR.u_pos
  have hX := hR.X_pos
  have hK := Kg_pos hu
  set S : Finset ℤ := (Wset u X).map Nat.castEmbedding with hS
  have hsumS : ∑ t ∈ Wset u X, wR u α t = ∑ z ∈ S, wR u α z := by
    rw [hS, Finset.sum_map]; simp
  have hsm : Summable (fun z : ℤ => wR u α z) := summable_gU_mul_cexp u α hu
  rw [hsumS, tsum_eq_sum_add_tsum_ite hsm S, add_sub_cancel_left]
  have hT0 : X ≤ t0 u := hXT
  have hpt : ∀ z : ℤ, ‖(if z ∈ S then 0 else wR u α z)‖ ≤ (Real.sqrt u)⁻¹ *
      (if X ≤ |(z : ℝ) - t0 u| then Real.exp (-(Kg u * X) * |(z : ℝ) - t0 u|) else 0) := by
    intro z
    by_cases hz : z ∈ S
    · simp only [hz, ↓reduceIte, norm_zero]
      apply mul_nonneg (by positivity); split_ifs <;> positivity
    · simp only [hz, ↓reduceIte]
      have hfar : X ≤ |(z : ℝ) - t0 u| := by
        by_contra hcon
        push Not at hcon
        apply hz
        have hz0 : 0 ≤ z := by
          have := neg_abs_le ((z : ℝ) - t0 u)
          have : (0 : ℝ) ≤ z := by linarith [hR.t0_ge, hR.X_le_u]
          exact_mod_cast this
        rw [hS, Finset.mem_map]
        refine ⟨z.toNat, ?_, by simp [hz0]⟩
        rw [mem_Wset hX.le hXT]
        have : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
          have := Int.toNat_of_nonneg hz0
          exact_mod_cast this
        rw [this]; exact hcon.le
      simp only [hfar, ↓reduceIte]
      rw [norm_wR]
      unfold gU
      apply mul_le_mul (prefactor_le hu) _ (by positivity) (by positivity)
      apply Real.exp_le_exp.mpr
      have : X * |(z : ℝ) - t0 u| ≤ ((z : ℝ) - t0 u) ^ 2 := by
        rw [← sq_abs]; nlinarith [abs_nonneg ((z : ℝ) - t0 u)]
      nlinarith
  obtain ⟨hs2, hle2⟩ := int_geom_tail (Kg u * X) (t0 u) X (by positivity)
  have hs3 := hs2.mul_left (Real.sqrt u)⁻¹
  have hsn : Summable (fun z : ℤ => ‖(if z ∈ S then 0 else wR u α z)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hs3
  calc _ ≤ ∑' z : ℤ, ‖(if z ∈ S then 0 else wR u α z)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' z : ℤ, (Real.sqrt u)⁻¹ * (if X ≤ |(z : ℝ) - t0 u| then
          Real.exp (-(Kg u * X) * |(z : ℝ) - t0 u|) else 0) :=
        Summable.tsum_le_tsum hpt hsn hs3
    _ = (Real.sqrt u)⁻¹ * ∑' z : ℤ, (if X ≤ |(z : ℝ) - t0 u| then
          Real.exp (-(Kg u * X) * |(z : ℝ) - t0 u|) else 0) := tsum_mul_left
    _ ≤ _ := by gcongr

/-! ## Assembly -/

/-- The main term `(1/c) exp(-i(2ρ+η)su/c - (ρβ+ηℓ)² s² u/c³)` of Theorem 4.1. -/
def mainTerm (ρ η s u : ℝ) : ℂ :=
  (1 / c : ℂ) * cexp (-(I * (((2 * ρ + η) / c * s * u : ℝ) : ℂ)) -
    ((((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u) : ℝ) : ℂ))

/-- The main term is the exterior phase times `1/ℓ` times the `n = 0` Poisson term. -/
lemma mainTerm_eq (ρ η s u : ℝ) :
    mainTerm ρ η s u = cexp (-(((ρ * s * u / ell) : ℝ) : ℂ) * I) * (1 / (ell : ℂ)) *
      (((ell / c : ℝ) : ℂ) * cexp (-(((s * (ρ * θ + η)) ^ 2 * ell ^ 2 * u / c ^ 3 : ℝ) : ℂ) -
        (((s * (ρ * θ + η)) * t0 u : ℝ) : ℂ) * I)) := by
  have hc := c_pos'; have hl := ell_pos
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hlC : (ell : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  unfold mainTerm
  have hexp : -(I * (((2 * ρ + η) / c * s * u : ℝ) : ℂ)) -
      ((((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u) : ℝ) : ℂ) =
      -(((ρ * s * u / ell) : ℝ) : ℂ) * I +
        (-(((s * (ρ * θ + η)) ^ 2 * ell ^ 2 * u / c ^ 3 : ℝ) : ℂ) -
          (((s * (ρ * θ + η)) * t0 u : ℝ) : ℂ) * I) := by
    have hb : bet = 2 * ell - c := by rw [c_eq]; ring
    unfold t0
    rw [θ_eq, hb]
    push_cast
    field_simp
    ring
  rw [hexp, Complex.exp_add]
  push_cast
  field_simp

lemma norm_mainPoisson_le (α : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ‖((ell / c : ℝ) : ℂ) * cexp (-((α ^ 2 * ell ^ 2 * u / c ^ 3 : ℝ) : ℂ) -
      ((α * t0 u : ℝ) : ℂ) * I)‖ ≤ ell / c := by
  have hc := c_pos'; have hl := ell_pos
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), Complex.norm_exp]
  have : (-((α ^ 2 * ell ^ 2 * u / c ^ 3 : ℝ) : ℂ) - ((α * t0 u : ℝ) : ℂ) * I).re =
      -(α ^ 2 * ell ^ 2 * u / c ^ 3) := by
    rw [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re,
      mul_zero, sub_zero]
  rw [this]
  have h1 : Real.exp (-(α ^ 2 * ell ^ 2 * u / c ^ 3)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]; positivity
  calc ell / c * Real.exp (-(α ^ 2 * ell ^ 2 * u / c ^ 3)) ≤ ell / c * 1 := by gcongr
    _ = ell / c := mul_one _

/-- **The explicit error bound behind Theorem 4.1**, an intermediate step rather than a form of
the theorem (it has no range of `s` and no exponent). Under `IrrMeasure d ϰ` there is `Crot ≥ 0`,
depending only on `d, ϰ` (from Lemma 2.7 [`lem:rotation`] through `err_rot`), such that
for all real `ρ, η, s, u, X` with `Regime u X` (`8⁵ ≤ u`, `√u ≤ X ≤ u^{3/5}`), `2ℓ/c ≤ X`
(implied by `Regime`), `|ρs| ≤ 1` and `|s(ρθ+η)| ≤ 1`, the error is at most the sum of the seven
error terms of the module docstring, written as six summands (the fifth combines the Gaussian
tail and the Poisson dual terms). `twisted_renewal_main` takes `X = u^{1/2+1/(10(ϰ+1))}`. -/
theorem renewal_error_bound {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∃ Crot : ℝ, 0 ≤ Crot ∧ ∀ (ρ η s u X : ℝ), Regime u X → 2 * ell / c ≤ X →
      |ρ * s| ≤ 1 → |s * (ρ * θ + η)| ≤ 1 →
      ‖renewalR ρ η s u - mainTerm ρ η s u‖ ≤
        8 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u)) +
        50 * (Real.sqrt u)⁻¹ +
        ((Wset u X).card : ℝ) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) +
        Crot * ((Wset u X).card : ℝ) ^ (1 - 1 / (ϰ + 1)) *
          ((Real.sqrt u)⁻¹ * (1 + (Wset u X).card * ((2 * X + 3) / u + |s * (ρ * θ + η)|))) +
        2 * (ell / c * (4 * Real.exp (-(u / 4))) +
          (Real.sqrt u)⁻¹ * (2 * Real.exp (-(Kg u * X * X / 2)) * (1 + 2 / (Kg u * X)))) +
        (2 * ell + 1) / ell ^ 2 * |ρ * s| * (ell / c) := by
  classical
  obtain ⟨Crot, hC0, hrot⟩ := err_rot hθ
  refine ⟨Crot, hC0, fun ρ η s u X hR hX1 hv hα => ?_⟩
  have hu := hR.u_pos
  have hXT : X ≤ t0 u := by linarith [hR.X_le_u, hR.t0_ge]
  set W := Wset u X with hW
  set v := ρ * s with hvdef
  set α := s * (ρ * θ + η) with hαdef
  set ph := cexp (-(((ρ * s * u / ell) : ℝ) : ℂ) * I) with hph
  set m := mv v with hm
  set Gm := ((ell / c : ℝ) : ℂ) * cexp (-((α ^ 2 * ell ^ 2 * u / c ^ 3 : ℝ) : ℂ) -
      ((α * t0 u : ℝ) : ℂ) * I) with hGm
  set Etail := ∑' t : ℕ, (if t ∈ W then 0 else rinner ρ η s u t) with hEtail
  set Sex := ∑ t ∈ W, ∑ A ∈ Ioc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1), rterm ρ η s u t A with hSex
  set Srt := ∑ t ∈ W, rterm ρ η s u t ⌈hT u t⌉₊ with hSrt
  set SwQ := ∑ t ∈ W, wR u α t * qv v (hT u t) with hSwQ
  set Eg := Srt - ph * SwQ with hEg
  set Erot := ∑ t ∈ W, wR u α t * (qv v (hT u t) - m) with hErot
  set Sw := ∑ t ∈ W, wR u α t with hSw
  set SZ := ∑' z : ℤ, wR u α z with hSZ
  set Egt := SZ - Sw with hEgt
  set Ep := SZ - Gm with hEp
  have e1 : renewalR ρ η s u = (Srt + Sex) + Etail := by
    rw [renewalR_eq, tsum_eq_sum_add_tsum_ite (summable_rinner ρ η s u) W]
    congr 1
    rw [hSrt, hSex, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => rinner_eq_add ρ η s u t
  have e4 : SwQ = Erot + m * Sw := by
    rw [hSwQ, hErot, hSw, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have e7 : mainTerm ρ η s u = ph * (1 / (ell : ℂ)) * Gm := mainTerm_eq ρ η s u
  have key : renewalR ρ η s u - mainTerm ρ η s u =
      Etail + Sex + Eg + ph * Erot + ph * m * (Ep - Egt) + ph * (m - 1 / (ell : ℂ)) * Gm := by
    rw [e1, e7, hEg, hEp, hEgt]
    linear_combination ph * e4
  rw [key]
  -- the norms
  have hph : ‖ph‖ = 1 := norm_cexp_neg_real_mul_I _
  have hm2 : ‖m‖ ≤ 2 := norm_mv_le v
  have hGm : ‖Gm‖ ≤ ell / c := norm_mainPoisson_le α hu.le
  have b1 := err_tail ρ η s hu hX1 hR.X_le_u hXT
  have b2 := err_extra hθ ρ η s hR hXT
  have b3 := err_gauss ρ η s hR hXT
  have b4 := hrot v α u X hR hv
  have b5 := err_gtail α hR hXT
  have b6 := gauss_sum_main u α hR.one_le_u hα
  have b7 := norm_mv_sub_le v
  have hEgt' : ‖Egt‖ ≤ (Real.sqrt u)⁻¹ *
      (2 * Real.exp (-(Kg u * X * X / 2)) * (1 + 2 / (Kg u * X))) := b5
  have hEp' : ‖Ep‖ ≤ ell / c * (4 * Real.exp (-(u / 4))) := by
    rw [hEp, hSZ]
    have : (∑' z : ℤ, wR u α z) = ∑' t : ℤ, (gU u t : ℂ) * cexp (-((α * t : ℝ) : ℂ) * I) := rfl
    rw [this]; exact b6
  have hEmm : ‖ph * m * (Ep - Egt)‖ ≤ 2 * (ell / c * (4 * Real.exp (-(u / 4))) +
      (Real.sqrt u)⁻¹ * (2 * Real.exp (-(Kg u * X * X / 2)) * (1 + 2 / (Kg u * X)))) := by
    rw [norm_mul, norm_mul, hph, one_mul]
    exact mul_le_mul hm2 ((norm_sub_le _ _).trans (add_le_add hEp' hEgt')) (norm_nonneg _)
      (by norm_num)
  have hErot' : ‖ph * Erot‖ ≤ Crot * ((W.card : ℝ)) ^ (1 - 1 / (ϰ + 1)) *
      ((Real.sqrt u)⁻¹ * (1 + W.card * ((2 * X + 3) / u + |α|))) := by
    rw [norm_mul, hph, one_mul]; exact b4
  have hlast : ‖ph * (m - 1 / (ell : ℂ)) * Gm‖ ≤ (2 * ell + 1) / ell ^ 2 * |v| * (ell / c) := by
    rw [norm_mul, norm_mul, hph, one_mul]
    exact mul_le_mul b7 hGm (norm_nonneg _) (by have := ell_pos; positivity)
  calc ‖Etail + Sex + Eg + ph * Erot + ph * m * (Ep - Egt) + ph * (m - 1 / (ell : ℂ)) * Gm‖
      ≤ ‖Etail‖ + ‖Sex‖ + ‖Eg‖ + ‖ph * Erot‖ + ‖ph * m * (Ep - Egt)‖ +
          ‖ph * (m - 1 / (ell : ℂ)) * Gm‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ ≤ _ := by
        gcongr

end CollatzCLT
