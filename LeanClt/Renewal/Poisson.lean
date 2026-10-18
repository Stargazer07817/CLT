import LeanClt.Renewal.GaussWindow

/-!
# §4.3: the Gaussian sum, by Poisson summation

`∑_{t ∈ ℤ} g_u(t) e^{-iαt} = (ℓ/c) ∑_{n ∈ ℤ} exp(-(π²/K)(n + α/2π)² - i(2πn + α)t₀)`
(Mathlib's `Complex.tsum_exp_neg_quadratic`). The `n = 0` term is the paper's Gaussian integral
`(ℓ/c) exp(-iαt₀ - α²ℓ²u/c³)`; for `|α| ≤ 1` and `u ≥ 1` the others total at most
`(ℓ/c) · 4e^{-u/4}`. This replaces the paper's sum-to-integral comparison by an exact identity.
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-- Gaussian sums over `ℤ` converge: `e^{-κ y²} ≤ e^{κ/4} e^{-κ|y|}`. -/
lemma summable_gauss_int {κ : ℝ} (hκ : 0 < κ) (t0' : ℝ) :
    Summable (fun t : ℤ => Real.exp (-(κ * ((t : ℝ) - t0') ^ 2))) := by
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun t => ?_)
    ((int_geom κ t0' hκ).1.mul_left (Real.exp (κ / 4)))
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : ((t : ℝ) - t0') ^ 2 = |(t : ℝ) - t0'| ^ 2 := (sq_abs _).symm
  have h2 : 0 ≤ (|(t : ℝ) - t0'| - 1 / 2) ^ 2 := sq_nonneg _
  rw [h1]; nlinarith

lemma Kg_pos {u : ℝ} (hu : 0 < u) : 0 < Kg u := by
  unfold Kg; have := c_pos'; have := ell_pos; positivity

lemma t0_pos {u : ℝ} (hu : 0 < u) : 0 < t0 u := by unfold t0; exact div_pos hu c_pos'

/-- The pointwise form of `g_u(t) e^{-iαt}` as a complex Gaussian. -/
lemma gU_mul_cexp (u α : ℝ) (t : ℝ) :
    (gU u t : ℂ) * cexp (-((α * t : ℝ) : ℂ) * I) =
      (((Real.sqrt (4 * π * t0 u))⁻¹ * Real.exp (-(Kg u * t0 u ^ 2)) : ℝ) : ℂ) *
        cexp (-π * ((Kg u / π : ℝ) : ℂ) * (t : ℂ) ^ 2 +
          2 * π * (((2 * Kg u * t0 u / (2 * π) : ℝ) : ℂ) - ((α / (2 * π) : ℝ) : ℂ) * I) * t) := by
  unfold gU
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  push_cast
  rw [mul_assoc, ← Complex.exp_add]
  conv_rhs => rw [mul_assoc, ← Complex.exp_add]
  congr 2
  field_simp
  ring

/-- `4 t₀ K = (c/ℓ)²`. -/
lemma four_t0_Kg {u : ℝ} (hu : 0 < u) : 4 * π * t0 u * (Kg u / π) = (c / ell) ^ 2 := by
  have := c_pos'; have := ell_pos; have := Real.pi_pos
  unfold t0 Kg; field_simp

/-- The prefactor: `(4πt₀)^{-1/2} (K/π)^{-1/2} = ℓ/c`. -/
lemma prefactor_eq {u : ℝ} (hu : 0 < u) :
    (Real.sqrt (4 * π * t0 u))⁻¹ * (Real.sqrt (Kg u / π))⁻¹ = ell / c := by
  have hc := c_pos'; have hl := ell_pos
  rw [← mul_inv, ← Real.sqrt_mul (by have := t0_pos hu; positivity), four_t0_Kg hu,
    Real.sqrt_sq (by positivity), inv_div]

/-- The dual terms of Poisson summation. -/
lemma dual_term (u α : ℝ) (hu : 0 < u) (n : ℤ) :
    (((Real.sqrt (4 * π * t0 u))⁻¹ * Real.exp (-(Kg u * t0 u ^ 2)) : ℝ) : ℂ) *
      (1 / ((Kg u / π : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        cexp (-π / ((Kg u / π : ℝ) : ℂ) *
          ((n : ℂ) + I * (((2 * Kg u * t0 u / (2 * π) : ℝ) : ℂ) - ((α / (2 * π) : ℝ) : ℂ) * I)) ^ 2)) =
    ((ell / c : ℝ) : ℂ) * cexp (-(((π ^ 2 / Kg u) * (n + α / (2 * π)) ^ 2 : ℝ) : ℂ) -
      ((((2 * π * n + α) * t0 u) : ℝ) : ℂ) * I) := by
  have hK := Kg_pos hu
  have hpi := Real.pi_pos
  have hKpi : 0 ≤ Kg u / π := by positivity
  -- the complex square root of the real `K/π`
  have hsq : ((Kg u / π : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (Kg u / π) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hKpi]; push_cast; norm_num
  rw [hsq]
  have hpre := prefactor_eq hu
  have hs0 : Real.sqrt (Kg u / π) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  -- split off the real prefactor
  have hsplit : (((Real.sqrt (4 * π * t0 u))⁻¹ * Real.exp (-(Kg u * t0 u ^ 2)) : ℝ) : ℂ) *
      (1 / ((Real.sqrt (Kg u / π) : ℝ) : ℂ) * cexp (-π / ((Kg u / π : ℝ) : ℂ) *
        ((n : ℂ) + I * (((2 * Kg u * t0 u / (2 * π) : ℝ) : ℂ) - ((α / (2 * π) : ℝ) : ℂ) * I)) ^ 2)) =
      (((Real.sqrt (4 * π * t0 u))⁻¹ * (Real.sqrt (Kg u / π))⁻¹ : ℝ) : ℂ) *
        (cexp (-((Kg u * t0 u ^ 2 : ℝ) : ℂ)) * cexp (-π / ((Kg u / π : ℝ) : ℂ) *
          ((n : ℂ) + I * (((2 * Kg u * t0 u / (2 * π) : ℝ) : ℂ) -
            ((α / (2 * π) : ℝ) : ℂ) * I)) ^ 2)) := by
    push_cast; ring
  rw [hsplit, hpre, ← Complex.exp_add]
  congr 2
  have hpiC : (π : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  have hKC : (Kg u : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have hIb : ∀ B1 B2 : ℂ, I * (B1 - B2 * I) = B2 + B1 * I := by
    intro B1 B2; ring_nf; rw [Complex.I_sq]; ring
  have hsq2 : ∀ x B1 B2 : ℂ, (x + (B2 + B1 * I)) ^ 2 = ((x + B2) ^ 2 - B1 ^ 2) +
      2 * (x + B2) * B1 * I := by
    intro x B1 B2; ring_nf; rw [Complex.I_sq]; ring
  rw [hIb, hsq2]
  push_cast
  field_simp
  ring

/-- **Poisson summation for the window Gaussian.** -/
theorem gauss_poisson (u α : ℝ) (hu : 0 < u) :
    ∑' t : ℤ, (gU u t : ℂ) * cexp (-((α * t : ℝ) : ℂ) * I) =
      ∑' n : ℤ, ((ell / c : ℝ) : ℂ) * cexp (-(((π ^ 2 / Kg u) * (n + α / (2 * π)) ^ 2 : ℝ) : ℂ) -
        ((((2 * π * n + α) * t0 u) : ℝ) : ℂ) * I) := by
  have hK := Kg_pos hu
  have ha : 0 < (((Kg u / π : ℝ)) : ℂ).re := by
    rw [Complex.ofReal_re]; exact div_pos hK Real.pi_pos
  rw [tsum_congr (fun t : ℤ => by rw [gU_mul_cexp u α t, Complex.ofReal_intCast]), tsum_mul_left,
    Complex.tsum_exp_neg_quadratic ha, ← tsum_mul_left, ← tsum_mul_left]
  exact tsum_congr (dual_term u α hu)

lemma norm_cexp_neg_real_mul_I (x : ℝ) : ‖cexp (-((x : ℝ) : ℂ) * I)‖ = 1 := by
  rw [show -((x : ℝ) : ℂ) * I = ((-x : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_gU_mul_cexp (u α t : ℝ) :
    ‖(gU u t : ℂ) * cexp (-((α * t : ℝ) : ℂ) * I)‖ = gU u t := by
  rw [norm_mul, norm_cexp_neg_real_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gU_nonneg u t)]

lemma summable_gU (u : ℝ) (hu : 0 < u) : Summable (fun t : ℤ => gU u t) := by
  unfold gU
  exact (summable_gauss_int (Kg_pos hu) (t0 u)).mul_left _

lemma summable_gU_mul_cexp (u α : ℝ) (hu : 0 < u) :
    Summable (fun t : ℤ => (gU u t : ℂ) * cexp (-((α * t : ℝ) : ℂ) * I)) := by
  refine Summable.of_norm ?_
  simp only [norm_gU_mul_cexp]
  exact summable_gU u hu

/-- **The Gaussian sum.** For `u ≥ 1` and `|α| ≤ 1`,
`|∑_{t ∈ ℤ} g_u(t) e^{-iαt} - (ℓ/c) e^{-α²ℓ²u/c³ - iαt₀}| ≤ (ℓ/c) · 4e^{-u/4}`. -/
theorem gauss_sum_main (u α : ℝ) (hu : 1 ≤ u) (hα : |α| ≤ 1) :
    ‖∑' t : ℤ, (gU u t : ℂ) * cexp (-((α * t : ℝ) : ℂ) * I) -
      ((ell / c : ℝ) : ℂ) * cexp (-((α ^ 2 * ell ^ 2 * u / c ^ 3 : ℝ) : ℂ) -
        ((α * t0 u : ℝ) : ℂ) * I)‖ ≤ ell / c * (4 * Real.exp (-(u / 4))) := by
  have hu0 : 0 < u := by linarith
  have hK := Kg_pos hu0
  have hc := c_pos'; have hl := ell_pos; have hpi := Real.pi_pos
  rw [gauss_poisson u α hu0]
  set κ := π ^ 2 / Kg u with hκ
  have hκ0 : 0 < κ := by positivity
  set t0' := -α / (2 * π) with ht0'
  set G : ℤ → ℂ := fun n => ((ell / c : ℝ) : ℂ) * cexp (-((κ * (n + α / (2 * π)) ^ 2 : ℝ) : ℂ) -
      ((((2 * π * n + α) * t0 u) : ℝ) : ℂ) * I) with hG
  have hshift : ∀ n : ℤ, ((n : ℝ) + α / (2 * π)) = (n : ℝ) - t0' := by
    intro n; rw [ht0']; ring
  have hnormG : ∀ n : ℤ, ‖G n‖ = ell / c * Real.exp (-(κ * ((n : ℝ) - t0') ^ 2)) := by
    intro n
    simp only [hG]
    have hre : ∀ a b : ℝ, (-((a : ℝ) : ℂ) - ((b : ℝ) : ℂ) * I).re = -a := by intro a b; simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      Complex.norm_exp, hre, hshift]
  have hGs : Summable G := by
    refine Summable.of_norm ?_
    simp only [hnormG]
    exact (summable_gauss_int hκ0 t0').mul_left _
  rw [hGs.tsum_eq_add_tsum_ite 0]
  have hG0 : G 0 = ((ell / c : ℝ) : ℂ) * cexp (-((α ^ 2 * ell ^ 2 * u / c ^ 3 : ℝ) : ℂ) -
      ((α * t0 u : ℝ) : ℂ) * I) := by
    simp only [hG]
    congr 3
    · congr 1; rw [hκ]; unfold Kg; push_cast; field_simp; ring
    · push_cast; ring
  rw [hG0, add_sub_cancel_left]
  -- the dual tail
  have hite_s : Summable (fun n : ℤ => ‖if n = 0 then (0 : ℂ) else G n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => by split_ifs <;> simp [norm_nonneg]) hGs.norm
  refine (norm_tsum_le_tsum_norm hite_s).trans ?_
  have hα' : |t0'| ≤ 1 / 4 := by
    rw [ht0', abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
  have hpt : ∀ n : ℤ, ‖if n = 0 then (0 : ℂ) else G n‖ ≤
      ell / c * (if 1 / 2 ≤ |(n : ℝ) - t0'| then
        Real.exp (-(κ / 2) * |(n : ℝ) - t0'|) else 0) := by
    intro n
    have hrhs : 0 ≤ ell / c * (if 1 / 2 ≤ |(n : ℝ) - t0'| then
        Real.exp (-(κ / 2) * |(n : ℝ) - t0'|) else 0) := by
      apply mul_nonneg (by positivity); split_ifs <;> positivity
    by_cases h0 : n = 0
    · rw [show (if n = 0 then (0 : ℂ) else G n) = 0 from by simp [h0], norm_zero]; exact hrhs
    · simp only [h0, ↓reduceIte]
      have h1 : 1 / 2 ≤ |(n : ℝ) - t0'| := by
        have hn : (1 : ℝ) ≤ |(n : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h0
        have := abs_sub_abs_le_abs_sub (n : ℝ) t0'
        linarith
      simp only [h1, ↓reduceIte]
      rw [hnormG]
      gcongr
      have h2 : |(n : ℝ) - t0'| / 2 ≤ |(n : ℝ) - t0'| ^ 2 := by
        nlinarith [abs_nonneg ((n : ℝ) - t0')]
      rw [← sq_abs]; nlinarith
  obtain ⟨hs2, hle2⟩ := int_geom_tail (κ / 2) t0' (1 / 2) (by positivity)
  calc ∑' n : ℤ, ‖if n = 0 then (0 : ℂ) else G n‖
      ≤ ∑' n : ℤ, ell / c * (if 1 / 2 ≤ |(n : ℝ) - t0'| then
          Real.exp (-(κ / 2) * |(n : ℝ) - t0'|) else 0) :=
        Summable.tsum_le_tsum hpt hite_s (hs2.mul_left _)
    _ = ell / c * ∑' n : ℤ, (if 1 / 2 ≤ |(n : ℝ) - t0'| then
          Real.exp (-(κ / 2) * |(n : ℝ) - t0'|) else 0) := tsum_mul_left
    _ ≤ ell / c * (2 * Real.exp (-(κ / 2 * (1 / 2) / 2)) * (1 + 2 / (κ / 2))) := by gcongr
    _ ≤ ell / c * (4 * Real.exp (-(u / 4))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        -- `κ = π²/K = 4π²ℓ²u/c³ ≥ 4u` and `4/κ ≤ 1`
        have hκu : 4 * u ≤ κ := by
          rw [hκ]; unfold Kg
          rw [div_div_eq_mul_div, le_div_iff₀ (by positivity)]
          have h1 : c ^ 3 ≤ 1 := pow_le_one₀ hc.le (by linarith [c_lt_third])
          have h0 : 3 * 0.69 ≤ π * ell :=
            mul_le_mul Real.pi_gt_three.le ell_gt.le (by norm_num) hpi.le
          have h2 : (1 : ℝ) ≤ π ^ 2 * ell ^ 2 := by nlinarith
          nlinarith
        have h1 : Real.exp (-(κ / 2 * (1 / 2) / 2)) ≤ Real.exp (-(u / 4)) :=
          Real.exp_le_exp.mpr (by linarith)
        have h2 : 2 / (κ / 2) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        have h3 := Real.exp_pos (-(κ / 2 * (1 / 2) / 2))
        calc 2 * Real.exp (-(κ / 2 * (1 / 2) / 2)) * (1 + 2 / (κ / 2))
            ≤ 2 * Real.exp (-(κ / 2 * (1 / 2) / 2)) * 2 := by gcongr; linarith
          _ ≤ 2 * Real.exp (-(u / 4)) * 2 := by gcongr
          _ = 4 * Real.exp (-(u / 4)) := by ring

end CollatzCLT
