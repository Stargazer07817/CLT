import LeanClt.Renewal.Assembly

/-!
# Theorem 4.1 (small-frequency twisted renewal)

* `twisted_renewal`: the estimate (4.3, `eq:renewal`), with `δ` depending only on `ϰ`;
  `twisted_renewal_main`: the same for fixed `d, ϰ`, with `δ = 1/(10(ϰ+1))`.
* The "Moreover" clauses. `renewalR_summable`: the series (4.2, `eq:R`) converges absolutely,
  as a double series over `ℕ × ℕ`. `renewalR_freq_zero`, `renewalR_zero_real`: `R_0 = R^{ρ,η}_0`
  does not depend on the reward, and is real and `≥ 0`. `norm_renewalR_le`:
  `|R^{ρ,η}_s(u)| ≤ R_0(u)`. `renewalR_zero_bounded`: `sup_u R_0(u) < ∞`, derived from
  `renewalR_bounded` (uniform in `ρ, η, s, u`). These clauses use no Diophantine input.

With `ε = 1/(ϰ+1)`, `γ = ε/10` and window half-width `X = u^{1/2+γ}`, every term of
`renewal_error_bound` is `O(u^{-γ})`; for `u` in a bounded range the crude bound applies. Hence
`δ = ε/10`. The paper's proof uses the window `√u log u` and gets `δ = ε/4`; the theorem asserts
only some `δ > 0` depending on `ϰ`, so the smaller exponent changes no statement.
-/

open Real Finset Complex Filter Topology

noncomputable section

namespace CollatzCLT

/-! ## Two asymptotic facts -/

lemma eventually_sqrt_mul_exp_le {γ k : ℝ} (hγ : 0 < γ) (hk : 0 < k) :
    ∀ᶠ u : ℝ in atTop, u ^ ((1 : ℝ) / 2) * Real.exp (-(k * u ^ (2 * γ))) ≤ u ^ (-γ) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((1 / 2 + γ) / (2 * γ)) k hk).comp
    (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 2 * γ))
  filter_upwards [h.eventually (gt_mem_nhds zero_lt_one), eventually_gt_atTop (0 : ℝ)]
    with u hu hu0
  simp only [Function.comp_apply] at hu
  rw [← Real.rpow_mul hu0.le, show 2 * γ * ((1 / 2 + γ) / (2 * γ)) = 1 / 2 + γ by
    field_simp] at hu
  have e : u ^ ((1 : ℝ) / 2) = u ^ (1 / 2 + γ) * u ^ (-γ) := by
    rw [← Real.rpow_add hu0]; ring_nf
  rw [e, mul_right_comm, neg_mul_eq_neg_mul]
  have hpos : 0 < u ^ (-γ) := Real.rpow_pos_of_pos hu0 _
  calc u ^ (1 / 2 + γ) * Real.exp (-k * u ^ (2 * γ)) * u ^ (-γ) ≤ 1 * u ^ (-γ) := by
        gcongr
    _ = u ^ (-γ) := one_mul _

lemma eventually_exp_le {γ : ℝ} :
    ∀ᶠ u : ℝ in atTop, Real.exp (-(u / 4)) ≤ u ^ (-γ) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero γ (1 / 4) (by norm_num)
  filter_upwards [h.eventually (gt_mem_nhds zero_lt_one), eventually_gt_atTop (0 : ℝ)]
    with u hu hu0
  have hpos : 0 < u ^ γ := Real.rpow_pos_of_pos hu0 _
  rw [Real.rpow_neg hu0.le, le_inv_comm₀ (Real.exp_pos _) hpos, ← Real.exp_neg]
  have : u ^ γ * Real.exp (-(1 / 4) * u) < 1 := hu
  have e : Real.exp (-(1 / 4) * u) = (Real.exp (- -(u / 4)))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [e, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)] at this
  exact this.le

/-! ## Power bookkeeping for `X = u^{1/2+γ}` -/

lemma sq_rpow_half_add {u γ : ℝ} (hu : 0 < u) :
    u ^ (1 / 2 + γ) * u ^ (1 / 2 + γ) = u * u ^ (2 * γ) := by
  rw [← Real.rpow_add hu, show 1 / 2 + γ + (1 / 2 + γ) = 1 + 2 * γ by ring, Real.rpow_add hu,
    Real.rpow_one]

lemma div_rpow_half_add_le {u γ : ℝ} (hu : 1 ≤ u) (hγ : 0 ≤ γ) :
    u / u ^ (1 / 2 + γ) ≤ u ^ ((1 : ℝ) / 2) := by
  have hu0 : 0 < u := by linarith
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hu0 _), ← Real.rpow_add hu0]
  calc u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
    _ ≤ u ^ ((1 : ℝ) / 2 + (1 / 2 + γ)) :=
        Real.rpow_le_rpow_of_exponent_le hu (by linarith)

lemma inv_sqrt_eq_rpow {u : ℝ} (hu : 0 < u) : (Real.sqrt u)⁻¹ = u ^ (-(1 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hu.le]; ring_nf

lemma one_le_rpow_of {u x : ℝ} (hu : 1 ≤ u) (hx : 0 ≤ x) : 1 ≤ u ^ x :=
  Real.one_le_rpow hu hx

/-- The exponential terms: `e^{-k u^{2γ}} (1 + L u/X) ≤ (1 + L) u^{-γ}` eventually. -/
lemma ev_exp_term {γ k L : ℝ} (hγ : 0 < γ) (hk : 0 < k) (hL : 0 ≤ L) :
    ∀ᶠ u : ℝ in atTop,
      Real.exp (-(k * u ^ (2 * γ))) * (1 + L * (u / u ^ (1 / 2 + γ))) ≤ (1 + L) * u ^ (-γ) := by
  filter_upwards [eventually_sqrt_mul_exp_le hγ hk, eventually_ge_atTop (1 : ℝ)] with u h1 hu1
  have hs : 1 ≤ u ^ ((1 : ℝ) / 2) := one_le_rpow_of hu1 (by norm_num)
  have h2 : 1 + L * (u / u ^ (1 / 2 + γ)) ≤ (1 + L) * u ^ ((1 : ℝ) / 2) := by
    have := div_rpow_half_add_le hu1 hγ.le
    nlinarith
  have he := Real.exp_pos (-(k * u ^ (2 * γ)))
  calc Real.exp (-(k * u ^ (2 * γ))) * (1 + L * (u / u ^ (1 / 2 + γ)))
      ≤ Real.exp (-(k * u ^ (2 * γ))) * ((1 + L) * u ^ ((1 : ℝ) / 2)) := by gcongr
    _ = (1 + L) * (u ^ ((1 : ℝ) / 2) * Real.exp (-(k * u ^ (2 * γ)))) := by ring
    _ ≤ (1 + L) * u ^ (-γ) := by gcongr

/-! ## The total error bound -/

/-- The total error with `#W ≤ 2X + 1`, `|s(ρθ+η)| ≤ A₁/√u` and `|ρs| ≤ A₂/√u`. -/
def Ebound (ϰ Crot A1 A2 u X : ℝ) : ℝ :=
  8 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u)) +
  50 * (Real.sqrt u)⁻¹ +
  (2 * X + 1) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) +
  Crot * (2 * X + 1) ^ (1 - 1 / (ϰ + 1)) *
    ((Real.sqrt u)⁻¹ * (1 + (2 * X + 1) * ((2 * X + 3) / u + A1 * (Real.sqrt u)⁻¹))) +
  2 * (ell / c * (4 * Real.exp (-(u / 4))) +
    (Real.sqrt u)⁻¹ * (2 * Real.exp (-(Kg u * X * X / 2)) * (1 + 2 / (Kg u * X)))) +
  (2 * ell + 1) / ell ^ 2 * (A2 * (Real.sqrt u)⁻¹) * (ell / c)

lemma Ebound_eventually {ϰ Crot A1 A2 : ℝ} (hϰ : 1 ≤ ϰ) (hC : 0 ≤ Crot) (hA1 : 0 ≤ A1)
    (hA2 : 0 ≤ A2) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      Ebound ϰ Crot A1 A2 u (u ^ (1 / 2 + 1 / (ϰ + 1) / 10)) ≤ C * u ^ (-(1 / (ϰ + 1) / 10)) := by
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (ϰ + 1) := ⟨_, rfl⟩
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = ε / 10 := ⟨_, rfl⟩
  have hrw : 1 / (ϰ + 1) / 10 = γ := by rw [hγdef, hε]
  simp only [hrw]
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε2 : ε ≤ 1 / 2 := by rw [hε, div_le_iff₀ (by linarith)]; linarith
  have hγ : 0 < γ := by rw [hγdef]; positivity
  have hγ2 : γ ≤ 1 / 20 := by rw [hγdef]; linarith
  have hc := c_pos'; have hl := ell_pos; have hκ := κW_pos
  set L1 := 2 / κW
  set k2 := c ^ 3 / (8 * ell ^ 2)
  set L2 := 8 * ell ^ 2 / c ^ 3
  refine ⟨8 * (1 + L1) + 50 + 198 + 3 * Crot * (16 + 3 * A1) + 8 * (ell / c) + 4 * (1 + L2) +
    (2 * ell + 1) / ell ^ 2 * A2 * (ell / c), ?_⟩
  filter_upwards [ev_exp_term hγ (k := κW / 2) (L := L1) (by positivity) (by positivity),
    ev_exp_term hγ (k := k2) (L := L2) (by positivity) (by positivity),
    eventually_exp_le (γ := γ), eventually_ge_atTop (1 : ℝ)] with u e1 e2 e3 hu1
  have hu : 0 < u := by linarith
  set X := u ^ (1 / 2 + γ) with hXdef
  set q := u ^ (-γ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hu _
  have hXX : X * X = u * u ^ (2 * γ) := sq_rpow_half_add hu
  have hX1 : 1 ≤ X := one_le_rpow_of hu1 (by linarith)
  have hX0 : 0 < X := by linarith
  have hp : (Real.sqrt u)⁻¹ = u ^ (-(1 : ℝ) / 2) := inv_sqrt_eq_rpow hu
  have hpq : (Real.sqrt u)⁻¹ ≤ q := by
    rw [hp, hq]; exact Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
  have hp0 : 0 ≤ (Real.sqrt u)⁻¹ := by positivity
  have hp1 : (Real.sqrt u)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (Real.sqrt_pos.mpr hu), Real.one_le_sqrt]; exact hu1
  have hY : u ^ (2 * γ) = X * X / u := by rw [hXX]; field_simp
  -- `p ≤ X/u`
  have hpX : (Real.sqrt u)⁻¹ ≤ X / u := by
    rw [hp, le_div_iff₀ hu]
    calc u ^ (-(1 : ℝ) / 2) * u = u ^ (-(1 : ℝ) / 2) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = u ^ ((1 : ℝ) / 2) := by rw [← Real.rpow_add hu]; norm_num
      _ ≤ X := Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
  -- (1) window tail
  have b1 : 8 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u)) ≤ 8 * (1 + L1) * q := by
    have ea : κW * X / u * X / 2 = κW / 2 * u ^ (2 * γ) := by rw [hY]; field_simp
    have eb : 2 / (κW * X / u) = L1 * (u / X) := by simp only [L1]; field_simp
    rw [ea, eb, mul_assoc, mul_assoc]
    linarith [e1]
  -- (2) extra endpoint
  have b2 : 50 * (Real.sqrt u)⁻¹ ≤ 50 * q := by linarith
  -- (3) Gaussian replacement
  have b3 : (2 * X + 1) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) ≤ 198 * q := by
    have h2g : (u ^ (2 * γ)) ^ 2 = u ^ (4 * γ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; push_cast; ring_nf
    have h4 : X ^ 4 = u ^ 2 * u ^ (4 * γ) := by
      have : X ^ 4 = (X * X) ^ 2 := by ring
      rw [this, hXX, mul_pow, h2g]
    have hexp : u ^ (4 * γ) * u ^ (-(1 : ℝ) / 2) ≤ q := by
      rw [← Real.rpow_add hu, hq]; exact Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
    calc (2 * X + 1) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹)
        ≤ (3 * X) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) := by gcongr; linarith
      _ = 198 * (X ^ 4 / u ^ 2) * (Real.sqrt u)⁻¹ := by ring
      _ = 198 * (u ^ (4 * γ) * u ^ (-(1 : ℝ) / 2)) := by
          rw [h4, hp]; field_simp
      _ ≤ 198 * q := by gcongr
  -- (4) Abel summation against the rotation
  have b4 : Crot * (2 * X + 1) ^ (1 - 1 / (ϰ + 1)) *
      ((Real.sqrt u)⁻¹ * (1 + (2 * X + 1) * ((2 * X + 3) / u + A1 * (Real.sqrt u)⁻¹))) ≤
      3 * Crot * (16 + 3 * A1) * q := by
    rw [← hε]
    have h1e : 0 ≤ 1 - ε := by linarith
    have hpow1 : (2 * X + 1) ^ (1 - ε) ≤ 3 * u ^ ((1 / 2 + γ) * (1 - ε)) := by
      calc (2 * X + 1) ^ (1 - ε) ≤ (3 * X) ^ (1 - ε) :=
            Real.rpow_le_rpow (by positivity) (by linarith) h1e
        _ = 3 ^ (1 - ε) * X ^ (1 - ε) := Real.mul_rpow (by norm_num) hX0.le
        _ ≤ 3 * X ^ (1 - ε) := by
            gcongr
            calc (3 : ℝ) ^ (1 - ε) ≤ 3 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 3 := Real.rpow_one 3
        _ = 3 * u ^ ((1 / 2 + γ) * (1 - ε)) := by rw [hXdef, ← Real.rpow_mul hu.le]
    have hbr : 1 + (2 * X + 1) * ((2 * X + 3) / u + A1 * (Real.sqrt u)⁻¹) ≤
        (16 + 3 * A1) * u ^ (2 * γ) := by
      rw [hY]
      have hXu : 1 ≤ X * X / u := by
        rw [← hY]; exact one_le_rpow_of hu1 (by linarith)
      have h5 : (2 * X + 3) / u ≤ 5 * (X / u) := by
        rw [mul_div_assoc']; gcongr; linarith
      have h6 : A1 * (Real.sqrt u)⁻¹ ≤ A1 * (X / u) := by gcongr
      have h7 : 2 * X + 1 ≤ 3 * X := by linarith
      have h8 : (2 * X + 3) / u + A1 * (Real.sqrt u)⁻¹ ≤ (5 + A1) * (X / u) := by nlinarith
      have h9 : 0 ≤ (2 * X + 3) / u + A1 * (Real.sqrt u)⁻¹ := by positivity
      calc 1 + (2 * X + 1) * ((2 * X + 3) / u + A1 * (Real.sqrt u)⁻¹)
          ≤ 1 + (3 * X) * ((5 + A1) * (X / u)) := by gcongr
        _ = 1 + (15 + 3 * A1) * (X * X / u) := by ring
        _ ≤ (16 + 3 * A1) * (X * X / u) := by nlinarith
    have hex : (1 / 2 + γ) * (1 - ε) + (-(1 : ℝ) / 2 + 2 * γ) ≤ -γ := by
      have e : (1 / 2 + γ) * (1 - ε) + (-(1 : ℝ) / 2 + 2 * γ) + γ = 4 * γ - ε / 2 - γ * ε := by
        ring
      have := mul_pos hγ hε0
      linarith
    have hfin : u ^ ((1 / 2 + γ) * (1 - ε)) * (u ^ (-(1 : ℝ) / 2) * u ^ (2 * γ)) ≤ q := by
      rw [← Real.rpow_add hu, ← Real.rpow_add hu, hq]
      exact Real.rpow_le_rpow_of_exponent_le hu1 hex
    calc Crot * (2 * X + 1) ^ (1 - ε) *
          ((Real.sqrt u)⁻¹ * (1 + (2 * X + 1) * ((2 * X + 3) / u + A1 * (Real.sqrt u)⁻¹)))
        ≤ Crot * (3 * u ^ ((1 / 2 + γ) * (1 - ε))) *
          ((Real.sqrt u)⁻¹ * ((16 + 3 * A1) * u ^ (2 * γ))) := by gcongr
      _ = 3 * Crot * (16 + 3 * A1) *
          (u ^ ((1 / 2 + γ) * (1 - ε)) * (u ^ (-(1 : ℝ) / 2) * u ^ (2 * γ))) := by rw [hp]; ring
      _ ≤ 3 * Crot * (16 + 3 * A1) * q := by gcongr
  -- (5) Poisson dual terms and the Gaussian tail
  have b5 : 2 * (ell / c * (4 * Real.exp (-(u / 4))) +
      (Real.sqrt u)⁻¹ * (2 * Real.exp (-(Kg u * X * X / 2)) * (1 + 2 / (Kg u * X)))) ≤
      (8 * (ell / c) + 4 * (1 + L2)) * q := by
    have ea : Kg u * X * X / 2 = k2 * u ^ (2 * γ) := by
      rw [mul_assoc, hXX]; simp only [k2]; unfold Kg; field_simp; ring
    have eb : 2 / (Kg u * X) = L2 * (u / X) := by
      simp only [L2]; unfold Kg; field_simp; ring
    rw [ea, eb]
    have h1 : Real.exp (-(k2 * u ^ (2 * γ))) * (1 + L2 * (u / X)) ≤ (1 + L2) * q := e2
    have h2 : (Real.sqrt u)⁻¹ * (2 * Real.exp (-(k2 * u ^ (2 * γ))) * (1 + L2 * (u / X))) ≤
        2 * ((1 + L2) * q) := by
      have h0 : 0 ≤ 2 * Real.exp (-(k2 * u ^ (2 * γ))) * (1 + L2 * (u / X)) := by positivity
      calc (Real.sqrt u)⁻¹ * (2 * Real.exp (-(k2 * u ^ (2 * γ))) * (1 + L2 * (u / X)))
          ≤ 1 * (2 * Real.exp (-(k2 * u ^ (2 * γ))) * (1 + L2 * (u / X))) := by gcongr
        _ ≤ 2 * ((1 + L2) * q) := by linarith
    have h3 : ell / c * (4 * Real.exp (-(u / 4))) ≤ ell / c * (4 * q) := by gcongr
    calc 2 * (ell / c * (4 * Real.exp (-(u / 4))) +
          (Real.sqrt u)⁻¹ * (2 * Real.exp (-(k2 * u ^ (2 * γ))) * (1 + L2 * (u / X))))
        ≤ 2 * (ell / c * (4 * q) + 2 * ((1 + L2) * q)) := by
          apply mul_le_mul_of_nonneg_left (add_le_add h3 h2) (by norm_num)
      _ = (8 * (ell / c) + 4 * (1 + L2)) * q := by ring
  -- (6) `m_v - 1/ℓ`
  have b6 : (2 * ell + 1) / ell ^ 2 * (A2 * (Real.sqrt u)⁻¹) * (ell / c) ≤
      (2 * ell + 1) / ell ^ 2 * A2 * (ell / c) * q := by
    have : (2 * ell + 1) / ell ^ 2 * (A2 * (Real.sqrt u)⁻¹) * (ell / c) =
        (2 * ell + 1) / ell ^ 2 * A2 * (ell / c) * (Real.sqrt u)⁻¹ := by ring
    rw [this]; gcongr
  unfold Ebound
  calc _ ≤ 8 * (1 + L1) * q + 50 * q + 198 * q + 3 * Crot * (16 + 3 * A1) * q +
        (8 * (ell / c) + 4 * (1 + L2)) * q + (2 * ell + 1) / ell ^ 2 * A2 * (ell / c) * q :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5) b6
    _ = _ := by ring

/-! ## Theorem 4.1 -/

lemma norm_mainTerm_le (ρ η s : ℝ) {u : ℝ} (hu : 0 ≤ u) : ‖mainTerm ρ η s u‖ ≤ 1 / c := by
  have hc := c_pos'
  unfold mainTerm
  rw [norm_mul, Complex.norm_exp]
  have hre : (-(I * (((2 * ρ + η) / c * s * u : ℝ) : ℂ)) -
      ((((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u) : ℝ) : ℂ)).re =
      -((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u) := by
    rw [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re]
    ring
  rw [hre]
  have h1 : Real.exp (-((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]; positivity
  have h2 : ‖(1 / c : ℂ)‖ = 1 / c := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [h2]
  calc 1 / c * Real.exp (-((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u)) ≤ 1 / c * 1 := by
        gcongr
    _ = 1 / c := mul_one _

/-- **Theorem 4.1 for fixed Rhin constants, with the explicit exponent.** Given
`IrrMeasure d ϰ`, for all real `ρ, η, M` there is `C` with
`‖R^{ρ,η}_s(u) - mainTerm ρ η s u‖ ≤ C u^{-1/(10(ϰ+1))}` for all `u ≥ 2` and `|s| √u ≤ M`.
`twisted_renewal` restates it with `δ` chosen before `d`. Proof: `renewal_error_bound` at
`X = u^{1/2+γ}`, `γ = 1/(10(ϰ+1))`, for large `u` (`Ebound_eventually`), and the crude bound
`Bcrude` on the bounded range `2 ≤ u ≤ U₁`. -/
theorem twisted_renewal_main {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∀ ρ η M : ℝ, ∃ C : ℝ, ∀ u s : ℝ, 2 ≤ u → |s| * √u ≤ M →
      ‖renewalR ρ η s u - mainTerm ρ η s u‖ ≤ C * u ^ (-(1 / (ϰ + 1) / 10)) := by
  have hϰ : 1 ≤ ϰ := hθ.2.1
  obtain ⟨Crot, hC0, hbound⟩ := renewal_error_bound hθ
  intro ρ η M
  set M' := |M|
  set A1 := M' * |ρ * θ + η|
  set A2 := M' * |ρ|
  have hA1 : 0 ≤ A1 := by positivity
  have hA2 : 0 ≤ A2 := by positivity
  set γ := 1 / (ϰ + 1) / 10 with hγ
  have hγ0 : 0 < γ := by positivity
  have hγ2 : γ ≤ 1 / 20 := by
    rw [hγ, div_le_iff₀ (by norm_num), div_le_iff₀ (by linarith)]; linarith
  obtain ⟨C1, hev⟩ := Ebound_eventually hϰ hC0 hA1 hA2
  have hreg : ∀ᶠ u : ℝ in Filter.atTop,
      Regime u (u ^ (1 / 2 + γ)) ∧ 2 * ell / c ≤ u ^ (1 / 2 + γ) ∧
        A1 * (Real.sqrt u)⁻¹ ≤ 1 ∧ A2 * (Real.sqrt u)⁻¹ ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop ((8 : ℝ) ^ 5),
      Filter.eventually_ge_atTop ((2 * ell / c) ^ 2), Filter.eventually_ge_atTop (A1 ^ 2),
      Filter.eventually_ge_atTop (A2 ^ 2)] with u h1 h2 h3 h4
    have hu1 : 1 ≤ u := le_trans (by norm_num) h1
    have hu0 : 0 < u := by linarith
    have hsq : Real.sqrt u ≤ u ^ (1 / 2 + γ) := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
    have hsp := Real.sqrt_pos.mpr hu0
    have hle : ∀ A : ℝ, 0 ≤ A → A ^ 2 ≤ u → A * (Real.sqrt u)⁻¹ ≤ 1 := by
      intro A hA hAu
      rw [← div_eq_mul_inv, div_le_one hsp]
      exact Real.le_sqrt_of_sq_le hAu
    refine ⟨⟨h1, hsq, Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)⟩, ?_,
      hle A1 hA1 h3, hle A2 hA2 h4⟩
    refine le_trans ?_ hsq
    exact Real.le_sqrt_of_sq_le h2
  obtain ⟨U0, hU0⟩ := Filter.eventually_atTop.mp (hev.and hreg)
  set U1 := max U0 2 with hU1
  have hU12 : 2 ≤ U1 := le_max_right _ _
  have hU1p : 0 < U1 := by linarith
  set B := (Bcrude U1 + 1 / c) * U1 ^ γ
  refine ⟨max C1 B, fun u s hu hs => ?_⟩
  have hu0 : 0 < u := by linarith
  have hq0 : 0 < u ^ (-γ) := Real.rpow_pos_of_pos hu0 _
  rcases le_or_gt U1 u with hU | hU
  · -- the asymptotic regime
    obtain ⟨hE, hR, hX1, hA1u, hA2u⟩ := hU0 u (le_trans (le_max_left _ _) hU)
    set X := u ^ (1 / 2 + γ)
    have hsp := Real.sqrt_pos.mpr hu0
    have hs' : |s| ≤ M' * (Real.sqrt u)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hsp]; exact hs.trans (le_abs_self M)
    have hv : |ρ * s| ≤ A2 * (Real.sqrt u)⁻¹ := by
      rw [abs_mul]
      calc |ρ| * |s| ≤ |ρ| * (M' * (Real.sqrt u)⁻¹) := by gcongr
        _ = A2 * (Real.sqrt u)⁻¹ := by ring
    have hα : |s * (ρ * θ + η)| ≤ A1 * (Real.sqrt u)⁻¹ := by
      rw [abs_mul]
      calc |s| * |ρ * θ + η| ≤ (M' * (Real.sqrt u)⁻¹) * |ρ * θ + η| := by gcongr
        _ = A1 * (Real.sqrt u)⁻¹ := by ring
    have hb := hbound ρ η s u X hR hX1 (hv.trans hA2u) (hα.trans hA1u)
    have hXT : X ≤ t0 u := by linarith [hR.X_le_u, hR.t0_ge]
    have hcard := card_Wset_le hR.X_pos.le hXT
    have hexp : 0 ≤ 1 - 1 / (ϰ + 1) := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have hmono : ‖renewalR ρ η s u - mainTerm ρ η s u‖ ≤ Ebound ϰ Crot A1 A2 u X := by
      refine hb.trans ?_
      unfold Ebound
      have hp0 : 0 ≤ (Real.sqrt u)⁻¹ := by positivity
      have hX0 := hR.X_pos
      have hc := c_pos'; have hl := ell_pos
      gcongr
    calc _ ≤ Ebound ϰ Crot A1 A2 u X := hmono
      _ ≤ C1 * u ^ (-γ) := hE
      _ ≤ max C1 B * u ^ (-γ) := by gcongr; exact le_max_left _ _
  · -- a bounded range: the crude bound
    have h1 : ‖renewalR ρ η s u - mainTerm ρ η s u‖ ≤ Bcrude U1 + 1 / c := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_mainTerm_le ρ η s hu0.le))
      exact (norm_renewalR_le_crude ρ η s u).trans (Bcrude_mono hU.le)
    have h2 : 1 ≤ U1 ^ γ * u ^ (-γ) := by
      have : U1 ^ (-γ) ≤ u ^ (-γ) := Real.rpow_le_rpow_of_nonpos hu0 hU.le (by linarith)
      have e : U1 ^ γ * U1 ^ (-γ) = 1 := by
        rw [← Real.rpow_add hU1p]; simp
      have := Real.rpow_pos_of_pos hU1p γ
      nlinarith
    have hB0 : 0 ≤ Bcrude U1 + 1 / c := (norm_nonneg _).trans h1
    calc _ ≤ Bcrude U1 + 1 / c := h1
      _ ≤ (Bcrude U1 + 1 / c) * (U1 ^ γ * u ^ (-γ)) := le_mul_of_one_le_right hB0 h2
      _ = B * u ^ (-γ) := by ring
      _ ≤ max C1 B * u ^ (-γ) := by gcongr; exact le_max_right _ _

/-! ## `sup_u R₀(u) < ∞` without Diophantine input -/

lemma norm_renewalR_le_tsum_pwin (ρ η s u : ℝ) : ‖renewalR ρ η s u‖ ≤ 2 * ∑' t, pwin u t := by
  rw [renewalR_eq]
  refine (norm_tsum_le_tsum_norm (summable_norm_rinner ρ η s u)).trans ?_
  calc _ ≤ ∑' t, 2 * pwin u t := Summable.tsum_le_tsum (norm_rinner_le ρ η s u)
        (summable_norm_rinner ρ η s u) ((summable_pwin u).mul_left 2)
    _ = 2 * ∑' t, pwin u t := tsum_mul_left

/-- In the window, `P(h_t ≤ S_t ≤ h_t + 1) ≤ 2(g_u(t) + 33X³/(u²√u))`. -/
lemma pwin_le_gU {u X : ℝ} (hR : Regime u X) {t : ℕ} (ht : |(t : ℝ) - t0 u| ≤ X) :
    pwin u t ≤ 2 * (gU u t + 33 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) := by
  have hE0 : 0 ≤ gU u t + 33 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹ := by
    have := gU_nonneg u t; have := hR.X_pos; have := hR.u_pos; positivity
  rw [pwin_eq_sum]
  have hcard : (Icc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1)).card ≤ 2 := by
    rw [Nat.card_Icc]; have := Nat.floor_le_ceil (hT u t); omega
  calc _ ≤ ∑ A ∈ Icc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1),
        (gU u t + 33 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) := by
        refine Finset.sum_le_sum fun A _ => ?_
        split_ifs with hw
        · have hA : |(A : ℝ) - hT u t| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith [hw.1, hw.2]
          have h1 := lawS_sub_gU_le hR ht hA
          have h2 := le_abs_self (lawS t A - gU u t)
          linarith
        · exact hE0
    _ = ((Icc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1)).card : ℝ) *
        (gU u t + 33 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (gU u t + 33 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) := by
        gcongr; exact_mod_cast hcard

/-- `∑_{t ∈ ℤ} g_u(t) ≤ 5ℓ/c` for `u ≥ 1`, from the Poisson evaluation at `α = 0`. -/
lemma tsum_gU_le {u : ℝ} (hu : 1 ≤ u) : ∑' z : ℤ, gU u z ≤ 5 * (ell / c) := by
  have hc := c_pos'; have hl := ell_pos
  have h := gauss_sum_main u 0 hu (by simp)
  have e1 : ∑' t : ℤ, (gU u t : ℂ) * cexp (-((0 * t : ℝ) : ℂ) * I) =
      ((∑' z : ℤ, gU u z : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; congr 1; funext t; simp
  have e2 : ((ell / c : ℝ) : ℂ) * cexp (-(((0 : ℝ) ^ 2 * ell ^ 2 * u / c ^ 3 : ℝ) : ℂ) -
      ((0 * t0 u : ℝ) : ℂ) * I) = ((ell / c : ℝ) : ℂ) := by simp
  rw [e1, e2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  have h2 := le_abs_self (∑' z : ℤ, gU u z - ell / c)
  have he : Real.exp (-(u / 4)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have h3 : ell / c * (4 * Real.exp (-(u / 4))) ≤ ell / c * 4 := by gcongr; linarith
  linarith

lemma sum_Wset_gU_le {u : ℝ} (hu : 0 < u) (X : ℝ) :
    ∑ t ∈ Wset u X, gU u t ≤ ∑' z : ℤ, gU u z := by
  have e : ∑ t ∈ Wset u X, gU u t =
      ∑ z ∈ (Wset u X).map (Nat.castEmbedding : ℕ ↪ ℤ), gU u (z : ℝ) := by
    rw [Finset.sum_map]; simp
  rw [e]
  exact Summable.sum_le_tsum (f := fun z : ℤ => gU u z) _ (fun i _ => gU_nonneg u i)
    (summable_gU u hu)

lemma tsum_eq_sum_add_tsum_ite_real {ι : Type*} [DecidableEq ι] {f : ι → ℝ} (hf : Summable f)
    (S : Finset ι) : ∑' i, f i = ∑ i ∈ S, f i + ∑' i, (if i ∈ S then 0 else f i) := by
  rw [← hf.sum_add_tsum_compl (s := S), tsum_subtype ((↑S : Set ι)ᶜ) f]
  congr 1
  refine tsum_congr fun i => ?_
  by_cases hi : i ∈ S <;> simp [hi, Set.indicator]

/-- The window-replacement error, summed over the window, is bounded. -/
lemma card_err_le {u γ : ℝ} (hu1 : 1 ≤ u) (hγ0 : 0 ≤ γ) (hγ2 : γ ≤ 1 / 20) :
    (2 * u ^ (1 / 2 + γ) + 1) *
      (66 * ((u ^ (1 / 2 + γ)) ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) ≤ 198 := by
  have hu : 0 < u := by linarith
  set X := u ^ (1 / 2 + γ) with hXdef
  have hXX : X * X = u * u ^ (2 * γ) := sq_rpow_half_add hu
  have hX1 : 1 ≤ X := one_le_rpow_of hu1 (by linarith)
  have hp : (Real.sqrt u)⁻¹ = u ^ (-(1 : ℝ) / 2) := inv_sqrt_eq_rpow hu
  have h2g : (u ^ (2 * γ)) ^ 2 = u ^ (4 * γ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; push_cast; ring_nf
  have h4 : X ^ 4 = u ^ 2 * u ^ (4 * γ) := by
    have : X ^ 4 = (X * X) ^ 2 := by ring
    rw [this, hXX, mul_pow, h2g]
  have hexp : u ^ (4 * γ) * u ^ (-(1 : ℝ) / 2) ≤ 1 := by
    rw [← Real.rpow_add hu]
    exact Real.rpow_le_one_of_one_le_of_nonpos hu1 (by linarith)
  calc (2 * X + 1) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹)
      ≤ (3 * X) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) := by gcongr; linarith
    _ = 198 * (X ^ 4 / u ^ 2) * (Real.sqrt u)⁻¹ := by ring
    _ = 198 * (u ^ (4 * γ) * u ^ (-(1 : ℝ) / 2)) := by rw [h4, hp]; field_simp
    _ ≤ 198 * 1 := by gcongr
    _ = 198 := mul_one _

/-- **`R^{ρ,η}_s(u)` is bounded uniformly in `u` and in the reward and frequency, with no
Diophantine input.** On a bounded range of `u`, the crude bound `Bcrude` (the paper's argument for
`u ≤ 2`). For large `u`, a variant of the paper's parenthetical alternative: the tails by
Lemma 4.2 [`lem:tails`] (`window_tail`), the window by
Lemma 4.3 [`lem:gauss`] in its absolute-error form (`lawS_sub_gU_le`, in place of the paper's
uniform middle-range bound), and the Poisson evaluation `∑ g_u ≤ 5ℓ/c`. Together with
`norm_renewalR_le` it is equivalent to `renewalR_zero_bounded`. -/
theorem renewalR_bounded : ∃ B : ℝ, ∀ ρ η s u : ℝ, ‖renewalR ρ η s u‖ ≤ B := by
  set γ : ℝ := 1 / 20 with hγ
  have hγ0 : 0 < γ := by norm_num [hγ]
  have hc := c_pos'; have hl := ell_pos; have hκ := κW_pos
  set L1 := 2 / κW
  have hreg : ∀ᶠ u : ℝ in Filter.atTop,
      Regime u (u ^ (1 / 2 + γ)) ∧ 2 * ell / c ≤ u ^ (1 / 2 + γ) ∧
        Real.exp (-(κW / 2 * u ^ (2 * γ))) * (1 + L1 * (u / u ^ (1 / 2 + γ))) ≤
          (1 + L1) * u ^ (-γ) := by
    filter_upwards [Filter.eventually_ge_atTop ((8 : ℝ) ^ 5),
      Filter.eventually_ge_atTop ((2 * ell / c) ^ 2),
      ev_exp_term hγ0 (k := κW / 2) (L := L1) (by positivity) (by positivity)] with u h1 h2 h3
    have hu1 : 1 ≤ u := le_trans (by norm_num) h1
    have hsq : Real.sqrt u ≤ u ^ (1 / 2 + γ) := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
    refine ⟨⟨h1, hsq, Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num [hγ])⟩, ?_, h3⟩
    exact le_trans (Real.le_sqrt_of_sq_le h2) hsq
  obtain ⟨U0, hU0⟩ := Filter.eventually_atTop.mp hreg
  set U1 := max U0 1
  refine ⟨max (Bcrude U1) (2 * (2 * (5 * (ell / c)) + 198 + 4 * (1 + L1))),
    fun ρ η s u => ?_⟩
  rcases le_or_gt u U1 with hu | hu
  · exact (norm_renewalR_le_crude ρ η s u).trans ((Bcrude_mono hu).trans (le_max_left _ _))
  refine le_trans ?_ (le_max_right _ _)
  obtain ⟨hR, hX1, hexp⟩ := hU0 u (le_trans (le_max_left _ _) hu.le)
  have hu1 : 1 ≤ u := le_trans (le_max_right _ _) hu.le
  have hu0 : 0 < u := by linarith
  set X := u ^ (1 / 2 + γ) with hXdef
  have hXT : X ≤ t0 u := by linarith [hR.X_le_u, hR.t0_ge]
  have hX0 := hR.X_pos
  refine (norm_renewalR_le_tsum_pwin ρ η s u).trans ?_
  gcongr
  classical
  rw [tsum_eq_sum_add_tsum_ite_real (summable_pwin u) (Wset u X)]
  -- the window
  have hwin : ∑ t ∈ Wset u X, pwin u t ≤ 2 * (5 * (ell / c)) + 198 := by
    calc ∑ t ∈ Wset u X, pwin u t
        ≤ ∑ t ∈ Wset u X, 2 * (gU u t + 33 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) :=
          Finset.sum_le_sum fun t ht => pwin_le_gU hR ((mem_Wset hX0.le hXT t).mp ht)
      _ = 2 * ∑ t ∈ Wset u X, gU u t +
          ((Wset u X).card : ℝ) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) := by
          rw [Finset.sum_congr rfl (fun (t : ℕ) _ => mul_add (2 : ℝ) (gU u (t : ℝ))
            (33 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹)), Finset.sum_add_distrib,
            ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ 2 * (5 * (ell / c)) + (2 * X + 1) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) := by
          gcongr
          · exact (sum_Wset_gU_le hu0 X).trans (tsum_gU_le hu1)
          · exact card_Wset_le hX0.le hXT
      _ ≤ 2 * (5 * (ell / c)) + 198 := by
          gcongr; exact card_err_le hu1 hγ0.le (by norm_num [hγ])
  -- the tail
  obtain ⟨hs, hle⟩ := window_tail hu0 hX1 hR.X_le_u
  have hpt : ∀ t : ℕ, (if t ∈ Wset u X then 0 else pwin u t) ≤
      (if X ≤ |(t : ℝ) - u / c| then pwin u t else 0) := by
    intro t
    by_cases ht : t ∈ Wset u X
    · simp only [ht, ↓reduceIte]; split_ifs
      · exact pwin_nonneg u t
      · exact le_rfl
    · have hfar : X ≤ |(t : ℝ) - u / c| := by
        rw [mem_Wset hX0.le hXT] at ht; push Not at ht; exact ht.le
      simp only [ht, hfar, ↓reduceIte, le_refl]
  have hnn : ∀ t : ℕ, 0 ≤ (if t ∈ Wset u X then 0 else pwin u t) := by
    intro t; split_ifs
    · exact le_rfl
    · exact pwin_nonneg u t
  have htail : ∑' t : ℕ, (if t ∈ Wset u X then 0 else pwin u t) ≤ 4 * (1 + L1) := by
    refine (Summable.tsum_le_tsum hpt (Summable.of_nonneg_of_le hnn hpt hs) hs).trans
      (hle.trans ?_)
    have hXX : X * X = u * u ^ (2 * γ) := sq_rpow_half_add hu0
    have ea : κW * X / u * X / 2 = κW / 2 * u ^ (2 * γ) := by
      rw [show κW * X / u * X / 2 = κW * (X * X) / (2 * u) by ring, hXX]; field_simp
    have eb : 2 / (κW * X / u) = L1 * (u / X) := by simp only [L1]; field_simp
    rw [ea, eb, mul_assoc]
    have hq : u ^ (-γ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1 (by linarith)
    have : (1 + L1) * u ^ (-γ) ≤ 1 + L1 := by
      have : 0 ≤ 1 + L1 := by positivity
      nlinarith
    linarith
  linarith

/-! ## The statements of Theorem 4.1 -/

/-- **Theorem 4.1 (small-frequency twisted renewal)** [`thm:renewal`],
the estimate (4.3, `eq:renewal`). For every `ϰ` there is `δ > 0`, depending only on `ϰ`
(explicitly `δ = 1/(10(ϰ+1))` when `ϰ ≥ 1`; for `ϰ < 1` the hypothesis below never holds), such
that if Rhin's measure (2.8, `eq:rhin`) holds
with exponent `ϰ` and some constant `d`, then for all fixed real `ρ, η` and every `M`, uniformly
for `u ≥ 2` and `|s| √u ≤ M`,
`R^{ρ,η}_s(u) = (1/c) exp(-i (2ρ+η)/c · s u - (ρβ+ηℓ)²/c³ · s² u) + O(u^{-δ})`,
the constant depending on `d, ϰ, ρ, η, M` (the paper's `O_{M,ρ,η}`, which leaves the fixed
constants `d, ϰ` of the Rhin import implicit). There is no condition on `(ρ, η)`, so rewards
with `ρβ + ηℓ = 0` are included. The paper's proof gives `δ = 1/(4(ϰ+1))`; only `δ > 0` is
asserted. -/
theorem twisted_renewal (ϰ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℝ, IrrMeasure d ϰ → ∀ ρ η M : ℝ, ∃ C : ℝ, ∀ u s : ℝ, 2 ≤ u →
      |s| * √u ≤ M →
      ‖renewalR ρ η s u - (1 / c : ℂ) *
        cexp (-(I * (((2 * ρ + η) / c * s * u : ℝ) : ℂ)) -
          ((((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u) : ℝ) : ℂ))‖ ≤ C * u ^ (-δ) := by
  have hpos : 0 < max ϰ 1 + 1 := by linarith [le_max_right ϰ 1]
  refine ⟨1 / (max ϰ 1 + 1) / 10, by positivity, fun d hθ => ?_⟩
  rw [max_eq_left hθ.2.1]
  exact twisted_renewal_main hθ

/-- **Theorem 4.1, absolute convergence.**
The series (4.2, `eq:R`), read as a double series over `(t, A)`, converges absolutely: the norms
of its terms are summable over `ℕ × ℕ`. This gives both `∑_t E|·| < ∞` and `∑_t |E[·]| < ∞`. -/
theorem renewalR_summable (ρ η s u : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      ‖if 0 ≤ Zval p.1 p.2 - u ∧ Zval p.1 p.2 - u ≤ ell then
        (lawS p.1 p.2 : ℂ) * (Real.exp (Zval p.1 p.2 - u) : ℂ) *
          cexp (-(((s * (ρ * p.2 + η * p.1)) : ℝ) : ℂ) * I)
      else 0‖) := by
  refine (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨fun t => ?_, ?_⟩
  · exact summable_of_ne_finset_zero (s := Icc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1))
      (fun A hA => by
        have := rterm_eq_zero (ρ := ρ) (η := η) (s := s) hA
        unfold rterm at this; rw [this, norm_zero])
  · exact renewalR_summable' ρ η s u

/-- **`R₀` does not depend on the reward**: `R^{ρ,η}_0(u) = R^{0,0}_0(u)`. -/
theorem renewalR_freq_zero (ρ η u : ℝ) : renewalR ρ η 0 u = renewalR 0 0 0 u := by
  unfold renewalR; simp

/-- `R₀(u)` is real and nonnegative, so `(renewalR 0 0 0 u).re`, used for `R_0(u)` below, is
`R_0(u)` itself. -/
theorem renewalR_zero_real (u : ℝ) :
    (renewalR 0 0 0 u).im = 0 ∧ 0 ≤ (renewalR 0 0 0 u).re := by
  have h := norm_renewalR_le' 0 0 0 u
  have h1 := Complex.abs_re_le_norm (renewalR 0 0 0 u)
  have h2 : (renewalR 0 0 0 u).re ^ 2 + (renewalR 0 0 0 u).im ^ 2 =
      ‖renewalR 0 0 0 u‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h3 : ‖renewalR 0 0 0 u‖ = (renewalR 0 0 0 u).re := le_antisymm h (le_trans (le_abs_self _) h1)
  refine ⟨?_, h3 ▸ norm_nonneg _⟩
  rw [h3] at h2
  nlinarith [sq_nonneg (renewalR 0 0 0 u).im]

/-- **Theorem 4.1, domination** `|R^{ρ,η}_s(u)| ≤ R_0(u)`. -/
theorem norm_renewalR_le (ρ η s u : ℝ) : ‖renewalR ρ η s u‖ ≤ (renewalR 0 0 0 u).re :=
  norm_renewalR_le' ρ η s u

/-- **Theorem 4.1, global boundedness of `R_0`**, with no Diophantine input:
`sup_{u ∈ ℝ} R_0(u) < ∞`. -/
theorem renewalR_zero_bounded : ∃ B : ℝ, ∀ u : ℝ, (renewalR 0 0 0 u).re ≤ B := by
  obtain ⟨B, hB⟩ := renewalR_bounded
  exact ⟨B, fun u => (Complex.re_le_norm _).trans (hB 0 0 0 u)⟩

end CollatzCLT
