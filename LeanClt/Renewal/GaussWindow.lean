import LeanClt.Renewal.Tails
import LeanClt.Renewal.LocalLimit

/-!
# §4.2: the Gaussian window (Lemma 4.3)

Put `t₀ = u/c`, `K = c³/(4ℓ²u)` and `g_u(t) = (4π t₀)^{-1/2} exp(-K (t - t₀)²)`. In the regime
`8⁵ ≤ u`, `√u ≤ X ≤ u^{3/5}` (`Regime u X`), for `|t - t₀| ≤ X` and `|A - h_t| ≤ 1`:

* `lawS_le_window`: `P(S_t = A) ≤ 25/√u`;
* `lawS_sub_gU_le`: `|P(S_t = A) - g_u(t)| ≤ 33 X³/(u² √u)`.

With `X = u^{1/2+γ}` the second bound, summed over the `≤ 3X` window points, is
`O(u^{4γ - 1/2})`, the paper's `O(u^{-1/2} log³ u)` with a power in place of the logarithm.
-/

open Real Finset

noncomputable section

namespace CollatzCLT

/-- `t₀ = u/c`. -/
def t0 (u : ℝ) : ℝ := u / c

/-- `K = c³/(4ℓ²u)`. -/
def Kg (u : ℝ) : ℝ := c ^ 3 / (4 * ell ^ 2 * u)

/-- `g_u(t) = (4π t₀)^{-1/2} exp(-K (t - t₀)²)`. -/
def gU (u t : ℝ) : ℝ := (Real.sqrt (4 * π * t0 u))⁻¹ * Real.exp (-(Kg u * (t - t0 u) ^ 2))

/-- The regime of the Gaussian window. -/
structure Regime (u X : ℝ) : Prop where
  u_ge : (8 : ℝ) ^ 5 ≤ u
  sqrt_le : Real.sqrt u ≤ X
  le_pow : X ≤ u ^ ((3 : ℝ) / 5)

namespace Regime

variable {u X : ℝ} (hR : Regime u X)
include hR

lemma u_pos : 0 < u := lt_of_lt_of_le (by norm_num) hR.u_ge

lemma one_le_u : 1 ≤ u := le_trans (by norm_num) hR.u_ge

lemma sqrt_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hR.u_pos

lemma X_pos : 0 < X := lt_of_lt_of_le hR.sqrt_pos hR.sqrt_le

lemma two_le_X : 2 ≤ X := by
  refine le_trans ?_ hR.sqrt_le
  rw [Real.le_sqrt (by norm_num) hR.u_pos.le]
  linarith [hR.u_ge]

lemma le_X_sq : u ≤ X ^ 2 := by
  have := pow_le_pow_left₀ (Real.sqrt_nonneg u) hR.sqrt_le 2
  rwa [Real.sq_sqrt hR.u_pos.le] at this

lemma X_le_u : X ≤ u := by
  refine hR.le_pow.trans ?_
  calc u ^ ((3 : ℝ) / 5) ≤ u ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hR.one_le_u (by norm_num)
    _ = u := Real.rpow_one u

lemma X_cube_le : X ^ 3 ≤ u ^ 2 := by
  have h1 : X ^ 3 ≤ (u ^ ((3 : ℝ) / 5)) ^ 3 := pow_le_pow_left₀ hR.X_pos.le hR.le_pow 3
  have h2 : (u ^ ((3 : ℝ) / 5)) ^ 3 = u ^ ((9 : ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.u_pos.le]; norm_num
  have h3 : u ^ ((9 : ℝ) / 5) ≤ u ^ ((2 : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hR.one_le_u (by norm_num)
  rw [Real.rpow_natCast] at h3
  linarith

lemma inv_sqrt_le_one : (Real.sqrt u)⁻¹ ≤ 1 := by
  rw [inv_le_one₀ hR.sqrt_pos, Real.one_le_sqrt]; exact hR.one_le_u

lemma inv_sqrt_le : (Real.sqrt u)⁻¹ ≤ X / u := by
  rw [inv_le_iff_one_le_mul₀ hR.sqrt_pos]
  have h := mul_le_mul_of_nonneg_right hR.sqrt_le (Real.sqrt_nonneg u)
  rw [Real.mul_self_sqrt hR.u_pos.le] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hR.u_pos, one_mul]; exact h

lemma X_div_le : X / u ≤ X ^ 3 / u ^ 2 := by
  rw [div_le_div_iff₀ hR.u_pos (by have := hR.u_pos; positivity)]
  have := hR.le_X_sq
  have := hR.X_pos
  have e : X ^ 3 * u = X * (X ^ 2 * u) := by ring
  have e2 : X * u ^ 2 = X * (u * u) := by ring
  have hu := hR.u_pos
  rw [e, e2]
  gcongr

lemma t0_ge : 3 * u ≤ t0 u := by
  unfold t0
  rw [le_div_iff₀ c_pos']
  nlinarith [c_lt_third, hR.u_pos]

/-- In the window, `t ≥ u`. -/
lemma t_ge {t : ℝ} (ht : |t - t0 u| ≤ X) : u ≤ t := by
  have := hR.t0_ge; have := hR.X_le_u; have := hR.u_pos
  have := neg_abs_le (t - t0 u)
  linarith

end Regime

lemma abs_hT_sub (u : ℝ) (t : ℕ) : |hT u t - 2 * t| = c / ell * |(t : ℝ) - t0 u| := by
  have hc := c_pos'; have hl := ell_pos
  rw [hT_sub_two_mul, abs_div, abs_of_pos hl, t0,
    show u - c * t = -(c * ((t : ℝ) - u / c)) by field_simp; ring, abs_neg, abs_mul,
    abs_of_pos hc]
  ring

lemma c_div_ell_le : c / ell ≤ 1 / 2 := by
  rw [div_le_iff₀ ell_pos]; linarith [c_lt_third, ell_gt]

/-- In the window, `|A - 2t| ≤ X` and `|h_t - 2t| ≤ X/2`. -/
lemma Regime.d_le {u X : ℝ} (hR : Regime u X) {t : ℕ} (ht : |(t : ℝ) - t0 u| ≤ X) {A : ℕ}
    (hA : |(A : ℝ) - hT u t| ≤ 1) : |(A : ℝ) - 2 * t| ≤ X ∧ |hT u t - 2 * t| ≤ X / 2 := by
  have h1 : |hT u t - 2 * t| ≤ X / 2 := by
    rw [abs_hT_sub]
    calc c / ell * |(t : ℝ) - t0 u| ≤ 1 / 2 * X :=
          mul_le_mul c_div_ell_le ht (abs_nonneg _) (by norm_num)
      _ = X / 2 := by ring
  refine ⟨?_, h1⟩
  calc |(A : ℝ) - 2 * t| = |((A : ℝ) - hT u t) + (hT u t - 2 * t)| := by ring_nf
    _ ≤ |(A : ℝ) - hT u t| + |hT u t - 2 * t| := abs_add_le _ _
    _ ≤ 1 + X / 2 := add_le_add hA h1
    _ ≤ X := by linarith [hR.two_le_X]

lemma inv_rpow_half_eq {x : ℝ} (hx : 0 ≤ x) : x⁻¹ ^ ((1 : ℝ) / 2) = (Real.sqrt x)⁻¹ := by
  rw [Real.sqrt_eq_rpow, Real.inv_rpow hx]

lemma rpow_neg_half_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 : ℝ) / 2) = (Real.sqrt x)⁻¹ := by
  rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hx, Real.sqrt_eq_rpow]

lemma inv_sqrt_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : (Real.sqrt b)⁻¹ ≤ (Real.sqrt a)⁻¹ :=
  inv_anti₀ (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt hab)

/-- `|e^{-a} - e^{-b}| ≤ |a - b|` for `a, b ≥ 0`. -/
lemma abs_exp_neg_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]; exact this hb ha (by linarith)
  have h1 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 1 - (b - a) ≤ Real.exp (-(b - a)) := by
    have := Real.add_one_le_exp (-(b - a)); linarith
  have h4 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h5 : 0 < Real.exp (-a) := Real.exp_pos _
  rw [h2]
  nlinarith

/-- `|1/√a - 1/√b| ≤ |a - b|/(2u√u)` for `a, b ≥ u > 0`. -/
lemma abs_inv_sqrt_sub_le {u a b : ℝ} (hu : 0 < u) (ha : u ≤ a) (hb : u ≤ b) :
    |(Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹| ≤ |a - b| / (2 * u * Real.sqrt u) := by
  have hsu := Real.sqrt_pos.mpr hu
  have hsa : Real.sqrt u ≤ Real.sqrt a := Real.sqrt_le_sqrt ha
  have hsb : Real.sqrt u ≤ Real.sqrt b := Real.sqrt_le_sqrt hb
  have hsa0 : 0 < Real.sqrt a := lt_of_lt_of_le hsu hsa
  have hsb0 : 0 < Real.sqrt b := lt_of_lt_of_le hsu hsb
  have e : (Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹ =
      (b - a) / (Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b)) := by
    have hA := Real.sq_sqrt (le_trans hu.le ha)
    have hB := Real.sq_sqrt (le_trans hu.le hb)
    field_simp
    nlinarith [hA, hB]
  have hD0 : 0 < Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b) :=
    mul_pos (mul_pos hsa0 hsb0) (add_pos hsa0 hsb0)
  rw [e, abs_div, abs_of_pos hD0, abs_sub_comm b a]
  refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
  have huu : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  calc 2 * u * Real.sqrt u = (Real.sqrt u * Real.sqrt u) * (Real.sqrt u + Real.sqrt u) := by
        rw [huu]; ring
    _ ≤ Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b) := by gcongr

/-- **Local bound in the window:** `|P(S_t = A) - G(t, A)| ≤ 12 u^{-1/2}(u^{-1/2} + X³/u²)` and
`G(t, A) ≤ u^{-1/2}`, where `G` is the local-limit Gaussian. -/
lemma lawS_window_local {u X : ℝ} (hR : Regime u X) {t : ℕ} (ht : |(t : ℝ) - t0 u| ≤ X) {A : ℕ}
    (hA : |(A : ℝ) - hT u t| ≤ 1) :
    |lawS t A - gaussApprox t A| ≤
      12 * (Real.sqrt u)⁻¹ * ((Real.sqrt u)⁻¹ + X ^ 3 / u ^ 2) ∧
      gaussApprox t A ≤ (Real.sqrt u)⁻¹ := by
  have htu := hR.t_ge ht
  have hu := hR.u_pos
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hu htu
  obtain ⟨hd, -⟩ := hR.d_le ht hA
  have hga : gaussApprox t A ≤ (Real.sqrt u)⁻¹ := by
    unfold gaussApprox
    rw [inv_rpow_half_eq (by positivity)]
    have h1 : Real.exp (-((A : ℝ) - 2 * t) ^ 2 / (4 * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have := sq_nonneg ((A : ℝ) - 2 * t); linarith
    have h2 : (Real.sqrt (4 * π * t))⁻¹ ≤ (Real.sqrt u)⁻¹ :=
      inv_sqrt_anti hu (by nlinarith [Real.pi_gt_three])
    calc (Real.sqrt (4 * π * t))⁻¹ * Real.exp (-((A : ℝ) - 2 * t) ^ 2 / (4 * t))
        ≤ (Real.sqrt (4 * π * t))⁻¹ * 1 := by gcongr
      _ ≤ (Real.sqrt u)⁻¹ := by rw [mul_one]; exact h2
  refine ⟨?_, hga⟩
  have hpow : X ≤ (t : ℝ) ^ ((3 : ℝ) / 5) :=
    hR.le_pow.trans (Real.rpow_le_rpow hu.le htu (by norm_num))
  have hll := lawS_local_limit_explicit t (le_trans hR.u_ge htu) A (hd.trans hpow)
  refine hll.trans ?_
  rw [rpow_neg_half_eq ht0.le]
  have hga0 : 0 ≤ gaussApprox t A := by unfold gaussApprox; positivity
  have h1 : (Real.sqrt t)⁻¹ ≤ (Real.sqrt u)⁻¹ := inv_sqrt_anti hu htu
  have h2 : |(A : ℝ) - 2 * t| ^ 3 / (t : ℝ) ^ 2 ≤ X ^ 3 / u ^ 2 := by
    apply div_le_div₀ (pow_pos hR.X_pos 3).le (pow_le_pow_left₀ (abs_nonneg _) hd 3) (by positivity)
    exact pow_le_pow_left₀ hu.le htu 2
  calc 12 * gaussApprox t A * ((Real.sqrt t)⁻¹ + |(A : ℝ) - 2 * t| ^ 3 / (t : ℝ) ^ 2)
      ≤ 12 * (Real.sqrt u)⁻¹ * ((Real.sqrt u)⁻¹ + X ^ 3 / u ^ 2) := by gcongr

/-- **`P(S_t = A) ≤ 25/√u` in the window.** -/
lemma lawS_le_window {u X : ℝ} (hR : Regime u X) {t : ℕ} (ht : |(t : ℝ) - t0 u| ≤ X) {A : ℕ}
    (hA : |(A : ℝ) - hT u t| ≤ 1) : lawS t A ≤ 25 * (Real.sqrt u)⁻¹ := by
  obtain ⟨h1, h2⟩ := lawS_window_local hR ht hA
  have h3 := hR.inv_sqrt_le_one
  have h4 : X ^ 3 / u ^ 2 ≤ 1 := by
    rw [div_le_one (by have := hR.u_pos; positivity)]; exact hR.X_cube_le
  have h5 : 0 ≤ (Real.sqrt u)⁻¹ := by have := hR.sqrt_pos; positivity
  have h6 : lawS t A ≤ gaussApprox t A + |lawS t A - gaussApprox t A| := by
    have := le_abs_self (lawS t A - gaussApprox t A); linarith
  have h7 : 12 * (Real.sqrt u)⁻¹ * ((Real.sqrt u)⁻¹ + X ^ 3 / u ^ 2) ≤
      12 * (Real.sqrt u)⁻¹ * 2 := by gcongr; linarith
  linarith

/-- The Gaussian `g_u` is bounded by `u^{-1/2}`. -/
lemma gU_le {u : ℝ} (hu : 0 < u) (t : ℝ) : gU u t ≤ (Real.sqrt u)⁻¹ := by
  have hc := c_pos'
  unfold gU
  have h1 : Real.exp (-(Kg u * (t - t0 u) ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]; unfold Kg; have := ell_pos; positivity
  have ht0 : u ≤ 4 * π * t0 u := by
    unfold t0
    have : u ≤ u / c := by rw [le_div_iff₀ hc]; nlinarith [c_lt_third]
    nlinarith [Real.pi_gt_three]
  calc (Real.sqrt (4 * π * t0 u))⁻¹ * Real.exp (-(Kg u * (t - t0 u) ^ 2))
      ≤ (Real.sqrt (4 * π * t0 u))⁻¹ * 1 := by gcongr
    _ ≤ (Real.sqrt u)⁻¹ := by rw [mul_one]; exact inv_sqrt_anti hu ht0

lemma gU_nonneg (u t : ℝ) : 0 ≤ gU u t := by unfold gU; positivity

/-- `K (t - t₀)² = (h_t - 2t)²/(4t₀)`. -/
lemma Kg_mul_sq (u : ℝ) (hu : 0 < u) (t : ℕ) :
    Kg u * ((t : ℝ) - t0 u) ^ 2 = (hT u t - 2 * t) ^ 2 / (4 * t0 u) := by
  have hc := c_pos'; have hl := ell_pos
  rw [hT_sub_two_mul]; unfold Kg t0
  field_simp
  ring

/-- **Lemma 4.3 [`lem:gauss`], absolute-error form.** `|P(S_t = A) - g_u(t)| ≤ 33 X³/(u² √u)` for
`|t - t₀| ≤ X` and `|A - h_t| ≤ 1`; the paper states the relative error
`P(S_t = A_t) = g_u(t)(1 + O(u^{-1/2} log³ u))`, which is stronger where `g_u(t)` is small. -/
lemma lawS_sub_gU_le {u X : ℝ} (hR : Regime u X) {t : ℕ} (ht : |(t : ℝ) - t0 u| ≤ X) {A : ℕ}
    (hA : |(A : ℝ) - hT u t| ≤ 1) :
    |lawS t A - gU u t| ≤ 33 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹ := by
  have hu := hR.u_pos
  have hc := c_pos'
  have hX := hR.X_pos
  have htu := hR.t_ge ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hu htu
  have ht0u : u ≤ t0 u := le_trans (by linarith) hR.t0_ge
  have ht00 : 0 < t0 u := lt_of_lt_of_le hu ht0u
  obtain ⟨h1, -⟩ := lawS_window_local hR ht hA
  obtain ⟨hd, hd0⟩ := hR.d_le ht hA
  set d := (A : ℝ) - 2 * t with hdd
  set d0 := hT u t - 2 * t with hd0d
  set s := (Real.sqrt u)⁻¹ with hs
  have hs0 : 0 < s := by rw [hs]; have := hR.sqrt_pos; positivity
  -- write both Gaussians as `(√(4π))⁻¹ (√τ)⁻¹ e^{-…}`
  have hsplit : ∀ τ : ℝ, 0 ≤ τ → (Real.sqrt (4 * π * τ))⁻¹ =
      (Real.sqrt (4 * π))⁻¹ * (Real.sqrt τ)⁻¹ := by
    intro τ hτ
    rw [Real.sqrt_mul (by positivity), mul_inv]
  have hpi : (Real.sqrt (4 * π))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity), Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  have hpi0 : 0 ≤ (Real.sqrt (4 * π))⁻¹ := by positivity
  have hga : gaussApprox t A = (Real.sqrt (4 * π))⁻¹ * (Real.sqrt t)⁻¹ *
      Real.exp (-(d ^ 2 / (4 * t))) := by
    unfold gaussApprox
    rw [inv_rpow_half_eq (by positivity), hsplit _ ht0.le, neg_div]
  have hgu : gU u t = (Real.sqrt (4 * π))⁻¹ * (Real.sqrt (t0 u))⁻¹ *
      Real.exp (-(d0 ^ 2 / (4 * t0 u))) := by
    unfold gU
    rw [hsplit _ ht00.le, Kg_mul_sq u hu t]
  -- the exponents
  have hE : |d ^ 2 / (4 * t) - d0 ^ 2 / (4 * t0 u)| ≤ X / u + X ^ 3 / u ^ 2 := by
    have hdd0 : |d - d0| ≤ 1 := by
      rw [hdd, hd0d, show (A : ℝ) - 2 * t - (hT u t - 2 * t) = (A : ℝ) - hT u t by ring]; exact hA
    have e : d ^ 2 / (4 * t) - d0 ^ 2 / (4 * t0 u) =
        (d - d0) * (d + d0) / (4 * t) + d0 ^ 2 * (t0 u - t) / (4 * t * t0 u) := by
      field_simp; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * t)]
      have : |d + d0| ≤ 2 * X := by
        have := abs_add_le d d0; linarith
      rw [div_le_div_iff₀ (by positivity) hu]
      calc |d - d0| * |d + d0| * u ≤ 1 * (2 * X) * u := by gcongr
        _ ≤ X * (4 * t) := by nlinarith
    · rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * t * t0 u), abs_pow,
        abs_sub_comm (t0 u) (t : ℝ)]
      have ht' : |(t : ℝ) - t0 u| ≤ X := ht
      have hd02 : |d0| ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc |d0| ^ 2 * |(t : ℝ) - t0 u| * u ^ 2 ≤ X ^ 2 * X * (t * t0 u) := by
            have : u ^ 2 ≤ t * t0 u := by nlinarith
            gcongr
        _ ≤ X ^ 3 * (4 * t * t0 u) := by
            have : 0 ≤ t * t0 u := by positivity
            nlinarith [pow_pos hX 3]
  have hexp : |Real.exp (-(d ^ 2 / (4 * t))) - Real.exp (-(d0 ^ 2 / (4 * t0 u)))| ≤
      X / u + X ^ 3 / u ^ 2 :=
    (abs_exp_neg_sub_le (by positivity) (by positivity)).trans hE
  -- the prefactors
  have hpre : |(Real.sqrt t)⁻¹ - (Real.sqrt (t0 u))⁻¹| ≤ X / u * s := by
    refine (abs_inv_sqrt_sub_le hu htu ht0u).trans ?_
    rw [hs, div_le_iff₀ (by have := hR.sqrt_pos; positivity)]
    have : X / u * (Real.sqrt u)⁻¹ * (2 * u * Real.sqrt u) = 2 * X := by
      have := hR.sqrt_pos; field_simp
    rw [this]; linarith
  have hst0 : (Real.sqrt (t0 u))⁻¹ ≤ s := inv_sqrt_anti hu ht0u
  have hE1 : Real.exp (-(d ^ 2 / (4 * t))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]; positivity
  have hgdiff : |gaussApprox t A - gU u t| ≤ s * (2 * (X / u) + X ^ 3 / u ^ 2) := by
    rw [hga, hgu]
    set P := (Real.sqrt (4 * π))⁻¹
    set a1 := (Real.sqrt t)⁻¹
    set a2 := (Real.sqrt (t0 u))⁻¹
    set e1 := Real.exp (-(d ^ 2 / (4 * t)))
    set e2 := Real.exp (-(d0 ^ 2 / (4 * t0 u)))
    have ha2 : 0 ≤ a2 := by positivity
    have he1 : 0 ≤ e1 := by positivity
    have e : P * a1 * e1 - P * a2 * e2 = P * ((a1 - a2) * e1 + a2 * (e1 - e2)) := by ring
    rw [e, abs_mul, abs_of_nonneg hpi0]
    calc P * |(a1 - a2) * e1 + a2 * (e1 - e2)| ≤ 1 * (|a1 - a2| * e1 + a2 * |e1 - e2|) := by
          gcongr
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg he1, abs_of_nonneg ha2]
      _ ≤ 1 * (X / u * s * 1 + s * (X / u + X ^ 3 / u ^ 2)) := by gcongr
      _ = s * (2 * (X / u) + X ^ 3 / u ^ 2) := by ring
  -- combine
  have hcomb : |lawS t A - gU u t| ≤
      12 * s * (s + X ^ 3 / u ^ 2) + s * (2 * (X / u) + X ^ 3 / u ^ 2) := by
    calc |lawS t A - gU u t| = |(lawS t A - gaussApprox t A) + (gaussApprox t A - gU u t)| := by
          ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 hgdiff)
  have hsX : s ≤ X ^ 3 / u ^ 2 := hR.inv_sqrt_le.trans hR.X_div_le
  have hXu : X / u ≤ X ^ 3 / u ^ 2 := hR.X_div_le
  refine hcomb.trans ?_
  nlinarith

end CollatzCLT
