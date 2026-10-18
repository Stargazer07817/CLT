import LeanClt.Architecture.FixedBase
import LeanClt.Architecture.Dyadic

/-!
# Odd dyadic sampling: definitions and elementary estimates

* `oddClosed Y`: the odd integers in `[Y, 2Y]`, the support of the paper's `N_Y`.
* `ph A q s c n = 1_A(n) e^{i s (q(n) + c)}`: the clock phase.
* `oddCF A q κ Y s = E[1_A(N_Y) e^{i s (q(N_Y) + κ log Y)}]`: the function `Φ_Y(s)` of §6.2,
  whose renormalisation is the subject of Lemma 6.1.

Elementary facts used in Lemma 6.5 [`lem:sampling`]: boundedness and continuity of the phases, the
Lipschitz bound `|e^{ia} - e^{ib}| ≤ |a - b|`, the count of odd integers in `[W, 2W]`,
and limits of `⌊X/m⌋`.
-/

open Real Filter Topology Finset Complex

namespace CollatzCLT

open Classical in
/-- The odd integers in `[Y, 2Y]`. -/
noncomputable def oddClosed (Y : ℝ) : Finset ℕ := (Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).filter Odd

/-- The clock phase `1_A(n) e^{i s (q(n) + c)}`. -/
noncomputable def ph (A : Set ℕ) (q : ℕ → ℝ) (s c : ℝ) (n : ℕ) : ℂ :=
  A.indicator (fun n => cexp (((s * (q n + c) : ℝ) : ℂ) * I)) n

/-- `Φ_Y(s) = E[1_A(N_Y) e^{i s (q(N_Y) + κ log Y)}]`, `N_Y` uniform on the odd integers
of `[Y, 2Y]` (§6.2). -/
noncomputable def oddCF (A : Set ℕ) (q : ℕ → ℝ) (κ Y s : ℝ) : ℂ :=
  ((oddClosed Y).card : ℂ)⁻¹ * ∑ u ∈ oddClosed Y, ph A q s (κ * Real.log Y) u

lemma norm_ph_le (A : Set ℕ) (q : ℕ → ℝ) (s c : ℝ) (n : ℕ) : ‖ph A q s c n‖ ≤ 1 := by
  unfold ph
  by_cases h : n ∈ A
  · rw [Set.indicator_of_mem h, norm_exp_ofReal_mul_I]
  · rw [Set.indicator_of_notMem h, norm_zero]; exact zero_le_one

lemma continuous_ph (A : Set ℕ) (q : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    Continuous (fun s => ph A q s c n) := by
  unfold ph
  by_cases h : n ∈ A
  · simp only [Set.indicator_of_mem h]; fun_prop
  · simp only [Set.indicator_of_notMem h]; exact continuous_const

lemma continuousAt_oddCF (A : Set ℕ) (q : ℕ → ℝ) (κ Y : ℝ) :
    ContinuousAt (oddCF A q κ Y) 0 := by
  unfold oddCF
  exact (continuous_const.mul (continuous_finsetSum _ fun u _ => continuous_ph A q _ u)).continuousAt

/-- `|e^{ia} - e^{ib}| ≤ |a - b|`. -/
lemma norm_cexp_sub_cexp_le (a b : ℝ) :
    ‖cexp ((a : ℂ) * I) - cexp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have h : cexp ((a : ℂ) * I) - cexp ((b : ℂ) * I) =
      cexp ((b : ℂ) * I) * (cexp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [h, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  exact (norm_exp_I_mul_ofReal_sub_one_le).trans (by simp [Real.norm_eq_abs])

/-- Changing the centring constant moves the phase by at most `|s| |c - c'|`. -/
lemma norm_ph_sub_le (A : Set ℕ) (q : ℕ → ℝ) (s c c' : ℝ) (n : ℕ) :
    ‖ph A q s c n - ph A q s c' n‖ ≤ |s| * |c - c'| := by
  unfold ph
  by_cases h : n ∈ A
  · simp only [Set.indicator_of_mem h]
    refine (norm_cexp_sub_cexp_le _ _).trans (le_of_eq ?_)
    rw [← abs_mul]; congr 1; ring
  · simp only [Set.indicator_of_notMem h, sub_zero, norm_zero]; positivity

/-! ## Counting odd integers -/

/-- For a natural `W`, `oddClosed W` is the set of odd `u` with `W ≤ u ≤ 2W`. -/
lemma oddClosed_natCast (W : ℕ) : oddClosed (W : ℝ) = (Icc W (2 * W)).filter Odd := by
  unfold oddClosed
  congr 2
  · exact Nat.ceil_natCast W
  · exact_mod_cast Nat.floor_natCast (2 * W)

/-- The odd integers of `[W, 2W]` are `2j + 1` for `W/2 ≤ j ≤ W - 1` (for `W ≥ 1`). -/
lemma card_oddClosed_natCast {W : ℕ} (hW : 1 ≤ W) : (oddClosed (W : ℝ)).card = W - W / 2 := by
  rw [oddClosed_natCast]
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) := fun a b h => by simpa using h
  have : (Icc W (2 * W)).filter Odd = (Icc (W / 2) (W - 1)).image (fun j => 2 * j + 1) := by
    ext u
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨j, rfl⟩⟩
      exact ⟨j, ⟨by omega, by omega⟩, rfl⟩
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨j, rfl⟩⟩
  rw [this, card_image_of_injective _ hinj, Nat.card_Icc]
  omega

/-- `W/2 ≤ #(odd ∩ [W, 2W]) ≤ W/2 + 1` (real division). -/
lemma card_oddClosed_bounds {W : ℕ} (hW : 1 ≤ W) :
    (W : ℝ) / 2 ≤ (oddClosed (W : ℝ)).card ∧ ((oddClosed (W : ℝ)).card : ℝ) ≤ W / 2 + 1 := by
  rw [card_oddClosed_natCast hW]
  have h1 : (W / 2 : ℕ) * 2 ≤ W := Nat.div_mul_le_self W 2
  have h2 : W < (W / 2 + 1) * 2 := by omega
  have hsub : ((W - W / 2 : ℕ) : ℝ) = (W : ℝ) - ((W / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  rw [hsub]
  have e1 : ((W / 2 : ℕ) : ℝ) * 2 ≤ W := by exact_mod_cast h1
  have e2 : (W : ℝ) < ((W / 2 : ℕ) + 1) * 2 := by exact_mod_cast h2
  constructor <;> linarith

/-! ## Limits of `⌊X / m⌋` -/

/-- `⌊X/m⌋ / X → 1/m`. -/
lemma tendsto_natDiv_div_self {m : ℕ} (hm : 0 < m) :
    Tendsto (fun X : ℕ => ((X / m : ℕ) : ℝ) / X) atTop (𝓝 (1 / m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hupper : ∀ X : ℕ, 0 < X → ((X / m : ℕ) : ℝ) / X ≤ 1 / m := by
    intro X hX
    have hX' : (0 : ℝ) < X := by exact_mod_cast hX
    rw [div_le_div_iff₀ hX' hm', one_mul]
    exact_mod_cast Nat.div_mul_le_self X m
  have hlower : ∀ X : ℕ, 0 < X → 1 / m - 1 / X ≤ ((X / m : ℕ) : ℝ) / X := by
    intro X hX
    have hX' : (0 : ℝ) < X := by exact_mod_cast hX
    have h0 : X < (X / m + 1) * m := by
      have := Nat.lt_div_mul_add (a := X) hm; rw [add_mul, one_mul]; exact this
    have h : (X : ℝ) < ((X / m : ℕ) + 1) * m := by exact_mod_cast h0
    rw [div_sub_div _ _ hm'.ne' hX'.ne', div_le_div_iff₀ (by positivity) hX']
    nlinarith
  have hlim : Tendsto (fun X : ℕ => 1 / (m : ℝ) - 1 / X) atTop (𝓝 (1 / m)) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with X hX using hlower X hX
  · filter_upwards [eventually_gt_atTop 0] with X hX using hupper X hX

/-- `⌊X/m⌋ → ∞`. -/
lemma tendsto_natDiv_atTop {m : ℕ} (hm : 0 < m) :
    Tendsto (fun X : ℕ => X / m) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b * m, fun X hX => ?_⟩
  exact (Nat.le_div_iff_mul_le hm).mpr hX

/-- `log ⌊X/m⌋ / log X → 1`. -/
lemma tendsto_log_natDiv_div_log {m : ℕ} (hm : 0 < m) :
    Tendsto (fun X : ℕ => Real.log ((X / m : ℕ) : ℝ) / Real.log X) atTop (𝓝 1) := by
  have hlogX : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- `log ⌊X/m⌋ = log X + log(⌊X/m⌋/X)` and the second term tends to `-log m`
  have hratio := tendsto_natDiv_div_self hm
  have hm' : (0 : ℝ) < 1 / m := by positivity
  have hlogr : Tendsto (fun X : ℕ => Real.log (((X / m : ℕ) : ℝ) / X)) atTop (𝓝 (Real.log (1 / m))) :=
    (Real.continuousAt_log hm'.ne').tendsto.comp hratio
  have hsmall : Tendsto (fun X : ℕ => Real.log (((X / m : ℕ) : ℝ) / X) / Real.log X) atTop (𝓝 0) :=
    hlogr.div_atTop hlogX
  have hsum : Tendsto (fun X : ℕ => 1 + Real.log (((X / m : ℕ) : ℝ) / X) / Real.log X) atTop
      (𝓝 1) := by simpa using tendsto_const_nhds.add hsmall
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop m, eventually_gt_atTop 1] with X hXm hX1
  have hX : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hq : (0 : ℝ) < ((X / m : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_pos hXm hm
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX1)
  rw [Real.log_div hq.ne' hX.ne']
  field_simp
  ring

/-- If `s_X √(log X) → τ`, then also `s_X √(log ⌊X/m⌋) → τ`. -/
lemma tendsto_mul_sqrt_log_natDiv {m : ℕ} (hm : 0 < m) {sX : ℕ → ℝ} {τ : ℝ}
    (hτ : Tendsto (fun X : ℕ => sX X * √(Real.log X)) atTop (𝓝 τ)) :
    Tendsto (fun X : ℕ => sX X * √(Real.log ((X / m : ℕ) : ℝ))) atTop (𝓝 τ) := by
  have hr := (Real.continuous_sqrt.tendsto 1).comp (tendsto_log_natDiv_div_log hm)
  rw [Real.sqrt_one] at hr
  have := hτ.mul hr
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with X hX1
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX1)
  simp only [Function.comp]
  rw [Real.sqrt_div' _ hL.le, mul_assoc, mul_div_cancel₀ _ (Real.sqrt_pos.mpr hL).ne']

end CollatzCLT
