import LeanClt.Sampling.Lemma64

/-!
# Lemma 6.5(ii) [`lem:sampling`], the `[Y, 2Y]` clause

Under the sequential conclusion of Proposition 6.2 [`prop:fixedbase`] for odd dyadic sampling
(`SeqLimit`) and doubling compatibility, the phase average over **all** integers of `[Y, 2Y]`
(`Y` real) converges to the same limit `e^{-D τ²} p`:
`#([Y,2Y] ∩ ℤ)⁻¹ ∑_{Y ≤ n ≤ 2Y} 1_A(n) e^{i s_Y (q(n) + κ log n)} → e^{-D τ²} p`
whenever `Y → ∞` and `s_Y √(log Y) → τ` (`interval_limit`). The centring is at the sampled point
`κ log n`; on `[Y, 2Y]` it differs from the paper's `κ log Y` by at most `|κ| log 2`, which the
frequency `s_Y → 0` kills.

The proof is the paper's. The integers of `[Y, 2Y]` with `v₂(n) = e` are `2^e u` with `u` odd in
`[Y/2^e, 2Y/2^e]` (`sum_interval_two_adic`); for fixed `e`, doubling compatibility turns that layer
into the odd dyadic sample at scale `Y/2^e`, of relative size `2^{-(e+1)}`
(`interval_layer_limit`); Tannery's theorem with domination `5 · 2^{-e}` replaces the truncation
`E₀ → ∞`.

`oddClosed_limit` is the odd-integer analogue (the sample is `oddClosed Y` itself), used for sets of
odd integers such as `P_U(b)`.
-/

open Real Filter Topology Finset Complex

namespace CollatzCLT

/-! ## Counting -/

/-- The odd integers of `[a, b]` are `2j + 1`, `a/2 ≤ j < (b+1)/2`. -/
lemma card_filter_odd_Icc (a b : ℕ) : ((Icc a b).filter Odd).card = (b + 1) / 2 - a / 2 := by
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) := fun x y h => by simpa using h
  have : (Icc a b).filter Odd = (Ico (a / 2) ((b + 1) / 2)).image (fun j => 2 * j + 1) := by
    ext u
    simp only [mem_filter, mem_Icc, mem_Ico, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨j, rfl⟩⟩
      exact ⟨j, ⟨by omega, by omega⟩, rfl⟩
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨j, rfl⟩⟩
  rw [this, card_image_of_injective _ hinj, Nat.card_Ico]

/-- Elementary facts about `a = ⌈W⌉` and `b = ⌊2W⌋` for `W ≥ 0`. -/
lemma ceil_floor_facts {W : ℝ} (hW : 0 ≤ W) :
    W ≤ ⌈W⌉₊ ∧ (⌈W⌉₊ : ℝ) < W + 1 ∧ (⌊2 * W⌋₊ : ℝ) ≤ 2 * W ∧ 2 * W < ⌊2 * W⌋₊ + 1 ∧
      ⌈W⌉₊ ≤ ⌊2 * W⌋₊ + 1 := by
  have h1 := Nat.le_ceil W
  have h2 := Nat.ceil_lt_add_one hW
  have h3 := Nat.floor_le (show 0 ≤ 2 * W by linarith)
  have h4 := Nat.lt_floor_add_one (2 * W)
  refine ⟨h1, h2, h3, h4, ?_⟩
  have : (⌈W⌉₊ : ℝ) < ⌊2 * W⌋₊ + 2 := by linarith
  have h6 : ⌈W⌉₊ < ⌊2 * W⌋₊ + 2 := by exact_mod_cast this
  omega

/-- `W/2 - 1 ≤ #(odd integers of [W, 2W]) ≤ W/2 + 1` for real `W ≥ 0`. -/
lemma card_oddClosed_real {W : ℝ} (hW : 0 ≤ W) :
    W / 2 - 1 ≤ ((oddClosed W).card : ℝ) ∧ ((oddClosed W).card : ℝ) ≤ W / 2 + 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ceil_floor_facts hW
  unfold oddClosed
  rw [card_filter_odd_Icc]
  set a := ⌈W⌉₊
  set b := ⌊2 * W⌋₊
  have hn1 : b ≤ 2 * ((b + 1) / 2 - a / 2) + a := by omega
  have hn2 : 2 * ((b + 1) / 2 - a / 2) + a ≤ b + 2 := by omega
  have r1 : (b : ℝ) ≤ 2 * (((b + 1) / 2 - a / 2 : ℕ) : ℝ) + a := by exact_mod_cast hn1
  have r2 : 2 * (((b + 1) / 2 - a / 2 : ℕ) : ℝ) + a ≤ b + 2 := by exact_mod_cast hn2
  constructor <;> linarith

/-- `Y - 1 ≤ #(integers of [Y, 2Y]) ≤ Y + 1` for real `Y ≥ 0`. -/
lemma card_Icc_real {Y : ℝ} (hY : 0 ≤ Y) :
    Y - 1 ≤ ((Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).card : ℝ) ∧ ((Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).card : ℝ) ≤ Y + 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ceil_floor_facts hY
  rw [Nat.card_Icc]
  have : ((⌊2 * Y⌋₊ + 1 - ⌈Y⌉₊ : ℕ) : ℝ) = (⌊2 * Y⌋₊ : ℝ) + 1 - ⌈Y⌉₊ := by
    rw [Nat.cast_sub h5]; push_cast; ring
  rw [this]
  constructor <;> linarith

/-! ## The two-adic decomposition of `[Y, 2Y]` -/

/-- **Two-adic decomposition of `[Y, 2Y]`.** The integers `n` of `[Y, 2Y]` with `v₂(n) = e` are
`2^e u` with `u` odd in `[Y/2^e, 2Y/2^e]`. -/
theorem sum_interval_two_adic {M : Type*} [AddCommMonoid M] (g : ℕ → M) {Y : ℝ} (hY : 0 < Y) :
    ∑ n ∈ Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, g n =
      ∑ e ∈ range (⌊2 * Y⌋₊ + 1), ∑ u ∈ oddClosed (Y / 2 ^ e), g (2 ^ e * u) := by
  classical
  have hc1 : 1 ≤ ⌈Y⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hY).ne'
  have h1 : Icc ⌈Y⌉₊ ⌊2 * Y⌋₊ = (Icc 1 ⌊2 * Y⌋₊).filter (fun n => ⌈Y⌉₊ ≤ n) := by
    ext n; simp only [mem_Icc, mem_filter]; omega
  rw [h1, sum_filter, sum_Icc_two_adic]
  apply sum_congr rfl
  intro e _
  rw [← sum_filter, filter_filter]
  apply sum_congr _ (fun _ _ => rfl)
  have h2e : (0 : ℝ) < 2 ^ e := by positivity
  ext u
  unfold oddClosed
  simp only [mem_filter, mem_Icc]
  have hceil : ⌈Y⌉₊ ≤ 2 ^ e * u ↔ ⌈Y / 2 ^ e⌉₊ ≤ u := by
    rw [Nat.ceil_le, Nat.ceil_le, div_le_iff₀ h2e]
    push_cast; constructor <;> intro h <;> linarith
  have hfloor : u ≤ ⌊2 * Y⌋₊ / 2 ^ e ↔ u ≤ ⌊2 * (Y / 2 ^ e)⌋₊ := by
    rw [Nat.le_div_iff_mul_le (by positivity), Nat.le_floor_iff (by positivity),
      Nat.le_floor_iff (by positivity), mul_div_assoc', le_div_iff₀ h2e]
    push_cast; rfl
  constructor
  · rintro ⟨⟨-, hu2⟩, hodd, hc⟩
    exact ⟨⟨hceil.mp hc, hfloor.mp hu2⟩, hodd⟩
  · rintro ⟨⟨hc, hu2⟩, hodd⟩
    exact ⟨⟨hodd.pos, hfloor.mpr hu2⟩, hodd, hceil.mpr hc⟩

/-- For `2^e > 2Y` the `e`-th layer of `[Y, 2Y]` is empty. -/
lemma oddClosed_eq_empty {Y : ℝ} (hY : 0 < Y) {e : ℕ} (he : 2 * Y < 2 ^ e) :
    oddClosed (Y / 2 ^ e) = ∅ := by
  unfold oddClosed
  have h2e : (0 : ℝ) < 2 ^ e := by positivity
  have hf : ⌊2 * (Y / 2 ^ e)⌋₊ = 0 := by
    rw [Nat.floor_eq_zero, mul_div_assoc', div_lt_one h2e]; exact he
  have hc : 1 ≤ ⌈Y / 2 ^ e⌉₊ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (div_pos hY h2e)).ne'
  rw [hf, Icc_eq_empty (by omega), filter_empty]

/-! ## Limits along real scales -/

/-- `s_k √(log Y_k) → τ` with `Y_k → ∞` forces `s_k → 0`. -/
lemma tendsto_zero_of_mul_sqrt_log' {Y s : ℕ → ℝ} {τ : ℝ} (hY : Tendsto Y atTop atTop)
    (hτ : Tendsto (fun k => s k * √(Real.log (Y k))) atTop (𝓝 τ)) : Tendsto s atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun k => √(Real.log (Y k))) atTop atTop :=
    (tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).comp hY
  refine (hτ.div_atTop hsqrt).congr' ?_
  filter_upwards [hY.eventually (eventually_gt_atTop 1)] with k hk
  have := Real.sqrt_pos.mpr (Real.log_pos hk)
  field_simp

/-- If `log Y'_k / log Y_k → 1`, the frequency condition passes from `Y` to `Y'`. -/
lemma tendsto_mul_sqrt_log_of_ratio {Y Y' s : ℕ → ℝ} {τ : ℝ} (hY : Tendsto Y atTop atTop)
    (hr : Tendsto (fun k => Real.log (Y' k) / Real.log (Y k)) atTop (𝓝 1))
    (hτ : Tendsto (fun k => s k * √(Real.log (Y k))) atTop (𝓝 τ)) :
    Tendsto (fun k => s k * √(Real.log (Y' k))) atTop (𝓝 τ) := by
  have hr' := (Real.continuous_sqrt.tendsto 1).comp hr
  rw [Real.sqrt_one] at hr'
  have := hτ.mul hr'
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [hY.eventually (eventually_gt_atTop 1)] with k hk
  have hL : 0 < Real.log (Y k) := Real.log_pos hk
  simp only [Function.comp]
  rw [Real.sqrt_div' _ hL.le, mul_assoc, mul_div_cancel₀ _ (Real.sqrt_pos.mpr hL).ne']

/-- `log(Y/2^e) / log Y → 1`. -/
lemma tendsto_log_div_pow_ratio {Y : ℕ → ℝ} (hY : Tendsto Y atTop atTop) (e : ℕ) :
    Tendsto (fun k => Real.log (Y k / 2 ^ e) / Real.log (Y k)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun k => Real.log (Y k)) atTop atTop := Real.tendsto_log_atTop.comp hY
  have h : Tendsto (fun k => 1 - (e * Real.log 2) / Real.log (Y k)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hlog)
  refine h.congr' ?_
  filter_upwards [hY.eventually (eventually_gt_atTop 1)] with k hk
  have hL : 0 < Real.log (Y k) := Real.log_pos hk
  rw [Real.log_div (by linarith) (by positivity), Real.log_pow]
  field_simp

/-- `(a Y + b) / (Y + c) → a` as `Y → ∞`. -/
lemma tendsto_affine_ratio {Y : ℕ → ℝ} (hY : Tendsto Y atTop atTop) (a b c : ℝ) :
    Tendsto (fun k => (a * Y k + b) / (Y k + c)) atTop (𝓝 a) := by
  have hinv : Tendsto (fun k => (Y k)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hY
  have h : Tendsto (fun k => (a + b * (Y k)⁻¹) / (1 + c * (Y k)⁻¹)) atTop
      (𝓝 ((a + b * 0) / (1 + c * 0))) :=
    (tendsto_const_nhds.add (hinv.const_mul b)).div (tendsto_const_nhds.add (hinv.const_mul c))
      (by simp)
  simp only [mul_zero, add_zero, div_one] at h
  refine h.congr' ?_
  filter_upwards [hY.eventually (eventually_gt_atTop (max 0 (-c)))] with k hk
  have hk0 : 0 < Y k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkc : 0 < Y k + c := by linarith [le_max_right 0 (-c)]
  field_simp

/-! ## Recentring on `[W, 2W]` -/

/-- On the odd integers of `[W, 2W]` (`W` real), recentring `κ log u` at `κ log W` costs at most
`|s| |κ| log 2` per point. -/
lemma norm_sum_recentre_le_real (A : Set ℕ) (q : ℕ → ℝ) (κ : ℝ) {W : ℝ} (hW : 0 < W) (s : ℝ) :
    ‖∑ u ∈ oddClosed W, (ph A q s (κ * Real.log u) u - ph A q s (κ * Real.log W) u)‖
      ≤ (oddClosed W).card * (|s| * (|κ| * Real.log 2)) := by
  calc ‖∑ u ∈ oddClosed W, (ph A q s (κ * Real.log u) u - ph A q s (κ * Real.log W) u)‖
      ≤ ∑ u ∈ oddClosed W, ‖ph A q s (κ * Real.log u) u - ph A q s (κ * Real.log W) u‖ :=
        norm_sum_le _ _
    _ ≤ ∑ u ∈ oddClosed W, |s| * (|κ| * Real.log 2) := by
        apply sum_le_sum
        intro u hu
        unfold oddClosed at hu
        rw [mem_filter, mem_Icc] at hu
        have hu1 : W ≤ u := Nat.ceil_le.mp hu.1.1
        have hu2 : (u : ℝ) ≤ 2 * W :=
          (Nat.cast_le.mpr hu.1.2).trans (Nat.floor_le (by linarith))
        have hlog : |Real.log u - Real.log W| ≤ Real.log 2 := by
          rw [← Real.log_div (by linarith) hW.ne', abs_of_nonneg
            (Real.log_nonneg ((one_le_div hW).mpr hu1))]
          exact Real.log_le_log (div_pos (by linarith) hW) ((div_le_iff₀ hW).mpr (by linarith))
        refine (norm_ph_sub_le A q s _ _ u).trans ?_
        rw [← mul_sub, abs_mul]
        gcongr
    _ = (oddClosed W).card * (|s| * (|κ| * Real.log 2)) := by simp

/-- `#oddClosed W > 0` for `W > 2`. -/
lemma card_oddClosed_pos {W : ℝ} (hW : 2 < W) : (0 : ℝ) < (oddClosed W).card := by
  have := (card_oddClosed_real (by linarith : (0 : ℝ) ≤ W)).1
  linarith

/-- The odd-sample sum is `#oddClosed(W) · Φ_W(s)` plus the recentring error. -/
lemma sum_oddClosed_eq (A : Set ℕ) (q : ℕ → ℝ) (κ W s : ℝ) (hc : ((oddClosed W).card : ℂ) ≠ 0) :
    ∑ u ∈ oddClosed W, ph A q s (κ * Real.log u) u =
      ∑ u ∈ oddClosed W, (ph A q s (κ * Real.log u) u - ph A q s (κ * Real.log W) u) +
        ((oddClosed W).card : ℂ) * oddCF A q κ W s := by
  unfold oddCF
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, sum_sub_distrib]
  ring

/-! ## The odd sample at scale `Y` -/

/-- **Odd dyadic sampling, centred at the sampled point.** Under `SeqLimit`, the average of
`1_A(u) e^{i s_Y (q(u) + κ log u)}` over the odd integers `u` of `[Y, 2Y]` tends to `e^{-D τ²} p`. -/
theorem oddClosed_limit {A : Set ℕ} {q : ℕ → ℝ} {κ D : ℝ} {p : ℂ} (hseq : SeqLimit A q κ D p)
    {Y s : ℕ → ℝ} {τ : ℝ} (hY : Tendsto Y atTop atTop)
    (hτ : Tendsto (fun k => s k * √(Real.log (Y k))) atTop (𝓝 τ)) :
    Tendsto (fun k => ((oddClosed (Y k)).card : ℂ)⁻¹ *
      ∑ u ∈ oddClosed (Y k), ph A q (s k) (κ * Real.log u) u) atTop
      (𝓝 ((Real.exp (-(D * τ ^ 2)) : ℂ) * p)) := by
  have hs0 := tendsto_zero_of_mul_sqrt_log' hY hτ
  have hcf := hseq Y s τ hY hτ
  have hR : Tendsto (fun k => ((oddClosed (Y k)).card : ℂ)⁻¹ *
      ∑ u ∈ oddClosed (Y k), (ph A q (s k) (κ * Real.log u) u -
        ph A q (s k) (κ * Real.log (Y k)) u)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun k => |s k| * (|κ| * Real.log 2))
    · filter_upwards [hY.eventually (eventually_gt_atTop 2)] with k hk
      have hc := card_oddClosed_pos hk
      have hb := norm_sum_recentre_le_real A q κ (by linarith : (0 : ℝ) < Y k) (s k)
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc _ ≤ (((oddClosed (Y k)).card : ℝ))⁻¹ *
            (((oddClosed (Y k)).card : ℝ) * (|s k| * (|κ| * Real.log 2))) := by gcongr
        _ = _ := by field_simp
    · simpa using (hs0.abs).mul_const (|κ| * Real.log 2)
  have := hR.add hcf
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [hY.eventually (eventually_gt_atTop 2)] with k hk
  have hc : ((oddClosed (Y k)).card : ℂ) ≠ 0 := by
    have := card_oddClosed_pos hk
    exact_mod_cast this.ne'
  rw [sum_oddClosed_eq A q κ (Y k) (s k) hc, mul_add, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-! ## The `e`-th layer of `[Y, 2Y]` -/

/-- **Layer limit.** For fixed `e` (with doubling compatibility at that `e`), the sum over the odd
`u ∈ [Y/2^e, 2Y/2^e]` of the phase at `2^e u`, divided by `#([Y, 2Y] ∩ ℤ)`, tends to
`2^{-(e+1)} e^{-D τ²} p`. -/
theorem interval_layer_limit {A : Set ℕ} {q : ℕ → ℝ} {κ D e0 : ℝ} {p : ℂ}
    (hseq : SeqLimit A q κ D p) (e : ℕ)
    (hdble : ∃ n0 : ℕ, ∀ u : ℕ, n0 ≤ u →
      (2 ^ e * u ∈ A ↔ u ∈ A) ∧ (u ∈ A → q (2 ^ e * u) = q u - e * e0))
    {Y s : ℕ → ℝ} {τ : ℝ} (hY : Tendsto Y atTop atTop)
    (hτ : Tendsto (fun k => s k * √(Real.log (Y k))) atTop (𝓝 τ)) :
    Tendsto (fun k => ((Icc ⌈Y k⌉₊ ⌊2 * Y k⌋₊).card : ℂ)⁻¹ *
      ∑ u ∈ oddClosed (Y k / 2 ^ e),
        ph A q (s k) (κ * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u))
      atTop (𝓝 ((1 / 2 : ℂ) ^ (e + 1) * ((Real.exp (-(D * τ ^ 2)) : ℂ) * p))) := by
  classical
  obtain ⟨n0, hn0⟩ := hdble
  set ℓ : ℂ := (Real.exp (-(D * τ ^ 2)) : ℂ) * p with hℓ
  have h2e : (0 : ℝ) < 2 ^ e := by positivity
  set W : ℕ → ℝ := fun k => Y k / 2 ^ e with hWdef
  have hW : Tendsto W atTop atTop := hY.atTop_div_const h2e
  have hτW : Tendsto (fun k => s k * √(Real.log (W k))) atTop (𝓝 τ) :=
    tendsto_mul_sqrt_log_of_ratio hY (tendsto_log_div_pow_ratio hY e) hτ
  have hs0 := tendsto_zero_of_mul_sqrt_log' hY hτ
  set NI : ℕ → ℝ := fun k => ((Icc ⌈Y k⌉₊ ⌊2 * Y k⌋₊).card : ℝ) with hNI
  set NO : ℕ → ℝ := fun k => ((oddClosed (W k)).card : ℝ) with hNO
  -- (a) the odd dyadic characteristic function at scale `W = Y/2^e`
  have hcf : Tendsto (fun k => oddCF A q κ (W k) (s k)) atTop (𝓝 ℓ) := hseq W s τ hW hτW
  -- (b) the relative size `#oddClosed(W) / #([Y,2Y] ∩ ℤ) → 2^{-(e+1)}`
  have hcnt : Tendsto (fun k => NO k / NI k) atTop (𝓝 ((1 / 2) ^ (e + 1))) := by
    have hlo := tendsto_affine_ratio hY ((1 / 2) ^ (e + 1)) (-1) 1
    have hhi := tendsto_affine_ratio hY ((1 / 2) ^ (e + 1)) 1 (-1)
    have hWY : ∀ k, (1 / 2 : ℝ) ^ (e + 1) * Y k = W k / 2 := by
      intro k; simp only [hWdef, one_div, inv_pow, pow_succ]; field_simp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [hY.eventually (eventually_gt_atTop 2)] with k hk
      have hWk : 0 ≤ W k := by simp only [hWdef]; positivity
      have c1 := (card_oddClosed_real hWk).1
      have i1 := (card_Icc_real (show 0 ≤ Y k by linarith)).1
      have i2 := (card_Icc_real (show 0 ≤ Y k by linarith)).2
      rw [hWY k]
      exact div_le_div₀ (by positivity) c1 (by linarith) i2
    · filter_upwards [hY.eventually (eventually_gt_atTop 2)] with k hk
      have hWk : 0 ≤ W k := by simp only [hWdef]; positivity
      have c2 := (card_oddClosed_real hWk).2
      have i1 := (card_Icc_real (show 0 ≤ Y k by linarith)).1
      rw [hWY k]
      exact div_le_div₀ (by positivity) c2 (by linarith) i1
  -- (c) the phase factor tends to `1`
  have hφ : Tendsto (fun k => cexp (((s k * (e * (κ * Real.log 2 - e0)) : ℝ) : ℂ) * I)) atTop
      (𝓝 1) := by
    have h1 : Tendsto (fun k => s k * (e * (κ * Real.log 2 - e0))) atTop (𝓝 0) := by
      simpa using hs0.mul_const (e * (κ * Real.log 2 - e0))
    have hc : Continuous (fun x : ℝ => cexp ((x : ℂ) * I)) := by fun_prop
    have := (hc.tendsto 0).comp h1
    have h0 : cexp (((0 : ℝ) : ℂ) * I) = 1 := by simp
    rw [h0] at this
    exact this
  -- (d) the recentring error, normalised by `#([Y,2Y] ∩ ℤ)`
  have hR : Tendsto (fun k => ((NI k : ℝ) : ℂ)⁻¹ *
      ∑ u ∈ oddClosed (W k), (ph A q (s k) (κ * Real.log u) u -
        ph A q (s k) (κ * Real.log (W k)) u)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun k => NO k / NI k * (|s k| * (|κ| * Real.log 2)))
    · filter_upwards [hY.eventually (eventually_gt_atTop 2)] with k hk
      have hWk : 0 < W k := by simp only [hWdef]; positivity
      have i1 := (card_Icc_real (show 0 ≤ Y k by linarith)).1
      have hI : 0 < NI k := by simp only [hNI]; linarith
      have hb := norm_sum_recentre_le_real A q κ hWk (s k)
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hI]
      calc _ ≤ (NI k)⁻¹ * (NO k * (|s k| * (|κ| * Real.log 2))) := by gcongr
        _ = _ := by ring
    · simpa using hcnt.mul ((hs0.abs).mul_const (|κ| * Real.log 2))
  -- (e) assemble
  have hlim := hφ.mul ((((Complex.continuous_ofReal.tendsto _).comp hcnt).mul hcf).add hR)
  have hval : (1 : ℂ) * ((((1 / 2 : ℝ) ^ (e + 1) : ℝ) : ℂ) * ℓ + 0) = (1 / 2 : ℂ) ^ (e + 1) * ℓ := by
    push_cast; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hW.eventually (eventually_gt_atTop ((n0 : ℝ) + 2))] with k hk
  have hk2 : 2 < W k := by linarith [(Nat.cast_nonneg n0 : (0 : ℝ) ≤ n0)]
  have hc : ((oddClosed (W k)).card : ℂ) ≠ 0 := by
    have := card_oddClosed_pos hk2
    exact_mod_cast this.ne'
  have hfac : ∀ u ∈ oddClosed (W k),
      ph A q (s k) (κ * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u) =
      cexp (((s k * (e * (κ * Real.log 2 - e0)) : ℝ) : ℂ) * I) *
        ph A q (s k) (κ * Real.log u) u := by
    intro u hu
    unfold oddClosed at hu
    rw [mem_filter, mem_Icc] at hu
    have hu1 : W k ≤ u := Nat.ceil_le.mp hu.1.1
    have hun : (n0 : ℝ) < u := by linarith
    have hun' : n0 < u := by exact_mod_cast hun
    exact ph_two_pow_mul e hn0 (s k) hun'.le (by omega)
  simp only [Function.comp_apply]
  rw [show Y k / 2 ^ e = W k from rfl, sum_congr rfl hfac, ← mul_sum,
    sum_oddClosed_eq A q κ (W k) (s k) hc]
  simp only [hNI, hNO]
  push_cast
  ring

/-! ## The `[Y, 2Y]` clause -/

/-- **Lemma 6.5(ii) [`lem:sampling`], the `[Y, 2Y]` clause.** Under the sequential conclusion of
Proposition 6.2 for odd dyadic sampling and doubling compatibility, for real scales `Y_k → ∞` and
frequencies with `s_k √(log Y_k) → τ`,
`#([Y_k, 2Y_k] ∩ ℤ)⁻¹ ∑_{Y_k ≤ n ≤ 2Y_k} 1_A(n) e^{i s_k (q(n) + κ log n)} → e^{-D τ²} p`. -/
theorem interval_limit {A : Set ℕ} {q : ℕ → ℝ} {κ D e0 : ℝ} {p : ℂ} (hseq : SeqLimit A q κ D p)
    (hdbl : DoublingCompatible A q e0) {Y s : ℕ → ℝ} {τ : ℝ} (hY : Tendsto Y atTop atTop)
    (hτ : Tendsto (fun k => s k * √(Real.log (Y k))) atTop (𝓝 τ)) :
    Tendsto (fun k => ((Icc ⌈Y k⌉₊ ⌊2 * Y k⌋₊).card : ℂ)⁻¹ *
      ∑ n ∈ Icc ⌈Y k⌉₊ ⌊2 * Y k⌋₊, ph A q (s k) (κ * Real.log n) n) atTop
      (𝓝 ((Real.exp (-(D * τ ^ 2)) : ℂ) * p)) := by
  classical
  set ℓ : ℂ := (Real.exp (-(D * τ ^ 2)) : ℂ) * p with hℓ
  -- the `e`-th two-adic layer
  let Fk : ℕ → ℕ → ℂ := fun k e => ((Icc ⌈Y k⌉₊ ⌊2 * Y k⌋₊).card : ℂ)⁻¹ *
    ∑ u ∈ oddClosed (Y k / 2 ^ e), ph A q (s k) (κ * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u)
  have hsum : ∀ᶠ k in atTop, ((Icc ⌈Y k⌉₊ ⌊2 * Y k⌋₊).card : ℂ)⁻¹ *
      ∑ n ∈ Icc ⌈Y k⌉₊ ⌊2 * Y k⌋₊, ph A q (s k) (κ * Real.log n) n = ∑' e, Fk k e := by
    filter_upwards [hY.eventually (eventually_gt_atTop 0)] with k hk
    rw [tsum_eq_sum (s := range (⌊2 * Y k⌋₊ + 1)), sum_interval_two_adic _ hk, mul_sum]
    intro e he
    simp only [mem_range, not_lt] at he
    have h2 : 2 * Y k < 2 ^ e := by
      have h1 : ((⌊2 * Y k⌋₊ + 1 : ℕ) : ℝ) ≤ e := by exact_mod_cast he
      have h3 : (e : ℝ) < 2 ^ e := by exact_mod_cast Nat.lt_two_pow_self
      push_cast at h1
      linarith [Nat.lt_floor_add_one (2 * Y k)]
    simp [Fk, oddClosed_eq_empty hk h2]
  -- each layer converges
  have hlayer : ∀ e : ℕ, Tendsto (fun k => Fk k e) atTop (𝓝 ((1 / 2 : ℂ) ^ (e + 1) * ℓ)) := by
    intro e
    obtain ⟨n0, hn0⟩ := hdbl.iterate
    exact interval_layer_limit hseq e ⟨n0, hn0 e⟩ hY hτ
  -- domination by `5 · 2^{-e}`
  have hbound : ∀ᶠ k in atTop, ∀ e, ‖Fk k e‖ ≤ 5 * (1 / 2 : ℝ) ^ e := by
    filter_upwards [hY.eventually (eventually_ge_atTop 2)] with k hk e
    have h2e : (0 : ℝ) < 2 ^ e := by positivity
    have i1 := (card_Icc_real (show 0 ≤ Y k by linarith)).1
    have hI : Y k / 2 ≤ ((Icc ⌈Y k⌉₊ ⌊2 * Y k⌋₊).card : ℝ) := by linarith
    have hle : ‖Fk k e‖ ≤ ((oddClosed (Y k / 2 ^ e)).card : ℝ) /
        ((Icc ⌈Y k⌉₊ ⌊2 * Y k⌋₊).card : ℝ) := by
      have hs : ‖∑ u ∈ oddClosed (Y k / 2 ^ e), ph A q (s k)
          (κ * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u)‖ ≤ (oddClosed (Y k / 2 ^ e)).card := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ u ∈ oddClosed (Y k / 2 ^ e), ‖ph A q (s k) (κ * Real.log ((2 ^ e * u : ℕ) : ℝ))
              (2 ^ e * u)‖ ≤ ∑ u ∈ oddClosed (Y k / 2 ^ e), (1 : ℝ) :=
              sum_le_sum fun u _ => norm_ph_le _ _ _ _ _
          _ = _ := by simp
      calc ‖Fk k e‖ = (((Icc ⌈Y k⌉₊ ⌊2 * Y k⌋₊).card : ℝ))⁻¹ * ‖∑ u ∈ oddClosed (Y k / 2 ^ e),
            ph A q (s k) (κ * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u)‖ := by
            simp only [Fk, norm_mul, norm_inv, Complex.norm_natCast]
        _ ≤ (((Icc ⌈Y k⌉₊ ⌊2 * Y k⌋₊).card : ℝ))⁻¹ * (oddClosed (Y k / 2 ^ e)).card := by
            gcongr
        _ = _ := by ring
    refine hle.trans ?_
    by_cases hcase : 2 * Y k < 2 ^ e
    · rw [oddClosed_eq_empty (by linarith) hcase]
      simp only [card_empty, Nat.cast_zero, zero_div]
      positivity
    · push Not at hcase
      have hW : 0 ≤ Y k / 2 ^ e := by positivity
      have c2 := (card_oddClosed_real hW).2
      have h1 : 1 ≤ 2 * (Y k / 2 ^ e) := by
        rw [mul_div_assoc', le_div_iff₀ h2e]; linarith
      have c3 : ((oddClosed (Y k / 2 ^ e)).card : ℝ) ≤ 5 / 2 * (Y k / 2 ^ e) := by linarith
      calc ((oddClosed (Y k / 2 ^ e)).card : ℝ) / ((Icc ⌈Y k⌉₊ ⌊2 * Y k⌋₊).card : ℝ)
          ≤ (5 / 2 * (Y k / 2 ^ e)) / (Y k / 2) :=
            div_le_div₀ (by positivity) c3 (by linarith) hI
        _ = 5 * (1 / 2 : ℝ) ^ e := by
            rw [one_div, inv_pow]
            field_simp
  have hT := tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left 5)
    hlayer hbound
  have hgeom : ∑' e : ℕ, (1 / 2 : ℂ) ^ (e + 1) * ℓ = ℓ := by
    simp_rw [pow_succ, mul_assoc]
    rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num)]
    norm_num
    ring
  rw [hgeom] at hT
  exact hT.congr' (hsum.mono fun k hk => hk.symm)

end CollatzCLT
