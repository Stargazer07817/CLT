import LeanClt.Main.Conditional
import LeanClt.Elementary.Syracuse

/-!
# The odd-clock bridge: positivity of `P_U(b)` from positivity of `P_T(b)`

For odd `b`, `P_T(b) = {2^e u : e ≥ 0, u ∈ P_U(b)}` (`pow_mul_mem_predT_iff`, with
`predU_eq`), so the windows satisfy the two-adic identity
`#(P_T(b) ∩ [1,X]) = ∑_{e} #(P_U(b) ∩ [1, ⌊X/2^e⌋])` (`card_window_predT`).

* `density_predU_of_adjacent`: the fixed-base limit (Proposition 6.2) at frequency `0` gives a
  natural density `d_U` of `P_U(b)`, **without** any positivity assumption (it may a priori be `0`).
* `predU_pos_of_predT_pos`: if `P_T(b)` has lower density `≥ c_T > 0` (Theorem 8.1) and `P_U(b)`
  has a density `d_U`, then `c_T ≤ 2 d_U`; hence `P_U(b)` has positive lower density. (In fact
  `dens P_T(b) = 2 dens P_U(b)`; only the inequality is needed.)
-/

open Real Filter Topology Finset

namespace CollatzCLT

/-! ## The set identity -/

lemma pow_mul_mem_predT_iff {b : ℕ} (hb : Odd b) {u : ℕ} (hu : 0 < u) (e : ℕ) :
    2 ^ e * u ∈ Pred T b ↔ u ∈ Pred T b := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hpos : 0 < 2 ^ e * u := by positivity
    have hne : 2 * (2 ^ e * u) ≠ b := by
      intro h
      have : Even b := ⟨2 ^ e * u, by rw [← h]; ring⟩
      exact (Nat.not_even_iff_odd.mpr hb) this
    rw [pow_succ, mul_comm (2 ^ e) 2, mul_assoc, two_mul_mem_predT_iff hpos hne, ih]

lemma odd_mem_predT_iff {b : ℕ} (hb : Odd b) {u : ℕ} (hu : Odd u) :
    u ∈ Pred T b ↔ u ∈ PredU b := by
  rw [predU_eq hb]
  exact ⟨fun h => ⟨hu, h⟩, fun h => h.2⟩

/-- **The two-adic count.** -/
theorem card_window_predT {b : ℕ} (hb : Odd b) (X : ℕ) :
    ((window (Pred T b) X).card : ℝ) =
      ∑ e ∈ range (X + 1), ((window (PredU b) (X / 2 ^ e)).card : ℝ) := by
  classical
  have h1 : ((window (Pred T b) X).card : ℝ) =
      ∑ n ∈ Icc 1 X, (if n ∈ Pred T b then (1 : ℝ) else 0) := by
    unfold window; rw [Finset.card_filter]; push_cast; rfl
  rw [h1, sum_Icc_two_adic]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h2 : ((window (PredU b) (X / 2 ^ e)).card : ℝ) =
      ∑ u ∈ (Icc 1 (X / 2 ^ e)).filter Odd, (if u ∈ PredU b then (1 : ℝ) else 0) := by
    unfold window
    rw [Finset.card_filter, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : u ∈ PredU b
    · simp [h, h.2.1]
    · simp only [h, ↓reduceIte, ite_self]
  rw [h2]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [mem_filter, mem_Icc] at hu
  rw [pow_mul_mem_predT_iff hb (by omega) e, odd_mem_predT_iff hb hu.2]

/-! ## Density of `P_U(b)` without positivity -/

/-- The fixed-base limit at frequency `0`: `P_U(b)` has a natural density. -/
theorem density_predU_of_adjacent (b : ℕ) {α : ℝ} (hα : 1 < α)
    (hadj : AdjacentScales (oddCF (PredU b) (fun n => -(hit U b n : ℝ)) κU) (VU / 2) α) :
    ∃ d : ℝ, HasDensity (PredU b) d := by
  obtain ⟨p, -, hseq0⟩ := fixed_base_limit_seq hα hadj
    (fun Y => continuousAt_oddCF (PredU b) _ κU Y)
  have h0 := uniform_limit_odd (fun Y sY τ hY hτ' => hseq0 atTop Y sY τ hY hτ')
    (fun n hn => hn.2.1) (sX := fun _ => 0) (τ := 0) (by simp)
  simp only [sum_ph_zero, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul,
    zero_pow two_ne_zero] at h0
  have hdC : Tendsto (fun X : ℕ => ((((window (PredU b) X).card : ℝ) / X : ℝ) : ℂ)) atTop
      (𝓝 (p / 2)) := by
    refine h0.congr' (Eventually.of_forall fun X => ?_)
    push_cast; ring
  refine ⟨p.re / 2, ?_⟩
  have := (Complex.continuous_re.tendsto _).comp hdC
  simpa [HasDensity, Function.comp_def] using this

/-! ## Positivity of `P_U(b)` -/

lemma geom_half_le (N : ℕ) : ∑ j ∈ range N, (1 / 2 : ℝ) ^ j ≤ 2 := by
  have h := summable_geometric_two.sum_le_tsum (range N) (fun j _ => by positivity)
  rwa [tsum_geometric_two] at h

lemma card_window_le (A : Set ℕ) (X : ℕ) : ((window A X).card : ℝ) ≤ X := by
  classical
  have : (window A X).card ≤ X := by
    unfold window
    exact (Finset.card_filter_le _ _).trans (by simp)
  exact_mod_cast this

lemma natdiv_le (X e : ℕ) : ((X / 2 ^ e : ℕ) : ℝ) ≤ X * (1 / 2) ^ e := by
  have h : ((X / 2 ^ e : ℕ) : ℝ) ≤ (X : ℝ) / ((2 ^ e : ℕ) : ℝ) := Nat.cast_div_le
  push_cast at h
  rw [one_div_pow, mul_one_div]; exact h

/-- `#(A ∩ [1, ⌊X/2^e⌋])/X → d/2^e` when `A` has density `d`. -/
lemma tendsto_window_div_pow {A : Set ℕ} {d : ℝ} (hd : HasDensity A d) (e : ℕ) :
    Tendsto (fun X : ℕ => ((window A (X / 2 ^ e)).card : ℝ) / X) atTop
      (𝓝 (d * (1 / 2) ^ e)) := by
  have h2e : (0 : ℝ) < 2 ^ e := by positivity
  have hY : Tendsto (fun X : ℕ => X / 2 ^ e) atTop atTop :=
    Nat.tendsto_div_const_atTop (by positivity)
  have h1 : Tendsto (fun X : ℕ => ((window A (X / 2 ^ e)).card : ℝ) / ((X / 2 ^ e : ℕ) : ℝ))
      atTop (𝓝 d) := hd.comp hY
  -- `⌊X/2^e⌋ / X → 2^{-e}`
  have h2 : Tendsto (fun X : ℕ => ((X / 2 ^ e : ℕ) : ℝ) / X) atTop (𝓝 ((1 / 2) ^ e)) := by
    have hlo : Tendsto (fun X : ℕ => (1 / 2 : ℝ) ^ e - 1 / X) atTop (𝓝 ((1 / 2) ^ e)) := by
      have := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ) ^ e)).sub this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with X hX
      have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
      have hmod := Nat.div_add_mod X (2 ^ e)
      have hlt := Nat.mod_lt X (show 0 < 2 ^ e by positivity)
      have hreal : (X : ℝ) < 2 ^ e * ((X / 2 ^ e : ℕ) : ℝ) + 2 ^ e := by
        have : (X : ℝ) = 2 ^ e * ((X / 2 ^ e : ℕ) : ℝ) + ((X % 2 ^ e : ℕ) : ℝ) := by
          exact_mod_cast hmod.symm
        have h' : ((X % 2 ^ e : ℕ) : ℝ) < 2 ^ e := by exact_mod_cast hlt
        linarith
      have hYlb : (X : ℝ) / 2 ^ e - 1 ≤ ((X / 2 ^ e : ℕ) : ℝ) := by
        have : (X : ℝ) / 2 ^ e < ((X / 2 ^ e : ℕ) : ℝ) + 1 := by
          rw [div_lt_iff₀ h2e]; linarith
        linarith
      calc (1 / 2 : ℝ) ^ e - 1 / X = ((X : ℝ) / 2 ^ e - 1) / X := by
            rw [one_div_pow]; field_simp
        _ ≤ ((X / 2 ^ e : ℕ) : ℝ) / X := div_le_div_of_nonneg_right hYlb hX0.le
    · filter_upwards [eventually_gt_atTop 0] with X hX
      have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
      rw [div_le_iff₀ hX0, mul_comm]
      exact natdiv_le X e
  refine (h1.mul h2).congr' ?_
  filter_upwards [eventually_ge_atTop (2 ^ e)] with X hX
  have hY0 : (0 : ℝ) < ((X / 2 ^ e : ℕ) : ℝ) := by
    have : 0 < X / 2 ^ e := Nat.div_pos hX (by positivity)
    exact_mod_cast this
  field_simp

/-- **The bridge.** If `P_T(b)` has positive lower density and `P_U(b)` has a natural density,
then `P_U(b)` has positive lower density. -/
theorem predU_pos_of_predT_pos {b : ℕ} (hb : Odd b) {dU : ℝ} (hdU : HasDensity (PredU b) dU)
    (hposT : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (Pred T b) X).card : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (PredU b) X).card : ℝ) := by
  obtain ⟨cT, hcT, hT⟩ := hposT
  have hdU0 : 0 ≤ dU := ge_of_tendsto hdU (Eventually.of_forall fun X => by positivity)
  -- for every `K`: `c_T ≤ ∑_{e<K} d_U 2^{-e} + 2·2^{-K} ≤ 2 d_U + 2·2^{-K}`
  have hK : ∀ K : ℕ, cT ≤ 2 * dU + 2 * (1 / 2 : ℝ) ^ K := by
    intro K
    have hlim : Tendsto (fun X : ℕ => ∑ e ∈ range K, ((window (PredU b) (X / 2 ^ e)).card : ℝ) / X
        + 2 * (1 / 2 : ℝ) ^ K) atTop
        (𝓝 (∑ e ∈ range K, dU * (1 / 2) ^ e + 2 * (1 / 2 : ℝ) ^ K)) :=
      (tendsto_finsetSum _ fun e _ => tendsto_window_div_pow hdU e).add tendsto_const_nhds
    have hle : cT ≤ ∑ e ∈ range K, dU * (1 / 2) ^ e + 2 * (1 / 2 : ℝ) ^ K := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [hT, eventually_gt_atTop 0, eventually_ge_atTop K] with X hX hX0 hXK
      have hXr : (0 : ℝ) < X := by exact_mod_cast hX0
      rw [card_window_predT hb X, ← Finset.sum_range_add_sum_Ico _ (by omega : K ≤ X + 1)] at hX
      have htail : ∑ e ∈ Ico K (X + 1), ((window (PredU b) (X / 2 ^ e)).card : ℝ) ≤
          2 * (1 / 2 : ℝ) ^ K * X := by
        calc ∑ e ∈ Ico K (X + 1), ((window (PredU b) (X / 2 ^ e)).card : ℝ)
            ≤ ∑ e ∈ Ico K (X + 1), (X : ℝ) * (1 / 2) ^ e := by
              exact Finset.sum_le_sum fun e _ => (card_window_le _ _).trans (natdiv_le X e)
          _ = (X : ℝ) * (1 / 2) ^ K * ∑ j ∈ range (X + 1 - K), (1 / 2 : ℝ) ^ j := by
              rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [pow_add]; ring
          _ ≤ (X : ℝ) * (1 / 2) ^ K * 2 := by
              gcongr
              exact geom_half_le _
          _ = 2 * (1 / 2 : ℝ) ^ K * X := by ring
      have : cT ≤ (∑ e ∈ range K, ((window (PredU b) (X / 2 ^ e)).card : ℝ) +
          ∑ e ∈ Ico K (X + 1), ((window (PredU b) (X / 2 ^ e)).card : ℝ)) / X := by
        rw [le_div_iff₀ hXr]; linarith
      calc cT ≤ _ := this
        _ = ∑ e ∈ range K, ((window (PredU b) (X / 2 ^ e)).card : ℝ) / X +
            (∑ e ∈ Ico K (X + 1), ((window (PredU b) (X / 2 ^ e)).card : ℝ)) / X := by
            rw [add_div, Finset.sum_div]
        _ ≤ _ := by
            gcongr
            rw [div_le_iff₀ hXr]; exact htail
    have hgeo : ∑ e ∈ range K, dU * (1 / 2 : ℝ) ^ e ≤ 2 * dU := by
      rw [← Finset.mul_sum]
      have := geom_half_le K
      nlinarith
    linarith
  -- let `K → ∞`
  have hcT2 : cT ≤ 2 * dU := by
    have ht : Tendsto (fun K : ℕ => 2 * dU + 2 * (1 / 2 : ℝ) ^ K) atTop (𝓝 (2 * dU + 2 * 0)) :=
      tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
        (by norm_num)).const_mul 2)
    rw [mul_zero, add_zero] at ht
    exact ge_of_tendsto' ht hK
  -- conclude with `c = c_T/4`
  refine ⟨cT / 4, by positivity, ?_⟩
  have hgt : cT / 4 < dU := by linarith
  filter_upwards [(hdU.eventually (lt_mem_nhds hgt)), eventually_gt_atTop 0] with X hX hX0
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX0
  rw [lt_div_iff₀ hXr] at hX
  linarith

end CollatzCLT
