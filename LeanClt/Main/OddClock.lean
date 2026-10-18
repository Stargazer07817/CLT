import LeanClt.Main.Conditional
import LeanClt.Elementary.Syracuse

/-!
# Theorem 1.1(iii) with positivity from Theorem 8.1

`main_U` assumed positive lower density of `P_U(b)` directly. The paper instead obtains it
from Theorem 8.1 for `P_T(b)` and the fact that `P_U(b)` is the odd part of `P_T(b)`. Here we
derive it with no further analytic input:

* the odd-clock limit at frequency `0` gives the density `δ` of `P_U(b)`;
* writing `n = 2^e u` with `u` odd, doubling compatibility of `P_T(b)` for `u ≥ n₀` gives
  `#P_T(b)∩[1,X] ≤ ∑_{e<E} (#P_U(b)∩[1,X/2^e] + n₀) + X/2^E`;
* hence `c ≤ 2δ + 2^{-E}` for every `E`, so `δ ≥ c/2 > 0`.
-/

open Real Filter Topology Finset Complex

namespace CollatzCLT

/-- The density of `A` from the uniform-sampling phase limit at frequency `0`. -/
lemma density_of_uniform {A : Set ℕ} {q : ℕ → ℝ} {κ : ℝ} {m : ℂ}
    (h0 : Tendsto (fun X : ℕ => (X : ℂ)⁻¹ * ∑ n ∈ Icc 1 X, ph A q 0 (κ * Real.log n) n) atTop
      (𝓝 m)) :
    Tendsto (fun X : ℕ => ((window A X).card : ℝ) / X) atTop (𝓝 m.re) := by
  simp only [sum_ph_zero] at h0
  have hdC : Tendsto (fun X : ℕ => ((((window A X).card : ℝ) / X : ℝ) : ℂ)) atTop (𝓝 m) := by
    refine h0.congr' (Eventually.of_forall fun X => ?_)
    push_cast; ring
  have := (Complex.continuous_re.tendsto _).comp hdC
  simpa [Function.comp_def] using this

/-- **Counting bound.** Splitting `n = 2^e u` (`u` odd) for `e < E` and bounding the rest. -/
lemma card_predT_le {b n0 : ℕ} (hb : Odd b)
    (hn0 : ∀ e u : ℕ, n0 ≤ u → (2 ^ e * u ∈ Pred T b ↔ u ∈ Pred T b)) (X E : ℕ) :
    ((window (Pred T b) X).card : ℝ) ≤
      ∑ e ∈ range E, (((window (PredU b) (X / 2 ^ e)).card : ℝ) + n0) + ((X / 2 ^ E : ℕ) : ℝ) := by
  classical
  -- counting as a sum of indicators, then the two-adic split
  have hcount : (window (Pred T b) X).card =
      ∑ n ∈ Icc 1 X, (if n ∈ Pred T b then 1 else 0) := by
    unfold window; rw [card_filter]
  have hsplit := sum_Icc_two_adic_aux (fun n => if n ∈ Pred T b then 1 else 0) X E
  rw [hcount, hsplit]
  push_cast
  gcongr with e he
  · -- the layer `e`: `u < n₀` contributes at most `n₀`, the rest lies in `P_U(b)`
    have hlayer : ∀ u ∈ (Icc 1 (X / 2 ^ e)).filter Odd,
        (if 2 ^ e * u ∈ Pred T b then (1 : ℝ) else 0) ≤
          (if u < n0 then 1 else 0) + (if u ∈ PredU b then 1 else 0) := by
      intro u hu
      rw [Finset.mem_filter, Finset.mem_Icc] at hu
      by_cases hu0 : u < n0
      · split_ifs <;> norm_num
      · have hiff := hn0 e u (by omega)
        have hU : u ∈ Pred T b → u ∈ PredU b := fun h => by
          rw [predU_eq hb]; exact ⟨hu.2, h⟩
        by_cases h1 : 2 ^ e * u ∈ Pred T b
        · have h2 : u ∈ PredU b := hU (hiff.mp h1)
          simp [h1, h2, hu0]
        · simp only [h1, if_false]
          split_ifs <;> norm_num
    calc ∑ u ∈ (Icc 1 (X / 2 ^ e)).filter Odd, (if 2 ^ e * u ∈ Pred T b then (1 : ℝ) else 0)
        ≤ ∑ u ∈ (Icc 1 (X / 2 ^ e)).filter Odd,
            ((if u < n0 then (1 : ℝ) else 0) + (if u ∈ PredU b then 1 else 0)) := by
          push_cast; exact sum_le_sum hlayer
      _ = ((((Icc 1 (X / 2 ^ e)).filter Odd).filter (· < n0)).card : ℝ) +
            ((((Icc 1 (X / 2 ^ e)).filter Odd).filter (· ∈ PredU b)).card : ℝ) := by
          rw [sum_add_distrib, ← sum_filter, ← sum_filter]; simp
      _ ≤ ((window (PredU b) (X / 2 ^ e)).card : ℝ) + n0 := by
          rw [add_comm]
          gcongr
          · intro u hu
            simp only [Finset.mem_filter] at hu
            unfold window
            simp only [Finset.mem_filter]
            exact ⟨hu.1.1, hu.2⟩
          · exact (card_le_card (fun u hu => by
              simp only [Finset.mem_filter] at hu; exact Finset.mem_range.mpr hu.2)).trans
              (by simp)
  · -- the remainder: at most `X / 2^E` terms
    calc ∑ m ∈ Icc 1 (X / 2 ^ E), (if 2 ^ E * m ∈ Pred T b then (1 : ℝ) else 0)
        ≤ ∑ m ∈ Icc 1 (X / 2 ^ E), (1 : ℝ) := sum_le_sum fun m _ => by split_ifs <;> norm_num
      _ = ((X / 2 ^ E : ℕ) : ℝ) := by simp

/-- **Theorem 1.1(iii), odd clock, conditional on Lemma 6.1 (odd clock) and Theorem 8.1
for `P_T(b)`.** -/
theorem main_U' (b : ℕ) (hb : Odd b) {α : ℝ} (hα : 1 < α)
    (hadj : AdjacentScales (oddCF (PredU b) (fun n => -(hit U b n : ℝ)) κU) (VU / 2) α)
    (hposT : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (Pred T b) X).card : ℝ)) :
    (∃ d > 0, HasDensity (PredU b) d) ∧ CLTOn (PredU b) (normalised (hit U b) κU VU) := by
  obtain ⟨c0, hc0, hc⟩ := hposT
  obtain ⟨p, -, hseq0⟩ := fixed_base_limit_seq hα hadj
    (fun Y => continuousAt_oddCF (PredU b) _ κU Y)
  have hseq : SeqLimit (PredU b) (fun n => -(hit U b n : ℝ)) κU (VU / 2) p :=
    fun Y sY τ hY hτ => hseq0 atTop Y sY τ hY hτ
  have hU := fun (sX : ℕ → ℝ) (τ : ℝ) (hτ : Tendsto (fun X : ℕ => sX X * √(Real.log X)) atTop
      (𝓝 τ)) => uniform_limit_odd hseq (fun n hn => hn.2.1) hτ
  -- the density `δ` of `P_U(b)`
  have h0 := hU (fun _ => 0) 0 (by simp)
  simp only [mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul,
    zero_pow two_ne_zero] at h0
  have hδ := density_of_uniform h0
  set δ := (p / 2).re
  have hδ0 : 0 ≤ δ := ge_of_tendsto' hδ (fun X => by positivity)
  -- `#P_U(b) ∩ [1, ⌊X/2^e⌋] / X → δ / 2^e`
  have hlayer : ∀ e : ℕ, Tendsto (fun X : ℕ => ((window (PredU b) (X / 2 ^ e)).card : ℝ) / X)
      atTop (𝓝 (δ * (1 / 2 ^ e))) := by
    intro e
    have he0 : 0 < 2 ^ e := by positivity
    have := (hδ.comp (tendsto_natDiv_atTop he0)).mul (tendsto_natDiv_div_self he0)
    push_cast at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (2 ^ e)] with X hX
    have hZ : (0 : ℝ) < ((X / 2 ^ e : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_div_iff_mul_le he0).mpr (by simpa using hX)
    simp only [Function.comp]
    field_simp
  -- doubling for `P_T(b)` above some `n₀`
  obtain ⟨n0, hn0⟩ := (doubling_T b hb.pos).iterate
  -- `c ≤ 2δ + 2^{-E}` for every `E`
  have hE : ∀ E : ℕ, c0 ≤ 2 * δ + (1 / 2) ^ E := by
    intro E
    have hlim : Tendsto (fun X : ℕ => ∑ e ∈ range E,
        (((window (PredU b) (X / 2 ^ e)).card : ℝ) / X + n0 / X) + (1 / 2 : ℝ) ^ E) atTop
        (𝓝 (∑ e ∈ range E, (δ * (1 / 2 ^ e) + 0) + (1 / 2 : ℝ) ^ E)) := by
      refine (tendsto_finsetSum _ fun e _ => (hlayer e).add ?_).add tendsto_const_nhds
      simpa using (tendsto_const_nhds (x := (n0 : ℝ))).div_atTop tendsto_natCast_atTop_atTop
    have hle : c0 ≤ ∑ e ∈ range E, (δ * (1 / 2 ^ e) + 0) + (1 / 2 : ℝ) ^ E := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [hc, eventually_gt_atTop 0] with X hX hX0
      have hXpos : (0 : ℝ) < X := by exact_mod_cast hX0
      have hb := card_predT_le hb (fun e u h => (hn0 e u h).1) X E
      have hrem : ((X / 2 ^ E : ℕ) : ℝ) / X ≤ (1 / 2 : ℝ) ^ E := by
        rw [div_le_iff₀ hXpos, div_pow, one_pow, div_mul_eq_mul_div, one_mul,
          le_div_iff₀ (by positivity)]
        exact_mod_cast Nat.div_mul_le_self X (2 ^ E)
      have : c0 ≤ ((window (Pred T b) X).card : ℝ) / X := by
        rw [le_div_iff₀ hXpos]; exact hX
      calc c0 ≤ ((window (Pred T b) X).card : ℝ) / X := this
        _ ≤ (∑ e ∈ range E, (((window (PredU b) (X / 2 ^ e)).card : ℝ) + n0)
              + ((X / 2 ^ E : ℕ) : ℝ)) / X := by gcongr
        _ = ∑ e ∈ range E, (((window (PredU b) (X / 2 ^ e)).card : ℝ) / X + n0 / X)
              + ((X / 2 ^ E : ℕ) : ℝ) / X := by
            rw [add_div, sum_div]; congr 1; apply sum_congr rfl; intro e _; rw [add_div]
        _ ≤ _ := by gcongr
    have hgeom : ∑ e ∈ range E, (δ * (1 / 2 ^ e) + 0) ≤ 2 * δ := by
      simp only [add_zero, ← mul_sum]
      rw [mul_comm]
      gcongr
      have := sum_geometric_two_le E
      simpa [one_div, inv_pow] using this
    linarith
  have hδpos : 0 < δ := by
    by_contra hneg
    push Not at hneg
    have hδ' : δ = 0 := le_antisymm hneg hδ0
    obtain ⟨E, hE'⟩ := exists_pow_lt_of_lt_one hc0 (by norm_num : (1 / 2 : ℝ) < 1)
    have := hE E
    rw [hδ'] at this
    linarith
  -- positive lower density of `P_U(b)` and the conclusion
  have hposU : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (PredU b) X).card : ℝ) := by
    refine ⟨δ / 2, by positivity, ?_⟩
    filter_upwards [hδ.eventually (lt_mem_nhds (by linarith : δ / 2 < δ)),
      eventually_gt_atTop 0] with X hX hX0
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX0
    rw [lt_div_iff₀ hXpos] at hX
    exact hX.le
  have := density_clt_of_uniform (by linarith [VU_pos]) hU hposU
  rwa [stat_eq] at this

end CollatzCLT
