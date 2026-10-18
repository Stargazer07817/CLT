import LeanClt.Main.OfTao
import LeanClt.Exceptional.Defs

/-!
# Lemma 6.1 [`lem:adjacent`] with constants uniform in the set, the clock and the threshold

`adjacent_uniform` (in `Adjacent.lean`) is Lemma 6.1 with the constants quantified before the set,
the clock and the threshold. `AdjacentScales`, the statement of `adjacent_of_transport`, quantifies
them after the pair `(A, q)`; the proof never uses the pair except through the transport property
at thresholds `x ≥ x₀`:

* `δ₀ = min(0.8 δ_R, 1)` comes from the twisted renewal theorem and depends only on `ϰ`;
* the transfer constants `C_T, x_T` come from Theorem 5.10 [`thm:transfer`], whose statement already
  quantifies the target subset `E ⊆ 𝓜_x`, the clock and the frequency after them;
* the count of atypical sources comes from Lemma 5.1 [`lem:typical`], which does not involve the set;
* the threshold `x_t` of the numerical side conditions does not involve the set, except through
  `x ≥ x₀`.

`adjacent_uniform` takes `x₀ ≤ x` as a separate hypothesis and quantifies `(A, q, x₀)` after the
constants; the threshold then enters only through the range `Y ≥ max(x₁, x₀)^α`. This is the
uniformity the paper uses in the proof of Theorem 1.3 [`thm:thresholds`] ("constant uniform over
target subsets and hence over `K`") and in §7.

Stage 1 of the checkpoint-11 plan put `adjacent_uniform` here, as a copy of the proof of
`adjacent_of_transport` with those two changes. At checkpoint 15 (decision D3) it moved, unchanged,
to `Adjacent.lean`, and `adjacent_of_transport` is now derived from it, so the proof exists once.

Consumers:
* `adjacent_of_uniform`: the uniform form gives Lemma 6.1 for each set and clock; it is the same
  statement as `adjacent_of_transport` and is kept, as a citation of it;
* `density_near_base`: the chain estimate (6.7, `eq:chain`) at `s = 0` from a base `B`, with
  Proposition 6.2 [`prop:fixedbase`] (i) and Lemma 6.5 [`lem:sampling`] (i): the density exists and
  lies within `C (log B)^{-δ}` of the odd proportion at `B`, with `δ, C, x₁` independent of
  `(A, q, x₀)`. No positivity is needed (the density-only form of `density_clt_of_adjacent`);
* `AK_base`: at the base `B = K^α` the odd proportion of `A_K` is at least `1 - (log K)^{-1}`, by
  Lemmas 5.1 [`lem:typical`] and 5.2 [`lem:orbit`]. Lemma 5.3 [`lem:failure`] is not needed.

The `_of_tao` forms replace `JointMixing` by Tao's two imports (`jointMixing_of_tao`).
-/

open Real Finset Complex Filter

noncomputable section

namespace CollatzCLT

/-! ## Consumers -/

open Classical in
/-- At frequency `0` the odd characteristic function is the odd proportion of `A` at scale `Y`;
it does not depend on the clock or the centring. -/
lemma oddCF_zero (A : Set ℕ) (q : ℕ → ℝ) (κ Y : ℝ) :
    oddCF A q κ Y 0 = (((oddClosed Y).filter (· ∈ A)).card : ℂ) / (oddClosed Y).card := by
  unfold oddCF ph
  rw [div_eq_inv_mul, Finset.card_filter, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u ∈ A <;> simp [hu]

open Classical in
lemma oddCF_zero_re (A : Set ℕ) (q : ℕ → ℝ) (κ Y : ℝ) :
    (oddCF A q κ Y 0).re = (((oddClosed Y).filter (· ∈ A)).card : ℝ) / (oddClosed Y).card := by
  rw [oddCF_zero, show ((((oddClosed Y).filter (· ∈ A)).card : ℂ) / (oddClosed Y).card) =
    (((((oddClosed Y).filter (· ∈ A)).card : ℝ) / (oddClosed Y).card : ℝ) : ℂ) by push_cast; rfl,
    Complex.ofReal_re]

lemma oddCF_zero_freq (A : Set ℕ) (q : ℕ → ℝ) (κ κ' Y : ℝ) :
    oddCF A q κ Y 0 = oddCF A q κ' Y 0 := by
  rw [oddCF_zero, oddCF_zero]

/-- The uniform form gives Lemma 6.1 [`lem:adjacent`] for each set and clock with the transport
property, with `Y₀ = max(x₁, x₀)^α`. Since checkpoint 15 this is exactly how `adjacent_of_transport`
is proved, so the proof here cites it. -/
theorem adjacent_of_uniform (hJM : JointMixing) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {A : Set ℕ} {q : ℕ → ℝ} {ρ η x₀ : ℝ} (htr : Transport A q ρ η x₀) :
    AdjacentScales (oddCF A q ((2 * ρ + η) / c)) ((ρ * bet + η * ell) ^ 2 / c ^ 3) alpha :=
  adjacent_of_transport hJM hθ htr

/-- **The chain estimate (6.7, `eq:chain`) at `s = 0`, uniform form**, with Proposition 6.2
[`prop:fixedbase`] (i) and Lemma 6.5 [`lem:sampling`] (i): for a set and clock with the transport
property and doubling compatibility, the density `p` of `A` exists and is within `C (log B)^{-δ}`
of the odd proportion of `A` at any base `B ≥ max(x₁, x₀)^α`, with `δ, C, x₁` independent of `A`,
`q` and `x₀`. No positivity hypothesis: this is the density-only form of
`density_clt_of_adjacent`. -/
theorem density_near_base (hJM : JointMixing) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (ρ η : ℝ) :
    ∃ δ C x₁ : ℝ, 0 < δ ∧ 0 ≤ C ∧ 1 < x₁ ∧
      ∀ (A : Set ℕ) (q : ℕ → ℝ) (x₀ e0 : ℝ), Transport A q ρ η x₀ → DoublingCompatible A q e0 →
        ∃ p : ℝ, HasDensity A p ∧ ∀ B : ℝ, (max x₁ x₀) ^ alpha ≤ B →
          |p - (oddCF A q 0 B 0).re| ≤ C * (Real.log B) ^ (-δ) := by
  obtain ⟨δ, hδ, hU⟩ := adjacent_uniform hJM hθ ρ η
  obtain ⟨C, x₁, hC, hx₁, h1⟩ := hU 1 one_pos
  have hα : (1 : ℝ) < alpha := alpha_gt_one
  have hr1 : alpha ^ (-δ) < 1 := rpow_lt_one_of_one_lt_of_neg hα (by linarith)
  refine ⟨δ, C / (1 - alpha ^ (-δ)), x₁, hδ, div_nonneg hC (by linarith), hx₁, ?_⟩
  intro A q x₀ e0 htr hdbl
  set κ := (2 * ρ + η) / c with hκ
  set D := (ρ * bet + η * ell) ^ 2 / c ^ 3 with hD
  obtain ⟨p, hp, hseq⟩ := fixed_base_limit_seq hα (adjacent_of_uniform hJM hθ htr)
    (fun Y => continuousAt_oddCF A q κ Y)
  -- Lemma 6.5(i) at `s = 0`: the density is `Re p`
  have hu := uniform_limit (A := A) (q := q) (κ := κ) (D := D) (p := p)
    (fun Y sY τ hY hτ => hseq atTop Y sY τ hY hτ) hdbl (sX := fun _ => 0) (τ := 0) (by simp)
  simp only [sum_ph_zero, zero_pow two_ne_zero, mul_zero, neg_zero, Real.exp_zero,
    Complex.ofReal_one, one_mul] at hu
  refine ⟨p.re, ?_, fun B hB => ?_⟩
  · have hre := (Complex.continuous_re.tendsto _).comp hu
    refine hre.congr fun X => ?_
    simp only [Function.comp_apply]
    rw [show ((X : ℂ)⁻¹ * ((window A X).card : ℂ)) = ((((window A X).card : ℝ) / X : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  · -- the chain from the base `B`, then `Y → ∞`
    have hY0 : 1 < (max x₁ x₀) ^ alpha :=
      Real.one_lt_rpow (lt_of_lt_of_le hx₁ (le_max_left _ _)) (by linarith)
    have hch : ∀ Y, B ≤ Y → ‖oddCF A q κ Y 0 - oddCF A q κ B 0‖ ≤
        C / (1 - alpha ^ (-δ)) * (Real.log B) ^ (-δ) := by
      intro Y hBY
      have := chain_Y hα hδ hC hY0 (h1 A q x₀ htr) hB hBY (s := 0) (by simp)
      simpa [renorm] using this
    have hlim : ‖p - oddCF A q κ B 0‖ ≤ C / (1 - alpha ^ (-δ)) * (Real.log B) ^ (-δ) :=
      le_of_tendsto (hp.sub_const _).norm (eventually_atTop.mpr ⟨B, hch⟩)
    rw [oddCF_zero_freq A q 0 κ B]
    calc |p.re - (oddCF A q κ B 0).re| = |(p - oddCF A q κ B 0).re| := by rw [Complex.sub_re]
      _ ≤ ‖p - oddCF A q κ B 0‖ := Complex.abs_re_le_norm _
      _ ≤ _ := hlim

open Classical in
/-- **The base of Theorem 1.3(i).** At `B = K^α` the odd proportion of `A_K` is at least
`1 - (log K)^{-1}`, for all large `K`. Every source `N ∈ [K^α, 2K^α]` with typical valuations
(Lemma 5.1 [`lem:typical`]) crosses below `K` (Lemma 5.2 [`lem:orbit`]), and the crossing point
`U^r(N) = T^k(N)` puts `N` in `A_K`. The paper uses Lemma 5.3 [`lem:failure`] here; its power
saving is not needed. -/
theorem AK_base (q : ℕ → ℝ) (κ : ℝ) : ∀ᶠ K : ℕ in atTop,
    1 - (Real.log K) ^ (-(1 : ℝ)) ≤ (oddCF (AK K) q κ ((K : ℝ) ^ alpha) 0).re := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (large_ev.and (typical 1))]
    with K hK
  obtain ⟨hL, htyp⟩ := hK
  set x : ℝ := (K : ℝ) with hxdef
  set Y : ℝ := x ^ alpha with hYdef
  have hY1 : x ^ alpha ≤ Y := le_rfl
  have hx1 : 1 < x := hL.x_gt
  have hY2 : Y ≤ x ^ (alpha ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by unfold alpha; norm_num)
  obtain ⟨hx0, h2e5, hxY, hY0⟩ := large_facts hL hY1
  -- every typical source enters `[1, K]`
  have hgood : ∀ N ∈ oddClosed Y, Good x N → N ∈ AK K := by
    intro N hN hG
    obtain ⟨hNo, -, -⟩ := mem_oddClosed hY0.le hN
    obtain ⟨⟨r, hr⟩, -⟩ := orbit_window hL hY1 hY2 hN hG
    obtain ⟨m, hm⟩ := exists_T_iterate_eq_U_iterate hNo r
    refine ⟨hNo.pos, m, ?_⟩
    rw [hm]
    have hr' : ((U^[r] N : ℕ) : ℝ) ≤ (K : ℝ) := hr
    exact_mod_cast hr'
  have hLYpos : (0 : ℝ) < LY Y := LY_pos (by linarith)
  -- the part of the window outside `A_K` consists of atypical sources
  have hsub : (oddClosed Y).filter (· ∉ AK K) ⊆ (oddClosed Y).filter (fun N => ¬ Good x N) := by
    intro N hN
    rw [Finset.mem_filter] at hN ⊢
    exact ⟨hN.1, fun hG => hN.2 (hgood N hN.1 hG)⟩
  have hle : (((oddClosed Y).filter (· ∉ AK K)).card : ℝ) ≤
      ((oddClosed Y).filter (fun N => ¬ Good x N)).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hout : (((oddClosed Y).filter (· ∉ AK K)).card : ℝ) ≤ Real.log K ^ (-(1 : ℝ)) * LY Y :=
    hle.trans (htyp Y hY1)
  have hsplit : (((oddClosed Y).filter (· ∈ AK K)).card : ℝ) +
      ((oddClosed Y).filter (· ∉ AK K)).card = LY Y := by
    exact_mod_cast Finset.card_filter_add_card_filter_not _
  rw [oddCF_zero_re, show ((oddClosed Y).card : ℝ) = LY Y from rfl, le_div_iff₀ hLYpos]
  linarith

/-! ## From Tao's imports -/

open Classical in
/-- **Lemma 6.1 [`lem:adjacent`], uniform form**, from Tao's imports and Rhin's measure. -/
theorem adjacent_uniform_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ}
    (hθ : IrrMeasure d ϰ) (ρ η : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M0 : ℝ, 0 < M0 → ∃ C x₁ : ℝ, 0 ≤ C ∧ 1 < x₁ ∧
      ∀ (A : Set ℕ) (q : ℕ → ℝ) (x₀ : ℝ), Transport A q ρ η x₀ →
      ∀ Y Y' s : ℝ, (max x₁ x₀) ^ alpha ≤ Y → Y ≤ Y' → Y' ≤ Y ^ alpha →
        |s| * √(Real.log Y') ≤ M0 →
        ‖renorm (oddCF A q ((2 * ρ + η) / c)) ((ρ * bet + η * ell) ^ 2 / c ^ 3) Y s -
          renorm (oddCF A q ((2 * ρ + η) / c)) ((ρ * bet + η * ell) ^ 2 / c ^ 3) Y' s‖ ≤
          C * (Real.log Y) ^ (-δ) :=
  adjacent_uniform (jointMixing_of_tao hTM hTP) hθ ρ η

/-- `density_near_base` from Tao's imports and Rhin's measure. -/
theorem density_near_base_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ}
    (hθ : IrrMeasure d ϰ) (ρ η : ℝ) :
    ∃ δ C x₁ : ℝ, 0 < δ ∧ 0 ≤ C ∧ 1 < x₁ ∧
      ∀ (A : Set ℕ) (q : ℕ → ℝ) (x₀ e0 : ℝ), Transport A q ρ η x₀ → DoublingCompatible A q e0 →
        ∃ p : ℝ, HasDensity A p ∧ ∀ B : ℝ, (max x₁ x₀) ^ alpha ≤ B →
          |p - (oddCF A q 0 B 0).re| ≤ C * (Real.log B) ^ (-δ) :=
  density_near_base (jointMixing_of_tao hTM hTP) hθ ρ η

end CollatzCLT
