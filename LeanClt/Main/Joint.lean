import LeanClt.Main.Variants

/-!
# Theorem 1.1(iv) [`thm:main`]: the joint law of the three clocks

For odd `b` with `3 ∤ b` and `N_X` uniform on `P_U(b) ∩ [1, X]`,
`((τ_U, τ_F, τ_T)(N_X) - (κ_U, κ_F, κ_T) log N_X) / √(log X) ⇒ √(2/c³) (ℓ, β, β + ℓ) Z`,
and the same under the variants of the closing sentence of Theorem 1.1.

The proof follows the paper's (Cramér–Wold through the general reward). For real
`t = (t₁, t₂, t₃)` the clock `q_t = -(t₁ τ_U + t₂ τ_F + t₃ τ_T)` on `P_U(b)` has the transport
property with reward `(ρ, η) = (t₂ + t₃, t₁ + t₃)` (`transport_joint`): `τ_U`, `τ_F`, `τ_T` have the
rewards `(0, 1)`, `(1, 0)`, `(1, 1)`, and `P_U(b) ⊆ P_F(b) ∩ P_T(b)`. Lemma 6.1, Proposition 6.2 and
odd dyadic sampling then give the characteristic function of `⟨t, S⟩` for every `t`, with
`κ_t = t₁ κ_U + t₂ κ_F + t₃ κ_T` and `D_t = (t₁ ℓ + t₂ β + t₃ (β + ℓ))² / c³ = ⟨t, a⟩² / 2`. The
degenerate directions `D_t = 0` are covered: nothing in Lemma 6.1 or Proposition 6.2 needs `D > 0`.
Lévy's continuity theorem in `ℝ³` (`jointLaw_of_charFun`) converts this into the joint distribution
function, every orthant having a null boundary for the rank-one limit.

Unlike the paper's proof, the third coordinate is not obtained from `τ_T = τ_F + τ_U`: the three
clocks are carried separately, which needs only the transport property of each.
-/

open Real Filter Topology Finset Complex MeasureTheory ProbabilityTheory

noncomputable section

namespace CollatzCLT

/-! ## The rank-one Gaussian law in `ℝ³` -/

/-- `(x₁, x₂, x₃)` as a point of Euclidean `ℝ³`. -/
abbrev vec3 (x₁ x₂ x₃ : ℝ) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![x₁, x₂, x₃]

lemma inner_vec3 (a b c x y z : ℝ) :
    inner ℝ (vec3 a b c) (vec3 x y z) = a * x + b * y + c * z := by
  simp [vec3, PiLp.inner_apply, Fin.sum_univ_three]
  ring

lemma vec3_ofLp (t : EuclideanSpace ℝ (Fin 3)) : t = vec3 (t.ofLp 0) (t.ofLp 1) (t.ofLp 2) := by
  ext i
  fin_cases i <;> rfl

/-- The law of `Z a`, `Z ~ N(0,1)`, for `a ∈ ℝ³`. -/
def rankOneLaw (a : EuclideanSpace ℝ (Fin 3)) : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)) :=
  ⟨(gaussianReal 0 1).map (fun w : ℝ => w • a), inferInstance⟩

lemma charFun_rankOneLaw (a t : EuclideanSpace ℝ (Fin 3)) :
    charFun ((rankOneLaw a : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
      Measure (EuclideanSpace ℝ (Fin 3))) t =
      cexp (-(((inner ℝ a t : ℝ) : ℂ) ^ 2 / 2)) := by
  simp only [rankOneLaw, ProbabilityMeasure.coe_mk]
  rw [charFun_apply, integral_map (by fun_prop)
    (Continuous.aestronglyMeasurable (by fun_prop))]
  have h : ∀ w : ℝ, cexp (((inner ℝ (w • a) t : ℝ) : ℂ) * I) =
      cexp (((inner ℝ a t : ℝ) : ℂ) * (w : ℂ) * I) := by
    intro w
    rw [real_inner_smul_left]
    push_cast
    ring_nf
  simp_rw [h]
  rw [← charFun_apply_real, charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-- The closed orthant `{x : x₁ ≤ z₁, x₂ ≤ z₂, x₃ ≤ z₃}`. -/
def orthant3 (z₁ z₂ z₃ : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | x.ofLp 0 ≤ z₁ ∧ x.ofLp 1 ≤ z₂ ∧ x.ofLp 2 ≤ z₃}

lemma isClosed_orthant3 (z₁ z₂ z₃ : ℝ) : IsClosed (orthant3 z₁ z₂ z₃) := by
  unfold orthant3
  simp only [Set.ofPred_and]
  exact (isClosed_le (by fun_prop) continuous_const).inter
    ((isClosed_le (by fun_prop) continuous_const).inter (isClosed_le (by fun_prop) continuous_const))

lemma frontier_orthant3_subset (z₁ z₂ z₃ : ℝ) :
    frontier (orthant3 z₁ z₂ z₃) ⊆
      {x | x.ofLp 0 = z₁} ∪ {x | x.ofLp 1 = z₂} ∪ {x | x.ofLp 2 = z₃} := by
  rw [(isClosed_orthant3 z₁ z₂ z₃).frontier_eq]
  rintro x ⟨⟨h1, h2, h3⟩, hx⟩
  have hU : IsOpen {y : EuclideanSpace ℝ (Fin 3) | y.ofLp 0 < z₁ ∧ y.ofLp 1 < z₂ ∧ y.ofLp 2 < z₃} := by
    simp only [Set.ofPred_and]
    exact (isOpen_lt (by fun_prop) continuous_const).inter
      ((isOpen_lt (by fun_prop) continuous_const).inter (isOpen_lt (by fun_prop) continuous_const))
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hc
  apply hx
  exact interior_maximal (by intro y hy; exact ⟨hy.1.le, hy.2.1.le, hy.2.2.le⟩) hU
    ⟨lt_of_le_of_ne h1 hc.1.1, lt_of_le_of_ne h2 hc.1.2, lt_of_le_of_ne h3 hc.2⟩

lemma rankOneLaw_coord_null (a : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) (ha : a.ofLp i ≠ 0)
    (z : ℝ) : ((rankOneLaw a : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
      Measure (EuclideanSpace ℝ (Fin 3))) {x | x.ofLp i = z} = 0 := by
  simp only [rankOneLaw, ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply (by fun_prop) (isClosed_eq (by fun_prop) continuous_const).measurableSet]
  have h : (fun w : ℝ => w • a) ⁻¹' {x | x.ofLp i = z} = {z / a.ofLp i} := by
    ext w
    simp [eq_div_iff ha]
  rw [h]
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  exact measure_singleton _

/-- **Lévy step in `ℝ³` for a rank-one Gaussian limit.** If along the finite samples `W k`, for
every `t ∈ ℝ³`, the empirical characteristic function of `t₁ S₁ + t₂ S₂ + t₃ S₃` tends to
`e^{-(t₁ a₁ + t₂ a₂ + t₃ a₃)²/2}`, and every `a_k ≠ 0`, then `(S₁, S₂, S₃) ⇒ (a₁, a₂, a₃) Z`. -/
theorem jointLaw_of_charFun {W : ℕ → Finset ℕ} {S₁ S₂ S₃ : ℕ → ℕ → ℝ} {a₁ a₂ a₃ : ℝ}
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0) (hne : ∀ᶠ k in atTop, (W k).Nonempty)
    (hcf : ∀ t₁ t₂ t₃ : ℝ, Tendsto (fun k => ((W k).card : ℂ)⁻¹ *
      ∑ n ∈ W k, cexp (((t₁ * S₁ k n + t₂ * S₂ k n + t₃ * S₃ k n : ℝ) : ℂ) * I)) atTop
      (𝓝 (cexp (-(((t₁ * a₁ + t₂ * a₂ + t₃ * a₃ : ℝ) : ℂ) ^ 2 / 2))))) :
    JointLaw atTop W S₁ S₂ S₃ a₁ a₂ a₃ := by
  classical
  intro z₁ z₂ z₃
  set a := vec3 a₁ a₂ a₃ with ha
  set μ₀ := rankOneLaw a with hμ₀
  have hcf' : ∀ t : EuclideanSpace ℝ (Fin 3), Tendsto (fun k => ((W k).card : ℂ)⁻¹ *
      ∑ n ∈ W k, cexp (inner ℝ (vec3 (S₁ k n) (S₂ k n) (S₃ k n)) t * I)) atTop
      (𝓝 (charFun (μ₀ : Measure _) t)) := by
    intro t
    rw [hμ₀, charFun_rankOneLaw, vec3_ofLp t, ha, inner_vec3]
    have h := hcf (t.ofLp 0) (t.ofLp 1) (t.ofLp 2)
    rw [show t.ofLp 0 * a₁ + t.ofLp 1 * a₂ + t.ofLp 2 * a₃ =
      a₁ * t.ofLp 0 + a₂ * t.ofLp 1 + a₃ * t.ofLp 2 by ring] at h
    refine h.congr' (Eventually.of_forall fun k => ?_)
    · congr 2
      funext n
      rw [inner_vec3]
      congr 2
      push_cast
      ring
  have hnull : (μ₀ : Measure _) (frontier (orthant3 z₁ z₂ z₃)) = 0 := by
    refine measure_mono_null (frontier_orthant3_subset z₁ z₂ z₃) ?_
    refine measure_union_null (measure_union_null ?_ ?_) ?_
    · exact rankOneLaw_coord_null a 0 (by simpa [ha] using ha₁) z₁
    · exact rankOneLaw_coord_null a 1 (by simpa [ha] using ha₂) z₂
    · exact rankOneLaw_coord_null a 2 (by simpa [ha] using ha₃) z₃
  have h := tendsto_propn_of_charFun μ₀ hne hcf' (isClosed_orthant3 z₁ z₂ z₃).measurableSet hnull
  have hval : (μ₀ : Measure _).real (orthant3 z₁ z₂ z₃) =
      (gaussianReal 0 1).real {w : ℝ | a₁ * w ≤ z₁ ∧ a₂ * w ≤ z₂ ∧ a₃ * w ≤ z₃} := by
    rw [hμ₀]
    simp only [rankOneLaw, ProbabilityMeasure.coe_mk]
    rw [map_measureReal_apply (by fun_prop) (isClosed_orthant3 z₁ z₂ z₃).measurableSet]
    congr 1
    ext w
    simp [orthant3, ha, mul_comm]
  rw [hval] at h
  refine h.congr fun k => ?_
  congr 3
  exact filter_congr fun n _ => by simp [orthant3]

/-- `JointLaw` along the real `X → ∞` from `JointLaw` along every real sequence `Y_k → ∞`. -/
lemma jointLaw_real_of_seq {W : ℝ → Finset ℕ} {S₁ S₂ S₃ : ℝ → ℕ → ℝ} {a₁ a₂ a₃ : ℝ}
    (h : ∀ Y : ℕ → ℝ, Tendsto Y atTop atTop → JointLaw atTop (fun k => W (Y k))
      (fun k => S₁ (Y k)) (fun k => S₂ (Y k)) (fun k => S₃ (Y k)) a₁ a₂ a₃) :
    JointLaw atTop W S₁ S₂ S₃ a₁ a₂ a₃ := by
  intro z₁ z₂ z₃
  rw [tendsto_iff_seq_tendsto]
  intro Y hY
  exact h Y hY z₁ z₂ z₃

/-- Empirical characteristic functions are unchanged by a perturbation of the phase that is small
in probability. -/
lemma avg_cexp_of_close {W : ℕ → Finset ℕ} {θ θ' : ℕ → ℕ → ℝ} {L : ℂ}
    (h : Tendsto (fun k => ((W k).card : ℂ)⁻¹ * ∑ n ∈ W k, cexp ((θ k n : ℂ) * I)) atTop (𝓝 L))
    (hclose : ∀ ε > 0, Tendsto (fun k => propn (W k) (fun n => ε < |θ' k n - θ k n|)) atTop
      (𝓝 0)) :
    Tendsto (fun k => ((W k).card : ℂ)⁻¹ * ∑ n ∈ W k, cexp ((θ' k n : ℂ) * I)) atTop (𝓝 L) := by
  classical
  suffices hd : Tendsto (fun k => ((W k).card : ℂ)⁻¹ * ∑ n ∈ W k, cexp ((θ' k n : ℂ) * I) -
      ((W k).card : ℂ)⁻¹ * ∑ n ∈ W k, cexp ((θ k n : ℂ) * I)) atTop (𝓝 0) by
    simpa using hd.add h
  have key : ∀ (ε : ℝ), 0 < ε → ∀ k, ‖((W k).card : ℂ)⁻¹ * ∑ n ∈ W k, cexp ((θ' k n : ℂ) * I) -
      ((W k).card : ℂ)⁻¹ * ∑ n ∈ W k, cexp ((θ k n : ℂ) * I)‖ ≤
        ε + 2 * propn (W k) (fun n => ε < |θ' k n - θ k n|) := by
    intro ε hε k
    rw [← mul_sub, ← sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos (W k).card with h0 | h0
    · rw [h0, Nat.cast_zero, inv_zero, zero_mul]
      have := propn_nonneg (W k) (fun n => ε < |θ' k n - θ k n|)
      linarith
    have hW : (0 : ℝ) < (W k).card := by exact_mod_cast h0
    have hterm : ∀ n ∈ W k, ‖cexp ((θ' k n : ℂ) * I) - cexp ((θ k n : ℂ) * I)‖ ≤
        ε + 2 * (if ε < |θ' k n - θ k n| then (1 : ℝ) else 0) := by
      intro n _
      split_ifs with hc
      · calc _ ≤ ‖cexp ((θ' k n : ℂ) * I)‖ + ‖cexp ((θ k n : ℂ) * I)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]; norm_num
          _ ≤ _ := by linarith
      · push Not at hc
        exact (norm_cexp_sub_cexp_le _ _).trans (by linarith)
    calc ((W k).card : ℝ)⁻¹ * ‖∑ n ∈ W k, (cexp ((θ' k n : ℂ) * I) - cexp ((θ k n : ℂ) * I))‖
        ≤ ((W k).card : ℝ)⁻¹ * ∑ n ∈ W k, (ε + 2 * (if ε < |θ' k n - θ k n| then (1 : ℝ) else 0)) := by
          gcongr
          exact (norm_sum_le _ _).trans (sum_le_sum hterm)
      _ = ε + 2 * propn (W k) (fun n => ε < |θ' k n - θ k n|) := by
          rw [sum_add_distrib, ← mul_sum, sum_boole, sum_const, nsmul_eq_mul]
          unfold propn
          field_simp
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hclose (ε / 3) (by positivity)) (ε / 3)
    (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hN k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (propn_nonneg _ _)] at h1
  rw [dist_zero_right]
  have := key (ε / 3) (by positivity) k
  linarith

/-! ## The transport property of the combined clocks -/

lemma Transport.restrict {A B : Set ℕ} {q q' : ℕ → ℝ} {ρ η ρ' η' x₀ : ℝ}
    (hA : Transport A q' ρ' η' x₀) (hB : Transport B q ρ η x₀) (hAB : A ⊆ B) :
    Transport A q ρ η x₀ := by
  intro x hx hm N hN hc hmT hM
  exact ⟨(hA x hx hm N hN hc hmT hM).1, fun hNA => (hB x hx hm N hN hc hmT hM).2 (hAB hNA)⟩

lemma Transport.lin3 {A : Set ℕ} {q₁ q₂ q₃ : ℕ → ℝ} {ρ₁ η₁ ρ₂ η₂ ρ₃ η₃ x₀ : ℝ}
    (h₁ : Transport A q₁ ρ₁ η₁ x₀) (h₂ : Transport A q₂ ρ₂ η₂ x₀) (h₃ : Transport A q₃ ρ₃ η₃ x₀)
    (t₁ t₂ t₃ : ℝ) :
    Transport A (fun n => t₁ * q₁ n + t₂ * q₂ n + t₃ * q₃ n) (t₁ * ρ₁ + t₂ * ρ₂ + t₃ * ρ₃)
      (t₁ * η₁ + t₂ * η₂ + t₃ * η₃) x₀ := by
  intro x hx hm N hN hc hmT hM
  obtain ⟨hi, e1⟩ := h₁ x hx hm N hN hc hmT hM
  obtain ⟨-, e2⟩ := h₂ x hx hm N hN hc hmT hM
  obtain ⟨-, e3⟩ := h₃ x hx hm N hN hc hmT hM
  refine ⟨hi, fun hNA => ?_⟩
  dsimp only
  rw [e1 hNA, e2 hNA, e3 hNA]
  ring

lemma predU_subset_predF (b : ℕ) : PredU b ⊆ Pred F b := by
  rintro n ⟨h0, hodd, k, hk⟩
  exact ⟨h0, wsum (vword n) k, (F_blocks hodd k).1.trans hk⟩

lemma predU_subset_predT (b : ℕ) : PredU b ⊆ Pred T b := by
  rintro n ⟨h0, hodd, k, hk⟩
  exact ⟨h0, wsum (vword n) k + k, (T_blocks hodd k).1.trans hk⟩

/-- **The combined clock `-(t₁ τ_U + t₂ τ_F + t₃ τ_T)` on `P_U(b)` has the transport property
with reward `(t₂ + t₃, t₁ + t₃)`.** -/
theorem transport_joint (b : ℕ) (t₁ t₂ t₃ : ℝ) :
    Transport (PredU b) (fun n => -(t₁ * hit U b n + t₂ * hit F b n + t₃ * hit T b n))
      (t₂ + t₃) (t₁ + t₃) (b + 1) := by
  have hF := (transport_U b).restrict (transport_F b) (predU_subset_predF b)
  have hT := (transport_U b).restrict (transport_T b) (predU_subset_predT b)
  have h := Transport.lin3 (transport_U b) hF hT t₁ t₂ t₃
  convert h using 1
  · funext n; ring
  · ring
  · ring

/-- Proposition 6.2 [`prop:fixedbase`] for the combined clock, in sequential form, with the odd
dyadic limit `2 dens P_U(b)`. -/
theorem seqLimit_joint (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) {dU : ℝ} (hdU : HasDensity (PredU b) dU) (t₁ t₂ t₃ : ℝ) :
    SeqLimit (PredU b) (fun n => -(t₁ * hit U b n + t₂ * hit F b n + t₃ * hit T b n))
      (t₁ * κU + t₂ * κF + t₃ * κT)
      ((t₁ * Real.log 2 + t₂ * Real.log 3 + t₃ * (Real.log 3 + Real.log 2)) ^ 2 / c ^ 3)
      ((2 * dU : ℝ) : ℂ) := by
  have h := adjacent_of_tao hTM hTP hθ (transport_joint b t₁ t₂ t₃)
  have e1 : (2 * (t₂ + t₃) + (t₁ + t₃)) / c = t₁ * κU + t₂ * κF + t₃ * κT := by
    unfold κU κF κT; ring
  have e2 : ((t₂ + t₃) * bet + (t₁ + t₃) * ell) ^ 2 / c ^ 3 =
      (t₁ * Real.log 2 + t₂ * Real.log 3 + t₃ * (Real.log 3 + Real.log 2)) ^ 2 / c ^ 3 := by
    unfold bet ell; ring
  rw [e1, e2] at h
  exact seqLimit_of_density_odd alpha_gt_one h (fun n hn => hn.2.1) hdU

/-! ## Assembly -/

/-- The combined clock, its centring constant and its variance constant. -/
abbrev qJ (b : ℕ) (t₁ t₂ t₃ : ℝ) : ℕ → ℝ :=
  fun n => -(t₁ * hit U b n + t₂ * hit F b n + t₃ * hit T b n)
abbrev κJ (t₁ t₂ t₃ : ℝ) : ℝ := t₁ * κU + t₂ * κF + t₃ * κT
abbrev DJ (t₁ t₂ t₃ : ℝ) : ℝ :=
  (t₁ * Real.log 2 + t₂ * Real.log 3 + t₃ * (Real.log 3 + Real.log 2)) ^ 2 / c ^ 3

lemma joint_coeffs_ne : √(2 / c ^ 3) * Real.log 2 ≠ 0 ∧ √(2 / c ^ 3) * Real.log 3 ≠ 0 ∧
    √(2 / c ^ 3) * (Real.log 3 + Real.log 2) ≠ 0 := by
  have hc := c_pos
  have hs : 0 < √(2 / c ^ 3) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_⟩ <;> positivity

/-- `e^{-D_t} = e^{-⟨t, a⟩²/2}` for `a = √(2/c³) (ℓ, β, β + ℓ)`. -/
lemma exp_joint (t₁ t₂ t₃ : ℝ) :
    ((Real.exp (-(DJ t₁ t₂ t₃ * (-1) ^ 2)) : ℝ) : ℂ) =
      cexp (-(((t₁ * (√(2 / c ^ 3) * Real.log 2) + t₂ * (√(2 / c ^ 3) * Real.log 3) +
        t₃ * (√(2 / c ^ 3) * (Real.log 3 + Real.log 2)) : ℝ) : ℂ) ^ 2 / 2)) := by
  have hc := c_pos
  have hx : DJ t₁ t₂ t₃ * (-1) ^ 2 = (t₁ * (√(2 / c ^ 3) * Real.log 2) +
      t₂ * (√(2 / c ^ 3) * Real.log 3) + t₃ * (√(2 / c ^ 3) * (Real.log 3 + Real.log 2))) ^ 2 / 2 := by
    have hsq : (√(2 / c ^ 3)) ^ 2 = 2 / c ^ 3 := Real.sq_sqrt (by positivity)
    have : (t₁ * (√(2 / c ^ 3) * Real.log 2) + t₂ * (√(2 / c ^ 3) * Real.log 3) +
        t₃ * (√(2 / c ^ 3) * (Real.log 3 + Real.log 2))) ^ 2 = (√(2 / c ^ 3)) ^ 2 *
        (t₁ * Real.log 2 + t₂ * Real.log 3 + t₃ * (Real.log 3 + Real.log 2)) ^ 2 := by ring
    rw [this, hsq, DJ]
    field_simp
  rw [hx, Complex.ofReal_exp]
  push_cast
  ring_nf

/-- The phase of the combined clock is `⟨t, S⟩`. -/
lemma phase_joint (t₁ t₂ t₃ τ₁ τ₂ τ₃ C L : ℝ) (hL : 0 < L) :
    (-1 / √L) * (-(t₁ * τ₁ + t₂ * τ₂ + t₃ * τ₃) + (t₁ * κU + t₂ * κF + t₃ * κT) * C) =
      t₁ * ((τ₁ - κU * C) / √L) + t₂ * ((τ₂ - κF * C) / √L) + t₃ * ((τ₃ - κT * C) / √L) := by
  have := Real.sqrt_pos.mpr hL
  field_simp
  ring

/-- **The joint law from conditional characteristic functions of the combined clocks.** -/
theorem jointLaw_of_cond {W : ℕ → Finset ℕ} {Lg : ℕ → ℝ} {C : ℕ → ℕ → ℝ} (b : ℕ)
    (hLg : ∀ᶠ k in atTop, 0 < Lg k)
    (hcond : ∀ t₁ t₂ t₃ : ℝ, (∀ᶠ k in atTop, (W k).Nonempty) ∧
      Tendsto (fun k => ((W k).card : ℂ)⁻¹ * ∑ n ∈ W k,
        cexp ((((-1 / √(Lg k)) * (qJ b t₁ t₂ t₃ n + κJ t₁ t₂ t₃ * C k n) : ℝ) : ℂ) * I)) atTop
        (𝓝 ((Real.exp (-(DJ t₁ t₂ t₃ * (-1) ^ 2)) : ℝ) : ℂ))) :
    JointLaw atTop W (fun k n => ((hit U b n : ℝ) - κU * C k n) / √(Lg k))
      (fun k n => ((hit F b n : ℝ) - κF * C k n) / √(Lg k))
      (fun k n => ((hit T b n : ℝ) - κT * C k n) / √(Lg k))
      (√(2 / c ^ 3) * Real.log 2) (√(2 / c ^ 3) * Real.log 3)
      (√(2 / c ^ 3) * (Real.log 3 + Real.log 2)) := by
  obtain ⟨h1, h2, h3⟩ := joint_coeffs_ne
  refine jointLaw_of_charFun h1 h2 h3 (hcond 0 0 0).1 fun t₁ t₂ t₃ => ?_
  have h := (hcond t₁ t₂ t₃).2
  rw [exp_joint] at h
  refine h.congr' ?_
  filter_upwards [hLg] with k hk
  congr 2
  funext n
  congr 3
  exact phase_joint t₁ t₂ t₃ _ _ _ _ _ hk

/-! ## The four samplings -/

variable {b : ℕ} {dU : ℝ}

lemma hτ_neg_one {Y : ℕ → ℝ} (hY : Tendsto Y atTop atTop) :
    Tendsto (fun k => (-1 / √(Real.log (Y k))) * √(Real.log (Y k))) atTop (𝓝 (-1)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hY.eventually (eventually_gt_atTop 1)] with k hk
  have := Real.sqrt_pos.mpr (Real.log_pos hk)
  field_simp

/-- `[1, X]`, centring at the sampled point: the conditional characteristic functions. -/
theorem cond_window (hdU0 : 0 < dU)
    (hseq : ∀ t₁ t₂ t₃ : ℝ,
      SeqLimit (PredU b) (qJ b t₁ t₂ t₃) (κJ t₁ t₂ t₃) (DJ t₁ t₂ t₃) ((2 * dU : ℝ) : ℂ))
    (t₁ t₂ t₃ : ℝ) :
    (∀ᶠ X in atTop, (window (PredU b) X).Nonempty) ∧
    Tendsto (fun X : ℕ => ((window (PredU b) X).card : ℂ)⁻¹ * ∑ n ∈ window (PredU b) X,
        cexp ((((-1 / √(Real.log X)) * (qJ b t₁ t₂ t₃ n + κJ t₁ t₂ t₃ * Real.log n) : ℝ) : ℂ) *
          I)) atTop (𝓝 ((Real.exp (-(DJ t₁ t₂ t₃ * (-1) ^ 2)) : ℝ) : ℂ)) := by
  have hτ := hτ_neg_one (Y := fun X : ℕ => (X : ℝ)) tendsto_natCast_atTop_atTop
  have h := uniform_limit_odd (hseq t₁ t₂ t₃) (fun n hn => hn.2.1) hτ
  have h0 := uniform_limit_odd (hseq t₁ t₂ t₃) (fun n hn => hn.2.1) (sX := fun _ => 0) (τ := 0)
    (by simp)
  have e : ((2 * dU : ℝ) : ℂ) / 2 = (dU : ℂ) := by push_cast; ring
  rw [e] at h h0
  simp only [zero_pow two_ne_zero, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one,
    one_mul] at h0
  exact cond_charFun_limit (J := fun X => Icc 1 X) (N := fun X => (X : ℂ))
    (c := fun _ n => κJ t₁ t₂ t₃ * Real.log n) (s := fun X => -1 / √(Real.log X))
    (by exact_mod_cast hdU0.ne') h h0

/-- **Theorem 1.1(iv)**, from the odd dyadic limits of the combined clocks. -/
theorem jointLaw_window (hdU0 : 0 < dU)
    (hseq : ∀ t₁ t₂ t₃ : ℝ,
      SeqLimit (PredU b) (qJ b t₁ t₂ t₃) (κJ t₁ t₂ t₃) (DJ t₁ t₂ t₃) ((2 * dU : ℝ) : ℂ)) :
    JointLaw atTop (window (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * Real.log n) / √(Real.log X))
      (fun X n => ((hit F b n : ℝ) - κF * Real.log n) / √(Real.log X))
      (fun X n => ((hit T b n : ℝ) - κT * Real.log n) / √(Real.log X))
      (√(2 / c ^ 3) * Real.log 2) (√(2 / c ^ 3) * Real.log 3)
      (√(2 / c ^ 3) * (Real.log 3 + Real.log 2)) := by
  refine jointLaw_of_cond (W := window (PredU b)) (Lg := fun X : ℕ => Real.log X)
    (C := fun _ n => Real.log n) b ?_ (cond_window hdU0 hseq)
  filter_upwards [eventually_gt_atTop 1] with X hX
  exact Real.log_pos (by exact_mod_cast hX)

/-- `[1, X]`, centring at `log X`. -/
theorem jointLaw_window_logX (hdU : HasDensity (PredU b) dU) (hdU0 : 0 < dU)
    (hseq : ∀ t₁ t₂ t₃ : ℝ,
      SeqLimit (PredU b) (qJ b t₁ t₂ t₃) (κJ t₁ t₂ t₃) (DJ t₁ t₂ t₃) ((2 * dU : ℝ) : ℂ)) :
    JointLaw atTop (window (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * Real.log X) / √(Real.log X))
      (fun X n => ((hit F b n : ℝ) - κF * Real.log X) / √(Real.log X))
      (fun X n => ((hit T b n : ℝ) - κT * Real.log X) / √(Real.log X))
      (√(2 / c ^ 3) * Real.log 2) (√(2 / c ^ 3) * Real.log 3)
      (√(2 / c ^ 3) * (Real.log 3 + Real.log 2)) := by
  refine jointLaw_of_cond (W := window (PredU b)) (Lg := fun X : ℕ => Real.log X)
    (C := fun X _ => Real.log X) b ?_ fun t₁ t₂ t₃ => ⟨(cond_window hdU0 hseq t₁ t₂ t₃).1, ?_⟩
  · filter_upwards [eventually_gt_atTop 1] with X hX
    exact Real.log_pos (by exact_mod_cast hX)
  refine avg_cexp_of_close (cond_window hdU0 hseq t₁ t₂ t₃).2 fun ε hε => ?_
  have h := close_logX (f := fun _ => 0) (κ := κJ t₁ t₂ t₃) (V := 1) one_pos
    (hdU.posLower hdU0) hε
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with X hX
  refine propn_congr fun n _ => ?_
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX)
  have e : (((0 : ℕ) : ℝ) - κJ t₁ t₂ t₃ * Real.log X) / √(1 * Real.log X) -
      normalised (fun _ => 0) (κJ t₁ t₂ t₃) 1 X n =
      (-1 / √(Real.log X)) * (qJ b t₁ t₂ t₃ n + κJ t₁ t₂ t₃ * Real.log X) -
      (-1 / √(Real.log X)) * (qJ b t₁ t₂ t₃ n + κJ t₁ t₂ t₃ * Real.log n) := by
    unfold normalised
    rw [one_mul]
    push_cast
    ring
  rw [e]

/-- `[X, 2X]`, both centrings, along a real sequence `Y_k → ∞`. -/
theorem cond_dyadic (hdU0 : 0 < dU)
    (hseq : ∀ t₁ t₂ t₃ : ℝ,
      SeqLimit (PredU b) (qJ b t₁ t₂ t₃) (κJ t₁ t₂ t₃) (DJ t₁ t₂ t₃) ((2 * dU : ℝ) : ℂ))
    {Y : ℕ → ℝ} (hY : Tendsto Y atTop atTop) (logX : Bool) (t₁ t₂ t₃ : ℝ) :
    (∀ᶠ k in atTop, (dyWindow (PredU b) (Y k)).Nonempty) ∧
    Tendsto (fun k => ((dyWindow (PredU b) (Y k)).card : ℂ)⁻¹ *
      ∑ n ∈ dyWindow (PredU b) (Y k), cexp ((((-1 / √(Real.log (Y k))) * (qJ b t₁ t₂ t₃ n +
        κJ t₁ t₂ t₃ * (if logX then Real.log (Y k) else Real.log n)) : ℝ) : ℂ) * I)) atTop
      (𝓝 ((Real.exp (-(DJ t₁ t₂ t₃ * (-1) ^ 2)) : ℝ) : ℂ)) := by
  have hodd : ∀ n ∈ PredU b, Odd n := fun n hn => hn.2.1
  have hp : ((2 * dU : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < 2 * dU).ne'
  have hτ := hτ_neg_one hY
  have hs0 : Tendsto (fun k => (0 : ℝ) * √(Real.log (Y k))) atTop (𝓝 0) := by simp
  cases logX with
  | false =>
    have h := oddClosed_limit (hseq t₁ t₂ t₃) hY hτ
    have h0 := oddClosed_limit (hseq t₁ t₂ t₃) hY hs0
    simp only [zero_pow two_ne_zero, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one,
      one_mul] at h0
    have := cond_charFun_limit (J := fun k => oddClosed (Y k))
      (N := fun k => ((oddClosed (Y k)).card : ℂ)) (c := fun _ n => κJ t₁ t₂ t₃ * Real.log n)
      (s := fun k => -1 / √(Real.log (Y k))) hp h h0
    simp only [oddClosed_filter_eq hodd] at this
    simpa using this
  | true =>
    have h := hseq t₁ t₂ t₃ Y _ (-1) hY hτ
    have h0 := hseq t₁ t₂ t₃ Y _ 0 hY hs0
    simp only [zero_pow two_ne_zero, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one,
      one_mul] at h0
    unfold oddCF at h h0
    have := cond_charFun_limit (J := fun k => oddClosed (Y k))
      (N := fun k => ((oddClosed (Y k)).card : ℂ))
      (c := fun k _ => κJ t₁ t₂ t₃ * Real.log (Y k))
      (s := fun k => -1 / √(Real.log (Y k))) hp h h0
    simp only [oddClosed_filter_eq hodd] at this
    simpa using this

/-- `[X, 2X]` (`X` real), centring at the sampled point or at `log X`. -/
theorem jointLaw_dyadic (hdU0 : 0 < dU)
    (hseq : ∀ t₁ t₂ t₃ : ℝ,
      SeqLimit (PredU b) (qJ b t₁ t₂ t₃) (κJ t₁ t₂ t₃) (DJ t₁ t₂ t₃) ((2 * dU : ℝ) : ℂ))
    (logX : Bool) :
    JointLaw atTop (dyWindow (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * (if logX then Real.log X else Real.log n)) /
        √(Real.log X))
      (fun X n => ((hit F b n : ℝ) - κF * (if logX then Real.log X else Real.log n)) /
        √(Real.log X))
      (fun X n => ((hit T b n : ℝ) - κT * (if logX then Real.log X else Real.log n)) /
        √(Real.log X))
      (√(2 / c ^ 3) * Real.log 2) (√(2 / c ^ 3) * Real.log 3)
      (√(2 / c ^ 3) * (Real.log 3 + Real.log 2)) := by
  refine jointLaw_real_of_seq fun Y hY => ?_
  refine jointLaw_of_cond (W := fun k => dyWindow (PredU b) (Y k))
    (Lg := fun k => Real.log (Y k))
    (C := fun k n => if logX then Real.log (Y k) else Real.log n) b ?_
    (cond_dyadic hdU0 hseq hY logX)
  filter_upwards [hY.eventually (eventually_gt_atTop 1)] with k hk
  exact Real.log_pos hk

/-! ## Theorem 1.1(iv) and its closing-sentence variants, from the imports -/

/-- **Theorem 1.1(iv) [`thm:main`]** from Tao's imports and Rhin's measure. -/
theorem joint_clocks_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ}
    (hθ : IrrMeasure d ϰ) (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    JointLaw atTop (window (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * Real.log n) / √(Real.log X))
      (fun X n => ((hit F b n : ℝ) - κF * Real.log n) / √(Real.log X))
      (fun X n => ((hit T b n : ℝ) - κT * Real.log n) / √(Real.log X))
      (√(2 / c ^ 3) * Real.log 2) (√(2 / c ^ 3) * Real.log 3)
      (√(2 / c ^ 3) * (Real.log 3 + Real.log 2)) := by
  obtain ⟨dU, hdU0, hdU, -, -⟩ := clock_data_U hTM hTP hθ b hb h3
  exact jointLaw_window hdU0 (seqLimit_joint hTM hTP hθ b hdU)

/-- **Theorem 1.1 [`thm:main`], closing sentence, applied to (iv)**, from Tao's imports and Rhin's
measure. -/
theorem joint_clocks_variants_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ}
    (hθ : IrrMeasure d ϰ) (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    JointLaw atTop (window (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * Real.log X) / √(Real.log X))
      (fun X n => ((hit F b n : ℝ) - κF * Real.log X) / √(Real.log X))
      (fun X n => ((hit T b n : ℝ) - κT * Real.log X) / √(Real.log X))
      (√(2 / c ^ 3) * Real.log 2) (√(2 / c ^ 3) * Real.log 3)
      (√(2 / c ^ 3) * (Real.log 3 + Real.log 2)) ∧
    JointLaw atTop (dyWindow (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * Real.log n) / √(Real.log X))
      (fun X n => ((hit F b n : ℝ) - κF * Real.log n) / √(Real.log X))
      (fun X n => ((hit T b n : ℝ) - κT * Real.log n) / √(Real.log X))
      (√(2 / c ^ 3) * Real.log 2) (√(2 / c ^ 3) * Real.log 3)
      (√(2 / c ^ 3) * (Real.log 3 + Real.log 2)) ∧
    JointLaw atTop (dyWindow (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * Real.log X) / √(Real.log X))
      (fun X n => ((hit F b n : ℝ) - κF * Real.log X) / √(Real.log X))
      (fun X n => ((hit T b n : ℝ) - κT * Real.log X) / √(Real.log X))
      (√(2 / c ^ 3) * Real.log 2) (√(2 / c ^ 3) * Real.log 3)
      (√(2 / c ^ 3) * (Real.log 3 + Real.log 2)) := by
  obtain ⟨dU, hdU0, hdU, -, -⟩ := clock_data_U hTM hTP hθ b hb h3
  have hseq := seqLimit_joint hTM hTP hθ b hdU
  exact ⟨jointLaw_window_logX hdU hdU0 hseq, jointLaw_dyadic hdU0 hseq false,
    jointLaw_dyadic hdU0 hseq true⟩

end CollatzCLT
