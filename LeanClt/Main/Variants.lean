import LeanClt.Sampling.Interval
import LeanClt.Architecture.LevyGeneral
import LeanClt.Main.VariantDefs
import LeanClt.Exceptional.Laws
import LeanClt.Main.OfTao
import LeanClt.Positivity.Main

/-!
# The closing sentence of Theorem 1.1 [`thm:main`] for the three clocks

"The same limits hold for sampling on dyadic intervals `[X, 2X]`, and `log N_X` may be replaced by
`log X` in the centring." For each of the raw, shortcut and odd clocks this file proves the CLT
* under uniform sampling from `P ∩ [1, X]` with centring `κ log X` (from `cltOn_logX`,
  Lemma 6.5(iii) [`lem:sampling`]);
* under uniform sampling from `P ∩ [X, 2X]`, `X` real, with centring `κ log N_X`;
* under uniform sampling from `P ∩ [X, 2X]` with centring `κ log X`.

For `[X, 2X]` the route is the paper's: the characteristic function along `[Y, 2Y]` comes from the
`[Y, 2Y]` clause of Lemma 6.5(ii) (`interval_limit`) for the doubling-compatible sets `P_T(b)` and
`P_F(b)`, and from odd dyadic sampling directly (`oddClosed_limit`) for the odd set `P_U(b)`;
Lévy's continuity theorem (`lawN_of_charFun`) converts it into the distribution-function form along
every real sequence `Y_k → ∞`, which is the real-variable limit (`cltOnDy_iff_seq`). On `[X, 2X]`
the two centrings differ by at most `|κ| log 2`, which is negligible after division by
`√(V log X)`.

The generic lemmas here are reused for Theorem 1.1(iv) in `Main/Joint.lean`.
-/

open Real Filter Topology Finset Complex MeasureTheory ProbabilityTheory

noncomputable section

namespace CollatzCLT

/-! ## Lévy's step for real statistics on general samples -/

/-- **Lévy step for `LawN`.** If along the finite samples `W k` the empirical characteristic
functions of `stat k ·` converge to `e^{-t²/2}`, then `stat k N_k ⇒ N(0,1)`. -/
theorem lawN_of_charFun {W : ℕ → Finset ℕ} {stat : ℕ → ℕ → ℝ}
    (hne : ∀ᶠ k in atTop, (W k).Nonempty)
    (hcf : ∀ t : ℝ, Tendsto (fun k => ((W k).card : ℂ)⁻¹ *
      ∑ n ∈ W k, cexp (t * stat k n * I)) atTop (𝓝 (cexp (-(t ^ 2 / 2))))) :
    LawN W stat := by
  classical
  intro z
  let μ₀ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hcf' : ∀ t : ℝ, Tendsto (fun k => ((W k).card : ℂ)⁻¹ *
      ∑ n ∈ W k, cexp (inner ℝ (stat k n) t * I)) atTop (𝓝 (charFun (μ₀ : Measure ℝ) t)) := by
    intro t
    have hg : charFun (μ₀ : Measure ℝ) t = cexp (-(t ^ 2 / 2)) := by
      simp only [μ₀, ProbabilityMeasure.coe_mk, charFun_gaussianReal]
      congr 1; push_cast; ring
    rw [hg]
    refine (hcf t).congr' (Eventually.of_forall fun k => ?_)
    congr 2
    funext n
    congr 2
    simp
  have hnull : (μ₀ : Measure ℝ) (frontier (Set.Iic z)) = 0 := by
    have hs : (gaussianReal 0 1 : Measure ℝ) {z} = 0 := by
      have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      exact measure_singleton z
    exact measure_mono_null (frontier_Iic_subset z) hs
  have h := tendsto_propn_of_charFun μ₀ hne hcf' measurableSet_Iic hnull
  have hΦ : (μ₀ : Measure ℝ).real (Set.Iic z) = Φ z := by
    simp [Φ, μ₀, cdf_eq_real]
  rw [hΦ] at h
  exact h

/-- `CLTOnDy` is `LawN` along every real sequence `Y_k → ∞`. -/
lemma cltOnDy_iff_seq {A : Set ℕ} {stat : ℝ → ℕ → ℝ} :
    CLTOnDy A stat ↔ ∀ Y : ℕ → ℝ, Tendsto Y atTop atTop →
      LawN (fun k => dyWindow A (Y k)) (fun k n => stat (Y k) n) := by
  constructor
  · intro h Y hY z
    exact (h z).comp hY
  · intro h z
    rw [tendsto_iff_seq_tendsto]
    intro Y hY
    exact h Y hY z

/-! ## From phase averages to conditional characteristic functions -/

open Classical in
lemma sum_ph_eq_filter (A : Set ℕ) (q : ℕ → ℝ) (J : Finset ℕ) (s : ℝ) (c : ℕ → ℝ) :
    ∑ n ∈ J, ph A q s (c n) n = ∑ n ∈ J.filter (· ∈ A), cexp (((s * (q n + c n) : ℝ) : ℂ) * I) := by
  rw [sum_filter]
  apply sum_congr rfl
  intro n _
  unfold ph
  by_cases h : n ∈ A <;> simp [h]

open Classical in
lemma sum_ph_zero_eq_card (A : Set ℕ) (q : ℕ → ℝ) (J : Finset ℕ) (c : ℕ → ℝ) :
    ∑ n ∈ J, ph A q 0 (c n) n = ((J.filter (· ∈ A)).card : ℂ) := by
  rw [sum_ph_eq_filter]
  simp

open Classical in
/-- **Conditioning on `A`.** If the phase averages over samples `J k`, normalised by `N k`,
converge to `L p` at frequencies `s k` and to `p ≠ 0` at frequency `0`, then the samples
`J k ∩ A` are eventually nonempty and the conditional characteristic function converges to `L`. -/
theorem cond_charFun_limit {A : Set ℕ} {q : ℕ → ℝ} {J : ℕ → Finset ℕ} {N : ℕ → ℂ}
    {c : ℕ → ℕ → ℝ} {s : ℕ → ℝ} {L p : ℂ} (hp : p ≠ 0)
    (h : Tendsto (fun k => (N k)⁻¹ * ∑ n ∈ J k, ph A q (s k) (c k n) n) atTop
      (𝓝 (L * p)))
    (h0 : Tendsto (fun k => (N k)⁻¹ * ∑ n ∈ J k, ph A q 0 (c k n) n) atTop (𝓝 p)) :
    (∀ᶠ k in atTop, ((J k).filter (· ∈ A)).Nonempty) ∧
    Tendsto (fun k => (((J k).filter (· ∈ A)).card : ℂ)⁻¹ *
      ∑ n ∈ (J k).filter (· ∈ A), cexp (((s k * (q n + c k n) : ℝ) : ℂ) * I)) atTop (𝓝 L) := by
  have h0' : Tendsto (fun k => (N k)⁻¹ * (((J k).filter (· ∈ A)).card : ℂ)) atTop
      (𝓝 p) := by
    refine h0.congr (fun k => ?_)
    rw [sum_ph_zero_eq_card A q (J k) (c k)]
  have hne : ∀ᶠ k in atTop, (N k)⁻¹ * (((J k).filter (· ∈ A)).card : ℂ) ≠ 0 :=
    h0'.eventually_ne hp
  refine ⟨hne.mono fun k hk => ?_, ?_⟩
  · rw [← Finset.card_pos]
    by_contra h'
    apply hk
    simp [Nat.le_zero.mp (not_lt.mp h')]
  · have := h.div h0' hp
    rw [mul_div_cancel_right₀ _ hp] at this
    refine this.congr' (hne.mono fun k hk => ?_)
    simp only [Pi.div_apply]
    rw [sum_ph_eq_filter A q (J k) (s k) (c k)]
    have hN : (N k)⁻¹ ≠ 0 := left_ne_zero_of_mul hk
    rw [mul_div_mul_left _ _ hN, div_eq_inv_mul]

/-! ## The CLT on `[X, 2X]` -/

/-- `t (f - κ log n)/√(V log Y) = (σ/√(log Y)) (-f + κ log n)` with `σ = -t/√V`. -/
lemma stat_eq_phase {V : ℝ} (hV : 0 < V) (t fn κl L : ℝ) (hL : 0 < L) :
    t * ((fn - κl) / √(V * L)) = (-t / √V) / √L * (-fn + κl) := by
  have h1 : 0 < √V := Real.sqrt_pos.mpr hV
  have h2 : 0 < √L := Real.sqrt_pos.mpr hL
  rw [Real.sqrt_mul hV.le]
  field_simp
  ring

/-- `e^{-(V/2) σ²} = e^{-t²/2}` for `σ = -t/√V`. -/
lemma exp_sigma_eq {V : ℝ} (hV : 0 < V) (t : ℝ) :
    Real.exp (-(V / 2 * (-t / √V) ^ 2)) = Real.exp (-(t ^ 2 / 2)) := by
  congr 1
  rw [div_pow, Real.sq_sqrt hV.le]
  field_simp

open Classical in
/-- **The CLT on `[X, 2X]` from phase averages.** Let `J Y` be finite samples with
`J Y ∩ A = A ∩ [Y, 2Y]`, normalised by `N Y`. If along every real sequence `Y_k → ∞` and for every
`σ` the phase averages of the clock `-f` at frequency `σ/√(log Y_k)`, centred at `κ log n`, tend
to `e^{-(V/2) σ²} p` with `p > 0`, then `(f(n) - κ log n)/√(V log X)` satisfies the CLT under
uniform sampling from `A ∩ [X, 2X]`. -/
theorem cltOnDy_of_limits {A : Set ℕ} {f : ℕ → ℕ} {κ V p : ℝ} (hV : 0 < V) (hp : 0 < p)
    {J : ℝ → Finset ℕ} {N : ℝ → ℂ} (hJ : ∀ Y, (J Y).filter (· ∈ A) = dyWindow A Y)
    (hlim : ∀ Y : ℕ → ℝ, Tendsto Y atTop atTop → ∀ σ : ℝ, Tendsto (fun k => (N (Y k))⁻¹ *
      ∑ n ∈ J (Y k), ph A (fun n => -(f n : ℝ)) (σ / √(Real.log (Y k))) (κ * Real.log n) n)
      atTop (𝓝 ((Real.exp (-(V / 2 * σ ^ 2)) : ℂ) * p))) :
    CLTOnDy A (fun X n => ((f n : ℝ) - κ * Real.log n) / √(V * Real.log X)) := by
  rw [cltOnDy_iff_seq]
  intro Y hY
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h0 : Tendsto (fun k => (N (Y k))⁻¹ * ∑ n ∈ J (Y k),
      ph A (fun n => -(f n : ℝ)) 0 (κ * Real.log n) n) atTop (𝓝 (p : ℂ)) := by
    have := hlim Y hY 0
    simp only [zero_div, zero_pow two_ne_zero, mul_zero, neg_zero, Real.exp_zero,
      Complex.ofReal_one, one_mul] at this
    exact this
  have hcond := fun σ : ℝ => cond_charFun_limit (A := A) (q := fun n => -(f n : ℝ))
    (J := fun k => J (Y k)) (N := fun k => N (Y k)) (c := fun _ n => κ * Real.log n)
    (s := fun k => σ / √(Real.log (Y k))) hpC (hlim Y hY σ) h0
  refine lawN_of_charFun ?_ fun t => ?_
  · exact ((hcond 0).1).mono fun k hk => by rwa [hJ] at hk
  · have h := (hcond (-t / √V)).2
    rw [exp_sigma_eq hV t, Complex.ofReal_exp] at h
    push_cast at h
    refine h.congr' ?_
    filter_upwards [hY.eventually (eventually_gt_atTop 1)] with k hk
    have hL : 0 < Real.log (Y k) := Real.log_pos hk
    simp only [hJ]
    congr 1
    apply sum_congr rfl
    intro n _
    congr 1
    rw [show (t : ℂ) * (((((f n : ℝ) - κ * Real.log n) / √(V * Real.log (Y k)) : ℝ)) : ℂ) =
      ((t * (((f n : ℝ) - κ * Real.log n) / √(V * Real.log (Y k))) : ℝ) : ℂ) by push_cast; ring,
      stat_eq_phase hV t _ _ _ hL]
    push_cast
    ring

open Classical in
/-- **The `[X, 2X]` CLT for a doubling-compatible set** (Lemma 6.5(ii) [`lem:sampling`], the
`[Y, 2Y]` clause, with Lévy's continuity theorem). -/
theorem cltOnDy_of_doubling {A : Set ℕ} {f : ℕ → ℕ} {κ V e0 p : ℝ} (hV : 0 < V) (hp : 0 < p)
    (hseq : SeqLimit A (fun n => -(f n : ℝ)) κ (V / 2) p)
    (hdbl : DoublingCompatible A (fun n => -(f n : ℝ)) e0) :
    CLTOnDy A (fun X n => ((f n : ℝ) - κ * Real.log n) / √(V * Real.log X)) := by
  refine cltOnDy_of_limits hV hp (J := fun Y => Icc ⌈Y⌉₊ ⌊2 * Y⌋₊)
    (N := fun Y => ((Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).card : ℂ)) (fun Y => rfl) fun Y hY σ => ?_
  refine interval_limit hseq hdbl hY (tendsto_const_nhds.congr' ?_)
  filter_upwards [hY.eventually (eventually_gt_atTop 1)] with k hk
  have := Real.sqrt_pos.mpr (Real.log_pos hk)
  field_simp

open Classical in
lemma oddClosed_filter_eq {A : Set ℕ} (hodd : ∀ n ∈ A, Odd n) (Y : ℝ) :
    (oddClosed Y).filter (· ∈ A) = dyWindow A Y := by
  unfold oddClosed dyWindow
  rw [filter_filter]
  exact filter_congr fun n _ => ⟨fun h => h.2, fun h => ⟨hodd n h, h⟩⟩

open Classical in
/-- **The `[X, 2X]` CLT for a set of odd integers**, from odd dyadic sampling directly. -/
theorem cltOnDy_of_odd {A : Set ℕ} {f : ℕ → ℕ} {κ V p : ℝ} (hV : 0 < V) (hp : 0 < p)
    (hodd : ∀ n ∈ A, Odd n) (hseq : SeqLimit A (fun n => -(f n : ℝ)) κ (V / 2) p) :
    CLTOnDy A (fun X n => ((f n : ℝ) - κ * Real.log n) / √(V * Real.log X)) := by
  refine cltOnDy_of_limits hV hp (J := oddClosed) (N := fun Y => ((oddClosed Y).card : ℂ))
    (oddClosed_filter_eq hodd) fun Y hY σ => ?_
  refine oddClosed_limit hseq hY (tendsto_const_nhds.congr' ?_)
  filter_upwards [hY.eventually (eventually_gt_atTop 1)] with k hk
  have := Real.sqrt_pos.mpr (Real.log_pos hk)
  field_simp

open Classical in
/-- On `[X, 2X]` the centring `κ log N_X` may be replaced by `κ log X`. -/
theorem cltOnDy_logX {A : Set ℕ} {f : ℕ → ℕ} {κ V : ℝ} (hV : 0 < V)
    (h : CLTOnDy A (fun X n => ((f n : ℝ) - κ * Real.log n) / √(V * Real.log X))) :
    CLTOnDy A (fun X n => ((f n : ℝ) - κ * Real.log X) / √(V * Real.log X)) := by
  rw [cltOnDy_iff_seq] at h ⊢
  intro Y hY
  refine lawN_of_uniform_close (e := fun k => |κ| * Real.log 2 / √(V * Real.log (Y k))) ?_ ?_
    (h Y hY)
  · exact tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp ((Real.tendsto_log_atTop.comp hY).const_mul_atTop hV))
  · filter_upwards [hY.eventually (eventually_gt_atTop 1)] with k hk n hn
    have hL : 0 < Real.log (Y k) := Real.log_pos hk
    have hs : 0 < √(V * Real.log (Y k)) := Real.sqrt_pos.mpr (by positivity)
    unfold dyWindow at hn
    rw [mem_filter, mem_Icc] at hn
    have hn1 : Y k ≤ n := Nat.ceil_le.mp hn.1.1
    have hn2 : (n : ℝ) ≤ 2 * Y k := (Nat.cast_le.mpr hn.1.2).trans (Nat.floor_le (by linarith))
    have hY0 : 0 < Y k := by linarith
    have hlog : |Real.log n - Real.log (Y k)| ≤ Real.log 2 := by
      rw [← Real.log_div (by linarith) hY0.ne', abs_of_nonneg
        (Real.log_nonneg ((one_le_div hY0).mpr hn1))]
      exact Real.log_le_log (div_pos (by linarith) hY0) ((div_le_iff₀ hY0).mpr (by linarith))
    rw [← sub_div, abs_div, abs_of_pos hs]
    apply div_le_div_of_nonneg_right _ hs.le
    rw [show ((f n : ℝ) - κ * Real.log (Y k)) - ((f n : ℝ) - κ * Real.log n) =
      κ * (Real.log n - Real.log (Y k)) by ring, abs_mul]
    exact mul_le_mul_of_nonneg_left hlog (abs_nonneg κ)

/-! ## The odd dyadic limit, identified -/

/-- For a doubling-compatible set with density `d`, Proposition 6.2 [`prop:fixedbase`] holds in
sequential form with limit `p = d` (Lemma 6.5(i) [`lem:sampling`]). -/
theorem seqLimit_of_density {A : Set ℕ} {q : ℕ → ℝ} {κ D α e0 d : ℝ} (hα : 1 < α)
    (hadj : AdjacentScales (oddCF A q κ) D α) (hdbl : DoublingCompatible A q e0)
    (hd : HasDensity A d) : SeqLimit A q κ D (d : ℂ) := by
  obtain ⟨p, -, hseq0⟩ := fixed_base_limit_seq hα hadj (fun Y => continuousAt_oddCF A q κ Y)
  have hseq : SeqLimit A q κ D p := fun Y sY τ hY hτ => hseq0 atTop Y sY τ hY hτ
  have h0 := uniform_limit hseq hdbl (sX := fun _ => 0) (τ := 0) (by simp)
  simp only [sum_ph_zero, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul,
    zero_pow two_ne_zero] at h0
  have hdC : Tendsto (fun X : ℕ => ((((window A X).card : ℝ) / X : ℝ) : ℂ)) atTop (𝓝 (d : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hd
  have hpd : p = d := tendsto_nhds_unique
    (h0.congr' (Eventually.of_forall fun X => by push_cast; ring)) hdC
  rw [← hpd]
  exact hseq

/-- For a set of odd integers with density `d`, the odd dyadic limit is `p = 2d`. -/
theorem seqLimit_of_density_odd {A : Set ℕ} {q : ℕ → ℝ} {κ D α d : ℝ} (hα : 1 < α)
    (hadj : AdjacentScales (oddCF A q κ) D α) (hodd : ∀ n ∈ A, Odd n) (hd : HasDensity A d) :
    SeqLimit A q κ D ((2 * d : ℝ) : ℂ) := by
  obtain ⟨p, -, hseq0⟩ := fixed_base_limit_seq hα hadj (fun Y => continuousAt_oddCF A q κ Y)
  have hseq : SeqLimit A q κ D p := fun Y sY τ hY hτ => hseq0 atTop Y sY τ hY hτ
  have h0 := uniform_limit_odd hseq hodd (sX := fun _ => 0) (τ := 0) (by simp)
  simp only [sum_ph_zero, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul,
    zero_pow two_ne_zero] at h0
  have hdC : Tendsto (fun X : ℕ => ((((window A X).card : ℝ) / X : ℝ) : ℂ)) atTop (𝓝 (d : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hd
  have hpd : p / 2 = d := tendsto_nhds_unique
    (h0.congr' (Eventually.of_forall fun X => by push_cast; ring)) hdC
  have : p = ((2 * d : ℝ) : ℂ) := by push_cast; rw [← hpd]; ring
  rw [← this]
  exact hseq

/-! ## The three clocks -/

/-- Raw clock: density, CLT (Theorem 1.1(i)–(ii)) and the odd dyadic limit. -/
theorem clock_data_T (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    ∃ p > 0, HasDensity (Pred T b) p ∧ CLTOn (Pred T b) (normalised (hit T b) κT VT) ∧
      SeqLimit (Pred T b) (fun n => -(hit T b n : ℝ)) κT (VT / 2) (p : ℂ) := by
  obtain ⟨⟨p, hp0, hp⟩, hclt⟩ :=
    main_T_of_tao hTM hTP hθ b hb (Positivity.positivity_of_tao hTM hTP hb h3)
  have h := adjacent_of_tao hTM hTP hθ (transport_T b)
  have e1 : (2 * 1 + 1) / c = κT := by unfold κT; norm_num
  have e2 : (1 * bet + 1 * ell) ^ 2 / c ^ 3 = VT / 2 := by unfold VT bet ell; ring
  rw [e1, e2] at h
  exact ⟨p, hp0, hp, hclt, seqLimit_of_density alpha_gt_one h (doubling_T b hb) hp⟩

/-- Shortcut clock: density, CLT (Theorem 1.1(i)–(ii)) and the odd dyadic limit. -/
theorem clock_data_F (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    ∃ p > 0, HasDensity (Pred F b) p ∧ CLTOn (Pred F b) (normalised (hit F b) κF VF) ∧
      SeqLimit (Pred F b) (fun n => -(hit F b n : ℝ)) κF (VF / 2) (p : ℂ) := by
  obtain ⟨⟨p, hp0, hp⟩, hclt⟩ :=
    main_F_of_tao hTM hTP hθ b hb (Positivity.positivity_of_tao hTM hTP (by omega)
      (fun h => h3 ((Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 3 2)).mp h)))
  have h := adjacent_of_tao hTM hTP hθ (transport_F b)
  have e1 : (2 * 1 + 0) / c = κF := by unfold κF; norm_num
  have e2 : (1 * bet + 0 * ell) ^ 2 / c ^ 3 = VF / 2 := by unfold VF bet; ring
  rw [e1, e2] at h
  exact ⟨p, hp0, hp, hclt, seqLimit_of_density alpha_gt_one h (doubling_F b hb) hp⟩

/-- Odd clock: density, CLT (Theorem 1.1(iii)) and the odd dyadic limit `2 dens P_U(b)`. -/
theorem clock_data_U (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    ∃ p > 0, HasDensity (PredU b) p ∧ CLTOn (PredU b) (normalised (hit U b) κU VU) ∧
      SeqLimit (PredU b) (fun n => -(hit U b n : ℝ)) κU (VU / 2) ((2 * p : ℝ) : ℂ) := by
  obtain ⟨⟨p, hp0, hp⟩, hclt⟩ :=
    main_U_of_tao hTM hTP hθ b hb (Positivity.positivity_of_tao hTM hTP hb.pos h3)
  have h := adjacent_of_tao hTM hTP hθ (transport_U b)
  have e1 : (2 * 0 + 1) / c = κU := by unfold κU; norm_num
  have e2 : (0 * bet + 1 * ell) ^ 2 / c ^ 3 = VU / 2 := by unfold VU ell; ring
  rw [e1, e2] at h
  exact ⟨p, hp0, hp, hclt, seqLimit_of_density_odd alpha_gt_one h (fun n hn => hn.2.1) hp⟩

/-! ## The closing sentence of Theorem 1.1 for (ii) and (iii) -/

/-- **Theorem 1.1 [`thm:main`], closing sentence, raw clock**, from Tao's imports and Rhin's
measure. -/
theorem clt_T_variants_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ}
    (hθ : IrrMeasure d ϰ) (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    CLTOn (Pred T b) (fun X n => ((hit T b n : ℝ) - κT * Real.log X) / √(VT * Real.log X)) ∧
    CLTOnDy (Pred T b) (fun X n => ((hit T b n : ℝ) - κT * Real.log n) / √(VT * Real.log X)) ∧
    CLTOnDy (Pred T b) (fun X n => ((hit T b n : ℝ) - κT * Real.log X) / √(VT * Real.log X)) := by
  obtain ⟨p, hp0, hp, hclt, hseq⟩ := clock_data_T hTM hTP hθ b hb h3
  have hdy := cltOnDy_of_doubling VT_pos hp0 hseq (doubling_T b hb)
  exact ⟨cltOn_logX VT_pos (hp.posLower hp0) hclt, hdy, cltOnDy_logX VT_pos hdy⟩

/-- **Theorem 1.1 [`thm:main`], closing sentence, shortcut clock**, from Tao's imports and Rhin's
measure. -/
theorem clt_F_variants_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ}
    (hθ : IrrMeasure d ϰ) (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    CLTOn (Pred F b) (fun X n => ((hit F b n : ℝ) - κF * Real.log X) / √(VF * Real.log X)) ∧
    CLTOnDy (Pred F b) (fun X n => ((hit F b n : ℝ) - κF * Real.log n) / √(VF * Real.log X)) ∧
    CLTOnDy (Pred F b) (fun X n => ((hit F b n : ℝ) - κF * Real.log X) / √(VF * Real.log X)) := by
  obtain ⟨p, hp0, hp, hclt, hseq⟩ := clock_data_F hTM hTP hθ b hb h3
  have hdy := cltOnDy_of_doubling VF_pos hp0 hseq (doubling_F b hb)
  exact ⟨cltOn_logX VF_pos (hp.posLower hp0) hclt, hdy, cltOnDy_logX VF_pos hdy⟩

/-- **Theorem 1.1 [`thm:main`], closing sentence, odd clock**, from Tao's imports and Rhin's
measure. -/
theorem clt_U_variants_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ}
    (hθ : IrrMeasure d ϰ) (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    CLTOn (PredU b) (fun X n => ((hit U b n : ℝ) - κU * Real.log X) / √(VU * Real.log X)) ∧
    CLTOnDy (PredU b) (fun X n => ((hit U b n : ℝ) - κU * Real.log n) / √(VU * Real.log X)) ∧
    CLTOnDy (PredU b) (fun X n => ((hit U b n : ℝ) - κU * Real.log X) / √(VU * Real.log X)) := by
  obtain ⟨p, hp0, hp, hclt, hseq⟩ := clock_data_U hTM hTP hθ b hb h3
  have hdy := cltOnDy_of_odd VU_pos (by positivity : (0 : ℝ) < 2 * p) (fun n hn => hn.2.1) hseq
  exact ⟨cltOn_logX VU_pos (hp.posLower hp0) hclt, hdy, cltOnDy_logX VU_pos hdy⟩

end CollatzCLT
