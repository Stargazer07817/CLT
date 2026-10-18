import LeanClt.Main.Variants

/-!
# Corollary 1.2 [`cor:rates`]: sharp hitting rates

From the CLT on a population `P` of positive density `p` (Theorem 1.1(ii)–(iii)), the sets
`{n ∈ P : τ(n) ≤ κ log n + z √(V log n)}` have density `Φ(z) p`, and the sets
`{n ∈ P : τ(n) ≤ (κ + η(n)) log n}` have density `p` or `0` when `η(x) √(log x) → +∞` or `-∞`; the
three cases of `{n ∈ P : τ(n) ≤ c log n}` follow (`rates_of_cltOn`). The argument is the paper's:
under `N_X` uniform on `P ∩ [1, X]`, `log N_X / log X → 1` in probability (here: the proportion
of `n` with `log X - log n > g(X)` tends to `0` for every `g → ∞`, `propn_gap`), Slutsky's step,
and tightness of the normalised clock. The restriction to `P` encodes the paper's convention
`τ = ∞` off `P`. For the odd clock the densities are taken among the odd integers
(`hasOddDensity_of_hasDensity`): for a set of odd integers this doubles the natural density.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-! ## Densities from proportions in a population -/

open Classical in
/-- If `P` has density `p` and the proportion of `n ∈ P ∩ [1, X]` with property `Q` tends to `L`,
then `{n ∈ P : Q n}` has density `L p`. -/
lemma hasDensity_of_propn_window {A : Set ℕ} {p L : ℝ} (hp : HasDensity A p) {Q : ℕ → Prop}
    (h : Tendsto (fun X => propn (window A X) Q) atTop (𝓝 L)) :
    HasDensity {n | n ∈ A ∧ Q n} (L * p) := by
  refine (h.mul hp).congr fun X => ?_
  have hw : window {n | n ∈ A ∧ Q n} X = (window A X).filter Q := by
    ext n
    simp only [mem_filter, mem_window, Set.mem_ofPred_eq]
    tauto
  unfold propn
  rw [hw]
  rcases Nat.eq_zero_or_pos (window A X).card with h0 | h0
  · have h0' : ((window A X).filter Q).card = 0 :=
      Nat.eq_zero_of_le_zero (h0 ▸ card_filter_le _ _)
    rw [h0, h0']
    simp
  · have : ((window A X).card : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    field_simp

/-- **`log N_X / log X → 1` in probability.** Under positive lower density, for every `g → ∞` the
proportion of `n ∈ A ∩ [1, X]` with `log X - log n > g(X)` tends to `0`. -/
lemma propn_gap {A : Set ℕ}
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window A X).card : ℝ))
    {g : ℕ → ℝ} (hg : Tendsto g atTop atTop) :
    Tendsto (fun X => propn (window A X) (fun n => g X < Real.log X - Real.log n)) atTop
      (𝓝 0) := by
  obtain ⟨c, hc, hcX⟩ := hpos
  have hlim : Tendsto (fun X => Real.exp (-g X) / c) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hg).div_const c
    simpa [Function.comp_def] using this
  refine tendsto_propn_zero hlim ?_
  filter_upwards [hcX, eventually_gt_atTop 0] with X hX hX0
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX0
  have hW : 0 < ((window A X).card : ℝ) := lt_of_lt_of_le (by positivity) hX
  refine (propn_le_of_subset (S := Icc 1 ⌊(X : ℝ) * Real.exp (-g X)⌋₊) fun n hn hlt => ?_).trans ?_
  · obtain ⟨⟨hn1, -⟩, -⟩ := mem_window.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have h2 : (n : ℝ) < X * Real.exp (-g X) := by
      rw [← Real.exp_log hn0, ← Real.exp_log hXr, ← Real.exp_add]
      exact Real.exp_lt_exp.mpr (by linarith)
    exact mem_Icc.mpr ⟨hn1, Nat.le_floor h2.le⟩
  · rw [card_Icc_one]
    have hfl := Nat.floor_le (show (0 : ℝ) ≤ X * Real.exp (-g X) by positivity)
    calc (⌊(X : ℝ) * Real.exp (-g X)⌋₊ : ℝ) / (window A X).card
        ≤ (X * Real.exp (-g X)) / (c * X) := div_le_div₀ (by positivity) hfl (by positivity) hX
      _ = Real.exp (-g X) / c := by field_simp

/-- The integers below a fixed `N₀` have vanishing proportion. -/
lemma propn_lt_const {A : Set ℕ}
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window A X).card : ℝ)) (N₀ : ℕ) :
    Tendsto (fun X => propn (window A X) (fun n => n < N₀)) atTop (𝓝 0) := by
  have hg : Tendsto (fun X : ℕ => Real.log X - Real.log (N₀ + 1) - 1) atTop atTop := by
    have := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ this)
  refine tendsto_propn_zero (propn_gap hpos hg) (Eventually.of_forall fun X => ?_)
  refine propn_mono fun n hn hlt => ?_
  obtain ⟨⟨hn1, -⟩, -⟩ := mem_window.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have : Real.log n < Real.log (N₀ + 1) :=
    Real.log_lt_log hn0 (by exact_mod_cast (by omega : n < N₀ + 1))
  linarith

/-! ## The three rate clauses for a population -/

variable {A : Set ℕ} {f : ℕ → ℕ} {κ V : ℝ}

/-- `1 - √r ≤ 1 - r` on `[0, 1]`. -/
lemma one_sub_sqrt_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 1 - √r ≤ 1 - r := by
  have : r ≤ √r := by
    calc r = √r * √r := (Real.mul_self_sqrt h0).symm
      _ ≤ √r * 1 := by
          gcongr
          exact Real.sqrt_le_one.mpr h1
      _ = √r := mul_one _
  linarith

/-- **The `z` clause.** Under the CLT on `A` and positive lower density, the proportion of
`n ∈ A ∩ [1, X]` with `f(n) ≤ κ log n + z √(V log n)` tends to `Φ(z)`. -/
theorem propn_rate_z (hV : 0 < V)
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window A X).card : ℝ))
    (h : CLTOn A (normalised f κ V)) (z : ℝ) :
    Tendsto (fun X => propn (window A X)
      (fun n => (f n : ℝ) ≤ κ * Real.log n + z * √(V * Real.log n))) atTop (𝓝 (Φ z)) := by
  -- the statistic whose event `≤ z` is the target event
  set stat' : ℕ → ℕ → ℝ := fun X n =>
    normalised f κ V X n - z * √(Real.log n / Real.log X) + z with hstat'
  have hlaw : LawN (window A) stat' := by
    refine lawN_of_close h fun ε hε => ?_
    have hg : Tendsto (fun X : ℕ => ε * Real.log X / (|z| + 1)) atTop atTop :=
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε).atTop_div_const
        (by positivity)
    refine tendsto_propn_zero (propn_gap hpos hg) ?_
    filter_upwards [eventually_gt_atTop 1] with X hX
    refine propn_mono fun n hn hlt => ?_
    obtain ⟨⟨hn1, hnX⟩, -⟩ := mem_window.mp hn
    have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hlnX : Real.log n ≤ Real.log X := Real.log_le_log hn0 (by exact_mod_cast hnX)
    have hr0 : 0 ≤ Real.log n / Real.log X := div_nonneg hln hL.le
    have hr1 : Real.log n / Real.log X ≤ 1 := (div_le_one hL).mpr hlnX
    have hd : |stat' X n - normalised f κ V X n| ≤
        (|z| + 1) * ((Real.log X - Real.log n) / Real.log X) := by
      rw [hstat', show normalised f κ V X n - z * √(Real.log n / Real.log X) + z -
        normalised f κ V X n = z * (1 - √(Real.log n / Real.log X)) by ring, abs_mul]
      have h1 : |1 - √(Real.log n / Real.log X)| ≤ (Real.log X - Real.log n) / Real.log X := by
        rw [abs_of_nonneg (by linarith [Real.sqrt_le_one.mpr hr1])]
        calc 1 - √(Real.log n / Real.log X) ≤ 1 - Real.log n / Real.log X :=
              one_sub_sqrt_le hr0 hr1
          _ = (Real.log X - Real.log n) / Real.log X := by field_simp
      have h2 : 0 ≤ (Real.log X - Real.log n) / Real.log X := div_nonneg (by linarith) hL.le
      calc |z| * |1 - √(Real.log n / Real.log X)| ≤ |z| * ((Real.log X - Real.log n) / Real.log X) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg z)
        _ ≤ _ := by nlinarith
    have h1 : ε < (|z| + 1) * ((Real.log X - Real.log n) / Real.log X) := lt_of_lt_of_le hlt hd
    have h2 : ε * Real.log X < (|z| + 1) * (Real.log X - Real.log n) := by
      have := mul_lt_mul_of_pos_right h1 hL
      rwa [mul_assoc, div_mul_cancel₀ _ hL.ne'] at this
    change ε * Real.log X / (|z| + 1) < Real.log X - Real.log n
    rw [div_lt_iff₀ (by positivity)]
    linarith
  refine (hlaw z).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with X hX
  refine propn_congr fun n hn => ?_
  obtain ⟨⟨hn1, -⟩, -⟩ := mem_window.mp hn
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX)
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hs : 0 < √(V * Real.log X) := Real.sqrt_pos.mpr (by positivity)
  have key : √(Real.log n / Real.log X) * √(V * Real.log X) = √(V * Real.log n) := by
    rw [← Real.sqrt_mul (div_nonneg hln hL.le)]
    congr 1
    field_simp
  simp only [hstat', normalised]
  rw [show ((f n : ℝ) - κ * Real.log n) / √(V * Real.log X) - z * √(Real.log n / Real.log X) + z ≤ z
    ↔ ((f n : ℝ) - κ * Real.log n) / √(V * Real.log X) ≤ z * √(Real.log n / Real.log X) by
      constructor <;> intro h <;> linarith, div_le_iff₀ hs, mul_assoc, key]
  constructor <;> intro h <;> linarith

/-- `√(log X)/2 ≤ √(log n)` when `log n ≥ log X / 4`. -/
lemma sqrt_log_half_le {Lx Ln : ℝ} (h : Lx / 4 ≤ Ln) : √Lx / 2 ≤ √Ln := by
  have h4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc √Lx / 2 = √(Lx / 4) := by rw [Real.sqrt_div' _ (by norm_num), h4]
    _ ≤ √Ln := Real.sqrt_le_sqrt h

/-- **The `η → +∞` clause.** If `η(x) √(log x) → +∞`, the proportion of `n ∈ A ∩ [1, X]` with
`f(n) ≤ (κ + η(n)) log n` tends to `1`. -/
theorem propn_rate_top (hV : 0 < V)
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window A X).card : ℝ))
    (h : CLTOn A (normalised f κ V)) {η : ℝ → ℝ}
    (hη : Tendsto (fun x => η x * √(Real.log x)) atTop atTop) :
    Tendsto (fun X => propn (window A X) (fun n => (f n : ℝ) ≤ (κ + η n) * Real.log n)) atTop
      (𝓝 1) := by
  have hηN : Tendsto (fun n : ℕ => η n * √(Real.log n)) atTop atTop :=
    hη.comp tendsto_natCast_atTop_atTop
  have hgap := propn_gap hpos (g := fun X : ℕ => 3 / 4 * Real.log X)
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => Eventually.of_forall fun X =>
    lt_of_le_of_lt (propn_le_one _ _) hb⟩
  set δ := 1 - a with hδ
  have hδ0 : 0 < δ := by linarith
  obtain ⟨M0, hM0⟩ :=
    (tendsto_Φ_atTop.eventually (lt_mem_nhds (show 1 - δ / 3 < 1 by linarith))).exists
  set M := max M0 0 with hMdef
  have hMΦ : 1 - δ / 3 < Φ M := lt_of_lt_of_le hM0 (Φ_mono (le_max_left _ _))
  have hM0' : 0 ≤ M := le_max_right _ _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hηN.eventually (eventually_ge_atTop (2 * √V * M)))
  filter_upwards [(h M).eventually (lt_mem_nhds hMΦ),
    (propn_lt_const hpos N₀).eventually (gt_mem_nhds (show (0 : ℝ) < δ / 3 by positivity)),
    hgap.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 3 by positivity)),
    eventually_gt_atTop 1] with X hX1 hX2 hX3 hX4
  have hle : propn (window A X) (fun n => normalised f κ V X n ≤ M) ≤
      propn (window A X) (fun n => (f n : ℝ) ≤ (κ + η n) * Real.log n) +
      (propn (window A X) (fun n => n < N₀) +
        propn (window A X) (fun n => 3 / 4 * Real.log X < Real.log X - Real.log n)) := by
    refine (propn_le_add (q := fun n => (f n : ℝ) ≤ (κ + η n) * Real.log n)
      (r := fun n => n < N₀ ∨ 3 / 4 * Real.log X < Real.log X - Real.log n)
      fun n hn hM' => ?_).trans ?_
    · by_cases h1 : n < N₀
      · exact Or.inr (Or.inl h1)
      by_cases h2 : 3 / 4 * Real.log X < Real.log X - Real.log n
      · exact Or.inr (Or.inr h2)
      left
      push Not at h1 h2
      have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX4)
      have hln4 : Real.log X / 4 ≤ Real.log n := by linarith
      have hln0 : 0 ≤ Real.log n := by linarith
      have hsq := sqrt_log_half_le hln4
      have hηn : 2 * √V * M ≤ η n * √(Real.log n) := hN₀ n h1
      have hs : 0 < √(V * Real.log X) := Real.sqrt_pos.mpr (by positivity)
      have hprod : M * √(V * Real.log X) ≤ η n * Real.log n := by
        have e1 : η n * Real.log n = (η n * √(Real.log n)) * √(Real.log n) := by
          rw [mul_assoc, Real.mul_self_sqrt hln0]
        have e2 : M * √(V * Real.log X) = (2 * √V * M) * (√(Real.log X) / 2) := by
          rw [Real.sqrt_mul hV.le]; ring
        rw [e1, e2]
        exact mul_le_mul hηn hsq (by positivity) (le_trans (by positivity) hηn)
      unfold normalised at hM'
      rw [div_le_iff₀ hs] at hM'
      rw [add_mul]
      linarith
    · gcongr
      exact propn_or_le _ _ _
  have hX1' : 1 - δ / 3 < propn (window A X) (fun n => normalised f κ V X n ≤ M) := hX1
  linarith

/-- **The `η → -∞` clause.** If `η(x) √(log x) → -∞`, the proportion of `n ∈ A ∩ [1, X]` with
`f(n) ≤ (κ + η(n)) log n` tends to `0`. -/
theorem propn_rate_bot (hV : 0 < V)
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window A X).card : ℝ))
    (h : CLTOn A (normalised f κ V)) {η : ℝ → ℝ}
    (hη : Tendsto (fun x => η x * √(Real.log x)) atTop atBot) :
    Tendsto (fun X => propn (window A X) (fun n => (f n : ℝ) ≤ (κ + η n) * Real.log n)) atTop
      (𝓝 0) := by
  have hηN : Tendsto (fun n : ℕ => η n * √(Real.log n)) atTop atBot :=
    hη.comp tendsto_natCast_atTop_atTop
  have hgap := propn_gap hpos (g := fun X : ℕ => 3 / 4 * Real.log X)
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun X => lt_of_lt_of_le ha (propn_nonneg _ _),
    fun b hb => ?_⟩
  obtain ⟨M0, hM0⟩ :=
    (tendsto_Φ_atBot.eventually (gt_mem_nhds (show (0 : ℝ) < b / 3 by positivity))).exists
  set M := max (-M0) 0 with hMdef
  have hMΦ : Φ (-M) < b / 3 :=
    lt_of_le_of_lt (Φ_mono (by rw [hMdef]; linarith [le_max_left (-M0) 0])) hM0
  have hM0' : 0 ≤ M := le_max_right _ _
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.mp (hηN.eventually (eventually_le_atBot (-(2 * √V * M))))
  filter_upwards [(h (-M)).eventually (gt_mem_nhds hMΦ),
    (propn_lt_const hpos N₀).eventually (gt_mem_nhds (show (0 : ℝ) < b / 3 by positivity)),
    hgap.eventually (gt_mem_nhds (show (0 : ℝ) < b / 3 by positivity)),
    eventually_gt_atTop 1] with X hX1 hX2 hX3 hX4
  have hle : propn (window A X) (fun n => (f n : ℝ) ≤ (κ + η n) * Real.log n) ≤
      propn (window A X) (fun n => normalised f κ V X n ≤ -M) +
      (propn (window A X) (fun n => n < N₀) +
        propn (window A X) (fun n => 3 / 4 * Real.log X < Real.log X - Real.log n)) := by
    refine (propn_le_add (q := fun n => normalised f κ V X n ≤ -M)
      (r := fun n => n < N₀ ∨ 3 / 4 * Real.log X < Real.log X - Real.log n)
      fun n hn hE => ?_).trans ?_
    · by_cases h1 : n < N₀
      · exact Or.inr (Or.inl h1)
      by_cases h2 : 3 / 4 * Real.log X < Real.log X - Real.log n
      · exact Or.inr (Or.inr h2)
      left
      push Not at h1 h2
      have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX4)
      have hln4 : Real.log X / 4 ≤ Real.log n := by linarith
      have hln0 : 0 ≤ Real.log n := by linarith
      have hsq := sqrt_log_half_le hln4
      have hηn : η n * √(Real.log n) ≤ -(2 * √V * M) := hN₀ n h1
      have hs : 0 < √(V * Real.log X) := Real.sqrt_pos.mpr (by positivity)
      have hprod : η n * Real.log n ≤ -M * √(V * Real.log X) := by
        have e1 : η n * Real.log n = (η n * √(Real.log n)) * √(Real.log n) := by
          rw [mul_assoc, Real.mul_self_sqrt hln0]
        have e2 : -M * √(V * Real.log X) = (-(2 * √V * M)) * (√(Real.log X) / 2) := by
          rw [Real.sqrt_mul hV.le]; ring
        rw [e1, e2]
        calc (η n * √(Real.log n)) * √(Real.log n) ≤ (-(2 * √V * M)) * √(Real.log n) :=
              mul_le_mul_of_nonneg_right hηn (Real.sqrt_nonneg _)
          _ ≤ (-(2 * √V * M)) * (√(Real.log X) / 2) :=
              mul_le_mul_of_nonpos_left hsq (by have := Real.sqrt_nonneg V; nlinarith)
      unfold normalised
      rw [div_le_iff₀ hs]
      rw [add_mul] at hE
      linarith
    · gcongr
      exact propn_or_le _ _ _
  have hX1' : propn (window A X) (fun n => normalised f κ V X n ≤ -M) < b / 3 := hX1
  linarith

/-- **Corollary 1.2 [`cor:rates`] for a population.** If `A` has density `p > 0` and
`(f(N_X) - κ log N_X)/√(V log X) ⇒ N(0,1)` under uniform sampling from `A ∩ [1, X]`, then the sets
`{n ∈ A : f(n) ≤ c₀ log n}`, `{n ∈ A : f(n) ≤ κ log n + z √(V log n)}` and
`{n ∈ A : f(n) ≤ (κ + η(n)) log n}` have the densities of Corollary 1.2. -/
theorem rates_of_cltOn {p : ℝ} (hV : 0 < V) (hp0 : 0 < p) (hp : HasDensity A p)
    (h : CLTOn A (normalised f κ V)) :
    (∀ c₀ : ℝ, HasDensity {n | n ∈ A ∧ (f n : ℝ) ≤ c₀ * Real.log n}
      (if κ < c₀ then p else if c₀ = κ then p / 2 else 0)) ∧
    (∀ z : ℝ, HasDensity {n | n ∈ A ∧ (f n : ℝ) ≤ κ * Real.log n + z * √(V * Real.log n)}
      (Φ z * p)) ∧
    (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(Real.log x)) atTop atTop →
      HasDensity {n | n ∈ A ∧ (f n : ℝ) ≤ (κ + η n) * Real.log n} p) ∧
    (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(Real.log x)) atTop atBot →
      HasDensity {n | n ∈ A ∧ (f n : ℝ) ≤ (κ + η n) * Real.log n} 0) := by
  have hpos := hp.posLower hp0
  have hz : ∀ z : ℝ, HasDensity {n | n ∈ A ∧ (f n : ℝ) ≤ κ * Real.log n + z * √(V * Real.log n)}
      (Φ z * p) := fun z => hasDensity_of_propn_window hp (propn_rate_z hV hpos h z)
  have htop : ∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(Real.log x)) atTop atTop →
      HasDensity {n | n ∈ A ∧ (f n : ℝ) ≤ (κ + η n) * Real.log n} p := fun η hη => by
    simpa using hasDensity_of_propn_window hp (propn_rate_top hV hpos h hη)
  have hbot : ∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(Real.log x)) atTop atBot →
      HasDensity {n | n ∈ A ∧ (f n : ℝ) ≤ (κ + η n) * Real.log n} 0 := fun η hη => by
    simpa using hasDensity_of_propn_window hp (propn_rate_bot hV hpos h hη)
  have hsqrt : Tendsto (fun x : ℝ => √(Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  refine ⟨fun c₀ => ?_, hz, htop, hbot⟩
  split_ifs with h1 h2
  · simpa only [add_sub_cancel] using
      htop (fun _ => c₀ - κ) (hsqrt.const_mul_atTop (sub_pos.mpr h1))
  · have := hz 0
    rw [Φ_zero] at this
    simp only [zero_mul, add_zero] at this
    rw [h2]
    convert this using 1
    ring
  · have h3 : c₀ - κ < 0 := sub_neg.mpr (lt_of_le_of_ne (not_lt.mp h1) h2)
    simpa only [add_sub_cancel] using hbot (fun _ => c₀ - κ) (hsqrt.const_mul_atTop_of_neg h3)

/-! ## Density among the odd integers -/

lemma card_window_odd (X : ℕ) : (window {n | Odd n} X).card = (X + 1) / 2 := by
  classical
  have : window {n | Odd n} X = (Icc 1 X).filter Odd := by
    ext n
    simp [mem_window]
  rw [this, card_filter_odd_Icc]
  omega

lemma tendsto_card_window_odd :
    Tendsto (fun X : ℕ => ((window {n | Odd n} X).card : ℝ) / X) atTop (𝓝 (1 / 2)) := by
  have hlo : Tendsto (fun X : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) := tendsto_const_nhds
  have hhi : Tendsto (fun X : ℕ => (1 / 2 : ℝ) + 1 / X) atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with X hX
    have hXr : (0 : ℝ) < X := by exact_mod_cast hX
    rw [card_window_odd, le_div_iff₀ hXr]
    have : X ≤ 2 * ((X + 1) / 2) := by omega
    have : (X : ℝ) ≤ 2 * (((X + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  · filter_upwards [eventually_gt_atTop 0] with X hX
    have hXr : (0 : ℝ) < X := by exact_mod_cast hX
    rw [card_window_odd, div_le_iff₀ hXr]
    have : 2 * ((X + 1) / 2) ≤ X + 1 := by omega
    have : 2 * (((X + 1) / 2 : ℕ) : ℝ) ≤ X + 1 := by exact_mod_cast this
    have e : (1 / 2 + 1 / (X : ℝ)) * X = X / 2 + 1 := by field_simp
    rw [e]
    linarith

/-- For a set of odd integers, the density among the odd integers is twice the natural density. -/
lemma hasOddDensity_of_hasDensity {S : Set ℕ} {d : ℝ} (hd : HasDensity S d)
    (hodd : ∀ n ∈ S, Odd n) : HasOddDensity S (2 * d) := by
  have hw : ∀ X, window {n | n ∈ S ∧ Odd n} X = window S X := by
    intro X
    ext n
    simp only [mem_window, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hodd n h2⟩
  have := hd.div tendsto_card_window_odd (by norm_num)
  rw [show d / (1 / 2) = 2 * d by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hXr : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  simp only [Pi.div_apply]
  rw [hw X, div_div_div_cancel_right₀ hXr]

/-! ## Corollary 1.2 for the three clocks, from the imports -/

/-- **Corollary 1.2 [`cor:rates`], raw clock**, from Tao's imports and Rhin's measure. -/
theorem rates_T_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    ∃ p > 0, HasDensity (Pred T b) p ∧
      (∀ c₀ : ℝ, HasDensity {n | n ∈ Pred T b ∧ (hit T b n : ℝ) ≤ c₀ * Real.log n}
        (if κT < c₀ then p else if c₀ = κT then p / 2 else 0)) ∧
      (∀ z : ℝ, HasDensity
        {n | n ∈ Pred T b ∧ (hit T b n : ℝ) ≤ κT * Real.log n + z * √(VT * Real.log n)}
        (Φ z * p)) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(Real.log x)) atTop atTop →
        HasDensity {n | n ∈ Pred T b ∧ (hit T b n : ℝ) ≤ (κT + η n) * Real.log n} p) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(Real.log x)) atTop atBot →
        HasDensity {n | n ∈ Pred T b ∧ (hit T b n : ℝ) ≤ (κT + η n) * Real.log n} 0) := by
  obtain ⟨p, hp0, hp, hclt, -⟩ := clock_data_T hTM hTP hθ b hb h3
  exact ⟨p, hp0, hp, rates_of_cltOn VT_pos hp0 hp hclt⟩

/-- **Corollary 1.2 [`cor:rates`], shortcut clock**, from Tao's imports and Rhin's measure. -/
theorem rates_F_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    ∃ p > 0, HasDensity (Pred F b) p ∧
      (∀ c₀ : ℝ, HasDensity {n | n ∈ Pred F b ∧ (hit F b n : ℝ) ≤ c₀ * Real.log n}
        (if κF < c₀ then p else if c₀ = κF then p / 2 else 0)) ∧
      (∀ z : ℝ, HasDensity
        {n | n ∈ Pred F b ∧ (hit F b n : ℝ) ≤ κF * Real.log n + z * √(VF * Real.log n)}
        (Φ z * p)) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(Real.log x)) atTop atTop →
        HasDensity {n | n ∈ Pred F b ∧ (hit F b n : ℝ) ≤ (κF + η n) * Real.log n} p) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(Real.log x)) atTop atBot →
        HasDensity {n | n ∈ Pred F b ∧ (hit F b n : ℝ) ≤ (κF + η n) * Real.log n} 0) := by
  obtain ⟨p, hp0, hp, hclt, -⟩ := clock_data_F hTM hTP hθ b hb h3
  exact ⟨p, hp0, hp, rates_of_cltOn VF_pos hp0 hp hclt⟩

/-- **Corollary 1.2 [`cor:rates`], odd clock**, densities among the odd integers, from Tao's
imports and Rhin's measure. -/
theorem rates_U_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    ∃ p > 0, HasOddDensity (PredU b) p ∧
      (∀ c₀ : ℝ, HasOddDensity {n | n ∈ PredU b ∧ (hit U b n : ℝ) ≤ c₀ * Real.log n}
        (if κU < c₀ then p else if c₀ = κU then p / 2 else 0)) ∧
      (∀ z : ℝ, HasOddDensity
        {n | n ∈ PredU b ∧ (hit U b n : ℝ) ≤ κU * Real.log n + z * √(VU * Real.log n)}
        (Φ z * p)) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(Real.log x)) atTop atTop →
        HasOddDensity {n | n ∈ PredU b ∧ (hit U b n : ℝ) ≤ (κU + η n) * Real.log n} p) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(Real.log x)) atTop atBot →
        HasOddDensity {n | n ∈ PredU b ∧ (hit U b n : ℝ) ≤ (κU + η n) * Real.log n} 0) := by
  obtain ⟨p, hp0, hp, hclt, -⟩ := clock_data_U hTM hTP hθ b hb h3
  obtain ⟨h1, h2, h3', h4⟩ := rates_of_cltOn VU_pos hp0 hp hclt
  have hodd : ∀ {P : ℕ → Prop}, ∀ n ∈ {n | n ∈ PredU b ∧ P n}, Odd n := fun n hn => hn.1.2.1
  refine ⟨2 * p, by positivity, hasOddDensity_of_hasDensity hp (fun n hn => hn.2.1),
    fun c₀ => ?_, fun z => ?_, fun η hη => hasOddDensity_of_hasDensity (h3' η hη) hodd,
    fun η hη => ?_⟩
  · convert hasOddDensity_of_hasDensity (h1 c₀) hodd using 1
    split_ifs <;> ring
  · convert hasOddDensity_of_hasDensity (h2 z) hodd using 1
    ring
  · convert hasOddDensity_of_hasDensity (h4 η hη) hodd using 1
    ring

end CollatzCLT
