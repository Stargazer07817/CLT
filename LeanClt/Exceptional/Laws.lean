import LeanClt.Defs

/-!
# The sampling toolkit for Theorems 1.3, 6.7–6.8 and Corollaries 1.5–1.6

Everything here is unconditional: statements about finite samples of integers, with no orbit
dynamics. As planned in checkpoint 11, every statement is phrased through proportions of finite
samples (`window` and its relatives), never through the measure-theoretic laws; the only
measure theory used is about the normal distribution function `Φ` itself.

* **The normal distribution function**: `Φ` is continuous, monotone, between `0` and `1`, tends to
  `0` and `1` at `∓∞`, and `Φ 0 = 1/2`.
* **Proportions.** `propn W p = #{n ∈ W : p n} / #W` on a finite sample `W`, and `LawN W stat`:
  along the family of samples `W X`, the statistic `stat X ·` converges in law to `N(0, 1)`, in
  distribution-function form. `CLTOn A stat` is `LawN (window A) stat` (`cltOn_iff_lawN`).
  General families `W X` (not only `window A X`) are needed for Theorem 6.8(ii)
  [`thm:movingray`], whose population `P_T(a_{j(X)}) ∩ [1, X]` moves with `X`.
* **Density algebra**: nonnegativity, `≤ 1`, uniqueness, monotonicity, finite disjoint unions,
  differences of nested sets, complements in `ℕ_{>0}`, positive lower density from positive
  density, and density `0` for a dyadic ray `{2^j b}`.
* **Transfer of the CLT**:
  - `lawN_of_close` (Slutsky's step): an additive perturbation that is small in probability;
  - `lawN_of_uniform_close` and `cltOn_bounded_shift`: a deterministic small perturbation, e.g. a
    bounded change of the clock;
  - `cltOn_logX` and `cltOn_of_logX`: Lemma 6.5(iii) [`lem:sampling`], under positive lower
    density the centring `κ log N_X` may be replaced by `κ log X`, and back;
  - `lawN_of_tight_shift`: an integer shift that is tight, divided by `√(L X)` for any scale
    `L X → ∞` (for the CLT, `L X = V log X`);
  - `abs_propn_sub_le`, `lawN_of_approx`, `lawN_of_subfamily`, `cltOn_of_subsets`: the total-variation
    bound for a subsample, and the sandwich between a population and large subpopulations;
  - `tendsto_joint_of_cltOn` and `cltOn_pos_of_mixture`: the joint law of (class, statistic) under
    uniform sampling from `[1, X]`, and the mixture over a partition with weights summing to `1`
    (the truncation argument of Corollary 1.6 [`cor:unconditional`]);
  - `density_rate`: the densities `1, 1/2, 0` of `{τ ≤ c₀ log n}` from a CLT on all of `ℕ_{>0}`
    (the argument of Corollary 1.2 [`cor:rates`] for `N_X` uniform on `[1, X]`).
-/

open Real Filter Topology Finset ProbabilityTheory MeasureTheory

noncomputable section

namespace CollatzCLT

/-! ## The normal distribution function -/

lemma Φ_nonneg (z : ℝ) : 0 ≤ Φ z := cdf_nonneg _ z

lemma Φ_le_one (z : ℝ) : Φ z ≤ 1 := cdf_le_one _ z

lemma Φ_mono : Monotone Φ := monotone_cdf _

lemma tendsto_Φ_atTop : Tendsto Φ atTop (𝓝 1) := tendsto_cdf_atTop _

lemma tendsto_Φ_atBot : Tendsto Φ atBot (𝓝 0) := tendsto_cdf_atBot _

/-- `Φ` is continuous: the standard Gaussian has no atoms. -/
lemma continuous_Φ : Continuous Φ := by
  rw [continuous_iff_continuousAt]
  intro z
  set F := cdf (gaussianReal 0 1) with hF
  have hm : Monotone F := monotone_cdf _
  have hs : (gaussianReal 0 1 : Measure ℝ) {z} = 0 := by
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    exact measure_singleton z
  have h1 := F.measure_singleton z
  rw [hF, measure_cdf, hs] at h1
  have hle : Function.leftLim F z ≤ F z := hm.leftLim_le le_rfl
  have h0 : F z - Function.leftLim F z ≤ 0 := ENNReal.ofReal_eq_zero.mp h1.symm
  have hcont : ContinuousAt F z := by
    rw [hm.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
    linarith
  exact hcont

/-- `Φ(0) = 1/2`: the standard Gaussian is symmetric and has no atoms. -/
lemma Φ_zero : Φ 0 = 1 / 2 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  set μ : Measure ℝ := gaussianReal 0 1 with hμ
  have hsymm : μ.map (fun x => -x) = μ := by rw [hμ, gaussianReal_map_neg, neg_zero]
  have h1 : μ (Set.Iic 0) = μ (Set.Ici 0) := by
    conv_lhs => rw [← hsymm]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext x
    simp
  have h2 : μ (Set.Ici 0) = μ (Set.Ioi 0) := (measure_congr Ioi_ae_eq_Ici).symm
  have h3 : μ (Set.Iic 0) + μ (Set.Ioi 0) = 1 := by
    rw [← measure_union (Set.disjoint_left.mpr fun x h h' => by simp at h h'; linarith)
      measurableSet_Ioi, Set.Iic_union_Ioi, measure_univ]
  have hΦ : Φ 0 = μ.real (Set.Iic 0) := by simp [Φ, hμ, cdf_eq_real]
  have hsum : μ (Set.Iic 0) + μ (Set.Iic 0) = 1 := by
    have e : μ (Set.Ioi 0) = μ (Set.Iic 0) := by rw [← h2, ← h1]
    rw [e] at h3
    exact h3
  have hfin : μ (Set.Iic 0) ≠ ⊤ := measure_ne_top _ _
  have := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hfin hfin, ENNReal.toReal_one] at this
  rw [hΦ, Measure.real]
  linarith

/-- Continuity of `Φ` from the left of `z`, in the form used below. -/
lemma exists_Φ_sub_gt {z m : ℝ} (hm : m < Φ z) : ∃ η > 0, m < Φ (z - η) := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp (continuous_Φ.continuousAt (x := z))
    (Φ z - m) (by linarith)
  refine ⟨δ / 2, by positivity, ?_⟩
  have := h (show dist (z - δ / 2) z < δ by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  rw [Real.dist_eq, abs_lt] at this
  linarith [this.1]

/-- Continuity of `Φ` from the right of `z`, in the form used below. -/
lemma exists_Φ_add_lt {z m : ℝ} (hm : Φ z < m) : ∃ η > 0, Φ (z + η) < m := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp (continuous_Φ.continuousAt (x := z))
    (m - Φ z) (by linarith)
  refine ⟨δ / 2, by positivity, ?_⟩
  have := h (show dist (z + δ / 2) z < δ by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  rw [Real.dist_eq, abs_lt] at this
  linarith [this.2]

/-! ## Proportions on finite samples -/

open Classical in
/-- The proportion of a finite sample `W` satisfying `p`: `#{n ∈ W : p n} / #W` (`0` if `W = ∅`).
Under `N` uniform on `W`, this is `P(p N)`. -/
def propn (W : Finset ℕ) (p : ℕ → Prop) : ℝ := ((W.filter p).card : ℝ) / W.card

/-- **Convergence in law to `N(0,1)` along a family of finite samples.** If `N_X` is uniform on
`W X`, then `stat X N_X ⇒ N(0,1)`, in distribution-function form. -/
def LawN (W : ℕ → Finset ℕ) (stat : ℕ → ℕ → ℝ) : Prop :=
  ∀ z : ℝ, Tendsto (fun X : ℕ => propn (W X) (fun n => stat X n ≤ z)) atTop (𝓝 (Φ z))

/-- `CLTOn A` is `LawN` along the windows `A ∩ [1, X]`. -/
lemma cltOn_iff_lawN {A : Set ℕ} {stat : ℕ → ℕ → ℝ} : CLTOn A stat ↔ LawN (window A) stat :=
  Iff.rfl

lemma propn_nonneg (W : Finset ℕ) (p : ℕ → Prop) : 0 ≤ propn W p := by
  unfold propn
  positivity

lemma propn_le_one (W : Finset ℕ) (p : ℕ → Prop) : propn W p ≤ 1 := by
  classical
  unfold propn
  rcases Nat.eq_zero_or_pos W.card with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast card_filter_le _ _

lemma propn_mono {W : Finset ℕ} {p q : ℕ → Prop} (h : ∀ n ∈ W, p n → q n) :
    propn W p ≤ propn W q := by
  classical
  unfold propn
  refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card fun n hn => ?_))
    (Nat.cast_nonneg _)
  rw [mem_filter] at hn ⊢
  exact ⟨hn.1, h n hn.1 hn.2⟩

/-- `P(p ∨ q) ≤ P(p) + P(q)`. -/
lemma propn_or_le (W : Finset ℕ) (p q : ℕ → Prop) :
    propn W (fun n => p n ∨ q n) ≤ propn W p + propn W q := by
  classical
  unfold propn
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine le_trans (Nat.cast_le.mpr (card_le_card (t := W.filter p ∪ W.filter q) ?_)) ?_
  · intro n hn
    simp only [mem_filter] at hn
    rw [mem_union, mem_filter, mem_filter]
    rcases hn.2 with h | h
    · exact Or.inl ⟨hn.1, h⟩
    · exact Or.inr ⟨hn.1, h⟩
  · exact_mod_cast card_union_le _ _

/-- If `p` implies `q ∨ r` on `W`, then `P(p) ≤ P(q) + P(r)`. -/
lemma propn_le_add {W : Finset ℕ} {p q r : ℕ → Prop} (h : ∀ n ∈ W, p n → q n ∨ r n) :
    propn W p ≤ propn W q + propn W r :=
  (propn_mono h).trans (propn_or_le W q r)

/-- **Total variation for a subsample.** Passing from `W` to `W' ⊆ W` changes every proportion by
at most twice the missing relative mass. -/
lemma abs_propn_sub_le {W W' : Finset ℕ} (h : W' ⊆ W) (p : ℕ → Prop) :
    |propn W p - propn W' p| ≤ 2 * (((W.card : ℝ) - W'.card) / W.card) := by
  classical
  unfold propn
  have hsplit : (W.filter p).card = (W'.filter p).card + ((W \ W').filter p).card := by
    rw [← card_union_of_disjoint (disjoint_filter_filter disjoint_sdiff), ← filter_union,
      union_sdiff_of_subset h]
  have hb : ((W \ W').filter p).card ≤ W.card - W'.card :=
    (card_filter_le _ _).trans (card_sdiff_of_subset h).le
  have ha : (W'.filter p).card ≤ W'.card := card_filter_le _ _
  have hww : W'.card ≤ W.card := card_le_card h
  have ha' : ((W'.filter p).card : ℝ) ≤ W'.card := by exact_mod_cast ha
  have hb' : (((W \ W').filter p).card : ℝ) ≤ (W.card : ℝ) - W'.card := by
    have e : (((W.card - W'.card : ℕ)) : ℝ) = (W.card : ℝ) - W'.card := by
      rw [Nat.cast_sub hww]
    rw [← e]
    exact_mod_cast hb
  have hww' : (W'.card : ℝ) ≤ W.card := by exact_mod_cast hww
  have hab : ((W.filter p).card : ℝ) = ((W'.filter p).card : ℝ) + ((W \ W').filter p).card := by
    rw [hsplit]; push_cast; ring
  rw [hab]
  set a : ℝ := ((W'.filter p).card : ℝ)
  set b : ℝ := (((W \ W').filter p).card : ℝ)
  set w : ℝ := (W.card : ℝ)
  set w' : ℝ := (W'.card : ℝ)
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ w' by positivity) with hw' | hw'
  · -- `W'` is empty
    have ha0' : a = 0 := by linarith
    rw [← hw', div_zero, sub_zero, ha0', zero_add, sub_zero]
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ w by positivity) with hw | hw
    · rw [← hw]; simp
    · rw [abs_of_nonneg (by positivity), div_self hw.ne', div_le_iff₀ hw]
      linarith
  · have hw : 0 < w := lt_of_lt_of_le hw' hww'
    have e1 : a / w ≤ a / w' := div_le_div_of_nonneg_left ha0 hw' hww'
    have e2 : b / w ≤ (w - w') / w := by gcongr
    have e3 : a / w' - a / w ≤ (w - w') / w := by
      rw [div_sub_div _ _ hw'.ne' hw.ne', div_le_div_iff₀ (by positivity) hw]
      nlinarith [mul_le_mul_of_nonneg_left ha' (show 0 ≤ w - w' by linarith)]
    have e4 : 0 ≤ (w - w') / w := div_nonneg (by linarith) hw.le
    have e5 : 0 ≤ b / w := div_nonneg hb0 hw.le
    rw [abs_le, add_div]
    constructor <;> linarith

/-! ## Density algebra -/

lemma window_mono {A B : Set ℕ} (h : A ⊆ B) (X : ℕ) : window A X ⊆ window B X := by
  classical
  intro n hn
  unfold window at hn ⊢
  rw [mem_filter] at hn ⊢
  exact ⟨hn.1, h hn.2⟩

lemma card_window_le_nat (A : Set ℕ) (X : ℕ) : (window A X).card ≤ X := by
  classical
  unfold window
  exact (card_filter_le _ _).trans (by simp)

lemma mem_window {A : Set ℕ} {X n : ℕ} : n ∈ window A X ↔ (1 ≤ n ∧ n ≤ X) ∧ n ∈ A := by
  classical
  unfold window
  rw [mem_filter, mem_Icc]

/-- The window of the positive integers is `[1, X]`. -/
lemma window_pos (X : ℕ) : window {n | 0 < n} X = Icc 1 X := by
  ext n
  rw [mem_window, mem_Icc, Set.mem_ofPred_eq]
  omega

lemma card_window_pos (X : ℕ) : (window {n | 0 < n} X).card = X := by
  rw [window_pos]
  simp

lemma HasDensity.nonneg {A : Set ℕ} {d : ℝ} (h : HasDensity A d) : 0 ≤ d :=
  ge_of_tendsto' h fun X => by positivity

lemma HasDensity.le_one {A : Set ℕ} {d : ℝ} (h : HasDensity A d) : d ≤ 1 := by
  refine le_of_tendsto h ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  rw [div_le_one (by exact_mod_cast hX)]
  exact_mod_cast card_window_le_nat A X

lemma HasDensity.unique {A : Set ℕ} {d d' : ℝ} (h : HasDensity A d) (h' : HasDensity A d') :
    d = d' :=
  tendsto_nhds_unique h h'

lemma HasDensity.mono {A B : Set ℕ} {a b : ℝ} (hAB : A ⊆ B) (hA : HasDensity A a)
    (hB : HasDensity B b) : a ≤ b :=
  le_of_tendsto_of_tendsto' hA hB fun X => by
    gcongr
    exact window_mono hAB X

/-- Two sets that agree on the positive integers have the same density. -/
lemma HasDensity.congr_pos {A B : Set ℕ} {d : ℝ} (hAB : ∀ n, 0 < n → (n ∈ A ↔ n ∈ B))
    (h : HasDensity A d) : HasDensity B d := by
  have : ∀ X, window A X = window B X := by
    intro X
    ext n
    rw [mem_window, mem_window]
    constructor
    · rintro ⟨hn, hA⟩; exact ⟨hn, (hAB n (by omega)).mp hA⟩
    · rintro ⟨hn, hB⟩; exact ⟨hn, (hAB n (by omega)).mpr hB⟩
  unfold HasDensity at h ⊢
  simpa only [this] using h

lemma hasDensity_empty : HasDensity ∅ 0 := by
  unfold HasDensity window
  simp

lemma hasDensity_pos : HasDensity {n | 0 < n} 1 := by
  unfold HasDensity
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  rw [card_window_pos, div_self (by exact_mod_cast hX.ne')]

/-- **Disjoint union.** -/
lemma HasDensity.union {A B : Set ℕ} {a b : ℝ} (hdisj : Disjoint A B) (hA : HasDensity A a)
    (hB : HasDensity B b) : HasDensity (A ∪ B) (a + b) := by
  classical
  unfold HasDensity at *
  refine (hA.add hB).congr fun X => ?_
  have hw : window (A ∪ B) X = window A X ∪ window B X := by
    ext n
    simp only [mem_union, mem_window, Set.mem_union]
    tauto
  have hd : Disjoint (window A X) (window B X) := by
    rw [Finset.disjoint_left]
    intro n hA' hB'
    rw [mem_window] at hA' hB'
    exact Set.disjoint_left.mp hdisj hA'.2 hB'.2
  rw [hw, card_union_of_disjoint hd]
  push_cast
  ring

/-- **Finite disjoint unions.** -/
lemma hasDensity_biUnion {ι : Type*} (s : Finset ι) {S : ι → Set ℕ} {d : ι → ℝ}
    (hdisj : (s : Set ι).PairwiseDisjoint S) (h : ∀ i ∈ s, HasDensity (S i) (d i)) :
    HasDensity (⋃ i ∈ s, S i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDensity_empty
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have hset : (⋃ j ∈ insert i s, S j) = S i ∪ ⋃ j ∈ s, S j := by
      ext n
      simp
    rw [hset]
    refine HasDensity.union ?_ (h i (mem_insert_self i s))
      (ih (hdisj.subset (by simp)) fun j hj => h j (mem_insert_of_mem hj))
    rw [Set.disjoint_iUnion₂_right]
    intro j hj
    exact hdisj (by simp) (by simp [hj]) (fun hij => hi (hij ▸ hj))

/-- **Difference of nested sets.** -/
lemma HasDensity.diff {A B : Set ℕ} {a b : ℝ} (hAB : A ⊆ B) (hA : HasDensity A a)
    (hB : HasDensity B b) : HasDensity (B \ A) (b - a) := by
  have hu : HasDensity (A ∪ (B \ A)) b := by
    rwa [Set.union_sdiff_cancel hAB]
  unfold HasDensity at *
  refine (hB.sub hA).congr fun X => ?_
  have := HasDensity.union (A := A) (B := B \ A) (a := a) (b := 0) Set.disjoint_sdiff_right
  classical
  have hw : window B X = window A X ∪ window (B \ A) X := by
    ext n
    simp only [mem_union, mem_window, Set.mem_sdiff]
    constructor
    · rintro ⟨hn, hB'⟩
      by_cases hA' : n ∈ A
      · exact Or.inl ⟨hn, hA'⟩
      · exact Or.inr ⟨hn, hB', hA'⟩
    · rintro (⟨hn, hA'⟩ | ⟨hn, hB', -⟩)
      · exact ⟨hn, hAB hA'⟩
      · exact ⟨hn, hB'⟩
  have hd : Disjoint (window A X) (window (B \ A) X) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    rw [mem_window] at h1 h2
    exact h2.2.2 h1.2
  rw [hw, card_union_of_disjoint hd]
  push_cast
  ring

/-- **Complement in the positive integers.** -/
lemma HasDensity.compl_pos {A : Set ℕ} {a : ℝ} (hA : HasDensity A a) :
    HasDensity {n | 0 < n ∧ n ∉ A} (1 - a) := by
  have h := HasDensity.diff (A := {n | 0 < n} ∩ A) (B := {n | 0 < n})
    Set.inter_subset_left (hA.congr_pos fun n hn => by simp [hn]) hasDensity_pos
  refine h.congr_pos fun n hn => ?_
  simp [hn]

/-- **Positive density gives positive lower density.** -/
lemma HasDensity.posLower {A : Set ℕ} {d : ℝ} (h : HasDensity A d) (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window A X).card : ℝ) := by
  refine ⟨d / 2, by positivity, ?_⟩
  filter_upwards [h.eventually (lt_mem_nhds (show d / 2 < d by linarith)),
    eventually_gt_atTop 0] with X hX hX0
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX0
  rw [lt_div_iff₀ hXpos] at hX
  exact hX.le

/-- A set whose windows have `o(X)` points has density `0`. -/
lemma hasDensity_zero_of_le {A : Set ℕ} {g : ℕ → ℝ}
    (hg : Tendsto (fun X : ℕ => g X / X) atTop (𝓝 0))
    (hle : ∀ᶠ X : ℕ in atTop, ((window A X).card : ℝ) ≤ g X) : HasDensity A 0 := by
  unfold HasDensity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Eventually.of_forall fun X => by positivity) ?_
  filter_upwards [hle] with X hX
  gcongr

/-- **A dyadic ray `{2^j b}` has density `0`** (`b > 0`). It has at most `log₂ X + 1` points in
`[1, X]`. Used for the ray points divisible by 3 in Theorem 6.7 [`thm:rayentry`]. -/
lemma hasDensity_dyadic {b : ℕ} (hb : 0 < b) : HasDensity {n | ∃ j, n = 2 ^ j * b} 0 := by
  classical
  refine hasDensity_zero_of_le (g := fun X => Real.log X / Real.log 2 + 1) ?_ ?_
  · have h1 : Tendsto (fun X : ℕ => Real.log X / X) atTop (𝓝 0) := by
      have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun X : ℕ => (1 : ℝ) / X) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have := (h1.div_const (Real.log 2)).add h2
    simp only [zero_div, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    have hX' : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
    field_simp
  · filter_upwards [eventually_gt_atTop 0] with X hX
    -- the window lies in the image of `j ↦ 2^j b` over `j ≤ log₂ X`
    have hsub : window {n | ∃ j, n = 2 ^ j * b} X ⊆
        (range (Nat.log 2 X + 1)).image (fun j => 2 ^ j * b) := by
      intro n hn
      rw [mem_window] at hn
      obtain ⟨⟨-, hnX⟩, j, rfl⟩ := hn
      refine mem_image.mpr ⟨j, mem_range.mpr ?_, rfl⟩
      have h2j : 2 ^ j ≤ X := le_trans (Nat.le_mul_of_pos_right _ hb) hnX
      exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by norm_num) h2j)
    have hcard := (card_le_card hsub).trans card_image_le
    rw [card_range] at hcard
    have hlog : (Nat.log 2 X : ℝ) ≤ Real.log X / Real.log 2 := by
      have := Real.natLog_le_logb X 2
      rwa [Real.logb] at this
    calc ((window {n | ∃ j, n = 2 ^ j * b} X).card : ℝ) ≤ ((Nat.log 2 X + 1 : ℕ) : ℝ) := by
          exact_mod_cast hcard
      _ ≤ Real.log X / Real.log 2 + 1 := by push_cast; linarith

/-! ## More on proportions -/

lemma propn_congr {W : Finset ℕ} {p q : ℕ → Prop} (h : ∀ n ∈ W, (p n ↔ q n)) :
    propn W p = propn W q :=
  le_antisymm (propn_mono fun n hn hp => (h n hn).mp hp) (propn_mono fun n hn hq => (h n hn).mpr hq)

lemma propn_eq_zero {W : Finset ℕ} {p : ℕ → Prop} (h : ∀ n ∈ W, ¬ p n) : propn W p = 0 := by
  classical
  unfold propn
  rw [Finset.filter_false_of_mem h]
  simp

/-- A proportion is at most the size of any set containing the counted points, over `#W`. -/
lemma propn_le_of_subset {W S : Finset ℕ} {p : ℕ → Prop} (h : ∀ n ∈ W, p n → n ∈ S) :
    propn W p ≤ (S.card : ℝ) / W.card := by
  classical
  unfold propn
  refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card fun n hn => ?_))
    (Nat.cast_nonneg _)
  rw [mem_filter] at hn
  exact h n hn.1 hn.2

lemma tendsto_propn_zero {W : ℕ → Finset ℕ} {p : ℕ → ℕ → Prop} {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 0)) (hle : ∀ᶠ X : ℕ in atTop, propn (W X) (p X) ≤ g X) :
    Tendsto (fun X => propn (W X) (p X)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Eventually.of_forall fun _ => propn_nonneg _ _) hle

lemma card_Icc_one (k : ℕ) : (Icc 1 k).card = k := by simp

/-- `√(V log X) → ∞`. -/
lemma tendsto_sqrt_log {V : ℝ} (hV : 0 < V) :
    Tendsto (fun X : ℕ => √(V * Real.log X)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hV)

/-- `b √(V log X) + c ≤ a log X` for large `X`, when `a > 0`: the Gaussian scale is `o(log X)`. -/
lemma eventually_sqrt_log_le {V a : ℝ} (hV : 0 < V) (ha : 0 < a) (b c : ℝ) :
    ∀ᶠ X : ℕ in atTop, b * √(V * Real.log X) + c ≤ a * Real.log X := by
  set K := max 1 (((|b| * √V + |c|) / a) ^ 2) with hK
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop K)] with X hX
  simp only [Function.comp_apply] at hX
  set L := Real.log X with hL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hX
  have hL0 : 0 ≤ L := by linarith
  set t := √L with ht
  have ht1 : 1 ≤ t := by rw [ht, show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hL1
  have ht2 : (|b| * √V + |c|) / a ≤ t := by
    have h1 : ((|b| * √V + |c|) / a) ^ 2 ≤ L := le_trans (le_max_right _ _) hX
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  have htt : t * t = L := Real.mul_self_sqrt hL0
  have hsq : √(V * L) = √V * t := Real.sqrt_mul hV.le L
  rw [hsq]
  have hb : b * (√V * t) ≤ |b| * √V * t := by
    have := mul_le_mul_of_nonneg_right (le_abs_self b) (by positivity : 0 ≤ √V * t)
    linarith
  have hc : c ≤ |c| * t := by nlinarith [le_abs_self c, abs_nonneg c]
  have hfin : (|b| * √V + |c|) * t ≤ a * L := by
    rw [div_le_iff₀ ha] at ht2
    nlinarith [Real.sqrt_nonneg V, abs_nonneg b, abs_nonneg c]
  nlinarith

/-- Among the integers of `[1, X]`, at most `e^{-R} X` are `≤ e^{-R} X`. -/
lemma propn_small_le {X : ℕ} (hX : 0 < X) (R : ℝ) :
    propn (window {n | 0 < n} X) (fun n => (n : ℝ) ≤ X * Real.exp (-R)) ≤ Real.exp (-R) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  refine (propn_le_of_subset (S := Icc 1 ⌊(X : ℝ) * Real.exp (-R)⌋₊) fun n hn hle => ?_).trans ?_
  · rw [window_pos, mem_Icc] at hn
    exact mem_Icc.mpr ⟨hn.1, Nat.le_floor hle⟩
  · rw [card_Icc_one, card_window_pos, div_le_iff₀ hXr]
    have := Nat.floor_le (show (0 : ℝ) ≤ X * Real.exp (-R) by positivity)
    linarith

/-! ## Transfer of the CLT -/

/-- **Slutsky's step.** If `stat X N_X ⇒ N(0,1)` and `stat' - stat → 0` in probability along the
samples, then `stat' X N_X ⇒ N(0,1)`. -/
theorem lawN_of_close {W : ℕ → Finset ℕ} {stat stat' : ℕ → ℕ → ℝ} (h : LawN W stat)
    (hclose : ∀ ε > 0, Tendsto (fun X : ℕ =>
      propn (W X) (fun n => ε < |stat' X n - stat X n|)) atTop (𝓝 0)) :
    LawN W stat' := by
  intro z
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨η, hη, hηΦ⟩ := exists_Φ_sub_gt (show (a + Φ z) / 2 < Φ z by linarith)
    have h1 := (h (z - η)).eventually (lt_mem_nhds hηΦ)
    have h2 := (hclose η hη).eventually
      (gt_mem_nhds (show (0 : ℝ) < (a + Φ z) / 2 - a by linarith))
    filter_upwards [h1, h2] with X hX1 hX2
    have hle : propn (W X) (fun n => stat X n ≤ z - η) ≤
        propn (W X) (fun n => stat' X n ≤ z) +
          propn (W X) (fun n => η < |stat' X n - stat X n|) := by
      refine propn_le_add fun n _ hn => ?_
      by_cases hd : η < |stat' X n - stat X n|
      · exact Or.inr hd
      · left
        push Not at hd
        have := (abs_le.mp hd).2
        linarith
    linarith
  · obtain ⟨η, hη, hηΦ⟩ := exists_Φ_add_lt (show Φ z < (b + Φ z) / 2 by linarith)
    have h1 := (h (z + η)).eventually (gt_mem_nhds hηΦ)
    have h2 := (hclose η hη).eventually
      (gt_mem_nhds (show (0 : ℝ) < b - (b + Φ z) / 2 by linarith))
    filter_upwards [h1, h2] with X hX1 hX2
    have hle : propn (W X) (fun n => stat' X n ≤ z) ≤
        propn (W X) (fun n => stat X n ≤ z + η) +
          propn (W X) (fun n => η < |stat' X n - stat X n|) := by
      refine propn_le_add fun n _ hn => ?_
      by_cases hd : η < |stat' X n - stat X n|
      · exact Or.inr hd
      · left
        push Not at hd
        have := (abs_le.mp hd).1
        linarith
    linarith

/-- **A deterministic small perturbation** does not affect the limit law. -/
theorem lawN_of_uniform_close {W : ℕ → Finset ℕ} {stat stat' : ℕ → ℕ → ℝ} {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0))
    (hclose : ∀ᶠ X : ℕ in atTop, ∀ n ∈ W X, |stat' X n - stat X n| ≤ e X)
    (h : LawN W stat) : LawN W stat' := by
  refine lawN_of_close h fun ε hε => tendsto_const_nhds.congr' ?_
  filter_upwards [hclose, he.eventually (gt_mem_nhds hε)] with X hX hXe
  exact (propn_eq_zero fun n hn hlt => by linarith [hX n hn]).symm

/-- **A bounded change of the clock** does not affect the CLT (`|f - g| ≤ B` on `A`). -/
theorem cltOn_bounded_shift {A : Set ℕ} {f g : ℕ → ℕ} {κ V : ℝ} (hV : 0 < V) (B : ℕ)
    (hfg : ∀ n ∈ A, f n ≤ g n + B ∧ g n ≤ f n + B)
    (h : CLTOn A (normalised f κ V)) : CLTOn A (normalised g κ V) := by
  refine lawN_of_uniform_close (e := fun X => (B : ℝ) / √(V * Real.log X))
    (tendsto_const_nhds.div_atTop (tendsto_sqrt_log hV)) (Eventually.of_forall fun X n hn => ?_) h
  have hnA : n ∈ A := (mem_window.mp hn).2
  obtain ⟨h1, h2⟩ := hfg n hnA
  have h1' : (f n : ℝ) ≤ g n + B := by exact_mod_cast h1
  have h2' : (g n : ℝ) ≤ f n + B := by exact_mod_cast h2
  have hd : |(g n : ℝ) - f n| ≤ B := abs_le.mpr ⟨by linarith, by linarith⟩
  unfold normalised
  rw [← sub_div, show ((g n : ℝ) - κ * log n) - ((f n : ℝ) - κ * log n) = (g n : ℝ) - f n by ring,
    abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right hd (Real.sqrt_nonneg _)

/-- Under positive lower density, the centrings `κ log n` and `κ log X` are close in probability:
the proportion of `n ∈ A ∩ [1, X]` where they differ by more than `ε √(V log X)` is at most
`e^{-R}/c` with `R → ∞`. -/
lemma close_logX {A : Set ℕ} {f : ℕ → ℕ} {κ V : ℝ} (hV : 0 < V)
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window A X).card : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun X : ℕ => propn (window A X) (fun n =>
      ε < |((f n : ℝ) - κ * Real.log X) / √(V * Real.log X) - normalised f κ V X n|))
      atTop (𝓝 0) := by
  obtain ⟨c, hc, hcX⟩ := hpos
  set R : ℕ → ℝ := fun X => ε * √(V * Real.log X) / (|κ| + 1) with hR
  have hRlim : Tendsto R atTop atTop :=
    ((tendsto_sqrt_log hV).const_mul_atTop hε).atTop_div_const (by positivity)
  have hg : Tendsto (fun X => Real.exp (-R X) / c) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hRlim).div_const c
    simpa [Function.comp_def] using this
  refine tendsto_propn_zero hg ?_
  filter_upwards [hcX, eventually_ge_atTop 2] with X hX hX2
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX2
  have hX0 : (0 : ℝ) < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hs : 0 < √(V * Real.log X) := Real.sqrt_pos.mpr (by positivity)
  have hW : 0 < ((window A X).card : ℝ) := lt_of_lt_of_le (by positivity) hX
  refine (propn_le_of_subset (S := Icc 1 ⌊(X : ℝ) * Real.exp (-R X)⌋₊) fun n hn hlt => ?_).trans ?_
  · obtain ⟨⟨hn1, hnX⟩, -⟩ := mem_window.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlogn : Real.log n ≤ Real.log X := Real.log_le_log hn0 (by exact_mod_cast hnX)
    have hdiff : ((f n : ℝ) - κ * Real.log X) / √(V * Real.log X) - normalised f κ V X n =
        κ * (Real.log n - Real.log X) / √(V * Real.log X) := by
      unfold normalised
      ring
    rw [hdiff, abs_div, abs_of_pos hs, lt_div_iff₀ hs, abs_mul,
      abs_of_nonpos (by linarith : Real.log n - Real.log X ≤ 0)] at hlt
    have h1 : R X < Real.log X - Real.log n := by
      change ε * √(V * Real.log X) / (|κ| + 1) < _
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg κ]
    have h2 : (n : ℝ) < X * Real.exp (-R X) := by
      rw [← Real.exp_log hn0, ← Real.exp_log hX0, ← Real.exp_add]
      exact Real.exp_lt_exp.mpr (by linarith)
    exact mem_Icc.mpr ⟨hn1, Nat.le_floor h2.le⟩
  · rw [card_Icc_one]
    have hfl := Nat.floor_le (show (0 : ℝ) ≤ X * Real.exp (-R X) by positivity)
    calc (⌊(X : ℝ) * Real.exp (-R X)⌋₊ : ℝ) / (window A X).card
        ≤ (X * Real.exp (-R X)) / (c * X) := div_le_div₀ (by positivity) hfl (by positivity) hX
      _ = Real.exp (-R X) / c := by field_simp

/-- **Lemma 6.5(iii) [`lem:sampling`], from `log N_X` to `log X`.** Under positive lower density,
the centring `κ log N_X` may be replaced by `κ log X`. -/
theorem cltOn_logX {A : Set ℕ} {f : ℕ → ℕ} {κ V : ℝ} (hV : 0 < V)
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window A X).card : ℝ))
    (h : CLTOn A (normalised f κ V)) :
    CLTOn A (fun X n => ((f n : ℝ) - κ * Real.log X) / √(V * Real.log X)) :=
  lawN_of_close h fun _ hε => close_logX hV hpos hε

/-- **Lemma 6.5(iii) [`lem:sampling`], from `log X` to `log N_X`** (the direction stated in the
paper). -/
theorem cltOn_of_logX {A : Set ℕ} {f : ℕ → ℕ} {κ V : ℝ} (hV : 0 < V)
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window A X).card : ℝ))
    (h : CLTOn A (fun X n => ((f n : ℝ) - κ * Real.log X) / √(V * Real.log X))) :
    CLTOn A (normalised f κ V) := by
  refine lawN_of_close h fun ε hε => (close_logX (f := f) (κ := κ) hV hpos hε).congr fun X => ?_
  exact propn_congr fun n _ => by rw [abs_sub_comm]

/-- **Slutsky's step for a tight integer shift.** If `|stat' - stat| ≤ s(n)/√(L X)` with
`L X → ∞` and `s(N_X)` tight along the samples, the limit law is unchanged. -/
theorem lawN_of_tight_shift {W : ℕ → Finset ℕ} {stat stat' : ℕ → ℕ → ℝ} {s : ℕ → ℕ}
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hdiff : ∀ᶠ X : ℕ in atTop, ∀ n ∈ W X, |stat' X n - stat X n| ≤ s n / √(L X))
    (htight : ∀ ε > 0, ∃ j0 : ℕ, ∀ᶠ X : ℕ in atTop, propn (W X) (fun n => j0 < s n) ≤ ε)
    (h : LawN W stat) : LawN W stat' := by
  refine lawN_of_close h fun ε hε => ?_
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun X => lt_of_lt_of_le ha (propn_nonneg _ _),
    fun b hb => ?_⟩
  obtain ⟨j0, hj0⟩ := htight (b / 2) (by positivity)
  have hLj : ∀ᶠ X : ℕ in atTop, (j0 : ℝ) < ε * √(L X) :=
    ((Real.tendsto_sqrt_atTop.comp hL).const_mul_atTop hε).eventually (eventually_gt_atTop _)
  filter_upwards [hdiff, hj0, hLj] with X hX1 hX2 hX3
  have hs : 0 < √(L X) := by
    have h0 : 0 < ε * √(L X) := lt_of_le_of_lt (Nat.cast_nonneg _) hX3
    exact (mul_pos_iff_of_pos_left hε).mp h0
  refine lt_of_le_of_lt (propn_mono (q := fun n => j0 < s n) fun n hn hlt => ?_)
    (lt_of_le_of_lt hX2 (by linarith))
  have h1 := lt_of_lt_of_le hlt (hX1 n hn)
  rw [lt_div_iff₀ hs] at h1
  exact_mod_cast (lt_trans hX3 h1 : (j0 : ℝ) < s n)

/-! ## Large subsamples -/

lemma two_deficit_le {W W' : Finset ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : (W.card : ℝ) - W'.card ≤ ε * W.card) :
    2 * (((W.card : ℝ) - W'.card) / W.card) ≤ 2 * ε := by
  rcases Nat.eq_zero_or_pos W.card with h0 | h0
  · simp [h0]
    linarith
  · have : (0 : ℝ) < W.card := by exact_mod_cast h0
    gcongr
    rwa [div_le_iff₀ this]

/-- **The sandwich lemma.** If the samples `W X` can be approximated, up to any fraction `ε` of their
mass, by subsamples along which the CLT holds, then the CLT holds along `W X`. -/
theorem lawN_of_approx {W : ℕ → Finset ℕ} {stat : ℕ → ℕ → ℝ}
    (h : ∀ ε > 0, ∃ W' : ℕ → Finset ℕ, (∀ X, W' X ⊆ W X) ∧ LawN W' stat ∧
      ∀ᶠ X : ℕ in atTop, ((W X).card : ℝ) - (W' X).card ≤ ε * (W X).card) :
    LawN W stat := by
  intro z
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨W', hsub, hlaw, hdef⟩ := h (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hlaw z) (ε / 2) (by positivity)
  obtain ⟨N', hN'⟩ := eventually_atTop.mp hdef
  refine ⟨max N N', fun X hX => ?_⟩
  have h1 := abs_propn_sub_le (hsub X) (fun n => stat X n ≤ z)
  have h2 := two_deficit_le (by positivity) (hN' X (le_of_max_le_right hX))
  have h3 := hN X (le_of_max_le_left hX)
  rw [Real.dist_eq] at h3 ⊢
  calc |propn (W X) (fun n => stat X n ≤ z) - Φ z|
      ≤ |propn (W X) (fun n => stat X n ≤ z) - propn (W' X) (fun n => stat X n ≤ z)| +
        |propn (W' X) (fun n => stat X n ≤ z) - Φ z| := abs_sub_le _ _ _
    _ < ε := by linarith

/-- **Restriction to a large subsample.** If the subsamples `W' X ⊆ W X` miss a vanishing
fraction of `W X`, the CLT along `W X` passes to `W' X`. This is the total-variation step of
Theorem 6.8(ii) [`thm:movingray`]. -/
theorem lawN_of_subfamily {W W' : ℕ → Finset ℕ} {stat : ℕ → ℕ → ℝ} (hsub : ∀ X, W' X ⊆ W X)
    (hdef : ∀ ε > 0, ∀ᶠ X : ℕ in atTop, ((W X).card : ℝ) - (W' X).card ≤ ε * (W X).card)
    (h : LawN W stat) : LawN W' stat := by
  intro z
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h z) (ε / 2) (by positivity)
  obtain ⟨N', hN'⟩ := eventually_atTop.mp (hdef (ε / 4) (by positivity))
  refine ⟨max N N', fun X hX => ?_⟩
  have h1 := abs_propn_sub_le (hsub X) (fun n => stat X n ≤ z)
  have h2 := two_deficit_le (by positivity) (hN' X (le_of_max_le_right hX))
  have h3 := hN X (le_of_max_le_left hX)
  rw [Real.dist_eq] at h3 ⊢
  rw [abs_sub_comm] at h1
  calc |propn (W' X) (fun n => stat X n ≤ z) - Φ z|
      ≤ |propn (W' X) (fun n => stat X n ≤ z) - propn (W X) (fun n => stat X n ≤ z)| +
        |propn (W X) (fun n => stat X n ≤ z) - Φ z| := abs_sub_le _ _ _
    _ < ε := by linarith

/-- The sandwich lemma for sets: a CLT on a set `C` from CLTs on subsets `A_j ⊆ C` whose relative
mass in `C` can be made arbitrarily close to `1` (proof of Theorem 6.7 [`thm:rayentry`]). -/
theorem cltOn_of_subsets {C : Set ℕ} {A : ℕ → Set ℕ} {stat : ℕ → ℕ → ℝ} (hA : ∀ j, A j ⊆ C)
    (hclt : ∀ j, CLTOn (A j) stat)
    (hmass : ∀ ε > 0, ∃ j, ∀ᶠ X : ℕ in atTop,
      ((window C X).card : ℝ) - (window (A j) X).card ≤ ε * (window C X).card) :
    CLTOn C stat :=
  lawN_of_approx fun ε hε =>
    let ⟨j, hj⟩ := hmass ε hε
    ⟨window (A j), fun X => window_mono (hA j) X, hclt j, hj⟩

/-- The mass condition of `cltOn_of_subsets` from densities: if `dens C = p` and
`dens A = a` with `p - a < ε p`, then eventually `#(C ∩ [1,X]) - #(A ∩ [1,X]) ≤ ε #(C ∩ [1,X])`. -/
lemma deficit_of_hasDensity {A C : Set ℕ} {a p ε : ℝ} (hA : HasDensity A a) (hC : HasDensity C p)
    (hε : p - a < ε * p) :
    ∀ᶠ X : ℕ in atTop, ((window C X).card : ℝ) - (window A X).card ≤ ε * (window C X).card := by
  have hlim : Tendsto (fun X : ℕ => ((window C X).card : ℝ) / X - (window A X).card / X -
      ε * (((window C X).card : ℝ) / X)) atTop (𝓝 (p - a - ε * p)) :=
    (hC.sub hA).sub (hC.const_mul ε)
  filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : p - a - ε * p < 0)),
    eventually_gt_atTop 0] with X hX hX0
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX0
  have : (((window C X).card : ℝ) - (window A X).card - ε * (window C X).card) / X < 0 := by
    rw [sub_div, sub_div, mul_div_assoc]
    exact hX
  rw [div_lt_iff₀ hXr, zero_mul] at this
  linarith

/-! ## Joint laws and mixtures under uniform sampling from `[1, X]` -/

open Classical in
/-- **Joint law of (membership, statistic)** under `N_X` uniform on `[1, X]`: if `dens A = p` and the
CLT holds on `A`, then `P(N_X ∈ A, stat ≤ z) → p Φ(z)`. -/
theorem tendsto_joint_of_cltOn {A : Set ℕ} {p : ℝ} {stat : ℕ → ℕ → ℝ} (hA : HasDensity A p)
    (h : CLTOn A stat) (z : ℝ) :
    Tendsto (fun X : ℕ => (((Icc 1 X).filter (fun n => n ∈ A ∧ stat X n ≤ z)).card : ℝ) / X)
      atTop (𝓝 (p * Φ z)) := by
  refine (hA.mul (h z)).congr fun X => ?_
  have hc : ((Icc 1 X).filter (fun n => n ∈ A ∧ stat X n ≤ z)).card =
      ((window A X).filter (fun n => stat X n ≤ z)).card := by
    unfold window
    rw [filter_filter]
  rw [hc]
  rcases Nat.eq_zero_or_pos (window A X).card with h0 | h0
  · have h0' : ((window A X).filter (fun n => stat X n ≤ z)).card = 0 :=
      Nat.eq_zero_of_le_zero (h0 ▸ card_filter_le _ _)
    rw [h0, h0']
    simp
  · have : ((window A X).card : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    field_simp

open Classical in
/-- **The mixture over a partition** (the truncation argument of Corollary 1.6
[`cor:unconditional`]). If disjoint sets `S i` have densities `wt i` summing to `1`, and under `N_X`
uniform on `[1, X]` the joint law `P(N_X ∈ S i, stat ≤ z) → wt i Φ(z)` for every `i`, then
`stat ⇒ N(0,1)` under uniform sampling from `[1, X]`. -/
theorem cltOn_pos_of_mixture {ι : Type*} {S : ι → Set ℕ} {wt : ι → ℝ} {stat : ℕ → ℕ → ℝ}
    (hdisj : Pairwise fun i j => Disjoint (S i) (S j)) (hdens : ∀ i, HasDensity (S i) (wt i)) (hsum : HasSum wt 1)
    (hjoint : ∀ i z, Tendsto (fun X : ℕ =>
      (((Icc 1 X).filter (fun n => n ∈ S i ∧ stat X n ≤ z)).card : ℝ) / X) atTop
      (𝓝 (wt i * Φ z))) :
    CLTOn {n | 0 < n} stat := by
  intro z
  -- the joint proportions `J i` and the densities `D i`
  set J : ι → ℕ → ℝ := fun i X =>
    (((Icc 1 X).filter (fun n => n ∈ S i ∧ stat X n ≤ z)).card : ℝ) / X with hJ
  set D : ι → ℕ → ℝ := fun i X => ((window (S i) X).card : ℝ) / X with hD
  set G : ℕ → ℝ := fun X => (((window {n | 0 < n} X).filter (fun n => stat X n ≤ z)).card : ℝ) /
    (window {n | 0 < n} X).card with hG
  change Tendsto G atTop (𝓝 (Φ z))
  have hdisjF : ∀ (F : Finset ι) X, (F : Set ι).PairwiseDisjoint
      (fun i => (Icc 1 X).filter (fun n => n ∈ S i ∧ stat X n ≤ z)) := by
    intro F X i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro n hi hj
    simp only [mem_filter] at hi hj
    exact Set.disjoint_left.mp (hdisj hij) hi.2.1 hj.2.1
  have hdisjQ : ∀ (F : Finset ι) X, (F : Set ι).PairwiseDisjoint (fun i => window (S i) X) := by
    intro F X i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro n hi hj
    exact Set.disjoint_left.mp (hdisj hij) (mem_window.mp hi).2 (mem_window.mp hj).2
  -- lower bound: the joint proportions add up to at most `G`
  have hlow : ∀ (F : Finset ι) X, 0 < X → ∑ i ∈ F, J i X ≤ G X := by
    intro F X hX
    have hXr : (0 : ℝ) < X := by exact_mod_cast hX
    have hsub : F.biUnion (fun i => (Icc 1 X).filter (fun n => n ∈ S i ∧ stat X n ≤ z)) ⊆
        (window {n | 0 < n} X).filter (fun n => stat X n ≤ z) := by
      intro n hn
      rw [mem_biUnion] at hn
      obtain ⟨i, -, hi⟩ := hn
      simp only [mem_filter] at hi ⊢
      exact ⟨by rw [window_pos]; exact hi.1, hi.2.2⟩
    have hc := card_le_card hsub
    rw [card_biUnion (hdisjF F X)] at hc
    simp only [hJ, hG, card_window_pos, ← Finset.sum_div]
    gcongr
    exact_mod_cast hc
  -- upper bound: what is not in the joint events lies outside `⋃_F S i`
  have hup : ∀ (F : Finset ι) X, 0 < X → G X ≤ ∑ i ∈ F, J i X + (1 - ∑ i ∈ F, D i X) := by
    intro F X hX
    have hXr : (0 : ℝ) < X := by exact_mod_cast hX
    set P := F.biUnion (fun i => (Icc 1 X).filter (fun n => n ∈ S i ∧ stat X n ≤ z))
    set Q := F.biUnion (fun i => window (S i) X)
    have hQ : Q ⊆ Icc 1 X := by
      intro n hn
      rw [mem_biUnion] at hn
      obtain ⟨i, -, hi⟩ := hn
      exact mem_Icc.mpr (mem_window.mp hi).1
    have hsub : (window {n | 0 < n} X).filter (fun n => stat X n ≤ z) ⊆ P ∪ (Icc 1 X \ Q) := by
      intro n hn
      simp only [mem_filter] at hn
      rw [window_pos] at hn
      by_cases hq : n ∈ Q
      · rw [mem_biUnion] at hq
        obtain ⟨i, hiF, hi⟩ := hq
        refine mem_union_left _ (mem_biUnion.mpr ⟨i, hiF, ?_⟩)
        simp only [mem_filter]
        exact ⟨hn.1, (mem_window.mp hi).2, hn.2⟩
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hn.1, hq⟩)
    have hc := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_sdiff_of_subset hQ, card_Icc_one, card_biUnion (hdisjF F X),
      card_biUnion (hdisjQ F X)] at hc
    have hQX : ∑ i ∈ F, (window (S i) X).card ≤ X := by
      rw [← card_biUnion (hdisjQ F X)]
      exact (card_le_card hQ).trans (card_Icc_one X).le
    have hc' : (((window {n | 0 < n} X).filter (fun n => stat X n ≤ z)).card : ℝ) ≤
        ∑ i ∈ F, (((Icc 1 X).filter (fun n => n ∈ S i ∧ stat X n ≤ z)).card : ℝ) +
          ((X : ℝ) - ∑ i ∈ F, ((window (S i) X).card : ℝ)) := by
      have := (Nat.cast_le (α := ℝ)).mpr hc
      push_cast [Nat.cast_sub hQX] at this
      exact this
    simp only [hJ, hD, hG, card_window_pos]
    rw [← Finset.sum_div, ← Finset.sum_div, div_le_iff₀ hXr]
    have e : ((∑ i ∈ F, (((Icc 1 X).filter (fun n => n ∈ S i ∧ stat X n ≤ z)).card : ℝ)) / X +
        (1 - (∑ i ∈ F, ((window (S i) X).card : ℝ)) / X)) * X =
        ∑ i ∈ F, (((Icc 1 X).filter (fun n => n ∈ S i ∧ stat X n ≤ z)).card : ℝ) +
          ((X : ℝ) - ∑ i ∈ F, ((window (S i) X).card : ℝ)) := by
      rw [add_mul, sub_mul, div_mul_cancel₀ _ hXr.ne', div_mul_cancel₀ _ hXr.ne', one_mul]
    rw [e]
    exact hc'
  -- the finite sums of the weights tend to `1`
  have hsumT : Tendsto (fun F : Finset ι => ∑ i ∈ F, wt i) atTop (𝓝 1) := hsum
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hF : Tendsto (fun F : Finset ι => (∑ i ∈ F, wt i) * Φ z) atTop (𝓝 (1 * Φ z)) :=
      hsumT.mul_const _
    rw [one_mul] at hF
    obtain ⟨F, hFa⟩ := (hF.eventually (lt_mem_nhds ha)).exists
    have hlim : Tendsto (fun X => ∑ i ∈ F, J i X) atTop (𝓝 (∑ i ∈ F, wt i * Φ z)) :=
      tendsto_finsetSum _ fun i _ => hjoint i z
    rw [← Finset.sum_mul] at hlim
    filter_upwards [hlim.eventually (lt_mem_nhds hFa), eventually_gt_atTop 0] with X hX hX0
    exact lt_of_lt_of_le hX (hlow F X hX0)
  · have hF : Tendsto (fun F : Finset ι => (∑ i ∈ F, wt i) * Φ z + (1 - ∑ i ∈ F, wt i)) atTop
        (𝓝 (1 * Φ z + (1 - 1))) := (hsumT.mul_const _).add (tendsto_const_nhds.sub hsumT)
    rw [one_mul, sub_self, add_zero] at hF
    obtain ⟨F, hFb⟩ := (hF.eventually (gt_mem_nhds hb)).exists
    have hlim : Tendsto (fun X => ∑ i ∈ F, J i X + (1 - ∑ i ∈ F, D i X)) atTop
        (𝓝 (∑ i ∈ F, wt i * Φ z + (1 - ∑ i ∈ F, wt i))) :=
      (tendsto_finsetSum _ fun i _ => hjoint i z).add
        (tendsto_const_nhds.sub (tendsto_finsetSum _ fun i _ => hdens i))
    rw [← Finset.sum_mul] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds hFb), eventually_gt_atTop 0] with X hX hX0
    exact lt_of_le_of_lt (hup F X hX0) hX

/-! ## Rates -/

/-- Densities of subsets of `ℕ_{>0}` are limits of proportions of `[1, X]`. -/
lemma hasDensity_of_propn {P : ℕ → Prop} {d : ℝ}
    (h : Tendsto (fun X => propn (window {n | 0 < n} X) P) atTop (𝓝 d)) :
    HasDensity {n | 0 < n ∧ P n} d := by
  classical
  refine h.congr fun X => ?_
  have hw : window {n | 0 < n ∧ P n} X = (window {n | 0 < n} X).filter P := by
    ext n
    simp only [mem_filter, mem_window, Set.mem_ofPred_eq]
    tauto
  unfold propn
  rw [hw, card_window_pos]

/-- **The rates lemma** (the argument of Corollary 1.2 [`cor:rates`] for `N_X` uniform on `[1, X]`).
If `(f(N_X) - κ log N_X)/√(V log X) ⇒ N(0,1)` under uniform sampling from `[1, X]`, then
`{n : f(n) ≤ c₀ log n}` has density `1`, `1/2` or `0` according as `c₀ > κ`, `c₀ = κ` or
`c₀ < κ`. -/
theorem density_rate {f : ℕ → ℕ} {κ V : ℝ} (hV : 0 < V) (h : CLTOn {n | 0 < n} (normalised f κ V))
    (c0 : ℝ) :
    HasDensity {n | 0 < n ∧ (f n : ℝ) ≤ c0 * Real.log n}
      (if κ < c0 then 1 else if c0 = κ then 1 / 2 else 0) := by
  apply hasDensity_of_propn
  set W := window {n | 0 < n} with hW
  have hlaw : LawN W (normalised f κ V) := h
  -- the event `n ≤ X e^{-R}` has proportion at most `e^{-R}`
  have hsmall : ∀ R : ℝ, ∀ᶠ X : ℕ in atTop,
      propn (W X) (fun n => (n : ℝ) ≤ X * Real.exp (-R)) ≤ Real.exp (-R) := fun R => by
    filter_upwards [eventually_gt_atTop 0] with X hX
    exact propn_small_le hX R
  -- outside the small integers, `log n ≥ log X - R`
  have hlog : ∀ {X n : ℕ} {R : ℝ}, 0 < X → ¬ ((n : ℝ) ≤ X * Real.exp (-R)) →
      Real.log X - R < Real.log n := by
    intro X n R hX hlt
    push Not at hlt
    have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
    have := Real.log_lt_log (by positivity) hlt
    rwa [Real.log_mul hX0.ne' (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg] at this
  split_ifs with h1 h2
  · -- `c₀ > κ`: density `1`
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => Eventually.of_forall fun X =>
      lt_of_le_of_lt (propn_le_one _ _) hb⟩
    set δ := 1 - a with hδ
    have hδ0 : 0 < δ := by linarith
    obtain ⟨M, hM⟩ := (tendsto_Φ_atTop.eventually (lt_mem_nhds
      (show 1 - δ / 3 < 1 by linarith))).exists
    obtain ⟨R, hR⟩ := (Real.tendsto_exp_neg_atTop_nhds_zero.eventually
      (gt_mem_nhds (show (0 : ℝ) < δ / 3 by positivity))).exists
    filter_upwards [(hlaw M).eventually (lt_mem_nhds (show 1 - 2 * δ / 3 < Φ M by linarith)),
      hsmall R, eventually_sqrt_log_le hV (sub_pos.mpr h1) M ((c0 - κ) * R),
      eventually_ge_atTop 2] with X hX1 hX2 hX3 hX4
    have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX4
    have hs : 0 < √(V * Real.log X) := Real.sqrt_pos.mpr (by
      have := Real.log_pos (show (1 : ℝ) < X by linarith); positivity)
    have hle : propn (W X) (fun n => normalised f κ V X n ≤ M) ≤
        propn (W X) (fun n => (f n : ℝ) ≤ c0 * Real.log n) +
          propn (W X) (fun n => (n : ℝ) ≤ X * Real.exp (-R)) := by
      refine propn_le_add fun n hn hM' => ?_
      by_cases hsm : (n : ℝ) ≤ X * Real.exp (-R)
      · exact Or.inr hsm
      · left
        have hl := hlog (by omega : 0 < X) hsm
        unfold normalised at hM'
        rw [div_le_iff₀ hs] at hM'
        nlinarith
    linarith
  · -- `c₀ = κ`: density `1/2`
    rw [← Φ_zero]
    refine (hlaw 0).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with X hX
    have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
    have hs : 0 < √(V * Real.log X) := Real.sqrt_pos.mpr (by
      have := Real.log_pos (show (1 : ℝ) < X by linarith); positivity)
    refine propn_congr fun n _ => ?_
    unfold normalised
    rw [div_le_iff₀ hs, zero_mul, h2, sub_nonpos]
  · -- `c₀ < κ`: density `0`
    have h3 : c0 < κ := lt_of_le_of_ne (not_lt.mp h1) h2
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun X => lt_of_lt_of_le ha (propn_nonneg _ _),
      fun b hb => ?_⟩
    obtain ⟨M, hM⟩ := (tendsto_Φ_atBot.eventually (gt_mem_nhds
      (show (0 : ℝ) < b / 3 by positivity))).exists
    obtain ⟨R, hR⟩ := (Real.tendsto_exp_neg_atTop_nhds_zero.eventually
      (gt_mem_nhds (show (0 : ℝ) < b / 3 by positivity))).exists
    filter_upwards [(hlaw M).eventually (gt_mem_nhds (show Φ M < b / 3 by linarith)),
      hsmall R, eventually_sqrt_log_le hV (sub_pos.mpr h3) (-M) ((κ - c0) * R),
      eventually_ge_atTop 2] with X hX1 hX2 hX3 hX4
    have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX4
    have hs : 0 < √(V * Real.log X) := Real.sqrt_pos.mpr (by
      have := Real.log_pos (show (1 : ℝ) < X by linarith); positivity)
    have hle : propn (W X) (fun n => (f n : ℝ) ≤ c0 * Real.log n) ≤
        propn (W X) (fun n => normalised f κ V X n ≤ M) +
          propn (W X) (fun n => (n : ℝ) ≤ X * Real.exp (-R)) := by
      refine propn_le_add fun n hn hf => ?_
      by_cases hsm : (n : ℝ) ≤ X * Real.exp (-R)
      · exact Or.inr hsm
      · left
        have hl := hlog (by omega : 0 < X) hsm
        unfold normalised
        rw [div_le_iff₀ hs]
        nlinarith
    linarith

end CollatzCLT
