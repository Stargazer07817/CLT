import LeanClt.Exceptional.Thresholds

/-!
# Theorems 6.7 [`thm:rayentry`] and 6.8 [`thm:movingray`]: first entry into a divergent ray

Stage 5 of the checkpoint-11 plan. For a nonrepeating ray `a_j = T^j(a)` with merging class
`C = mergeClass a`, write `h_j = dens P_T(a_j)` and `π_C = dens C`.

* **`ray_densities`.** `π_C > 0` and every `h_j` exists (Theorem 1.3(iii) [`thm:thresholds`] and
  Theorem 1.1(i) [`thm:main`]; `h_j = 0` when `3 ∣ a_j`, a dyadic ray). The `h_j` increase, and
  `π_C - h_j ≤ 1 - h_K` once `C ∩ A_K ⊆ P_T(a_j)` (`classAK_subset_pred`), so `h_j → π_C` by
  Theorem 1.3(i).
* **Theorem 6.7** (`rayentry`, conclusion `RayEntryLaw`). `{n ∈ C : J_R(n) ≤ j} = P_T(a_j)`
  (`ray_identities`) gives `P(J_R ≤ j) → h_j/π_C` and tightness. The CLT for `e_R` on `C` is the
  sandwich `cltOn_of_subsets` over the subsets `P_T(a_{j + j₀})`, with `j₀` such that every later ray
  point is prime to 3: on each, `τ_{T,a_m} - e_R = m - J_R ∈ [0, m]` is bounded
  (`cltOn_bounded_shift`) and the fixed-target CLT applies.
* **Theorem 6.8(i)** (`movingray_joint`, conclusion `RayJointLaw`). The joint event
  `{J_R ≤ j, Z_X ≤ z}` in `C` is `{Z_X ≤ z}` in `P_T(a_j)`; its proportion factors as
  `P(Z_X ≤ z | P_T(a_j)) · #P_T(a_j)/#C`. When `3 ∤ a_j` the first factor tends to `Φ(z)` by the
  fixed-target CLT, the bounded shift and Lemma 6.5(iii) [`lem:sampling`] (`cltOn_logX`, centring
  `κ_T log X`); when `3 ∣ a_j` the proportion is at most `#P_T(a_j)/#C → 0 = h_j/π_C`.
* **Theorem 6.8(ii)** (`movingray_moving`, conclusion `RayMovingLaw`), by the route recorded in
  checkpoint 13, with `log N_X` centring throughout (no detour through `log X`):
  `#P_T(a_{j(X)}) / #C → 1` from `P_T(a_{J₀}) ⊆ P_T(a_{j(X)})` and `h_{J₀}/π_C → 1`;
  `e_R - J_R` satisfies the CLT on `C` (`lawN_of_tight_shift`, `J_R` tight); the CLT passes to the
  moving subsample `P_T(a_{j(X)}) ∩ [1, X]` (`lawN_of_subfamily`, the total-variation bound); and
  there `τ_{T,a_{j(X)}} - j(X) = e_R - J_R` exactly (`lawN_of_uniform_close` with zero error).

The three conclusions are named propositions so that Corollary 1.5 [`cor:dichotomy`] can cite them.
`RayEntryLaw` and `RayMovingLaw` are the checkpoint-11 statements; `RayJointLaw` carries the conjunct
`Tendsto h atTop (𝓝 pC)` added by the checkpoint-12 statement audit, without which the
distribution-function form would also hold for a defective limit law.

This file does not import `LeanClt/Statements.lean` (checkpoint 12).
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-! ## The three conclusions -/

/-- The conclusion of **Theorem 6.7** for the ray `a_j = T^j(a)` with class `C = mergeClass a`:
`dens P_T(a_j) ↑ π_C`; `P(J_R(N_X) ≤ j) → dens P_T(a_j)/π_C`; `J_R(N_X)` is tight; and `e_R`
satisfies the CLT under uniform sampling from `C ∩ [1, X]`. -/
def RayEntryLaw (a : ℕ) : Prop :=
  ∃ pC : ℝ, 0 < pC ∧ HasDensity (mergeClass a) pC ∧
  ∃ h : ℕ → ℝ, (∀ j, HasDensity (Pred T (T^[j] a)) (h j)) ∧ Monotone h ∧
    Tendsto h atTop (𝓝 pC) ∧
    (∀ j : ℕ, Tendsto (fun X : ℕ =>
      (((window (mergeClass a) X).filter (fun n => rayIndex a n ≤ j)).card : ℝ) /
        (window (mergeClass a) X).card) atTop (𝓝 (h j / pC))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ j0 : ℕ, ∀ᶠ X : ℕ in atTop,
      (((window (mergeClass a) X).filter (fun n => j0 < rayIndex a n)).card : ℝ) ≤
        ε * (window (mergeClass a) X).card) ∧
    CLTOn (mergeClass a) (normalised (entry (fwdOrbit a)) κT VT)

/-- The conclusion of **Theorem 6.8(i)**, in distribution-function form: with `h_j = dens P_T(a_j)`,
`P(J_R ≤ j, (e_R - κ_T log X)/√(V_T log X) ≤ z) → (h_j/π_C) Φ(z)`, and `h_j → π_C`, i.e. the pair
converges in law to `w ⊗ N(0,1)` with `w_j = (h_j - h_{j-1})/π_C`. -/
def RayJointLaw (a : ℕ) : Prop :=
  ∃ pC : ℝ, 0 < pC ∧ HasDensity (mergeClass a) pC ∧
  ∃ h : ℕ → ℝ, (∀ j, HasDensity (Pred T (T^[j] a)) (h j)) ∧ Tendsto h atTop (𝓝 pC) ∧
    ∀ (j : ℕ) (z : ℝ), Tendsto (fun X : ℕ =>
      (((window (mergeClass a) X).filter (fun n => rayIndex a n ≤ j ∧
          ((entry (fwdOrbit a) n : ℝ) - κT * Real.log X) / √(VT * Real.log X) ≤ z)).card : ℝ) /
        (window (mergeClass a) X).card) atTop (𝓝 (h j / pC * Φ z))

/-- The conclusion of **Theorem 6.8(ii)** (moving target `a_{j(X)}`, travel subtracted). -/
def RayMovingLaw (a : ℕ) : Prop :=
  ∀ jX : ℕ → ℕ, Tendsto jX atTop atTop →
    Tendsto (fun X : ℕ => ((window (Pred T (T^[jX X] a)) X).card : ℝ) /
      (window (mergeClass a) X).card) atTop (𝓝 1) ∧
    ∀ z : ℝ, Tendsto (fun X : ℕ =>
      (((window (Pred T (T^[jX X] a)) X).filter (fun n =>
          ((hit T (T^[jX X] a) n : ℝ) - jX X - κT * Real.log n) / √(VT * Real.log X) ≤ z)).card
            : ℝ) / (window (Pred T (T^[jX X] a)) X).card) atTop (𝓝 (Φ z))

/-! ## Finite-sample helpers -/

/-- `propn` with any decidability instance for the predicate. -/
lemma propn_eq_card_div {W : Finset ℕ} (p : ℕ → Prop) [DecidablePred p] :
    propn W p = ((W.filter p).card : ℝ) / W.card := by
  unfold propn
  congr

/-- If `A ⊆ B ∪ D`, then `dens A ≤ dens B + dens D`. -/
lemma HasDensity.le_add_of_subset_union {A B D : Set ℕ} {a b d : ℝ} (h : A ⊆ B ∪ D)
    (hA : HasDensity A a) (hB : HasDensity B b) (hD : HasDensity D d) : a ≤ b + d := by
  classical
  refine le_of_tendsto_of_tendsto' hA (hB.add hD) fun X => ?_
  rw [← add_div]
  have hw : window A X ⊆ window B X ∪ window D X := by
    intro n hn
    rw [mem_window] at hn
    rw [mem_union, mem_window, mem_window]
    rcases h hn.2 with h' | h'
    · exact Or.inl ⟨hn.1, h'⟩
    · exact Or.inr ⟨hn.1, h'⟩
  have hc : ((window A X).card : ℝ) ≤ (window B X).card + (window D X).card := by
    exact_mod_cast (card_le_card hw).trans (card_union_le _ _)
  exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)

/-- The ratio of two window counts tends to the ratio of the densities. -/
lemma tendsto_card_div_card {A C : Set ℕ} {a p : ℝ} (hA : HasDensity A a) (hC : HasDensity C p)
    (hp : p ≠ 0) :
    Tendsto (fun X : ℕ => ((window A X).card : ℝ) / (window C X).card) atTop (𝓝 (a / p)) := by
  refine (hA.div hC hp).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hX' : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hX']

/-- `x/c = (x/p)(p/c)` for counts `x ≤ p`. -/
lemma div_eq_div_mul_div_of_le {x p c : ℕ} (h : x ≤ p) :
    (x : ℝ) / c = (x : ℝ) / p * ((p : ℝ) / c) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    obtain rfl : x = 0 := by omega
    simp
  · rw [div_mul_div_comm, mul_comm (x : ℝ) p, mul_div_mul_left _ _ (by exact_mod_cast hp.ne')]

/-! ## Ray combinatorics on windows -/

/-- The sets `P_T(a_j)` increase with `j`. -/
lemma pred_ray_mono {a : ℕ} (ha : 0 < a) {j j' : ℕ} (hjj : j ≤ j') :
    Pred T (T^[j] a) ⊆ Pred T (T^[j'] a) := by
  intro n hn
  refine pred_trans hn ⟨iterate_T_pos ha j, j' - j, ?_⟩
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hjj]

/-- `P_T(a_j) ⊆ C`. -/
lemma pred_ray_subset_class {a : ℕ} (ha : 0 < a) (hR : NonRepeating a) (j : ℕ) :
    Pred T (T^[j] a) ⊆ mergeClass a := by
  rw [(ray_identities ha hR j).1]
  exact fun n hn => hn.1

/-- `{n ∈ C ∩ [1, X] : J_R(n) ≤ j} = P_T(a_j) ∩ [1, X]`. -/
lemma window_filter_rayIndex {a : ℕ} (ha : 0 < a) (hR : NonRepeating a) (j X : ℕ) :
    (window (mergeClass a) X).filter (fun n => rayIndex a n ≤ j) =
      window (Pred T (T^[j] a)) X := by
  rw [(ray_identities ha hR j).1]
  ext n
  simp only [mem_filter, mem_window, Set.mem_ofPred_eq]
  tauto

/-! ## The densities along a ray -/

/-- **The densities along a ray** (proof of Theorem 6.7 [`thm:rayentry`]). The class `C` of `a` has a
positive density `π_C`; every `P_T(a_j)` has a density `h_j`, which is positive, with the
fixed-target CLT, when `3 ∤ a_j`, and is `0` when `3 ∣ a_j`; `h` is nondecreasing and tends to
`π_C`. -/
theorem ray_densities (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {a : ℕ} (ha : 0 < a) (hR : NonRepeating a) :
    ∃ pC : ℝ, 0 < pC ∧ HasDensity (mergeClass a) pC ∧
    ∃ h : ℕ → ℝ, (∀ j, HasDensity (Pred T (T^[j] a)) (h j)) ∧ Monotone h ∧
      Tendsto h atTop (𝓝 pC) ∧
      (∀ j, ¬ 3 ∣ T^[j] a → 0 < h j ∧
        CLTOn (Pred T (T^[j] a)) (normalised (hit T (T^[j] a)) κT VT)) ∧
      (∀ j, 3 ∣ T^[j] a → h j = 0) := by
  -- the class density, from Theorem 1.3(iii)
  obtain ⟨dC, hdC, hdCpos, -⟩ := thresholds_iii hTM hTP hθ
  have hC : HasDensity (mergeClass a) (dC (Quotient.mk mergeSetoid a)) := by
    rw [mergeClass_eq_classSet]
    exact hdC _
  have hpC : 0 < dC (Quotient.mk mergeSetoid a) := hdCpos a ha
  -- the densities `h_j`, from Theorem 1.1(i) or the dyadic ray
  have hex : ∀ j, ∃ x, HasDensity (Pred T (T^[j] a)) x ∧
      (¬ 3 ∣ T^[j] a → 0 < x ∧
        CLTOn (Pred T (T^[j] a)) (normalised (hit T (T^[j] a)) κT VT)) ∧
      (3 ∣ T^[j] a → x = 0) := by
    intro j
    have hb : 0 < T^[j] a := iterate_T_pos ha j
    by_cases h3 : 3 ∣ T^[j] a
    · refine ⟨0, ?_, fun h => absurd h3 h, fun _ => rfl⟩
      rw [pred_of_three_dvd hb h3]
      exact hasDensity_dyadic hb
    · obtain ⟨⟨x, hx, hxd⟩, hclt⟩ :=
        main_T_of_tao hTM hTP hθ _ hb (Positivity.positivity_of_tao hTM hTP hb h3)
      exact ⟨x, hxd, fun _ => ⟨hx, hclt⟩, fun h => absurd h h3⟩
  choose h hh hpos hzero using hex
  have hmono : Monotone h := monotone_nat_of_le_succ fun j =>
    (hh j).mono (pred_ray_mono ha (Nat.le_succ j)) (hh (j + 1))
  have hle : ∀ j, h j ≤ dC (Quotient.mk mergeSetoid a) := fun j =>
    (hh j).mono (pred_ray_subset_class ha hR j) hC
  -- `π_C - h_j ≤ 1 - h_K ≤ C (log K)^{-δ₀}` once `C ∩ A_K ⊆ P_T(a_j)`
  obtain ⟨hexK, Cc, δ0, -, hδ0, hlow⟩ := thresholds_i hTM hTP hθ
  have hgap : ∀ K : ℕ, 2 ≤ K → ∃ jK, ∀ j, jK ≤ j →
      dC (Quotient.mk mergeSetoid a) - Cc * Real.log K ^ (-δ0) ≤ h j := by
    intro K hK2
    obtain ⟨hK', hhK⟩ := hexK K (by omega)
    obtain ⟨jK, hjK⟩ := classAK_subset_pred ha hR K
    refine ⟨jK, fun j hj => ?_⟩
    have hsub : mergeClass a ⊆ Pred T (T^[j] a) ∪ {n | 0 < n ∧ n ∉ AK K} := by
      intro n hn
      by_cases hnK : n ∈ AK K
      · exact Or.inl (hjK j hj ⟨hn, hnK⟩)
      · exact Or.inr ⟨hn.1, hnK⟩
    have h1 := HasDensity.le_add_of_subset_union hsub hC (hh j) hhK.compl_pos
    have h2 := hlow K hK2 hK' hhK
    linarith
  have hlim : Tendsto h atTop (𝓝 (dC (Quotient.mk mergeSetoid a))) := by
    rw [tendsto_order]
    refine ⟨fun x hx => ?_, fun x hx => Eventually.of_forall fun j => lt_of_le_of_lt (hle j) hx⟩
    have hK : Tendsto (fun K : ℕ => dC (Quotient.mk mergeSetoid a) - Cc * Real.log K ^ (-δ0))
        atTop (𝓝 (dC (Quotient.mk mergeSetoid a))) := by
      have := (((tendsto_rpow_neg_atTop hδ0).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul Cc).const_sub
          (dC (Quotient.mk mergeSetoid a))
      simpa [Function.comp_def] using this
    obtain ⟨K, hK1, hK2⟩ := ((hK.eventually (lt_mem_nhds hx)).and (eventually_ge_atTop 2)).exists
    obtain ⟨jK, hjK⟩ := hgap K hK2
    exact eventually_atTop.mpr ⟨jK, fun j hj => lt_of_lt_of_le hK1 (hjK j hj)⟩
  exact ⟨_, hpC, hC, h, hh, hmono, hlim, hpos, hzero⟩

/-! ## Theorem 6.7 -/

/-- **Theorem 6.7 [`thm:rayentry`].** For a nonrepeating `T`-ray `a_j = T^j(a)` with class `C`:
`dens P_T(a_j) ↑ π_C`, `P(J_R(N_X) ≤ j) → dens P_T(a_j)/π_C`, `J_R(N_X)` is tight, and the first
entry time `e_R` satisfies the CLT with `(κ_T, V_T)` under uniform sampling from `C ∩ [1, X]`. -/
theorem rayentry (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {a : ℕ} (ha : 0 < a) (hR : NonRepeating a) : RayEntryLaw a := by
  obtain ⟨pC, hpC, hC, h, hh, hmono, hlim, hpos, -⟩ := ray_densities hTM hTP hθ ha hR
  have hεp : ∀ ε : ℝ, 0 < ε → pC - ε * pC < pC := fun ε hε => by
    have := mul_pos hε hpC
    linarith
  refine ⟨pC, hpC, hC, h, hh, hmono, hlim, fun j => ?_, fun ε hε => ?_, ?_⟩
  · -- `P(J_R ≤ j) → h_j/π_C`
    refine (tendsto_card_div_card (hh j) hC hpC.ne').congr fun X => ?_
    rw [window_filter_rayIndex ha hR j X]
  · -- tightness: the window of `C` misses `P_T(a_{j₀})` in at most a fraction `ε`
    obtain ⟨j0, hj0⟩ := (hlim.eventually (lt_mem_nhds (hεp ε hε))).exists
    refine ⟨j0, ?_⟩
    filter_upwards [deficit_of_hasDensity (ε := ε) (hh j0) hC (by linarith)] with X hX
    refine le_trans ?_ hX
    have hPC : window (Pred T (T^[j0] a)) X ⊆ window (mergeClass a) X :=
      window_mono (pred_ray_subset_class ha hR j0) X
    have hsub : (window (mergeClass a) X).filter (fun n => j0 < rayIndex a n) ⊆
        window (mergeClass a) X \ window (Pred T (T^[j0] a)) X := by
      intro n hn
      simp only [mem_filter] at hn
      refine mem_sdiff.mpr ⟨hn.1, fun hP => ?_⟩
      rw [← window_filter_rayIndex ha hR j0 X] at hP
      simp only [mem_filter] at hP
      omega
    have hc := card_le_card hsub
    rw [card_sdiff_of_subset hPC] at hc
    rw [← Nat.cast_sub (card_le_card hPC)]
    exact_mod_cast hc
  · -- the CLT on `C`: the sandwich over `P_T(a_{j + j₀})`, `3 ∤ a_{j + j₀}`
    obtain ⟨j₀, hj₀⟩ := eventually_not_three_dvd ha
    refine cltOn_of_subsets (A := fun j => Pred T (T^[j + j₀] a))
      (fun j => pred_ray_subset_class ha hR _) (fun j => ?_) (fun ε hε => ?_)
    · obtain ⟨-, hclt⟩ := hpos (j + j₀) (hj₀ _ (Nat.le_add_left _ _))
      refine cltOn_bounded_shift VT_pos (j + j₀) (fun n hn => ?_) hclt
      obtain ⟨hJ, heq⟩ := (ray_identities ha hR (j + j₀)).2 n hn
      constructor <;> omega
    · have hl : Tendsto (fun j => h (j + j₀)) atTop (𝓝 pC) :=
        (tendsto_add_atTop_iff_nat j₀).mpr hlim
      obtain ⟨j, hj⟩ := (hl.eventually (lt_mem_nhds (hεp ε hε))).exists
      exact ⟨j, deficit_of_hasDensity (ε := ε) (hh _) hC (by linarith)⟩

/-! ## Theorem 6.8 -/

/-- **Theorem 6.8(i) [`thm:movingray`].** Under `N_X` uniform on `C ∩ [1, X]`, the pair
`(J_R(N_X), (e_R(N_X) - κ_T log X)/√(V_T log X))` converges in law to `w ⊗ N(0,1)`, in
distribution-function form. -/
theorem movingray_joint (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {a : ℕ} (ha : 0 < a) (hR : NonRepeating a) : RayJointLaw a := by
  obtain ⟨pC, hpC, hC, h, hh, -, hlim, hpos, hzero⟩ := ray_densities hTM hTP hθ ha hR
  refine ⟨pC, hpC, hC, h, hh, hlim, fun j z => ?_⟩
  -- the joint event in `C` is the event `Z_X ≤ z` in `P_T(a_j)`
  have hev : ∀ X : ℕ, (window (mergeClass a) X).filter (fun n => rayIndex a n ≤ j ∧
      ((entry (fwdOrbit a) n : ℝ) - κT * Real.log X) / √(VT * Real.log X) ≤ z) =
      (window (Pred T (T^[j] a)) X).filter (fun n =>
        ((entry (fwdOrbit a) n : ℝ) - κT * Real.log X) / √(VT * Real.log X) ≤ z) := by
    intro X
    rw [← window_filter_rayIndex ha hR j X]
    ext n
    simp only [mem_filter]
    tauto
  have hratio := tendsto_card_div_card (hh j) hC hpC.ne'
  by_cases h3 : 3 ∣ T^[j] a
  · -- `h_j = 0`: the proportion is at most `#P_T(a_j)/#C → 0`
    rw [hzero j h3, zero_div] at hratio ⊢
    rw [zero_mul]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hratio
      (fun X => by positivity) (fun X => ?_)
    dsimp only
    rw [hev X]
    exact div_le_div_of_nonneg_right (by exact_mod_cast card_filter_le _ _) (Nat.cast_nonneg _)
  · -- `3 ∤ a_j`: the CLT on `P_T(a_j)` with `log X` centring, times `#P_T(a_j)/#C`
    obtain ⟨hjpos, hclt⟩ := hpos j h3
    have hclt' : CLTOn (Pred T (T^[j] a)) (normalised (entry (fwdOrbit a)) κT VT) := by
      refine cltOn_bounded_shift VT_pos j (fun n hn => ?_) hclt
      obtain ⟨hJ, heq⟩ := (ray_identities ha hR j).2 n hn
      constructor <;> omega
    have hcltX := cltOn_logX VT_pos ((hh j).posLower hjpos) hclt' z
    have hprod := hcltX.mul hratio
    rw [mul_comm] at hprod
    refine hprod.congr fun X => ?_
    dsimp only
    rw [hev X]
    exact (div_eq_div_mul_div_of_le (card_filter_le _ _)).symm

/-- **Theorem 6.8(ii) [`thm:movingray`].** For every `j(X) → ∞`:
`#(P_T(a_{j(X)}) ∩ [1, X]) / #(C ∩ [1, X]) → 1`, and under `N_X` uniform on `P_T(a_{j(X)}) ∩ [1, X]`,
`(τ_{T,a_{j(X)}}(N_X) - j(X) - κ_T log N_X)/√(V_T log X) ⇒ N(0,1)`. -/
theorem movingray_moving (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {a : ℕ} (ha : 0 < a) (hR : NonRepeating a) : RayMovingLaw a := by
  obtain ⟨pC, hpC, hC, h, hh, -, hlim, -, htight, hclt⟩ := rayentry hTM hTP hθ ha hR
  intro jX hjX
  have hPC : ∀ X, window (Pred T (T^[jX X] a)) X ⊆ window (mergeClass a) X := fun X =>
    window_mono (pred_ray_subset_class ha hR _) X
  -- the moving population has relative mass `→ 1` in `C`
  have hratio : Tendsto (fun X : ℕ => ((window (Pred T (T^[jX X] a)) X).card : ℝ) /
      (window (mergeClass a) X).card) atTop (𝓝 1) := by
    rw [tendsto_order]
    refine ⟨fun x hx => ?_, fun x hx => Eventually.of_forall fun X => lt_of_le_of_lt ?_ hx⟩
    · have hq : Tendsto (fun j => h j / pC) atTop (𝓝 1) := by
        have := hlim.div_const pC
        rwa [div_self hpC.ne'] at this
      obtain ⟨J0, hJ0⟩ := (hq.eventually (lt_mem_nhds hx)).exists
      filter_upwards [(tendsto_card_div_card (hh J0) hC hpC.ne').eventually (lt_mem_nhds hJ0),
        hjX.eventually (eventually_ge_atTop J0)] with X hX1 hX2
      refine lt_of_lt_of_le hX1 ?_
      gcongr
      exact window_mono (pred_ray_mono ha hX2) X
    · exact div_le_one_of_le₀ (by exact_mod_cast card_le_card (hPC X)) (Nat.cast_nonneg _)
  refine ⟨hratio, fun z => ?_⟩
  -- the missing relative mass vanishes
  have hdef : ∀ ε > 0, ∀ᶠ X : ℕ in atTop, ((window (mergeClass a) X).card : ℝ) -
      (window (Pred T (T^[jX X] a)) X).card ≤ ε * (window (mergeClass a) X).card := by
    intro ε hε
    filter_upwards [hratio.eventually (lt_mem_nhds (show 1 - ε < 1 by linarith))] with X hX
    rcases Nat.eq_zero_or_pos (window (mergeClass a) X).card with h0 | h0
    · have h0' : (window (Pred T (T^[jX X] a)) X).card = 0 :=
        Nat.eq_zero_of_le_zero (h0 ▸ card_le_card (hPC X))
      rw [h0, h0']
      simp
    · have hc : (0 : ℝ) < (window (mergeClass a) X).card := by exact_mod_cast h0
      rw [lt_div_iff₀ hc] at hX
      linarith
  -- tightness of `J_R` in proportion form
  have htight' : ∀ ε > 0, ∃ j0 : ℕ, ∀ᶠ X : ℕ in atTop,
      propn (window (mergeClass a) X) (fun n => j0 < rayIndex a n) ≤ ε := by
    intro ε hε
    obtain ⟨j0, hj0⟩ := htight ε hε
    refine ⟨j0, ?_⟩
    filter_upwards [hj0] with X hX
    rw [propn_eq_card_div]
    rcases Nat.eq_zero_or_pos (window (mergeClass a) X).card with h0 | h0
    · rw [h0, Nat.cast_zero, div_zero]
      exact hε.le
    · rw [div_le_iff₀ (by exact_mod_cast h0)]
      exact hX
  -- `e_R - J_R` satisfies the CLT on `C` (Slutsky, `J_R` tight)
  have hlaw1 : LawN (window (mergeClass a)) (fun X n =>
      ((entry (fwdOrbit a) n : ℝ) - rayIndex a n - κT * Real.log n) / √(VT * Real.log X)) := by
    refine lawN_of_tight_shift (s := rayIndex a) (L := fun X => VT * Real.log X)
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop VT_pos)
      (Eventually.of_forall fun X n _ => ?_) htight' hclt
    show _ ≤ (rayIndex a n : ℝ) / √(VT * Real.log X)
    unfold normalised
    rw [← sub_div, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
      show (entry (fwdOrbit a) n : ℝ) - rayIndex a n - κT * Real.log n -
        ((entry (fwdOrbit a) n : ℝ) - κT * Real.log n) = -(rayIndex a n : ℝ) by ring,
      abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
  -- restriction to the moving subsample (the total-variation step)
  have hlaw2 := lawN_of_subfamily hPC hdef hlaw1
  -- on `P_T(a_{j(X)})`, `τ_{T,a_{j(X)}} - j(X) = e_R - J_R` exactly
  have hlaw3 : LawN (fun X => window (Pred T (T^[jX X] a)) X) (fun X n =>
      ((hit T (T^[jX X] a) n : ℝ) - jX X - κT * Real.log n) / √(VT * Real.log X)) := by
    refine lawN_of_uniform_close (e := fun _ => 0) tendsto_const_nhds
      (Eventually.of_forall fun X n hn => ?_) hlaw2
    obtain ⟨-, heq⟩ := (ray_identities ha hR (jX X)).2 n (mem_window.mp hn).2
    have heq' : (hit T (T^[jX X] a) n : ℝ) + rayIndex a n = entry (fwdOrbit a) n + jX X := by
      exact_mod_cast heq
    have hnum : (hit T (T^[jX X] a) n : ℝ) - jX X - κT * Real.log n =
        (entry (fwdOrbit a) n : ℝ) - rayIndex a n - κT * Real.log n := by linarith
    rw [hnum, sub_self, abs_zero]
  exact (hlaw3 z).congr fun X => propn_eq_card_div _

end CollatzCLT
