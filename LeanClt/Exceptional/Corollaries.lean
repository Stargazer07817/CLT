import LeanClt.Exceptional.Rays

/-!
# Corollaries 1.5 [`cor:dichotomy`] and 1.6 [`cor:unconditional`]

Stage 6 of the checkpoint-11 plan, following §9 of the paper. The theorems here are
`dichotomy_of_tao` and `unconditional_of_tao`; their statements are the audited checkpoint-11
statements, and `LeanClt/Statements.lean` restates them as `dichotomy` and `unconditional`, in the
same way as Theorem 1.1 [`thm:main`] there is proved from `main_T_of_tao`.

* **Corollary 1.5.** `dens E = 1 - dens P_T(1)` exists and is `< 1` because `dens P_T(1) > 0`
  (Theorem 1.1(i) at `b = 1`). A counterexample lies in `P_T(b)` for a counterexample `b` prime to 3
  (`exists_three_free_basin`), and `P_T(b) ⊆ E` (`pred_subset_exc`) has positive density, so
  `E ≠ ∅` gives `dens E > 0`; hence `dens P_T(1) = 1 ↔ E = ∅`. For a cycle through `b`: `3 ∤ b`
  (`not_three_dvd_of_periodic`), the basin of the cycle is `P_T(b)` (`reach_cycle`), and the cycle
  entry time differs from `τ_{T,b}` by at most the period minus one (`hit_le_entry_cycle`,
  `cltOn_bounded_shift`). The cycle clause is stated for every cycle, the trivial one included
  (checkpoint 11, D2: a deviation, stronger). For a divergent orbit: Theorems 6.7 [`thm:rayentry`]
  and 6.8 [`thm:movingray`].
* **Corollary 1.6.** On each class `C` the reference orbit is `fwdOrbit r`, `r = ref n` for any
  `n ∈ C`. If `r` is periodic, `C = P_T(r)` (`mergeClass_eq_pred_of_periodic`) and the law is that of
  the cycle entry time, as above. Otherwise the class has no periodic point (`RefChoice`), so `r`
  starts a nonrepeating ray (`nonRepeating_ref`) and Theorem 6.7 applies. With the class densities of
  Theorem 1.3(iii) [`thm:thresholds`] this gives the joint law on each class
  (`tendsto_joint_of_cltOn`), the unconditional law by the truncation argument
  (`cltOn_pos_of_mixture`, using the census `Σ π_C = 1`), and the densities of
  `{ε ≤ c₀ log n}` (`density_rate`). The class of `0` in the quotient is empty and has density `0`
  (`classSet_zero`). Finiteness of `ε`, the bound on `P_T(1)` and the change of reference orbit are
  `eps_finite`, `eps_class_one` and `ref_change` (`Exceptional/Orbits.lean`).

This file does not import `LeanClt/Statements.lean` (checkpoint 12): Theorem 1.1(i)–(ii) is taken
from `main_T_of_tao` and `Positivity.positivity_of_tao` directly.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-! ## Classes, cycles and reference orbits -/

lemma T_zero : T 0 = 0 := by decide

/-- The class of `0` in the quotient has no positive member. -/
lemma classSet_zero : classSet (Quotient.mk mergeSetoid 0) = ∅ := by
  ext m
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hm, h⟩
  have h' : Merge m 0 := Quotient.exact h
  obtain ⟨i, j, hij⟩ := h'
  rw [Function.iterate_fixed T_zero] at hij
  exact (iterate_T_pos hm i).ne' hij

/-- The class of a periodic point `r` is the basin `P_T(r)`. -/
lemma mergeClass_eq_pred_of_periodic {r : ℕ} (hper : IsPeriodic r) : mergeClass r = Pred T r := by
  ext n
  constructor
  · rintro ⟨hn, h⟩
    obtain ⟨j, hj⟩ := mem_fwdOrbit_of_periodic_merge hper (merge_equivalence.symm h)
    exact ⟨hn, j, hj⟩
  · exact fun hn => pred_subset_mergeClass r hn

/-- **The law on one class** (proof of Corollary 1.6 [`cor:unconditional`]). If `r > 0` is periodic or
starts a nonrepeating ray, the first entry time into `fwdOrbit r` satisfies the CLT with
`(κ_T, V_T)` under uniform sampling from the class of `r`. -/
theorem cltOn_class_entry (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {r : ℕ} (hr : 0 < r) (hcase : IsPeriodic r ∨ NonRepeating r) :
    CLTOn (mergeClass r) (normalised (entry (fwdOrbit r)) κT VT) := by
  rcases hcase with hper | hR
  · rw [mergeClass_eq_pred_of_periodic hper]
    obtain ⟨p, hp, hpr⟩ := hper
    have h3 := not_three_dvd_of_periodic hr hp hpr
    obtain ⟨-, hclt⟩ :=
      main_T_of_tao hTM hTP hθ r hr (Positivity.positivity_of_tao hTM hTP hr h3)
    refine cltOn_bounded_shift VT_pos (p - 1) (fun n hn => ?_) hclt
    obtain ⟨h1, h2⟩ := hit_le_entry_cycle hp hpr hn
    constructor <;> omega
  · obtain ⟨-, -, -, -, -, -, -, -, -, hclt⟩ := rayentry hTM hTP hθ hr hR
    exact hclt

/-- If the reference point of a class is not periodic, it starts a nonrepeating ray: a repetition
`T^i(r) = T^j(r)`, `i < j`, would make `T^i(r)` a periodic point of the class, and `RefChoice`
would then make `r` periodic. -/
lemma nonRepeating_ref {ref : ℕ → ℕ} (href : RefChoice ref) {n0 : ℕ} (hn0 : 0 < n0)
    (hnp : ¬ IsPeriodic (ref n0)) : NonRepeating (ref n0) := by
  obtain ⟨hr, hrn⟩ := href.1 n0 hn0
  -- a repetition `T^i(r) = T^j(r)` with `i < j` gives a periodic point of the class
  have key : ∀ i j : ℕ, i < j → T^[i] (ref n0) = T^[j] (ref n0) → False := by
    intro i j hlt hij
    refine hnp (href.2.2 n0 hn0 ⟨T^[i] (ref n0), iterate_T_pos hr i,
      merge_equivalence.trans (merge_equivalence.symm (merge_iterate _ i)) hrn, j - i, by omega, ?_⟩)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact hij.symm
  intro i j hij
  have hij' : T^[i] (ref n0) = T^[j] (ref n0) := hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key i j hlt hij'
  · exact key j i hlt hij'.symm

/-- **The entrance law on one class** (proof of Corollary 1.6 [`cor:unconditional`]): `ε`
satisfies the CLT with `(κ_T, V_T)` under uniform sampling from the class of any `n₀ > 0`. -/
theorem cltOn_class_eps (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {ref : ℕ → ℕ} (href : RefChoice ref) {n0 : ℕ} (hn0 : 0 < n0) :
    CLTOn (mergeClass n0) (normalised (eps ref) κT VT) := by
  obtain ⟨hr, hrn⟩ := href.1 n0 hn0
  -- on the class, `ε` is the entry time into `fwdOrbit (ref n₀)`
  have heps : ∀ n ∈ mergeClass n0, eps ref n = entry (fwdOrbit (ref n0)) n := by
    intro n hn
    unfold eps
    rw [href.2.1 n n0 hn.1 hn0 hn.2]
  have hclass : mergeClass (ref n0) = mergeClass n0 := by
    ext m
    constructor
    · rintro ⟨hm, h⟩
      exact ⟨hm, merge_equivalence.trans h hrn⟩
    · rintro ⟨hm, h⟩
      exact ⟨hm, merge_equivalence.trans h (merge_equivalence.symm hrn)⟩
  have hcase : IsPeriodic (ref n0) ∨ NonRepeating (ref n0) := by
    by_cases hper : IsPeriodic (ref n0)
    · exact Or.inl hper
    · exact Or.inr (nonRepeating_ref href hn0 hper)
  have hclt := cltOn_class_entry hTM hTP hθ hr hcase
  rw [hclass] at hclt
  refine cltOn_bounded_shift VT_pos 0 (fun n hn => ?_) hclt
  rw [heps n hn]
  omega

/-! ## Corollary 1.5 -/

/-- **Corollary 1.5 [`cor:dichotomy`].** The cycle clause is stated for every cycle (the paper: a
non-trivial one). -/
theorem dichotomy_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    (∃ dE : ℝ, HasDensity Exc dE ∧ dE < 1 ∧ (Exc.Nonempty → 0 < dE)) ∧
    (HasDensity (Pred T 1) 1 ↔ Exc = ∅) ∧
    (∀ b ∈ Exc, ¬ 3 ∣ b → Pred T b ⊆ Exc ∧ (∃ d > 0, HasDensity (Pred T b) d) ∧
      CLTOn (Pred T b) (normalised (hit T b) κT VT)) ∧
    (∀ b : ℕ, 0 < b → IsPeriodic b →
      (∃ d > 0, HasDensity (Reach (fwdOrbit b)) d) ∧
      CLTOn (Reach (fwdOrbit b)) (normalised (entry (fwdOrbit b)) κT VT)) ∧
    (∀ a : ℕ, 0 < a → NonRepeating a → RayEntryLaw a ∧ RayJointLaw a ∧ RayMovingLaw a) := by
  -- Theorem 1.1(i)-(ii) for a target prime to 3
  have hmain : ∀ b : ℕ, 0 < b → ¬ 3 ∣ b →
      (∃ d > 0, HasDensity (Pred T b) d) ∧ CLTOn (Pred T b) (normalised (hit T b) κT VT) :=
    fun b hb h3 => main_T_of_tao hTM hTP hθ b hb (Positivity.positivity_of_tao hTM hTP hb h3)
  have hexc : ∀ b ∈ Exc, ¬ 3 ∣ b → Pred T b ⊆ Exc ∧ (∃ d > 0, HasDensity (Pred T b) d) ∧
      CLTOn (Pred T b) (normalised (hit T b) κT VT) :=
    fun b hb h3 => ⟨pred_subset_exc hb, hmain b hb.1 h3⟩
  -- `dens E = 1 - dens P_T(1)`
  obtain ⟨⟨p1, hp1, hd1⟩, -⟩ := hmain 1 one_pos (by norm_num)
  have hE : HasDensity Exc (1 - p1) := hd1.compl_pos
  have hEpos : Exc.Nonempty → 0 < 1 - p1 := by
    rintro ⟨n, hn⟩
    obtain ⟨b, hb, h3, -⟩ := exists_three_free_basin hn
    obtain ⟨-, ⟨db, hdb, hdbd⟩, -⟩ := hexc b hb h3
    exact lt_of_lt_of_le hdb (hdbd.mono (pred_subset_exc hb) hE)
  refine ⟨⟨1 - p1, hE, by linarith, hEpos⟩, ⟨fun h1 => ?_, fun hE0 => ?_⟩, hexc,
    fun b hb hper => ?_, fun a ha hR => ⟨rayentry hTM hTP hθ ha hR,
      movingray_joint hTM hTP hθ ha hR, movingray_moving hTM hTP hθ ha hR⟩⟩
  · -- `dens P_T(1) = 1` forces `E = ∅`
    rw [← Set.not_nonempty_iff_eq_empty]
    intro hne
    have h2 := hEpos hne
    have h3 := hd1.unique h1
    linarith
  · -- `E = ∅`: every positive integer reaches `1`
    refine hasDensity_pos.congr_pos fun n hn => ?_
    exact ⟨fun _ => exc_eq_empty_iff.mp hE0 n hn, fun _ => hn⟩
  · -- a cycle through `b`
    obtain ⟨q, hq, hqb⟩ := hper
    have h3 := not_three_dvd_of_periodic hb hq hqb
    rw [reach_cycle hq hqb]
    obtain ⟨hd, hclt⟩ := hmain b hb h3
    refine ⟨hd, cltOn_bounded_shift VT_pos (q - 1) (fun n hn => ?_) hclt⟩
    obtain ⟨h1, h2⟩ := hit_le_entry_cycle hq hqb hn
    constructor <;> omega

/-! ## Corollary 1.6 -/

open Classical in
/-- **Corollary 1.6 [`cor:unconditional`].** For an admissible choice of reference orbits: `ε` is
finite; on each class `C`, `P(N_X ∈ C, Z_X ≤ z) → π_C Φ(z)` under `N_X` uniform on `[1, X]`; the
unconditional law `Z_X ⇒ N(0,1)`; the densities of `{ε ≤ c₀ log n}`; and `0 ≤ τ_{T,1} - ε ≤ 2` on
`P_T(1)`. The change-of-reference clause is `ref_change`. -/
theorem unconditional_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ}
    (hθ : IrrMeasure d ϰ) {ref : ℕ → ℕ} (href : RefChoice ref) :
    (∀ n : ℕ, 0 < n → ∃ k, T^[k] n ∈ fwdOrbit (ref n)) ∧
    (∀ n0 : ℕ, 0 < n0 → ∃ pC : ℝ, HasDensity (mergeClass n0) pC ∧ ∀ z : ℝ,
      Tendsto (fun X : ℕ => ((((Icc 1 X).filter (fun n => n ∈ mergeClass n0 ∧
          normalised (eps ref) κT VT X n ≤ z)).card : ℝ) / X)) atTop (𝓝 (pC * Φ z))) ∧
    CLTOn {n | 0 < n} (normalised (eps ref) κT VT) ∧
    (∀ c0 : ℝ, HasDensity {n | 0 < n ∧ (eps ref n : ℝ) ≤ c0 * Real.log n}
      (if κT < c0 then 1 else if c0 = κT then 1 / 2 else 0)) ∧
    (∀ n ∈ Pred T 1, eps ref n ≤ hit T 1 n ∧ hit T 1 n ≤ eps ref n + 2) := by
  obtain ⟨dC, hdC, -, hsum⟩ := thresholds_iii hTM hTP hθ
  have hdC' : ∀ n0 : ℕ, HasDensity (mergeClass n0) (dC (Quotient.mk mergeSetoid n0)) :=
    fun n0 => by rw [mergeClass_eq_classSet]; exact hdC _
  -- the joint law on each class of the quotient
  have hjoint : ∀ (C : Quotient mergeSetoid) (z : ℝ), Tendsto (fun X : ℕ =>
      ((((Icc 1 X).filter (fun n => n ∈ classSet C ∧
          normalised (eps ref) κT VT X n ≤ z)).card : ℝ) / X)) atTop (𝓝 (dC C * Φ z)) := by
    intro C z
    induction C using Quotient.inductionOn with
    | h n0 =>
      rcases Nat.eq_zero_or_pos n0 with rfl | hn0
      · -- the class of `0` is empty
        have h0 : dC (Quotient.mk mergeSetoid 0) = 0 := by
          have := hdC (Quotient.mk mergeSetoid 0)
          rw [classSet_zero] at this
          exact this.unique hasDensity_empty
        rw [h0, zero_mul]
        refine tendsto_const_nhds.congr fun X => ?_
        rw [classSet_zero]
        simp
      · rw [← mergeClass_eq_classSet]
        exact tendsto_joint_of_cltOn (hdC' n0) (cltOn_class_eps hTM hTP hθ href hn0) z
  -- the unconditional law: the mixture over the classes, with the census `Σ π_C = 1`
  have hclt : CLTOn {n | 0 < n} (normalised (eps ref) κT VT) :=
    cltOn_pos_of_mixture classSet_disjoint hdC hsum hjoint
  refine ⟨eps_finite href, fun n0 hn0 => ⟨_, hdC' n0, fun z => ?_⟩, hclt,
    fun c0 => density_rate VT_pos hclt c0, eps_class_one href⟩
  have := hjoint (Quotient.mk mergeSetoid n0) z
  rwa [← mergeClass_eq_classSet] at this

end CollatzCLT
