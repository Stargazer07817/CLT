import LeanClt.Renewal.Kernel
import LeanClt.Renewal.Chernoff

/-!
# §4.2: tails (Lemma 4.2), absolute convergence and domination

* `int_geom`, `int_geom_tail`: `∑_{t ∈ ℤ} e^{-b|t - t₀|} ≤ 2/(1 - e^{-b})`, and the tail beyond
  `X` is at most `2 e^{-bX/2}(1 + 2/b)`.
* `pwin u t = P(h_t ≤ S_t ≤ h_t + 1)`; `‖R-term_t‖ ≤ 2 pwin u t`.
* `pwin_le_geom`: `pwin u t ≤ (e^{a T(u)} + 2) e^{-a t}` (lower tail, Chernoff), hence absolute
  convergence, `|R_s| ≤ R_0`, and a bound on `R_0(u)` that is uniform for `u ≤ U`.
* `pwin_le_window`: outside `|t - u/c| ≤ X`, `pwin u t ≤ 2 e^{-(κ X/u)|t - u/c|}`.
-/

open Real Finset Complex Filter Topology

noncomputable section

namespace CollatzCLT

/-! ## Two-sided geometric sums over `ℤ` -/

lemma one_div_one_sub_exp_le {a : ℝ} (ha : 0 < a) : 1 / (1 - Real.exp (-a)) ≤ 1 + 1 / a := by
  have h1 : a + 1 ≤ Real.exp a := Real.add_one_le_exp a
  have h2 : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
  have he : 0 < Real.exp (-a) := Real.exp_pos _
  have h3 : Real.exp (-a) * (1 + a) ≤ 1 := by nlinarith
  have h4 : 0 < 1 - Real.exp (-a) := by nlinarith
  rw [div_le_iff₀ h4]
  have : (1 + 1 / a) * (1 - Real.exp (-a)) = (1 + a) / a * (1 - Real.exp (-a)) := by
    field_simp; ring
  rw [this, div_mul_eq_mul_div, le_div_iff₀ ha]
  nlinarith

lemma exp_neg_mul_le_pow {b y : ℝ} (hb : 0 ≤ b) (k : ℕ) (hy : (k : ℝ) ≤ y) :
    Real.exp (-b * y) ≤ Real.exp (-b) ^ k := by
  rw [← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- `∑_{t ∈ ℤ} e^{-b|t - t₀|} ≤ 2/(1 - e^{-b})`. -/
lemma int_geom (b t0 : ℝ) (hb : 0 < b) :
    Summable (fun t : ℤ => Real.exp (-b * |(t : ℝ) - t0|)) ∧
      ∑' t : ℤ, Real.exp (-b * |(t : ℝ) - t0|) ≤ 2 / (1 - Real.exp (-b)) := by
  set m : ℤ := ⌊t0⌋ + 1 with hm
  set f : ℤ → ℝ := fun t => Real.exp (-b * |(t : ℝ) - t0|) with hf
  set g : ℤ → ℝ := fun n => f (n + m) with hg
  set r := Real.exp (-b) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hr]; rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hfl := Int.floor_le t0
  have hfl2 := Int.lt_floor_add_one t0
  have hg1 : ∀ k : ℕ, g k ≤ r ^ k := by
    intro k
    simp only [hg, hf]
    apply exp_neg_mul_le_pow hb.le
    rw [hm]; push_cast
    rw [abs_of_nonneg (by linarith)]; linarith
  have hg2 : ∀ k : ℕ, g (-(k + 1)) ≤ r ^ k := by
    intro k
    simp only [hg, hf]
    apply exp_neg_mul_le_pow hb.le
    rw [hm]; push_cast
    rw [abs_of_nonpos (by linarith)]; linarith
  have hgn : ∀ n, 0 ≤ g n := fun n => (Real.exp_pos _).le
  have hgeo := summable_geometric_of_lt_one hr0 hr1
  have hs1 : Summable (fun k : ℕ => g k) := Summable.of_nonneg_of_le (fun k => hgn _) hg1 hgeo
  have hs2 : Summable (fun k : ℕ => g (-(k + 1))) :=
    Summable.of_nonneg_of_le (fun k => hgn _) hg2 hgeo
  have hgs : Summable g := Summable.of_nat_of_neg_add_one hs1 hs2
  have hfg : f = g ∘ (Equiv.subRight m) := by
    funext t; simp [hg, hf]
  have hfs : Summable f := by rw [hfg]; exact (Equiv.summable_iff _).mpr hgs
  refine ⟨hfs, ?_⟩
  have : ∑' t : ℤ, f t = ∑' n : ℤ, g n := by
    rw [hfg]; exact Equiv.tsum_eq (Equiv.subRight m) g
  change ∑' t : ℤ, f t ≤ _
  rw [this, tsum_of_nat_of_neg_add_one hs1 hs2]
  have e1 : ∑' k : ℕ, g k ≤ ∑' k : ℕ, r ^ k := Summable.tsum_le_tsum hg1 hs1 hgeo
  have e2 : ∑' k : ℕ, g (-(k + 1)) ≤ ∑' k : ℕ, r ^ k := Summable.tsum_le_tsum hg2 hs2 hgeo
  rw [tsum_geometric_of_lt_one hr0 hr1] at e1 e2
  have : 2 / (1 - r) = (1 - r)⁻¹ + (1 - r)⁻¹ := by ring
  rw [this]; linarith

/-- The tail beyond `X`: `∑_{|t - t₀| ≥ X} e^{-b|t - t₀|} ≤ 2 e^{-bX/2}(1 + 2/b)`. -/
lemma int_geom_tail (b t0 X : ℝ) (hb : 0 < b) :
    Summable (fun t : ℤ => if X ≤ |(t : ℝ) - t0| then Real.exp (-b * |(t : ℝ) - t0|) else 0) ∧
      ∑' t : ℤ, (if X ≤ |(t : ℝ) - t0| then Real.exp (-b * |(t : ℝ) - t0|) else 0) ≤
        2 * Real.exp (-(b * X / 2)) * (1 + 2 / b) := by
  obtain ⟨hs, hle⟩ := int_geom (b / 2) t0 (by positivity)
  have hpt : ∀ t : ℤ, (if X ≤ |(t : ℝ) - t0| then Real.exp (-b * |(t : ℝ) - t0|) else 0) ≤
      Real.exp (-(b * X / 2)) * Real.exp (-(b / 2) * |(t : ℝ) - t0|) := by
    intro t
    split_ifs with h
    · rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    · positivity
  have hnn : ∀ t : ℤ, 0 ≤ (if X ≤ |(t : ℝ) - t0| then Real.exp (-b * |(t : ℝ) - t0|) else 0) := by
    intro t; split_ifs <;> positivity
  have hs' := hs.mul_left (Real.exp (-(b * X / 2)))
  refine ⟨Summable.of_nonneg_of_le hnn hpt hs', ?_⟩
  calc _ ≤ ∑' t : ℤ, Real.exp (-(b * X / 2)) * Real.exp (-(b / 2) * |(t : ℝ) - t0|) :=
        Summable.tsum_le_tsum hpt (Summable.of_nonneg_of_le hnn hpt hs') hs'
    _ = Real.exp (-(b * X / 2)) * ∑' t : ℤ, Real.exp (-(b / 2) * |(t : ℝ) - t0|) := tsum_mul_left
    _ ≤ Real.exp (-(b * X / 2)) * (2 / (1 - Real.exp (-(b / 2)))) := by gcongr
    _ ≤ Real.exp (-(b * X / 2)) * (2 * (1 + 2 / b)) := by
        gcongr
        have := one_div_one_sub_exp_le (a := b / 2) (by positivity)
        rw [show 1 / (b / 2) = 2 / b by field_simp] at this
        rw [show 2 / (1 - Real.exp (-(b / 2))) = 2 * (1 / (1 - Real.exp (-(b / 2)))) by ring]
        linarith
    _ = 2 * Real.exp (-(b * X / 2)) * (1 + 2 / b) := by ring

/-- The same tail over `ℕ`. -/
lemma nat_geom_tail (b t0 X : ℝ) (hb : 0 < b) :
    Summable (fun t : ℕ => if X ≤ |(t : ℝ) - t0| then Real.exp (-b * |(t : ℝ) - t0|) else 0) ∧
      ∑' t : ℕ, (if X ≤ |(t : ℝ) - t0| then Real.exp (-b * |(t : ℝ) - t0|) else 0) ≤
        2 * Real.exp (-(b * X / 2)) * (1 + 2 / b) := by
  obtain ⟨hs, hle⟩ := int_geom_tail b t0 X hb
  have hnn : ∀ t : ℤ, 0 ≤ (if X ≤ |(t : ℝ) - t0| then Real.exp (-b * |(t : ℝ) - t0|) else 0) := by
    intro t; split_ifs <;> positivity
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := Nat.cast_injective
  have h1 := hs.comp_injective hinj
  have h2 := tsum_comp_le_tsum_of_inj hs hnn hinj
  simp only [Function.comp_def, Int.cast_natCast] at h1 h2
  exact ⟨h1, h2.trans hle⟩

/-! ## The window probability -/

lemma summable_lawS (n : ℕ) : Summable (lawS n) := by
  simpa using summable_lawS_mul_pow n (x := 1) (by norm_num) (by norm_num)

lemma tsum_lawS (n : ℕ) : ∑' A : ℕ, lawS n A = 1 := by
  have := mgf_lawS n (x := 1) (by norm_num) (by norm_num)
  norm_num at this; exact this

lemma summable_ite_lawS (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Summable (fun A => if P A then lawS n A else 0) :=
  Summable.of_nonneg_of_le (fun A => by split_ifs <;> simp [lawS_nonneg])
    (fun A => by split_ifs <;> simp [lawS_nonneg]) (summable_lawS n)

/-- `pwin u t = P(h_t ≤ S_t ≤ h_t + 1)`. -/
def pwin (u : ℝ) (t : ℕ) : ℝ :=
  ∑' A : ℕ, if hT u t ≤ A ∧ (A : ℝ) ≤ hT u t + 1 then lawS t A else 0

lemma pwin_nonneg (u : ℝ) (t : ℕ) : 0 ≤ pwin u t :=
  tsum_nonneg fun A => by split_ifs <;> simp [lawS_nonneg]

lemma pwin_le_one (u : ℝ) (t : ℕ) : pwin u t ≤ 1 := by
  rw [← tsum_lawS t]
  exact Summable.tsum_le_tsum (fun A => by split_ifs <;> simp [lawS_nonneg])
    (summable_ite_lawS _ _) (summable_lawS t)

lemma pwin_eq_sum (u : ℝ) (t : ℕ) :
    pwin u t = ∑ A ∈ Icc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1),
      (if hT u t ≤ A ∧ (A : ℝ) ≤ hT u t + 1 then lawS t A else 0) := by
  unfold pwin
  refine tsum_eq_sum fun A hA => ?_
  rw [ite_eq_right_iff]; intro h; exact absurd (mem_Icc_of_window h.1 h.2) hA

lemma norm_rterm_le_ite (ρ η s u : ℝ) (t A : ℕ) :
    ‖rterm ρ η s u t A‖ ≤ 2 * (if hT u t ≤ A ∧ (A : ℝ) ≤ hT u t + 1 then lawS t A else 0) := by
  by_cases hw : 0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell
  · have hw' := (window_iff u t A).mp hw
    simp only [hw', and_self, ↓reduceIte]
    exact norm_rterm_le ρ η s u t A
  · have hw' : ¬(hT u t ≤ A ∧ (A : ℝ) ≤ hT u t + 1) := fun h => hw ((window_iff u t A).mpr h)
    unfold rterm; simp only [hw, hw', ↓reduceIte, norm_zero, mul_zero, le_refl]

lemma sum_norm_rterm_le (ρ η s u : ℝ) (t : ℕ) :
    ∑ A ∈ Icc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1), ‖rterm ρ η s u t A‖ ≤ 2 * pwin u t := by
  rw [pwin_eq_sum, mul_sum]
  exact Finset.sum_le_sum fun A _ => norm_rterm_le_ite ρ η s u t A

lemma norm_rinner_le (ρ η s u : ℝ) (t : ℕ) : ‖rinner ρ η s u t‖ ≤ 2 * pwin u t := by
  rw [rinner_eq_sum]
  exact (norm_sum_le _ _).trans (sum_norm_rterm_le ρ η s u t)

/-- `‖R-term_t‖ ≤ Re(R_0-term_t)`. -/
lemma norm_rinner_le_re (ρ η s u : ℝ) (t : ℕ) :
    ‖rinner ρ η s u t‖ ≤ (rinner 0 0 0 u t).re := by
  rw [rinner_eq_sum, rinner_eq_sum, Complex.re_sum]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun A _ => ?_))
  rw [norm_rterm_eq, rterm_zero, Complex.ofReal_re]

lemma hT_sub_two_mul (u : ℝ) (t : ℕ) : hT u t - 2 * t = (u - c * t) / ell := by
  unfold hT; rw [c_eq]; field_simp [ell_pos.ne']; ring

/-- Chernoff on the window: if every window value `A` has `|A - 2t| ≥ x`, then
`pwin u t ≤ 2 exp(-min(x²/(12t), x/8))`. -/
lemma pwin_le_chernoff {u : ℝ} {t : ℕ} (ht : 1 ≤ t) {x : ℝ} (hx : 0 ≤ x)
    (hw : ∀ A : ℕ, hT u t ≤ A → (A : ℝ) ≤ hT u t + 1 → x ≤ |(A : ℝ) - 2 * t|) :
    pwin u t ≤ 2 * Real.exp (-min (x ^ 2 / (12 * t)) (x / 8)) := by
  classical
  refine le_trans ?_ (lawS_chernoff ht hx)
  unfold pwin
  refine Summable.tsum_le_tsum (fun A => ?_) (summable_ite_lawS _ _) (summable_ite_lawS _ _)
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (hw A h1.1 h1.2) h2
  · exact lawS_nonneg _ _
  · exact le_rfl

/-! ## Lower tail: absolute convergence, domination, `R_0` on bounded ranges -/

/-- The lower-tail rate `a = min(c²/(48ℓ²), c/(16ℓ))`. -/
def aL : ℝ := min (c ^ 2 / (48 * ell ^ 2)) (c / (16 * ell))

/-- The threshold `T(u) = 2(max(u,0) + ℓ)/c + 1`. -/
def Tc (u : ℝ) : ℝ := 2 * (max u 0 + ell) / c + 1

lemma aL_pos : 0 < aL := by
  have := c_pos'; have := ell_pos
  unfold aL; exact lt_min (by positivity) (by positivity)

lemma Tc_mono {u u' : ℝ} (h : u ≤ u') : Tc u ≤ Tc u' := by
  unfold Tc
  have := c_pos'
  gcongr

lemma one_le_Tc (u : ℝ) : 1 ≤ Tc u := by
  unfold Tc
  have := c_pos'; have := ell_pos
  have : 0 ≤ 2 * (max u 0 + ell) / c := by
    apply div_nonneg _ c_pos'.le
    have := le_max_right u 0; linarith
  linarith

/-- **Lower tail.** `P(h_t ≤ S_t ≤ h_t + 1) ≤ (e^{a T(u)} + 2) (e^{-a})^t`. -/
lemma pwin_le_geom (u : ℝ) (t : ℕ) :
    pwin u t ≤ (Real.exp (aL * Tc u) + 2) * Real.exp (-aL) ^ t := by
  have hc := c_pos'; have hl := ell_pos; have ha := aL_pos
  have hgeo : Real.exp (-aL) ^ t = Real.exp (-(aL * t)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hgeo]
  have hE : 0 < Real.exp (-(aL * t)) := Real.exp_pos _
  by_cases ht : (t : ℝ) < Tc u
  · calc pwin u t ≤ 1 := pwin_le_one u t
      _ ≤ Real.exp (aL * Tc u) * Real.exp (-(aL * t)) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
      _ ≤ (Real.exp (aL * Tc u) + 2) * Real.exp (-(aL * t)) := by nlinarith
  · push Not at ht
    have ht1 : 1 ≤ t := by
      have := one_le_Tc u
      exact_mod_cast (show (1 : ℝ) ≤ t by linarith)
    set up := max u 0 with hup
    have hup0 : u ≤ up := le_max_left u 0
    have hup1 : 0 ≤ up := le_max_right u 0
    have hct : 2 * (up + ell) ≤ c * t := by
      have : 2 * (up + ell) / c ≤ t := by unfold Tc at ht; linarith
      have h' := (div_le_iff₀ hc).mp this
      linarith [mul_comm (t : ℝ) c]
    set x := (c * t - up - ell) / ell with hx
    have hxge : c * t / (2 * ell) ≤ x := by
      rw [hx, div_le_div_iff₀ (by positivity) hl]; nlinarith
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
    have hx0 : 0 ≤ x := le_trans (by positivity) hxge
    have hw : ∀ A : ℕ, hT u t ≤ A → (A : ℝ) ≤ hT u t + 1 → x ≤ |(A : ℝ) - 2 * t| := by
      intro A _ h2
      have h3 := hT_sub_two_mul u t
      have : (A : ℝ) - 2 * t ≤ -x := by
        have : (u - c * t) / ell ≤ (up - c * t) / ell := by gcongr
        rw [hx]
        have : (A : ℝ) - 2 * t ≤ (up - c * t) / ell + 1 := by linarith
        have e : (up - c * t) / ell + 1 = -((c * t - up - ell) / ell) := by
          field_simp; ring
        linarith
      exact le_trans (by linarith) (neg_le_abs _)
    refine (pwin_le_chernoff ht1 hx0 hw).trans ?_
    have hmin : aL * t ≤ min (x ^ 2 / (12 * t)) (x / 8) := by
      apply le_min
      · have h1 : aL * t ≤ c ^ 2 / (48 * ell ^ 2) * t :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) htpos.le
        refine h1.trans ?_
        rw [le_div_iff₀ (by positivity)]
        have : (c * t / (2 * ell)) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hxge 2
        have e : c ^ 2 / (48 * ell ^ 2) * t * (12 * t) = (c * t / (2 * ell)) ^ 2 := by
          field_simp; ring
        linarith
      · have h1 : aL * t ≤ c / (16 * ell) * t :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) htpos.le
        have e : c / (16 * ell) * t = (c * t / (2 * ell)) / 8 := by field_simp; ring
        linarith
    have : Real.exp (-min (x ^ 2 / (12 * t)) (x / 8)) ≤ Real.exp (-(aL * t)) :=
      Real.exp_le_exp.mpr (by linarith)
    have : 0 ≤ Real.exp (aL * Tc u) := (Real.exp_pos _).le
    nlinarith

lemma exp_neg_aL_lt_one : Real.exp (-aL) < 1 := by
  rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith [aL_pos])

lemma summable_pwin (u : ℝ) : Summable (pwin u) :=
  Summable.of_nonneg_of_le (pwin_nonneg u) (pwin_le_geom u)
    ((summable_geometric_of_lt_one (Real.exp_pos _).le exp_neg_aL_lt_one).mul_left _)

/-- `∑_t P(h_t ≤ S_t ≤ h_t + 1) ≤ (e^{a T(u)} + 2)/(1 - e^{-a})`. -/
lemma tsum_pwin_le (u : ℝ) :
    ∑' t, pwin u t ≤ (Real.exp (aL * Tc u) + 2) / (1 - Real.exp (-aL)) := by
  have hg := (summable_geometric_of_lt_one (Real.exp_pos _).le exp_neg_aL_lt_one).mul_left
    (Real.exp (aL * Tc u) + 2)
  calc _ ≤ ∑' t : ℕ, (Real.exp (aL * Tc u) + 2) * Real.exp (-aL) ^ t :=
        Summable.tsum_le_tsum (pwin_le_geom u) (summable_pwin u) hg
    _ = _ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le exp_neg_aL_lt_one]
        rfl

lemma tsum_norm_rterm_le (ρ η s u : ℝ) (t : ℕ) :
    ∑' A : ℕ, ‖rterm ρ η s u t A‖ ≤ 2 * pwin u t := by
  rw [tsum_eq_sum (s := Icc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1)) (fun A hA => by
    rw [rterm_eq_zero hA, norm_zero])]
  exact sum_norm_rterm_le ρ η s u t

/-- **Theorem 4.1, absolute convergence, iterated form**: `∑_t ∑_A ‖term(t, A)‖ < ∞`; the
`ℕ × ℕ` form is `renewalR_summable`. -/
theorem renewalR_summable' (ρ η s u : ℝ) :
    Summable (fun t : ℕ => ∑' A : ℕ, ‖rterm ρ η s u t A‖) :=
  Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _)
    (tsum_norm_rterm_le ρ η s u) ((summable_pwin u).mul_left 2)

lemma summable_norm_rinner (ρ η s u : ℝ) : Summable (fun t => ‖rinner ρ η s u t‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_rinner_le ρ η s u)
    ((summable_pwin u).mul_left 2)

lemma summable_rinner (ρ η s u : ℝ) : Summable (rinner ρ η s u) :=
  (summable_norm_rinner ρ η s u).of_norm

/-- **Theorem 4.1: domination** `|R_s(u)| ≤ R_0(u)` (restated as `norm_renewalR_le` in
`Theorem41.lean`). -/
theorem norm_renewalR_le' (ρ η s u : ℝ) : ‖renewalR ρ η s u‖ ≤ (renewalR 0 0 0 u).re := by
  rw [renewalR_eq, renewalR_eq, Complex.re_tsum (summable_rinner 0 0 0 u)]
  refine (norm_tsum_le_tsum_norm (summable_norm_rinner ρ η s u)).trans ?_
  refine Summable.tsum_le_tsum (norm_rinner_le_re ρ η s u) (summable_norm_rinner ρ η s u) ?_
  exact Summable.of_nonneg_of_le (fun t => (norm_nonneg _).trans (norm_rinner_le_re 0 0 0 u t))
    (fun t => (Complex.re_le_norm _).trans (norm_rinner_le 0 0 0 u t))
    ((summable_pwin u).mul_left 2)

/-- The crude bound `B(u) = 2(e^{a T(u)} + 2)/(1 - e^{-a})`, nondecreasing in `u`. -/
def Bcrude (u : ℝ) : ℝ := 2 * ((Real.exp (aL * Tc u) + 2) / (1 - Real.exp (-aL)))

lemma Bcrude_mono {u u' : ℝ} (h : u ≤ u') : Bcrude u ≤ Bcrude u' := by
  unfold Bcrude
  have : 0 < 1 - Real.exp (-aL) := by linarith [exp_neg_aL_lt_one]
  have h1 : Real.exp (aL * Tc u) ≤ Real.exp (aL * Tc u') :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Tc_mono h) aL_pos.le)
  have := div_le_div_of_nonneg_right (show Real.exp (aL * Tc u) + 2 ≤ Real.exp (aL * Tc u') + 2 by
    linarith) this.le
  linarith

/-- `‖R_s(u)‖ ≤ B(u)` for every `u`. -/
lemma norm_renewalR_le_crude (ρ η s u : ℝ) : ‖renewalR ρ η s u‖ ≤ Bcrude u := by
  rw [renewalR_eq]
  refine (norm_tsum_le_tsum_norm (summable_norm_rinner ρ η s u)).trans ?_
  calc _ ≤ ∑' t, 2 * pwin u t := Summable.tsum_le_tsum (norm_rinner_le ρ η s u)
        (summable_norm_rinner ρ η s u) ((summable_pwin u).mul_left 2)
    _ = 2 * ∑' t, pwin u t := tsum_mul_left
    _ ≤ Bcrude u := by unfold Bcrude; gcongr; exact tsum_pwin_le u

/-! ## Outside the Gaussian window -/

lemma c_lt_third : c < 1 / 3 := by
  unfold c
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
  have h2 : Real.log (4 / 3) ≠ 4 / 3 - 1 := by
    intro h
    have := Real.exp_log (show (0 : ℝ) < 4 / 3 by norm_num)
    rw [h] at this
    have := Real.add_one_lt_exp (show (4 / 3 - 1 : ℝ) ≠ 0 by norm_num)
    linarith
  have := lt_of_le_of_ne this h2
  linarith

/-- The window-tail rate constant `κ = c³/(96ℓ²)`. -/
def κW : ℝ := c ^ 3 / (96 * ell ^ 2)

lemma κW_pos : 0 < κW := by unfold κW; have := c_pos'; have := ell_pos; positivity

lemma pwin_zero {u : ℝ} (hu : 0 < u) : pwin u 0 = 0 := by
  unfold pwin
  refine (tsum_congr fun A => ?_).trans tsum_zero
  rw [ite_eq_right_iff]
  intro h
  have h1 := h.1
  unfold hT at h1
  simp only [Nat.cast_zero, mul_zero, add_zero] at h1
  rcases Nat.eq_zero_or_pos A with hA | hA
  · subst hA
    have : 0 < u / ell := div_pos hu ell_pos
    simp at h1; linarith
  · simp [lawS, Nat.pos_iff_ne_zero.mp hA]

/-- **Lemma 4.2, window tail.** If `2ℓ/c ≤ X ≤ u` and `|t - u/c| ≥ X`, then
`P(h_t ≤ S_t ≤ h_t + 1) ≤ 2 exp(-(κX/u)|t - u/c|)`. -/
lemma pwin_le_window {u X : ℝ} (hu : 0 < u) (hX1 : 2 * ell / c ≤ X) (hX2 : X ≤ u) (t : ℕ)
    (ht : X ≤ |(t : ℝ) - u / c|) :
    pwin u t ≤ 2 * Real.exp (-(κW * X / u * |(t : ℝ) - u / c|)) := by
  have hc := c_pos'; have hl := ell_pos
  rcases Nat.eq_zero_or_pos t with h0 | ht1
  · subst h0; rw [pwin_zero hu]; positivity
  set y := |(t : ℝ) - u / c| with hy
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX1
  have hy0 : 0 < y := lt_of_lt_of_le hX0 ht
  set x := c * y / (2 * ell) with hx
  have hT0 : (0 : ℝ) < t := by exact_mod_cast ht1
  have htle : (t : ℝ) ≤ u / c + y := by
    have := le_abs_self ((t : ℝ) - u / c); linarith
  have hw : ∀ A : ℕ, hT u t ≤ A → (A : ℝ) ≤ hT u t + 1 → x ≤ |(A : ℝ) - 2 * t| := by
    intro A h1 h2
    have h3 : |hT u t - 2 * t| = c * y / ell := by
      rw [hT_sub_two_mul, abs_div, abs_of_pos hl, hy]
      congr 1
      rw [show u - c * t = -(c * ((t : ℝ) - u / c)) by field_simp; ring, abs_neg, abs_mul,
        abs_of_pos hc]
    have h4 : |hT u t - 2 * t| ≤ |(A : ℝ) - 2 * t| + 1 := by
      have := abs_sub_abs_le_abs_sub (hT u t - 2 * t) ((A : ℝ) - 2 * t)
      have : |hT u t - 2 * t - ((A : ℝ) - 2 * t)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      linarith [abs_sub_abs_le_abs_sub (hT u t - 2 * t) ((A : ℝ) - 2 * t)]
    have h5 : 1 ≤ c * y / (2 * ell) := by
      rw [le_div_iff₀ (by positivity)]
      have : 2 * ell / c * c = 2 * ell := by field_simp
      nlinarith
    have : c * y / ell = 2 * (c * y / (2 * ell)) := by field_simp
    rw [hx]; linarith
  refine (pwin_le_chernoff ht1 (by positivity) hw).trans ?_
  have hcX : c * X ≤ u := by nlinarith [c_lt_third]
  -- `c X t ≤ 2 u y`
  have key : c * X * t ≤ 2 * u * y := by
    have e : c * (u / c) = u := by field_simp
    have h1 : c * X * t ≤ c * X * (u / c + y) := by
      apply mul_le_mul_of_nonneg_left htle; positivity
    have h2 : c * X * (u / c + y) = X * u + c * X * y := by
      rw [mul_add, show c * X * (u / c) = X * (c * (u / c)) by ring, e]
    nlinarith
  have hmin : κW * X / u * y ≤ min (x ^ 2 / (12 * t)) (x / 8) := by
    apply le_min
    · have e1 : x ^ 2 / (12 * t) = c ^ 2 * y ^ 2 / (48 * ell ^ 2 * t) := by
        rw [hx]; field_simp; ring
      have e2 : κW * X / u * y = c ^ 3 * X * y / (96 * ell ^ 2 * u) := by
        unfold κW; field_simp
      rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
      have : c ^ 3 * X * y * (48 * ell ^ 2 * t) = (48 * c ^ 2 * ell ^ 2 * y) * (c * X * t) := by
        ring
      have h' : c ^ 2 * y ^ 2 * (96 * ell ^ 2 * u) = (48 * c ^ 2 * ell ^ 2 * y) * (2 * u * y) := by
        ring
      rw [this, h']
      exact mul_le_mul_of_nonneg_left key (by positivity)
    · have e2 : κW * X / u * y = c ^ 3 * X * y / (96 * ell ^ 2 * u) := by
        unfold κW; field_simp
      have e3 : x / 8 = c * y / (16 * ell) := by rw [hx]; field_simp; ring
      rw [e2, e3, div_le_div_iff₀ (by positivity) (by positivity)]
      have hc6 : c ≤ 6 * ell := by linarith [c_lt_third, ell_gt]
      have : c ^ 2 * X ≤ 6 * ell * u := by
        calc c ^ 2 * X = c * (c * X) := by ring
          _ ≤ c * u := by gcongr
          _ ≤ 6 * ell * u := by gcongr
      have e4 : c ^ 3 * X * y * (16 * ell) = (16 * c * ell * y) * (c ^ 2 * X) := by ring
      have e5 : c * y * (96 * ell ^ 2 * u) = (16 * c * ell * y) * (6 * ell * u) := by ring
      rw [e4, e5]
      exact mul_le_mul_of_nonneg_left this (by positivity)
  have := Real.exp_le_exp.mpr (neg_le_neg hmin)
  linarith

/-- **Lemma 4.2, summed.** With `b = κX/u`,
`∑_{|t - u/c| ≥ X} P(h_t ≤ S_t ≤ h_t + 1) ≤ 4 e^{-bX/2}(1 + 2/b)`. -/
lemma window_tail {u X : ℝ} (hu : 0 < u) (hX1 : 2 * ell / c ≤ X) (hX2 : X ≤ u) :
    Summable (fun t : ℕ => if X ≤ |(t : ℝ) - u / c| then pwin u t else 0) ∧
      ∑' t : ℕ, (if X ≤ |(t : ℝ) - u / c| then pwin u t else 0) ≤
        4 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u)) := by
  have hX0 : 0 < X := lt_of_lt_of_le (by have := c_pos'; have := ell_pos; positivity) hX1
  have hb : 0 < κW * X / u := by have := κW_pos; positivity
  obtain ⟨hs, hle⟩ := nat_geom_tail (κW * X / u) (u / c) X hb
  have hpt : ∀ t : ℕ, (if X ≤ |(t : ℝ) - u / c| then pwin u t else 0) ≤
      2 * (if X ≤ |(t : ℝ) - u / c| then
        Real.exp (-(κW * X / u) * |(t : ℝ) - u / c|) else 0) := by
    intro t
    split_ifs with h
    · rw [neg_mul]; exact pwin_le_window hu hX1 hX2 t h
    · simp
  have hnn : ∀ t : ℕ, 0 ≤ (if X ≤ |(t : ℝ) - u / c| then pwin u t else 0) := by
    intro t; split_ifs
    · exact pwin_nonneg u t
    · exact le_rfl
  have hs2 := hs.mul_left 2
  refine ⟨Summable.of_nonneg_of_le hnn hpt hs2, ?_⟩
  calc _ ≤ ∑' t : ℕ, 2 * (if X ≤ |(t : ℝ) - u / c| then
          Real.exp (-(κW * X / u) * |(t : ℝ) - u / c|) else 0) :=
        Summable.tsum_le_tsum hpt (Summable.of_nonneg_of_le hnn hpt hs2) hs2
    _ = 2 * ∑' t : ℕ, (if X ≤ |(t : ℝ) - u / c| then
          Real.exp (-(κW * X / u) * |(t : ℝ) - u / c|) else 0) := tsum_mul_left
    _ ≤ 2 * (2 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u))) := by gcongr
    _ = _ := by ring

end CollatzCLT
