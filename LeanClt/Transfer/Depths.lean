import LeanClt.Transfer.Identity
import LeanClt.Renewal.Theorem41

/-!
# Lemma 5.9: restoring all depths, and the cutoff `S_m ≤ 3m`

After the exact identity, the sum over the depths `r ∈ J_Y` is, for each target `M` and coarse
total `S₁`, the partial renewal sum `∑_{t : m+t ∈ J_Y} R_t(u)`, `u = log(Y/M) - Z_m`. It is
compared with the full kernel `R^{ρ,η}_s(u) = ∑_t R_t(u)` restricted to `S₁ ∈ [m, 3m]`:

* typical `S₁` (`|S₁ - 2m| ≤ L^{0.6}`): `u ≍ L` and every omitted `t` has
  `|t - u/c| ≥ L^{0.8}` (`u_bounds`), so the omitted terms are a window tail
  (`window_tail`, §4), of size `8 e^{-κ L^{0.6}/2} (1 + 2L^{0.2}/κ)`;
* atypical `S₁`: both sides are bounded by the unconditional renewal bounds, and the geometric
  weight of atypical `S₁` is `≤ P(|S_m - 2m| ≥ L^{0.6})`.

The harmonic bound at the coarse depth `m` (`sum_E_muJ_le`) controls the sum over targets.
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-! ## Numerical side conditions beyond `Large` -/

/-- Further numerical conditions on `L`, `m`, `n₀` used for the depth restoration and the final
error terms. -/
structure Large2 (x : ℝ) : Prop where
  m6 : Lx x ^ (0.6 : ℝ) ≤ mT x
  ulo : Lx x ^ (0.8 : ℝ) + 2 * c * mT x + Lx x ^ (0.7 : ℝ) + ell * Lx x ^ (0.6 : ℝ) ≤
    (alpha - 1) * Lx x
  uhi : (alpha ^ 2 - 1) * Lx x + Lx x ^ (0.7 : ℝ) + ell * Lx x ^ (0.6 : ℝ) ≤ Lx x
  tgap : 4 * (Lx x ^ (0.7 : ℝ) + ell * Lx x ^ (0.6 : ℝ)) ≤ Lx x ^ (0.8 : ℝ)
  xw : 2 * ell / c ≤ Lx x ^ (0.8 : ℝ)
  nsmall : ell * (n0 x + Lx x ^ (0.6 : ℝ)) ≤ 0.2 * Lx x
  l04 : 4 ≤ Lx x ^ (0.4 : ℝ)
  n6 : 6 * (n0 x : ℝ) ≤ Lx x
  u0 : Lx x ^ (0.7 : ℝ) + 2 * mT x ≤ (alpha - 1) * Lx x

/-! ## The depth window -/

lemma logY_bounds {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y) (hY2 : Y ≤ x ^ (alpha ^ 2)) :
    alpha * Lx x ≤ Real.log Y ∧ Real.log Y ≤ alpha ^ 2 * Lx x := by
  obtain ⟨hx0, -, -, hY0⟩ := large_facts hL hY1
  constructor
  · rw [← log_rpow_Lx hx0]; exact Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hY1
  · rw [← log_rpow_Lx hx0]; exact Real.log_le_log hY0 hY2

lemma rY_eq {x Y : ℝ} (hx0 : 0 < x) (hY0 : 0 < Y) : rY x Y = (Real.log Y - Lx x) / c - mT x := by
  unfold rY; rw [Real.log_div hY0.ne' hx0.ne']; rfl

lemma rY_bounds {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y) (hY2 : Y ≤ x ^ (alpha ^ 2)) :
    (alpha - 1) * Lx x / c - mT x ≤ rY x Y ∧ rY x Y ≤ (alpha ^ 2 - 1) * Lx x / c - mT x := by
  obtain ⟨hx0, -, -, hY0⟩ := large_facts hL hY1
  obtain ⟨h1, h2⟩ := logY_bounds hL hY1 hY2
  have hc := c_pos'
  rw [rY_eq hx0 hY0]
  constructor
  · have : (alpha - 1) * Lx x ≤ Real.log Y - Lx x := by linarith
    have := div_le_div_of_nonneg_right this hc.le
    linarith
  · have : Real.log Y - Lx x ≤ (alpha ^ 2 - 1) * Lx x := by linarith
    have := div_le_div_of_nonneg_right this hc.le
    linarith

/-- `J_Y ⊆ [m, n₀ - m]` (5.5). -/
lemma JY_bounds {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y) (hY2 : Y ≤ x ^ (alpha ^ 2))
    {r : ℕ} (hr : r ∈ JY x Y) : mT x ≤ r ∧ r + mT x ≤ n0 x := by
  unfold JY at hr
  rw [mem_filter, mem_range] at hr
  obtain ⟨-, hw⟩ := hr
  obtain ⟨h1, h2⟩ := rY_bounds hL hY1 hY2
  have hlo := hL.jlow; have hhi := hL.jhigh
  have hw' := abs_le.mp hw
  constructor
  · have : (mT x : ℝ) ≤ r := by linarith [hw'.1]
    exact_mod_cast this
  · have : (r : ℝ) + mT x ≤ n0 x := by linarith [hw'.2]
    exact_mod_cast this

/-- Outside `J_Y`, the depth is more than `2L^{0.8}` from `r_Y`. -/
lemma not_JY {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y) (hY2 : Y ≤ x ^ (alpha ^ 2))
    {r : ℕ} (hr : r ∉ JY x Y) : 2 * Lx x ^ (0.8 : ℝ) < |(r : ℝ) - rY x Y| := by
  unfold JY at hr
  rw [mem_filter, mem_range, not_and_or] at hr
  rcases hr with hr | hr
  · have hr' : (n0 x : ℝ) + 1 ≤ r := by exact_mod_cast (not_lt.mp hr)
    obtain ⟨-, h2⟩ := rY_bounds hL hY1 hY2
    have hhi := hL.jhigh
    have hm0 : (0 : ℝ) ≤ mT x := Nat.cast_nonneg _
    have h08 : 0 ≤ Lx x ^ (0.8 : ℝ) := Real.rpow_nonneg (by linarith [hL.L_ge]) _
    rw [abs_of_nonneg (by linarith)]
    linarith
  · push Not at hr; exact hr

/-! ## The argument `u` of the kernel -/

lemma Mset_log {x : ℝ} {M : ℕ} (hM : M ∈ Mset x) :
    |Real.log M - (Lx x + c * mT x)| ≤ Lx x ^ (0.7 : ℝ) := hM.2.2.2

/-- **The kernel argument for a typical coarse total.** `L^{0.8} ≤ u ≤ L`, and every depth
outside `J_Y` is at distance `≥ L^{0.8}` from `u/c`. -/
theorem u_bounds {x Y : ℝ} (hL : Large x) (hL2 : Large2 x) (hY1 : x ^ alpha ≤ Y)
    (hY2 : Y ≤ x ^ (alpha ^ 2)) {M : ℕ} (hM : M ∈ Mset x) {S1 : ℕ} (hS1 : typT x (mT x) S1) :
    Lx x ^ (0.8 : ℝ) ≤ uMS Y M S1 (mT x) ∧ uMS Y M S1 (mT x) ≤ Lx x ∧
      ∀ t : ℕ, t + mT x ∉ JY x Y →
        Lx x ^ (0.8 : ℝ) ≤ |(t : ℝ) - uMS Y M S1 (mT x) / c| := by
  obtain ⟨hx0, -, -, hY0⟩ := large_facts hL hY1
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.1.pos
  obtain ⟨hY1', hY2'⟩ := logY_bounds hL hY1 hY2
  have hlM := abs_le.mp (Mset_log hM)
  have hS := abs_le.mp hS1
  have hc := c_pos'; have hc4 := c_ge_quarter; have hl := ell_pos
  have hceq := c_eq
  have hu : uMS Y M S1 (mT x) =
      Real.log Y - Real.log M - ell * ((S1 : ℝ) - 2 * mT x) - c * mT x := by
    unfold uMS; rw [Real.log_div hY0.ne' hM0.ne']; rw [hceq]; ring
  have hS' : |ell * ((S1 : ℝ) - 2 * mT x)| ≤ ell * Lx x ^ (0.6 : ℝ) := by
    rw [abs_mul, abs_of_pos hl]; exact mul_le_mul_of_nonneg_left hS1 hl.le
  have hS'' := abs_le.mp hS'
  have halpha : alpha = 1.001 := rfl
  refine ⟨?_, ?_, ?_⟩
  · have := hL2.ulo; rw [hu]; nlinarith
  · have := hL2.uhi; rw [hu]; nlinarith
  · intro t ht
    have hJ := not_JY hL hY1 hY2 ht
    rw [rY_eq hx0 hY0] at hJ
    push_cast at hJ
    -- `t - u/c = (t + m - r_Y) + (log M - L - cm + ℓ(S₁ - 2m))/c`
    have hid : (t : ℝ) - uMS Y M S1 (mT x) / c =
        ((t : ℝ) + mT x - ((Real.log Y - Lx x) / c - mT x)) +
          (Real.log M - (Lx x + c * mT x) + ell * ((S1 : ℝ) - 2 * mT x)) / c := by
      rw [hu]; field_simp; ring
    have herr : |(Real.log M - (Lx x + c * mT x) + ell * ((S1 : ℝ) - 2 * mT x)) / c| ≤
        4 * (Lx x ^ (0.7 : ℝ) + ell * Lx x ^ (0.6 : ℝ)) := by
      rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]
      have h1 := abs_add_le (Real.log M - (Lx x + c * mT x)) (ell * ((S1 : ℝ) - 2 * mT x))
      have h2 : 0 ≤ Lx x ^ (0.7 : ℝ) + ell * Lx x ^ (0.6 : ℝ) := by
        have := Real.rpow_nonneg (show 0 ≤ Lx x by linarith [hL.L_ge]) (0.7 : ℝ)
        have := Real.rpow_nonneg (show 0 ≤ Lx x by linarith [hL.L_ge]) (0.6 : ℝ)
        positivity
      nlinarith [Mset_log hM]
    have hg := hL2.tgap
    rw [hid]
    have := abs_sub_abs_le_abs_add ((t : ℝ) + mT x - ((Real.log Y - Lx x) / c - mT x))
      ((Real.log M - (Lx x + c * mT x) + ell * ((S1 : ℝ) - 2 * mT x)) / c)
    have h3 : |((t : ℝ) + mT x - ((Real.log Y - Lx x) / c - mT x))| -
        |-((Real.log M - (Lx x + c * mT x) + ell * ((S1 : ℝ) - 2 * mT x)) / c)| ≤
        |((t : ℝ) + mT x - ((Real.log Y - Lx x) / c - mT x)) +
          (Real.log M - (Lx x + c * mT x) + ell * ((S1 : ℝ) - 2 * mT x)) / c| := by
      have := abs_sub_abs_le_abs_sub ((t : ℝ) + mT x - ((Real.log Y - Lx x) / c - mT x))
        (-((Real.log M - (Lx x + c * mT x) + ell * ((S1 : ℝ) - 2 * mT x)) / c))
      rwa [sub_neg_eq_add] at this
    rw [abs_neg] at h3
    linarith

/-! ## Renewal tails -/

/-- **Omitted depths form a window tail.** -/
theorem renewal_minus_window {u X : ℝ} (hu : 0 < u) (hX1 : 2 * ell / c ≤ X) (hX2 : X ≤ u)
    (ρ η s : ℝ) (I : Finset ℕ) (hI : ∀ t ∉ I, X ≤ |(t : ℝ) - u / c|) :
    ‖renewalR ρ η s u - ∑ t ∈ I, rinner ρ η s u t‖ ≤
      2 * (4 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u))) := by
  classical
  obtain ⟨hsum, htail⟩ := window_tail hu hX1 hX2
  rw [renewalR_eq, tsum_eq_sum_add_tsum_ite (summable_rinner ρ η s u) I, add_sub_cancel_left]
  have hs1 : Summable (fun t : ℕ => ‖(if t ∈ I then 0 else rinner ρ η s u t)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => ?_)
      (summable_norm_rinner ρ η s u)
    split_ifs <;> simp
  refine (norm_tsum_le_tsum_norm hs1).trans ?_
  have hle : ∀ t : ℕ, ‖(if t ∈ I then 0 else rinner ρ η s u t)‖ ≤
      2 * (if X ≤ |(t : ℝ) - u / c| then pwin u t else 0) := by
    intro t
    by_cases ht : t ∈ I
    · simp only [ht, ↓reduceIte, norm_zero]
      split_ifs <;> [exact mul_nonneg (by norm_num) (pwin_nonneg u t); simp]
    · simp only [ht, ↓reduceIte, hI t ht]
      exact norm_rinner_le ρ η s u t
  calc ∑' t : ℕ, ‖(if t ∈ I then 0 else rinner ρ η s u t)‖
      ≤ ∑' t : ℕ, 2 * (if X ≤ |(t : ℝ) - u / c| then pwin u t else 0) :=
        Summable.tsum_le_tsum hle hs1 (hsum.mul_left 2)
    _ = 2 * ∑' t : ℕ, (if X ≤ |(t : ℝ) - u / c| then pwin u t else 0) := tsum_mul_left
    _ ≤ _ := by gcongr

/-- A uniform bound for the tail at `X = L^{0.8}`, `u ≤ L`. -/
lemma tail_uniform {L u : ℝ} (hL : 1 ≤ L) (hu1 : L ^ (0.8 : ℝ) ≤ u) (hu2 : u ≤ L) :
    2 * (4 * Real.exp (-(κW * L ^ (0.8 : ℝ) / u * L ^ (0.8 : ℝ) / 2)) *
        (1 + 2 / (κW * L ^ (0.8 : ℝ) / u))) ≤
      8 * Real.exp (-(κW * L ^ (0.6 : ℝ) / 2)) * (1 + 2 * L ^ (0.2 : ℝ) / κW) := by
  have hκ := κW_pos
  have hL0 : 0 < L := by linarith
  have h8 : 0 < L ^ (0.8 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hu0 : 0 < u := lt_of_lt_of_le h8 hu1
  have e1 : L ^ (0.8 : ℝ) * L ^ (0.8 : ℝ) = L ^ (0.6 : ℝ) * L := by
    rw [← Real.rpow_add hL0, show L ^ (0.6 : ℝ) * L = L ^ (0.6 : ℝ) * L ^ (1 : ℝ) by
      rw [Real.rpow_one], ← Real.rpow_add hL0]; norm_num
  have e2 : L = L ^ (0.2 : ℝ) * L ^ (0.8 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have h06 : 0 < L ^ (0.6 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have h02 : 0 < L ^ (0.2 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hexp : Real.exp (-(κW * L ^ (0.8 : ℝ) / u * L ^ (0.8 : ℝ) / 2)) ≤
      Real.exp (-(κW * L ^ (0.6 : ℝ) / 2)) := by
    apply Real.exp_le_exp.mpr
    have : κW * L ^ (0.6 : ℝ) ≤ κW * L ^ (0.8 : ℝ) / u * L ^ (0.8 : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hu0, mul_assoc κW (L ^ (0.8 : ℝ)), e1]
      have := mul_le_mul_of_nonneg_left hu2 (mul_nonneg hκ.le h06.le)
      nlinarith
    linarith
  have hfrac : 2 / (κW * L ^ (0.8 : ℝ) / u) ≤ 2 * L ^ (0.2 : ℝ) / κW := by
    rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hκ]
    have : u ≤ L ^ (0.2 : ℝ) * L ^ (0.8 : ℝ) := e2 ▸ hu2
    nlinarith
  have hpos : 0 ≤ Real.exp (-(κW * L ^ (0.8 : ℝ) / u * L ^ (0.8 : ℝ) / 2)) := (Real.exp_pos _).le
  have hpos2 : 0 ≤ 1 + 2 / (κW * L ^ (0.8 : ℝ) / u) := by positivity
  calc 2 * (4 * Real.exp (-(κW * L ^ (0.8 : ℝ) / u * L ^ (0.8 : ℝ) / 2)) *
        (1 + 2 / (κW * L ^ (0.8 : ℝ) / u)))
      = 8 * (Real.exp (-(κW * L ^ (0.8 : ℝ) / u * L ^ (0.8 : ℝ) / 2)) *
        (1 + 2 / (κW * L ^ (0.8 : ℝ) / u))) := by ring
    _ ≤ 8 * (Real.exp (-(κW * L ^ (0.6 : ℝ) / 2)) * (1 + 2 * L ^ (0.2 : ℝ) / κW)) := by
        gcongr
    _ = _ := by ring

/-- The partial renewal sums are bounded uniformly. -/
theorem norm_sum_rinner_le : ∃ B : ℝ, 0 ≤ B ∧ ∀ (ρ η s u : ℝ) (I : Finset ℕ),
    ‖∑ t ∈ I, rinner ρ η s u t‖ ≤ B := by
  obtain ⟨B, hB⟩ := renewalR_zero_bounded
  refine ⟨max B 0, le_max_right _ _, fun ρ η s u I => ?_⟩
  have hre : ∀ t, 0 ≤ (rinner 0 0 0 u t).re :=
    fun t => (norm_nonneg _).trans (norm_rinner_le_re 0 0 0 u t)
  have hsre : Summable (fun t => (rinner 0 0 0 u t).re) :=
    Complex.reCLM.summable (summable_rinner 0 0 0 u)
  calc ‖∑ t ∈ I, rinner ρ η s u t‖ ≤ ∑ t ∈ I, ‖rinner ρ η s u t‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ I, (rinner 0 0 0 u t).re :=
        Finset.sum_le_sum fun t _ => norm_rinner_le_re ρ η s u t
    _ ≤ ∑' t, (rinner 0 0 0 u t).re := hsre.sum_le_tsum I (fun t _ => hre t)
    _ = (renewalR 0 0 0 u).re := by
        rw [renewalR_eq, Complex.re_tsum (summable_rinner 0 0 0 u)]
    _ ≤ max B 0 := (hB u).trans (le_max_left _ _)

/-! ## The harmonic bound at the coarse depth -/

/-- `∑_{M ∈ E} (3^m/M) P(S_m = S₁, X_m ≡ M) ≤ 5 P(S_m = S₁)`. -/
theorem sum_E_muJ_le {x : ℝ} (hL : Large x) (E : Finset ℕ) (hE : (↑E : Set ℕ) ⊆ Mset x)
    (hmn : mT x + mT x ≤ n0 x) (S1 : ℕ) :
    ∑ M ∈ E, (3 : ℝ) ^ mT x / M * muJ (mT x) S1 (M : ZMod (3 ^ mT x)) ≤ 5 * lawS (mT x) S1 := by
  classical
  unfold muJ
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, ← sum_words_half, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have hH := harmonic hL E hE hmn (Xmod a)
  calc ∑ M ∈ E, (3 : ℝ) ^ mT x / M * (if Xmod a = (M : ZMod (3 ^ mT x)) then
        (1 / 2 : ℝ) ^ S1 else 0)
      = (1 / 2 : ℝ) ^ S1 * ((3 : ℝ) ^ mT x *
          ∑ M ∈ E.filter (fun M : ℕ => (M : ZMod (3 ^ mT x)) = Xmod a), (1 : ℝ) / M) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun M _ => ?_
        by_cases h : (M : ZMod (3 ^ mT x)) = Xmod a
        · rw [if_pos h.symm, if_pos h]; ring
        · rw [if_neg (Ne.symm h), if_neg h]; ring
    _ ≤ (1 / 2 : ℝ) ^ S1 * 5 := by gcongr
    _ = 5 * (1 / 2 : ℝ) ^ S1 := by ring

/-! ## The renewal side -/

lemma two_m_le_n0 {x : ℝ} (hL : Large x) : mT x + mT x ≤ n0 x := by
  have h1 := hL.jlow; have h2 := hL.jhigh
  have hc := c_pos'
  have h08 : 0 ≤ Lx x ^ (0.8 : ℝ) := Real.rpow_nonneg (by linarith [hL.L_ge]) _
  have hL0 : 0 ≤ Lx x := by linarith [hL.L_ge]
  have h3 : (alpha - 1) * Lx x / c ≤ (alpha ^ 2 - 1) * Lx x / c := by
    apply div_le_div_of_nonneg_right _ hc.le
    unfold alpha; nlinarith
  have : (mT x : ℝ) + mT x ≤ n0 x := by linarith
  exact_mod_cast this

/-- The uniform tail bound `T_b(L) = 8 e^{-κ L^{0.6}/2} (1 + 2L^{0.2}/κ)`. -/
def Tb (L : ℝ) : ℝ := 8 * Real.exp (-(κW * L ^ (0.6 : ℝ) / 2)) * (1 + 2 * L ^ (0.2 : ℝ) / κW)

lemma Tb_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ Tb L := by
  unfold Tb
  have := κW_pos
  have := Real.rpow_nonneg hL (0.2 : ℝ)
  positivity

open Classical in
/-- **One target and one coarse total.** -/
theorem pair_bound {x Y : ℝ} (hL : Large x) (hL2 : Large2 x) (hY1 : x ^ alpha ≤ Y)
    (hY2 : Y ≤ x ^ (alpha ^ 2)) (ρ η s B : ℝ) (hBR : ∀ u, ‖renewalR ρ η s u‖ ≤ B)
    (hBI : ∀ u (I : Finset ℕ), ‖∑ t ∈ I, rinner ρ η s u t‖ ≤ B) {M : ℕ} (hM : M ∈ Mset x)
    (S1 : ℕ) (I : Finset ℕ) (hI : ∀ t ∉ I, t + mT x ∉ JY x Y) :
    ‖∑ t ∈ I, rinner ρ η s (uMS Y M S1 (mT x)) t -
        (if S1 ∈ Icc (mT x) (3 * mT x) then renewalR ρ η s (uMS Y M S1 (mT x)) else 0)‖ ≤
      Tb (Lx x) + (if typT x (mT x) S1 then 0 else 2 * B) := by
  have hLL : 1 ≤ Lx x := by linarith [hL.L_ge]
  by_cases hT : typT x (mT x) S1
  · rw [if_pos hT, add_zero]
    have hmem : S1 ∈ Icc (mT x) (3 * mT x) := by
      have h := abs_le.mp hT
      have hm6 := hL2.m6
      rw [mem_Icc]
      constructor
      · have : (mT x : ℝ) ≤ S1 := by linarith [h.1]
        exact_mod_cast this
      · have : (S1 : ℝ) ≤ 3 * mT x := by linarith [h.2]
        exact_mod_cast this
    rw [if_pos hmem, norm_sub_rev]
    obtain ⟨hu1, hu2, hut⟩ := u_bounds hL hL2 hY1 hY2 hM hT
    have hu0 : 0 < uMS Y M S1 (mT x) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hu1
    refine (renewal_minus_window hu0 hL2.xw hu1 ρ η s I (fun t ht => hut t (hI t ht))).trans ?_
    exact tail_uniform hLL hu1 hu2
  · rw [if_neg hT]
    have hT0 := Tb_nonneg (show 0 ≤ Lx x by linarith)
    calc _ ≤ ‖∑ t ∈ I, rinner ρ η s (uMS Y M S1 (mT x)) t‖ +
          ‖(if S1 ∈ Icc (mT x) (3 * mT x) then renewalR ρ η s (uMS Y M S1 (mT x)) else 0)‖ :=
          norm_sub_le _ _
      _ ≤ B + B := by
          gcongr
          · exact hBI _ _
          · split_ifs
            · exact hBR _
            · rw [norm_zero]; exact (norm_nonneg _).trans (hBI 0 ∅)
      _ ≤ Tb (Lx x) + 2 * B := by linarith

/-- **Lemma 5.9 and the cutoff, on the renewal side.** -/
theorem renewal_side {x Y : ℝ} (hL : Large x) (hL2 : Large2 x) (hY1 : x ^ alpha ≤ Y)
    (hY2 : Y ≤ x ^ (alpha ^ 2)) (E : Finset ℕ) (hE : (↑E : Set ℕ) ⊆ Mset x) (q : ℕ → ℝ)
    (ρ η s B : ℝ) (hB0 : 0 ≤ B) (hBR : ∀ u, ‖renewalR ρ η s u‖ ≤ B)
    (hBI : ∀ u (I : Finset ℕ), ‖∑ t ∈ I, rinner ρ η s u t‖ ≤ B) {K : ℕ} (hK3 : 3 * mT x ≤ K)
    (I : Finset ℕ) (hI : ∀ t ∉ I, t + mT x ∉ JY x Y) :
    ‖∑ M ∈ E, ∑ S1 ∈ range (K + 1), (muJ (mT x) S1 (M : ZMod (3 ^ mT x)) : ℂ) *
          (((Y * 3 ^ mT x / M : ℝ) : ℂ) * phase q ρ η s M S1 (mT x) *
            ∑ t ∈ I, rinner ρ η s (uMS Y M S1 (mT x)) t) -
        ∑ M ∈ E, ∑ S1 ∈ Icc (mT x) (3 * mT x), (muJ (mT x) S1 (M : ZMod (3 ^ mT x)) : ℂ) *
          (((Y * 3 ^ mT x / M : ℝ) : ℂ) * phase q ρ η s M S1 (mT x) *
            renewalR ρ η s (uMS Y M S1 (mT x)))‖ ≤
      5 * Y * (Tb (Lx x) + 2 * B * chern (mT x) (Lx x ^ (0.6 : ℝ))) := by
  classical
  obtain ⟨hx0, -, -, hY0⟩ := large_facts hL hY1
  set m := mT x with hm
  have hm1 : 1 ≤ m := hL.m_ge
  have hLL : 0 ≤ Lx x := by linarith [hL.L_ge]
  have hT0 := Tb_nonneg hLL
  have hIcc : Icc m (3 * m) = (range (K + 1)).filter (fun S1 => S1 ∈ Icc m (3 * m)) := by
    ext S1; simp only [mem_filter, mem_range, mem_Icc]; omega
  rw [show ∑ M ∈ E, ∑ S1 ∈ Icc m (3 * m), (muJ m S1 (M : ZMod (3 ^ m)) : ℂ) *
        (((Y * 3 ^ m / M : ℝ) : ℂ) * phase q ρ η s M S1 m * renewalR ρ η s (uMS Y M S1 m)) =
      ∑ M ∈ E, ∑ S1 ∈ range (K + 1), (if S1 ∈ Icc m (3 * m) then
        (muJ m S1 (M : ZMod (3 ^ m)) : ℂ) * (((Y * 3 ^ m / M : ℝ) : ℂ) * phase q ρ η s M S1 m *
          renewalR ρ η s (uMS Y M S1 m)) else 0) from
      Finset.sum_congr rfl fun M _ => by rw [← Finset.sum_filter, ← hIcc],
    ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  set b : ℕ → ℝ := fun S1 => Tb (Lx x) + (if typT x m S1 then 0 else 2 * B) with hb
  have hpt : ∀ M ∈ E, ∀ S1 ∈ range (K + 1),
      ‖(muJ m S1 (M : ZMod (3 ^ m)) : ℂ) * (((Y * 3 ^ m / M : ℝ) : ℂ) * phase q ρ η s M S1 m *
          ∑ t ∈ I, rinner ρ η s (uMS Y M S1 m) t) -
        (if S1 ∈ Icc m (3 * m) then (muJ m S1 (M : ZMod (3 ^ m)) : ℂ) *
          (((Y * 3 ^ m / M : ℝ) : ℂ) * phase q ρ η s M S1 m *
            renewalR ρ η s (uMS Y M S1 m)) else 0)‖ ≤
      Y * (b S1 * ((3 : ℝ) ^ m / M * muJ m S1 (M : ZMod (3 ^ m)))) := by
    intro M hM S1 _
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (hE hM).1.pos
    have hpair := pair_bound hL hL2 hY1 hY2 ρ η s B hBR hBI (hE hM) S1 I hI
    have heq : (muJ m S1 (M : ZMod (3 ^ m)) : ℂ) * (((Y * 3 ^ m / M : ℝ) : ℂ) *
          phase q ρ η s M S1 m * ∑ t ∈ I, rinner ρ η s (uMS Y M S1 m) t) -
        (if S1 ∈ Icc m (3 * m) then (muJ m S1 (M : ZMod (3 ^ m)) : ℂ) *
          (((Y * 3 ^ m / M : ℝ) : ℂ) * phase q ρ η s M S1 m *
            renewalR ρ η s (uMS Y M S1 m)) else 0) =
        ((muJ m S1 (M : ZMod (3 ^ m)) * (Y * 3 ^ m / M) : ℝ) : ℂ) * phase q ρ η s M S1 m *
          (∑ t ∈ I, rinner ρ η s (uMS Y M S1 m) t -
            (if S1 ∈ Icc m (3 * m) then renewalR ρ η s (uMS Y M S1 m) else 0)) := by
      split_ifs <;> push_cast <;> ring
    rw [heq, norm_mul, norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by have := muJ_nonneg m S1 (M : ZMod (3 ^ m)); positivity)]
    calc muJ m S1 (M : ZMod (3 ^ m)) * (Y * 3 ^ m / M) * ‖∑ t ∈ I, rinner ρ η s (uMS Y M S1 m) t -
          (if S1 ∈ Icc m (3 * m) then renewalR ρ η s (uMS Y M S1 m) else 0)‖
        ≤ muJ m S1 (M : ZMod (3 ^ m)) * (Y * 3 ^ m / M) * b S1 :=
          mul_le_mul_of_nonneg_left hpair
            (by have := muJ_nonneg m S1 (M : ZMod (3 ^ m)); positivity)
      _ = Y * (b S1 * ((3 : ℝ) ^ m / M * muJ m S1 (M : ZMod (3 ^ m)))) := by ring
  have hb0 : ∀ S1, 0 ≤ b S1 := fun S1 => by
    simp only [hb]; split_ifs <;> linarith
  calc _ ≤ ∑ M ∈ E, ∑ S1 ∈ range (K + 1), Y * (b S1 * ((3 : ℝ) ^ m / M *
        muJ m S1 (M : ZMod (3 ^ m)))) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun M hM =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun S1 hS1 => hpt M hM S1 hS1))
    _ = Y * ∑ S1 ∈ range (K + 1), b S1 * ∑ M ∈ E, (3 : ℝ) ^ m / M *
        muJ m S1 (M : ZMod (3 ^ m)) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S1 _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ Y * ∑ S1 ∈ range (K + 1), b S1 * (5 * lawS m S1) := by
        gcongr with S1 _
        exact sum_E_muJ_le hL E hE (two_m_le_n0 hL) S1
    _ = 5 * Y * (Tb (Lx x) * ∑ S1 ∈ range (K + 1), lawS m S1 + 2 * B *
        ∑ S1 ∈ range (K + 1), (if typT x m S1 then 0 else lawS m S1)) := by
        have e : ∀ S1, Y * (b S1 * (5 * lawS m S1)) = 5 * Y * (Tb (Lx x) * lawS m S1 +
            2 * B * (if typT x m S1 then 0 else lawS m S1)) := by
          intro S1; simp only [hb]; split_ifs <;> ring
        rw [Finset.mul_sum, Finset.sum_congr rfl (fun S1 _ => e S1), ← Finset.mul_sum,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 5 * Y * (Tb (Lx x) * 1 + 2 * B * chern m (Lx x ^ (0.6 : ℝ))) := by
        gcongr
        · have := (summable_lawS m).sum_le_tsum (range (K + 1)) (fun i _ => lawS_nonneg m i)
          rwa [tsum_lawS] at this
        · refine le_trans ?_ (lawS_chernoff hm1 (Real.rpow_nonneg hLL _))
          refine le_trans ?_ ((summable_ite_lawS m (fun A : ℕ =>
            Lx x ^ (0.6 : ℝ) ≤ |(A : ℝ) - 2 * m|)).sum_le_tsum (range (K + 1))
              (fun i _ => by split_ifs <;> simp [lawS_nonneg]))
          refine Finset.sum_le_sum fun S1 _ => ?_
          by_cases hT : typT x m S1
          · rw [if_pos hT]; split_ifs <;> simp [lawS_nonneg]
          · rw [if_neg hT, if_pos]
            unfold typT at hT; push Not at hT; exact hT.le
    _ = 5 * Y * (Tb (Lx x) + 2 * B * chern m (Lx x ^ (0.6 : ℝ))) := by ring

end CollatzCLT
