import LeanClt.Applications.Kernel
import LeanClt.Main.OfTao

/-!
# The pinned transfer (proof of Theorem 6.10 [`thm:anticonc`]), stage 2 of the checkpoint-20 plan

From Tao's two imports only (`TaoMajorant`, `TaoPrefix`); no Diophantine input.

* `pinned_setup`: for a set and clock with the transport property (6.2, `eq:transport`) and a
  dyadic scale `Y`, the threshold `x = Y^{1/α}` satisfies every numerical condition of §5, and
  `E[1_A(N_Y) e^{isq(N_Y)}]` is within `C/log x` of the right side of (5.14, `eq:transfer`),
  uniformly in `s`
  (`phi0_close`, Theorem 5.10 [`thm:transfer`] with `A = 1`, Lemma 5.1 [`lem:typical`]). The
  constants do not depend on `(A, q, x₀)`.
* `phi0_le_of_kernel`: the right side of (5.14) is at most `(Y/L_Y) ∑_{M,S} w_{M,S} |R_s(u)|`,
  with `Y/L_Y ≤ 4` and `∑ w ≤ 5` (`sum_wMS_le`, the harmonic bound `H ≤ 5` of
  Proposition 5.5 [`prop:harmonic`] at the coarse depth `m`), so the statement's `C₁` is `20`.
  Every argument `u` is at least `log Y/(4000α)` (`uMS_ge_linear`), so a bound on the kernel
  there bounds the phase average.
* `anticonc_odd_dyadic`: **route (b)**. For an integer clock and an integer reward every phase
  is `e^{iks}` with `k ∈ ℤ`. Taking the Fourier coefficient at `j` (`fcoef`) of `phi0` and of
  `transferRHS`, which are uniformly close (`phi0 ≈ transferLHS ≈ transferRHS`, `pinned_setup`),
  turns `phi0` into `P(N_Y ∈ A, q(N_Y) = j)`
  (`fcoef_phi0`) and `transferRHS` into `(Y/L_Y) ∑ w_{M,S} 𝒦_{K-j}(u)` (`renewalR_fourier`), v8's
  identity (6.10, `eq:pinned`); the error is at most its uniform bound. `pinnedK_le` and
  `u ≥ L/4000` then give `P ≤ C/√(log Y)`.
-/

open Real Filter Topology Finset Complex

noncomputable section

namespace CollatzCLT

/-! ## The right side of (5.14) in weighted form -/

lemma transferRHS_eq_w {x Y : ℝ} (hY0 : 0 < Y) (hLY : (0 : ℝ) < LY Y) (E : Finset ℕ)
    (q : ℕ → ℝ) (ρ η s : ℝ) :
    transferRHS x Y E q ρ η s = ((Y / LY Y : ℝ) : ℂ) *
      ∑ M ∈ E, ∑ S ∈ Icc (mT x) (3 * mT x), (wMS x M S : ℂ) * phase q ρ η s M S (mT x) *
        renewalR ρ η s (uMS Y M S (mT x)) := by
  have h := LY_mul_RHS (x := x) hY0 hLY.ne' E q ρ η s
  have hLYc : (LY Y : ℂ) ≠ 0 := by exact_mod_cast hLY.ne'
  have : transferRHS x Y E q ρ η s =
      (LY Y : ℂ)⁻¹ * ((LY Y : ℂ) * transferRHS x Y E q ρ η s) := by field_simp
  rw [this, h, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  unfold wMS
  push_cast
  field_simp

/-! ## The common setup at the threshold `x = Y^{1/α}` -/

/-- For fixed rewards `(ρ, η)`: constants `C, x₁`, independent of the set, the clock and the
transport threshold, such that for every `Y ≥ max(x₁, x₀)^α` the threshold `x = Y^{1/α}` has
`Large x`, `log x = log Y/α ≥ 1`, `‖φ⁰_Y(s) - RHS(s)‖ ≤ C/log x` for all `s`, `u ≥ log x/4000`
on the whole coarse range, `L_Y > 0` and `Y/L_Y ≤ 4`. -/
theorem pinned_setup (hTM : TaoMajorant) (hTP : TaoPrefix) (ρ η : ℝ) :
    ∃ C x₁ : ℝ, 0 ≤ C ∧ 2 ≤ x₁ ∧ ∀ (A : Set ℕ) (q : ℕ → ℝ) (x₀ : ℝ), Transport A q ρ η x₀ →
      ∀ Y : ℝ, (max x₁ x₀) ^ alpha ≤ Y → ∃ x : ℝ, Large x ∧ 1 ≤ Lx x ∧ 0 < Y ∧
        Lx x = Real.log Y / alpha ∧
        (∀ s, ‖phi0 A q Y s - transferRHS x Y (EA A x) q ρ η s‖ ≤ C / Lx x) ∧
        (∀ M ∈ EA A x, ∀ S ∈ Icc (mT x) (3 * mT x), Lx x / 4000 ≤ uMS Y M S (mT x)) ∧
        0 < (LY Y : ℝ) ∧ Y / LY Y ≤ 4 := by
  classical
  obtain ⟨CT, xT, hT⟩ := transfer_of_tao hTM hTP ρ η 1 one_pos
  have f7 := ev_of_log (ev_rpow_le_mul (a := 0.7) (ε := 1 / 2000) (by norm_num) (by norm_num))
  have hev := large_ev.and ((typical 1).and (f7.and (eventually_ge_atTop xT)))
  obtain ⟨xt, hxt⟩ := eventually_atTop.mp hev
  refine ⟨2 + |CT|, max xt 2, by positivity, le_max_right _ _, ?_⟩
  intro A q x₀ htr Y hY
  have hα : (1 : ℝ) < alpha := by unfold alpha; norm_num
  have hα0 : (0 : ℝ) < alpha := by linarith
  set mx := max (max xt 2) x₀ with hmx
  have hmx2 : 2 ≤ mx := le_trans (le_max_right _ _) (le_max_left _ _)
  have hmx0 : 0 < mx := by linarith
  have hmxY : mx ≤ Y := le_trans (Real.self_le_rpow_of_one_le (by linarith) hα.le) hY
  have hY0 : 0 < Y := by linarith
  set x := Y ^ alpha⁻¹ with hxdef
  have hx0 : 0 < x := Real.rpow_pos_of_pos hY0 _
  have hxα : x ^ alpha = Y := Real.rpow_inv_rpow hY0.le hα0.ne'
  have hmxx : mx ≤ x := by
    have h2 := Real.rpow_le_rpow (by positivity) hY (inv_nonneg.mpr hα0.le)
    rwa [← Real.rpow_mul hmx0.le, mul_inv_cancel₀ hα0.ne', Real.rpow_one] at h2
  have hxt' : xt ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hmxx
  have hx0' : x₀ ≤ x := le_trans (le_max_right _ _) hmxx
  obtain ⟨hL, htyp, h7, hxT⟩ := hxt x hxt'
  have hY1 : x ^ alpha ≤ Y := hxα.le
  have hY2 : Y ≤ x ^ (alpha ^ 2) := by
    rw [sq, Real.rpow_mul hx0.le, hxα]
    exact Real.self_le_rpow_of_one_le (by linarith) hα.le
  have hLx : Lx x = Real.log Y / alpha := by
    unfold Lx; rw [hxdef, Real.log_rpow hY0]; field_simp
  have hLb : (200000 : ℝ) ≤ Lx x := hL.L_ge
  have hL0 : 0 < Lx x := by linarith
  obtain ⟨-, h2e5, hxY, -⟩ := large_facts hL hY1
  have hLY4 : Y / 4 ≤ (LY Y : ℝ) := by have := LY_ge hY0.le; linarith
  have hLYpos : (0 : ℝ) < LY Y := lt_of_lt_of_le (by positivity) hLY4
  have hLinv : Lx x ^ (-(1 : ℝ)) = 1 / Lx x := by rw [Real.rpow_neg_one, one_div]
  refine ⟨x, hL, by linarith, hY0, hLx, fun s => ?_, fun M hM S hS => ?_, hLYpos, ?_⟩
  · have e1 := phi0_close htr hx0' hL hY1 hY2 s
    have e2 := hT x Y hxT hY1 hY2 (EA A x) (EA_sub A x) q s
    have ht := htyp Y hY1
    rw [hLinv] at ht e2
    have e1' : 2 * (((oddClosed Y).filter (fun N => ¬ Good x N)).card : ℝ) / LY Y ≤
        2 / Lx x := by
      rw [div_le_div_iff₀ hLYpos hL0]
      have := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ 2 * Lx x by positivity)
      calc 2 * (((oddClosed Y).filter (fun N => ¬ Good x N)).card : ℝ) * Lx x
          = 2 * Lx x * (((oddClosed Y).filter (fun N => ¬ Good x N)).card : ℝ) := by ring
        _ ≤ 2 * Lx x * (1 / Lx x * LY Y) := this
        _ = 2 * LY Y := by field_simp
    have e2' : CT * (1 / Lx x) ≤ |CT| / Lx x := by
      rw [mul_one_div]; gcongr; exact le_abs_self _
    calc ‖phi0 A q Y s - transferRHS x Y (EA A x) q ρ η s‖
        ≤ ‖phi0 A q Y s - transferLHS x Y (EA A x) q ρ η s‖ +
          ‖transferLHS x Y (EA A x) q ρ η s - transferRHS x Y (EA A x) q ρ η s‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 / Lx x + |CT| / Lx x := add_le_add (e1.trans e1') (e2.trans e2')
      _ = (2 + |CT|) / Lx x := by ring
  · have hS3 := (mem_Icc.mp hS).2
    exact uMS_ge_linear hL hY1 (by linarith) (EA_sub A x hM) hS3
  · rw [div_le_iff₀ hLYpos]; linarith

/-! ## A bound on the phase average from a bound on the kernel -/

/-- **The fixed-frequency transfer bound** (proof of Theorem 6.13): if the kernel `R^{ρ,η}_s(u)` is
bounded by `B` for `u ≥ c₀ log Y`, then `|E[1_A(N_Y) e^{isq(N_Y)}]| ≤ C₁B + C/log Y` for
`Y ≥ max(x₁, x₀)^α`. Here `C₁` bounds the harmonic factor `(Y/L_Y) ∑ w` of the right side of
(5.14, `eq:transfer`); it comes from the harmonic bound of
Proposition 5.5 [`prop:harmonic`], and the proof takes `C₁ = 20`. `C₁, C, x₁, c₀` do not depend
on `(A, q, x₀, s)`. -/
theorem phi0_le_of_kernel (hTM : TaoMajorant) (hTP : TaoPrefix) (ρ η : ℝ) :
    ∃ C₁ C x₁ c₀ : ℝ, 0 < c₀ ∧ ∀ (A : Set ℕ) (q : ℕ → ℝ) (x₀ : ℝ), Transport A q ρ η x₀ →
      ∀ (s Y : ℝ), (max x₁ x₀) ^ alpha ≤ Y → ∀ B : ℝ,
        (∀ u : ℝ, c₀ * Real.log Y ≤ u → ‖renewalR ρ η s u‖ ≤ B) →
        ‖phi0 A q Y s‖ ≤ C₁ * B + C / Real.log Y := by
  obtain ⟨C, x₁, hC, hx₁, hset⟩ := pinned_setup hTM hTP ρ η
  have hα0 : (0 : ℝ) < alpha := by unfold alpha; norm_num
  refine ⟨20, C * alpha, x₁, 1 / (4000 * alpha), by positivity, ?_⟩
  intro A q x₀ htr s Y hY B hB
  obtain ⟨x, hL, hL1, hY0, hLx, hclose, hu, hLYpos, hYLY⟩ := hset A q x₀ htr Y hY
  have hL0 : 0 < Lx x := by linarith
  have hlogY : Real.log Y = alpha * Lx x := by rw [hLx]; field_simp
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ le_rfl)
  have hRB : ∀ M ∈ EA A x, ∀ S ∈ Icc (mT x) (3 * mT x),
      ‖renewalR ρ η s (uMS Y M S (mT x))‖ ≤ B := by
    intro M hM S hS
    refine hB _ ((le_of_eq ?_).trans (hu M hM S hS))
    rw [hlogY]; field_simp
  have hYL0 : 0 ≤ Y / LY Y := by positivity
  have hRHS : ‖transferRHS x Y (EA A x) q ρ η s‖ ≤ 20 * B := by
    rw [transferRHS_eq_w hY0 hLYpos, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hYL0]
    have hsum : ‖∑ M ∈ EA A x, ∑ S ∈ Icc (mT x) (3 * mT x), (wMS x M S : ℂ) *
        phase q ρ η s M S (mT x) * renewalR ρ η s (uMS Y M S (mT x))‖ ≤
        ∑ M ∈ EA A x, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S * B := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun M hM =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun S hS => ?_))
      rw [norm_mul, norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (wMS_nonneg x M S)]
      exact mul_le_mul_of_nonneg_left (hRB M hM S hS) (wMS_nonneg x M S)
    have hw := sum_wMS_le hL (EA A x) (EA_sub A x)
    have hwB : ∑ M ∈ EA A x, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S * B ≤ 5 * B := by
      rw [show ∑ M ∈ EA A x, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S * B =
          (∑ M ∈ EA A x, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S) * B by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun M _ => by rw [Finset.sum_mul]]
      exact mul_le_mul_of_nonneg_right hw hB0
    calc Y / LY Y * ‖∑ M ∈ EA A x, ∑ S ∈ Icc (mT x) (3 * mT x), (wMS x M S : ℂ) *
          phase q ρ η s M S (mT x) * renewalR ρ η s (uMS Y M S (mT x))‖
        ≤ 4 * (5 * B) := mul_le_mul hYLY (hsum.trans hwB) (norm_nonneg _) (by norm_num)
      _ = 20 * B := by ring
  have hCL : C / Lx x = C * alpha / Real.log Y := by
    rw [hlogY]; field_simp
  calc ‖phi0 A q Y s‖
      ≤ ‖phi0 A q Y s - transferRHS x Y (EA A x) q ρ η s‖ +
        ‖transferRHS x Y (EA A x) q ρ η s‖ := norm_le_norm_sub_add _ _
    _ ≤ C / Lx x + 20 * B := add_le_add (hclose s) hRHS
    _ = 20 * B + C * alpha / Real.log Y := by rw [hCL]; ring

/-! ## Fourier coefficients in the frequency -/

/-- The Fourier coefficient `(2π)⁻¹ ∫₀^{2π} e^{-ijs} g(s) ds` of a function of the frequency. -/
def fcoef (j : ℤ) (g : ℝ → ℂ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ s in (0 : ℝ)..(2 * π), cexp (((((-j : ℤ) : ℝ) * s : ℝ) : ℂ) * I) * g s

lemma fcoef_sub (j : ℤ) {g g' : ℝ → ℂ} (hg : Continuous g) (hg' : Continuous g') :
    fcoef j (fun s => g s - g' s) = fcoef j g - fcoef j g' := by
  unfold fcoef
  have h1 : IntervalIntegrable (fun s => cexp (((((-j : ℤ) : ℝ) * s : ℝ) : ℂ) * I) * g s)
      MeasureTheory.volume 0 (2 * π) := ((continuous_phase _).mul hg).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun s => cexp (((((-j : ℤ) : ℝ) * s : ℝ) : ℂ) * I) * g' s)
      MeasureTheory.volume 0 (2 * π) := ((continuous_phase _).mul hg').intervalIntegrable _ _
  rw [← mul_sub, ← intervalIntegral.integral_sub h1 h2]
  congr 2; ext s; dsimp only; ring

lemma fcoef_const_mul (j : ℤ) (a : ℂ) (g : ℝ → ℂ) :
    fcoef j (fun s => a * g s) = a * fcoef j g := by
  unfold fcoef
  simp_rw [mul_left_comm _ a]
  rw [intervalIntegral.integral_const_mul]; ring

lemma fcoef_sum {ι : Type*} (j : ℤ) (I' : Finset ι) (g : ι → ℝ → ℂ)
    (hg : ∀ i, Continuous (g i)) :
    fcoef j (fun s => ∑ i ∈ I', g i s) = ∑ i ∈ I', fcoef j (g i) := by
  unfold fcoef
  have h1 : ∀ i ∈ I', IntervalIntegrable
      (fun s => cexp (((((-j : ℤ) : ℝ) * s : ℝ) : ℂ) * I) * g i s) MeasureTheory.volume 0 (2 * π) :=
    fun i _ => ((continuous_phase _).mul (hg i)).intervalIntegrable _ _
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum h1, Finset.mul_sum]

lemma two_pi_ne_zero_complex : (2 * (π : ℂ)) ≠ 0 := by
  exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)

/-- `fcoef j (e^{iks}) = 1{k = j}`. -/
lemma fcoef_cexp (j k : ℤ) :
    fcoef j (fun s => cexp ((((k : ℝ) * s : ℝ) : ℂ) * I)) = if k = j then 1 else 0 := by
  unfold fcoef
  have e : ∀ s : ℝ, cexp (((((-j : ℤ) : ℝ) * s : ℝ) : ℂ) * I) * cexp ((((k : ℝ) * s : ℝ) : ℂ) * I) =
      cexp (((((k - j : ℤ) : ℝ) * s : ℝ) : ℂ) * I) := by
    intro s; rw [← Complex.exp_add]; push_cast; ring_nf
  simp_rw [e]
  rw [integral_cexp_int]
  have := two_pi_ne_zero_complex
  by_cases hk : k = j
  · rw [ite_eq_left (sub_eq_zero.mpr hk), ite_eq_left hk]; push_cast; field_simp
  · rw [ite_eq_right (fun h => hk (sub_eq_zero.mp h)), ite_eq_right hk, mul_zero]

/-- `fcoef j (e^{iKs} R^{ρ,η}_s(u)) = 𝒦_{K-j}(u)` for integer rewards (`renewalR_fourier`). -/
lemma fcoef_renewal (ρ η : ℕ) (j K : ℤ) (u : ℝ) :
    fcoef j (fun s => cexp ((((K : ℝ) * s : ℝ) : ℂ) * I) * renewalR ρ η s u) =
      (pinnedK ρ η (K - j) u : ℂ) := by
  rw [← renewalR_fourier]
  unfold fcoef
  congr 2; ext s
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

lemma norm_fcoef_le (j : ℤ) {g : ℝ → ℂ} {B : ℝ} (hB : ∀ s, ‖g s‖ ≤ B) : ‖fcoef j g‖ ≤ B := by
  unfold fcoef
  have hπ : 0 < 2 * π := by positivity
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
    (f := fun s => cexp (((((-j : ℤ) : ℝ) * s : ℝ) : ℂ) * I) * g s) (C := B)
    (fun s _ => by rw [norm_phase_mul]; exact hB s)
  rw [sub_zero, abs_of_pos hπ] at h2
  have h1 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, h1]
  calc 1 / (2 * π) * ‖∫ s in (0 : ℝ)..(2 * π),
        cexp (((((-j : ℤ) : ℝ) * s : ℝ) : ℂ) * I) * g s‖
      ≤ 1 / (2 * π) * (B * (2 * π)) := by gcongr
    _ = B := by field_simp

lemma continuous_phi0 (A : Set ℕ) (q : ℕ → ℝ) (Y : ℝ) : Continuous (fun s => phi0 A q Y s) := by
  unfold phi0
  refine continuous_const.mul (continuous_finsetSum _ fun u _ => ?_)
  by_cases hu : u ∈ A
  · simp only [Set.indicator_of_mem hu]; fun_prop
  · simp only [Set.indicator_of_notMem hu]; exact continuous_const

open Classical in
/-- The Fourier coefficient of the phase average of an integer clock is the probability of the
level set: `fcoef j φ⁰_Y = P(N_Y ∈ A, q(N_Y) = j)`. -/
lemma fcoef_phi0 (A : Set ℕ) (q : ℕ → ℤ) (Y : ℝ) (j : ℤ) :
    fcoef j (fun s => phi0 A (fun n => (q n : ℝ)) Y s) =
      (((oddClosed Y).filter (fun n => n ∈ A ∧ q n = j)).card : ℂ) / (oddClosed Y).card := by
  have e : (fun s => phi0 A (fun n => (q n : ℝ)) Y s) = fun s =>
      ((oddClosed Y).card : ℂ)⁻¹ * ∑ u ∈ oddClosed Y,
        (if u ∈ A then cexp (((((q u : ℤ) : ℝ) * s : ℝ) : ℂ) * I) else 0) := by
    ext s; unfold phi0
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ A
    · rw [Set.indicator_of_mem hu, ite_eq_left hu, mul_comm s]
    · rw [Set.indicator_of_notMem hu, ite_eq_right hu]
  rw [e, fcoef_const_mul, fcoef_sum]
  · have hterm : ∀ u, fcoef j (fun s => if u ∈ A then cexp (((((q u : ℤ) : ℝ) * s : ℝ) : ℂ) * I)
        else 0) = if u ∈ A ∧ q u = j then 1 else 0 := by
      intro u
      by_cases hu : u ∈ A
      · simp only [hu, ite_true, true_and]; exact fcoef_cexp j (q u)
      · simp only [hu, ite_false, false_and]
        unfold fcoef; simp
    simp_rw [hterm]
    rw [Finset.sum_boole, div_eq_inv_mul]
  · intro u
    by_cases hu : u ∈ A
    · simp only [hu, ite_true]; fun_prop
    · simp only [hu, ite_false]; exact continuous_const

/-! ## The pinned transfer -/

open Classical in
/-- One reward at a time. -/
theorem anticonc_odd_dyadic_one (hTM : TaoMajorant) (hTP : TaoPrefix) (ρ η : ℕ)
    (hρη : (ρ = 1 ∧ η = 0) ∨ (ρ = 1 ∧ η = 1) ∨ (ρ = 0 ∧ η = 1)) :
    ∃ C x₁ : ℝ, 0 ≤ C ∧ 2 ≤ x₁ ∧
      ∀ (A : Set ℕ) (q : ℕ → ℤ) (x₀ : ℝ), Transport A (fun n => (q n : ℝ)) ρ η x₀ →
        ∀ Y : ℝ, (max x₁ x₀) ^ alpha ≤ Y → ∀ j : ℤ,
          (((oddClosed Y).filter (fun n => n ∈ A ∧ q n = j)).card : ℝ) ≤
            C * (oddClosed Y).card / √(Real.log Y) := by
  classical
  obtain ⟨C, x₁, hC, hx₁, hset⟩ := pinned_setup hTM hTP ρ η
  obtain ⟨CK, hCK⟩ := pinnedK_le
  have hCK0 : 0 ≤ CK := by
    have := (pinnedK_nonneg ρ η 0 1).trans (hCK ρ η hρη 0 1 one_pos)
    simpa using this
  refine ⟨2 * (1280 * CK + C), x₁, by positivity, hx₁, ?_⟩
  intro A q x₀ htr Y hY j
  obtain ⟨x, hL, hL1, hY0, hLx, hclose, hu, hLYpos, hYLY⟩ := hset A _ x₀ htr Y hY
  set L := Lx x with hLdef
  have hL0 : 0 < L := by linarith
  have hα : (1 : ℝ) < alpha := by unfold alpha; norm_num
  have hα4 : alpha ≤ 4 := by unfold alpha; norm_num
  have hlogY : Real.log Y = alpha * L := by rw [hLx]; field_simp
  have hlogY0 : 0 < Real.log Y := by rw [hlogY]; positivity
  set E := EA A x with hE
  set m := mT x with hm
  set P : ℝ := (((oddClosed Y).filter (fun n => n ∈ A ∧ q n = j)).card : ℝ) / LY Y with hP
  -- the integer phases of the right side
  set K : ℕ → ℕ → ℤ := fun M S => q M - (ρ : ℤ) * S - (η : ℤ) * m with hK
  have hphase : ∀ s M S, phase (fun n => (q n : ℝ)) ρ η s M S m =
      cexp ((((K M S : ℝ) * s : ℝ) : ℂ) * I) := by
    intro s M S; unfold phase; congr 2; simp only [hK]; push_cast; ring
  set Rv : ℝ := Y / LY Y * ∑ M ∈ E, ∑ S ∈ Icc m (3 * m),
    wMS x M S * pinnedK ρ η (K M S - j) (uMS Y M S m) with hRv
  -- the Fourier coefficients
  have hcont_inner : ∀ M, Continuous (fun s => ∑ S ∈ Icc m (3 * m), (wMS x M S : ℂ) *
      (cexp ((((K M S : ℝ) * s : ℝ) : ℂ) * I) * renewalR ρ η s (uMS Y M S m))) := fun M =>
    continuous_finsetSum _ fun S _ =>
      continuous_const.mul ((continuous_phase _).mul (continuous_renewalR _ _ _))
  have hRHSfun : (fun s => transferRHS x Y E (fun n => (q n : ℝ)) ρ η s) = fun s =>
      ((Y / LY Y : ℝ) : ℂ) * ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), (wMS x M S : ℂ) *
        (cexp ((((K M S : ℝ) * s : ℝ) : ℂ) * I) * renewalR ρ η s (uMS Y M S m)) := by
    ext s
    rw [transferRHS_eq_w hY0 hLYpos]
    congr 1
    refine Finset.sum_congr rfl fun M _ => Finset.sum_congr rfl fun S _ => ?_
    rw [hphase, mul_assoc]
  have hcontR : Continuous (fun s => transferRHS x Y E (fun n => (q n : ℝ)) ρ η s) := by
    rw [hRHSfun]
    exact continuous_const.mul (continuous_finsetSum _ fun M _ => hcont_inner M)
  have hinner : ∀ M, fcoef j (fun s => ∑ S ∈ Icc m (3 * m), (wMS x M S : ℂ) *
      (cexp ((((K M S : ℝ) * s : ℝ) : ℂ) * I) * renewalR ρ η s (uMS Y M S m))) =
      ∑ S ∈ Icc m (3 * m), (wMS x M S : ℂ) * (pinnedK ρ η (K M S - j) (uMS Y M S m) : ℂ) := by
    intro M
    refine (fcoef_sum j (Icc m (3 * m)) (fun S s => (wMS x M S : ℂ) *
      (cexp ((((K M S : ℝ) * s : ℝ) : ℂ) * I) * renewalR ρ η s (uMS Y M S m)))
      (fun S => continuous_const.mul ((continuous_phase _).mul (continuous_renewalR _ _ _)))).trans
      (Finset.sum_congr rfl fun S _ => ?_)
    rw [fcoef_const_mul, fcoef_renewal]
  have hfR : fcoef j (fun s => transferRHS x Y E (fun n => (q n : ℝ)) ρ η s) = (Rv : ℂ) := by
    rw [hRHSfun, fcoef_const_mul, fcoef_sum _ _ _ hcont_inner,
      Finset.sum_congr rfl fun M _ => hinner M, hRv]
    push_cast
    rfl
  have hfP : fcoef j (fun s => phi0 A (fun n => (q n : ℝ)) Y s) = (P : ℂ) := by
    rw [fcoef_phi0, hP]; push_cast; rfl
  -- `P ≤ R + ε`
  have hdiff : ‖((P - Rv : ℝ) : ℂ)‖ ≤ C / L := by
    have := norm_fcoef_le j (g := fun s => phi0 A (fun n => (q n : ℝ)) Y s -
      transferRHS x Y E (fun n => (q n : ℝ)) ρ η s) (fun s => hclose s)
    rw [fcoef_sub j (continuous_phi0 _ _ _) hcontR, hfP, hfR] at this
    push_cast; exact this
  rw [Complex.norm_real, Real.norm_eq_abs] at hdiff
  have hPR : P ≤ Rv + C / L := by linarith [le_abs_self (P - Rv)]
  -- the kernel bound on the whole coarse range
  have hsqL : 0 < √L := Real.sqrt_pos.mpr hL0
  have hkern : ∀ M ∈ E, ∀ S ∈ Icc m (3 * m),
      pinnedK ρ η (K M S - j) (uMS Y M S m) ≤ 64 * CK / √L := by
    intro M hM S hS
    have hu4 := hu M hM S hS
    have hupos : 0 < uMS Y M S m := lt_of_lt_of_le (by positivity) hu4
    refine (hCK ρ η hρη _ _ hupos).trans ?_
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hupos) hsqL]
    have : √L ≤ 64 * √(uMS Y M S m) := by
      rw [show (64 : ℝ) = √(64 ^ 2) by rw [Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul
        (by norm_num)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    nlinarith
  have hRv : Rv ≤ 4 * (5 * (64 * CK / √L)) := by
    have hw := sum_wMS_le hL E (EA_sub A x)
    have hsum : ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), wMS x M S * pinnedK ρ η (K M S - j) (uMS Y M S m) ≤
        5 * (64 * CK / √L) := by
      calc _ ≤ ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), wMS x M S * (64 * CK / √L) :=
            Finset.sum_le_sum fun M hM => Finset.sum_le_sum fun S hS =>
              mul_le_mul_of_nonneg_left (hkern M hM S hS) (wMS_nonneg x M S)
        _ = (∑ M ∈ E, ∑ S ∈ Icc m (3 * m), wMS x M S) * (64 * CK / √L) := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun M _ => by rw [Finset.sum_mul]
        _ ≤ 5 * (64 * CK / √L) := mul_le_mul_of_nonneg_right hw (by positivity)
    have hsum0 : 0 ≤ ∑ M ∈ E, ∑ S ∈ Icc m (3 * m),
        wMS x M S * pinnedK ρ η (K M S - j) (uMS Y M S m) :=
      Finset.sum_nonneg fun M _ => Finset.sum_nonneg fun S _ =>
        mul_nonneg (wMS_nonneg x M S) (pinnedK_nonneg _ _ _ _)
    rw [hRv]
    exact mul_le_mul hYLY hsum (by positivity) (by norm_num)
  -- `C/L ≤ C/√L` and `√(log Y) ≤ 2√L`
  have hLsq : √L ≤ L := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hCL : C / L ≤ C / √L := div_le_div_of_nonneg_left hC hsqL hLsq
  have hPbd : P ≤ (1280 * CK + C) / √L := by
    have : Rv + C / L ≤ (1280 * CK + C) / √L := by
      have h := add_le_add hRv hCL
      calc Rv + C / L ≤ 4 * (5 * (64 * CK / √L)) + C / √L := h
        _ = (1280 * CK + C) / √L := by ring
    linarith
  have hsqY : √(Real.log Y) ≤ 2 * √L := by
    rw [hlogY, show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsqY0 : 0 < √(Real.log Y) := Real.sqrt_pos.mpr hlogY0
  -- conclude
  have hcard : (((oddClosed Y).filter (fun n => n ∈ A ∧ q n = j)).card : ℝ) = P * LY Y := by
    rw [hP, div_mul_cancel₀ _ hLYpos.ne']
  rw [hcard, show ((oddClosed Y).card : ℝ) = LY Y from rfl]
  have hK0 : 0 ≤ 1280 * CK + C := by positivity
  calc P * LY Y ≤ (1280 * CK + C) / √L * LY Y := mul_le_mul_of_nonneg_right hPbd hLYpos.le
    _ ≤ 2 * (1280 * CK + C) * LY Y / √(Real.log Y) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hsqL hsqY0]
        have := mul_le_mul_of_nonneg_left hsqY (show 0 ≤ (1280 * CK + C) * LY Y by positivity)
        nlinarith

open Classical in
/-- **Odd dyadic anti-concentration for a transported integer clock.** For the three clock rewards
and every `(A, q, x₀)` with the transport property, `P(N_Y ∈ A, q(N_Y) = j) ≤ C/√(log Y)`
uniformly in `j`, for `Y ≥ max(x₁, x₀)^α`. `C, x₁` do not depend on `(A, q, x₀)`; no Diophantine
input. -/
theorem anticonc_odd_dyadic (hTM : TaoMajorant) (hTP : TaoPrefix) :
    ∃ C x₁ : ℝ, ∀ ρ η : ℕ, (ρ = 1 ∧ η = 0) ∨ (ρ = 1 ∧ η = 1) ∨ (ρ = 0 ∧ η = 1) →
      ∀ (A : Set ℕ) (q : ℕ → ℤ) (x₀ : ℝ), Transport A (fun n => (q n : ℝ)) ρ η x₀ →
        ∀ Y : ℝ, (max x₁ x₀) ^ alpha ≤ Y → ∀ j : ℤ,
          (((oddClosed Y).filter (fun n => n ∈ A ∧ q n = j)).card : ℝ) ≤
            C * (oddClosed Y).card / √(Real.log Y) := by
  obtain ⟨C1, a1, hC1, ha1, h1⟩ := anticonc_odd_dyadic_one hTM hTP 1 0 (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨C2, a2, hC2, ha2, h2⟩ :=
    anticonc_odd_dyadic_one hTM hTP 1 1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  obtain ⟨C3, a3, hC3, ha3, h3⟩ :=
    anticonc_odd_dyadic_one hTM hTP 0 1 (Or.inr (Or.inr ⟨rfl, rfl⟩))
  refine ⟨max (max C1 C2) C3, max (max a1 a2) a3, ?_⟩
  have hα0 : (0 : ℝ) ≤ alpha := by unfold alpha; norm_num
  have mono : ∀ a x₀ : ℝ, 0 ≤ a → a ≤ max (max a1 a2) a3 → ∀ Y : ℝ,
      (max (max (max a1 a2) a3) x₀) ^ alpha ≤ Y → (max a x₀) ^ alpha ≤ Y := by
    intro a x₀ ha0 ha Y hY
    refine le_trans (Real.rpow_le_rpow (le_trans ha0 (le_max_left _ _))
      (max_le_max ha le_rfl) hα0) hY
  have fin : ∀ (Ci : ℝ) (Y : ℝ) (n : ℕ) (k : ℝ), Ci ≤ max (max C1 C2) C3 →
      (k ≤ Ci * n / √(Real.log Y)) → k ≤ max (max C1 C2) C3 * n / √(Real.log Y) := by
    intro Ci Y n k hCi hk
    refine hk.trans ?_
    gcongr
  rintro ρ η (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) A q x₀ htr Y hY j
  · exact fin C1 Y _ _ ((le_max_left _ _).trans (le_max_left _ _))
      (h1 A q x₀ htr Y (mono a1 x₀ (by linarith) ((le_max_left _ _).trans (le_max_left _ _))
        Y hY) j)
  · exact fin C2 Y _ _ ((le_max_right _ _).trans (le_max_left _ _))
      (h2 A q x₀ htr Y (mono a2 x₀ (by linarith) ((le_max_right _ _).trans (le_max_left _ _))
        Y hY) j)
  · exact fin C3 Y _ _ (le_max_right _ _)
      (h3 A q x₀ htr Y (mono a3 x₀ (by linarith) (le_max_right _ _) Y hY) j)

end CollatzCLT
