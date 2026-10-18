import LeanClt.Applications.PinnedTransfer
import LeanClt.Sampling.Interval
import LeanClt.Elementary.Flow

/-!
# Proposition 6.12 [`prop:harmonicfirsthit`] (first-hit harmonic sums), stage 5′ of the checkpoint-20 plan

From Tao's two imports only (`TaoMajorant`, `TaoPrefix`); no Diophantine input.

**The first bound** replaces v8's integral of the pinned identity (6.10, `eq:pinned`) against
`dY/Y` by a sum over the grid of scales `Y_k = x^α (√2)^k`, `0 ≤ k ≤ K = O(log x)`, at a FIXED
threshold `x > b`; no measure theory is needed.

* `transport_F_of_lt`: the transport property (6.2, `eq:transport`) of `P_F(b)` holds at every real
  threshold above `b` (`transport_F b` is the threshold `b + 1`).
* `pinned_setup_fixed`: `pinned_setup` with `x` fixed and `Y ∈ [x^α, x^{α²}]` free.
* `pinned_le_of_close`: the Fourier coefficient at `j` of `φ⁰_Y - RHS` (as in
  `anticonc_odd_dyadic_one`) bounds `P(N_Y ∈ A, q(N_Y) = j)` by
  `(Y/L_Y) ∑ w_{M,S} 𝒦_{K-j}(u_{M,S}) + B`; here `w`, `K` and the index set do not depend on `Y`.
* `sum_grid_pinnedK_le`: along `u₀ + kℓ/2`, for the shortcut reward, each term of `𝒦_h` is supported
  on one closed `u`-interval of length `ℓ`, which holds at most three grid points, so
  `∑_k 𝒦_h(u₀ + kℓ/2) ≤ 6 ∑_t P(S_t = h) ≤ 6` (`sum_lawS_diag`: `∑_t P(S_t = h)` is `1` for
  `h = 0` and `1/2` for `h ≥ 1`).
* `harmonic_grid`: every odd `n ∈ [2x^α, x^{α²}]` lies in `[Y_k, 2Y_k]` for some grid point with
  `L_{Y_k} ≤ n`, so `∑ 1/n ≤ ∑_k P_{Y_k} ≤ 4·5·6 + (K+1) C/log x ≤ 120 + C`.

**The second bound** (`harmonic_second`): `τ_{F,b}(n) = m` forces `n ≤ b 2^m` (`le_of_hit_F`). The
odd sources are covered by the small `n` and the ranges `[2x_i^α, x_i^{α²}]`,
`log x_i = t₀ β^i`, `β = (1+α)/2`, of which `O_b(log(m+2))` reach `b 2^m` (`harmonic_odd`). The even
sources satisfy `τ(2k) = τ(k) + 1` (`hit_F_two_mul`) unless `2k = b`, so the sum `G(m)` over all
sources obeys `G(m) ≤ G(m-1)/2 + (odd part)` and `G(0) ≤ 1/b`: this is v8's decomposition
`n = 2^e q` with weights `2^{-e}` and the single exceptional source `2^m b`, unrolled one halving at
a time.
-/

open Real Filter Topology Finset Complex

noncomputable section

namespace CollatzCLT

/-! ## The transport property of `P_F(b)` at any threshold above `b` -/

/-- `transport_F` at any real threshold `x₀ > b` (v8's hypothesis `x > b` in Proposition 6.12);
`transport_F b` is the threshold `b + 1`. -/
theorem transport_F_of_lt (b : ℕ) {x₀ : ℝ} (hb : (b : ℝ) < x₀) :
    Transport (Pred F b) (fun n => -(hit F b n : ℝ)) 1 0 x₀ := by
  intro x hx hm1 N hN _ hmT _
  set r := passT x N - mT x
  obtain ⟨hFb, hFst⟩ := F_blocks hN r
  have hab := early_above hm1 hmT
  have hav : ∀ j ≤ wsum (vword N) r, F^[j] N ≠ b := by
    intro j hj hjb
    obtain ⟨i, hi, hle⟩ := hFst j hj
    have h1 := hab i hi
    have h2 : (U^[i] N : ℝ) ≤ b := by rw [← hjb]; exact_mod_cast hle
    linarith
  obtain ⟨hiff, hhit⟩ := pred_shift hFb hav hN.pos (odd_U_iterate hN r).pos
  refine ⟨hiff, fun hNA => ?_⟩
  simp only [hhit hNA]; push_cast; ring

/-! ## The setup at a fixed threshold -/

/-- `pinned_setup` with the threshold `x` fixed and the scale `Y` free in `[x^α, x^{α²}]`. For fixed
rewards: constants `C, x₁`, independent of the set, the clock and the transport threshold `x₀`,
such that every `x ≥ max(x₁, x₀)` has `Large x` and `log x ≥ 1`, and every `Y ∈ [x^α, x^{α²}]`
has `‖φ⁰_Y(s) - RHS(s)‖ ≤ C/log x` for all `s`, `L_Y > 0` and `Y/L_Y ≤ 4`. -/
theorem pinned_setup_fixed (hTM : TaoMajorant) (hTP : TaoPrefix) (ρ η : ℝ) :
    ∃ C x₁ : ℝ, 0 ≤ C ∧ ∀ (A : Set ℕ) (q : ℕ → ℝ) (x₀ x : ℝ), Transport A q ρ η x₀ →
      x₀ ≤ x → x₁ ≤ x → Large x ∧ 1 ≤ Lx x ∧ ∀ Y : ℝ, x ^ alpha ≤ Y → Y ≤ x ^ (alpha ^ 2) →
        0 < Y ∧ (∀ s, ‖phi0 A q Y s - transferRHS x Y (EA A x) q ρ η s‖ ≤ C / Lx x) ∧
        0 < (LY Y : ℝ) ∧ Y / LY Y ≤ 4 := by
  classical
  obtain ⟨CT, xT, hT⟩ := transfer_of_tao hTM hTP ρ η 1 one_pos
  have hev := large_ev.and ((typical 1).and (eventually_ge_atTop xT))
  obtain ⟨xt, hxt⟩ := eventually_atTop.mp hev
  refine ⟨2 + |CT|, xt, by positivity, ?_⟩
  intro A q x₀ x htr hx0 hx1
  obtain ⟨hL, htyp, hxT⟩ := hxt x hx1
  have hLb : (200000 : ℝ) ≤ Lx x := hL.L_ge
  have hL0 : 0 < Lx x := by linarith
  refine ⟨hL, by linarith, fun Y hY1 hY2 => ?_⟩
  obtain ⟨-, h2e5, hxY, hY0⟩ := large_facts hL hY1
  have hLY4 : Y / 4 ≤ (LY Y : ℝ) := by have := LY_ge hY0.le; linarith
  have hLYpos : (0 : ℝ) < LY Y := lt_of_lt_of_le (by positivity) hLY4
  have hLinv : Lx x ^ (-(1 : ℝ)) = 1 / Lx x := by rw [Real.rpow_neg_one, one_div]
  refine ⟨hY0, fun s => ?_, hLYpos, ?_⟩
  · have e1 := phi0_close htr hx0 hL hY1 hY2 s
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
  · rw [div_le_iff₀ hLYpos]; linarith

/-! ## The pinned identity at one scale, as an inequality -/

/-- The index `K_{M,S} - j = q(M) - ρS - ηm - j` of the pinned kernel in (6.10, `eq:pinned`), for
an integer clock `q`, an integer reward `(ρ, η)` and the level `j`. It does not depend on `Y`. -/
def pinIdx (q : ℕ → ℤ) (ρ η : ℕ) (x : ℝ) (j : ℤ) (M S : ℕ) : ℤ :=
  q M - (ρ : ℤ) * S - (η : ℤ) * mT x - j

open Classical in
/-- **The pinned identity (6.10, `eq:pinned`) at one scale, as an inequality.** If `φ⁰_Y` is within
`B` of the right side of (5.14, `eq:transfer`) uniformly in `s`, then for an integer clock and an
integer reward `P(N_Y ∈ A, q(N_Y) = j) ≤ (Y/L_Y) ∑_{M,S} w_{M,S} 𝒦_{K-j}(u_{M,S}) + B`: the Fourier
coefficient at `j` (`fcoef`) of the difference, as in `anticonc_odd_dyadic_one`. -/
lemma pinned_le_of_close {A : Set ℕ} {q : ℕ → ℤ} {ρ η : ℕ} {x Y B : ℝ} {E : Finset ℕ}
    (hY0 : 0 < Y) (hLYpos : (0 : ℝ) < LY Y)
    (hclose : ∀ s, ‖phi0 A (fun n => (q n : ℝ)) Y s -
      transferRHS x Y E (fun n => (q n : ℝ)) ρ η s‖ ≤ B) (j : ℤ) :
    (((oddClosed Y).filter (fun n => n ∈ A ∧ q n = j)).card : ℝ) / LY Y ≤
      Y / LY Y * ∑ M ∈ E, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S *
        pinnedK ρ η (pinIdx q ρ η x j M S) (uMS Y M S (mT x)) + B := by
  have hphase : ∀ s M S, phase (fun n => (q n : ℝ)) ρ η s M S (mT x) =
      cexp (((((q M - (ρ : ℤ) * S - (η : ℤ) * mT x : ℤ) : ℝ) * s : ℝ) : ℂ) * I) := by
    intro s M S; unfold phase; congr 2; push_cast; ring
  have hcont_inner : ∀ M, Continuous (fun s => ∑ S ∈ Icc (mT x) (3 * mT x), (wMS x M S : ℂ) *
      (cexp (((((q M - (ρ : ℤ) * S - (η : ℤ) * mT x : ℤ) : ℝ) * s : ℝ) : ℂ) * I) *
        renewalR ρ η s (uMS Y M S (mT x)))) := fun M =>
    continuous_finsetSum _ fun S _ =>
      continuous_const.mul ((continuous_phase _).mul (continuous_renewalR _ _ _))
  have hRHSfun : (fun s => transferRHS x Y E (fun n => (q n : ℝ)) ρ η s) = fun s =>
      ((Y / LY Y : ℝ) : ℂ) * ∑ M ∈ E, ∑ S ∈ Icc (mT x) (3 * mT x), (wMS x M S : ℂ) *
        (cexp (((((q M - (ρ : ℤ) * S - (η : ℤ) * mT x : ℤ) : ℝ) * s : ℝ) : ℂ) * I) *
          renewalR ρ η s (uMS Y M S (mT x))) := by
    ext s
    rw [transferRHS_eq_w hY0 hLYpos]
    congr 1
    refine Finset.sum_congr rfl fun M _ => Finset.sum_congr rfl fun S _ => ?_
    rw [hphase, mul_assoc]
  have hcontR : Continuous (fun s => transferRHS x Y E (fun n => (q n : ℝ)) ρ η s) := by
    rw [hRHSfun]
    exact continuous_const.mul (continuous_finsetSum _ fun M _ => hcont_inner M)
  have hinner : ∀ M, fcoef j (fun s => ∑ S ∈ Icc (mT x) (3 * mT x), (wMS x M S : ℂ) *
      (cexp (((((q M - (ρ : ℤ) * S - (η : ℤ) * mT x : ℤ) : ℝ) * s : ℝ) : ℂ) * I) *
        renewalR ρ η s (uMS Y M S (mT x)))) =
      ∑ S ∈ Icc (mT x) (3 * mT x), (wMS x M S : ℂ) *
        (pinnedK ρ η (pinIdx q ρ η x j M S) (uMS Y M S (mT x)) : ℂ) := by
    intro M
    refine (fcoef_sum j (Icc (mT x) (3 * mT x)) (fun S s => (wMS x M S : ℂ) *
      (cexp (((((q M - (ρ : ℤ) * S - (η : ℤ) * mT x : ℤ) : ℝ) * s : ℝ) : ℂ) * I) *
        renewalR ρ η s (uMS Y M S (mT x))))
      (fun S => continuous_const.mul ((continuous_phase _).mul (continuous_renewalR _ _ _)))).trans
      (Finset.sum_congr rfl fun S _ => ?_)
    rw [fcoef_const_mul, fcoef_renewal]
    rfl
  set Rv : ℝ := Y / LY Y * ∑ M ∈ E, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S *
    pinnedK ρ η (pinIdx q ρ η x j M S) (uMS Y M S (mT x)) with hRv
  have hfR : fcoef j (fun s => transferRHS x Y E (fun n => (q n : ℝ)) ρ η s) = (Rv : ℂ) := by
    rw [hRHSfun, fcoef_const_mul, fcoef_sum _ _ _ hcont_inner,
      Finset.sum_congr rfl fun M _ => hinner M, hRv]
    push_cast
    rfl
  set P : ℝ := (((oddClosed Y).filter (fun n => n ∈ A ∧ q n = j)).card : ℝ) / LY Y with hP
  have hfP : fcoef j (fun s => phi0 A (fun n => (q n : ℝ)) Y s) = (P : ℂ) := by
    rw [fcoef_phi0, hP]; push_cast; rfl
  have hdiff : ‖((P - Rv : ℝ) : ℂ)‖ ≤ B := by
    have := norm_fcoef_le j (g := fun s => phi0 A (fun n => (q n : ℝ)) Y s -
      transferRHS x Y E (fun n => (q n : ℝ)) ρ η s) (fun s => hclose s)
    rw [fcoef_sub j (continuous_phi0 _ _ _) hcontR, hfP, hfR] at this
    push_cast; exact this
  rw [Complex.norm_real, Real.norm_eq_abs] at hdiff
  linarith [le_abs_self (P - Rv)]

/-! ## The pinned kernel along a grid of arguments -/

/-- For the shortcut reward and `h < 0` every term of `𝒦_h` vanishes. -/
lemma pinnedK_10_neg {h : ℤ} (hh : h < 0) (u : ℝ) : pinnedK 1 0 h u = 0 := by
  have hz : ∀ t A, pterm 1 0 h u t A = 0 := fun t A => by
    by_contra hne
    have p := (pterm_ne_zero hne).2.2
    simp only [one_mul, zero_mul, add_zero] at p
    omega
  rw [pinnedK_eq]; simp [hz]

/-- For the shortcut reward and `h = n ≥ 0` the pinning is `A = n`, and only `t ≤ n` contribute,
since `P(S_t = n) = 0` for `t > n`. -/
lemma pinnedK_10_eq (n : ℕ) (u : ℝ) :
    pinnedK 1 0 n u = ∑ t ∈ range (n + 1), pterm 1 0 n u t n := by
  have hA : ∀ t A, A ≠ n → pterm 1 0 (n : ℤ) u t A = 0 := fun t A hA => by
    by_contra hne
    have p := (pterm_ne_zero hne).2.2
    simp only [one_mul, zero_mul, add_zero, Nat.cast_inj] at p
    exact hA p
  have ht : ∀ t, n < t → pterm 1 0 (n : ℤ) u t n = 0 := fun t ht => by
    unfold pterm; rw [lawS_eq_zero_of_lt ht]; simp
  rw [pinnedK_eq]
  rw [show (fun t => ∑' A, pterm 1 0 (n : ℤ) u t A) = fun t => pterm 1 0 n u t n from
    funext fun t => tsum_eq_single n (fun A h => hA t A h)]
  exact tsum_eq_sum fun t htn => ht t (by simp only [mem_range, not_lt] at htn; omega)

/-- `∑_t P(S_t = n)` is `1` for `n = 0` and `1/2` for `n ≥ 1` (v8's `∫ 𝒦_h = 1/2`); the terms
`t > n` vanish. -/
lemma sum_lawS_diag (n : ℕ) :
    ∑ t ∈ range (n + 1), lawS t n = if n = 0 then 1 else 1 / 2 := by
  rcases n with _ | k
  · simp
  · rw [Finset.sum_range_succ', lawS_zero_succ, add_zero, ite_eq_right (Nat.succ_ne_zero k)]
    simp_rw [lawS_succ_succ_eq k]
    rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num

lemma sum_lawS_diag_le (n : ℕ) : ∑ t ∈ range (n + 1), lawS t n ≤ 1 := by
  rw [sum_lawS_diag]; split_ifs <;> norm_num

/-- Along the grid `u₀ + kℓ/2` one term `(t, A)` of `𝒦_h` is nonzero at most at three grid points
(its window `0 ≤ Z_t - u ≤ ℓ` has length `ℓ`), each time at most `2 P(S_t = A)`. -/
lemma sum_grid_pterm_le (ρ η : ℕ) (h : ℤ) (u₀ : ℝ) (K t A : ℕ) :
    ∑ k ∈ range (K + 1), pterm ρ η h (u₀ + k * (ell / 2)) t A ≤ 6 * lawS t A := by
  classical
  have hsum : ∑ k ∈ range (K + 1), pterm ρ η h (u₀ + k * (ell / 2)) t A =
      ∑ k ∈ (range (K + 1)).filter (fun k : ℕ => pterm ρ η h (u₀ + k * (ell / 2)) t A ≠ 0),
        pterm ρ η h (u₀ + k * (ell / 2)) t A := (Finset.sum_filter_ne_zero _).symm
  set G := (range (K + 1)).filter (fun k : ℕ => pterm ρ η h (u₀ + k * (ell / 2)) t A ≠ 0)
    with hG
  have hl := ell_pos
  have hcard : G.card ≤ 3 := by
    rcases G.eq_empty_or_nonempty with hE | hne
    · rw [hE]; simp
    · have hk₀ : G.min' hne ∈ G := G.min'_mem hne
      have hsub : G ⊆ Icc (G.min' hne) (G.min' hne + 2) := by
        intro k hk
        have hle : G.min' hne ≤ k := G.min'_le k hk
        have w := pterm_ne_zero (mem_filter.mp hk).2
        have w₀ := pterm_ne_zero (mem_filter.mp hk₀).2
        rw [mem_Icc]
        refine ⟨hle, ?_⟩
        have h1 : ((k : ℝ) - (G.min' hne : ℕ)) * (ell / 2) ≤ ell := by nlinarith [w.1, w₀.2.1]
        have h2 : (k : ℝ) - (G.min' hne : ℕ) ≤ 2 := by nlinarith
        have h3 : (k : ℝ) ≤ (G.min' hne : ℕ) + 2 := by linarith
        exact_mod_cast h3
      calc G.card ≤ (Icc (G.min' hne) (G.min' hne + 2)).card := card_le_card hsub
        _ = 3 := by rw [Nat.card_Icc]; omega
  rw [hsum]
  calc ∑ k ∈ G, pterm ρ η h (u₀ + k * (ell / 2)) t A
      ≤ ∑ k ∈ G, 2 * lawS t A := Finset.sum_le_sum fun k _ => pterm_le _ _ _ _ _ _
    _ = G.card * (2 * lawS t A) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * (2 * lawS t A) := by
        have := lawS_nonneg t A
        gcongr
        exact_mod_cast hcard
    _ = 6 * lawS t A := by ring

/-- **The pinned kernel on the grid:** `∑_{k ≤ K} 𝒦_h(u₀ + kℓ/2) ≤ 6` for the shortcut reward,
uniformly in `h`, `u₀` and `K` (the grid form of v8's `∫ 𝒦_h ≤ 1`). -/
lemma sum_grid_pinnedK_le (h : ℤ) (u₀ : ℝ) (K : ℕ) :
    ∑ k ∈ range (K + 1), pinnedK 1 0 h (u₀ + k * (ell / 2)) ≤ 6 := by
  rcases lt_or_ge h 0 with hneg | hpos
  · simp [pinnedK_10_neg hneg]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    simp_rw [pinnedK_10_eq]
    rw [Finset.sum_comm]
    calc ∑ t ∈ range (n + 1), ∑ k ∈ range (K + 1), pterm 1 0 n (u₀ + k * (ell / 2)) t n
        ≤ ∑ t ∈ range (n + 1), 6 * lawS t n :=
          Finset.sum_le_sum fun t _ => sum_grid_pterm_le 1 0 n u₀ K t n
      _ = 6 * ∑ t ∈ range (n + 1), lawS t n := by rw [Finset.mul_sum]
      _ ≤ 6 * 1 := by gcongr; exact sum_lawS_diag_le n
      _ = 6 := by ring

/-! ## v8's continuous form: `∫ 𝒦_h = 1/2` (not used by the grid route) -/

/-- One term of `𝒦_n(u)` for the shortcut reward is `P(S_t = n) e^{Z_t - u}` on the closed
interval `Z_t - ℓ ≤ u ≤ Z_t`. -/
lemma pterm_10_eq_indicator (n t : ℕ) (u : ℝ) :
    pterm 1 0 n u t n = (Set.Icc (Zval t n - ell) (Zval t n)).indicator
      (fun u => lawS t n * Real.exp (Zval t n - u)) u := by
  unfold pterm
  rw [Set.indicator_apply]
  have hiff : (0 ≤ Zval t n - u ∧ Zval t n - u ≤ ell ∧ ((1 * n + 0 * t : ℕ) : ℤ) = (n : ℤ)) ↔
      u ∈ Set.Icc (Zval t n - ell) (Zval t n) := by
    rw [Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, -⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith, by simp⟩
  simp only [hiff]

lemma integrable_pterm_10 (n t : ℕ) :
    MeasureTheory.Integrable (fun u : ℝ => pterm 1 0 n u t n) := by
  simp_rw [pterm_10_eq_indicator]
  exact (Continuous.integrableOn_Icc (by fun_prop)).integrable_indicator measurableSet_Icc

/-- `∫ P(S_t = n) e^{Z_t - u} 1{Z_t - ℓ ≤ u ≤ Z_t} du = P(S_t = n) (e^ℓ - 1) = P(S_t = n)`. -/
lemma integral_pterm_10 (n t : ℕ) : ∫ u : ℝ, pterm 1 0 n u t n = lawS t n := by
  simp_rw [pterm_10_eq_indicator]
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [ell_pos] : Zval t n - ell ≤ Zval t n),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun v => Real.exp v) (Zval t n)]
  simp only [sub_sub_cancel, sub_self]
  rw [integral_exp, Real.exp_zero, exp_ell]
  ring

/-- `∫_ℝ 𝒦_h(u) du = ∑_t P(S_t = h) = 1/2` for `h ≥ 1` (and `≤ 1` for all `h`), for the shortcut
reward (proof of Proposition 6.12). -/
theorem integral_pinnedK (h : ℤ) :
    (1 ≤ h → ∫ u : ℝ, pinnedK 1 0 h u = 1 / 2) ∧ ∫ u : ℝ, pinnedK 1 0 h u ≤ 1 := by
  have key : ∀ n : ℕ, ∫ u : ℝ, pinnedK 1 0 n u = ∑ t ∈ range (n + 1), lawS t n := by
    intro n
    simp_rw [pinnedK_10_eq]
    rw [MeasureTheory.integral_finsetSum _ (fun t _ => integrable_pterm_10 n t)]
    exact Finset.sum_congr rfl fun t _ => integral_pterm_10 n t
  rcases lt_or_ge h 0 with hneg | hpos
  · refine ⟨fun h1 => absurd h1 (by omega), ?_⟩
    simp [pinnedK_10_neg hneg]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    rw [key, sum_lawS_diag]
    refine ⟨fun h1 => ?_, by split_ifs <;> norm_num⟩
    rw [ite_eq_right (show n ≠ 0 by omega)]

/-! ## The grid of scales -/

/-- `log(Y₀ (√2)^k) = log Y₀ + kℓ/2`. -/
lemma log_gridY {Y₀ : ℝ} (hY₀ : 0 < Y₀) (k : ℕ) :
    Real.log (Y₀ * √2 ^ k) = Real.log Y₀ + k * (ell / 2) := by
  have h2 : (0 : ℝ) < √2 := by positivity
  rw [Real.log_mul hY₀.ne' (pow_pos h2 k).ne', Real.log_pow, Real.log_sqrt (by norm_num)]
  rfl

/-- On the grid `Y_k = Y₀ (√2)^k` the kernel argument `u = log(Y/M) - Z_m` moves by `kℓ/2`. -/
lemma uMS_grid {Y₀ : ℝ} (hY₀ : 0 < Y₀) {M : ℕ} (hM : M ≠ 0) (S r k : ℕ) :
    uMS (Y₀ * √2 ^ k) M S r = uMS Y₀ M S r + k * (ell / 2) := by
  unfold uMS
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  rw [mul_div_right_comm, log_gridY (div_pos hY₀ hM0)]
  ring

/-- The grid `Y_k = Y₀ (√2)^k` covers `[2Y₀, ∞)`, its ratio `√2` being below `2`: every `n ≥ 2Y₀`
has `Y_k ≤ n ≤ 2Y_k` for `k = ⌊log(n/Y₀)/(ℓ/2)⌋`, and `kℓ/2 ≤ log(n/Y₀)`. -/
lemma exists_gridY {Y₀ : ℝ} (hY₀ : 0 < Y₀) {n : ℝ} (hn : 2 * Y₀ ≤ n) :
    ∃ k : ℕ, (k : ℝ) * (ell / 2) ≤ Real.log (n / Y₀) ∧ Y₀ * √2 ^ k ≤ n ∧
      n ≤ 2 * (Y₀ * √2 ^ k) := by
  have hl := ell_pos
  have hn0 : 0 < n := by linarith
  have hlogn : Real.log (n / Y₀) = Real.log n - Real.log Y₀ := Real.log_div hn0.ne' hY₀.ne'
  have hw : ell ≤ Real.log (n / Y₀) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hY₀]; linarith)
  have hw0 : 0 ≤ Real.log (n / Y₀) / (ell / 2) := div_nonneg (by linarith) (by linarith)
  have hf1 := Nat.floor_le hw0
  have hf2 := Nat.lt_floor_add_one (Real.log (n / Y₀) / (ell / 2))
  rw [le_div_iff₀ (by linarith)] at hf1
  rw [div_lt_iff₀ (by linarith)] at hf2
  refine ⟨⌊Real.log (n / Y₀) / (ell / 2)⌋₊, hf1, ?_, ?_⟩
  · have hpos : 0 < Y₀ * √2 ^ ⌊Real.log (n / Y₀) / (ell / 2)⌋₊ :=
      mul_pos hY₀ (pow_pos (by positivity) _)
    rw [← Real.log_le_log_iff hpos hn0, log_gridY hY₀]
    linarith
  · have hpos : 0 < 2 * (Y₀ * √2 ^ ⌊Real.log (n / Y₀) / (ell / 2)⌋₊) :=
      mul_pos two_pos (mul_pos hY₀ (pow_pos (by positivity) _))
    rw [← Real.log_le_log_iff hn0 hpos, Real.log_mul two_ne_zero
      (mul_pos hY₀ (pow_pos (by positivity) _)).ne', log_gridY hY₀]
    have h2 : Real.log 2 = ell := rfl
    rw [h2]
    linarith

open Classical in
/-- **The first bound for any transported integer clock with the shortcut reward**, at a fixed
threshold `x`: the sum of `1/n` over the odd `n ∈ [2x^α, x^{α²}]` of a level set is at most
`120 + C`. The pinned bound (`pinned_le_of_close`) is summed over the grid `Y_k = x^α (√2)^k`,
`k ≤ K = ⌊2(α² - α) log x/ℓ⌋`; the kernel sums are `≤ 6` (`sum_grid_pinnedK_le`), the weights
`≤ 5` (`sum_wMS_le`), `Y/L_Y ≤ 4`, and `(K + 1)·C/log x ≤ C`. -/
theorem harmonic_grid (hTM : TaoMajorant) (hTP : TaoPrefix) :
    ∃ C x₁ : ℝ, 0 ≤ C ∧ ∀ (A : Set ℕ) (q : ℕ → ℤ) (x : ℝ),
      Transport A (fun n => (q n : ℝ)) ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) x → x₁ ≤ x → ∀ j : ℤ,
        ∑ n ∈ (Icc ⌈2 * x ^ alpha⌉₊ ⌊x ^ (alpha ^ 2)⌋₊).filter
          (fun n => Odd n ∧ n ∈ A ∧ q n = j), (1 : ℝ) / n ≤ 120 + C := by
  obtain ⟨C, x₁, hC, hset⟩ := pinned_setup_fixed hTM hTP ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)
  refine ⟨C, x₁, hC, ?_⟩
  intro A q x htr hx₁ j
  obtain ⟨hL, hL1, hY⟩ := hset A _ x x htr le_rfl hx₁
  have hl := ell_pos
  have hl6 := ell_gt
  have hαα : 0 ≤ alpha ^ 2 - alpha := by unfold alpha; norm_num
  have hαα' : 4 * (alpha ^ 2 - alpha) ≤ 1 / 2 := by unfold alpha; norm_num
  obtain ⟨hx0, h2e5, hxY, -⟩ := large_facts hL (le_refl (x ^ alpha))
  have hLb : (200000 : ℝ) ≤ Lx x := hL.L_ge
  set L := Lx x with hLdef
  have hL0 : 0 < L := by linarith
  have hY₀0 : 0 < x ^ alpha := Real.rpow_pos_of_pos hx0 _
  have hx2pos : 0 < x ^ (alpha ^ 2) := Real.rpow_pos_of_pos hx0 _
  have hlogY₀ : Real.log (x ^ alpha) = alpha * L := log_rpow_Lx hx0 alpha
  have hlogx2 : Real.log (x ^ (alpha ^ 2)) = alpha ^ 2 * L := log_rpow_Lx hx0 _
  have hYk0 : ∀ k : ℕ, 0 < x ^ alpha * √2 ^ k := fun k =>
    mul_pos hY₀0 (pow_pos (by positivity) k)
  set Kx : ℕ := ⌊2 * (alpha ^ 2 - alpha) * L / ell⌋₊ with hKx
  have hKa : 0 ≤ 2 * (alpha ^ 2 - alpha) * L / ell :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hαα) hL0.le) hl.le
  -- the grid points `k ≤ K` lie in `[x^α, x^{α²}]`, and `K + 1 ≤ log x`
  have hYk1 : ∀ k : ℕ, x ^ alpha ≤ x ^ alpha * √2 ^ k := fun k =>
    le_mul_of_one_le_right hY₀0.le
      (one_le_pow₀ (Real.sqrt_one.symm.le.trans (Real.sqrt_le_sqrt (by norm_num))))
  have hYk2 : ∀ k : ℕ, k ≤ Kx → x ^ alpha * √2 ^ k ≤ x ^ (alpha ^ 2) := by
    intro k hk
    have h1 : (k : ℝ) ≤ 2 * (alpha ^ 2 - alpha) * L / ell :=
      (Nat.cast_le.mpr hk).trans (Nat.floor_le hKa)
    rw [le_div_iff₀ hl] at h1
    rw [← Real.log_le_log_iff (hYk0 k) hx2pos, log_gridY hY₀0, hlogY₀, hlogx2]
    linarith
  have hKL : ((Kx : ℕ) : ℝ) + 1 ≤ L := by
    have h1 : (Kx : ℝ) ≤ 2 * (alpha ^ 2 - alpha) * L / ell := Nat.floor_le hKa
    have h2 : 2 * (alpha ^ 2 - alpha) * L / ell ≤ L / 2 := by
      rw [div_le_iff₀ hl]
      nlinarith [mul_le_mul_of_nonneg_right hαα' hL0.le, mul_le_mul_of_nonneg_right hl6.le hL0.le]
    linarith
  set Wk : ℕ → ℝ := fun k => ∑ M ∈ EA A x, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S *
    pinnedK 1 0 (pinIdx q 1 0 x j M S) (uMS (x ^ alpha) M S (mT x) + k * (ell / 2)) with hWk
  set Pk : ℕ → ℝ := fun k => (((oddClosed (x ^ alpha * √2 ^ k)).filter
    (fun n => n ∈ A ∧ q n = j)).card : ℝ) / LY (x ^ alpha * √2 ^ k) with hPk
  -- the left side: each `n` lies in `[Y_k, 2Y_k]` for a grid point with `L_{Y_k} ≤ n`
  have hleft : ∑ n ∈ (Icc ⌈2 * x ^ alpha⌉₊ ⌊x ^ (alpha ^ 2)⌋₊).filter
      (fun n => Odd n ∧ n ∈ A ∧ q n = j), (1 : ℝ) / n ≤ ∑ k ∈ range (Kx + 1), Pk k := by
    have hpt : ∀ n ∈ (Icc ⌈2 * x ^ alpha⌉₊ ⌊x ^ (alpha ^ 2)⌋₊).filter
        (fun n => Odd n ∧ n ∈ A ∧ q n = j), (1 : ℝ) / n ≤ ∑ k ∈ range (Kx + 1),
        (if n ∈ (oddClosed (x ^ alpha * √2 ^ k)).filter (fun n => n ∈ A ∧ q n = j)
          then (1 : ℝ) / LY (x ^ alpha * √2 ^ k) else 0) := by
      intro n hn
      obtain ⟨hnI, hodd, hnA, hqj⟩ := mem_filter.mp hn
      have hn1 : 2 * x ^ alpha ≤ (n : ℝ) := Nat.ceil_le.mp (mem_Icc.mp hnI).1
      have hn2 : (n : ℝ) ≤ x ^ (alpha ^ 2) := (Nat.le_floor_iff hx2pos.le).mp (mem_Icc.mp hnI).2
      have hn0 : (0 : ℝ) < n := by linarith
      obtain ⟨k, hk1, hk2, hk3⟩ := exists_gridY hY₀0 hn1
      have hkK : k ≤ Kx := by
        apply Nat.le_floor
        rw [le_div_iff₀ hl]
        have := Real.log_le_log hn0 hn2
        rw [Real.log_div hn0.ne' hY₀0.ne', hlogY₀] at hk1
        rw [hlogx2] at this
        linarith
      have hmem : n ∈ oddClosed (x ^ alpha * √2 ^ k) := by
        unfold oddClosed
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.ceil_le.mpr hk2, Nat.le_floor hk3⟩, hodd⟩
      have hnT : n ∈ (oddClosed (x ^ alpha * √2 ^ k)).filter (fun n => n ∈ A ∧ q n = j) :=
        mem_filter.mpr ⟨hmem, hnA, hqj⟩
      have hLYk : ((LY (x ^ alpha * √2 ^ k) : ℕ) : ℝ) ≤ n := by
        have h := (card_oddClosed_real (hYk0 k).le).2
        change ((oddClosed _).card : ℝ) ≤ _
        linarith
      have hLYpos : (0 : ℝ) < LY (x ^ alpha * √2 ^ k) := by
        have : 0 < (oddClosed (x ^ alpha * √2 ^ k)).card := Finset.card_pos.mpr ⟨n, hmem⟩
        change (0 : ℝ) < ((oddClosed _).card : ℝ)
        exact_mod_cast this
      calc (1 : ℝ) / n ≤ 1 / LY (x ^ alpha * √2 ^ k) := one_div_le_one_div_of_le hLYpos hLYk
        _ = if n ∈ (oddClosed (x ^ alpha * √2 ^ k)).filter (fun n => n ∈ A ∧ q n = j)
            then (1 : ℝ) / LY (x ^ alpha * √2 ^ k) else 0 := (ite_eq_left hnT).symm
        _ ≤ ∑ k ∈ range (Kx + 1),
            (if n ∈ (oddClosed (x ^ alpha * √2 ^ k)).filter (fun n => n ∈ A ∧ q n = j)
              then (1 : ℝ) / LY (x ^ alpha * √2 ^ k) else 0) :=
          Finset.single_le_sum (f := fun k : ℕ =>
            if n ∈ (oddClosed (x ^ alpha * √2 ^ k)).filter (fun n => n ∈ A ∧ q n = j)
              then (1 : ℝ) / LY (x ^ alpha * √2 ^ k) else 0)
            (fun i _ => by positivity) (mem_range.mpr (Nat.lt_succ_of_le hkK))
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one_div]
    simp only [hPk]
    gcongr
    exact Finset.inter_subset_right
  -- each scale: the pinned bound, with the argument shifted by `kℓ/2`
  have hscale : ∀ k ∈ range (Kx + 1), Pk k ≤ 4 * Wk k + C / L := by
    intro k hk
    have hk' : k ≤ Kx := Nat.lt_succ_iff.mp (mem_range.mp hk)
    obtain ⟨hYpos, hclose, hLYpos, hY4⟩ := hY _ (hYk1 k) (hYk2 k hk')
    have h := pinned_le_of_close (ρ := 1) (η := 0) hYpos hLYpos hclose j
    have hsum_eq : ∑ M ∈ EA A x, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S *
        pinnedK 1 0 (pinIdx q 1 0 x j M S) (uMS (x ^ alpha * √2 ^ k) M S (mT x)) = Wk k := by
      refine Finset.sum_congr rfl fun M hM => Finset.sum_congr rfl fun S _ => ?_
      rw [uMS_grid hY₀0 (EA_sub A x hM).1.pos.ne']
    rw [hsum_eq] at h
    have hW0 : 0 ≤ Wk k := Finset.sum_nonneg fun M _ => Finset.sum_nonneg fun S _ =>
      mul_nonneg (wMS_nonneg x M S) (pinnedK_nonneg _ _ _ _)
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hY4 hW0) le_rfl)
  -- the kernel sums over the grid
  have hW : ∑ k ∈ range (Kx + 1), Wk k ≤ 30 := by
    simp only [hWk]
    rw [Finset.sum_comm]
    calc ∑ M ∈ EA A x, ∑ k ∈ range (Kx + 1), ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S *
          pinnedK 1 0 (pinIdx q 1 0 x j M S) (uMS (x ^ alpha) M S (mT x) + k * (ell / 2))
        = ∑ M ∈ EA A x, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S * ∑ k ∈ range (Kx + 1),
          pinnedK 1 0 (pinIdx q 1 0 x j M S) (uMS (x ^ alpha) M S (mT x) + k * (ell / 2)) := by
          refine Finset.sum_congr rfl fun M _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun S _ => by rw [Finset.mul_sum]
      _ ≤ ∑ M ∈ EA A x, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S * 6 :=
          Finset.sum_le_sum fun M _ => Finset.sum_le_sum fun S _ =>
            mul_le_mul_of_nonneg_left (sum_grid_pinnedK_le _ _ _) (wMS_nonneg x M S)
      _ = (∑ M ∈ EA A x, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S) * 6 := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun M _ => by rw [Finset.sum_mul]
      _ ≤ 5 * 6 := by
          gcongr
          exact sum_wMS_le hL (EA A x) (EA_sub A x)
      _ = 30 := by norm_num
  have hCL : 0 ≤ C / L := div_nonneg hC hL0.le
  calc ∑ n ∈ (Icc ⌈2 * x ^ alpha⌉₊ ⌊x ^ (alpha ^ 2)⌋₊).filter
        (fun n => Odd n ∧ n ∈ A ∧ q n = j), (1 : ℝ) / n
      ≤ ∑ k ∈ range (Kx + 1), Pk k := hleft
    _ ≤ ∑ k ∈ range (Kx + 1), (4 * Wk k + C / L) := Finset.sum_le_sum hscale
    _ = 4 * ∑ k ∈ range (Kx + 1), Wk k + ((Kx : ℝ) + 1) * (C / L) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_range, nsmul_eq_mul]
        push_cast; ring
    _ ≤ 4 * 30 + L * (C / L) := by gcongr
    _ = 120 + C := by field_simp; ring

open Classical in
/-- **The first bound of Proposition 6.12**, with an explicit `0 ≤ C`: `C, x₀` absolute; for
`b ≥ 1`, `x ≥ x₀` with `x > b` and every `m`, the sum of `1/n` over the odd `n ∈ [2x^α, x^{α²}]`
with `n ∈ P_F(b)` and `τ_{F,b}(n) = m` is at most `C`. `harmonic_grid` at threshold `x` for the
clock `-τ_{F,b}` (transported at `x > b`, `transport_F_of_lt`) and the level `-m`. -/
theorem harmonic_first (hTM : TaoMajorant) (hTP : TaoPrefix) :
    ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ b : ℕ, 0 < b → ∀ x : ℝ, x₀ ≤ x → (b : ℝ) < x → ∀ m : ℕ,
      ∑ n ∈ (Icc ⌈2 * x ^ alpha⌉₊ ⌊x ^ (alpha ^ 2)⌋₊).filter
          (fun n => Odd n ∧ n ∈ Pred F b ∧ hit F b n = m), (1 : ℝ) / n ≤ C := by
  obtain ⟨C, x₁, hC, h⟩ := harmonic_grid hTM hTP
  refine ⟨120 + C, x₁, by positivity, fun b _ x hx hbx m => ?_⟩
  have htr : Transport (Pred F b) (fun n => ((-(hit F b n : ℤ) : ℤ) : ℝ)) ((1 : ℕ) : ℝ)
      ((0 : ℕ) : ℝ) x := by simpa using transport_F_of_lt b hbx
  have hfilt : (Icc ⌈2 * x ^ alpha⌉₊ ⌊x ^ (alpha ^ 2)⌋₊).filter
      (fun n => Odd n ∧ n ∈ Pred F b ∧ hit F b n = m) =
      (Icc ⌈2 * x ^ alpha⌉₊ ⌊x ^ (alpha ^ 2)⌋₊).filter
      (fun n => Odd n ∧ n ∈ Pred F b ∧ -(hit F b n : ℤ) = -(m : ℤ)) :=
    Finset.filter_congr fun n _ => by simp only [neg_inj, Nat.cast_inj]
  rw [hfilt]
  exact h (Pred F b) (fun n => -(hit F b n : ℤ)) x htr hx (-(m : ℤ))

/-! ## The second bound: the constraint `n ≤ b 2^m` -/

/-- `n ≤ 2 F(n)`: one step of `F` at least halves. -/
lemma le_two_mul_F (n : ℕ) : n ≤ 2 * F n := by
  unfold F; split_ifs with h
  · obtain ⟨k, rfl⟩ := h; omega
  · omega

/-- `n ≤ 2^k F^k(n)`. -/
lemma le_pow_mul_F_iterate (n k : ℕ) : n ≤ 2 ^ k * F^[k] n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, pow_succ]
    calc n ≤ 2 * F n := le_two_mul_F n
      _ ≤ 2 * (2 ^ k * F^[k] (F n)) := Nat.mul_le_mul_left 2 (ih (F n))
      _ = 2 ^ k * 2 * F^[k] (F n) := by ring

/-- `τ_{F,b}(n) = m` forces `n ≤ b 2^m`, since `F(n) ≥ n/2` (proof of Proposition 6.12). -/
lemma le_of_hit_F {b n m : ℕ} (hn : n ∈ Pred F b) (hm : hit F b n = m) : n ≤ b * 2 ^ m := by
  have h := le_pow_mul_F_iterate n (hit F b n)
  rw [iterate_hit hn.2, hm] at h
  rw [mul_comm]; exact h

/-! ## The second bound: the summand and the even sources -/

open Classical in
/-- The summand of the second bound: `1/n` on the level set `τ_{F,b}(n) = m` of `P_F(b)`, `n > 0`. -/
def hsumF (b m n : ℕ) : ℝ := if 0 < n ∧ n ∈ Pred F b ∧ hit F b n = m then (1 : ℝ) / n else 0

lemma hsumF_nonneg (b m n : ℕ) : 0 ≤ hsumF b m n := by
  unfold hsumF; split_ifs <;> positivity

/-- The summand vanishes above `b 2^m` (`le_of_hit_F`). -/
lemma hsumF_eq_zero {b m n : ℕ} (hn : b * 2 ^ m < n) : hsumF b m n = 0 := by
  classical
  unfold hsumF
  rw [ite_eq_right_iff]
  rintro ⟨-, hP, hh⟩
  exact absurd (le_of_hit_F hP hh) (not_le.mpr hn)

lemma summable_hsumF_comp (b m : ℕ) (g : ℕ → ℕ) (hg : ∀ k, k ≤ g k) :
    Summable (fun k => hsumF b m (g k)) :=
  summable_of_ne_finset_zero (s := range (b * 2 ^ m + 1)) fun k hk =>
    hsumF_eq_zero (by simp only [mem_range, not_lt] at hk; have := hg k; omega)

lemma summable_hsumF (b m : ℕ) : Summable (fun n => hsumF b m n) :=
  summable_of_ne_finset_zero (s := range (b * 2 ^ m + 1)) fun n hn =>
    hsumF_eq_zero (by simp only [mem_range, not_lt] at hn; omega)

/-- `m = 0`: the only source is `n = b`, of weight `1/b ≤ 1`. -/
lemma tsum_hsumF_zero (b : ℕ) (hb : 0 < b) : ∑' n, hsumF b 0 n ≤ 1 := by
  classical
  rw [tsum_eq_single b]
  · unfold hsumF; split_ifs
    · rw [div_le_one (by exact_mod_cast hb)]; exact_mod_cast hb
    · norm_num
  · intro n hn
    unfold hsumF
    rw [ite_eq_right_iff]
    rintro ⟨-, hP, hh⟩
    have h := iterate_hit hP.2
    rw [hh] at h
    exact absurd h hn

/-- An even source `2k` with `τ_{F,b}(2k) = m + 1 ≥ 1` is not `b`, so `τ(2k) = τ(k) + 1`
(`hit_F_two_mul`): its weight is half that of the source `k` at level `m`. -/
lemma hsumF_two_mul_le {b m : ℕ} (k : ℕ) : hsumF b (m + 1) (2 * k) ≤ hsumF b m k / 2 := by
  classical
  unfold hsumF
  by_cases h1 : 0 < 2 * k ∧ 2 * k ∈ Pred F b ∧ hit F b (2 * k) = m + 1
  · obtain ⟨h0, hP, hh⟩ := h1
    have hk0 : 0 < k := by omega
    have hb : 2 * k ≠ b := by
      intro hb
      have : hit F b (2 * k) = 0 := Nat.le_zero.mp (hit_le (show F^[0] (2 * k) = b from hb))
      omega
    have hPk : k ∈ Pred F b := (two_mul_mem_predF_iff hk0 hb).mp hP
    have hhk : hit F b k = m := by have := hit_F_two_mul hb hPk; omega
    rw [ite_eq_left (show 0 < 2 * k ∧ 2 * k ∈ Pred F b ∧ hit F b (2 * k) = m + 1 from
      ⟨h0, hP, hh⟩), ite_eq_left (show 0 < k ∧ k ∈ Pred F b ∧ hit F b k = m from ⟨hk0, hPk, hhk⟩)]
    push_cast
    exact le_of_eq (by ring)
  · rw [ite_eq_right h1]
    exact div_nonneg (by split_ifs <;> positivity) (by norm_num)

/-! ## The second bound: the odd sources -/

/-- The ratio `β = (1 + α)/2 ∈ (1, α)` of the exponents `log x_i = t₀ β^i` of the covering. -/
def covB : ℝ := (1 + alpha) / 2

lemma one_lt_covB : 1 < covB := by unfold covB alpha; norm_num

open Classical in
/-- The summation set of the first bound at threshold `x`: the odd `n ∈ [2x^α, x^{α²}]` with
`n ∈ P_F(b)` and `τ_{F,b}(n) = m`. -/
def firstSet (b m : ℕ) (x : ℝ) : Finset ℕ :=
  (Icc ⌈2 * x ^ alpha⌉₊ ⌊x ^ (alpha ^ 2)⌋₊).filter (fun n => Odd n ∧ n ∈ Pred F b ∧ hit F b n = m)

/-- **The covering of the second bound.** For `t₀ ≥ 2000` and `log n ≥ log 2 + αt₀`, the range
`[2x_i^α, x_i^{α²}]` with `x_i = exp(t₀β^i)` contains `n` for `i = ⌊log y/log β⌋`,
`y = (log n - log 2)/(αt₀)`: `β^i ≤ y < β^{i+1}`, and consecutive ranges overlap because
`log 2 ≤ α(α - β)t₀`. Moreover `i ≤ log(log n)/log β`. -/
lemma exists_cover_index {t₀ : ℝ} (ht₀ : 2000 ≤ t₀) {n : ℝ} (hn0 : 0 < n)
    (hn : Real.log 2 + alpha * t₀ ≤ Real.log n) :
    ∃ i : ℕ, 2 * Real.exp (t₀ * covB ^ i) ^ alpha ≤ n ∧
      n ≤ Real.exp (t₀ * covB ^ i) ^ (alpha ^ 2) ∧
      (i : ℝ) ≤ Real.log (Real.log n) / Real.log covB := by
  have hα : (1 : ℝ) < alpha := by unfold alpha; norm_num
  have hβ1 := one_lt_covB
  have hlβ : 0 < Real.log covB := Real.log_pos hβ1
  have hgap : 1 ≤ alpha * (alpha - covB) * 2000 := by unfold covB alpha; norm_num
  have hgap0 : 0 ≤ alpha * (alpha - covB) := by unfold covB alpha; norm_num
  have hl2 := Real.log_pos one_lt_two
  have hl2' := Real.log_two_lt_d9
  have hαt : 0 < alpha * t₀ := mul_pos (by linarith) (by linarith)
  have hαt1 : 1 ≤ alpha * t₀ := by nlinarith
  set y := (Real.log n - Real.log 2) / (alpha * t₀) with hy
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hαt]; linarith
  have hy0 : 0 < y := by linarith
  have hly : 0 ≤ Real.log y / Real.log covB := div_nonneg (Real.log_nonneg hy1) hlβ.le
  have hi1 := Nat.floor_le hly
  have hi2 := Nat.lt_floor_add_one (Real.log y / Real.log covB)
  set i := ⌊Real.log y / Real.log covB⌋₊ with hi
  have hb1 : covB ^ i ≤ y := by
    rw [← Real.log_le_log_iff (pow_pos (by linarith) i) hy0, Real.log_pow]
    rw [le_div_iff₀ hlβ] at hi1; linarith
  have hb2 : y < covB ^ (i + 1) := by
    rw [← Real.log_lt_log_iff hy0 (pow_pos (by linarith) _), Real.log_pow]
    rw [div_lt_iff₀ hlβ] at hi2; push_cast; linarith
  have hE : 2000 ≤ t₀ * covB ^ i :=
    ht₀.trans (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hβ1.le))
  refine ⟨i, ?_, ?_, ?_⟩
  · rw [← Real.exp_mul]
    have h2 : 2 * Real.exp (t₀ * covB ^ i * alpha) =
        Real.exp (Real.log 2 + t₀ * covB ^ i * alpha) := by
      rw [Real.exp_add, Real.exp_log two_pos]
    rw [h2]
    calc Real.exp (Real.log 2 + t₀ * covB ^ i * alpha) ≤ Real.exp (Real.log n) := by
          apply Real.exp_le_exp.mpr
          rw [hy, le_div_iff₀ hαt] at hb1
          linarith
      _ = n := Real.exp_log hn0
  · rw [← Real.exp_mul]
    calc n = Real.exp (Real.log n) := (Real.exp_log hn0).symm
      _ ≤ Real.exp (t₀ * covB ^ i * alpha ^ 2) := by
          apply Real.exp_le_exp.mpr
          rw [hy, div_lt_iff₀ hαt, pow_succ] at hb2
          have h3 := mul_le_mul_of_nonneg_left hE hgap0
          linarith
  · have hyl : y ≤ Real.log n := by
      rw [hy, div_le_iff₀ hαt]
      nlinarith [mul_le_mul_of_nonneg_left hαt1 (show 0 ≤ Real.log n by linarith)]
    calc (i : ℝ) ≤ Real.log y / Real.log covB := hi1
      _ ≤ Real.log (Real.log n) / Real.log covB :=
          div_le_div_of_nonneg_right (Real.log_le_log hy0 hyl) hlβ.le

open Classical in
/-- **The odd sources of the second bound:** for `b ≥ 1` there is `D` with
`∑_{n odd, τ_{F,b}(n) = m} 1/n ≤ D log(m+2)` for every `m`. The odd `n ≤ b 2^m` below
`N₀ = ⌈2e^{αt₀}⌉` contribute at most `N₀`; every other one lies in a range `[2x_i^α, x_i^{α²}]`,
`log x_i = t₀β^i` (`exists_cover_index`), with `i ≤ I(m) = ⌊log(log b + m + 1)/log β⌋`, and each
range has harmonic mass at most `C` by the first bound (`t₀ ≥ max(x₀, b)`). Finally
`N₀ + (I(m) + 1)C = O_b(log(m+2))`. -/
theorem harmonic_odd (hTM : TaoMajorant) (hTP : TaoPrefix) (b : ℕ) (hb : 0 < b) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m : ℕ, ∑' k, hsumF b m (2 * k + 1) ≤ D * Real.log (m + 2) := by
  obtain ⟨C, x₀, hC, h1⟩ := harmonic_first hTM hTP
  have hα : (1 : ℝ) < alpha := by unfold alpha; norm_num
  have hβ1 := one_lt_covB
  have hlβ : 0 < Real.log covB := Real.log_pos hβ1
  have hl2 := Real.log_pos one_lt_two
  have hl2' := Real.log_two_lt_d9
  set t₀ : ℝ := max (max x₀ (b : ℝ)) 2000 with ht₀
  have ht₀2 : 2000 ≤ t₀ := le_max_right _ _
  have ht₀x : x₀ ≤ t₀ := (le_max_left _ _).trans (le_max_left _ _)
  have ht₀b : (b : ℝ) ≤ t₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hαt : 0 < alpha * t₀ := mul_pos (by linarith) (by linarith)
  -- every range of the covering is admissible for the first bound
  have hxi : ∀ i : ℕ, x₀ ≤ Real.exp (t₀ * covB ^ i) ∧ (b : ℝ) < Real.exp (t₀ * covB ^ i) := by
    intro i
    have h1 : t₀ ≤ t₀ * covB ^ i := le_mul_of_one_le_right (by linarith) (one_le_pow₀ hβ1.le)
    have h2 := Real.add_one_le_exp (t₀ * covB ^ i)
    constructor <;> linarith
  set N₀ : ℕ := ⌈2 * Real.exp (alpha * t₀)⌉₊ with hN₀
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb)
  set a : ℝ := Real.log (Real.log b + 1) with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
  set Q : ℝ := (a + 1) / Real.log covB + 1 with hQ
  have hQ0 : 0 ≤ Q := add_nonneg (div_nonneg (by linarith) hlβ.le) zero_le_one
  refine ⟨(N₀ + C * Q) / Real.log 2,
    div_nonneg (add_nonneg (Nat.cast_nonneg _) (mul_nonneg hC hQ0)) hl2.le, fun m => ?_⟩
  set I : ℕ := ⌊Real.log (Real.log b + m + 1) / Real.log covB⌋₊ with hI
  -- the odd sources, as a finite sum
  have hsupp : ∀ n ∉ range (b * 2 ^ m + 1), (if Odd n then hsumF b m n else 0) = 0 := by
    intro n hn
    rw [hsumF_eq_zero (by simp only [mem_range, not_lt] at hn; omega)]
    simp
  have hsg : Summable (fun n => if Odd n then hsumF b m n else 0) :=
    summable_of_ne_finset_zero hsupp
  have hA : ∑' k, hsumF b m (2 * k + 1) ≤ ∑' n, (if Odd n then hsumF b m n else 0) := by
    have := tsum_comp_le_tsum_of_inj hsg
      (fun n => by split_ifs; exacts [hsumF_nonneg _ _ _, le_rfl])
      (i := fun k => 2 * k + 1) (fun k k' h => by simp only at h; omega)
    refine (tsum_congr fun k => ?_).trans_le this
    simp only [Function.comp_apply]
    rw [ite_eq_left (odd_two_mul_add_one k)]
  rw [tsum_eq_sum hsupp] at hA
  -- pointwise: small `n`, or one range of the covering
  have hpt : ∀ n ∈ range (b * 2 ^ m + 1), (if Odd n then hsumF b m n else 0) ≤
      (if n < N₀ then (1 : ℝ) else 0) + ∑ i ∈ range (I + 1),
        (if n ∈ firstSet b m (Real.exp (t₀ * covB ^ i)) then (1 : ℝ) / n else 0) := by
    intro n _
    have hR0 : 0 ≤ ∑ i ∈ range (I + 1),
        (if n ∈ firstSet b m (Real.exp (t₀ * covB ^ i)) then (1 : ℝ) / n else 0) :=
      Finset.sum_nonneg fun i _ => by positivity
    by_cases hodd : Odd n
    · rw [ite_eq_left hodd]
      unfold hsumF
      by_cases hc : 0 < n ∧ n ∈ Pred F b ∧ hit F b n = m
      · rw [ite_eq_left hc]
        obtain ⟨hn0, hP, hh⟩ := hc
        have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
        by_cases hsm : n < N₀
        · rw [ite_eq_left hsm]
          have : (1 : ℝ) / n ≤ 1 := by
            rw [div_le_one hnr]; exact_mod_cast hn0
          linarith
        · rw [ite_eq_right hsm, zero_add]
          have hn1 : 2 * Real.exp (alpha * t₀) ≤ (n : ℝ) := Nat.ceil_le.mp (not_lt.mp hsm)
          have hlog : Real.log 2 + alpha * t₀ ≤ Real.log n := by
            have := Real.log_le_log (by positivity) hn1
            rwa [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp] at this
          obtain ⟨i, hi1, hi2, hi3⟩ := exists_cover_index ht₀2 hnr hlog
          have hiI : i ≤ I := by
            apply Nat.le_floor
            refine hi3.trans (div_le_div_of_nonneg_right ?_ hlβ.le)
            have hnb : (n : ℝ) ≤ b * 2 ^ m := by exact_mod_cast le_of_hit_F hP hh
            have hlogn : Real.log n ≤ Real.log b + m := by
              have := Real.log_le_log hnr hnb
              rw [Real.log_mul (Nat.cast_pos.mpr hb).ne' (pow_pos two_pos m).ne',
                Real.log_pow] at this
              nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
            exact Real.log_le_log (by linarith) (by linarith)
          have hmem : n ∈ firstSet b m (Real.exp (t₀ * covB ^ i)) := by
            unfold firstSet
            exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.ceil_le.mpr hi1,
              Nat.le_floor hi2⟩, hodd, hP, hh⟩
          calc (1 : ℝ) / n = if n ∈ firstSet b m (Real.exp (t₀ * covB ^ i)) then (1 : ℝ) / n
                else 0 := (ite_eq_left hmem).symm
            _ ≤ ∑ i ∈ range (I + 1),
                (if n ∈ firstSet b m (Real.exp (t₀ * covB ^ i)) then (1 : ℝ) / n else 0) :=
              Finset.single_le_sum (f := fun i : ℕ =>
                if n ∈ firstSet b m (Real.exp (t₀ * covB ^ i)) then (1 : ℝ) / n else 0)
                (fun i _ => by positivity) (mem_range.mpr (Nat.lt_succ_of_le hiI))
      · rw [ite_eq_right hc]
        have : (0 : ℝ) ≤ if n < N₀ then 1 else 0 := by positivity
        linarith
    · rw [ite_eq_right hodd]
      have : (0 : ℝ) ≤ if n < N₀ then 1 else 0 := by positivity
      linarith
  have hsmall : ∑ n ∈ range (b * 2 ^ m + 1), (if n < N₀ then (1 : ℝ) else 0) ≤ N₀ := by
    rw [Finset.sum_boole]
    exact_mod_cast (card_le_card (fun n hn => mem_range.mpr (mem_filter.mp hn).2)).trans
      (card_range N₀).le
  have hrange : ∀ i ∈ range (I + 1), ∑ n ∈ range (b * 2 ^ m + 1),
      (if n ∈ firstSet b m (Real.exp (t₀ * covB ^ i)) then (1 : ℝ) / n else 0) ≤ C := by
    intro i _
    rw [Finset.sum_ite_mem]
    refine (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun n _ _ => by positivity)).trans ?_
    exact h1 b hb _ (hxi i).1 (hxi i).2 m
  have hB : ∑ n ∈ range (b * 2 ^ m + 1), (if Odd n then hsumF b m n else 0) ≤
      N₀ + ((I : ℝ) + 1) * C := by
    calc _ ≤ ∑ n ∈ range (b * 2 ^ m + 1), ((if n < N₀ then (1 : ℝ) else 0) +
          ∑ i ∈ range (I + 1),
            (if n ∈ firstSet b m (Real.exp (t₀ * covB ^ i)) then (1 : ℝ) / n else 0)) :=
          Finset.sum_le_sum hpt
      _ = ∑ n ∈ range (b * 2 ^ m + 1), (if n < N₀ then (1 : ℝ) else 0) +
          ∑ i ∈ range (I + 1), ∑ n ∈ range (b * 2 ^ m + 1),
            (if n ∈ firstSet b m (Real.exp (t₀ * covB ^ i)) then (1 : ℝ) / n else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
      _ ≤ N₀ + ∑ i ∈ range (I + 1), C := add_le_add hsmall (Finset.sum_le_sum hrange)
      _ = N₀ + ((I : ℝ) + 1) * C := by
          rw [Finset.sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  -- `N₀ + (I + 1)C ≤ (N₀ + CQ) log(m+2)/log 2`
  have hm2 : Real.log 2 ≤ Real.log (m + 2) :=
    Real.log_le_log two_pos (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  set r := Real.log (m + 2) / Real.log 2 with hr
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hl2]; linarith
  have hlm : Real.log (m + 2) = r * Real.log 2 := by rw [hr]; field_simp
  have hIQ : (I : ℝ) + 1 ≤ Q * r := by
    have hI1 : (I : ℝ) ≤ Real.log (Real.log b + m + 1) / Real.log covB :=
      Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]))
        hlβ.le)
    have hI2 : Real.log (Real.log b + m + 1) ≤ a + Real.log (m + 2) := by
      rw [ha, ← Real.log_mul (by linarith) (by positivity)]
      exact Real.log_le_log (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
        (by nlinarith [mul_nonneg hlb (Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have hI3 : a + Real.log (m + 2) ≤ (a + 1) * r := by
      rw [hlm]
      nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hr1),
        mul_nonneg (by linarith : (0 : ℝ) ≤ r) (by linarith : (0 : ℝ) ≤ 1 - Real.log 2)]
    have hI4 : (I : ℝ) ≤ (a + 1) * r / Real.log covB :=
      hI1.trans (div_le_div_of_nonneg_right (hI2.trans hI3) hlβ.le)
    have : (a + 1) * r / Real.log covB = (a + 1) / Real.log covB * r := by ring
    rw [hQ]
    nlinarith
  have e1 : (N₀ : ℝ) ≤ N₀ * r := le_mul_of_one_le_right (Nat.cast_nonneg _) hr1
  have e2 : ((I : ℝ) + 1) * C ≤ Q * r * C := mul_le_mul_of_nonneg_right hIQ hC
  calc ∑' k, hsumF b m (2 * k + 1) ≤ N₀ + ((I : ℝ) + 1) * C := hA.trans hB
    _ ≤ (N₀ + C * Q) * r := by linarith
    _ = (N₀ + C * Q) / Real.log 2 * Real.log (m + 2) := by rw [hlm]; field_simp

/-- **The second bound of Proposition 6.12:** `∑_{n ≥ 1, τ_{F,b}(n) = m} 1/n ≤ C_b log(m+2)`. With
`G(m) = ∑_n hsumF b m n`: `G(0) ≤ 1/b ≤ 1`, and for `m ≥ 1` the even sources give at most `G(m-1)/2`
(`hsumF_two_mul_le`, through `tsum_even_add_odd`) and the odd ones at most `D log(m+2)`
(`harmonic_odd`), so `G(m) ≤ 2D log(m+2) + 1` by induction. -/
theorem harmonic_second (hTM : TaoMajorant) (hTP : TaoPrefix) :
    ∀ b : ℕ, 0 < b → ∃ C : ℝ, ∀ m : ℕ, ∑' n, hsumF b m n ≤ C * Real.log (m + 2) := by
  intro b hb
  obtain ⟨D, hD, hodd⟩ := harmonic_odd hTM hTP b hb
  have hl2 := Real.log_pos one_lt_two
  have key : ∀ m : ℕ, ∑' n, hsumF b m n ≤ 2 * D * Real.log (m + 2) + 1 := by
    intro m
    induction m with
    | zero =>
      have h0 := tsum_hsumF_zero b hb
      have : 0 ≤ 2 * D * Real.log (((0 : ℕ) : ℝ) + 2) :=
        mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
      linarith
    | succ m ih =>
      rw [← tsum_even_add_odd (summable_hsumF_comp b (m + 1) (fun k => 2 * k) (fun k => by omega))
        (summable_hsumF_comp b (m + 1) (fun k => 2 * k + 1) (fun k => by omega))]
      have hE : ∑' k, hsumF b (m + 1) (2 * k) ≤ (∑' n, hsumF b m n) / 2 := by
        rw [← tsum_div_const]
        exact Summable.tsum_le_tsum (fun k => hsumF_two_mul_le k)
          (summable_hsumF_comp b (m + 1) (fun k => 2 * k) (fun k => by omega))
          ((summable_hsumF b m).div_const 2)
      have hO := hodd (m + 1)
      have hlog : Real.log ((m : ℝ) + 2) ≤ Real.log (((m + 1 : ℕ) : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by push_cast; linarith)
      have := mul_le_mul_of_nonneg_left hlog hD
      linarith
  refine ⟨2 * D + 1 / Real.log 2, fun m => ?_⟩
  have hm2 : Real.log 2 ≤ Real.log (m + 2) :=
    Real.log_le_log two_pos (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have h1 : 1 ≤ Real.log (m + 2) / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
  calc ∑' n, hsumF b m n ≤ 2 * D * Real.log (m + 2) + 1 := key m
    _ ≤ 2 * D * Real.log (m + 2) + Real.log (m + 2) / Real.log 2 := by linarith
    _ = (2 * D + 1 / Real.log 2) * Real.log (m + 2) := by ring

/-! ## Proposition 6.12 -/

open Classical in
/-- **Proposition 6.12 [`prop:harmonicfirsthit`] (first-hit harmonic sums).** First bound: `C, x₀`
absolute; for `b ≥ 1`, `x ≥ x₀` with `x > b`, uniformly in `m ≥ 0`, the sum of `1/n` over odd
`n ∈ [2x^α, x^{α²}]` with `τ_{F,b}(n) = m` (so `n ∈ P_F(b)`) is `≤ C`. Second bound:
`∑_{n ≥ 1, τ_{F,b}(n) = m} 1/n = O_b(log(m+2))`, over all positive `n` (a finite sum, since
`τ_{F,b}(n) = m` forces `n ≤ b 2^m`; written as a `tsum`). No Diophantine input. -/
theorem harmonicfirsthit (hTM : TaoMajorant) (hTP : TaoPrefix) :
    (∃ C x₀ : ℝ, ∀ b : ℕ, 0 < b → ∀ x : ℝ, x₀ ≤ x → (b : ℝ) < x → ∀ m : ℕ,
      ∑ n ∈ (Icc ⌈2 * x ^ alpha⌉₊ ⌊x ^ (alpha ^ 2)⌋₊).filter
          (fun n => Odd n ∧ n ∈ Pred F b ∧ hit F b n = m), (1 : ℝ) / n ≤ C) ∧
    (∀ b : ℕ, 0 < b → ∃ C : ℝ, ∀ m : ℕ,
      ∑' n : ℕ, (if 0 < n ∧ n ∈ Pred F b ∧ hit F b n = m then (1 : ℝ) / n else 0) ≤
        C * Real.log (m + 2)) := by
  obtain ⟨C, x₀, -, h1⟩ := harmonic_first hTM hTP
  exact ⟨⟨C, x₀, h1⟩, harmonic_second hTM hTP⟩

end CollatzCLT
