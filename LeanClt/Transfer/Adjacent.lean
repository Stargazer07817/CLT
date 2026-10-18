import LeanClt.Transfer.Scalar
import LeanClt.Architecture.FixedBase

/-!
# §6.1–6.2: transported populations and Lemma 6.1 (adjacent scales)

For a set `A` and clock `q` with the transport property (6.2) and `E'_A = 𝓜_x ∩ A`:

* `phi0_close`: `E[1_A(N_Y) e^{isq(N_Y)}]` is the left side of (5.14) with `E' = E'_A`, up to the
  atypical sources (Lemma 5.1);
* `renorm_close`: the renormalised characteristic function `Ψ_Y(s)` is within
  `O((log x)^{-δ₀})` of `K_x(s)` (6.5), which does not depend on `Y`;
* `adjacent_uniform` (Lemma 6.1 [`lem:adjacent`], uniform form): choosing `x = Y^{1/α}` puts `Y`
  and `Y'` in the same range. The constants `δ`, `C` and `x₁` do not depend on the set `A`, the
  clock `q` or the transport threshold `x₀`, which enters only through `Y ≥ max(x₁, x₀)^α`;
* `adjacent_of_transport` (Lemma 6.1): the uniform form for one set and clock.

Until checkpoint 15, `adjacent_of_transport` carried the proof and `adjacent_uniform`, in
`AdjacentUniform.lean`, a copy of it with `x₀ ≤ x` split off as a hypothesis. The proof now
exists once, in `adjacent_uniform`, and `adjacent_of_transport` is derived from it (decision D3).
Neither statement changed.
-/

open Real Finset Complex Filter

noncomputable section

namespace CollatzCLT

open Classical in
/-- `𝓜_x` as a finite set. -/
def Mfin (x : ℝ) : Finset ℕ :=
  (range (⌊Real.exp (Lx x + c * mT x + Lx x ^ (0.7 : ℝ))⌋₊ + 1)).filter (fun M => M ∈ Mset x)

lemma mem_Mfin {x : ℝ} {M : ℕ} : M ∈ Mfin x ↔ M ∈ Mset x := by
  classical
  unfold Mfin
  rw [mem_filter, mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hM0 : (0 : ℝ) < M := by exact_mod_cast h.1.pos
  have hlog := (abs_le.mp h.2.2.2).2
  have : (M : ℝ) ≤ Real.exp (Lx x + c * mT x + Lx x ^ (0.7 : ℝ)) := by
    rw [← Real.exp_log hM0]; exact Real.exp_le_exp.mpr (by linarith)
  exact Nat.lt_succ_of_le (Nat.le_floor this)

open Classical in
/-- `E'_A = 𝓜_x ∩ A`. -/
def EA (A : Set ℕ) (x : ℝ) : Finset ℕ := (Mfin x).filter (fun M => M ∈ A)

lemma EA_sub (A : Set ℕ) (x : ℝ) : (↑(EA A x) : Set ℕ) ⊆ Mset x := by
  intro M hM
  classical
  unfold EA at hM
  rw [Finset.mem_coe, mem_filter] at hM
  exact mem_Mfin.mp hM.1

lemma mem_EA {A : Set ℕ} {x : ℝ} {M : ℕ} (hM : M ∈ Mset x) : M ∈ EA A x ↔ M ∈ A := by
  classical
  unfold EA
  rw [mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_Mfin.mpr hM, h⟩⟩

/-- `Φ⁰_Y(s) = E[1_A(N_Y) e^{isq(N_Y)}]`. -/
def phi0 (A : Set ℕ) (q : ℕ → ℝ) (Y s : ℝ) : ℂ :=
  ((oddClosed Y).card : ℂ)⁻¹ * ∑ u ∈ oddClosed Y, A.indicator (fun n => cexp (((s * q n : ℝ) : ℂ) * I)) u

open Classical in
/-- **Transport identifies the population with the first-passage event.** -/
theorem phi0_close {A : Set ℕ} {q : ℕ → ℝ} {ρ η x₀ : ℝ} (htr : Transport A q ρ η x₀) {x Y : ℝ}
    (hx : x₀ ≤ x) (hL : Large x) (hY1 : x ^ alpha ≤ Y) (hY2 : Y ≤ x ^ (alpha ^ 2)) (s : ℝ) :
    ‖phi0 A q Y s - transferLHS x Y (EA A x) q ρ η s‖ ≤
      2 * (((oddClosed Y).filter (fun N => ¬ Good x N)).card : ℝ) / LY Y := by
  obtain ⟨hx0, -, hxY, hY0⟩ := large_facts hL hY1
  have hLYpos : (0 : ℝ) < LY Y := LY_pos (by linarith [large_facts hL hY1])
  unfold phi0 transferLHS
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast,
    show ((oddClosed Y).card : ℝ) = LY Y from rfl, div_eq_mul_inv, mul_comm _ (LY Y : ℝ)⁻¹]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hpt : ∀ N ∈ oddClosed Y, ‖A.indicator (fun n => cexp (((s * q n : ℝ) : ℂ) * I)) N -
      (if Event x (EA A x) N then cexp ((((s * (q (U^[passT x N - mT x] N) -
        ρ * wsum (vword N) (passT x N - mT x) - η * (passT x N - mT x : ℕ))) : ℝ) : ℂ) * I)
        else 0)‖ ≤ if ¬ Good x N then 2 else 0 := by
    intro N hN
    by_cases hG : Good x N
    · rw [if_neg (not_not.mpr hG)]
      obtain ⟨hNo, -, -⟩ := mem_oddClosed hY0.le hN
      obtain ⟨hcr, hmp, -, -, hMs⟩ := orbit_window hL hY1 hY2 hN hG
      obtain ⟨hiff, hq⟩ := htr x hx hL.m_ge N hNo hcr hmp hMs
      have hEv : Event x (EA A x) N ↔ N ∈ A := by
        unfold Event
        rw [mem_EA hMs, ← hiff]
        exact ⟨fun h => h.2.2, fun h => ⟨hcr, hmp, h⟩⟩
      by_cases hA : N ∈ A
      · rw [Set.indicator_of_mem hA, if_pos (hEv.mpr hA), hq hA, sub_self, norm_zero]
      · rw [Set.indicator_of_notMem hA, if_neg (fun h => hA (hEv.mp h)), sub_self, norm_zero]
    · rw [if_pos hG]
      refine (norm_sub_le _ _).trans ?_
      have h1 := norm_ph_le A q s 0 N
      unfold ph at h1
      simp only [add_zero] at h1
      have h2 : ‖(if Event x (EA A x) N then cexp ((((s * (q (U^[passT x N - mT x] N) -
          ρ * wsum (vword N) (passT x N - mT x) - η * (passT x N - mT x : ℕ))) : ℝ) : ℂ) * I)
          else 0)‖ ≤ 1 := by
        split_ifs
        · rw [Complex.norm_exp_ofReal_mul_I]
        · simp
      linarith
  calc _ ≤ ∑ N ∈ oddClosed Y, ‖A.indicator (fun n => cexp (((s * q n : ℝ) : ℂ) * I)) N -
        (if Event x (EA A x) N then cexp ((((s * (q (U^[passT x N - mT x] N) -
          ρ * wsum (vword N) (passT x N - mT x) - η * (passT x N - mT x : ℕ))) : ℝ) : ℂ) * I)
          else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ N ∈ oddClosed Y, (if ¬ Good x N then (2 : ℝ) else 0) := Finset.sum_le_sum hpt
    _ = 2 * ((oddClosed Y).filter (fun N => ¬ Good x N)).card := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ## The renormalised characteristic function -/

/-- `e^{(Ds² + iκs) log Z}`. -/
def Ez (D κ Z s : ℝ) : ℂ := cexp (((D * s ^ 2 * Real.log Z : ℝ) : ℂ) + ((s * κ * Real.log Z : ℝ) : ℂ) * I)

lemma norm_Ez (D κ Z s : ℝ) : ‖Ez D κ Z s‖ = Real.exp (D * s ^ 2 * Real.log Z) := by
  unfold Ez
  rw [Complex.norm_exp, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring_nf

lemma oddCF_eq (A : Set ℕ) (q : ℕ → ℝ) (κ Z s : ℝ) :
    oddCF A q κ Z s = cexp (((s * κ * Real.log Z : ℝ) : ℂ) * I) * phi0 A q Z s := by
  unfold oddCF phi0
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold ph
  by_cases hu : u ∈ A
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, ← Complex.exp_add]
    congr 1; push_cast; ring
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]

lemma renorm_eq (A : Set ℕ) (q : ℕ → ℝ) (κ D Z s : ℝ) :
    renorm (oddCF A q κ) D Z s = Ez D κ Z s * phi0 A q Z s := by
  unfold renorm Ez
  rw [oddCF_eq, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]

/-- `v = log M + Z_m` at `S_m = S`. -/
def vMS (M S m : ℕ) : ℝ := Real.log M + (ell * S - bet * m)

/-- **The `Y`-free kernel `K_x(s)` (6.5).** -/
def Kx (A : Set ℕ) (q : ℕ → ℝ) (ρ η x s : ℝ) : ℂ :=
  (2 / c : ℂ) * ∑ M ∈ EA A x, ∑ S ∈ Icc (mT x) (3 * mT x),
    (((3 : ℝ) ^ mT x / M * muJ (mT x) S (M : ZMod (3 ^ mT x)) : ℝ) : ℂ) *
      phase q ρ η s M S (mT x) *
      cexp ((((2 * ρ + η) / c * s * vMS M S (mT x) : ℝ) : ℂ) * I +
        (((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * vMS M S (mT x) : ℝ) : ℂ))

lemma uMS_eq {Z : ℝ} (hZ : 0 < Z) {M : ℕ} (hM : 0 < M) (S m : ℕ) :
    uMS Z M S m = Real.log Z - vMS M S m := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  unfold uMS vMS; rw [Real.log_div hZ.ne' hM0.ne']; ring

/-- `u ≥ 0` for every coarse total `S ≤ 3m`. -/
lemma uMS_nonneg {x Y : ℝ} (hL : Large x) (hL2 : Large2 x) (hY1 : x ^ alpha ≤ Y)
    (hY2 : Y ≤ x ^ (alpha ^ 2)) {M : ℕ} (hM : M ∈ Mset x) {S : ℕ} (hS : S ≤ 3 * mT x) :
    0 ≤ uMS Y M S (mT x) := by
  obtain ⟨hx0, -, -, hY0⟩ := large_facts hL hY1
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.1.pos
  obtain ⟨hY1', -⟩ := logY_bounds hL hY1 hY2
  have hlM := (abs_le.mp (Mset_log hM)).2
  have hu0 := hL2.u0
  have hc3 := c_lt_third; have hl7 := ell_lt_07; have hceq := c_eq
  have hS' : (S : ℝ) ≤ 3 * mT x := by exact_mod_cast hS
  have hm0 : (0 : ℝ) ≤ mT x := Nat.cast_nonneg _
  have hl := ell_pos
  unfold uMS
  rw [Real.log_div hY0.ne' hM0.ne']
  have h1 : ell * (S : ℝ) ≤ ell * (3 * mT x) := mul_le_mul_of_nonneg_left hS' hl.le
  have h2 : (c + 3 * ell - bet) * (mT x : ℝ) ≤ 2 * mT x :=
    mul_le_mul_of_nonneg_right (by linarith) hm0
  have halpha : alpha = 1.001 := rfl
  rw [halpha] at hY1' hu0
  nlinarith

/-! ## Weighted sums over targets and coarse totals -/

/-- The weight `(3^m/M) P(S_m = S, X_m ≡ M)`. -/
def wMS (x : ℝ) (M S : ℕ) : ℝ := (3 : ℝ) ^ mT x / M * muJ (mT x) S (M : ZMod (3 ^ mT x))

lemma wMS_nonneg (x : ℝ) (M S : ℕ) : 0 ≤ wMS x M S := by
  unfold wMS; have := muJ_nonneg (mT x) S (M : ZMod (3 ^ mT x)); positivity

lemma sum_wMS_le {x : ℝ} (hL : Large x) (E : Finset ℕ) (hE : (↑E : Set ℕ) ⊆ Mset x) :
    ∑ M ∈ E, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S ≤ 5 := by
  rw [Finset.sum_comm]
  calc ∑ S ∈ Icc (mT x) (3 * mT x), ∑ M ∈ E, wMS x M S
      ≤ ∑ S ∈ Icc (mT x) (3 * mT x), 5 * lawS (mT x) S :=
        Finset.sum_le_sum fun S _ => sum_E_muJ_le hL E hE (two_m_le_n0 hL) S
    _ = 5 * ∑ S ∈ Icc (mT x) (3 * mT x), lawS (mT x) S := by rw [Finset.mul_sum]
    _ ≤ 5 * 1 := by
        gcongr
        have := (summable_lawS (mT x)).sum_le_tsum (Icc (mT x) (3 * mT x))
          (fun i _ => lawS_nonneg _ i)
        rwa [tsum_lawS] at this
    _ = 5 := by ring

open Classical in
lemma sum_wMS_err_le {x : ℝ} (hL : Large x) (E : Finset ℕ) (hE : (↑E : Set ℕ) ⊆ Mset x)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (g : ℕ → ℕ → ℝ)
    (hg : ∀ M ∈ E, ∀ S, g M S ≤ a + (if typT x (mT x) S then 0 else b)) :
    ∑ M ∈ E, ∑ S ∈ Icc (mT x) (3 * mT x), wMS x M S * g M S ≤
      5 * (a + b * chern (mT x) (Lx x ^ (0.6 : ℝ))) := by
  set m := mT x
  have hm1 : 1 ≤ m := hL.m_ge
  have hL0 : 0 < Lx x := by linarith [hL.L_ge]
  set e : ℕ → ℝ := fun S => a + (if typT x m S then 0 else b) with he
  have he0 : ∀ S, 0 ≤ e S := fun S => by simp only [he]; split_ifs <;> positivity
  calc _ ≤ ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), wMS x M S * e S :=
        Finset.sum_le_sum fun M hM => Finset.sum_le_sum fun S _ =>
          mul_le_mul_of_nonneg_left (hg M hM S) (wMS_nonneg x M S)
    _ = ∑ S ∈ Icc m (3 * m), e S * ∑ M ∈ E, wMS x M S := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun M _ => by ring
    _ ≤ ∑ S ∈ Icc m (3 * m), e S * (5 * lawS m S) :=
        Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left
          (sum_E_muJ_le hL E hE (two_m_le_n0 hL) S) (he0 S)
    _ = 5 * (a * ∑ S ∈ Icc m (3 * m), lawS m S +
          b * ∑ S ∈ Icc m (3 * m), (if typT x m S then 0 else lawS m S)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        simp only [he]; split_ifs <;> ring
    _ ≤ 5 * (a * 1 + b * chern m (Lx x ^ (0.6 : ℝ))) := by
        gcongr
        · have := (summable_lawS m).sum_le_tsum (Icc m (3 * m)) (fun i _ => lawS_nonneg m i)
          rwa [tsum_lawS] at this
        · refine le_trans ?_ (lawS_chernoff hm1 (Real.rpow_nonneg hL0.le _))
          refine le_trans ?_ ((summable_ite_lawS m (fun A : ℕ =>
            Lx x ^ (0.6 : ℝ) ≤ |(A : ℝ) - 2 * m|)).sum_le_tsum (Icc m (3 * m))
              (fun i _ => by split_ifs <;> simp [lawS_nonneg]))
          refine Finset.sum_le_sum fun S _ => ?_
          by_cases hT : typT x m S
          · rw [if_pos hT]; split_ifs <;> simp [lawS_nonneg]
          · rw [if_neg hT, if_pos]
            unfold typT at hT; push Not at hT; exact hT.le
    _ = 5 * (a + b * chern m (Lx x ^ (0.6 : ℝ))) := by ring

/-! ## `Ψ_Y(s)` is close to `K_x(s)` -/

/-- The renewal main term `(1/c) e^{-(iκs + Ds²) u}`. -/
def mainT (ρ η s u : ℝ) : ℂ :=
  (1 / c : ℂ) * cexp (-(I * (((2 * ρ + η) / c * s * u : ℝ) : ℂ)) -
    (((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u : ℝ) : ℂ))

lemma norm_mainT_le (ρ η s : ℝ) {u : ℝ} (hu : 0 ≤ u) : ‖mainT ρ η s u‖ ≤ 1 / c := by
  have hc := c_pos'
  unfold mainT
  rw [norm_mul, Complex.norm_exp, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc]
  have hre : (-(I * (((2 * ρ + η) / c * s * u : ℝ) : ℂ)) -
      (((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u : ℝ) : ℂ)).re =
      -((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u) := by
    rw [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre]
  have hnn : 0 ≤ (ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u := by positivity
  have h1 : Real.exp (-((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  calc 1 / c * Real.exp (-((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * u)) ≤ 1 / c * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 / c := mul_one _

lemma Ez_mainT {Z : ℝ} (hZ : 0 < Z) (ρ η s : ℝ) {M : ℕ} (hM : 0 < M) (S m : ℕ) :
    Ez ((ρ * bet + η * ell) ^ 2 / c ^ 3) ((2 * ρ + η) / c) Z s * mainT ρ η s (uMS Z M S m) =
      (1 / c : ℂ) * cexp ((((2 * ρ + η) / c * s * vMS M S m : ℝ) : ℂ) * I +
        (((ρ * bet + η * ell) ^ 2 / c ^ 3 * s ^ 2 * vMS M S m : ℝ) : ℂ)) := by
  unfold Ez mainT
  rw [uMS_eq hZ hM, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast; ring

open Classical in
/-- **(6.4): `Ψ_Y(s) = K_x(s) + O(·)`**, with all error terms explicit. -/
theorem renorm_close {A : Set ℕ} {q : ℕ → ℝ} {ρ η x₀ : ℝ} (htr : Transport A q ρ η x₀)
    {x Z : ℝ} (hx : x₀ ≤ x) (hL : Large x) (hL2 : Large2 x) (hZ1 : x ^ alpha ≤ Z)
    (hZ2 : Z ≤ x ^ (alpha ^ 2)) {M0 s : ℝ} (hs : |s| * √(Real.log Z) ≤ M0)
    (B CR δ : ℝ) (hδ : 0 < δ) (hCR0 : 0 ≤ CR) (hB : ∀ u, ‖renewalR ρ η s u‖ ≤ B)
    (hCR : ∀ u, 2 ≤ u → |s| * √u ≤ M0 → ‖renewalR ρ η s u - mainT ρ η s u‖ ≤ CR * u ^ (-δ)) :
    ‖renorm (oddCF A q ((2 * ρ + η) / c)) ((ρ * bet + η * ell) ^ 2 / c ^ 3) Z s -
        Kx A q ρ η x s‖ ≤
      Real.exp ((ρ * bet + η * ell) ^ 2 / c ^ 3 * M0 ^ 2) *
        (2 * (((oddClosed Z).filter (fun N => ¬ Good x N)).card : ℝ) / LY Z +
          ‖transferLHS x Z (EA A x) q ρ η s - transferRHS x Z (EA A x) q ρ η s‖ +
          20 * (CR * Lx x ^ (-(0.8 * δ)) + (B + 1 / c) * chern (mT x) (Lx x ^ (0.6 : ℝ))) +
          60 / (c * Z)) := by
  classical
  obtain ⟨hx0, h2e5, hxZ, hZ0⟩ := large_facts hL hZ1
  have hc := c_pos'
  set κ := (2 * ρ + η) / c with hκ
  set D := (ρ * bet + η * ell) ^ 2 / c ^ 3 with hD
  have hD0 : 0 ≤ D := by positivity
  set m := mT x with hm
  set L := Lx x with hLdef
  set E := EA A x with hEdef
  have hE : (↑E : Set ℕ) ⊆ Mset x := EA_sub A x
  have hEpos : ∀ M ∈ E, 0 < M := fun M hM => (hE hM).1.pos
  have hLb : (200000 : ℝ) ≤ L := hL.L_ge
  have hL0 : 0 < L := by linarith
  have hLY4 : Z / 4 ≤ (LY Z : ℝ) := by have := LY_ge hZ0.le; linarith
  have hLYpos : (0 : ℝ) < LY Z := lt_of_lt_of_le (by positivity) hLY4
  -- `log Z ≥ L`
  have hlogZ : L ≤ Real.log Z := by
    have := (logY_bounds hL hZ1 hZ2).1
    have : (1 : ℝ) ≤ alpha := by unfold alpha; norm_num
    nlinarith
  have hlogZ0 : 0 ≤ Real.log Z := by linarith
  -- the size of `e^{Ds² log Z}`
  set K0 := Real.exp (D * M0 ^ 2) with hK0
  have hK00 : 0 < K0 := Real.exp_pos _
  have hEz : ‖Ez D κ Z s‖ ≤ K0 := by
    rw [norm_Ez]
    apply Real.exp_le_exp.mpr
    have h1 : s ^ 2 * Real.log Z ≤ M0 ^ 2 := by
      have h0 : 0 ≤ |s| * √(Real.log Z) := by positivity
      have := pow_le_pow_left₀ h0 hs 2
      rwa [mul_pow, sq_abs, Real.sq_sqrt hlogZ0] at this
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  -- the right side in word–target form
  have hRHS : transferRHS x Z E q ρ η s = ((Z / LY Z : ℝ) : ℂ) *
      ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), (wMS x M S : ℂ) * phase q ρ η s M S m *
        renewalR ρ η s (uMS Z M S m) := by
    have h := LY_mul_RHS (x := x) hZ0 hLYpos.ne' E q ρ η s
    have hLYc : (LY Z : ℂ) ≠ 0 := by exact_mod_cast hLYpos.ne'
    have : transferRHS x Z E q ρ η s =
        (LY Z : ℂ)⁻¹ * ((LY Z : ℂ) * transferRHS x Z E q ρ η s) := by field_simp
    rw [this, h, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    unfold wMS
    rw [← hm]
    push_cast
    field_simp
  -- the per-(M, S) comparison
  set ch := chern m (L ^ (0.6 : ℝ)) with hch
  have hcl : (0 : ℝ) ≤ 1 / c := by positivity
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hδ8 : 0 ≤ L ^ (-(0.8 * δ)) := Real.rpow_nonneg hL0.le _
  have hR : ∀ M ∈ E, ∀ S ∈ Icc m (3 * m),
      ‖renewalR ρ η s (uMS Z M S m) - mainT ρ η s (uMS Z M S m)‖ ≤
        CR * L ^ (-(0.8 * δ)) + (if typT x m S then 0 else B + 1 / c) := by
    intro M hM S hS
    have hS3 : S ≤ 3 * m := (mem_Icc.mp hS).2
    have hu0 := uMS_nonneg hL hL2 hZ1 hZ2 (hE hM) hS3
    by_cases hT : typT x m S
    · rw [if_pos hT, add_zero]
      obtain ⟨hu1, hu2, -⟩ := u_bounds hL hL2 hZ1 hZ2 (hE hM) hT
      have h08 : 0 < L ^ (0.8 : ℝ) := Real.rpow_pos_of_pos hL0 _
      have h2 : (2 : ℝ) ≤ L ^ (0.8 : ℝ) := by
        refine le_trans ?_ hL2.xw
        rw [le_div_iff₀ hc, c_eq]
        have : ell < bet := Real.log_lt_log (by norm_num) (by norm_num)
        linarith
      have hsu : |s| * √(uMS Z M S m) ≤ M0 :=
        le_trans (by gcongr; exact hu2.trans hlogZ) hs
      refine (hCR _ (h2.trans hu1) hsu).trans ?_
      gcongr
      calc uMS Z M S m ^ (-δ) ≤ (L ^ (0.8 : ℝ)) ^ (-δ) :=
            Real.rpow_le_rpow_of_nonpos h08 hu1 (by linarith)
        _ = L ^ (-(0.8 * δ)) := by rw [← Real.rpow_mul hL0.le]; ring_nf
    · rw [if_neg hT]
      calc _ ≤ ‖renewalR ρ η s (uMS Z M S m)‖ + ‖mainT ρ η s (uMS Z M S m)‖ := norm_sub_le _ _
        _ ≤ B + 1 / c := add_le_add (hB _) (norm_mainT_le ρ η s hu0)
        _ ≤ _ := by have := mul_nonneg hCR0 hδ8; linarith
  have hpair : ∀ M ∈ E, ∀ S ∈ Icc m (3 * m),
      ‖Ez D κ Z s * ((Z / LY Z : ℝ) : ℂ) * renewalR ρ η s (uMS Z M S m) -
        (2 / c : ℂ) * cexp (((κ * s * vMS M S m : ℝ) : ℂ) * I + ((D * s ^ 2 * vMS M S m : ℝ) : ℂ))‖ ≤
      K0 * (Z / LY Z * (CR * L ^ (-(0.8 * δ)) + (if typT x m S then 0 else B + 1 / c)) +
        |Z / LY Z - 2| * (1 / c)) := by
    intro M hM S hS
    have hS3 : S ≤ 3 * m := (mem_Icc.mp hS).2
    have hu0 := uMS_nonneg hL hL2 hZ1 hZ2 (hE hM) hS3
    have hid := Ez_mainT hZ0 ρ η s (hEpos M hM) S m
    have hsplit : Ez D κ Z s * ((Z / LY Z : ℝ) : ℂ) * renewalR ρ η s (uMS Z M S m) -
        (2 / c : ℂ) * cexp (((κ * s * vMS M S m : ℝ) : ℂ) * I + ((D * s ^ 2 * vMS M S m : ℝ) : ℂ)) =
        Ez D κ Z s * (((Z / LY Z : ℝ) : ℂ) * (renewalR ρ η s (uMS Z M S m) -
          mainT ρ η s (uMS Z M S m)) + ((Z / LY Z - 2 : ℝ) : ℂ) * mainT ρ η s (uMS Z M S m)) := by
      have : (2 / c : ℂ) * cexp (((κ * s * vMS M S m : ℝ) : ℂ) * I +
          ((D * s ^ 2 * vMS M S m : ℝ) : ℂ)) = 2 * (Ez D κ Z s * mainT ρ η s (uMS Z M S m)) := by
        rw [hid]; ring
      rw [this]; push_cast; ring
    rw [hsplit, norm_mul]
    refine mul_le_mul hEz ?_ (norm_nonneg _) hK00.le
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (hR M hM S hS) (by positivity)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_mainT_le ρ η s hu0) (abs_nonneg _)
  -- the comparison of `Ez · RHS` with `K_x`
  have hKdiff : ‖Ez D κ Z s * transferRHS x Z E q ρ η s - Kx A q ρ η x s‖ ≤
      K0 * (20 * (CR * L ^ (-(0.8 * δ)) + (B + 1 / c) * ch) + 60 / (c * Z)) := by
    have hexp : Ez D κ Z s * transferRHS x Z E q ρ η s - Kx A q ρ η x s =
        ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), (wMS x M S : ℂ) * phase q ρ η s M S m *
          (Ez D κ Z s * ((Z / LY Z : ℝ) : ℂ) * renewalR ρ η s (uMS Z M S m) -
            (2 / c : ℂ) * cexp (((κ * s * vMS M S m : ℝ) : ℂ) * I +
              ((D * s ^ 2 * vMS M S m : ℝ) : ℂ))) := by
      rw [hRHS]
      unfold Kx
      rw [← hm, ← hEdef, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun M _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun S _ => ?_
      unfold wMS
      ring
    rw [hexp]
    have hYLY : |Z / LY Z - 2| ≤ 12 / Z := by
      rw [show Z / LY Z - 2 = (Z - 2 * LY Z) / LY Z by field_simp, abs_div,
        abs_of_pos hLYpos, div_le_div_iff₀ hLYpos hZ0]
      have := Y_sub_LY hZ0.le
      nlinarith [abs_nonneg (Z - 2 * LY Z)]
    have hYLY4 : Z / LY Z ≤ 4 := by rw [div_le_iff₀ hLYpos]; linarith
    have hsum1 := sum_wMS_err_le hL E hE (mul_nonneg hCR0 hδ8) (show 0 ≤ B + 1 / c by positivity)
      (fun M S => CR * L ^ (-(0.8 * δ)) + (if typT x m S then 0 else B + 1 / c))
      (fun M _ S => le_rfl)
    have hsum2 := sum_wMS_le hL E hE
    calc _ ≤ ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), wMS x M S *
          (K0 * (Z / LY Z * (CR * L ^ (-(0.8 * δ)) + (if typT x m S then 0 else B + 1 / c)) +
            |Z / LY Z - 2| * (1 / c))) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun M hM =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun S hS => ?_))
          rw [norm_mul, norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (wMS_nonneg x M S)]
          exact mul_le_mul_of_nonneg_left (hpair M hM S hS) (wMS_nonneg x M S)
      _ = K0 * (Z / LY Z * ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), wMS x M S *
            (CR * L ^ (-(0.8 * δ)) + (if typT x m S then 0 else B + 1 / c)) +
          |Z / LY Z - 2| * (1 / c) * ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), wMS x M S) := by
          simp only [Finset.mul_sum]
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun M _ => ?_
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun S _ => ?_
          ring
      _ ≤ K0 * (4 * (5 * (CR * L ^ (-(0.8 * δ)) + (B + 1 / c) * ch)) + 12 / Z * (1 / c) * 5) := by
          gcongr
          all_goals first
            | exact Finset.sum_nonneg fun M _ => Finset.sum_nonneg fun S _ => wMS_nonneg x M S
            | exact Finset.sum_nonneg fun M _ => Finset.sum_nonneg fun S _ =>
                mul_nonneg (wMS_nonneg x M S) (by split_ifs <;> positivity)
      _ = K0 * (20 * (CR * L ^ (-(0.8 * δ)) + (B + 1 / c) * ch) + 60 / (c * Z)) := by
          field_simp; ring
  -- assemble
  have hphi := phi0_close htr hx hL hZ1 hZ2 s
  rw [← hEdef] at hphi
  have hdec : renorm (oddCF A q κ) D Z s - Kx A q ρ η x s =
      Ez D κ Z s * (phi0 A q Z s - transferLHS x Z E q ρ η s) +
      Ez D κ Z s * (transferLHS x Z E q ρ η s - transferRHS x Z E q ρ η s) +
      (Ez D κ Z s * transferRHS x Z E q ρ η s - Kx A q ρ η x s) := by
    rw [renorm_eq]; ring
  rw [hdec]
  calc _ ≤ ‖Ez D κ Z s * (phi0 A q Z s - transferLHS x Z E q ρ η s)‖ +
        ‖Ez D κ Z s * (transferLHS x Z E q ρ η s - transferRHS x Z E q ρ η s)‖ +
        ‖Ez D κ Z s * transferRHS x Z E q ρ η s - Kx A q ρ η x s‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ K0 * (2 * (((oddClosed Z).filter (fun N => ¬ Good x N)).card : ℝ) / LY Z) +
        K0 * ‖transferLHS x Z E q ρ η s - transferRHS x Z E q ρ η s‖ +
        K0 * (20 * (CR * L ^ (-(0.8 * δ)) + (B + 1 / c) * ch) + 60 / (c * Z)) := by
        gcongr
        · rw [norm_mul]; exact mul_le_mul hEz hphi (norm_nonneg _) hK00.le
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_right hEz (norm_nonneg _)
    _ = _ := by ring

/-! ## Lemma 6.1 -/

open Classical in
/-- **Lemma 6.1 [`lem:adjacent`], uniform form.** For fixed rewards `(ρ, η)`: `δ`, `C` and `x₁` do
not depend on the set `A`, the clock `q` or the transport threshold `x₀`; the threshold enters only
through the range `Y ≥ max(x₁, x₀)^α`. -/
theorem adjacent_uniform (hJM : JointMixing) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (ρ η : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M0 : ℝ, 0 < M0 → ∃ C x₁ : ℝ, 0 ≤ C ∧ 1 < x₁ ∧
      ∀ (A : Set ℕ) (q : ℕ → ℝ) (x₀ : ℝ), Transport A q ρ η x₀ →
      ∀ Y Y' s : ℝ, (max x₁ x₀) ^ alpha ≤ Y → Y ≤ Y' → Y' ≤ Y ^ alpha →
        |s| * √(Real.log Y') ≤ M0 →
        ‖renorm (oddCF A q ((2 * ρ + η) / c)) ((ρ * bet + η * ell) ^ 2 / c ^ 3) Y s -
          renorm (oddCF A q ((2 * ρ + η) / c)) ((ρ * bet + η * ell) ^ 2 / c ^ 3) Y' s‖ ≤
          C * (Real.log Y) ^ (-δ) := by
  obtain ⟨δ, hδ, hR⟩ := twisted_renewal ϰ
  set δ₀ := min (0.8 * δ) 1 with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (by positivity) one_pos
  refine ⟨δ₀, hδ₀0, fun M0 hM0 => ?_⟩
  obtain ⟨CR, hCR⟩ := hR d hθ ρ η M0
  set CR' := max CR 0 with hCR'
  have hCR0 : 0 ≤ CR' := le_max_right _ _
  obtain ⟨BR, hBR⟩ := renewalR_bounded
  set B := max BR 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  obtain ⟨CT, xT, hT⟩ := transfer hJM ρ η 1 one_pos
  have hc := c_pos'
  set D := (ρ * bet + η * ell) ^ 2 / c ^ 3 with hD
  set K0 := Real.exp (D * M0 ^ 2) with hK0
  have hK00 : 0 < K0 := Real.exp_pos _
  set C1 := 2 + |CT| + 20 * CR' + 40 * (B + 1 / c) + 60 / c with hC1
  have hC10 : 0 ≤ C1 := by positivity
  have f1 := ev_of_log (ev_pow_mul_exp_le 0 1 (k := 1 / 2) (b := 0.2) (by norm_num) (by norm_num))
  have hev := large_ev.and (large2_ev.and ((typical 1).and (f1.and
    ((eventually_ge_atTop xT).and (eventually_ge_atTop 1)))))
  obtain ⟨xt, hxt⟩ := eventually_atTop.mp hev
  -- the estimate at one threshold, for every set and clock with the transport property; the
  -- transport threshold `x₀` enters only through the hypothesis `x₀ ≤ x`
  have hone : ∀ (A : Set ℕ) (q : ℕ → ℝ) (x₀ : ℝ), Transport A q ρ η x₀ →
      ∀ x Z s : ℝ, max xt 1 ≤ x → x₀ ≤ x → x ^ alpha ≤ Z → Z ≤ x ^ (alpha ^ 2) →
      |s| * √(Real.log Z) ≤ M0 →
      ‖renorm (oddCF A q ((2 * ρ + η) / c)) D Z s - Kx A q ρ η x s‖ ≤
        K0 * C1 * Lx x ^ (-δ₀) := by
    intro A q x₀ htr x Z s hx hx0' hZ1 hZ2 hs
    obtain ⟨hL, hL2, htyp, g1, hx1, -⟩ := hxt x (le_trans (le_max_left _ _) hx)
    obtain ⟨hx0, h2e5, hxZ, hZ0⟩ := large_facts hL hZ1
    have hBs : ∀ u, ‖renewalR ρ η s u‖ ≤ B := fun u => (hBR ρ η s u).trans (le_max_left _ _)
    have hCRs : ∀ u, 2 ≤ u → |s| * √u ≤ M0 →
        ‖renewalR ρ η s u - mainT ρ η s u‖ ≤ CR' * u ^ (-δ) := fun u hu hsu =>
      (hCR u s hu hsu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by linarith) _))
    have hmain := renorm_close htr hx0' hL hL2 hZ1 hZ2 hs B CR' δ hδ hCR0 hBs hCRs
    refine hmain.trans ?_
    set L := Lx x with hLdef
    have hLb : (200000 : ℝ) ≤ L := hL.L_ge
    have hL0 : 0 < L := by linarith
    have hL1 : 1 ≤ L := by linarith
    have hp1 : L ^ (-(1 : ℝ)) ≤ L ^ (-δ₀) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [min_le_right (0.8 * δ) 1])
    have hp2 : L ^ (-(0.8 * δ)) ≤ L ^ (-δ₀) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [min_le_left (0.8 * δ) 1])
    have hLinv : L ^ (-(1 : ℝ)) = 1 / L := by rw [Real.rpow_neg_one, one_div]
    have hp10 : 0 ≤ L ^ (-(1 : ℝ)) := Real.rpow_nonneg hL0.le _
    have hp0 : 0 ≤ L ^ (-δ₀) := Real.rpow_nonneg hL0.le _
    have hLY4 : Z / 4 ≤ (LY Z : ℝ) := by have := LY_ge hZ0.le; linarith
    have hLYpos : (0 : ℝ) < LY Z := lt_of_lt_of_le (by positivity) hLY4
    -- the four error terms
    have e1 : 2 * (((oddClosed Z).filter (fun N => ¬ Good x N)).card : ℝ) / LY Z ≤
        2 * L ^ (-δ₀) := by
      have := htyp Z hZ1
      rw [div_le_iff₀ hLYpos]
      have h1 : L ^ (-(1 : ℝ)) * LY Z ≤ L ^ (-δ₀) * LY Z :=
        mul_le_mul_of_nonneg_right hp1 hLYpos.le
      have h2 : Lx x ^ (-(1 : ℝ)) = L ^ (-(1 : ℝ)) := rfl
      rw [h2] at this
      linarith
    have e2 : ‖transferLHS x Z (EA A x) q ρ η s - transferRHS x Z (EA A x) q ρ η s‖ ≤
        |CT| * L ^ (-δ₀) :=
      (hT x Z hx1 hZ1 hZ2 (EA A x) (EA_sub A x) q s).trans
        (mul_le_mul (le_abs_self _) hp1 hp10 (abs_nonneg _))
    have hch : chern (mT x) (L ^ (0.6 : ℝ)) ≤ 2 * L ^ (-δ₀) := by
      have hmn : (mT x : ℝ) ≤ n0 x := by exact_mod_cast (show mT x ≤ n0 x by
        have := two_m_le_n0 hL; omega)
      have h6 := hL2.n6
      rw [← hLdef] at h6
      refine (chern_L06_le hL0 hL2.l04 hL.m_ge (by linarith)).trans ?_
      rw [Real.rpow_zero, one_mul] at g1
      have : Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))) ≤ L ^ (-(1 : ℝ)) := g1
      linarith
    have hZL : L ≤ Z := by
      have h := Real.add_one_le_exp (Real.log x)
      rw [Real.exp_log hx0] at h
      have : L = Real.log x := rfl
      linarith
    have e4 : 60 / (c * Z) ≤ 60 / c * L ^ (-δ₀) := by
      calc 60 / (c * Z) ≤ 60 / (c * L) := by gcongr
        _ = 60 / c * L ^ (-(1 : ℝ)) := by rw [hLinv]; field_simp
        _ ≤ 60 / c * L ^ (-δ₀) := by gcongr
    have hcl : 0 ≤ 1 / c := by positivity
    calc K0 * (2 * (((oddClosed Z).filter (fun N => ¬ Good x N)).card : ℝ) / LY Z +
          ‖transferLHS x Z (EA A x) q ρ η s - transferRHS x Z (EA A x) q ρ η s‖ +
          20 * (CR' * L ^ (-(0.8 * δ)) + (B + 1 / c) * chern (mT x) (L ^ (0.6 : ℝ))) +
          60 / (c * Z))
        ≤ K0 * (2 * L ^ (-δ₀) + |CT| * L ^ (-δ₀) +
          20 * (CR' * L ^ (-δ₀) + (B + 1 / c) * (2 * L ^ (-δ₀))) + 60 / c * L ^ (-δ₀)) := by
          gcongr
      _ = K0 * C1 * L ^ (-δ₀) := by rw [hC1]; ring
  -- choose `x = Y^{1/α}`
  have hα : (1 : ℝ) < alpha := by unfold alpha; norm_num
  have hα0 : (0 : ℝ) < alpha := by linarith
  refine ⟨2 * K0 * C1 * alpha, max (max xt 1) 2, by positivity,
    lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro A q x₀ htr Y Y' s hY hYY' hY'Y hs
  set mx := max (max (max xt 1) 2) x₀ with hmx
  have hmx2 : 2 ≤ mx := le_trans (le_max_right _ _) (le_max_left _ _)
  have hmx0 : 0 < mx := by linarith
  have hmxY : mx ≤ Y := le_trans (Real.self_le_rpow_of_one_le (by linarith) hα.le) hY
  have hY2 : 2 ≤ Y := le_trans hmx2 hmxY
  have hY0 : 0 < Y := by linarith
  set x := Y ^ alpha⁻¹ with hxdef
  have hx0 : 0 < x := Real.rpow_pos_of_pos hY0 _
  have hxα : x ^ alpha = Y := Real.rpow_inv_rpow hY0.le hα0.ne'
  have hmxx : mx ≤ x := by
    have h2 := Real.rpow_le_rpow (by positivity) hY (inv_nonneg.mpr hα0.le)
    rwa [← Real.rpow_mul hmx0.le, mul_inv_cancel₀ hα0.ne', Real.rpow_one] at h2
  have hxt' : max xt 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hmxx
  have hx0' : x₀ ≤ x := le_trans (le_max_right _ _) hmxx
  have hxα2 : x ^ (alpha ^ 2) = Y ^ alpha := by
    rw [sq, Real.rpow_mul hx0.le, hxα]
  have hlogYY' : Real.log Y ≤ Real.log Y' := Real.log_le_log hY0 hYY'
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hsY : |s| * √(Real.log Y) ≤ M0 :=
    le_trans (by gcongr) hs
  have hYa : Y ≤ Y ^ alpha := Real.self_le_rpow_of_one_le (by linarith) hα.le
  have h1 := hone A q x₀ htr x Y s hxt' hx0' hxα.le (hxα2 ▸ hYa) hsY
  have h2 := hone A q x₀ htr x Y' s hxt' hx0' (hxα.le.trans hYY') (hxα2 ▸ hY'Y) hs
  have hLx : Lx x = Real.log Y / alpha := by
    unfold Lx; rw [hxdef, Real.log_rpow hY0]; field_simp
  have hLpos : 0 < Real.log Y := Real.log_pos (by linarith)
  have hpow : Lx x ^ (-δ₀) ≤ alpha * Real.log Y ^ (-δ₀) := by
    rw [hLx, Real.div_rpow hLpos.le hα0.le, Real.rpow_neg hα0.le, div_inv_eq_mul, mul_comm]
    gcongr
    calc alpha ^ δ₀ ≤ alpha ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hα.le (min_le_right _ _)
      _ = alpha := Real.rpow_one _
  calc ‖renorm (oddCF A q ((2 * ρ + η) / c)) D Y s -
        renorm (oddCF A q ((2 * ρ + η) / c)) D Y' s‖
      ≤ ‖renorm (oddCF A q ((2 * ρ + η) / c)) D Y s - Kx A q ρ η x s‖ +
        ‖renorm (oddCF A q ((2 * ρ + η) / c)) D Y' s - Kx A q ρ η x s‖ := by
        rw [← norm_neg (renorm _ D Y' s - _)]
        refine le_trans (le_of_eq ?_) (norm_add_le _ _)
        congr 1; ring
    _ ≤ K0 * C1 * Lx x ^ (-δ₀) + K0 * C1 * Lx x ^ (-δ₀) := add_le_add h1 h2
    _ = 2 * K0 * C1 * Lx x ^ (-δ₀) := by ring
    _ ≤ 2 * K0 * C1 * (alpha * Real.log Y ^ (-δ₀)) := by gcongr
    _ = 2 * K0 * C1 * alpha * Real.log Y ^ (-δ₀) := by ring

open Classical in
/-- **Lemma 6.1 (adjacent scales)** for any set and clock with the transport property, with
`κ = (2ρ+η)/c` and `D = (ρβ+ηℓ)²/c³`. It is the uniform form `adjacent_uniform` specialised to one
set and clock, with `Y₀ = max(x₁, x₀)^α`; the choice `x = Y^{1/α}`, under which `Y` and `Y'` share
`K_x(s)`, is made there. -/
theorem adjacent_of_transport (hJM : JointMixing) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {A : Set ℕ} {q : ℕ → ℝ} {ρ η x₀ : ℝ} (htr : Transport A q ρ η x₀) :
    AdjacentScales (oddCF A q ((2 * ρ + η) / c)) ((ρ * bet + η * ell) ^ 2 / c ^ 3) alpha := by
  obtain ⟨δ, hδ, hU⟩ := adjacent_uniform hJM hθ ρ η
  refine ⟨δ, hδ, fun M0 hM0 => ?_⟩
  obtain ⟨C, x₁, hC, hx₁, h⟩ := hU M0 hM0
  exact ⟨C, hC, (max x₁ x₀) ^ alpha,
    Real.one_lt_rpow (lt_of_lt_of_le hx₁ (le_max_left _ _)) (by unfold alpha; norm_num),
    h A q x₀ htr⟩

end CollatzCLT
