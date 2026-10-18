import LeanClt.Applications.PinnedTransfer
import LeanClt.Applications.Coordinates
import LeanClt.Exceptional.Laws
import LeanClt.Main.Conditional

/-!
# Theorem 6.10 [`thm:anticonc`]: anti-concentration (stage 4 of the checkpoint-20 plan)

From Tao's two imports only (`TaoMajorant`, `TaoPrefix`); no Diophantine input.

* **The sampling conversion** (`levelCount_le_explicit`, `levelCount_le_of_odd_dyadic`). An odd dyadic
  bound `#{u ∈ odd ∩ [Y, 2Y] : u ∈ A, g(u) = j} ≤ C #(odd ∩ [Y, 2Y])/√(log Y)`, uniform in `j`,
  becomes the bound `#{n ≤ X : n ∈ A, g(n) = j} ≤ (4C + 1) X/√(log X)` for a clock that moves by a
  constant under doubling. Write `n = 2^e u` with `u` odd. The `n` with `u ≤ √X` (which include the
  finitely many odd parts below the doubling threshold, such as the halving string through an even
  target `b`) number at most `(log₂ X + 1)√X`. For `u > √X` the doubling property gives `u ∈ A` and
  `g(u) = j + eδ`, a level of `g` (an initial halving string shifts the level by `e`, which the
  supremum over levels absorbs), and `u` lies in one of the dyadic blocks `[W/2^{k+1}, W/2^k]`,
  `W = ⌊X/2^e⌋`, each at scale at least `√X/4`. The blocks of all layers `e` have total length at
  most `2X`.
* **Theorem 6.10** (`anticonc`). The conversion is applied to `anticonc_odd_dyadic` for `P_T(b)` and
  `P_F(b)` (transport and doubling of §6.5), for `P_U(b)` (odd sources: only the layer `e = 0`), for
  the two coordinates of a divergent class (`transport_coordT`, `transport_coordF`, threshold-free,
  which is why `X₀` is absolute in (ii) and (iii)), and for the class-dependent clock on a finite
  union of classes, pinned at level 0 (`levelCount_classClock`). The closing sentence uses
  `#(S ∩ [1, X]) ≥ pX/2` for large `X`, with the same `C₀`.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-- `#{n ≤ X : n ∈ S, f(n) = j}`: the level set of an integer clock or spatial coordinate `f`
on `S`, counted in `[1, X]`. -/
def levelCount (S : Set ℕ) (f : ℕ → ℤ) (j : ℤ) (X : ℕ) : ℕ :=
  ((window S X).filter (fun n => f n = j)).card

/-! ## Elementary counting -/

/-- `#(odd ∩ [Y, 2Y]) ≤ Y + 1`. -/
lemma card_oddClosed_le {Y : ℝ} (hY : 0 ≤ Y) : ((oddClosed Y).card : ℝ) ≤ Y + 1 := by
  classical
  have h1 : (oddClosed Y).card ≤ ⌊2 * Y⌋₊ + 1 - ⌈Y⌉₊ := by
    unfold oddClosed
    exact (card_filter_le _ _).trans (by rw [Nat.card_Icc])
  have hf : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
  have hc : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
  by_cases h : ⌈Y⌉₊ ≤ ⌊2 * Y⌋₊ + 1
  · have h2 : ((oddClosed Y).card : ℝ) ≤ ((⌊2 * Y⌋₊ + 1 - ⌈Y⌉₊ : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_one] at h2
    linarith
  · have h0 : (oddClosed Y).card = 0 := by omega
    rw [h0, Nat.cast_zero]
    linarith

/-- A level set on a smaller set is smaller. -/
lemma levelCount_mono {S S' : Set ℕ} (h : S ⊆ S') (f : ℕ → ℤ) (j : ℤ) (X : ℕ) :
    levelCount S f j X ≤ levelCount S' f j X := by
  unfold levelCount
  exact card_le_card (monotone_filter_left _ (window_mono h X))

open Classical in
/-- **The sampling conversion, explicit form.** If the clock `g` on `A` drops by `eδ` from `u` to
`2^e u` for odd `u ≥ n₀`, and the odd dyadic level sets at scales `Y ≥ Y₀` are bounded by
`C #(odd ∩ [Y, 2Y])/√(log Y)`, then for every cutoff `V ≥ max(n₀, 2Y₀)`, with `E = ⌊log₂ X⌋`,
`#{n ≤ X : n ∈ A, g(n) = j} ≤ (E + 1)V + (C/√(log Y₀))(2X + (E + 1)²)`. -/
lemma levelCount_le_explicit {A : Set ℕ} {g : ℕ → ℤ} {δ : ℤ} {n0 V X : ℕ} {C Y₀ : ℝ}
    (hC : 0 ≤ C) (hY₀ : 1 < Y₀) (hV : 2 * Y₀ ≤ V) (hn0 : n0 ≤ V)
    (hdbl : ∀ e u : ℕ, n0 ≤ u → Odd u → 2 ^ e * u ∈ A → u ∈ A ∧ g (2 ^ e * u) = g u - e * δ)
    (hodd : ∀ Y : ℝ, Y₀ ≤ Y → ∀ j : ℤ,
      (((oddClosed Y).filter (fun n => n ∈ A ∧ g n = j)).card : ℝ) ≤
        C * (oddClosed Y).card / √(Real.log Y))
    (j : ℤ) :
    (levelCount A g j X : ℝ) ≤
      (Nat.log 2 X + 1) * V + C / √(Real.log Y₀) * (2 * X + (Nat.log 2 X + 1) ^ 2) := by
  set E := Nat.log 2 X with hE
  set D := C / √(Real.log Y₀) with hD
  have hlogY₀ : 0 < Real.log Y₀ := Real.log_pos hY₀
  have hsq0 : 0 < √(Real.log Y₀) := Real.sqrt_pos.mpr hlogY₀
  have hD0 : 0 ≤ D := div_nonneg hC hsq0.le
  -- the dyadic blocks `[W/2^{k+1}, W/2^k]`, `W = ⌊X/2^e⌋`, and the small odd parts
  set Yb : ℕ → ℕ → ℝ := fun e k => ((X / 2 ^ e : ℕ) : ℝ) / 2 ^ (k + 1) with hYb
  set blk : ℕ × ℕ → Finset ℕ := fun p =>
    ((oddClosed (Yb p.1 p.2)).filter (fun u => V < u ∧ u ∈ A ∧ g u = j + p.1 * δ)).image
      (fun u => 2 ^ p.1 * u) with hblk
  set small : Finset ℕ := ((range (E + 1)) ×ˢ (Icc 1 V)).image (fun p => 2 ^ p.1 * p.2)
    with hsmall
  have hsub : (window A X).filter (fun n => g n = j) ⊆
      small ∪ (range (E + 1) ×ˢ range (E + 1)).biUnion blk := by
    intro n hn
    rw [mem_filter, mem_window] at hn
    obtain ⟨⟨⟨hn1, hnX⟩, hnA⟩, hgn⟩ := hn
    obtain ⟨e, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
    have hu0 : 0 < u := hu.pos
    have h2e : 0 < 2 ^ e := by positivity
    have he : e ≤ E := Nat.le_log_of_pow_le (by norm_num)
      ((Nat.le_mul_of_pos_right _ hu0).trans hnX)
    by_cases hsm : u ≤ V
    · refine mem_union_left _ (mem_image.mpr ⟨(e, u), ?_, rfl⟩)
      rw [mem_product, mem_range, mem_Icc]
      exact ⟨by omega, hu0, hsm⟩
    · push Not at hsm
      obtain ⟨huA, hgu⟩ := hdbl e u (hn0.trans hsm.le) hu hnA
      set W := X / 2 ^ e with hW
      have huW : u ≤ W := (Nat.le_div_iff_mul_le h2e).mpr (by rw [mul_comm]; exact hnX)
      have hWu : W / u ≠ 0 := (Nat.div_pos huW hu0).ne'
      set k := Nat.log 2 (W / u) with hk
      have hk1 : 2 ^ k * u ≤ W :=
        (Nat.le_div_iff_mul_le hu0).mp (Nat.pow_log_le_self 2 hWu)
      have hk2 : W < 2 ^ (k + 1) * u :=
        (Nat.div_lt_iff_lt_mul hu0).mp (Nat.lt_pow_succ_log_self (by norm_num) _)
      have hkE : k ≤ E := Nat.log_mono_right ((Nat.div_le_self _ _).trans (Nat.div_le_self _ _))
      refine mem_union_right _ (mem_biUnion.mpr ⟨(e, k), ?_, mem_image.mpr ⟨u, ?_, rfl⟩⟩)
      · rw [mem_product, mem_range, mem_range]
        omega
      · have hgu' : g u = j + e * δ := by linarith
        refine mem_filter.mpr ⟨?_, hsm, huA, hgu'⟩
        have hYk : Yb e k = (W : ℝ) / 2 ^ (k + 1) := rfl
        have h2Yk : 2 * Yb e k = (W : ℝ) / 2 ^ k := by
          rw [hYk, pow_succ]
          field_simp
        unfold oddClosed
        rw [mem_filter, mem_Icc]
        refine ⟨⟨Nat.ceil_le.mpr ?_, (Nat.le_floor_iff (by positivity)).mpr ?_⟩, hu⟩
        · rw [hYk, div_le_iff₀ (by positivity)]
          exact_mod_cast (show W ≤ u * 2 ^ (k + 1) by rw [mul_comm]; exact hk2.le)
        · rw [h2Yk, le_div_iff₀ (by positivity)]
          exact_mod_cast (show u * 2 ^ k ≤ W by rw [mul_comm]; exact hk1)
  -- the count of each block
  have hblock : ∀ e k : ℕ, (((oddClosed (Yb e k)).filter
      (fun u => V < u ∧ u ∈ A ∧ g u = j + e * δ)).card : ℝ) ≤ D * (Yb e k + 1) := by
    intro e k
    have hY0 : 0 ≤ Yb e k := by positivity
    by_cases hbig : Y₀ ≤ Yb e k
    · have h1 : ((oddClosed (Yb e k)).filter (fun u => V < u ∧ u ∈ A ∧ g u = j + e * δ)).card ≤
          ((oddClosed (Yb e k)).filter (fun u => u ∈ A ∧ g u = j + e * δ)).card := by
        refine card_le_card fun u hu => ?_
        rw [mem_filter] at hu ⊢
        exact ⟨hu.1, hu.2.2⟩
      have h2 := hodd _ hbig (j + e * δ)
      have hsq : √(Real.log Y₀) ≤ √(Real.log (Yb e k)) :=
        Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hbig)
      have h3 : C * (oddClosed (Yb e k)).card / √(Real.log (Yb e k)) ≤ D * (Yb e k + 1) := by
        rw [hD, div_mul_eq_mul_div]
        calc C * (oddClosed (Yb e k)).card / √(Real.log (Yb e k))
            ≤ C * (oddClosed (Yb e k)).card / √(Real.log Y₀) :=
              div_le_div_of_nonneg_left (by positivity) hsq0 hsq
          _ ≤ C * (Yb e k + 1) / √(Real.log Y₀) := by
              gcongr
              exact card_oddClosed_le hY0
      calc _ ≤ (((oddClosed (Yb e k)).filter (fun u => u ∈ A ∧ g u = j + e * δ)).card : ℝ) := by
            exact_mod_cast h1
        _ ≤ _ := h2
        _ ≤ _ := h3
    · push Not at hbig
      have hempty : (oddClosed (Yb e k)).filter
          (fun u => V < u ∧ u ∈ A ∧ g u = j + e * δ) = ∅ := by
        rw [filter_eq_empty_iff]
        intro u hu hP
        unfold oddClosed at hu
        rw [mem_filter, mem_Icc] at hu
        have h1 : (u : ℝ) ≤ 2 * Yb e k := (Nat.le_floor_iff (by positivity)).mp hu.1.2
        have h2 : (V : ℝ) < u := by exact_mod_cast hP.1
        linarith
      rw [hempty, card_empty, Nat.cast_zero]
      positivity
  -- the geometric sums
  have hsumk : ∀ e : ℕ, ∑ k ∈ range (E + 1), (Yb e k + 1) ≤ (X : ℝ) * (1 / 2) ^ e + (E + 1) := by
    intro e
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    have hY : ∑ k ∈ range (E + 1), Yb e k =
        ((X / 2 ^ e : ℕ) : ℝ) / 2 * ∑ k ∈ range (E + 1), (1 / 2 : ℝ) ^ k := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      simp only [hYb, one_div, inv_pow, pow_succ]
      ring
    have hW : ((X / 2 ^ e : ℕ) : ℝ) ≤ (X : ℝ) * (1 / 2) ^ e := by
      have := Nat.cast_div_le (α := ℝ) (m := X) (n := 2 ^ e)
      rw [Nat.cast_pow, Nat.cast_ofNat] at this
      rw [one_div, inv_pow, ← div_eq_mul_inv]
      exact this
    have hg := sum_geometric_two_le (E + 1)
    have hW0 : 0 ≤ ((X / 2 ^ e : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith
  have hsum : ∑ p ∈ range (E + 1) ×ˢ range (E + 1), (((oddClosed (Yb p.1 p.2)).filter
      (fun u => V < u ∧ u ∈ A ∧ g u = j + p.1 * δ)).card : ℝ) ≤
      D * (2 * X + (E + 1) ^ 2) := by
    calc _ ≤ ∑ p ∈ range (E + 1) ×ˢ range (E + 1), D * (Yb p.1 p.2 + 1) :=
          sum_le_sum fun p _ => hblock p.1 p.2
      _ = D * ∑ e ∈ range (E + 1), ∑ k ∈ range (E + 1), (Yb e k + 1) := by
          rw [← mul_sum, sum_product]
      _ ≤ D * ∑ e ∈ range (E + 1), ((X : ℝ) * (1 / 2) ^ e + (E + 1)) := by
          gcongr with e
          exact hsumk e
      _ ≤ D * (2 * X + (E + 1) ^ 2) := by
          gcongr
          rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
          have hg := sum_geometric_two_le (E + 1)
          have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
          push_cast
          nlinarith
  -- assembling
  have hsmallc : (small.card : ℝ) ≤ (E + 1) * V := by
    have : small.card ≤ (E + 1) * V := by
      refine card_image_le.trans ?_
      rw [card_product, card_range, Nat.card_Icc, Nat.add_sub_cancel]
    exact_mod_cast this
  have hcard : (levelCount A g j X : ℝ) ≤ small.card + ∑ p ∈ range (E + 1) ×ˢ range (E + 1),
      (((oddClosed (Yb p.1 p.2)).filter (fun u => V < u ∧ u ∈ A ∧ g u = j + p.1 * δ)).card : ℝ) := by
    have h1 : levelCount A g j X ≤ small.card + ∑ p ∈ range (E + 1) ×ˢ range (E + 1),
        ((oddClosed (Yb p.1 p.2)).filter (fun u => V < u ∧ u ∈ A ∧ g u = j + p.1 * δ)).card := by
      unfold levelCount
      refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
      gcongr
      exact card_biUnion_le.trans (sum_le_sum fun p _ => card_image_le)
    exact_mod_cast h1
  linarith

/-- `(log x)² ≤ c √x` for all large `x`, for every `c > 0`. -/
lemma eventually_log_sq_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ c * √x := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop (s := 1 / 2) 2 (by norm_num)).bound hc,
    eventually_ge_atTop 1] with x hx hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.rpow_two,
    ← Real.sqrt_eq_rpow] at hx
  exact hx

open Classical in
/-- **The sampling conversion** (proof of Theorem 6.10 [`thm:anticonc`]): from an odd dyadic bound
of the form of `anticonc_odd_dyadic` at scales `Y ≥ Y₁`, uniform in the level, to the bound
`#{n ≤ X : n ∈ A, g(n) = j} ≤ (4C + 1)X/√(log X)` on `[1, X]`, for a clock that drops by `eδ` from
`u` to `2^e u` for odd `u ≥ n₀`. The threshold `X₁` depends only on `C`, `Y₁` and `n₀`. -/
theorem levelCount_le_of_odd_dyadic (C Y₁ : ℝ) (n0 : ℕ) (hC : 0 ≤ C) :
    ∃ X₁ : ℝ, ∀ (A : Set ℕ) (g : ℕ → ℤ) (δ : ℤ),
      (∀ e u : ℕ, n0 ≤ u → Odd u → 2 ^ e * u ∈ A → u ∈ A ∧ g (2 ^ e * u) = g u - e * δ) →
      (∀ Y : ℝ, Y₁ ≤ Y → ∀ j : ℤ,
        (((oddClosed Y).filter (fun n => n ∈ A ∧ g n = j)).card : ℝ) ≤
          C * (oddClosed Y).card / √(Real.log Y)) →
      ∀ X : ℕ, X₁ ≤ X → ∀ j : ℤ,
        (levelCount A g j X : ℝ) ≤ (4 * C + 1) * X / √(Real.log X) := by
  set c : ℝ := 1 / (3 + 18 * C) with hc
  have hc0 : 0 < c := by positivity
  set R : ℝ := 4 * max Y₁ 2 + 2 * n0 + 4 with hR
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    ((eventually_log_sq_le c hc0).and (eventually_ge_atTop (max 256 (R ^ 2))))
  refine ⟨X₁, fun A g δ hdbl hodd X hX j => ?_⟩
  obtain ⟨hlog2, hXbig⟩ := hX₁ X hX
  have hX256 : (256 : ℝ) ≤ X := le_trans (le_max_left _ _) hXbig
  have hXR : R ^ 2 ≤ (X : ℝ) := le_trans (le_max_right _ _) hXbig
  have hX0 : (0 : ℝ) < X := by linarith
  have hXn : 0 < X := by exact_mod_cast hX0
  -- the cutoff `V = ⌊√X⌋`, with `√X/2 < V ≤ √X`
  set V := Nat.sqrt X with hV
  have hVle : (V : ℝ) ≤ √X := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) hX0.le]
    exact_mod_cast Nat.sqrt_le' X
  have hV1 : 1 ≤ V := Nat.sqrt_pos.mpr hXn
  have hVgt : √X < 2 * V := by
    rw [Real.sqrt_lt' (by positivity)]
    have h1 : X < (V + 1) ^ 2 := Nat.lt_succ_sqrt' X
    have h2 : (V + 1) ^ 2 ≤ (2 * V) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    exact_mod_cast h1.trans_le h2
  have hR0 : 0 ≤ R := by positivity
  have hRs : R ≤ √X := by
    rw [Real.le_sqrt hR0 hX0.le]
    exact hXR
  have hmax : Y₁ ≤ max Y₁ 2 := le_max_left _ _
  have hmax2 : (2 : ℝ) ≤ max Y₁ 2 := le_max_right _ _
  set Y₀ : ℝ := (V : ℝ) / 2 with hY₀
  have hY₀1 : 1 < Y₀ := by
    have : (n0 : ℝ) ≥ 0 := Nat.cast_nonneg _
    rw [hY₀]
    linarith
  have hY₁ : Y₁ ≤ Y₀ := by
    have : (n0 : ℝ) ≥ 0 := Nat.cast_nonneg _
    rw [hY₀]
    linarith
  have hn0V : n0 ≤ V := by
    have : (n0 : ℝ) ≤ V := by
      have : 0 ≤ max Y₁ 2 := by linarith
      linarith
    exact_mod_cast this
  have hV2 : 2 * Y₀ ≤ V := by rw [hY₀]; linarith
  have hexp := levelCount_le_explicit hC hY₀1 hV2 hn0V hdbl
    (fun Y hY j => hodd Y (hY₁.trans hY) j) (X := X) j
  -- `L = log X`
  set L := Real.log X with hL
  have hlog2v : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hL256 : 4 * Real.log 4 ≤ L := by
    have h1 : Real.log 256 ≤ L := Real.log_le_log (by norm_num) hX256
    have h2 : Real.log 256 = 4 * Real.log 4 := by
      rw [show (256 : ℝ) = 4 ^ 4 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hsqL0 : 0 < √L := Real.sqrt_pos.mpr hL0
  -- `log Y₀ ≥ L/4`, so `C/√(log Y₀) ≤ 2C/√L`
  have hlogY₀ : L / 4 ≤ Real.log Y₀ := by
    have hs0 : 0 < √(X : ℝ) := Real.sqrt_pos.mpr hX0
    have h1 : Real.log (√X / 4) ≤ Real.log Y₀ :=
      Real.log_le_log (by positivity) (by rw [hY₀]; linarith)
    rw [Real.log_div hs0.ne' (by norm_num), Real.log_sqrt hX0.le] at h1
    linarith
  have hsqY : √L / 2 ≤ √(Real.log Y₀) := by
    have h4 : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc √L / 2 = √(L / 4) := by rw [Real.sqrt_div' _ (by norm_num), h4]
      _ ≤ √(Real.log Y₀) := Real.sqrt_le_sqrt hlogY₀
  have hD : C / √(Real.log Y₀) ≤ 2 * C / √L := by
    calc C / √(Real.log Y₀) ≤ C / (√L / 2) := div_le_div_of_nonneg_left hC (by positivity) hsqY
      _ = 2 * C / √L := by rw [div_div_eq_mul_div, mul_comm]
  -- `⌊log₂ X⌋ + 1 ≤ 3L`
  have hE : ((Nat.log 2 X : ℕ) : ℝ) + 1 ≤ 3 * L := by
    have h1 : (2 : ℝ) ^ Nat.log 2 X ≤ X := by exact_mod_cast Nat.pow_log_le_self 2 hXn.ne'
    have h2 : (Nat.log 2 X : ℝ) * Real.log 2 ≤ L := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) h1
    have h3 : (0 : ℝ) ≤ Nat.log 2 X := Nat.cast_nonneg _
    nlinarith
  have hE0 : (0 : ℝ) ≤ (Nat.log 2 X : ℕ) + 1 := by positivity
  -- the lower-order terms
  have hsqL : √L ≤ L := by
    calc √L ≤ √(L ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = L := Real.sqrt_sq hL0.le
  have hsqX : √(X : ℝ) ≤ X := by
    calc √(X : ℝ) ≤ √((X : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = X := Real.sqrt_sq hX0.le
  have hXX : √(X : ℝ) * √(X : ℝ) = X := Real.mul_self_sqrt hX0.le
  have key : 3 * L * √X + 2 * C / √L * (9 * L ^ 2) ≤ X / √L := by
    have a1 : L * √X * √L ≤ L ^ 2 * √X := by
      calc L * √X * √L ≤ L * √X * L :=
            mul_le_mul_of_nonneg_left hsqL (by positivity)
        _ = L ^ 2 * √X := by ring
    have a2 : L ^ 2 * √X ≤ c * X := by
      calc L ^ 2 * √X ≤ c * √X * √X := mul_le_mul_of_nonneg_right hlog2 (Real.sqrt_nonneg _)
        _ = c * X := by rw [mul_assoc, hXX]
    have a3 : L ^ 2 ≤ c * X := hlog2.trans (mul_le_mul_of_nonneg_left hsqX hc0.le)
    have a4 : (3 + 18 * C) * c = 1 := by rw [hc]; field_simp
    have a5 : 3 * (c * X) + 18 * C * (c * X) = X := by linear_combination (X : ℝ) * a4
    have a6 : 18 * C * L ^ 2 ≤ 18 * C * (c * X) := mul_le_mul_of_nonneg_left a3 (by positivity)
    have hk1 : 3 * L * √X * √L + 18 * C * L ^ 2 ≤ X := by linarith
    have heq : 3 * L * √X + 2 * C / √L * (9 * L ^ 2) =
        (3 * L * √X * √L + 18 * C * L ^ 2) / √L := by
      field_simp
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hk1 hsqL0.le
  have h1 : ((Nat.log 2 X : ℕ) + 1) * (V : ℝ) ≤ 3 * L * √X :=
    mul_le_mul hE hVle (Nat.cast_nonneg _) (by positivity)
  have h2 : C / √(Real.log Y₀) * (2 * X + ((Nat.log 2 X : ℕ) + 1) ^ 2) ≤
      2 * C / √L * (2 * X + 9 * L ^ 2) := by
    have hsq : (((Nat.log 2 X : ℕ) : ℝ) + 1) ^ 2 ≤ 9 * L ^ 2 := by
      exact (pow_le_pow_left₀ hE0 hE 2).trans (le_of_eq (by ring))
    exact mul_le_mul hD (by linarith) (by positivity) (by positivity)
  calc (levelCount A g j X : ℝ)
      ≤ ((Nat.log 2 X : ℕ) + 1) * V + C / √(Real.log Y₀) * (2 * X + ((Nat.log 2 X : ℕ) + 1) ^ 2) :=
        hexp
    _ ≤ 3 * L * √X + 2 * C / √L * (2 * X + 9 * L ^ 2) := add_le_add h1 h2
    _ = (3 * L * √X + 2 * C / √L * (9 * L ^ 2)) + 2 * C / √L * (2 * X) := by ring
    _ ≤ X / √L + 2 * C / √L * (2 * X) := by linarith
    _ = (4 * C + 1) * X / √L := by ring

open Classical in
/-- **Anti-concentration in `[1, X]` for a transported, doubling integer clock**: the sampling
conversion applied to `anticonc_odd_dyadic`. One constant `C₁` for the three clock rewards; the
threshold `X₁` depends only on the doubling threshold `n₀` and the transport threshold `x₀`, not on
`(A, q, δ)`. No Diophantine input. -/
theorem levelCount_le_of_transport (hTM : TaoMajorant) (hTP : TaoPrefix) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ ρ η : ℕ, (ρ = 1 ∧ η = 0) ∨ (ρ = 1 ∧ η = 1) ∨ (ρ = 0 ∧ η = 1) →
      ∀ (n0 : ℕ) (x₀ : ℝ), ∃ X₁ : ℝ, ∀ (A : Set ℕ) (q : ℕ → ℤ) (δ : ℤ),
        Transport A (fun n => (q n : ℝ)) ρ η x₀ →
        (∀ e u : ℕ, n0 ≤ u → Odd u → 2 ^ e * u ∈ A → u ∈ A ∧ q (2 ^ e * u) = q u - e * δ) →
        ∀ X : ℕ, X₁ ≤ X → ∀ j : ℤ, (levelCount A q j X : ℝ) ≤ C₁ * X / √(Real.log X) := by
  obtain ⟨C, x₁, hodd⟩ := anticonc_odd_dyadic hTM hTP
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨4 * max C 0 + 1, by linarith, fun ρ η hρη n0 x₀ => ?_⟩
  obtain ⟨X₁, hX₁⟩ := levelCount_le_of_odd_dyadic (max C 0) ((max x₁ x₀) ^ alpha) n0 hC0
  refine ⟨X₁, fun A q δ ht hdbl X hX j => hX₁ A q δ hdbl (fun Y hY j => ?_) X hX j⟩
  refine (hodd ρ η hρη A q x₀ ht Y hY j).trans ?_
  gcongr
  exact le_max_left _ _

/-! ## The clocks of Theorem 6.10 -/

/-- Level sets of `f` at `j` are those of `-f` at `-j`. -/
lemma levelCount_neg (S : Set ℕ) (f : ℕ → ℤ) (j : ℤ) (X : ℕ) :
    levelCount S f j X = levelCount S (fun n => -f n) (-j) X := by
  unfold levelCount
  congr 1
  exact filter_congr fun n _ => neg_inj.symm

/-- A doubling-compatible clock `-τ` with shift `1` drops by `e` under `u ↦ 2^e u` for large `u`
(the raw and shortcut clocks, `doubling_T`, `doubling_F`). -/
lemma dbl_of_doublingCompatible {A : Set ℕ} {τ : ℕ → ℕ}
    (h : DoublingCompatible A (fun n => -(τ n : ℝ)) 1) :
    ∃ n0 : ℕ, ∀ e u : ℕ, n0 ≤ u → Odd u → 2 ^ e * u ∈ A →
      u ∈ A ∧ -(τ (2 ^ e * u) : ℤ) = -(τ u : ℤ) - e * 1 := by
  obtain ⟨n0, hn0⟩ := h.iterate
  refine ⟨n0, fun e u hu _ hA => ?_⟩
  have huA := (hn0 e u hu).1.mp hA
  have h2 : -(τ (2 ^ e * u) : ℝ) = -(τ u : ℝ) - e * 1 := (hn0 e u hu).2 huA
  refine ⟨huA, Int.cast_injective (α := ℝ) ?_⟩
  push_cast
  linarith

/-- On a set of odd integers only the layer `e = 0` occurs. -/
lemma dbl_odd {A : Set ℕ} (hA : ∀ n ∈ A, Odd n) (q : ℕ → ℤ) :
    ∀ e u : ℕ, 0 ≤ u → Odd u → 2 ^ e * u ∈ A → u ∈ A ∧ q (2 ^ e * u) = q u - e * 0 := by
  intro e u _ _ h
  rcases e with _ | e
  · simp only [pow_zero, one_mul] at h ⊢
    exact ⟨h, by simp⟩
  · exfalso
    have hev : Even (2 ^ (e + 1) * u) := by
      rw [pow_succ]
      exact ⟨2 ^ e * u, by ring⟩
    exact Nat.not_even_iff_odd.mpr (hA _ h) hev

/-- The shortcut coordinate on its class drops by `e` under `u ↦ 2^e u`. -/
lemma dbl_coordF {a : ℕ} (ha : 0 < a) (hR : NonRepeating a) :
    ∀ e u : ℕ, 1 ≤ u → Odd u → 2 ^ e * u ∈ mergeClass a →
      u ∈ mergeClass a ∧ coordF a (2 ^ e * u) = coordF a u - e * 1 := by
  intro e u hu _ h
  have huC := (two_pow_mul_mem_mergeClass hu e).mp h
  exact ⟨huC, by rw [coordF_two_pow_mul ha hR huC, mul_one]⟩

/-- The raw coordinate on its class drops by `e` under `u ↦ 2^e u`. -/
lemma dbl_coordT {a : ℕ} (hR : NonRepeating a) :
    ∀ e u : ℕ, 1 ≤ u → Odd u → 2 ^ e * u ∈ mergeClass a →
      u ∈ mergeClass a ∧ coordT a (2 ^ e * u) = coordT a u - e * 1 := by
  intro e u hu _ h
  have huC := (two_pow_mul_mem_mergeClass hu e).mp h
  exact ⟨huC, by rw [coordT_two_pow_mul hR huC, mul_one]⟩

/-- The class-dependent clock on a union of classes drops by `e` under `u ↦ 2^e u`. -/
lemma dbl_classClock {A : Finset ℕ} (hdis : ∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a')
    (coord : ℕ → ℕ → ℤ) (jC : ℕ → ℤ)
    (hc : ∀ a ∈ A, ∀ u ∈ mergeClass a, ∀ e : ℕ, coord a (2 ^ e * u) = coord a u - e) :
    ∀ e u : ℕ, 1 ≤ u → Odd u → 2 ^ e * u ∈ ⋃ a ∈ A, mergeClass a →
      u ∈ (⋃ a ∈ A, mergeClass a) ∧
        classClock A coord jC (2 ^ e * u) = classClock A coord jC u - e * 1 := by
  intro e u hu _ h
  obtain ⟨h1, h2⟩ := classClock_two_pow_mul hdis coord jC hc hu e
  have huU := h1.mp h
  exact ⟨huU, by rw [h2 huU, mul_one]⟩

/-- **One indicator for all classes** (proof of Theorem 6.10(iii)): the level set of the
class-dependent clock at `0` is the disjoint union of the level sets `{ℓ_C = j_C}` of the classes. -/
lemma levelCount_classClock {A : Finset ℕ} (hdis : ∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a')
    (coord : ℕ → ℕ → ℤ) (jC : ℕ → ℤ) (X : ℕ) :
    levelCount (⋃ a ∈ A, mergeClass a) (classClock A coord jC) 0 X =
      ∑ a ∈ A, levelCount (mergeClass a) (coord a) (jC a) X := by
  classical
  unfold levelCount
  have hset : (window (⋃ a ∈ A, mergeClass a) X).filter (fun n => classClock A coord jC n = 0) =
      A.biUnion (fun a => (window (mergeClass a) X).filter (fun n => coord a n = jC a)) := by
    ext n
    simp only [mem_filter, mem_window, mem_biUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨hnX, a, ha, hna⟩, h0⟩
      refine ⟨a, ha, ⟨hnX, hna⟩, ?_⟩
      rw [classClock_eq hdis coord jC ha hna] at h0
      linarith
    · rintro ⟨a, ha, ⟨hnX, hna⟩, h⟩
      refine ⟨⟨hnX, a, ha, hna⟩, ?_⟩
      rw [classClock_eq hdis coord jC ha hna, h, sub_self]
  rw [hset, card_biUnion]
  intro a ha a' ha' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro n h1 h2
  rw [mem_filter, mem_window] at h1 h2
  exact hne (mem_mergeClass_unique hdis (Finset.mem_coe.mp ha) (Finset.mem_coe.mp ha')
    h1.1.2 h2.1.2)

/-- `v ≤ C₁X/√L` gives `v ≤ 2C₁X/√L`. -/
lemma le_two_mul_of_le {v C₁ X L : ℝ} (hC₁ : 0 ≤ C₁) (hX : 0 ≤ X) (h : v ≤ C₁ * X / √L) :
    v ≤ 2 * C₁ * X / √L :=
  h.trans (div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hC₁ hX]) (Real.sqrt_nonneg _))

/-- A proportion in a set of density `p`, from a count bound and `#(S ∩ [1, X]) ≥ pX/2`. -/
lemma div_card_le {num C₁ p : ℝ} {cnt X : ℕ} (hp : 0 < p) (hX : 0 < X)
    (hcnt : p * X / 2 ≤ cnt) (h0 : 0 ≤ num) (h : num ≤ C₁ * X / √(Real.log X)) :
    num / cnt ≤ 2 * C₁ / (p * √(Real.log X)) := by
  have hX' : (0 : ℝ) < X := by exact_mod_cast hX
  have hpX : 0 < p * X / 2 := by positivity
  calc num / cnt ≤ num / (p * X / 2) := div_le_div_of_nonneg_left h0 hpX hcnt
    _ ≤ C₁ * X / √(Real.log X) / (p * X / 2) := div_le_div_of_nonneg_right h hpX.le
    _ = 2 * C₁ / (p * √(Real.log X)) := by
        rcases eq_or_lt_of_le (Real.sqrt_nonneg (Real.log X)) with hs | hs
        · rw [← hs]
          simp
        · field_simp

/-- A set of positive density `p` has `#(S ∩ [1, X]) ≥ pX/2` for all large `X`. -/
lemma exists_half_le_card_window {S : Set ℕ} {p : ℝ} (hS : HasDensity S p) (hp : 0 < p) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → 0 < X ∧ p * X / 2 ≤ (window S X).card := by
  have h := (hS.eventually (lt_mem_nhds (show p / 2 < p by linarith))).and
    (eventually_gt_atTop 0)
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨N, fun X hX => ?_⟩
  obtain ⟨h1, h2⟩ := hN X hX
  refine ⟨h2, ?_⟩
  have hX' : (0 : ℝ) < X := by exact_mod_cast h2
  rw [lt_div_iff₀ hX'] at h1
  linarith

/-! ## Theorem 6.10 -/

open Classical in
/-- **Theorem 6.10 [`thm:anticonc`] (anti-concentration).** `C₀` is absolute, `X₀` is absolute for
(ii) and (iii); in (i) `X ≥ X₁(b)`. The conjuncts, in order:
(i) for `G ∈ {T, F}` and every positive `b`, `sup_j #{n ≤ X : n ∈ P_G(b), τ_{G,b}(n) = j} ≤
C₀X/√(log X)`; the same for odd `b`, the odd clock and odd sources (`P_U(b)` is odd);
(ii) for every divergent class (the class of a nonrepeating `T`-ray `a`, any origin `a`) and its
shortcut and raw coordinates, `sup_j #{n ≤ X : n ∈ C, ℓ_C(n) = j} ≤ C₀X/√(log X)`, uniformly in
the class and the origin (`C₀, X₀` are chosen before `a`);
(iii) for any finite family of distinct divergent classes (base points pairwise non-merging) and
any choice of one level per class, the sum of the counts is `≤ C₀X/√(log X)`, with no factor
counting the classes;
(closing sentence) under conditional sampling from a set `S` of positive density `p`, the
corresponding proportions are `≤ C₀/(p√(log X))`. No Diophantine input. -/
theorem anticonc (hTM : TaoMajorant) (hTP : TaoPrefix) :
    ∃ C₀ X₀ : ℝ, 0 < C₀ ∧
    (∀ b : ℕ, 0 < b → ∃ X₁ : ℝ, ∀ X : ℕ, X₁ ≤ X → ∀ j : ℤ,
      (levelCount (Pred T b) (fun n => (hit T b n : ℤ)) j X : ℝ) ≤ C₀ * X / √(Real.log X) ∧
      (levelCount (Pred F b) (fun n => (hit F b n : ℤ)) j X : ℝ) ≤ C₀ * X / √(Real.log X)) ∧
    (∀ b : ℕ, Odd b → ∃ X₁ : ℝ, ∀ X : ℕ, X₁ ≤ X → ∀ j : ℤ,
      (levelCount (PredU b) (fun n => (hit U b n : ℤ)) j X : ℝ) ≤ C₀ * X / √(Real.log X)) ∧
    (∀ X : ℕ, X₀ ≤ X → ∀ a : ℕ, 0 < a → NonRepeating a → ∀ j : ℤ,
      (levelCount (mergeClass a) (coordF a) j X : ℝ) ≤ C₀ * X / √(Real.log X) ∧
      (levelCount (mergeClass a) (coordT a) j X : ℝ) ≤ C₀ * X / √(Real.log X)) ∧
    (∀ X : ℕ, X₀ ≤ X → ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a ∧ NonRepeating a) →
      (∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a') → ∀ jC : ℕ → ℤ,
      ∑ a ∈ A, (levelCount (mergeClass a) (coordF a) (jC a) X : ℝ) ≤ C₀ * X / √(Real.log X) ∧
      ∑ a ∈ A, (levelCount (mergeClass a) (coordT a) (jC a) X : ℝ) ≤ C₀ * X / √(Real.log X)) ∧
    (∀ (S : Set ℕ) (p : ℝ), 0 < p → HasDensity S p →
      (∀ b : ℕ, 0 < b → ∃ X₁ : ℝ, ∀ X : ℕ, X₁ ≤ X → ∀ j : ℤ,
        (levelCount (S ∩ Pred T b) (fun n => (hit T b n : ℤ)) j X : ℝ) / (window S X).card ≤
          C₀ / (p * √(Real.log X)) ∧
        (levelCount (S ∩ Pred F b) (fun n => (hit F b n : ℤ)) j X : ℝ) / (window S X).card ≤
          C₀ / (p * √(Real.log X))) ∧
      (∀ b : ℕ, Odd b → ∃ X₁ : ℝ, ∀ X : ℕ, X₁ ≤ X → ∀ j : ℤ,
        (levelCount (S ∩ PredU b) (fun n => (hit U b n : ℤ)) j X : ℝ) / (window S X).card ≤
          C₀ / (p * √(Real.log X))) ∧
      (∃ X₁ : ℝ, ∀ X : ℕ, X₁ ≤ X →
        (∀ a : ℕ, 0 < a → NonRepeating a → ∀ j : ℤ,
          (levelCount (S ∩ mergeClass a) (coordF a) j X : ℝ) / (window S X).card ≤
            C₀ / (p * √(Real.log X)) ∧
          (levelCount (S ∩ mergeClass a) (coordT a) j X : ℝ) / (window S X).card ≤
            C₀ / (p * √(Real.log X))) ∧
        (∀ A : Finset ℕ, (∀ a ∈ A, 0 < a ∧ NonRepeating a) →
          (∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a') → ∀ jC : ℕ → ℤ,
          (∑ a ∈ A, (levelCount (S ∩ mergeClass a) (coordF a) (jC a) X : ℝ)) /
            (window S X).card ≤ C₀ / (p * √(Real.log X)) ∧
          (∑ a ∈ A, (levelCount (S ∩ mergeClass a) (coordT a) (jC a) X : ℝ)) /
            (window S X).card ≤ C₀ / (p * √(Real.log X))))) := by
  obtain ⟨C₁, hC₁, hconv⟩ := levelCount_le_of_transport hTM hTP
  have r10 : ((1 : ℕ) = 1 ∧ (0 : ℕ) = 0) ∨ ((1 : ℕ) = 1 ∧ (0 : ℕ) = 1) ∨
      ((1 : ℕ) = 0 ∧ (0 : ℕ) = 1) := Or.inl ⟨rfl, rfl⟩
  have r11 : ((1 : ℕ) = 1 ∧ (1 : ℕ) = 0) ∨ ((1 : ℕ) = 1 ∧ (1 : ℕ) = 1) ∨
      ((1 : ℕ) = 0 ∧ (1 : ℕ) = 1) := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have r01 : ((0 : ℕ) = 1 ∧ (1 : ℕ) = 0) ∨ ((0 : ℕ) = 1 ∧ (1 : ℕ) = 1) ∨
      ((0 : ℕ) = 0 ∧ (1 : ℕ) = 1) := Or.inr (Or.inr ⟨rfl, rfl⟩)
  -- (i): the raw and shortcut clocks of `P_T(b)`, `P_F(b)`, with the constant `C₁`
  have hTF : ∀ b : ℕ, 0 < b → ∃ X₁ : ℝ, ∀ X : ℕ, X₁ ≤ X → ∀ j : ℤ,
      (levelCount (Pred T b) (fun n => (hit T b n : ℤ)) j X : ℝ) ≤ C₁ * X / √(Real.log X) ∧
      (levelCount (Pred F b) (fun n => (hit F b n : ℤ)) j X : ℝ) ≤ C₁ * X / √(Real.log X) := by
    intro b hb
    obtain ⟨nT, hnT⟩ := dbl_of_doublingCompatible (doubling_T b hb)
    obtain ⟨nF, hnF⟩ := dbl_of_doublingCompatible (doubling_F b hb)
    obtain ⟨XT, hXT⟩ := hconv 1 1 r11 nT (b + 1)
    obtain ⟨XF, hXF⟩ := hconv 1 0 r10 nF (b + 1)
    refine ⟨max XT XF, fun X hX j => ⟨?_, ?_⟩⟩
    · rw [levelCount_neg]
      exact hXT (Pred T b) (fun n => -(hit T b n : ℤ)) 1 (by simpa using transport_T b) hnT X
        (le_of_max_le_left hX) (-j)
    · rw [levelCount_neg]
      exact hXF (Pred F b) (fun n => -(hit F b n : ℤ)) 1 (by simpa using transport_F b) hnF X
        (le_of_max_le_right hX) (-j)
  -- (i): the odd clock on odd sources
  have hU : ∀ b : ℕ, Odd b → ∃ X₁ : ℝ, ∀ X : ℕ, X₁ ≤ X → ∀ j : ℤ,
      (levelCount (PredU b) (fun n => (hit U b n : ℤ)) j X : ℝ) ≤ C₁ * X / √(Real.log X) := by
    intro b _
    obtain ⟨XU, hXU⟩ := hconv 0 1 r01 0 (b + 1)
    refine ⟨XU, fun X hX j => ?_⟩
    rw [levelCount_neg]
    exact hXU (PredU b) (fun n => -(hit U b n : ℤ)) 0 (by simpa using transport_U b)
      (dbl_odd (fun n (hn : n ∈ PredU b) => hn.2.1) (fun n => -(hit U b n : ℤ))) X hX (-j)
  -- (ii) and (iii): the coordinates, with an absolute threshold (transport at threshold `0`)
  obtain ⟨XF, hXF⟩ := hconv 1 0 r10 1 0
  obtain ⟨XT, hXT⟩ := hconv 1 1 r11 1 0
  have hcls : ∀ X : ℕ, max XF XT ≤ X → ∀ a : ℕ, 0 < a → NonRepeating a → ∀ j : ℤ,
      (levelCount (mergeClass a) (coordF a) j X : ℝ) ≤ C₁ * X / √(Real.log X) ∧
      (levelCount (mergeClass a) (coordT a) j X : ℝ) ≤ C₁ * X / √(Real.log X) := by
    intro X hX a ha hR j
    exact ⟨hXF _ (coordF a) 1 (by simpa using transport_coordF ha hR 0) (dbl_coordF ha hR) X
        (le_of_max_le_left hX) j,
      hXT _ (coordT a) 1 (by simpa using transport_coordT ha hR 0) (dbl_coordT hR) X
        (le_of_max_le_right hX) j⟩
  have hun : ∀ X : ℕ, max XF XT ≤ X → ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a ∧ NonRepeating a) →
      (∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a') → ∀ jC : ℕ → ℤ,
      ∑ a ∈ A, (levelCount (mergeClass a) (coordF a) (jC a) X : ℝ) ≤ C₁ * X / √(Real.log X) ∧
      ∑ a ∈ A, (levelCount (mergeClass a) (coordT a) (jC a) X : ℝ) ≤ C₁ * X / √(Real.log X) := by
    intro X hX A hA hdis jC
    constructor
    · rw [← Nat.cast_sum, ← levelCount_classClock hdis coordF jC X]
      exact hXF _ (classClock A coordF jC) 1 (by simpa using transport_classClockF hA hdis jC 0)
        (dbl_classClock hdis coordF jC fun a ha u hu e =>
          coordF_two_pow_mul (hA a ha).1 (hA a ha).2 hu e) X (le_of_max_le_left hX) 0
    · rw [← Nat.cast_sum, ← levelCount_classClock hdis coordT jC X]
      exact hXT _ (classClock A coordT jC) 1 (by simpa using transport_classClockT hA hdis jC 0)
        (dbl_classClock hdis coordT jC fun a ha u hu e => coordT_two_pow_mul (hA a ha).2 hu e) X
        (le_of_max_le_right hX) 0
  have hC₁0 : 0 ≤ C₁ := hC₁.le
  refine ⟨2 * C₁, max XF XT, by linarith, fun b hb => ?_, fun b hb => ?_,
    fun X hX a ha hR j => ?_, fun X hX A hA hdis jC => ?_, fun S p hp hS => ?_⟩
  · obtain ⟨X₁, h⟩ := hTF b hb
    exact ⟨X₁, fun X hX j => ⟨le_two_mul_of_le hC₁0 (Nat.cast_nonneg X) (h X hX j).1,
      le_two_mul_of_le hC₁0 (Nat.cast_nonneg X) (h X hX j).2⟩⟩
  · obtain ⟨X₁, h⟩ := hU b hb
    exact ⟨X₁, fun X hX j => le_two_mul_of_le hC₁0 (Nat.cast_nonneg X) (h X hX j)⟩
  · obtain ⟨h1, h2⟩ := hcls X hX a ha hR j
    exact ⟨le_two_mul_of_le hC₁0 (Nat.cast_nonneg X) h1,
      le_two_mul_of_le hC₁0 (Nat.cast_nonneg X) h2⟩
  · obtain ⟨h1, h2⟩ := hun X hX A hA hdis jC
    exact ⟨le_two_mul_of_le hC₁0 (Nat.cast_nonneg X) h1,
      le_two_mul_of_le hC₁0 (Nat.cast_nonneg X) h2⟩
  · -- the closing sentence: `#(S ∩ [1, X]) ≥ pX/2` for large `X`
    obtain ⟨N, hN⟩ := exists_half_le_card_window hS hp
    have hmono : ∀ (B : Set ℕ) (f : ℕ → ℤ) (j : ℤ) (X : ℕ),
        (levelCount (S ∩ B) f j X : ℝ) ≤ levelCount B f j X := fun B f j X => by
      exact_mod_cast levelCount_mono Set.inter_subset_right f j X
    have hNX : ∀ X₁ : ℝ, ∀ X : ℕ, max X₁ N ≤ X → 0 < X ∧ p * X / 2 ≤ (window S X).card :=
      fun X₁ X hX => hN X (by exact_mod_cast le_of_max_le_right hX)
    refine ⟨fun b hb => ?_, fun b hb => ?_, ⟨max (max XF XT) N, fun X hX => ⟨?_, ?_⟩⟩⟩
    · obtain ⟨X₁, h⟩ := hTF b hb
      refine ⟨max X₁ N, fun X hX j => ?_⟩
      obtain ⟨hX0, hcnt⟩ := hNX X₁ X hX
      obtain ⟨h1, h2⟩ := h X (le_of_max_le_left hX) j
      exact ⟨div_card_le hp hX0 hcnt (Nat.cast_nonneg _) ((hmono _ _ _ _).trans h1),
        div_card_le hp hX0 hcnt (Nat.cast_nonneg _) ((hmono _ _ _ _).trans h2)⟩
    · obtain ⟨X₁, h⟩ := hU b hb
      refine ⟨max X₁ N, fun X hX j => ?_⟩
      obtain ⟨hX0, hcnt⟩ := hNX X₁ X hX
      exact div_card_le hp hX0 hcnt (Nat.cast_nonneg _) ((hmono _ _ _ _).trans
        (h X (le_of_max_le_left hX) j))
    · intro a ha hR j
      obtain ⟨hX0, hcnt⟩ := hNX _ X hX
      obtain ⟨h1, h2⟩ := hcls X (le_of_max_le_left hX) a ha hR j
      exact ⟨div_card_le hp hX0 hcnt (Nat.cast_nonneg _) ((hmono _ _ _ _).trans h1),
        div_card_le hp hX0 hcnt (Nat.cast_nonneg _) ((hmono _ _ _ _).trans h2)⟩
    · intro A hA hdis jC
      obtain ⟨hX0, hcnt⟩ := hNX _ X hX
      obtain ⟨h1, h2⟩ := hun X (le_of_max_le_left hX) A hA hdis jC
      exact ⟨div_card_le hp hX0 hcnt (sum_nonneg fun _ _ => Nat.cast_nonneg _)
          ((sum_le_sum fun a _ => hmono _ _ _ _).trans h1),
        div_card_le hp hX0 hcnt (sum_nonneg fun _ _ => Nat.cast_nonneg _)
          ((sum_le_sum fun a _ => hmono _ _ _ _).trans h2)⟩

end CollatzCLT
