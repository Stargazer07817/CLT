import LeanClt.Positivity.Histories

/-!
# §8.3: the marked mass, Lemma 8.6 and the favourable seed residue

**`Z_n` as a function of `M mod 3^{Q_n}`** (point G7 of checkpoint 06). At an odd target `R` the
transfer operator of a word `w` reads off realisability: `T_w g (R mod 3^{t+d})` is
`W(w) g(src w R mod 3^t)` when `w` is realisable at `R` and `0` otherwise
(`Tw_natCast_of_realizes`, `Tw_natCast_of_not_realizes`, from Lemma 8.2). Hence
`Z_n(M) = ∑_H T_{H.flatten} ρ_{k_n}(M mod 3^{t+d})` over all `n`-block histories `H`
(`Zmark_eq_sum_Tw`), and with `Q_n = ∑_{j<n} h_{b_j} + k_n` (`Qn`), `Z_n(M) = Zres b0 n Q (M mod 3^Q)`
for every `Q ≥ Q_n` and every odd `M` (`Zmark_eq_Zres`). By (8.2) and the product structure of the
histories (`sum_blocks_gm`: `∑_H 2^{-A(H)} = ∏_{j<n} p_j`), its mean over `G_Q` is
`(2/3) ∏_{j<n} p_j` (`sum_Zres`).

**The generation step.** Removing the last block, `Z_{n+1}(M)` is the sum over `n`-block histories
of `W` times `∑_{w ∈ V_{b_n,K_n}} T_{w,Q} ρ_{k_{n+1}}` at the endpoint (`sum_hist_succ`), so
`Z_{n+1}(M) - Z_n(M) = ∑_y 𝓗_{n,Q}(y) g(y)` with
`g = ∑_w T_{w,Q} ρ_{k_{n+1}} - lift(ρ_{k_n})` and `Q = h_{b_n} + k_{n+1} ≤ 2 b_n`
(`Zmark_succ_sub`).

* **Lemma 8.6 [`lem:D1`]**, (8.9, `eq:D1`) is `uniform_cauchy`: Lemma 8.3 with `l = k_n`, (8.8),
  Lemma 8.4 and (8.1) with `A = 6`, as in the paper.
* **The favourable residue** (the unlabelled paragraph of §8.3 after Lemma 8.6) is
  `favourable_residue`. There is no limit `z(M)`: `n⋆` is chosen so that the tail
  `∑_{n ≥ n⋆}` of the bound (8.9) is below `p₀/3`, where `p₀ > 0` bounds the partial products of
  the `p_j` (Lemma 8.4); some residue `y` mod `3^{Q_{n⋆}}` has
  `Z_{n⋆} ≥ (2/3)∏_{j<n⋆} p_j ≥ 2p₀/3` (pigeonhole, `exists_Zres_ge`), and finite telescoping gives
  `Z_n(M) ≥ p₀/3` for every `n ≥ n⋆` and every odd `M ≥ 16^{b_0}` with `M ≡ y`; the theorem's `p` is
  `p₀/3`. The residue need not be a unit (point G8 of checkpoint 06): Lemma 8.7 reaches every
  residue class.
-/

open Finset Real Filter

noncomputable section

namespace CollatzCLT
namespace Positivity

/-! ## Transfer operators at an odd integer target -/

/-- At an odd target `R` realised by `w`, `T_w g (R mod 3^{t+d}) = W(w) g(src w R mod 3^t)`. -/
lemma Tw_natCast_of_realizes {w : Word} (hw : w.Pos) {R : ℕ} (hR : Odd R) (h : Realizes w R)
    (t : ℕ) (g : ZMod (3 ^ t) → ℝ) :
    Tw t w g (R : ZMod (3 ^ (t + w.length))) = wt w * g (src w R) := by
  have hcast : (ZMod.cast (R : ZMod (3 ^ (t + w.length))) : ZMod (3 ^ w.length)) =
      thetaRes w.length w := by
    rw [ZMod.cast_natCast (pow_dvd_pow 3 (Nat.le_add_left _ _))]; exact h
  obtain ⟨z0, hz0⟩ := (mem_range_FwN (n := t + w.length) (t := t) rfl _).mpr hcast
  have hres := (realisable hw hR (z := z0) hz0.symm).2.2.2.1
  have hinj := FwN_injective (w := w) (n := t + w.length) (t := t) (by omega)
  unfold Tw
  congr 1
  rw [Finset.sum_eq_single z0]
  · rw [if_pos (show Fw t w z0 = _ from hz0), hres]
  · intro z _ hz
    rw [if_neg]
    intro h'
    exact hz (hinj (h'.trans hz0.symm))
  · simp

/-- At an odd target `R` not realised by `w`, `T_w g (R mod 3^{t+d}) = 0`. -/
lemma Tw_natCast_of_not_realizes {w : Word} (hw : w.Pos) {R : ℕ} (hR : Odd R)
    (h : ¬ Realizes w R) (t : ℕ) (g : ZMod (3 ^ t) → ℝ) :
    Tw t w g (R : ZMod (3 ^ (t + w.length))) = 0 := by
  unfold Tw
  rw [Finset.sum_eq_zero, mul_zero]
  intro z _
  rw [if_neg]
  intro hz
  exact h (realisable hw hR (z := z) hz.symm).1

lemma TwQ_natCast {Q t : ℕ} {w : Word} (hQ : t + w.length ≤ Q) (g : ZMod (3 ^ t) → ℝ) (R : ℕ) :
    TwQ Q t w g (R : ZMod (3 ^ Q)) = Tw t w g (R : ZMod (3 ^ (t + w.length))) := by
  unfold TwQ; rw [ZMod.cast_natCast (pow_dvd_pow 3 hQ)]

/-! ## Histories: one more block -/

lemma flatten_append_singleton (H : List Word) (w : Word) : (H ++ [w]).flatten = H.flatten ++ w := by
  simp

lemma append_singleton_injective :
    Function.Injective (fun p : List Word × Word => p.1 ++ [p.2]) := by
  rintro ⟨H, w⟩ ⟨H', w'⟩ h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  simp only [List.cons.injEq, and_true] at h2
  exact Prod.ext h1 h2

lemma blocks_succ (b0 n : ℕ) :
    blocks b0 (n + 1) =
      (blocks b0 n ×ˢ central (bseq b0 n) (Kseq n)).image fun p => p.1 ++ [p.2] := rfl

lemma endpt_odd {b0 M n : ℕ} (hM : Odd M) {H : List Word} (hH : H ∈ hist b0 M n) :
    Odd (endpt M H) := by
  obtain ⟨hb, hr⟩ := mem_hist.mp hH
  exact (realisable_of_realizes (flatten_pos (mem_blocks.mp hb).2) hM hr).2.1

open Classical in
/-- The histories of `n + 1` blocks are the realisable one-block extensions of those of `n`
blocks. -/
lemma hist_succ (b0 M n : ℕ) (hM : Odd M) :
    hist b0 M (n + 1) = ((hist b0 M n ×ˢ central (bseq b0 n) (Kseq n)).filter
      (fun p => Realizes p.2 (endpt M p.1))).image (fun p => p.1 ++ [p.2]) := by
  ext H'
  rw [mem_hist, blocks_succ, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨H, w⟩, hp, rfl⟩, hr⟩
    rw [Finset.mem_product] at hp
    rw [flatten_append_singleton, realizes_append (flatten_pos (mem_blocks.mp hp.1).2) hM] at hr
    refine ⟨(H, w), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨mem_hist.mpr ⟨hp.1, hr.1⟩, hp.2⟩, hr.2⟩
  · rintro ⟨⟨H, w⟩, hp, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hH, hw⟩, hr⟩ := hp
    obtain ⟨hHb, hHr⟩ := mem_hist.mp hH
    refine ⟨⟨(H, w), Finset.mem_product.mpr ⟨hHb, hw⟩, rfl⟩, ?_⟩
    rw [flatten_append_singleton, realizes_append (flatten_pos (mem_blocks.mp hHb).2) hM]
    exact ⟨hHr, hr⟩

/-- The endpoint of a one-block extension is the source of the new block at the old endpoint. -/
lemma endpt_append {b0 M n : ℕ} (hM : Odd M) {H : List Word} (hH : H ∈ hist b0 M n) {w : Word}
    (hw : w.Pos) (hr : Realizes w (endpt M H)) : endpt M (H ++ [w]) = src w (endpt M H) := by
  obtain ⟨hHb, hHr⟩ := mem_hist.mp hH
  have hHp := flatten_pos (mem_blocks.mp hHb).2
  unfold endpt
  rw [flatten_append_singleton]
  exact src_append hHp hw hM ((realizes_append hHp hM).mpr ⟨hHr, hr⟩)

/-- **The generation step.** A sum over `(n+1)`-block histories of `W` times a function of the
endpoint residue is the sum over `n`-block histories of `W` times `∑_{w ∈ V_{b_n,K_n}} T_w g` at
the endpoint. -/
theorem sum_hist_succ {b0 M : ℕ} (hM : Odd M) (n t : ℕ) (g : ZMod (3 ^ t) → ℝ) :
    ∑ H ∈ hist b0 M (n + 1), wt H.flatten * g (endpt M H) =
      ∑ H ∈ hist b0 M n, wt H.flatten * ∑ w ∈ central (bseq b0 n) (Kseq n),
        Tw t w g ((endpt M H : ℕ) : ZMod (3 ^ (t + w.length))) := by
  rw [hist_succ b0 M n hM, Finset.sum_image (fun p _ q _ h => append_singleton_injective h),
    Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun H hH => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hwp := central_pos hw
  have hRo := endpt_odd hM hH
  split_ifs with hr
  · rw [Tw_natCast_of_realizes hwp hRo hr, endpt_append hM hH hwp hr, flatten_append_singleton,
      wt_append]
    ring
  · rw [Tw_natCast_of_not_realizes hwp hRo hr, mul_zero]

/-- Pairing the histogram with a function: `∑_y 𝓗_{n,q}(y) f(y) = ∑_H W(H) f(R_H mod 3^q)`. -/
lemma sum_histo_mul (b0 M n q : ℕ) (f : ZMod (3 ^ q) → ℝ) :
    ∑ y, histo b0 M n q y * f y =
      ∑ H ∈ hist b0 M n, wt H.flatten * f ((endpt M H : ℕ) : ZMod (3 ^ q)) := by
  unfold histo
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun H _ => ?_
  simp [ite_mul]

/-! ## `Z_n` as a function of `M mod 3^{Q_n}`, and its mean -/

/-- `Q_n = ∑_{j<n} h_{b_j} + k_n`: residues mod `3^{Q_n}` determine every history residue. -/
def Qn (b0 n : ℕ) : ℕ := ∑ j ∈ range n, hB (bseq b0 j) + kseq b0 n

/-- `Z_n` as a function on `G_Q`: `∑_H T_{H.flatten, Q} ρ_{k_n}` over all `n`-block histories. -/
def Zres (b0 n Q : ℕ) (y : ZMod (3 ^ Q)) : ℝ :=
  ∑ H ∈ blocks b0 n, TwQ Q (kseq b0 n) H.flatten (rhoX (kseq b0 n)) y

lemma flatten_length_le {b0 n : ℕ} {H : List Word} (hH : H ∈ blocks b0 n) :
    H.flatten.length ≤ ∑ j ∈ range n, hB (bseq b0 j) := by
  induction n generalizing H with
  | zero =>
    simp only [blocks, Finset.mem_singleton] at hH
    subst hH; simp
  | succ n ih =>
    rw [blocks_succ, Finset.mem_image] at hH
    obtain ⟨⟨H', w⟩, hp, rfl⟩ := hH
    rw [Finset.mem_product] at hp
    rw [flatten_append_singleton, List.length_append, Finset.sum_range_succ]
    exact Nat.add_le_add (ih hp.1) (central_length_le hp.2)

lemma Zmark_eq_sum_Tw (b0 : ℕ) {M : ℕ} (hM : Odd M) (n : ℕ) :
    Zmark b0 M n = ∑ H ∈ blocks b0 n, Tw (kseq b0 n) H.flatten (rhoX (kseq b0 n))
      (M : ZMod (3 ^ (kseq b0 n + H.flatten.length))) := by
  unfold Zmark hist
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun H hH => ?_
  have hpos := flatten_pos (mem_blocks.mp hH).2
  split_ifs with h
  · rw [Tw_natCast_of_realizes hpos hM h]; rfl
  · rw [Tw_natCast_of_not_realizes hpos hM h]

/-- **`Z_n(M)` depends only on `M mod 3^Q`** for `Q ≥ Q_n` (odd `M`). -/
theorem Zmark_eq_Zres (b0 : ℕ) {M : ℕ} (hM : Odd M) {n Q : ℕ} (hQ : Qn b0 n ≤ Q) :
    Zmark b0 M n = Zres b0 n Q (M : ZMod (3 ^ Q)) := by
  rw [Zmark_eq_sum_Tw b0 hM n]
  unfold Zres
  refine Finset.sum_congr rfl fun H hH => ?_
  rw [TwQ_natCast]
  have := flatten_length_le hH
  unfold Qn at hQ
  omega

/-- The product structure of the histories: `∑_H 2^{-A(H)} = ∏_{j<n} p_j`. -/
theorem sum_blocks_gm (b0 n : ℕ) : ∑ H ∈ blocks b0 n, gm H.flatten = ∏ j ∈ range n, pj b0 j := by
  induction n with
  | zero => simp [blocks, gm, tot]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih, blocks_succ,
      Finset.sum_image (fun p _ q _ h => append_singleton_injective h), Finset.sum_product]
    unfold pj pmass
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [flatten_append_singleton, gm_append]

lemma sum_rhoX (k : ℕ) : ∑ y : ZMod (3 ^ k), rhoX k y = 2 / 3 * 3 ^ k := by
  unfold rhoX; rw [← Finset.mul_sum, sum_lawX, mul_one]

lemma sum_TwQ {Q t : ℕ} {w : Word} (hQ : t + w.length ≤ Q) (g : ZMod (3 ^ t) → ℝ) :
    ∑ y : ZMod (3 ^ Q), TwQ Q t w g y = 3 ^ Q * (gm w * ((∑ z, g z) / 3 ^ t)) := by
  unfold TwQ
  rw [sum_cast_eq hQ (Tw t w g), ← mean_Tw]
  have e : (3 : ℝ) ^ Q = 3 ^ (Q - (t + w.length)) * 3 ^ (t + w.length) := by
    rw [← pow_add]; congr 1; omega
  rw [e]
  push_cast
  field_simp

/-- **The mean of `Z_n`** over `G_Q` (`Q ≥ Q_n`) is `(2/3) ∏_{j<n} p_j`, by (8.2). -/
theorem sum_Zres (b0 n : ℕ) {Q : ℕ} (hQ : Qn b0 n ≤ Q) :
    ∑ y : ZMod (3 ^ Q), Zres b0 n Q y = 3 ^ Q * (2 / 3 * ∏ j ∈ range n, pj b0 j) := by
  unfold Zres
  rw [Finset.sum_comm, ← sum_blocks_gm, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun H hH => ?_
  have hl := flatten_length_le hH
  unfold Qn at hQ
  rw [sum_TwQ (by omega), sum_rhoX]
  field_simp

/-- **Pigeonhole:** some residue class mod `3^Q` carries at least the mean of `Z_n`. -/
theorem exists_Zres_ge (b0 n : ℕ) {Q : ℕ} (hQ : Qn b0 n ≤ Q) :
    ∃ y : ZMod (3 ^ Q), 2 / 3 * ∏ j ∈ range n, pj b0 j ≤ Zres b0 n Q y := by
  obtain ⟨y, -, hy⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
    (f := fun _ => 2 / 3 * ∏ j ∈ range n, pj b0 j) (g := Zres b0 n Q) (by
      rw [sum_Zres b0 n hQ, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      push_cast; exact le_rfl)
  exact ⟨y, hy⟩

/-! ## Lemma 8.6 -/

/-- `q₁ = G (200/201)^6`. -/
def q1 : ℝ := Gc * (200 / 201) ^ 6

/-- `q₂ = G 2^{-1/10}`. -/
def q2 : ℝ := Gc * 2 ^ (-(1 / 10 : ℝ))

lemma q1_nonneg : 0 ≤ q1 := by unfold q1 Gc; norm_num

lemma q1_lt_one : q1 < 1 := by unfold q1 Gc; norm_num

lemma two_rpow_neg_tenth_pow_ten : ((2 : ℝ) ^ (-(1 / 10 : ℝ))) ^ 10 = 1 / 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num [Real.rpow_neg_one]

lemma q2_nonneg : 0 ≤ q2 := by unfold q2 Gc; positivity

/-- `q₂ < 1`, since `G^{10} < 2`. -/
lemma q2_lt_one : q2 < 1 := by
  apply lt_of_pow_lt_pow_left₀ 10 (by norm_num : (0 : ℝ) ≤ 1)
  unfold q2
  rw [mul_pow, two_rpow_neg_tenth_pow_ten]
  unfold Gc; norm_num

lemma rpow_neg_six_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (-6 : ℝ) = 1 / x ^ 6 := by
  rw [Real.rpow_neg hx, one_div]; norm_cast

/-- `G^n 2^{-K_n-1} ≤ q₂^n`. -/
lemma Gc_pow_mul_half_pow_le (n : ℕ) : Gc ^ n * (1 / 2) ^ (Kseq n + 1) ≤ q2 ^ n := by
  unfold q2
  rw [mul_pow]
  have hG : 0 ≤ Gc ^ n := by unfold Gc; positivity
  apply mul_le_mul_of_nonneg_left _ hG
  have e1 : ((2 : ℝ) ^ (-(1 / 10 : ℝ))) ^ n = (2 : ℝ) ^ (-(1 / 10 : ℝ) * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have e2 : (1 / 2 : ℝ) ^ (Kseq n + 1) = (2 : ℝ) ^ (-((Kseq n + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  rw [e1, e2]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (n : ℝ) < 10 * ((Kseq n + 1 : ℕ) : ℝ) := by
    have h : n < 10 * (Kseq n + 1) := by unfold Kseq; omega
    exact_mod_cast h
  linarith

/-- `b_n^{-6} ≤ ((200/201)^6)^n` once `b_0 ≥ 200`. -/
lemma inv_bseq_pow_six_le {b0 : ℕ} (hb0 : 200 ≤ b0) (n : ℕ) :
    1 / (bseq b0 n : ℝ) ^ 6 ≤ ((200 / 201 : ℝ) ^ 6) ^ n := by
  have hl := bseq_lower hb0 n
  have hb : (1 : ℝ) ≤ b0 := by exact_mod_cast (show 1 ≤ b0 by omega)
  have h1 : (201 / 200 : ℝ) ^ n ≤ bseq b0 n :=
    le_trans (le_mul_of_one_le_left (by positivity) hb) hl
  have h2 : ((201 / 200 : ℝ) ^ n) ^ 6 ≤ (bseq b0 n : ℝ) ^ 6 := pow_le_pow_left₀ (by positivity) h1 6
  have e : ((200 / 201 : ℝ) ^ 6) ^ n * ((201 / 200 : ℝ) ^ n) ^ 6 = 1 := by
    rw [← pow_mul, ← pow_mul, mul_comm 6 n, ← mul_pow]; norm_num
  have hbpos : (0 : ℝ) < (bseq b0 n : ℝ) ^ 6 := by
    have : (0 : ℝ) < bseq b0 n := lt_of_lt_of_le (by positivity) h1
    positivity
  rw [div_le_iff₀ hbpos]
  calc (1 : ℝ) = ((200 / 201 : ℝ) ^ 6) ^ n * ((201 / 200 : ℝ) ^ n) ^ 6 := e.symm
    _ ≤ ((200 / 201 : ℝ) ^ 6) ^ n * (bseq b0 n : ℝ) ^ 6 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `k_m^{-6} ≤ 8^6 ((200/201)^6)^n` for `m ≥ n`. -/
lemma kseq_rpow_le {b0 : ℕ} (hb0 : 200 ≤ b0) {n m : ℕ} (hm : n ≤ m) :
    (kseq b0 m : ℝ) ^ (-6 : ℝ) ≤ 8 ^ 6 * ((200 / 201 : ℝ) ^ 6) ^ n := by
  have hbn : 200 ≤ bseq b0 n := hb0.trans (le_bseq b0 n)
  have hbm : bseq b0 n ≤ bseq b0 m := bseq_mono b0 hm
  have h8 : bseq b0 n ≤ 8 * kseq b0 m := by unfold kseq; omega
  have hk : (0 : ℝ) < kseq b0 m := by
    have : 1 ≤ kseq b0 m := by unfold kseq; omega
    exact_mod_cast this
  have hb : (0 : ℝ) < bseq b0 n := by exact_mod_cast (show 0 < bseq b0 n by omega)
  have h8' : (bseq b0 n : ℝ) ≤ 8 * kseq b0 m := by exact_mod_cast h8
  rw [rpow_neg_six_eq hk.le]
  have h1 : 1 / (kseq b0 m : ℝ) ^ 6 ≤ 8 ^ 6 * (1 / (bseq b0 n : ℝ) ^ 6) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc (bseq b0 n : ℝ) ^ 6 ≤ (8 * kseq b0 m) ^ 6 := pow_le_pow_left₀ hb.le h8' 6
      _ = 8 ^ 6 * (kseq b0 m : ℝ) ^ 6 := by ring
  exact h1.trans (mul_le_mul_of_nonneg_left (inv_bseq_pow_six_le hb0 n) (by norm_num))

/-- `(4b + 4) exp(-⌈b^{3/5}⌉²/(576 b)) ≤ C/b^6`, from `e^y ≥ y^{40}/40!` and
`⌈b^{3/5}⌉^5 ≥ b^3`. -/
lemma rejection_term_le_six {b : ℕ} (hb : 1 ≤ b) :
    (4 * b + 4 : ℝ) * Real.exp (-((mB b : ℝ) ^ 2) / (576 * b)) ≤
      8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40) / (b : ℝ) ^ 6 := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by linarith
  set y : ℝ := (mB b : ℝ) ^ 2 / (576 * b) with hy
  have hy0 : 0 ≤ y := by positivity
  have hexp := Real.pow_div_factorial_le_exp y hy0 40
  have hm : (b : ℝ) ^ 48 ≤ (mB b : ℝ) ^ 80 := by
    have h := Nat.pow_le_pow_left (pow_three_le_mB_pow_five b) 16
    rw [← pow_mul, ← pow_mul] at h
    exact_mod_cast h
  have hy40 : (b : ℝ) ^ 8 / 576 ^ 40 ≤ y ^ 40 := by
    rw [hy, div_pow, mul_pow, ← pow_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (b : ℝ) ^ 8 * (576 ^ 40 * (b : ℝ) ^ 40) = 576 ^ 40 * (b : ℝ) ^ 48 := by ring
    rw [this, show (mB b : ℝ) ^ (2 * 40) = (mB b : ℝ) ^ 80 by norm_num]
    nlinarith
  have hF : (0 : ℝ) < Nat.factorial 40 := by exact_mod_cast Nat.factorial_pos 40
  have hlow : (b : ℝ) ^ 8 / (576 ^ 40 * Nat.factorial 40) ≤ Real.exp y := by
    calc (b : ℝ) ^ 8 / (576 ^ 40 * Nat.factorial 40)
        = ((b : ℝ) ^ 8 / 576 ^ 40) / Nat.factorial 40 := by rw [div_div]
      _ ≤ y ^ 40 / Nat.factorial 40 := by gcongr
      _ ≤ Real.exp y := hexp
  have hneg : -((mB b : ℝ) ^ 2) / (576 * b) = -y := by rw [hy, neg_div]
  rw [hneg, Real.exp_neg]
  have hpos2 : 0 < (b : ℝ) ^ 8 / (576 ^ 40 * Nat.factorial 40) := by positivity
  have hinv : (Real.exp y)⁻¹ ≤ (576 ^ 40 * Nat.factorial 40) / (b : ℝ) ^ 8 := by
    rw [← inv_div]; exact inv_anti₀ hpos2 hlow
  calc (4 * b + 4 : ℝ) * (Real.exp y)⁻¹
      ≤ (8 * b) * ((576 ^ 40 * Nat.factorial 40) / (b : ℝ) ^ 8) :=
        mul_le_mul (by linarith) hinv (by positivity) (by positivity)
    _ = 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40) / (b : ℝ) ^ 7 := by field_simp
    _ ≤ 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40) / (b : ℝ) ^ 6 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_right₀ hb' (by norm_num))

/-- `1 - p_n ≤ D ((200/201)^6)^n + 2^{-K_n-1}` (Lemma 8.4 with the rejection term absorbed). -/
lemma one_sub_pj_le {b0 : ℕ} (hb0 : 200 ≤ b0) (n : ℕ) :
    1 - pj b0 n ≤ 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40) * ((200 / 201 : ℝ) ^ 6) ^ n +
      (1 / 2) ^ (Kseq n + 1) := by
  have hbn : 200 ≤ bseq b0 n := hb0.trans (le_bseq b0 n)
  have h1 := one_sub_pmass_central_le (b := bseq b0 n) (by omega) (Kseq n)
  have h2 := rejection_term_le_six (b := bseq b0 n) (by omega)
  have h3 := inv_bseq_pow_six_le hb0 n
  have h4 : 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40) / (bseq b0 n : ℝ) ^ 6 ≤
      8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40) * ((200 / 201 : ℝ) ^ 6) ^ n := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  unfold pj
  linarith

/-- The function paired with the histogram in the generation step:
`g = ∑_{w ∈ V_{b_n,K_n}} T_{w,Q} ρ_{k_{n+1}} - lift(ρ_{k_n})` on `G_Q`, `Q = h_{b_n} + k_{n+1}`. -/
def cauchyDiff (b0 n : ℕ) (y : ZMod (3 ^ (hB (bseq b0 n) + kseq b0 (n + 1)))) : ℝ :=
  ∑ w ∈ central (bseq b0 n) (Kseq n),
    TwQ (hB (bseq b0 n) + kseq b0 (n + 1)) (kseq b0 (n + 1)) w (rhoX (kseq b0 (n + 1))) y -
      rhoX (kseq b0 n) (ZMod.cast y)

/-- **Removing the last block:** `Z_{n+1}(M) - Z_n(M) = ∑_y 𝓗_{n,Q}(y) g(y)`. -/
theorem Zmark_succ_sub (b0 : ℕ) {M : ℕ} (hM : Odd M) (n : ℕ) :
    Zmark b0 M (n + 1) - Zmark b0 M n =
      ∑ y, histo b0 M n (hB (bseq b0 n) + kseq b0 (n + 1)) y * cauchyDiff b0 n y := by
  rw [sum_histo_mul]
  unfold Zmark cauchyDiff
  rw [sum_hist_succ hM n (kseq b0 (n + 1)) (rhoX (kseq b0 (n + 1))), ← Finset.sum_sub_distrib]
  have hk : kseq b0 n ≤ hB (bseq b0 n) + kseq b0 (n + 1) := by unfold kseq hB; omega
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [mul_sub]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [TwQ_natCast (Q := hB (bseq b0 n) + kseq b0 (n + 1)) (t := kseq b0 (n + 1)) (w := w)
      (by have := central_length_le hw; omega)]
  · rw [ZMod.cast_natCast (pow_dvd_pow 3 hk)]

/-- **Lemma 8.6 [`lem:D1`]**, (8.9, `eq:D1`): with `A = 6` in (8.1),
`|Z_{n+1}(M) - Z_n(M)| ≤ C_{b_0} (n+1)^3 [q₁^n + q₂^n] + C_{b_0} b_n^{-6}`, uniformly in odd seeds
`M ≥ 16^{b_0}`. (The `k_n^{-6}`, `k_{n+1}^{-6}` and rejection terms are bounded by multiples of
`q₁^n`, so the `b_n^{-6}` term is not needed; it is kept to match (8.9).) -/
theorem uniform_cauchy (hA1 : OffsetMixing) : ∃ b₁ : ℕ, ∀ b0 ≥ b₁, ∃ C : ℝ, ∀ M : ℕ, Odd M →
    16 ^ b0 ≤ M → ∀ n : ℕ, |Zmark b0 M (n + 1) - Zmark b0 M n| ≤
      C * (n + 1) ^ 3 * (q1 ^ n + q2 ^ n) + C * (bseq b0 n : ℝ) ^ (-6 : ℝ) := by
  obtain ⟨b₂, hHP⟩ := histogram_pairing
  obtain ⟨C6, hTC⟩ := transfer_comparison hA1 (A := 6) (by norm_num)
  refine ⟨max b₂ 200, fun b0 hb0 => ?_⟩
  have hb2 : b₂ ≤ b0 := le_of_max_le_left hb0
  have hb200 : 200 ≤ b0 := le_of_max_le_right hb0
  obtain ⟨CH, hCH⟩ := hHP b0 hb2
  refine ⟨max CH 0 * (2 / 3) * (2 * max C6 0 * 8 ^ 6 +
      8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40) + 1), fun M hM hM16 n => ?_⟩
  have hbn : 200 ≤ bseq b0 n := hb200.trans (le_bseq b0 n)
  rw [Zmark_succ_sub b0 hM n]
  have hq : hB (bseq b0 n) + kseq b0 (n + 1) ≤ 2 * bseq b0 n := by
    unfold hB wB kseq; rw [bseq_succ]; omega
  have h1 := hCH M n _ hM hM16 hq (cauchyDiff b0 n)
  have hk1 : 1 ≤ kseq b0 n := by unfold kseq; omega
  have hkk : kseq b0 n ≤ kseq b0 (n + 1) := by unfold kseq; rw [bseq_succ]; omega
  have h2 : normL1 (hB (bseq b0 n) + kseq b0 (n + 1)) (cauchyDiff b0 n) ≤
      2 / 3 * (C6 * (kseq b0 (n + 1) : ℝ) ^ (-(6 : ℝ)) + C6 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) +
        (1 - pj b0 n)) :=
    hTC (central (bseq b0 n) (Kseq n)) (hB (bseq b0 n)) (kseq b0 (n + 1)) (kseq b0 n)
      (central_prefixFree _ _) (fun w hw => ⟨central_pos hw, central_length_le hw⟩)
      (hk1.trans hkk) hk1 (by unfold hB kseq; omega)
  -- the real arithmetic
  have hN0 := normL1_nonneg _ (cauchyDiff b0 n)
  have ha := kseq_rpow_le hb200 (show n ≤ n + 1 by omega)
  have hc := kseq_rpow_le hb200 (le_refl n)
  have ha0 : 0 ≤ (kseq b0 (n + 1) : ℝ) ^ (-(6 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hc0 : 0 ≤ (kseq b0 n : ℝ) ^ (-(6 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hp := one_sub_pj_le hb200 n
  have hC60 : (0 : ℝ) ≤ max C6 0 := le_max_right _ _
  have hCa : C6 * (kseq b0 (n + 1) : ℝ) ^ (-(6 : ℝ)) ≤
      max C6 0 * (8 ^ 6 * ((200 / 201 : ℝ) ^ 6) ^ n) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) ha0).trans (mul_le_mul_of_nonneg_left ha hC60)
  have hCc : C6 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) ≤
      max C6 0 * (8 ^ 6 * ((200 / 201 : ℝ) ^ 6) ^ n) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hc0).trans (mul_le_mul_of_nonneg_left hc hC60)
  have hN : normL1 (hB (bseq b0 n) + kseq b0 (n + 1)) (cauchyDiff b0 n) ≤
      2 / 3 * ((2 * max C6 0 * 8 ^ 6 + 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40)) *
        ((200 / 201 : ℝ) ^ 6) ^ n + (1 / 2) ^ (Kseq n + 1)) := by
    refine h2.trans ?_
    have : C6 * (kseq b0 (n + 1) : ℝ) ^ (-(6 : ℝ)) + C6 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) +
        (1 - pj b0 n) ≤ (2 * max C6 0 * 8 ^ 6 + 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40)) *
          ((200 / 201 : ℝ) ^ 6) ^ n + (1 / 2) ^ (Kseq n + 1) := by nlinarith
    linarith
  have hGn : 0 ≤ Gc ^ n := by unfold Gc; positivity
  have hq1n : Gc ^ n * ((200 / 201 : ℝ) ^ 6) ^ n = q1 ^ n := by unfold q1; rw [mul_pow]
  have hq2n := Gc_pow_mul_half_pow_le n
  have hGN : Gc ^ n * normL1 (hB (bseq b0 n) + kseq b0 (n + 1)) (cauchyDiff b0 n) ≤
      2 / 3 * ((2 * max C6 0 * 8 ^ 6 + 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40)) * q1 ^ n +
        q2 ^ n) := by
    calc Gc ^ n * normL1 (hB (bseq b0 n) + kseq b0 (n + 1)) (cauchyDiff b0 n)
        ≤ Gc ^ n * (2 / 3 * ((2 * max C6 0 * 8 ^ 6 + 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40)) *
          ((200 / 201 : ℝ) ^ 6) ^ n + (1 / 2) ^ (Kseq n + 1))) :=
          mul_le_mul_of_nonneg_left hN hGn
      _ = 2 / 3 * ((2 * max C6 0 * 8 ^ 6 + 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40)) *
          (Gc ^ n * ((200 / 201 : ℝ) ^ 6) ^ n) + Gc ^ n * (1 / 2) ^ (Kseq n + 1)) := by ring
      _ ≤ _ := by rw [hq1n]; linarith
  have hn3 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
  have hCH0 : (0 : ℝ) ≤ max CH 0 := le_max_right _ _
  have hq1 : 0 ≤ q1 ^ n := pow_nonneg q1_nonneg n
  have hq2 : 0 ≤ q2 ^ n := pow_nonneg q2_nonneg n
  have hD : (0 : ℝ) ≤ 2 * max C6 0 * 8 ^ 6 + 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40) := by
    positivity
  have hb6 : (0 : ℝ) ≤ (bseq b0 n : ℝ) ^ (-6 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hfin : max CH 0 * (((n : ℝ) + 1) ^ 3 * (Gc ^ n *
      normL1 (hB (bseq b0 n) + kseq b0 (n + 1)) (cauchyDiff b0 n))) ≤
      max CH 0 * (2 / 3) * (2 * max C6 0 * 8 ^ 6 + 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40) + 1) *
        (n + 1) ^ 3 * (q1 ^ n + q2 ^ n) := by
    have h3 : ((n : ℝ) + 1) ^ 3 * (Gc ^ n *
        normL1 (hB (bseq b0 n) + kseq b0 (n + 1)) (cauchyDiff b0 n)) ≤
        ((n : ℝ) + 1) ^ 3 * (2 / 3 * ((2 * max C6 0 * 8 ^ 6 +
          8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40)) * q1 ^ n + q2 ^ n)) :=
      mul_le_mul_of_nonneg_left hGN hn3
    have h4 : (2 * max C6 0 * 8 ^ 6 + 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40)) * q1 ^ n + q2 ^ n ≤
        (2 * max C6 0 * 8 ^ 6 + 8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40) + 1) * (q1 ^ n + q2 ^ n) := by
      nlinarith
    calc max CH 0 * (((n : ℝ) + 1) ^ 3 * (Gc ^ n *
          normL1 (hB (bseq b0 n) + kseq b0 (n + 1)) (cauchyDiff b0 n)))
        ≤ max CH 0 * (((n : ℝ) + 1) ^ 3 * (2 / 3 * ((2 * max C6 0 * 8 ^ 6 +
          8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40)) * q1 ^ n + q2 ^ n))) :=
          mul_le_mul_of_nonneg_left h3 hCH0
      _ ≤ max CH 0 * (((n : ℝ) + 1) ^ 3 * (2 / 3 * ((2 * max C6 0 * 8 ^ 6 +
          8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40) + 1) * (q1 ^ n + q2 ^ n)))) := by
          gcongr
      _ = _ := by ring
  have hC0 : 0 ≤ max CH 0 * (2 / 3) * (2 * max C6 0 * 8 ^ 6 +
      8 * ((Nat.factorial 40 : ℝ) * 576 ^ 40) + 1) := by positivity
  calc |∑ y, histo b0 M n (hB (bseq b0 n) + kseq b0 (n + 1)) y * cauchyDiff b0 n y|
      ≤ CH * (n + 1) ^ 3 * Gc ^ n * normL1 (hB (bseq b0 n) + kseq b0 (n + 1)) (cauchyDiff b0 n) :=
        h1
    _ ≤ max CH 0 * (((n : ℝ) + 1) ^ 3 * (Gc ^ n *
          normL1 (hB (bseq b0 n) + kseq b0 (n + 1)) (cauchyDiff b0 n))) := by
        rw [show CH * (n + 1) ^ 3 * Gc ^ n *
          normL1 (hB (bseq b0 n) + kseq b0 (n + 1)) (cauchyDiff b0 n) = CH * (((n : ℝ) + 1) ^ 3 *
            (Gc ^ n * normL1 (hB (bseq b0 n) + kseq b0 (n + 1)) (cauchyDiff b0 n))) by ring]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ _ := hfin
    _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hC0 hb6)

/-! ## The favourable residue -/

lemma summable_cube_geom {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 3 * q ^ n) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one 3 (r := q)
    (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  have hg := summable_geometric_of_lt_one h0 h1
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((hs.mul_left 8).add hg)
  have hq : 0 ≤ q ^ n := pow_nonneg h0 n
  have hn : ((n : ℝ) + 1) ^ 3 ≤ 8 * (n : ℝ) ^ 3 + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have h3 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith
      nlinarith
  calc ((n : ℝ) + 1) ^ 3 * q ^ n ≤ (8 * (n : ℝ) ^ 3 + 1) * q ^ n :=
        mul_le_mul_of_nonneg_right hn hq
    _ = 8 * ((n : ℝ) ^ 3 * q ^ n) + q ^ n := by ring

/-- **The favourable seed residue** (§8.3, the unlabelled paragraph after Lemma 8.6): there are
`p > 0`, a generation `n⋆`, a modulus `3^Q` and a residue `y` such that `Z_n(M) ≥ p` for every
`n ≥ n⋆` and every odd seed `M ≥ 16^{b_0}` with `M ≡ y (mod 3^Q)`. (The paper's `z(M) ≥ p_∞/3`;
here `p` is a third of a lower bound for the partial products of the `p_j`, and there is no
limit.) -/
theorem favourable_residue (hA1 : OffsetMixing) : ∃ b₁ : ℕ, ∀ b0 ≥ b₁,
    ∃ (p : ℝ) (nst Q : ℕ) (y : ZMod (3 ^ Q)), 0 < p ∧ ∀ M : ℕ, Odd M → 16 ^ b0 ≤ M →
      (M : ZMod (3 ^ Q)) = y → ∀ n ≥ nst, p ≤ Zmark b0 M n := by
  obtain ⟨b₂, hUC⟩ := uniform_cauchy hA1
  obtain ⟨b₃, hBR⟩ := block_rejection_prod
  refine ⟨max (max b₂ b₃) 200, fun b0 hb0 => ?_⟩
  have hb2 : b₂ ≤ b0 := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hb0)
  have hb3 : b₃ ≤ b0 := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hb0)
  have hb200 : 200 ≤ b0 := le_trans (le_max_right _ _) hb0
  obtain ⟨C, hC⟩ := hUC b0 hb2
  obtain ⟨-, p, hp, hprod⟩ := hBR b0 hb3
  -- the bound (8.9), with a nonnegative constant and `b_n^{-6} ≤ ((200/201)^6)^n`
  have hC0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hbound : ∀ M : ℕ, Odd M → 16 ^ b0 ≤ M → ∀ n : ℕ,
      |Zmark b0 M (n + 1) - Zmark b0 M n| ≤ max C 0 * (((n : ℝ) + 1) ^ 3 * (q1 ^ n + q2 ^ n) +
        ((200 / 201 : ℝ) ^ 6) ^ n) := by
    intro M hM hM16 n
    have h := hC M hM hM16 n
    have hX : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 * (q1 ^ n + q2 ^ n) := by
      have := pow_nonneg q1_nonneg n; have := pow_nonneg q2_nonneg n; positivity
    have hb : 0 < (bseq b0 n : ℝ) := by
      exact_mod_cast (show 0 < bseq b0 n by have := le_bseq b0 n; omega)
    have hY : (bseq b0 n : ℝ) ^ (-6 : ℝ) ≤ ((200 / 201 : ℝ) ^ 6) ^ n := by
      rw [rpow_neg_six_eq hb.le]; exact inv_bseq_pow_six_le hb200 n
    have hY0 : 0 ≤ (bseq b0 n : ℝ) ^ (-6 : ℝ) := Real.rpow_nonneg hb.le _
    calc |Zmark b0 M (n + 1) - Zmark b0 M n|
        ≤ C * (((n : ℝ) + 1) ^ 3 * (q1 ^ n + q2 ^ n)) + C * (bseq b0 n : ℝ) ^ (-6 : ℝ) := by
          have e : C * (n + 1) ^ 3 * (q1 ^ n + q2 ^ n) =
              C * (((n : ℝ) + 1) ^ 3 * (q1 ^ n + q2 ^ n)) := by ring
          rw [← e]; exact h
      _ ≤ max C 0 * (((n : ℝ) + 1) ^ 3 * (q1 ^ n + q2 ^ n)) +
          max C 0 * ((200 / 201 : ℝ) ^ 6) ^ n := by
          exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
            ((mul_le_mul_of_nonneg_right (le_max_left _ _) hY0).trans
              (mul_le_mul_of_nonneg_left hY hC0))
      _ = _ := by ring
  -- its tail
  set e : ℕ → ℝ := fun n => max C 0 * (((n : ℝ) + 1) ^ 3 * (q1 ^ n + q2 ^ n) +
    ((200 / 201 : ℝ) ^ 6) ^ n) with he_def
  have he0 : ∀ n, 0 ≤ e n := fun n => by
    have := pow_nonneg q1_nonneg n; have := pow_nonneg q2_nonneg n
    simp only [he_def]; positivity
  have hes : Summable e := by
    have s1 := summable_cube_geom q1_nonneg q1_lt_one
    have s2 := summable_cube_geom q2_nonneg q2_lt_one
    have s3 := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (200 / 201) ^ 6)
      (by norm_num : ((200 : ℝ) / 201) ^ 6 < 1)
    refine ((s1.add s2).add s3).mul_left (max C 0) |>.congr fun n => ?_
    simp only [he_def]; ring
  obtain ⟨N, hN⟩ := ((tendsto_sum_nat_add e).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < p / 3))).exists
  obtain ⟨y, hy⟩ := exists_Zres_ge b0 N (Q := Qn b0 N) le_rfl
  refine ⟨p / 3, N, Qn b0 N, y, by positivity, fun M hM hM16 hMy n hn => ?_⟩
  have h0 : 2 / 3 * p ≤ Zmark b0 M N := by
    rw [Zmark_eq_Zres b0 hM le_rfl, hMy]
    have := hprod N
    linarith
  have htel : ∀ n ≥ N, Zmark b0 M N - ∑ i ∈ Ico N n, e i ≤ Zmark b0 M n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn]
      have h1 := hbound M hM hM16 n
      have h2 := neg_abs_le (Zmark b0 M (n + 1) - Zmark b0 M n)
      simp only [he_def] at ih ⊢
      linarith
  have hs' : Summable (fun k => e (k + N)) := (summable_nat_add_iff N).mpr hes
  have htail : ∑ i ∈ Ico N n, e i ≤ ∑' k, e (k + N) := by
    rw [Finset.sum_Ico_eq_sum_range]
    calc ∑ k ∈ range (n - N), e (N + k) = ∑ k ∈ range (n - N), e (k + N) :=
          Finset.sum_congr rfl fun k _ => by rw [add_comm]
      _ ≤ ∑' k, e (k + N) := hs'.sum_le_tsum (range (n - N)) (fun k _ => he0 _)
  have := htel n hn
  linarith

end Positivity
end CollatzCLT
