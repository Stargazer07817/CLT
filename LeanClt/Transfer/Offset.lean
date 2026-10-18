import LeanClt.Transfer.Source

/-!
# Offset removal (first half of Lemma 5.7)

`depth_offset`: `depthSum r = ∑_{S ≤ K, |S - 2r| ≤ L^{0.6}} 2^{-S} ∑_{a ∈ words r S}
Gt r S (F_r(a)) + O(Δ)`.

* `depth_window`: replace the true source window `Y ≤ N ≤ 2Y` by the simplified window
  `Y ≤ 2^S U^r(N)/3^r ≤ 2Y`. Since `2^S U^r(N)/3^r = N + 2^S F_r/3^r` with
  `0 ≤ 2^S F_r/3^r ≤ Δ` for a typical word, the two windows disagree only on the sources within
  `Δ` of an endpoint: at most `2Δ + 2` odd integers, and each has a unimodular phase.
* `depthPlus_eq`: with the simplified window, the sum over sources is exactly a sum over words
  and targets: for a fixed word `a`, `N ↦ U^r(N)` is a bijection from the sources with word `a`
  onto the targets `M ≡ F_r(a) (mod 3^r)` in the window (Lemma 2.1).
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-- The odd integers in `[0, 2Y]`. -/
def Tset (Y : ℝ) : Finset ℕ := (range (⌊2 * Y⌋₊ + 1)).filter Odd

lemma mem_Tset {Y : ℝ} (hY : 0 ≤ Y) {N : ℕ} : N ∈ Tset Y ↔ Odd N ∧ (N : ℝ) ≤ 2 * Y := by
  simp only [Tset, mem_filter, mem_range]
  rw [Nat.lt_succ_iff, Nat.le_floor_iff (by linarith)]
  tauto

lemma oddClosed_eq_Tset {Y : ℝ} (hY : 0 ≤ Y) :
    oddClosed Y = (Tset Y).filter (fun N : ℕ => Y ≤ (N : ℝ)) := by
  ext N
  rw [mem_filter, mem_Tset hY]
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := mem_oddClosed hY h
    exact ⟨⟨h1, h3⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    unfold oddClosed
    rw [mem_filter, mem_Icc]
    exact ⟨⟨Nat.ceil_le.mpr h2, Nat.le_floor h3⟩, h1⟩

lemma card_interval_le (T : Finset ℕ) {a b : ℝ} (hb : 0 ≤ b) (hab : a ≤ b + 1) :
    ((T.filter (fun N : ℕ => a ≤ (N : ℝ) ∧ (N : ℝ) ≤ b)).card : ℝ) ≤ b - a + 1 := by
  have hsub : T.filter (fun N : ℕ => a ≤ (N : ℝ) ∧ (N : ℝ) ≤ b) ⊆ Icc ⌈a⌉₊ ⌊b⌋₊ := by
    intro N hN
    rw [mem_filter] at hN
    rw [mem_Icc]
    exact ⟨Nat.ceil_le.mpr hN.2.1, Nat.le_floor hN.2.2⟩
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Icc] at h1
  have h2 : ((⌊b⌋₊ + 1 - ⌈a⌉₊ : ℕ) : ℝ) ≤ b - a + 1 := by
    rcases le_or_gt ⌈a⌉₊ (⌊b⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]; push_cast
      have := Nat.floor_le hb; have := Nat.le_ceil a; linarith
    · rw [Nat.sub_eq_zero_of_le h.le]; simp; linarith
  exact (Nat.cast_le.mpr h1).trans h2

/-- `2^S F_r / 3^r ≤ 2^S / 2^r`, using `F_r ≤ (3/2)^r - 1`. -/
lemma Kint_div_le {a : ℕ → ℕ} (ha : ∀ i, 1 ≤ a i) (r : ℕ) :
    (Kint a r : ℝ) / 3 ^ r ≤ 2 ^ wsum a r / 2 ^ r := by
  have hK : (Kint a r : ℝ) = 2 ^ wsum a r * ((offset a r : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (Kint_cast a r)
    push_cast at this; exact this
  have hF : ((offset a r : ℚ) : ℝ) ≤ (3 / 2 : ℝ) ^ r := by
    have h := (Rat.cast_le (K := ℝ)).mpr (offset_le a ha r)
    push_cast at h; linarith
  rw [hK, div_le_div_iff₀ (by positivity) (by positivity)]
  calc 2 ^ wsum a r * ((offset a r : ℚ) : ℝ) * 2 ^ r ≤ 2 ^ wsum a r * (3 / 2 : ℝ) ^ r * 2 ^ r := by
        gcongr
    _ = 2 ^ wsum a r * 3 ^ r := by rw [mul_assoc, ← mul_pow]; norm_num

lemma two_pow_eq_exp (n : ℕ) : (2 : ℝ) ^ n = Real.exp (n * ell) := by
  rw [Real.exp_nat_mul, ell, Real.exp_log (by norm_num)]

/-- For a typical total at depth `r ≤ n₀`, `2^S/2^r ≤ Δ`. -/
lemma two_pow_div_le_Δ {x : ℝ} {r S : ℕ} (hr : r ≤ n0 x) (hS : typT x r S) :
    (2 : ℝ) ^ S / 2 ^ r ≤ Δx x := by
  rw [two_pow_eq_exp, two_pow_eq_exp, ← Real.exp_sub, Δx]
  apply Real.exp_le_exp.mpr
  have h1 := (abs_le.mp hS).2
  have h2 : (r : ℝ) ≤ n0 x := by exact_mod_cast hr
  have hl := ell_pos
  nlinarith

/-- `2^{S_r} U^r(N)/3^r = N + 2^{S_r} F_r/3^r`. -/
lemma src_plus (N r : ℕ) :
    (2 : ℝ) ^ wsum (vword N) r * (U^[r] N : ℝ) / 3 ^ r = N + (Kint (vword N) r : ℝ) / 3 ^ r := by
  have h := two_pow_mul_U N r
  have h' : (2 : ℝ) ^ wsum (vword N) r * (U^[r] N : ℝ) = 3 ^ r * N + Kint (vword N) r := by
    exact_mod_cast h
  rw [h']; field_simp

open Classical in
/-- The depth sum with the simplified window, over all odd `N ≤ 2Y`. -/
def depthPlus (x Y : ℝ) (E : Finset ℕ) (q : ℕ → ℝ) (ρ η s : ℝ) (r : ℕ) : ℂ :=
  ∑ N ∈ Tset Y, if typT x r (wsum (vword N) r) ∧ U^[r] N ∈ E ∧
      win Y r (wsum (vword N) r) (U^[r] N) then
    phase q ρ η s (U^[r] N) (wsum (vword N) r) r else 0

/-- **Window replacement**: `|depthSum r - depthPlus r| ≤ 2Δ + 2`. -/
theorem depth_window {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y) (E : Finset ℕ)
    (q : ℕ → ℝ) (ρ η s : ℝ) {r : ℕ} (hr : r ≤ n0 x) :
    ‖depthSum x Y E q ρ η s r - depthPlus x Y E q ρ η s r‖ ≤ 2 * Δx x + 2 := by
  classical
  obtain ⟨hx0, -, -, hY0⟩ := large_facts hL hY1
  have hΔ0 : 0 ≤ Δx x := (Real.exp_pos _).le
  set Δ := Δx x
  unfold depthSum depthPlus
  rw [oddClosed_eq_Tset hY0.le, Finset.sum_filter, ← Finset.sum_sub_distrib]
  have hpt : ∀ N ∈ Tset Y,
      ‖(if Y ≤ (N : ℝ) then (if typT x r (wsum (vword N) r) ∧ U^[r] N ∈ E then
          phase q ρ η s (U^[r] N) (wsum (vword N) r) r else 0) else 0) -
        (if typT x r (wsum (vword N) r) ∧ U^[r] N ∈ E ∧
          win Y r (wsum (vword N) r) (U^[r] N) then
          phase q ρ η s (U^[r] N) (wsum (vword N) r) r else 0)‖ ≤
      if (Y - Δ ≤ (N : ℝ) ∧ (N : ℝ) ≤ Y) ∨ (2 * Y - Δ ≤ (N : ℝ) ∧ (N : ℝ) ≤ 2 * Y) then 1 else 0 := by
    intro N hN
    obtain ⟨hNo, hN2⟩ := (mem_Tset hY0.le).mp hN
    by_cases hP : typT x r (wsum (vword N) r) ∧ U^[r] N ∈ E
    · set S := wsum (vword N) r
      have hk0 : 0 ≤ (Kint (vword N) r : ℝ) / 3 ^ r := by positivity
      have hkΔ : (Kint (vword N) r : ℝ) / 3 ^ r ≤ Δ :=
        (Kint_div_le (vword_pos hNo) r).trans (two_pow_div_le_Δ hr hP.1)
      have hplus := src_plus N r
      have hiff : (typT x r S ∧ U^[r] N ∈ E ∧ win Y r S (U^[r] N)) ↔ win Y r S (U^[r] N) :=
        ⟨fun h => h.2.2, fun h => ⟨hP.1, hP.2, h⟩⟩
      simp only [hP, and_self, ↓reduceIte, if_congr hiff rfl rfl]
      unfold win
      by_cases hYN : Y ≤ (N : ℝ)
      · by_cases hw : Y ≤ 2 ^ S * (U^[r] N : ℝ) / 3 ^ r ∧ 2 ^ S * (U^[r] N : ℝ) / 3 ^ r ≤ 2 * Y
        · simp only [hYN, hw, and_self, ↓reduceIte, sub_self, norm_zero]
          split_ifs <;> norm_num
        · have : 2 * Y - Δ ≤ (N : ℝ) := by
            by_contra hc
            apply hw
            constructor <;> linarith
          simp only [hYN, hw, true_and, and_false, ↓reduceIte, sub_zero, norm_phase]
          rw [if_pos (Or.inr ⟨this, hN2⟩)]
      · by_cases hw : Y ≤ 2 ^ S * (U^[r] N : ℝ) / 3 ^ r ∧ 2 ^ S * (U^[r] N : ℝ) / 3 ^ r ≤ 2 * Y
        · have : Y - Δ ≤ (N : ℝ) := by linarith [hw.1]
          simp only [hYN, hw, and_self, ↓reduceIte, zero_sub, norm_neg, norm_phase]
          rw [if_pos (Or.inl ⟨this, by linarith⟩)]
        · simp only [hYN, hw, true_and, and_false, ↓reduceIte, sub_self, norm_zero]
          split_ifs <;> norm_num
    · have h2 : ¬ (typT x r (wsum (vword N) r) ∧ U^[r] N ∈ E ∧
          win Y r (wsum (vword N) r) (U^[r] N)) := fun h => hP ⟨h.1, h.2.1⟩
      simp only [hP, h2, ↓reduceIte, ite_self, sub_self, norm_zero]
      split_ifs <;> norm_num
  calc _ ≤ _ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum hpt
    _ = ((Tset Y).filter (fun N : ℕ => (Y - Δ ≤ (N : ℝ) ∧ (N : ℝ) ≤ Y) ∨
          (2 * Y - Δ ≤ (N : ℝ) ∧ (N : ℝ) ≤ 2 * Y))).card := by
        rw [← Finset.sum_filter]; simp
    _ ≤ ((Tset Y).filter (fun N : ℕ => Y - Δ ≤ (N : ℝ) ∧ (N : ℝ) ≤ Y)).card +
          ((Tset Y).filter (fun N : ℕ => 2 * Y - Δ ≤ (N : ℝ) ∧ (N : ℝ) ≤ 2 * Y)).card := by
        rw [Finset.filter_or]
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ (Y - (Y - Δ) + 1) + (2 * Y - (2 * Y - Δ) + 1) := by
        gcongr
        · exact card_interval_le _ hY0.le (by linarith)
        · exact card_interval_le _ (by linarith) (by linarith)
    _ = 2 * Δ + 2 := by ring

/-! ## The exact word–target form of `depthPlus` -/

lemma wsum_eq_of_word {M r S : ℕ} {w : Fin r → ℕ} (hw : w ∈ words r S)
    (hMw : (fun i : Fin r => vword M i) = w) : wsum (vword M) r = S := by
  rw [mem_words] at hw
  rw [← hw.1, wsum, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => congrFun hMw i

lemma vword_eq_ext {M r : ℕ} {w : Fin r → ℕ} (hMw : (fun i : Fin r => vword M i) = w) :
    ∀ i < r, vword M i = ext w i := by
  intro i hi
  simp only [ext, hi, ↓reduceDIte]
  exact congrFun hMw ⟨i, hi⟩

/-- **Lemma 2.1, existence, in residue form.** An odd `M ≡ F_r(a) (mod 3^r)` has an odd source
with word `a`. -/
lemma source_of_cast {r S M : ℕ} {a : Fin r → ℕ} (ha : a ∈ words r S) (hM : Odd M)
    (hz : (M : ZMod (3 ^ r)) = Fres (ext a) r) :
    ∃ n : ℕ, Odd n ∧ (∀ i < r, vword n i = ext a i) ∧ U^[r] n = M := by
  have hpos : ∀ i, 1 ≤ ext a i := ext_pos (mem_words.mp ha).2
  obtain ⟨k, hk⟩ := dvd_of_cast_Fres hz
  have hK := Kint_cast (ext a) r
  have hq : ((k : ℤ) : ℚ) = 2 ^ wsum (ext a) r * ((M : ℚ) - offset (ext a) r) / 3 ^ r := by
    have hk' : ((2 ^ wsum (ext a) r * (M : ℤ) - Kint (ext a) r : ℤ) : ℚ) =
        (((3 ^ r : ℕ) : ℤ) * k : ℤ) := by rw [hk]
    push_cast at hk'
    rw [hK] at hk'
    field_simp
    linarith
  obtain ⟨n, -, hno, hpre, hU⟩ := source_exists hpos hM hq
  exact ⟨n, hno, hpre, hU⟩

lemma words_disjoint (r K : ℕ) :
    (↑(range (K + 1)) : Set ℕ).PairwiseDisjoint (fun S => words r S) := by
  intro S _ S' _ hSS'
  rw [Function.onFun, Finset.disjoint_left]
  intro w hw hw'
  rw [mem_words] at hw hw'
  exact hSS' (hw.1.symm.trans hw'.1)

open Classical in
/-- **The word–target form.** With the simplified window, the depth sum is exactly
`∑_{S ≤ K typical} 2^{-S} ∑_{a ∈ words r S} Gt r S (F_r(a))`. -/
theorem depthPlus_eq {x Y : ℝ} (hY0 : 0 ≤ Y) (E : Finset ℕ) (hEo : ∀ M ∈ E, Odd M)
    (q : ℕ → ℝ) (ρ η s : ℝ) {r : ℕ} (hr : r ≤ n0 x) {K : ℕ} (hK : 2 * Y * 3 ^ n0 x < 2 ^ K) :
    depthPlus x Y E q ρ η s r = ∑ S ∈ range (K + 1), if typT x r S then
      (1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r) else 0 := by
  unfold depthPlus
  rw [← Finset.sum_filter]
  set w : ℕ → (Fin r → ℕ) := fun N i => vword N i with hw
  have hmaps : ∀ N ∈ (Tset Y).filter (fun N : ℕ => typT x r (wsum (vword N) r) ∧ U^[r] N ∈ E ∧
      win Y r (wsum (vword N) r) (U^[r] N)),
      w N ∈ (range (K + 1)).biUnion (fun S => words r S) := by
    intro N hN
    rw [mem_filter] at hN
    obtain ⟨hNT, -, -, hwin⟩ := hN
    obtain ⟨hNo, -⟩ := (mem_Tset hY0).mp hNT
    rw [mem_biUnion]
    refine ⟨wsum (vword N) r, ?_, ?_⟩
    · have hU1 : (1 : ℝ) ≤ U^[r] N := by exact_mod_cast (odd_U_iterate hNo r).pos
      have h2 := hwin.2
      rw [div_le_iff₀ (by positivity)] at h2
      have h3 : (3 : ℝ) ^ r ≤ 3 ^ n0 x := pow_le_pow_right₀ (by norm_num) hr
      have h4 : (2 : ℝ) ^ wsum (vword N) r < 2 ^ K := by
        have : (2 : ℝ) ^ wsum (vword N) r ≤ 2 ^ wsum (vword N) r * U^[r] N :=
          le_mul_of_one_le_right (by positivity) hU1
        nlinarith
      have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h4
      rw [mem_range]; omega
    · rw [mem_words]
      refine ⟨?_, fun i => vword_pos hNo i⟩
      rw [wsum, ← Fin.sum_univ_eq_sum_range]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_biUnion (words_disjoint r K)]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs with hT
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hRHS : (1 / 2 : ℂ) ^ S * Gt Y E q ρ η s r S (Fres (ext a) r) =
        ∑ M ∈ E.filter (fun M : ℕ => (M : ZMod (3 ^ r)) = Fres (ext a) r ∧ win Y r S M),
          phase q ρ η s M S r := by
      unfold Gt
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun M _ => ?_
      split_ifs
      · rw [← mul_assoc, ← mul_pow]; norm_num
      · simp
    rw [hRHS]
    apply Finset.sum_bij (fun N _ => U^[r] N)
    · intro N hN
      rw [mem_filter, mem_filter] at hN
      obtain ⟨⟨-, -, hE', hwin⟩, hwa⟩ := hN
      have hS := wsum_eq_of_word ha hwa
      rw [mem_filter]
      refine ⟨hE', ?_, ?_⟩
      · rw [U_cast_Fres, Fres_congr (vword_eq_ext hwa)]
      · rw [← hS]; exact hwin
    · intro N1 h1 N2 h2 heq
      rw [mem_filter] at h1 h2
      apply source_unique (r := r) _ heq
      intro i hi
      rw [vword_eq_ext h1.2 i hi, vword_eq_ext h2.2 i hi]
    · intro M hM
      rw [mem_filter] at hM
      obtain ⟨hME, hz, hwin⟩ := hM
      obtain ⟨n, hno, hpre, hU⟩ := source_of_cast ha (hEo M hME) hz
      have hwn : w n = a := by
        funext i
        rw [hw]
        simp only
        rw [hpre i i.isLt]
        simp [ext]
      have hSn := wsum_eq_of_word ha hwn
      refine ⟨n, ?_, hU⟩
      rw [mem_filter, mem_filter]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hwn⟩
      · rw [mem_Tset hY0]
        refine ⟨hno, ?_⟩
        have hp := src_plus n r
        rw [hSn, hU] at hp
        have : (0 : ℝ) ≤ (Kint (vword n) r : ℝ) / 3 ^ r := by positivity
        linarith [hwin.2]
      · rw [hSn]; exact hT
      · rw [hU]; exact hME
      · rw [hSn, hU]; exact hwin
    · intro N hN
      rw [mem_filter] at hN
      rw [wsum_eq_of_word ha hN.2]
  · refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun N hN => ?_
    rw [mem_filter, mem_filter] at hN
    exfalso
    apply hT
    rw [← wsum_eq_of_word ha hN.2]
    exact hN.1.2.1

open Classical in
/-- **Offset removal (Lemma 5.7, first half).** -/
theorem depth_offset {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y) (E : Finset ℕ)
    (hEo : ∀ M ∈ E, Odd M) (q : ℕ → ℝ) (ρ η s : ℝ) {r : ℕ} (hr : r ≤ n0 x) {K : ℕ}
    (hK : 2 * Y * 3 ^ n0 x < 2 ^ K) :
    ‖depthSum x Y E q ρ η s r - ∑ S ∈ range (K + 1), if typT x r S then
      (1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r) else 0‖ ≤
        2 * Δx x + 2 := by
  obtain ⟨-, -, -, hY0⟩ := large_facts hL hY1
  rw [← depthPlus_eq hY0.le E hEo q ρ η s hr hK]
  exact depth_window hL hY1 E q ρ η s hr

end CollatzCLT
