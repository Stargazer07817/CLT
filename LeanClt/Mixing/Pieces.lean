import LeanClt.Mixing.Weighted

/-!
# §3.2: the pieces of the near-diagonal estimate

Fix a prefix event `D ⊆ words p l` (Imported Theorem 2.4, `imp:prefix`) and write `n = p + q`.

* `gP n p D s y = P(S_n = s, X_n = y, (a₁…a_p) ∈ D)`, the piece `g_{p,l}` of `μ_n`;
  `sum_gP_le_muJ`: prefix-disjoint pieces sum to at most `μ_n` pointwise;
  `tsum_gP`: the mass of a piece is `|D| 2^{-l}`.
* `fourierZ_gP`: **exact factorisation** of one counter slice,
  `ĝ_s(ξ) = P̂_{p,l}(ξ) · T_s(ξ)` with `T_s(ξ) = E[1{S'_q = s - l} χ_ξ(3^p 2^{-l} X̃'_q)]`
  (`tailT`). This is (3.4, `eq:factor`) with the counter resolved: there is no phase `e^{itl}`.
* `piece_slice_bound`: if `|T_s(ξ)| ≤ β` at every excluded frequency, then
  `∑_y |g_s - Q_m g_s| ≤ β √(3^n 2^{-l})` — Plancherel (`l2_sub_Qs_le`), the collision bound
  `∑_y P_{p,l}(y)² ≤ 2^{-l}` from separation (part of (2.7, `eq:collision`)), and
  Cauchy–Schwarz over `y`.
* `tail_char_reduce`: an excluded frequency `ξ` (`3^m ξ ≠ 0`) turns the tail character into a
  character of conductor `3^r` with `r > m - p`, applied to the reduction of `X̃'_q`.
* `Qop_add_sum`, `Qop_mass`, `Qop_nonneg_of`: linearity, mass preservation and positivity of `Q_m`.
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-! ## The operator `Q_m` on general functions -/

lemma Qop_add_sum {n m : ℕ} {ι : Type*} (I : Finset ι) (a : ℕ → ZMod (3 ^ n) → ℝ)
    (b : ι → ℕ → ZMod (3 ^ n) → ℝ) (s : ℕ) (x : ZMod (3 ^ n)) :
    Qop n m (fun s y => a s y + ∑ i ∈ I, b i s y) s x =
      Qop n m a s x + ∑ i ∈ I, Qop n m (b i) s x := by
  unfold Qop
  have e : ∀ y : ZMod (3 ^ n), (if (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast x then
      a s y + ∑ i ∈ I, b i s y else 0) =
      (if (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast x then a s y else 0) +
        ∑ i ∈ I, (if (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast x then b i s y else 0) := by
    intro y; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_add_distrib, mul_add, Finset.sum_comm]
  congr 1
  exact Finset.mul_sum _ _ _

/-- `Q_m` preserves the mass of every counter slice. -/
lemma Qop_mass {n m : ℕ} (h : m ≤ n) (ν : ℕ → ZMod (3 ^ n) → ℝ) (s : ℕ) :
    ∑ x : ZMod (3 ^ n), Qop n m ν s x = ∑ y : ZMod (3 ^ n), ν s y := by
  classical
  unfold Qop
  rw [← Finset.mul_sum, Finset.sum_comm]
  have e : ∀ y : ZMod (3 ^ n), (∑ x : ZMod (3 ^ n),
      if (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast x then ν s y else 0) =
      ((3 ^ (n - m) : ℕ) : ℝ) * ν s y := by
    intro y
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 2
    rw [← card_cast_fiber h (ZMod.cast y)]
    congr 1; ext x; simp [eq_comm]
  rw [Finset.sum_congr rfl (fun y _ => e y), ← Finset.mul_sum, ← mul_assoc,
    zpow_mul_three_pow h, one_mul]

lemma Qop_nonneg_of {n m : ℕ} {ν : ℕ → ZMod (3 ^ n) → ℝ} {s : ℕ} (hν : ∀ y, 0 ≤ ν s y)
    (x : ZMod (3 ^ n)) : 0 ≤ Qop n m ν s x := by
  unfold Qop
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => by
    split_ifs
    · exact hν y
    · exact le_rfl)

lemma ofReal_ite_zero (P : Prop) [Decidable P] (a : ℝ) :
    ((if P then a else 0 : ℝ) : ℂ) = if P then (a : ℂ) else 0 := by
  split_ifs <;> simp

/-! ## Pieces -/

/-- The piece `g_{p,l}(s, y) = P(S_n = s, X_n = y, (a₁…a_p) ∈ D)` of `μ_n`. -/
def gP (n p : ℕ) (D : Finset (Fin p → ℕ)) (s : ℕ) (y : ZMod (3 ^ n)) : ℝ :=
  ∑ a ∈ words n s, if h : p ≤ n then
    (if prefixOf h a ∈ D ∧ Xmod a = y then (1 / 2 : ℝ) ^ s else 0) else 0

lemma gP_nonneg (n p : ℕ) (D : Finset (Fin p → ℕ)) (s : ℕ) (y : ZMod (3 ^ n)) :
    0 ≤ gP n p D s y :=
  Finset.sum_nonneg fun a _ => by
    split_ifs
    · positivity
    · exact le_rfl
    · exact le_rfl

lemma prefixOf_prefixOf {p p' n : ℕ} (h1 : p ≤ p') (h2 : p' ≤ n) (a : Fin n → ℕ) :
    prefixOf h1 (prefixOf h2 a) = prefixOf (h1.trans h2) a := rfl

open Classical in
/-- **Prefix-disjoint pieces sum to at most `μ_n`.** -/
lemma sum_gP_le_muJ (n : ℕ) (I : Finset (ℕ × ℕ)) (D : (p : ℕ) → ℕ → Finset (Fin p → ℕ))
    (hdisj : ∀ pl ∈ I, ∀ pl' ∈ I, pl ≠ pl' → ∀ h : pl.1 ≤ pl'.1, ∀ w ∈ D pl'.1 pl'.2,
      prefixOf h w ∉ D pl.1 pl.2) (s : ℕ) (y : ZMod (3 ^ n)) :
    ∑ pl ∈ I, gP n pl.1 (D pl.1 pl.2) s y ≤ muJ n s y := by
  unfold gP muJ
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  set S := I.filter (fun pl => ∃ h : pl.1 ≤ n, prefixOf h a ∈ D pl.1 pl.2) with hSdef
  have hS : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro pl hpl pl' hpl'
    obtain ⟨hplI, h, hmem⟩ := mem_filter.mp hpl
    obtain ⟨hplI', h', hmem'⟩ := mem_filter.mp hpl'
    by_contra hne
    rcases le_total pl.1 pl'.1 with hle | hle
    · exact hdisj pl hplI pl' hplI' hne hle _ hmem' (by rw [prefixOf_prefixOf]; exact hmem)
    · exact hdisj pl' hplI' pl hplI (Ne.symm hne) hle _ hmem (by rw [prefixOf_prefixOf]; exact hmem')
  set c : ℝ := if Xmod a = y then (1 / 2 : ℝ) ^ s else 0 with hc
  have hc0 : 0 ≤ c := by rw [hc]; split_ifs <;> positivity
  have hterm : ∀ pl ∈ I, (if h : pl.1 ≤ n then
      (if prefixOf h a ∈ D pl.1 pl.2 ∧ Xmod a = y then (1 / 2 : ℝ) ^ s else 0) else 0) ≤
      if pl ∈ S then c else 0 := by
    intro pl hpl
    by_cases h : pl.1 ≤ n
    · rw [dif_pos h]
      by_cases hm : prefixOf h a ∈ D pl.1 pl.2
      · have : pl ∈ S := mem_filter.mpr ⟨hpl, h, hm⟩
        rw [if_pos this, hc]
        split_ifs <;> simp_all
      · rw [if_neg (by tauto)]
        split_ifs <;> simp [hc0]
    · rw [dif_neg h]; split_ifs <;> simp [hc0]
  calc _ ≤ ∑ pl ∈ I, (if pl ∈ S then c else 0) := Finset.sum_le_sum hterm
    _ = S.card * c := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr (Finset.filter_subset _ _), Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * c := by gcongr; exact_mod_cast hS
    _ = c := one_mul c

/-- Words of length `p + q` whose first `p` letters lie in `D ⊆ words p l`. -/
lemma sum_words_prefix {β : Type*} [AddCommMonoid β] (p q l s : ℕ) (D : Finset (Fin p → ℕ))
    (hD : D ⊆ words p l) (F : (Fin (p + q) → ℕ) → β) :
    ∑ a ∈ words (p + q) s, (if prefixOf (Nat.le_add_right p q) a ∈ D then F a else 0) =
      if l ≤ s then ∑ u ∈ D, ∑ v ∈ words q (s - l), F (Fin.append u v) else 0 := by
  classical
  rw [sum_words_append p q s]
  simp_rw [prefixOf_append]
  have e : ∀ s1 ∈ range (s + 1), (∑ u ∈ words p s1, ∑ v ∈ words q (s - s1),
      (if u ∈ D then F (Fin.append u v) else 0)) =
      if l = s1 then ∑ u ∈ D, ∑ v ∈ words q (s - l), F (Fin.append u v) else 0 := by
    intro s1 _
    have hfil : (words p s1).filter (· ∈ D) = if l = s1 then D else ∅ := by
      ext u
      simp only [mem_filter]
      split_ifs with hl
      · subst hl; exact ⟨fun h => h.2, fun h => ⟨hD h, h⟩⟩
      · simp only [Finset.notMem_empty, iff_false, not_and]
        intro hu huD
        exact hl ((mem_words.mp (hD huD)).1.symm.trans (mem_words.mp hu).1)
    calc (∑ u ∈ words p s1, ∑ v ∈ words q (s - s1), (if u ∈ D then F (Fin.append u v) else 0))
        = ∑ u ∈ words p s1, (if u ∈ D then ∑ v ∈ words q (s - s1), F (Fin.append u v) else 0) :=
          Finset.sum_congr rfl fun u _ => by split_ifs <;> simp
      _ = ∑ u ∈ (words p s1).filter (· ∈ D), ∑ v ∈ words q (s - s1), F (Fin.append u v) :=
          (Finset.sum_filter _ _).symm
      _ = _ := by
          rw [hfil]
          split_ifs with hl
          · subst hl; rfl
          · rfl
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq]
  by_cases hl : l ≤ s
  · rw [if_pos (mem_range.mpr (by omega)), if_pos hl]
  · rw [if_neg (by rw [mem_range]; omega), if_neg hl]

/-- The slice mass of a piece. -/
lemma sum_gP {n p q l : ℕ} (hn : p + q = n) (D : Finset (Fin p → ℕ)) (hD : D ⊆ words p l)
    (s : ℕ) : ∑ y : ZMod (3 ^ n), gP n p D s y =
      if l ≤ s then (D.card : ℝ) * (1 / 2) ^ l * lawS q (s - l) else 0 := by
  subst hn
  unfold gP
  simp only [dif_pos (Nat.le_add_right p q)]
  rw [Finset.sum_comm]
  have e : ∀ a ∈ words (p + q) s, (∑ y : ZMod (3 ^ (p + q)),
      (if prefixOf (Nat.le_add_right p q) a ∈ D ∧ Xmod a = y then (1 / 2 : ℝ) ^ s else 0)) =
      if prefixOf (Nat.le_add_right p q) a ∈ D then (1 / 2 : ℝ) ^ s else 0 := by
    intro a _
    split_ifs with hu
    · simp [hu]
    · simp [hu]
  rw [Finset.sum_congr rfl e, sum_words_prefix p q l s D hD (fun _ => (1 / 2 : ℝ) ^ s)]
  split_ifs with hl
  · simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← sum_words_half q (s - l), Finset.sum_const, nsmul_eq_mul,
      show (1 / 2 : ℝ) ^ s = (1 / 2) ^ l * (1 / 2) ^ (s - l) by rw [← pow_add]; congr 1; omega]
    ring
  · rfl

/-- **The mass of a piece is `|D| 2^{-l}`.** -/
lemma tsum_gP {n p q l : ℕ} (hn : p + q = n) (D : Finset (Fin p → ℕ)) (hD : D ⊆ words p l) :
    Summable (fun s => ∑ y : ZMod (3 ^ n), gP n p D s y) ∧
      ∑' s, ∑ y : ZMod (3 ^ n), gP n p D s y = (D.card : ℝ) * (1 / 2) ^ l := by
  simp_rw [sum_gP hn D hD]
  set c : ℝ := (D.card : ℝ) * (1 / 2) ^ l
  set f : ℕ → ℝ := fun s => if l ≤ s then c * lawS q (s - l) else 0 with hf
  have hshift : (fun i => f (i + l)) = fun i => c * lawS q i := by
    funext i; simp only [hf, if_pos (Nat.le_add_left l i), Nat.add_sub_cancel]
  have hsf : Summable f := by
    rw [← summable_nat_add_iff l, hshift]; exact (summable_lawS q).mul_left c
  refine ⟨hsf, ?_⟩
  rw [← hsf.sum_add_tsum_nat_add l, hshift, tsum_mul_left, tsum_lawS, mul_one]
  rw [Finset.sum_eq_zero (fun i hi => if_neg (by have := mem_range.mp hi; omega)), zero_add]

/-! ## Exact factorisation of a slice -/

/-- The prefix offset law `P_{p,l}(y) = P(X̃_p ≡ y (3^n), (a₁…a_p) ∈ D)`. -/
def prefLaw (n : ℕ) {p : ℕ} (D : Finset (Fin p → ℕ)) (l : ℕ) (y : ZMod (3 ^ n)) : ℝ :=
  ∑ u ∈ D, if XmodN n u = y then (1 / 2 : ℝ) ^ l else 0

/-- The tail transform `T_s(ξ) = E[1{S'_q = s - l} χ_ξ(3^p 2^{-l} X̃'_q)]` (zero for `s < l`). -/
def tailT (n p q l s : ℕ) (ξ : ZMod (3 ^ n)) : ℂ :=
  if l ≤ s then (1 / 2 : ℂ) ^ (s - l) *
    ∑ v ∈ words q (s - l), chiZ ξ (3 ^ p * half n ^ l * XmodN n v) else 0

lemma fourierZ_prefLaw (n : ℕ) {p : ℕ} (D : Finset (Fin p → ℕ)) (l : ℕ) (ξ : ZMod (3 ^ n)) :
    fourierZ (fun y => (prefLaw n D l y : ℂ)) ξ =
      ∑ u ∈ D, (1 / 2 : ℂ) ^ l * chiZ ξ (XmodN n u) := by
  unfold fourierZ prefLaw
  push_cast
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp_rw [ofReal_ite_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [mul_comm]

/-- **Exact factorisation (3.4, `eq:factor`), counter-resolved.** -/
theorem fourierZ_gP {n p q l : ℕ} (hn : p + q = n) (D : Finset (Fin p → ℕ))
    (hD : D ⊆ words p l) (s : ℕ) (ξ : ZMod (3 ^ n)) :
    fourierZ (fun y => (gP n p D s y : ℂ)) ξ =
      fourierZ (fun y => (prefLaw n D l y : ℂ)) ξ * tailT n p q l s ξ := by
  subst hn
  have hL : fourierZ (fun y => (gP (p + q) p D s y : ℂ)) ξ =
      ∑ a ∈ words (p + q) s, if prefixOf (Nat.le_add_right p q) a ∈ D then
        (1 / 2 : ℂ) ^ s * chiZ ξ (Xmod a) else 0 := by
    unfold fourierZ gP
    simp only [dif_pos (Nat.le_add_right p q)]
    push_cast
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hu : prefixOf (Nat.le_add_right p q) a ∈ D
    · simp only [hu, true_and, if_true]
      simp_rw [ofReal_ite_zero, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq]
      simp [mul_comm]
    · simp [hu]
  rw [hL, sum_words_prefix p q l s D hD, fourierZ_prefLaw]
  unfold tailT
  split_ifs with hl
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hul : (∑ i, u i) = l := (mem_words.mp (hD hu)).1
    rw [Xmod_eq_XmodN, XmodN_append, chiZ_add, hul,
      show (1 / 2 : ℂ) ^ s = (1 / 2) ^ l * (1 / 2) ^ (s - l) by rw [← pow_add]; congr 1; omega]
    ring
  · rw [mul_zero]

/-! ## The slice bound -/

/-- **Collision bound** (from separation, part of (2.7, `eq:collision`)):
`∑_y P_{p,l}(y)² ≤ 2^{-l}`. -/
lemma sum_prefLaw_sq_le (n : ℕ) {p l : ℕ} (D : Finset (Fin p → ℕ)) (hD : D ⊆ words p l)
    (hinj : Set.InjOn (XmodN n) (↑D : Set (Fin p → ℕ))) :
    ∑ y : ZMod (3 ^ n), prefLaw n D l y ^ 2 ≤ (1 / 2 : ℝ) ^ l := by
  classical
  have h0 : ∀ y, 0 ≤ prefLaw n D l y := fun y =>
    Finset.sum_nonneg fun u _ => by split_ifs <;> positivity
  have hmax : ∀ y, prefLaw n D l y ≤ (1 / 2 : ℝ) ^ l := by
    intro y
    unfold prefLaw
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : (D.filter fun u => XmodN n u = y).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro u hu u' hu'
      rw [mem_filter] at hu hu'
      exact hinj hu.1 hu'.1 (hu.2.trans hu'.2.symm)
    calc ((D.filter fun u => XmodN n u = y).card : ℝ) * (1 / 2) ^ l ≤ 1 * (1 / 2) ^ l := by
          gcongr; exact_mod_cast hc
      _ = _ := one_mul _
  have hsum : ∑ y : ZMod (3 ^ n), prefLaw n D l y ≤ 1 := by
    unfold prefLaw
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_const, nsmul_eq_mul]
    calc (D.card : ℝ) * (1 / 2) ^ l ≤ ((words p l).card : ℝ) * (1 / 2) ^ l := by
          gcongr
      _ = lawS p l := by rw [← sum_words_half, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 := lawS_le_one p l
  calc ∑ y, prefLaw n D l y ^ 2 ≤ ∑ y, (1 / 2 : ℝ) ^ l * prefLaw n D l y :=
        Finset.sum_le_sum fun y _ => by rw [sq]; exact mul_le_mul_of_nonneg_right (hmax y) (h0 y)
    _ = (1 / 2 : ℝ) ^ l * ∑ y, prefLaw n D l y := by rw [Finset.mul_sum]
    _ ≤ (1 / 2 : ℝ) ^ l * 1 := by gcongr
    _ = _ := mul_one _

/-- **The slice bound.** If the tail transform is at most `β` at every frequency excluded by
`Q_m`, then `∑_y |g_s(y) - (Q_m g)_s(y)| ≤ β √(3^n 2^{-l})`. -/
theorem piece_slice_bound {n p q m l : ℕ} (hn : p + q = n) (hmn : m ≤ n)
    (D : Finset (Fin p → ℕ)) (hD : D ⊆ words p l)
    (hinj : Set.InjOn (XmodN n) (↑D : Set (Fin p → ℕ))) {β : ℝ} (hβ : 0 ≤ β)
    (hT : ∀ ξ : ZMod (3 ^ n), ξ * 3 ^ m ≠ 0 → ∀ s' : ℕ,
      ‖(1 / 2 : ℂ) ^ s' * ∑ v ∈ words q s', chiZ ξ (3 ^ p * half n ^ l * XmodN n v)‖ ≤ β)
    (s : ℕ) :
    ∑ y : ZMod (3 ^ n), |gP n p D s y - Qop n m (gP n p D) s y| ≤
      β * √((3 : ℝ) ^ n * (1 / 2) ^ l) := by
  have hTb : ∀ ξ : ZMod (3 ^ n), ξ * 3 ^ m ≠ 0 → ‖tailT n p q l s ξ‖ ≤ β := by
    intro ξ hξ
    unfold tailT
    split_ifs
    · exact hT ξ hξ (s - l)
    · simpa using hβ
  have hL2 := l2_sub_Qs_le hmn (fun y => (gP n p D s y : ℂ)) (fun y => (prefLaw n D l y : ℂ))
    (tailT n p q l s) (fourierZ_gP hn D hD s) hTb
  have hQ : ∀ y, (gP n p D s y : ℂ) - Qs n m (fun y => (gP n p D s y : ℂ)) y =
      ((gP n p D s y - Qop n m (gP n p D) s y : ℝ) : ℂ) := by
    intro y; rw [Complex.ofReal_sub, Qop_eq_Qs]
  simp_rw [hQ, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hL2
  have hcoll := sum_prefLaw_sq_le n D hD hinj
  set h : ZMod (3 ^ n) → ℝ := fun y => gP n p D s y - Qop n m (gP n p D) s y with hh
  have hsq : ∑ y, h y ^ 2 ≤ β ^ 2 * (1 / 2 : ℝ) ^ l :=
    hL2.trans (mul_le_mul_of_nonneg_left hcoll (sq_nonneg β))
  -- Cauchy–Schwarz over `y`
  have hcs : (∑ y, |h y|) ^ 2 ≤ (3 : ℝ) ^ n * ∑ y, h y ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod (3 ^ n)))
      (fun _ => (1 : ℝ)) (fun y => |h y|)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      mul_one, sq_abs] at this
    push_cast at this
    exact this
  have hS0 : 0 ≤ ∑ y, |h y| := Finset.sum_nonneg fun y _ => abs_nonneg _
  have h3 : (0 : ℝ) ≤ 3 ^ n := by positivity
  rw [show β * √((3 : ℝ) ^ n * (1 / 2) ^ l) = √((3 : ℝ) ^ n * (β ^ 2 * (1 / 2) ^ l)) by
    rw [show (3 : ℝ) ^ n * (β ^ 2 * (1 / 2) ^ l) = β ^ 2 * ((3 : ℝ) ^ n * (1 / 2) ^ l) by ring,
      Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ]]
  rw [Real.le_sqrt hS0 (by positivity)]
  exact hcs.trans (mul_le_mul_of_nonneg_left hsq h3)

/-! ## Excluded frequencies have large conductor -/

lemma chiZ_congr {n : ℕ} {ξ x ξ' x' : ZMod (3 ^ n)} (h : ξ * x = ξ' * x') :
    chiZ ξ x = chiZ ξ' x' := by
  rw [chiZ_eq_stdAddChar, chiZ_eq_stdAddChar, h]

/-- **Frequency reduction**: `χ^{(N)}_{3^a b}(y) = χ^{(r)}_b(y mod 3^r)` for `N = a + r`. -/
lemma chiZ_reduce {N a r : ℕ} (hN : N = a + r) (b : ℕ) (y : ZMod (3 ^ N)) :
    chiZ ((3 : ZMod (3 ^ N)) ^ a * (b : ZMod (3 ^ N))) y =
      chiZ (b : ZMod (3 ^ r)) (ZMod.cast y : ZMod (3 ^ r)) := by
  subst hN
  have e1 : -((3 : ZMod (3 ^ (a + r))) ^ a * (b : ZMod (3 ^ (a + r))) * y) =
      ((-((3 ^ a * b * y.val : ℕ) : ℤ) : ℤ) : ZMod (3 ^ (a + r))) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val y]
    push_cast; ring
  have e2 : -((b : ZMod (3 ^ r)) * (ZMod.cast y : ZMod (3 ^ r))) =
      ((-((b * y.val : ℕ) : ℤ) : ℤ) : ZMod (3 ^ r)) := by
    rw [ZMod.cast_eq_val]; push_cast; ring
  rw [chiZ_eq_stdAddChar, chiZ_eq_stdAddChar, e1, e2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [show (3 : ℂ) ^ (a + r) = 3 ^ a * 3 ^ r from pow_add 3 a r]
  field_simp

lemma cast_mul_zmod {r n : ℕ} (h : r ≤ n) (x y : ZMod (3 ^ n)) :
    (ZMod.cast (x * y) : ZMod (3 ^ r)) = ZMod.cast x * ZMod.cast y := by
  have := map_mul (ZMod.castHom (pow_dvd_pow 3 h) (ZMod (3 ^ r))) x y
  simpa only [ZMod.castHom_apply] using this

lemma cast_half_pow {r n : ℕ} (h : r ≤ n) (l : ℕ) :
    (ZMod.cast (half n ^ l) : ZMod (3 ^ r)) = half r ^ l := by
  have := map_pow (ZMod.castHom (pow_dvd_pow 3 h) (ZMod (3 ^ r))) (half n) l
  rw [ZMod.castHom_apply, cast_half h] at this
  exact this

/-- **An excluded frequency has conductor `3^r` with `r > m - p`.** For `ξ` with `3^m ξ ≠ 0`
in `ℤ/3^nℤ`, `n = p + q`, `p ≤ m ≤ n`, there are `r` with `m - p < r ≤ q` and a unit `ζ` of
`ℤ/3^rℤ` such that the tail character is `χ_ζ` applied to `X̃'_q mod 3^r`. -/
lemma tail_char_reduce {n p q m : ℕ} (l : ℕ) (hn : p + q = n) (hpm : p ≤ m) (hmn : m ≤ n)
    (ξ : ZMod (3 ^ n)) (hξ : ξ * 3 ^ m ≠ 0) :
    ∃ r : ℕ, m - p < r ∧ r ≤ q ∧ ∃ ζ : ZMod (3 ^ r), ¬ 3 ∣ ζ.val ∧
      ∀ v : Fin q → ℕ, chiZ ξ (3 ^ p * half n ^ l * XmodN n v) =
        chiZ ζ (ZMod.cast (Xmod v) : ZMod (3 ^ r)) := by
  have hV : ξ.val ≠ 0 := by
    intro h; apply hξ; rw [(ZMod.val_eq_zero ξ).mp h, zero_mul]
  obtain ⟨j, b, hb3, hVb⟩ := Nat.exists_eq_pow_mul_and_not_dvd hV 3 (by norm_num)
  have hξeq : ξ = (3 : ZMod (3 ^ n)) ^ j * (b : ZMod (3 ^ n)) := by
    rw [← ZMod.natCast_zmod_val ξ, hVb]; push_cast; ring
  have hj : j < n - m := by
    by_contra hj
    push Not at hj
    apply hξ
    rw [hξeq, show (3 : ZMod (3 ^ n)) ^ j * (b : ZMod (3 ^ n)) * 3 ^ m =
      3 ^ (m + j) * b by rw [pow_add]; ring, three_pow_eq_zero (by omega), zero_mul]
  refine ⟨q - j, by omega, by omega, (b : ZMod (3 ^ (q - j))) * half (q - j) ^ l, ?_, ?_⟩
  · -- `ζ` is a unit modulo `3`
    intro h3
    have hr : 3 ∣ 3 ^ (q - j) := dvd_pow_self 3 (by omega)
    set φ := ZMod.castHom hr (ZMod 3)
    have hφ0 : φ ((b : ZMod (3 ^ (q - j))) * half (q - j) ^ l) = 0 := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]; exact h3
    have hφh : φ (half (q - j)) * 2 = 1 := by
      rw [← map_ofNat φ 2, ← map_mul, mul_comm, two_mul_half, map_one]
    have hb0 : (b : ZMod 3) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have hh0 : φ (half (q - j)) ≠ 0 := by intro h0; rw [h0, zero_mul] at hφh; exact zero_ne_one hφh
    rw [map_mul, map_pow, map_natCast] at hφ0
    exact mul_ne_zero hb0 (pow_ne_zero l hh0) hφ0
  · intro v
    have hrq : q - j ≤ q := by omega
    have hrn : q - j ≤ n := by omega
    have h1 : ξ * (3 ^ p * half n ^ l * XmodN n v) =
        ((3 : ZMod (3 ^ n)) ^ (p + j) * (b : ZMod (3 ^ n))) * (half n ^ l * XmodN n v) := by
      rw [hξeq, pow_add]; ring
    rw [chiZ_congr h1, chiZ_reduce (show n = (p + j) + (q - j) by omega), cast_mul_zmod hrn,
      cast_half_pow hrn, cast_XmodN hrn, Xmod_eq_XmodN, cast_XmodN hrq]
    exact chiZ_congr (by ring)

end CollatzCLT
