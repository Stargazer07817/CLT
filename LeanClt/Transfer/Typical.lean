import LeanClt.Transfer.Words
import LeanClt.Transfer.Geom

/-!
# Valuation words of `N_Y`: comparison with the geometric model

For `N_Y` uniform on the odd integers of `[Y, 2Y]` (`L_Y` of them), each word `a` of length `j`
and total `s` has `|#{N : prefix a} - L_Y 2^{-s}| ≤ 2` (`count_prefix`), because the prefix
condition is one residue class mod `2^{s+1}`. Summing over words gives deviation bounds for the
valuation total `S_j(N_Y)` with an additive error `2^{K+3}` (`count_dev_le`). This is what the
coupling import was used for in Lemmas 5.1 and 5.3.
-/

open Real Finset

namespace CollatzCLT

/-- Extend a finite word by `1`s. -/
def ext {n : ℕ} (a : Fin n → ℕ) (i : ℕ) : ℕ := if h : i < n then a ⟨i, h⟩ else 1

lemma ext_pos {n : ℕ} {a : Fin n → ℕ} (ha : ∀ i, 1 ≤ a i) (i : ℕ) : 1 ≤ ext a i := by
  unfold ext; split_ifs <;> simp [ha]

lemma wsum_ext {n : ℕ} (a : Fin n → ℕ) : wsum (ext a) n = ∑ i, a i := by
  unfold wsum ext
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

lemma vword_pos {N : ℕ} (hN : Odd N) (i : ℕ) : 1 ≤ vword N i :=
  one_le_padicValNat_of_odd (by
    cases i with
    | zero => simpa using hN
    | succ i => rw [Function.iterate_succ_apply']; exact U_odd _)

/-- `S_j(N)`, the valuation total of the first `j` odd steps. -/
def Swd (N j : ℕ) : ℕ := wsum (vword N) j

/-- `L_Y`, the number of odd integers in `[Y, 2Y]`. -/
noncomputable def LY (Y : ℝ) : ℕ := (oddClosed Y).card

lemma oddClosed_bounds {Y : ℝ} (hY : 0 ≤ Y) : ⌈Y⌉₊ ≤ ⌊2 * Y⌋₊ + 1 := by
  have h1 : (⌈Y⌉₊ : ℝ) < Y + 1 := Nat.ceil_lt_add_one hY
  have h2 : 2 * Y < (⌊2 * Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have : (⌈Y⌉₊ : ℝ) < ⌊2 * Y⌋₊ + 2 := by linarith
  exact_mod_cast (show ⌈Y⌉₊ < ⌊2 * Y⌋₊ + 2 by exact_mod_cast this) |> Nat.lt_succ_iff.mp

lemma oddClosed_eq_filter (Y : ℝ) :
    oddClosed Y = (Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).filter (fun N => N ≡ 1 [MOD 2]) := by
  unfold oddClosed
  congr 1; funext N
  simp [Nat.ModEq, Nat.odd_iff]

/-- `L_Y = (⌊2Y⌋ + 1 - ⌈Y⌉)/2 ± 1`. -/
lemma LY_bound {Y : ℝ} (hY : 0 ≤ Y) :
    |(LY Y : ℝ) - ((⌊2 * Y⌋₊ + 1 - ⌈Y⌉₊ : ℕ) : ℝ) / 2| ≤ 1 := by
  unfold LY
  rw [oddClosed_eq_filter]
  have := card_modEq_Icc ⌈Y⌉₊ ⌊2 * Y⌋₊ 2 1 (by norm_num) (oddClosed_bounds hY)
  simpa using this

/-- **One word, one residue class.** For a word `a` of length `j` and total `s`,
`|#{N ∈ [Y,2Y] odd : prefix a} - L_Y 2^{-s}| ≤ 2`. -/
theorem count_prefix {Y : ℝ} (hY : 0 ≤ Y) {j s : ℕ} {a : Fin j → ℕ} (ha : a ∈ words j s) :
    |(((oddClosed Y).filter (fun N => ∀ i < j, vword N i = ext a i)).card : ℝ) -
      LY Y * (1 / 2 : ℝ) ^ s| ≤ 2 := by
  rw [mem_words] at ha
  obtain ⟨hs, ha1⟩ := ha
  have hpos := ext_pos ha1
  have hw : wsum (ext a) j = s := by rw [wsum_ext, hs]
  obtain ⟨c, hc⟩ := prefix_iff_modEq hpos j
  rw [hw] at hc
  have hset : (oddClosed Y).filter (fun N => ∀ i < j, vword N i = ext a i) =
      (Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).filter (fun N => N ≡ c [MOD 2 ^ (s + 1)]) := by
    unfold oddClosed
    rw [Finset.filter_filter]
    congr 1; funext N
    exact propext (hc N)
  rw [hset]
  have h1 := card_modEq_Icc ⌈Y⌉₊ ⌊2 * Y⌋₊ (2 ^ (s + 1)) c (by positivity) (oddClosed_bounds hY)
  have h2 := LY_bound hY
  set len : ℝ := ((⌊2 * Y⌋₊ + 1 - ⌈Y⌉₊ : ℕ) : ℝ)
  have hp : (0 : ℝ) < (1 / 2) ^ s := by positivity
  have hp1 : (1 / 2 : ℝ) ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have e : len / ((2 ^ (s + 1) : ℕ) : ℝ) = len / 2 * (1 / 2) ^ s := by
    push_cast; rw [pow_succ, div_pow, one_pow]; field_simp
  rw [e] at h1
  have h3 : |len / 2 * (1 / 2) ^ s - LY Y * (1 / 2) ^ s| ≤ 1 := by
    rw [← sub_mul, abs_mul, abs_of_pos hp, abs_sub_comm]
    calc |(LY Y : ℝ) - len / 2| * (1 / 2) ^ s ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  calc _ = |((((Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).filter (fun N => N ≡ c [MOD 2 ^ (s + 1)])).card : ℝ) -
        len / 2 * (1 / 2) ^ s) + (len / 2 * (1 / 2) ^ s - LY Y * (1 / 2) ^ s)| := by ring_nf
    _ ≤ 1 + 1 := (abs_add_le _ _).trans (add_le_add h1 h3)
    _ = 2 := by norm_num

/-! ## The law of `S_j(N_Y)` -/

lemma Swd_eq_sum (N j : ℕ) : Swd N j = ∑ i : Fin j, vword N i := by
  unfold Swd wsum; rw [Fin.sum_univ_eq_sum_range]

/-- `#{N : S_j(N) = s}` is the sum over words of total `s` of the prefix counts. -/
lemma count_S_eq (Y : ℝ) (j s : ℕ) :
    ((oddClosed Y).filter (fun N => Swd N j = s)).card =
      ∑ a ∈ words j s, ((oddClosed Y).filter (fun N => ∀ i < j, vword N i = ext a i)).card := by
  rw [card_eq_sum_card_fiberwise (f := fun N (i : Fin j) => vword N i) (t := words j s)]
  · refine Finset.sum_congr rfl fun a ha => ?_
    congr 1
    ext N
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hN, -⟩, hfa⟩
      refine ⟨hN, fun i hi => ?_⟩
      have := congrFun hfa ⟨i, hi⟩
      simp [ext, hi, this]
    · rintro ⟨hN, hpre⟩
      have hfa : (fun i : Fin j => vword N i) = a := by
        funext i; have := hpre i i.2; simpa [ext] using this
      refine ⟨⟨hN, ?_⟩, hfa⟩
      rw [mem_words] at ha
      rw [Swd_eq_sum, ← ha.1]
      exact Finset.sum_congr rfl fun i _ => congrFun hfa i
  · intro N hN
    rw [Finset.mem_coe, Finset.mem_filter] at hN
    obtain ⟨hNo, hS⟩ := hN
    have hodd : Odd N := (Finset.mem_filter.mp hNo).2
    rw [Finset.mem_coe, mem_words]
    refine ⟨by rw [← hS, Swd_eq_sum], fun i => vword_pos hodd i⟩

/-- `|#{N : S_j(N) = s} - L_Y P(S_j = s)| ≤ 2·2^s`. -/
lemma count_S_bound {Y : ℝ} (hY : 0 ≤ Y) (j s : ℕ) :
    |(((oddClosed Y).filter (fun N => Swd N j = s)).card : ℝ) - LY Y * lawS j s| ≤ 2 * 2 ^ s := by
  rw [count_S_eq, ← sum_words_half, Finset.mul_sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ a ∈ words j s, |(((oddClosed Y).filter (fun N => ∀ i < j, vword N i = ext a i)).card
        : ℝ) - LY Y * (1 / 2) ^ s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ words j s, (2 : ℝ) := Finset.sum_le_sum fun a ha => count_prefix hY ha
    _ = 2 * (words j s).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ 2 * 2 ^ s := by gcongr; exact card_words_le j s

lemma sum_pow_two_le (K : ℕ) : ∑ s ∈ range (K + 1), (2 : ℝ) ^ s ≤ 2 ^ (K + 1) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have : (2 : ℝ) ^ (K + 1 + 1) = 2 ^ (K + 1) + 2 ^ (K + 1) := by ring
    linarith

/-- `2·exp(-min(x²/(12j), x/8))`, the Chernoff bound of Lemma 2.2(i). -/
noncomputable def chern (j : ℕ) (x : ℝ) : ℝ := 2 * Real.exp (-min (x ^ 2 / (12 * j)) (x / 8))

/-- **Deviations of `S_j(N_Y)`.** For `j ≥ 1`, `t ≥ 0` and `K ≥ 2j`,
`#{N : |S_j(N) - 2j| ≥ t} ≤ L_Y (chern j t + chern j (K - 2j)) + 2^{K+3}`. -/
theorem count_dev_le {Y : ℝ} (hY : 0 ≤ Y) {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : 0 ≤ t) {K : ℕ}
    (hK : 2 * j ≤ K) :
    (((oddClosed Y).filter (fun N => t ≤ |(Swd N j : ℝ) - 2 * j|)).card : ℝ) ≤
      LY Y * (chern j t + chern j ((K : ℝ) - 2 * j)) + 2 ^ (K + 3) := by
  classical
  set L := (LY Y : ℝ)
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  -- the count by values of `S_j`
  have hcount : ∀ (P : ℕ → Prop) [DecidablePred P],
      (((oddClosed Y).filter (fun N => Swd N j ≤ K ∧ P (Swd N j))).card : ℝ) =
        ∑ s ∈ (range (K + 1)).filter P, (((oddClosed Y).filter (fun N => Swd N j = s)).card : ℝ) := by
    intro P _
    rw [card_eq_sum_card_fiberwise (f := fun N => Swd N j) (t := (range (K + 1)).filter P)]
    · push_cast
      refine Finset.sum_congr rfl fun s hs => ?_
      congr 2
      ext N
      simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; subst h2; exact ⟨⟨h1, by omega, hs.2⟩, rfl⟩
    · intro N hN
      rw [Finset.mem_coe, Finset.mem_filter] at hN
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hN.2.1, hN.2.2⟩
  have hbound : ∀ (P : ℕ → Prop) [DecidablePred P],
      |(((oddClosed Y).filter (fun N => Swd N j ≤ K ∧ P (Swd N j))).card : ℝ) -
        L * ∑ s ∈ (range (K + 1)).filter P, lawS j s| ≤ 2 ^ (K + 2) := by
    intro P _
    rw [hcount P, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ s ∈ (range (K + 1)).filter P,
          |(((oddClosed Y).filter (fun N => Swd N j = s)).card : ℝ) - L * lawS j s| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ (range (K + 1)).filter P, 2 * (2 : ℝ) ^ s :=
          Finset.sum_le_sum fun s _ => count_S_bound hY j s
      _ ≤ ∑ s ∈ range (K + 1), 2 * (2 : ℝ) ^ s :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ ≤ 2 ^ (K + 2) := by
          rw [← Finset.mul_sum]
          have := sum_pow_two_le K
          rw [pow_succ 2 (K + 1)]; linarith
  -- the geometric tail sums
  have hsum : Summable (lawS j) := summable_lawS j
  have hgeo1 : ∑ s ∈ (range (K + 1)).filter (fun s : ℕ => t ≤ |(s : ℝ) - 2 * j|), lawS j s ≤
      chern j t := by
    have h := lawS_chernoff hj ht
    refine le_trans ?_ h
    rw [Finset.sum_filter]
    refine Summable.sum_le_tsum _ (fun s _ => by split_ifs <;> simp [lawS_nonneg]) ?_ |>.trans'
      (Finset.sum_le_sum fun s _ => le_rfl)
    exact summable_ite_lawS j _
  have htail : 1 - ∑ s ∈ range (K + 1), lawS j s ≤ chern j ((K : ℝ) - 2 * j) := by
    have hx : (0 : ℝ) ≤ (K : ℝ) - 2 * j := by
      have : ((2 * j : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
      push_cast at this; linarith
    have h := lawS_chernoff hj hx
    have hsplit := hsum.sum_add_tsum_nat_add (K + 1)
    rw [tsum_lawS] at hsplit
    have : ∑' i, lawS j (i + (K + 1)) ≤
        ∑' A : ℕ, (if (K : ℝ) - 2 * j ≤ |(A : ℝ) - 2 * j| then lawS j A else 0) := by
      have hs2 := summable_ite_lawS j (fun A : ℕ => (K : ℝ) - 2 * j ≤ |(A : ℝ) - 2 * j|)
      refine le_trans ?_ (tsum_comp_le_tsum_of_inj hs2 (fun A => by split_ifs <;> simp [lawS_nonneg])
        (i := fun i => i + (K + 1)) (fun a b h => by simpa using h))
      refine Summable.tsum_le_tsum (fun i => ?_) ((summable_nat_add_iff (K + 1)).mpr hsum)
        (hs2.comp_injective (fun a b h => by simpa using h))
      simp only [Function.comp_apply]
      have hc : (K : ℝ) - 2 * j ≤ |(((i + (K + 1) : ℕ)) : ℝ) - 2 * j| := by
        rw [abs_of_nonneg (by push_cast; linarith)]
        push_cast; linarith
      simp only [hc, ↓reduceIte, le_refl]
    unfold chern at h ⊢
    linarith
  -- assemble
  have hA := hbound (fun s : ℕ => t ≤ |(s : ℝ) - 2 * j|)
  have hB := hbound (fun _ => True)
  rw [Finset.filter_true] at hB
  simp only [and_true] at hB
  have hsplitN : (((oddClosed Y).filter (fun N => t ≤ |(Swd N j : ℝ) - 2 * j|)).card : ℝ) ≤
      (((oddClosed Y).filter (fun N => Swd N j ≤ K ∧ t ≤ |(Swd N j : ℝ) - 2 * j|)).card : ℝ) +
      (L - (((oddClosed Y).filter (fun N => Swd N j ≤ K)).card : ℝ)) := by
    have h1 : ((oddClosed Y).filter (fun N => t ≤ |(Swd N j : ℝ) - 2 * j|)).card ≤
        ((oddClosed Y).filter (fun N => Swd N j ≤ K ∧ t ≤ |(Swd N j : ℝ) - 2 * j|)).card +
        ((oddClosed Y).filter (fun N => ¬ Swd N j ≤ K)).card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1.1))]
      exact Finset.card_le_card (fun N hN => by
        simp only [Finset.mem_filter, Finset.mem_union] at hN ⊢
        by_cases h : Swd N j ≤ K
        · exact Or.inl ⟨hN.1, h, hN.2⟩
        · exact Or.inr ⟨hN.1, h⟩)
    have h2 := Finset.card_filter_add_card_filter_not (s := oddClosed Y)
      (fun N => Swd N j ≤ K)
    have h3 : (((oddClosed Y).filter (fun N => ¬ Swd N j ≤ K)).card : ℝ) =
        L - (((oddClosed Y).filter (fun N => Swd N j ≤ K)).card : ℝ) := by
      simp only [L, LY]; rw [← h2]; push_cast; ring
    have : (((oddClosed Y).filter (fun N => t ≤ |(Swd N j : ℝ) - 2 * j|)).card : ℝ) ≤
        (((oddClosed Y).filter (fun N => Swd N j ≤ K ∧ t ≤ |(Swd N j : ℝ) - 2 * j|)).card : ℝ) +
        (((oddClosed Y).filter (fun N => ¬ Swd N j ≤ K)).card : ℝ) := by exact_mod_cast h1
    linarith
  have habs1 := (abs_le.mp hA).2
  have habs2 := (abs_le.mp hB).1
  have hp1 : L * ∑ s ∈ (range (K + 1)).filter (fun s : ℕ => t ≤ |(s : ℝ) - 2 * j|), lawS j s ≤
      L * chern j t := mul_le_mul_of_nonneg_left hgeo1 hL0
  have hp2 : L * (1 - ∑ s ∈ range (K + 1), lawS j s) ≤ L * chern j ((K : ℝ) - 2 * j) :=
    mul_le_mul_of_nonneg_left htail hL0
  have h8 : (2 : ℝ) ^ (K + 2) + 2 ^ (K + 2) = 2 ^ (K + 3) := by ring
  nlinarith

end CollatzCLT
