import LeanClt.Positivity.Realise

/-!
# §8.1: transfer operators, (8.2) and Lemma 8.3

For a word `w` of depth `d`, the transfer operator of §8.1 sends a function `g` on `G_t = ℤ/3^tℤ`
to `(T_w g)(y) = W(w) ∑_{F_w(z) = y} g(z)` on `G_{t+d}` (`Tw`). It is convenient to allow any target
modulus `n` (`TN n w g`, with `Tw t w g = TN (t + d) w g`); `TwQ Q t w g` is `T_w g` read through
reduction from `G_Q`.

* **(8.2, `eq:B1`)** `normL1_Tw`, `mean_Tw`: `‖T_w g‖_{L¹(G_{t+d})} = 2^{-A(w)} ‖g‖_{L¹(G_t)}`, and
  the mean scales by `2^{-A(w)}`.
* `TN_rhoX`: `T_w ρ_t = (2/3) 3^{t+d} P(X_{t+d} = ·, prefix = w)` (the prefix decomposition
  `lawXpre_decomp`).
* `lift_comm`: `T_{w,Q} ρ_k = T_w(lift ρ_k)` on `G_Q` (used without statement in the proof of
  Lemma 8.3). This needs the image of `F_w`: `y ∈ F_w(G_t)` iff `y ≡ ϑ_w (mod 3^d)`
  (`mem_range_FwN`).
* **Lemma 8.3 [`lem:B2`]** `transfer_comparison`, with the paper's proof: replace `ρ_k` by
  `ρ_{Q-d}` in each term (cost `2^{-A(w)} (2/3) C_A k^{-A}` by (8.2) and (8.1)), identify
  `∑_w T_w ρ_{Q-d}` with the part of `ρ_Q` carried by the disjoint prefix events (dominated by
  `ρ_Q` pointwise, `sum_lawXpre_le`; of mean `(2/3) p(V)`, `sum_sum_lawXpre`), and compare `ρ_Q`
  with `lift(ρ_l)` by (8.1).
-/

open Finset Function

noncomputable section

namespace CollatzCLT
namespace Positivity

/-! ## Transfer operators -/

/-- `T_w g` at any target modulus `n`: `y ↦ W(w) ∑_{F_w(z) = y} g(z)`. -/
def TN (n : ℕ) {t : ℕ} (w : Word) (g : ZMod (3 ^ t) → ℝ) (y : ZMod (3 ^ n)) : ℝ :=
  wt w * ∑ z : ZMod (3 ^ t), if FwN n w z = y then g z else 0

/-- **The transfer operator** `T_w : functions on G_t → functions on G_{t+d}` of §8.1. -/
def Tw (t : ℕ) (w : Word) (g : ZMod (3 ^ t) → ℝ) (y : ZMod (3 ^ (t + w.length))) : ℝ :=
  wt w * ∑ z : ZMod (3 ^ t), if Fw t w z = y then g z else 0

/-- `T_{w,Q} g`: `T_w g` read through reduction from `G_Q`; a lift to `G_Q` when
`t + |w| ≤ Q`, which holds at every use. -/
def TwQ (Q t : ℕ) (w : Word) (g : ZMod (3 ^ t) → ℝ) (y : ZMod (3 ^ Q)) : ℝ :=
  Tw t w g (ZMod.cast y)

lemma Tw_eq_TN (t : ℕ) (w : Word) (g : ZMod (3 ^ t) → ℝ) : Tw t w g = TN (t + w.length) w g :=
  rfl

/-! ## Sums through an injection -/

lemma abs_sum_ite_inj {α β : Type*} [Fintype α] [DecidableEq β] {F : α → β} (hF : Injective F)
    (g : α → ℝ) (y : β) :
    |∑ z, if F z = y then g z else 0| = ∑ z, if F z = y then |g z| else 0 := by
  by_cases h : ∃ z0, F z0 = y
  · obtain ⟨z0, rfl⟩ := h
    rw [Finset.sum_eq_single z0, Finset.sum_eq_single z0]
    · simp
    · intro b _ hb; simp [hF.ne hb]
    · simp
    · intro b _ hb; simp [hF.ne hb]
    · simp
  · have h' : ∀ z, F z ≠ y := fun z hz => h ⟨z, hz⟩
    simp [h']

lemma sum_sum_ite {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (F : α → β)
    (φ : α → ℝ) : ∑ y, ∑ z, (if F z = y then φ z else 0) = ∑ z, φ z := by
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

/-! ## (8.2) -/

lemma normL1_TN {n t : ℕ} {w : Word} (hn : n = t + w.length) (g : ZMod (3 ^ t) → ℝ) :
    normL1 n (TN n w g) = gm w * normL1 t g := by
  have hinj := FwN_injective (w := w) (n := n) (t := t) (by omega)
  unfold normL1 TN
  have h1 : ∀ y, |wt w * ∑ z : ZMod (3 ^ t), if FwN n w z = y then g z else 0| =
      wt w * ∑ z : ZMod (3 ^ t), if FwN n w z = y then |g z| else 0 := by
    intro y
    rw [abs_mul, abs_of_pos (wt_pos w), abs_sum_ite_inj hinj]
  simp_rw [h1]
  rw [← Finset.mul_sum, sum_sum_ite, hn, wt, pow_add]
  field_simp

/-- **(8.2, `eq:B1`)**: `‖T_w g‖_{L¹(G_{t+d})} = 2^{-A(w)} ‖g‖_{L¹(G_t)}`. -/
theorem normL1_Tw (t : ℕ) (w : Word) (g : ZMod (3 ^ t) → ℝ) :
    normL1 (t + w.length) (Tw t w g) = gm w * normL1 t g := by
  rw [Tw_eq_TN]; exact normL1_TN rfl g

lemma mean_TN {n t : ℕ} {w : Word} (hn : n = t + w.length) (g : ZMod (3 ^ t) → ℝ) :
    (∑ y, TN n w g y) / 3 ^ n = gm w * ((∑ z, g z) / 3 ^ t) := by
  unfold TN
  rw [← Finset.mul_sum, sum_sum_ite, hn, wt, pow_add]
  field_simp

/-- **(8.2, `eq:B1`)**, the mean: the mean of `T_w g` is `2^{-A(w)}` times the mean of `g`. -/
theorem mean_Tw (t : ℕ) (w : Word) (g : ZMod (3 ^ t) → ℝ) :
    (∑ y, Tw t w g y) / 3 ^ (t + w.length) = gm w * ((∑ z, g z) / 3 ^ t) := by
  rw [Tw_eq_TN]; exact mean_TN rfl g

/-- `T_w ρ_t = (2/3) 3^{t+d} P(X_{t+d} = ·, prefix = w)`. -/
lemma TN_rhoX {n t : ℕ} {w : Word} (hw : w.Pos) (hn : n = t + w.length) (y : ZMod (3 ^ n)) :
    TN n w (rhoX t) y = 2 / 3 * 3 ^ n * lawXpre n w y := by
  subst hn
  rw [lawXpre_decomp (by omega : t + w.length = w.length + t) hw y]
  unfold TN rhoX
  have : ∀ z : ZMod (3 ^ t),
      (if FwN (t + w.length) w z = y then 2 / 3 * 3 ^ t * lawX t z else 0) =
      2 / 3 * 3 ^ t * (if FwN (t + w.length) w z = y then lawX t z else 0) := by
    intro z; split_ifs <;> simp
  simp_rw [this, ← Finset.mul_sum]
  rw [wt, pow_add (3 : ℝ) t w.length]
  ring

/-! ## The image of `F_w`, and lifting -/

/-- `F_w` does not depend on the digits of `z` beyond the modulus. -/
lemma FwN_cast_val {n k t : ℕ} {w : Word} (hn : n ≤ k + w.length)
    (z : ZMod (3 ^ t)) : FwN n w (ZMod.cast z : ZMod (3 ^ k)) = FwN n w z := by
  unfold FwN
  congr 1
  have hval : (ZMod.cast z : ZMod (3 ^ k)).val = z.val % 3 ^ k := by
    rw [ZMod.cast_eq_val, ZMod.val_natCast]
  rw [hval]
  conv_rhs => rw [← Nat.mod_add_div z.val (3 ^ k)]
  push_cast
  have h0 : (3 : ZMod (3 ^ n)) ^ (w.length + k) = 0 := three_pow_eq_zero (by omega)
  rw [pow_add] at h0
  linear_combination (-(half n ^ tot w) * ((z.val / 3 ^ k : ℕ) : ZMod (3 ^ n))) * h0

/-- **The image of `F_w`:** `y ∈ F_w(G_t)` iff `y ≡ ϑ_w (mod 3^d)`. -/
theorem mem_range_FwN {n t : ℕ} {w : Word} (hn : n = t + w.length) (y : ZMod (3 ^ n)) :
    (∃ z : ZMod (3 ^ t), FwN n w z = y) ↔
      (ZMod.cast y : ZMod (3 ^ w.length)) = thetaRes w.length w := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [cast_FwN (by omega), FwN, three_pow_eq_zero le_rfl]
    ring
  · intro h
    subst hn
    have hY : (ZMod.cast y : ZMod (3 ^ w.length)) = (y.val : ZMod (3 ^ w.length)) :=
      ZMod.cast_eq_val y
    rw [hY, thetaRes_eq_kint] at h
    -- `3^d ∣ 2^A Y - K`
    have h2 : ((2 ^ tot w * y.val - kint w : ℤ) : ZMod (3 ^ w.length)) = 0 := by
      push_cast
      rw [h]
      have := two_pow_mul_half_pow w.length (tot w)
      linear_combination (kint w : ZMod (3 ^ w.length)) * this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    obtain ⟨m, hm⟩ := h2
    refine ⟨(m : ZMod (3 ^ t)), ?_⟩
    -- `3^d · val(m mod 3^t) ≡ 3^d m (mod 3^{t+d})`
    have hv : (((m : ZMod (3 ^ t)).val : ℕ) : ℤ) = m % (3 ^ t : ℕ) := ZMod.val_intCast m
    have hdecomp := Int.emod_add_mul_ediv m ((3 ^ t : ℕ) : ℤ)
    have key : (3 : ZMod (3 ^ (t + w.length))) ^ w.length *
        (((m : ZMod (3 ^ t)).val : ℕ) : ZMod (3 ^ (t + w.length))) =
        ((3 ^ w.length * m : ℤ) : ZMod (3 ^ (t + w.length))) := by
      have e : ((3 ^ w.length * ((m : ZMod (3 ^ t)).val : ℤ) : ℤ) : ZMod (3 ^ (t + w.length))) =
          ((3 ^ w.length * m : ℤ) : ZMod (3 ^ (t + w.length))) := by
        rw [hv]
        conv_rhs => rw [← hdecomp]
        push_cast
        have h0 : (3 : ZMod (3 ^ (t + w.length))) ^ w.length * 3 ^ t = 0 := by
          rw [← pow_add]; exact three_pow_eq_zero (by omega)
        linear_combination (-(((m / (3 : ℤ) ^ t : ℤ) : ZMod (3 ^ (t + w.length))))) * h0
      push_cast at e ⊢
      exact e
    have hm' : ((2 ^ tot w * y.val - kint w : ℤ) : ZMod (3 ^ (t + w.length))) =
        ((3 ^ w.length * m : ℤ) : ZMod (3 ^ (t + w.length))) := by rw [hm]; push_cast; ring
    push_cast at hm' key
    unfold FwN
    rw [thetaRes_eq_kint]
    conv_rhs => rw [← ZMod.natCast_zmod_val y]
    have := two_pow_mul_half_pow (t + w.length) (tot w)
    linear_combination (half (t + w.length) ^ tot w) * key -
      (half (t + w.length) ^ tot w) * hm' + ((y.val : ZMod (3 ^ (t + w.length)))) * this

/-- **Lifting commutes with transfer:** `T_{w,Q} g = T_w(lift g)` on `G_Q`, for `g` on `G_k` and
`Q = t + d`, `k ≤ t`. -/
theorem lift_comm {Q t k : ℕ} {w : Word} (hQ : Q = t + w.length) (hk : k ≤ t)
    (g : ZMod (3 ^ k) → ℝ) (y : ZMod (3 ^ Q)) :
    TwQ Q k w g y = TN Q w (fun z : ZMod (3 ^ t) => g (ZMod.cast z)) y := by
  unfold TwQ
  rw [Tw_eq_TN]
  unfold TN
  congr 1
  have hinjQ := FwN_injective (w := w) (n := Q) (t := t) (by omega)
  have hinjk := FwN_injective (w := w) (n := k + w.length) (t := k) (by omega)
  by_cases hy : ∃ z0 : ZMod (3 ^ t), FwN Q w z0 = y
  · obtain ⟨z0, rfl⟩ := hy
    have hc : (ZMod.cast (FwN Q w z0) : ZMod (3 ^ (k + w.length))) =
        FwN (k + w.length) w (ZMod.cast z0 : ZMod (3 ^ k)) := by
      rw [cast_FwN (by omega), FwN_cast_val le_rfl]
    rw [hc, Finset.sum_eq_single (ZMod.cast z0 : ZMod (3 ^ k)),
      Finset.sum_eq_single z0]
    · simp
    · intro b _ hb; simp [hinjQ.ne hb]
    · simp
    · intro b _ hb; simp [hinjk.ne hb]
    · simp
  · have hR : ∀ z : ZMod (3 ^ t), FwN Q w z ≠ y := fun z hz => hy ⟨z, hz⟩
    have hL : ∀ z : ZMod (3 ^ k), FwN (k + w.length) w z ≠ ZMod.cast y := by
      intro z hz
      apply hy
      rw [mem_range_FwN hQ]
      have h1 := (mem_range_FwN (n := k + w.length) rfl _).mp ⟨z, hz⟩
      rwa [cast_cast_zmod (Nat.le_add_left _ _) (by omega)] at h1
    simp [hR, hL]

/-! ## The normalised `L¹` norm -/

lemma normL1_nonneg (q : ℕ) (f : ZMod (3 ^ q) → ℝ) : 0 ≤ normL1 q f := by
  unfold normL1
  exact div_nonneg (Finset.sum_nonneg fun y _ => abs_nonneg _) (by positivity)

lemma normL1_add_le (q : ℕ) (f g : ZMod (3 ^ q) → ℝ) :
    normL1 q (fun y => f y + g y) ≤ normL1 q f + normL1 q g := by
  unfold normL1
  rw [← add_div, ← Finset.sum_add_distrib]
  gcongr with y
  exact abs_add_le _ _

lemma normL1_sum_le {ι : Type*} (q : ℕ) (s : Finset ι) (f : ι → ZMod (3 ^ q) → ℝ) :
    normL1 q (fun y => ∑ i ∈ s, f i y) ≤ ∑ i ∈ s, normL1 q (f i) := by
  unfold normL1
  rw [← Finset.sum_div, Finset.sum_comm]
  gcongr with y
  exact Finset.abs_sum_le_sum_abs _ _

/-! ## Lemma 8.3 -/

/-- **Lemma 8.3 [`lem:B2`]**, (8.3, `eq:B2`): for a finite prefix-free family `V` of words of depth
at most `h`, `k ≥ 1`, `Q = h + k` and `1 ≤ l ≤ Q`,
`‖∑_{w ∈ V} T_{w,Q} ρ_k - lift(ρ_l)‖_{L¹(G_Q)} ≤ (2/3)[C_A k^{-A} + C_A l^{-A} + 1 - p(V)]`. -/
theorem transfer_comparison (hA1 : OffsetMixing) {A : ℝ} (hA : 0 < A) : ∃ C : ℝ,
    ∀ (V : Finset Word) (h k l : ℕ), PrefixFree V → (∀ w ∈ V, w.Pos ∧ w.length ≤ h) →
      1 ≤ k → 1 ≤ l → l ≤ h + k →
      normL1 (h + k) (fun y => ∑ w ∈ V, TwQ (h + k) k w (rhoX k) y - rhoX l (ZMod.cast y)) ≤
        2 / 3 * (C * (k : ℝ) ^ (-A) + C * (l : ℝ) ^ (-A) + (1 - pmass V)) := by
  obtain ⟨C, hC⟩ := hA1 A hA
  have hC0 : 0 ≤ C := by
    have := (normL1_nonneg 1 _).trans (hC 1 1 le_rfl le_rfl)
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at this
    linarith
  refine ⟨C, fun V h k l hV hVw hk hl hlQ => ?_⟩
  have hpos : ∀ w ∈ V, w.Pos := fun w hw => (hVw w hw).1
  set Q := h + k with hQdef
  -- `B_w = T_w ρ_{Q-d}`, the part of `ρ_Q` carried by the prefix event of `w`
  set B : Word → ZMod (3 ^ Q) → ℝ := fun w y => TN Q w (rhoX (Q - w.length)) y with hB
  have hBpre : ∀ w ∈ V, ∀ y, B w y = 2 / 3 * 3 ^ Q * lawXpre Q w y := by
    intro w hw y
    exact TN_rhoX (hpos w hw) (by have := (hVw w hw).2; omega) y
  -- the decomposition of the integrand
  have hdec : (fun y => ∑ w ∈ V, TwQ Q k w (rhoX k) y - rhoX l (ZMod.cast y)) =
      fun y => (∑ w ∈ V, (TwQ Q k w (rhoX k) y - B w y) + (∑ w ∈ V, B w y - rhoX Q y)) +
        (rhoX Q y - rhoX l (ZMod.cast y)) := by
    funext y; rw [Finset.sum_sub_distrib]; ring
  -- (i) replacing `ρ_k` by `ρ_{Q-d}` costs `2^{-A(w)} (2/3) C k^{-A}` per word
  have h1 : normL1 Q (fun y => ∑ w ∈ V, (TwQ Q k w (rhoX k) y - B w y)) ≤
      2 / 3 * (C * (k : ℝ) ^ (-A)) * pmass V := by
    refine (normL1_sum_le Q V _).trans ?_
    rw [pmass, Finset.mul_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    have hwh := (hVw w hw).2
    have hQw : Q = (Q - w.length) + w.length := by omega
    have hkt : k ≤ Q - w.length := by omega
    have heq : (fun y => TwQ Q k w (rhoX k) y - B w y) =
        TN Q w (fun z : ZMod (3 ^ (Q - w.length)) => rhoX k (ZMod.cast z) - rhoX (Q - w.length) z) := by
      funext y
      rw [lift_comm hQw hkt, hB]
      simp only [TN, ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs <;> simp
    rw [heq, normL1_TN hQw]
    have hmix := hC k (Q - w.length) hk hkt
    have hsymm : normL1 (Q - w.length)
        (fun z : ZMod (3 ^ (Q - w.length)) => rhoX k (ZMod.cast z) - rhoX (Q - w.length) z) =
        normL1 (Q - w.length) (fun z => rhoX (Q - w.length) z - rhoX k (ZMod.cast z)) := by
      unfold normL1; simp_rw [abs_sub_comm]
    rw [hsymm, mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) (gm_pos w).le
  -- (ii) the prefix events carry `(2/3) p(V)` of `ρ_Q`
  have h2 : normL1 Q (fun y => ∑ w ∈ V, B w y - rhoX Q y) = 2 / 3 * (1 - pmass V) := by
    have hle : ∀ y, ∑ w ∈ V, B w y ≤ rhoX Q y := by
      intro y
      rw [Finset.sum_congr rfl fun w hw => hBpre w hw y, ← Finset.mul_sum, rhoX]
      exact mul_le_mul_of_nonneg_left (sum_lawXpre_le hV Q y) (by positivity)
    unfold normL1
    have habs : ∀ y, |∑ w ∈ V, B w y - rhoX Q y| = rhoX Q y - ∑ w ∈ V, B w y := by
      intro y; rw [abs_sub_comm, abs_of_nonneg (by linarith [hle y])]
    simp_rw [habs]
    rw [Finset.sum_sub_distrib]
    have e1 : ∑ y : ZMod (3 ^ Q), rhoX Q y = 2 / 3 * 3 ^ Q := by
      simp only [rhoX]; rw [← Finset.mul_sum, sum_lawX, mul_one]
    have e2 : ∑ y : ZMod (3 ^ Q), ∑ w ∈ V, B w y = 2 / 3 * 3 ^ Q * pmass V := by
      calc ∑ y : ZMod (3 ^ Q), ∑ w ∈ V, B w y
          = ∑ y : ZMod (3 ^ Q), ∑ w ∈ V, 2 / 3 * 3 ^ Q * lawXpre Q w y :=
            Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w hw => hBpre w hw y
        _ = 2 / 3 * 3 ^ Q * ∑ y : ZMod (3 ^ Q), ∑ w ∈ V, lawXpre Q w y := by
            simp_rw [← Finset.mul_sum]
        _ = 2 / 3 * 3 ^ Q * pmass V := by
            rw [sum_sum_lawXpre hpos (fun w hw => by have := (hVw w hw).2; omega)]
    rw [e1, e2]
    field_simp
  -- (iii) `ρ_Q` against `lift(ρ_l)`
  have h3 := hC l Q hl hlQ
  rw [hdec]
  have hs1 := normL1_add_le Q
    (fun y => ∑ w ∈ V, (TwQ Q k w (rhoX k) y - B w y) + (∑ w ∈ V, B w y - rhoX Q y))
    (fun y => rhoX Q y - rhoX l (ZMod.cast y))
  have hs2 := normL1_add_le Q (fun y => ∑ w ∈ V, (TwQ Q k w (rhoX k) y - B w y))
    (fun y => ∑ w ∈ V, B w y - rhoX Q y)
  beta_reduce at hs1 hs2
  have hp1 := pmass_le_one hV hpos
  have hp0 := pmass_nonneg V
  have hk0 : 0 ≤ C * (k : ℝ) ^ (-A) := mul_nonneg hC0 (by positivity)
  have hkp : C * (k : ℝ) ^ (-A) * pmass V ≤ C * (k : ℝ) ^ (-A) := by nlinarith
  linarith [h1, h2, h3, hs1, hs2, hkp]

end Positivity
end CollatzCLT
