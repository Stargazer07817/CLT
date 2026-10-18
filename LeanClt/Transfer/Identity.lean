import LeanClt.Transfer.Smooth

/-!
# Lemma 5.8: the exact smoothing identity, depth by depth

At depth `r = m + t`, under `Q_m μ_r` the residue is a uniform lift of `X_m` and the counter is
`S_m + S'_t` with an independent tail:
`(Q_m μ_r)(S, z) = 3^{-t} ∑_{S₁} μ_m(S₁, z mod 3^m) P(S_t = S - S₁)` (`Qop_split`). Inserting
this into `∑_{S,z} (Q_m μ_r)(S,z) L_Y G̃(S,z)` and writing
`2^S 3^{-t} = Y (3^m/M) e^{Z'_t - u}`, `u = log(Y/M) - Z_m`, the window `Y ≤ 2^S M/3^r ≤ 2Y`
becomes `0 ≤ Z'_t - u ≤ ℓ` and the depth-`r` term is the `t`-th term of the renewal kernel
(`depth_identity`).
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-- **`Q_m μ_{m+t}` in terms of `μ_m` and the tail law.** -/
lemma Qop_split (m t S : ℕ) (z : ZMod (3 ^ (m + t))) :
    Qop (m + t) m (muJ (m + t)) S z =
      (1 / 3 ^ t : ℝ) * ∑ S1 ∈ range (S + 1), muJ m S1 (ZMod.cast z) * lawS t (S - S1) := by
  unfold Qop
  congr 1
  · rw [Nat.cast_add, sub_add_cancel_left, zpow_neg, zpow_natCast, one_div]
  -- collapse the sum over lifts
  have h1 : ∑ y : ZMod (3 ^ (m + t)), (if (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast z then
      muJ (m + t) S y else 0) = ∑ a ∈ words (m + t) S,
        if (ZMod.cast (Xmod a) : ZMod (3 ^ m)) = ZMod.cast z then (1 / 2 : ℝ) ^ S else 0 := by
    unfold muJ
    have e : ∀ y : ZMod (3 ^ (m + t)), (if (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast z then
        ∑ a ∈ words (m + t) S, (if Xmod a = y then (1 / 2 : ℝ) ^ S else 0) else 0) =
        ∑ a ∈ words (m + t) S, (if Xmod a = y ∧ (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast z then
          (1 / 2 : ℝ) ^ S else 0) := by
      intro y
      split_ifs with h
      · exact Finset.sum_congr rfl fun a _ => by simp [h]
      · simp [h]
    rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (Xmod a)]
    · simp
    · intro y _ hy
      rw [if_neg]
      rintro ⟨h, -⟩
      exact hy h.symm
    · simp
  rw [h1, sum_words_append m t S]
  refine Finset.sum_congr rfl fun S1 hS1 => ?_
  have hS1 := mem_range.mp hS1
  unfold muJ
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a1 _ => ?_
  have hc : ∀ a2 : Fin t → ℕ, (ZMod.cast (Xmod (Fin.append a1 a2)) : ZMod (3 ^ m)) = Xmod a1 := by
    intro a2
    have := cast_Xmod_append a1 a2
    rwa [ZMod.castHom_apply] at this
  rw [Finset.sum_congr rfl (fun a2 _ => by rw [hc a2])]
  split_ifs with h
  · rw [← sum_words_half, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a2 _ => ?_
    rw [← pow_add]; congr 1; omega
  · simp

/-- `u = log(Y/M) - Z_m` at `S_m = S₁`. -/
def uMS (Y : ℝ) (M S1 m : ℕ) : ℝ := Real.log (Y / M) - (ell * S1 - bet * m)

lemma Zval_sub_uMS {Y : ℝ} (hY : 0 < Y) {M : ℕ} (hM : 0 < M) (m t S1 A : ℕ) :
    Zval t A - uMS Y M S1 m = Real.log (2 ^ (S1 + A) * (M : ℝ) / 3 ^ (m + t) / Y) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Real.log_div (by positivity) hY.ne', Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) hM0.ne', Real.log_pow, Real.log_pow]
  unfold Zval uMS ell bet
  rw [Real.log_div hY.ne' hM0.ne']
  push_cast; ring

/-- The renewal window is the simplified source window. -/
lemma window_iff_win {Y : ℝ} (hY : 0 < Y) {M : ℕ} (hM : 0 < M) (m t S1 A : ℕ) :
    (0 ≤ Zval t A - uMS Y M S1 m ∧ Zval t A - uMS Y M S1 m ≤ ell) ↔
      win Y (m + t) (S1 + A) M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Zval_sub_uMS hY hM]
  unfold win ell
  have hw0 : (0 : ℝ) < 2 ^ (S1 + A) * (M : ℝ) / 3 ^ (m + t) := by positivity
  rw [Real.log_nonneg_iff (by positivity), one_le_div hY,
    Real.log_le_log_iff (by positivity) (by norm_num), div_le_iff₀ hY]

lemma rterm_zero_of_not_win {ρ η s Y : ℝ} (hY : 0 < Y) {M : ℕ} (hM : 0 < M) {m t S1 A : ℕ}
    (h : ¬ win Y (m + t) (S1 + A) M) : rterm ρ η s (uMS Y M S1 m) t A = 0 := by
  unfold rterm
  rw [if_neg (fun h' => h ((window_iff_win hY hM m t S1 A).mp h'))]

open Classical in
/-- **One term of the identity.** -/
lemma rterm_eq {Y : ℝ} (hY : 0 < Y) (q : ℕ → ℝ) (ρ η s : ℝ) {M : ℕ} (hM : 0 < M)
    (m t S1 A : ℕ) :
    ((Y * 3 ^ m / M : ℝ) : ℂ) * phase q ρ η s M S1 m * rterm ρ η s (uMS Y M S1 m) t A =
      if win Y (m + t) (S1 + A) M then
        ((lawS t A * (1 / 3 ^ t) : ℝ) : ℂ) *
          ((2 : ℂ) ^ (S1 + A) * phase q ρ η s M (S1 + A) (m + t))
      else 0 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  by_cases h : win Y (m + t) (S1 + A) M
  · rw [if_pos h]
    unfold rterm
    rw [if_pos ((window_iff_win hY hM m t S1 A).mpr h), Zval_sub_uMS hY hM,
      Real.exp_log (by positivity)]
    have hph : phase q ρ η s M S1 m * cexp (-(((s * (ρ * A + η * t)) : ℝ) : ℂ) * I) =
        phase q ρ η s M (S1 + A) (m + t) := by
      unfold phase; rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hreal : Y * 3 ^ m / M * (2 ^ (S1 + A) * (M : ℝ) / 3 ^ (m + t) / Y) =
        2 ^ (S1 + A) * (1 / 3 ^ t) := by
      rw [pow_add 3 m t]; field_simp
    calc ((Y * 3 ^ m / M : ℝ) : ℂ) * phase q ρ η s M S1 m *
          ((lawS t A : ℂ) * ((2 ^ (S1 + A) * (M : ℝ) / 3 ^ (m + t) / Y : ℝ) : ℂ) *
            cexp (-(((s * (ρ * A + η * t)) : ℝ) : ℂ) * I))
        = ((Y * 3 ^ m / M * (2 ^ (S1 + A) * (M : ℝ) / 3 ^ (m + t) / Y) : ℝ) : ℂ) *
            (lawS t A : ℂ) * (phase q ρ η s M S1 m *
              cexp (-(((s * (ρ * A + η * t)) : ℝ) : ℂ) * I)) := by push_cast; ring
      _ = _ := by rw [hreal, hph]; push_cast; ring
  · rw [if_neg h, rterm_zero_of_not_win hY hM h, mul_zero]

/-- **Lemma 5.8 at one depth `r = m + t`.** -/
theorem depth_identity {Y : ℝ} (hY : 0 < Y) (E : Finset ℕ) (hEpos : ∀ M ∈ E, 0 < M)
    (q : ℕ → ℝ) (ρ η s : ℝ) (m t K : ℕ)
    (hK : ∀ S M, M ∈ E → win Y (m + t) S M → S ≤ K) :
    ∑ S ∈ range (K + 1), ∑ z : ZMod (3 ^ (m + t)),
        (Qop (m + t) m (muJ (m + t)) S z : ℂ) * Gt Y E q ρ η s (m + t) S z =
      ∑ M ∈ E, ∑ S1 ∈ range (K + 1), (muJ m S1 (M : ZMod (3 ^ m)) : ℂ) *
        (((Y * 3 ^ m / M : ℝ) : ℂ) * phase q ρ η s M S1 m * rinner ρ η s (uMS Y M S1 m) t) := by
  classical
  set G : ℕ → ℕ → ℕ → ℂ := fun M S1 A => if win Y (m + t) (S1 + A) M then
    (muJ m S1 (M : ZMod (3 ^ m)) : ℂ) * (((lawS t A * (1 / 3 ^ t) : ℝ) : ℂ) *
      ((2 : ℂ) ^ (S1 + A) * phase q ρ η s M (S1 + A) (m + t))) else 0 with hG
  -- the sum over residues collapses onto `z = M mod 3^r`
  have hb : ∀ S, ∑ z : ZMod (3 ^ (m + t)),
      (Qop (m + t) m (muJ (m + t)) S z : ℂ) * Gt Y E q ρ η s (m + t) S z =
      ∑ M ∈ E, ∑ S1 ∈ range (S + 1), G M S1 (S - S1) := by
    intro S
    unfold Gt
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun M _ => ?_
    have hcast : (ZMod.cast ((M : ZMod (3 ^ (m + t)))) : ZMod (3 ^ m)) = (M : ZMod (3 ^ m)) :=
      ZMod.cast_natCast (pow_dvd_pow 3 (Nat.le_add_right m t)) M
    by_cases hw : win Y (m + t) S M
    · simp only [hw, and_true, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), Qop_split, hcast]
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun S1 hS1 => ?_
      have hS1 := mem_range.mp hS1
      have hSS : S1 + (S - S1) = S := by omega
      simp only [hG, hSS, hw, ↓reduceIte]
      push_cast; ring
    · simp only [hw, and_false, ↓reduceIte, mul_zero, Finset.sum_const_zero]
      symm
      refine Finset.sum_eq_zero fun S1 hS1 => ?_
      have hS1 := mem_range.mp hS1
      have hSS : S1 + (S - S1) = S := by omega
      simp only [hG, hSS, hw, ↓reduceIte]
  simp_rw [hb]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun M hM => ?_
  have hM0 := hEpos M hM
  rw [Finset.sum_range_diag_flip (K + 1) (G M)]
  refine Finset.sum_congr rfl fun S1 hS1 => ?_
  have hS1 := mem_range.mp hS1
  -- the renewal sum over `A` is finite
  have hfin : rinner ρ η s (uMS Y M S1 m) t =
      ∑ A ∈ range (K + 1 - S1), rterm ρ η s (uMS Y M S1 m) t A := by
    unfold rinner
    refine tsum_eq_sum fun A hA => ?_
    rw [mem_range, not_lt] at hA
    refine rterm_zero_of_not_win hY hM0 fun hw => ?_
    have := hK _ M hM hw
    omega
  rw [hfin, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [rterm_eq hY q ρ η s hM0 m t S1 A]
  simp only [hG]
  split_ifs <;> simp

end CollatzCLT
