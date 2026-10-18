import LeanClt.Elementary.Orbits

/-!
# Lemma 8.7: a nonperiodic seed in any residue class

**Lemma 8.7 [`lem:seed`].** Let `3 ∤ a` and choose `e ∈ {1, 2}` with `2^e a ≡ 1 (mod 3)`. The odd
integers `R_j = (2^e a 4^j - 1)/3` satisfy `3 R_j + 1 = 2^{e+2j} a`, so `R_j ∈ P_T(a)`; and
`v₃(R_{j+t} - R_j) = v₃(t)`, so any `3^Q` consecutive indices give `3^Q` distinct residues mod `3^Q`,
i.e. every residue class. Two indices in the class give two seeds with the same `U`-image (the odd
part of `a`), and at most one of them is `U`-periodic, because a periodic point has exactly one
preimage on its cycle.

The Lean statement allows any residue `y` and any lower bound `B` (the paper uses the favourable
class `y_*` and `B = 16^{b₀}`); the proof is the paper's.

* `seedR c j = (c 4^j - 1)/3`; `three_seedR`: `3 R_j + 1 = c 4^j` when `c ≡ 1 (mod 3)`.
* `seedR_not_modEq`: distinct indices less than `3^Q` apart are distinct mod `3^Q` (lifting the
  exponent: `v₃(4^t - 1) = 1 + v₃(t)`).
* `seedR_hits`: every window of `3^Q` consecutive indices meets every residue class.
* `eq_of_U_periodic`: two `U`-periodic points with the same `U`-image are equal.
* `seed`: the lemma.
-/

open Function Finset

namespace CollatzCLT
namespace Positivity

/-! ## The candidate seeds -/

/-- `R_j = (c 4^j - 1)/3`, with `c = 2^e a`. -/
def seedR (c j : ℕ) : ℕ := (c * 4 ^ j - 1) / 3

lemma mul_four_pow_mod {c : ℕ} (hc : c % 3 = 1) (j : ℕ) : c * 4 ^ j % 3 = 1 := by
  rw [Nat.mul_mod, Nat.pow_mod]; simp [hc]

lemma three_seedR {c : ℕ} (hc : c % 3 = 1) (j : ℕ) : 3 * seedR c j + 1 = c * 4 ^ j := by
  have h := mul_four_pow_mod hc j
  unfold seedR
  generalize c * 4 ^ j = x at h ⊢
  omega

lemma seedR_odd {c : ℕ} (hc : c % 3 = 1) (hce : Even c) (j : ℕ) : Odd (seedR c j) := by
  have h := three_seedR hc j
  have he : Even (3 * seedR c j + 1) := by rw [h]; exact hce.mul_right _
  have h3 : Odd (3 * seedR c j) := by
    rcases Nat.even_or_odd (3 * seedR c j) with h' | h'
    · exact absurd he (by rw [Nat.even_add_one]; exact not_not.mpr h')
    · exact h'
  exact (Nat.odd_mul.mp h3).2

lemma three_mul_add_one_le (j : ℕ) : 3 * j + 1 ≤ 2 * 4 ^ j := by
  induction j with
  | zero => norm_num
  | succ k ih =>
    have := Nat.one_le_pow k 4 (by norm_num)
    rw [pow_succ]; omega

lemma le_seedR {c : ℕ} (hc : c % 3 = 1) (hc2 : 2 ≤ c) (j : ℕ) : j ≤ seedR c j := by
  have h := three_seedR hc j
  have h4 := three_mul_add_one_le j
  have : 2 * 4 ^ j ≤ c * 4 ^ j := Nat.mul_le_mul_right _ hc2
  omega

lemma seedR_injective {c : ℕ} (hc : c % 3 = 1) (hc0 : 0 < c) : Injective (seedR c) := by
  intro j j' h
  have h1 := three_seedR hc j
  have h2 := three_seedR hc j'
  rw [h] at h1
  have : c * 4 ^ j = c * 4 ^ j' := by rw [← h1, h2]
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) (Nat.eq_of_mul_eq_mul_left hc0 this)

/-- **Lifting the exponent:** if `3^{Q+1} ∣ 4^t - 1` with `t > 0` then `3^Q ∣ t`. -/
lemma three_pow_dvd_of_dvd_four_pow_sub {Q t : ℕ} (ht : 0 < t) (h : 3 ^ (Q + 1) ∣ 4 ^ t - 1) :
    3 ^ Q ∣ t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlte : padicValNat 3 (4 ^ t - 1 ^ t) = padicValNat 3 (4 - 1) + padicValNat 3 t :=
    padicValNat.pow_sub_pow (by decide) (by norm_num) (by norm_num) (by norm_num) ht.ne'
  rw [one_pow] at hlte
  have h41 : 4 ^ t - 1 ≠ 0 := by
    have : 1 < 4 ^ t := Nat.one_lt_pow ht.ne' (by norm_num)
    omega
  have hv := (padicValNat_dvd_iff_le h41).mp h
  have h3 : padicValNat 3 (4 - 1) = 1 := by norm_num [padicValNat.self]
  rw [hlte, h3] at hv
  exact (padicValNat_dvd_iff_le ht.ne').mpr (by omega)

lemma coprime_three_pow {c : ℕ} (hc : c % 3 = 1) (Q j : ℕ) :
    Nat.gcd (3 ^ (Q + 1)) (c * 4 ^ j) = 1 := by
  have h3c : Nat.Coprime 3 c := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  have h34 : Nat.Coprime 3 (4 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
  exact Nat.Coprime.pow_left _ (Nat.Coprime.mul_right h3c h34)

/-- Distinct indices less than `3^Q` apart give distinct residues mod `3^Q`. -/
lemma seedR_not_modEq {c : ℕ} (hc : c % 3 = 1) {Q j t : ℕ} (ht : 0 < t) (htQ : t < 3 ^ Q) :
    ¬ seedR c j ≡ seedR c (j + t) [MOD 3 ^ Q] := by
  intro h
  have h1 : 3 * seedR c j + 1 ≡ 3 * seedR c (j + t) + 1 [MOD 3 ^ (Q + 1)] := by
    have := Nat.ModEq.mul_left' 3 h
    rw [← pow_succ'] at this
    exact Nat.ModEq.add_right 1 this
  rw [three_seedR hc, three_seedR hc, pow_add 4 j t, ← mul_assoc] at h1
  have h2 : 1 ≡ 4 ^ t [MOD 3 ^ (Q + 1)] := by
    have h1' : c * 4 ^ j * 1 ≡ c * 4 ^ j * 4 ^ t [MOD 3 ^ (Q + 1)] := by rwa [mul_one]
    exact Nat.ModEq.cancel_left_of_coprime (coprime_three_pow hc Q j) h1'
  have h3 : 3 ^ (Q + 1) ∣ 4 ^ t - 1 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h2
  have h4 := three_pow_dvd_of_dvd_four_pow_sub ht h3
  have := Nat.le_of_dvd ht h4
  omega

/-- Every window of `3^Q` consecutive indices meets every residue class mod `3^Q`. -/
lemma seedR_hits {c : ℕ} (hc : c % 3 = 1) (Q J : ℕ) (y : ZMod (3 ^ Q)) :
    ∃ j, J ≤ j ∧ j < J + 3 ^ Q ∧ (seedR c j : ZMod (3 ^ Q)) = y := by
  let φ : Fin (3 ^ Q) → ZMod (3 ^ Q) := fun i => (seedR c (J + i) : ZMod (3 ^ Q))
  have hinj : Injective φ := by
    intro i i' h
    have h' : seedR c (J + i) ≡ seedR c (J + i') [MOD 3 ^ Q] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp h
    by_contra hne
    have hne' : (i : ℕ) ≠ i' := fun e => hne (Fin.ext e)
    have hi := i.isLt
    have hi' := i'.isLt
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
    · have := seedR_not_modEq hc (Q := Q) (j := J + i) (t := i' - i) (by omega) (by omega)
      rw [show J + i + (i' - i) = J + i' by omega] at this
      exact this h'
    · have := seedR_not_modEq hc (Q := Q) (j := J + i') (t := i - i') (by omega) (by omega)
      rw [show J + i' + (i - i') = J + i by omega] at this
      exact this h'.symm
  have hbij : Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, by simp [ZMod.card]⟩
  obtain ⟨i, hi⟩ := hbij.2 y
  exact ⟨J + i, by omega, by omega, hi⟩

/-! ## Periodic points and their preimages -/

/-- Two `U`-periodic points with the same `U`-image are equal: a periodic point has exactly one
preimage on its cycle. -/
lemma eq_of_U_periodic {R R' p p' : ℕ} (hp : 0 < p) (hp' : 0 < p') (hR : U^[p] R = R)
    (hR' : U^[p'] R' = R') (hU : U R = U R') : R = R' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hp
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_lt hp'
  simp only [zero_add] at *
  set c := U R with hc
  -- `R = U^[k] c` and `c` is periodic with period `k + 1`
  have hRc : U^[k] c = R := by rw [hc, ← iterate_succ_apply]; exact hR
  have hRc' : U^[k'] c = R' := by rw [hU, ← iterate_succ_apply]; exact hR'
  have hper : IsPeriodicPt U (k + 1) c := by
    change U^[k + 1] c = c
    rw [iterate_succ_apply', hRc]
  have hper' : IsPeriodicPt U (k' + 1) c := by
    change U^[k' + 1] c = c
    rw [iterate_succ_apply', hRc', ← hU]
  -- both equal `U^[(k+1)(k'+1) - 1] c`
  have e1 : U^[k + (k + 1) * k'] c = R := by
    rw [iterate_add_apply, (hper.mul_const k').eq, hRc]
  have e2 : U^[k' + (k' + 1) * k] c = R' := by
    rw [iterate_add_apply, (hper'.mul_const k).eq, hRc']
  rw [← e1, ← e2]
  congr 1
  ring

/-! ## The seed -/

lemma T_iterate_two_pow_mul (k a : ℕ) : T^[k] (2 ^ k * a) = a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply]
    have hev : Even (2 ^ (k + 1) * a) := by rw [pow_succ]; exact ⟨2 ^ k * a, by ring⟩
    rw [T_of_even hev, show 2 ^ (k + 1) * a = 2 * (2 ^ k * a) by ring,
      Nat.mul_div_cancel_left _ (by norm_num), ih]

lemma U_of_three_add_one {R k a : ℕ} (ha : 0 < a) (h : 3 * R + 1 = 2 ^ k * a) :
    U R = a / 2 ^ padicValNat 2 a := by
  unfold U
  rw [h, padicValNat.mul (by positivity) ha.ne', padicValNat.prime_pow, pow_add,
    Nat.mul_div_mul_left _ _ (by positivity)]

/-- **Lemma 8.7 [`lem:seed`]**, for any residue class `y` mod `3^Q`: there is a `U`-nonperiodic odd
seed `M ≥ B` in `P_T(a)` with `M ≡ y (mod 3^Q)`. -/
theorem seed {a : ℕ} (ha : 0 < a) (h3 : ¬ 3 ∣ a) (Q B : ℕ) (y : ZMod (3 ^ Q)) :
    ∃ M : ℕ, Odd M ∧ B ≤ M ∧ (M : ZMod (3 ^ Q)) = y ∧ M ∈ Pred T a ∧
      ∀ p, 0 < p → U^[p] M ≠ M := by
  -- `c = 2^e a ≡ 1 (mod 3)` with `e ∈ {1, 2}`
  set e : ℕ := if a % 3 = 2 then 1 else 2 with he
  set c : ℕ := 2 ^ e * a with hcdef
  have he1 : 1 ≤ e := by rw [he]; split_ifs <;> norm_num
  have hc : c % 3 = 1 := by
    rw [hcdef, he]
    split_ifs with h
    · simp only [pow_one]; omega
    · have : a % 3 = 1 := by omega
      norm_num; omega
  have hce : Even c := by
    rw [hcdef]
    obtain ⟨f, hf⟩ := Nat.exists_eq_add_of_le he1
    rw [hf, pow_add]; exact ⟨2 ^ f * a, by ring⟩
  have hc2 : 2 ≤ c := by
    have : 2 ≤ 2 ^ e := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he1
    calc 2 ≤ 2 ^ e := this
      _ ≤ 2 ^ e * a := Nat.le_mul_of_pos_right _ ha
  -- `3 R_j + 1 = 2^{e + 2j} a`
  have h3R : ∀ j, 3 * seedR c j + 1 = 2 ^ (e + 2 * j) * a := by
    intro j
    rw [three_seedR hc, hcdef, pow_add, pow_mul]; norm_num; ring
  have hUR : ∀ j, U (seedR c j) = a / 2 ^ padicValNat 2 a := fun j => U_of_three_add_one ha (h3R j)
  have hpred : ∀ j, seedR c j ∈ Pred T a := by
    intro j
    refine ⟨(seedR_odd hc hce j).pos, e + 2 * j + 1, ?_⟩
    rw [iterate_succ_apply, T_of_odd (Nat.not_even_iff_odd.mpr (seedR_odd hc hce j)), h3R j,
      T_iterate_two_pow_mul]
  -- two indices in the class `y`, in disjoint windows above `B`
  obtain ⟨j1, hj1, hj1', hy1⟩ := seedR_hits hc Q B y
  obtain ⟨j2, hj2, hj2', hy2⟩ := seedR_hits hc Q (B + 3 ^ Q) y
  have hne : seedR c j1 ≠ seedR c j2 := fun h =>
    absurd (seedR_injective hc (by omega) h) (by omega)
  -- at most one of them is periodic
  by_cases hper : ∃ p, 0 < p ∧ U^[p] (seedR c j1) = seedR c j1
  · refine ⟨seedR c j2, seedR_odd hc hce j2, le_trans (by omega) (le_seedR hc hc2 j2), hy2,
      hpred j2, fun p hp hp2 => ?_⟩
    obtain ⟨p1, hp1, hp1'⟩ := hper
    exact hne (eq_of_U_periodic hp1 hp hp1' hp2 (by rw [hUR, hUR]))
  · exact ⟨seedR c j1, seedR_odd hc hce j1, le_trans hj1 (le_seedR hc hc2 j1), hy1, hpred j1,
      fun p hp h => hper ⟨p, hp, h⟩⟩

end Positivity
end CollatzCLT
