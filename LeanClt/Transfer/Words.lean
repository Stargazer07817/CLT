import LeanClt.Transfer.Defs
import LeanClt.Elementary.Inverse
import LeanClt.Elementary.Syracuse

/-!
# Valuation words as residue classes, and counting in `[Y, 2Y]`

* `Kint a r = 2^{S_r} F_r(a)`, an integer (odd for `r ≥ 1`).
* `prefix_iff_mod`: an odd `N` has valuation word starting with `a_0, …, a_{r-1}` (total `S`)
  iff `3^r N + 2^S F_r(a) ≡ 2^S (mod 2^{S+1})`.
* `prefix_iff_modEq`: this is a single residue class `N ≡ c (mod 2^{S+1})`.
* `card_modEq_Icc`: a residue class mod `Q` meets an interval of length `ℓ` in `ℓ/Q ± 1` points.

This replaces the coupling import (Tao, Prop. 1.9) in Lemmas 5.1 and 5.3.
-/

open Real Finset

namespace CollatzCLT

/-! ## The integer `2^{S_r} F_r` -/

/-- `Kint a r = 2^{S_r} F_r(a)`, by the recursion `K_{j+1} = 3 K_j + 2^{S_j}`. -/
def Kint (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 3 * Kint a j + 2 ^ wsum a j

lemma Kint_cast (a : ℕ → ℕ) (j : ℕ) : (Kint a j : ℚ) = 2 ^ wsum a j * offset a j := by
  induction j with
  | zero => simp [Kint, offset]
  | succ j ih =>
    simp only [Kint, wsum, sum_range_succ, pow_add, offset] at ih ⊢
    push_cast
    rw [ih]
    field_simp

lemma wsum_pos {a : ℕ → ℕ} (ha : ∀ i, 1 ≤ a i) {j : ℕ} (hj : 1 ≤ j) : 1 ≤ wsum a j := by
  unfold wsum
  calc 1 ≤ a 0 := ha 0
    _ ≤ ∑ i ∈ range j, a i := single_le_sum (fun i _ => Nat.zero_le _) (mem_range.mpr hj)

lemma Kint_odd {a : ℕ → ℕ} (ha : ∀ i, 1 ≤ a i) {j : ℕ} (hj : 1 ≤ j) : Odd (Kint a j) := by
  induction j with
  | zero => omega
  | succ j ih =>
    simp only [Kint]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [Kint, wsum]
    · have h1 := ih hj0
      have h2 : Even (2 ^ wsum a j) := (Nat.even_pow' (by have := wsum_pos ha hj0; omega)).mpr
        even_two
      exact (Odd.mul (by decide : Odd 3) h1).add_even h2

/-! ## Dependence on the first `r` letters only -/

lemma wsum_congr {a b : ℕ → ℕ} {r : ℕ} (h : ∀ i < r, a i = b i) : wsum a r = wsum b r :=
  sum_congr rfl fun i hi => h i (mem_range.mp hi)

lemma offset_congr {a b : ℕ → ℕ} {r : ℕ} (h : ∀ i < r, a i = b i) : offset a r = offset b r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [offset]
    rw [ih (fun i hi => h i (by omega)), h r (by omega)]

lemma Kint_congr {a b : ℕ → ℕ} {r : ℕ} (h : ∀ i < r, a i = b i) : Kint a r = Kint b r := by
  have := Kint_cast a r
  rw [wsum_congr h, offset_congr h, ← Kint_cast b r] at this
  exact_mod_cast this

/-! ## The prefix condition is a residue class -/

/-- **An odd `N` has valuation prefix `a` iff `3^r N + 2^S F_r(a) ≡ 2^S (mod 2^{S+1})`.** -/
theorem prefix_iff_mod {a : ℕ → ℕ} (ha : ∀ i, 1 ≤ a i) (r : ℕ) {N : ℕ} (hN : Odd N) :
    (∀ i < r, vword N i = a i) ↔
      (3 ^ r * N + Kint a r) % 2 ^ (wsum a r + 1) = 2 ^ wsum a r := by
  set S := wsum a r
  constructor
  · intro h
    have hS : wsum (vword N) r = S := wsum_congr h
    have hK : Kint (vword N) r = Kint a r := Kint_congr h
    -- `2^S U^r(N) = 3^r N + K`
    have hU := U_iterate_affine N r
    rw [hS, offset_congr h] at hU
    have hKc := Kint_cast a r
    have heq : (2 ^ S * U^[r] N : ℚ) = 3 ^ r * N + Kint a r := by
      rw [hU, hKc]; field_simp; ring
    have heqN : 2 ^ S * U^[r] N = 3 ^ r * N + Kint a r := by exact_mod_cast heq
    obtain ⟨k, hk⟩ : Odd (U^[r] N) := by
      cases r with
      | zero => simpa using hN
      | succ r => rw [Function.iterate_succ_apply']; exact U_odd _
    rw [← heqN, hk, mul_add, mul_one, pow_succ,
      show 2 ^ S * (2 * k) = 2 ^ S * 2 * k by ring, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by have := Nat.one_le_two_pow (n := S); omega)
  · intro h
    -- `3^r N + K = 2^S (2q + 1)`
    set X := 3 ^ r * N + Kint a r with hX
    set q := X / 2 ^ (S + 1) with hq
    have hdiv : 2 ^ (S + 1) * q + X % 2 ^ (S + 1) = X := Nat.div_add_mod X (2 ^ (S + 1))
    rw [h] at hdiv
    set M := 2 * q + 1 with hM
    have hMeq : X = 2 ^ S * M := by
      rw [hM, show 2 ^ S * (2 * q + 1) = 2 ^ (S + 1) * q + 2 ^ S by ring]; exact hdiv.symm
    have hMo : Odd M := ⟨q, rfl⟩
    have hNq : ((N : ℤ) : ℚ) = 2 ^ wsum a r * ((M : ℚ) - offset a r) / 3 ^ r := by
      have hc : (3 ^ r * N + Kint a r : ℚ) = 2 ^ S * M := by exact_mod_cast hMeq
      rw [Kint_cast] at hc
      push_cast
      field_simp
      linarith
    obtain ⟨n, hn, -, hpre, -⟩ := source_exists ha hMo hNq
    have : n = N := by exact_mod_cast hn
    subst this
    exact hpre

lemma isUnit_three_zmod (k : ℕ) : IsUnit (3 : ZMod (2 ^ k)) := by
  have : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by decide)
  exact (ZMod.unitOfCoprime 3 this).isUnit

/-- **The prefix condition is a single residue class mod `2^{S+1}`**, and the class consists of
odd numbers. -/
theorem prefix_iff_modEq {a : ℕ → ℕ} (ha : ∀ i, 1 ≤ a i) (r : ℕ) :
    ∃ c : ℕ, ∀ N : ℕ, (Odd N ∧ ∀ i < r, vword N i = a i) ↔ N ≡ c [MOD 2 ^ (wsum a r + 1)] := by
  set S := wsum a r
  set Q := 2 ^ (S + 1)
  have hQ : 0 < Q := by positivity
  have hu := isUnit_three_zmod (S + 1)
  set c : ℕ := (((2 ^ S : ℕ) - (Kint a r : ZMod Q)) * hu.unit⁻¹ ^ r : ZMod Q).val
  refine ⟨c, fun N => ?_⟩
  have key : (3 ^ r * N + Kint a r) % Q = 2 ^ S ↔ N ≡ c [MOD Q] := by
    have h2S : 2 ^ S % Q = 2 ^ S := Nat.mod_eq_of_lt (by
      simp only [Q, pow_succ]; have := Nat.one_le_two_pow (n := S); omega)
    rw [← h2S, ← ZMod.natCast_eq_natCast_iff', ← ZMod.natCast_eq_natCast_iff]
    simp only [c, ZMod.natCast_val, ZMod.cast_id', id_eq]
    push_cast
    have h3 : ((3 : ZMod Q)) ^ r * (hu.unit⁻¹ : (ZMod Q)ˣ) ^ r = 1 := by
      rw [← mul_pow, IsUnit.mul_val_inv, one_pow]
    constructor
    · intro h
      calc (N : ZMod Q) = ((3 : ZMod Q) ^ r * N) * (hu.unit⁻¹ : (ZMod Q)ˣ) ^ r := by
            rw [mul_comm ((3 : ZMod Q) ^ r), mul_assoc, h3, mul_one]
        _ = (2 ^ S - Kint a r) * (hu.unit⁻¹ : (ZMod Q)ˣ) ^ r := by
            congr 1; rw [← h]; ring
    · intro h
      rw [h]
      calc (3 : ZMod Q) ^ r * ((2 ^ S - Kint a r) * (hu.unit⁻¹ : (ZMod Q)ˣ) ^ r) + Kint a r
          = (2 ^ S - Kint a r) * ((3 : ZMod Q) ^ r * (hu.unit⁻¹ : (ZMod Q)ˣ) ^ r) + Kint a r := by
            ring
        _ = 2 ^ S := by rw [h3]; ring
  constructor
  · rintro ⟨hN, hpre⟩
    exact key.mp ((prefix_iff_mod ha r hN).mp hpre)
  · intro hc
    have hmod := key.mpr hc
    -- members of the class are odd
    have hNo : Odd N := by
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp only [pow_zero, one_mul, Kint, add_zero, S, wsum, range_zero, sum_empty,
          zero_add, pow_one] at hmod
        exact Nat.odd_iff.mpr hmod
      · have hS1 : 1 ≤ S := wsum_pos ha hr
        have hKo := Kint_odd ha hr
        by_contra hev
        rw [Nat.not_odd_iff_even] at hev
        have hsum_odd : Odd (3 ^ r * N + Kint a r) := (hev.mul_left _).add_odd hKo
        have : Even ((3 ^ r * N + Kint a r) % Q) := by
          rw [hmod]; exact (Nat.even_pow' (by omega)).mpr even_two
        have h2 : (3 ^ r * N + Kint a r) % Q % 2 = (3 ^ r * N + Kint a r) % 2 :=
          Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))
        rw [Nat.even_iff] at this
        rw [Nat.odd_iff] at hsum_odd
        omega
    exact ⟨hNo, (prefix_iff_mod ha r hNo).mpr hmod⟩

/-! ## Counting in an interval -/

/-- A residue class mod `Q` meets `[lo, hi]` in `(hi + 1 - lo)/Q ± 1` points. -/
lemma card_modEq_Icc (lo hi Q c : ℕ) (hQ : 0 < Q) (hle : lo ≤ hi + 1) :
    |(((Icc lo hi).filter (fun N => N ≡ c [MOD Q])).card : ℝ) - ((hi + 1 - lo : ℕ) : ℝ) / Q| ≤ 1 := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  have h := Nat.Ico_filter_modEq_card lo (hi + 1) hQ c
  set A : ℤ := ⌈(((hi + 1 : ℕ) : ℚ) - c) / (Q : ℚ)⌉ with hA
  set B : ℤ := ⌈((lo : ℚ) - c) / (Q : ℚ)⌉ with hB
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hA1 := Int.le_ceil ((((hi + 1 : ℕ) : ℚ) - c) / (Q : ℚ))
  have hA2 := Int.ceil_lt_add_one ((((hi + 1 : ℕ) : ℚ) - c) / (Q : ℚ))
  have hB1 := Int.le_ceil (((lo : ℚ) - c) / (Q : ℚ))
  have hB2 := Int.ceil_lt_add_one (((lo : ℚ) - c) / (Q : ℚ))
  have hdiff : (((hi + 1 : ℕ) : ℚ) - c) / Q - ((lo : ℚ) - c) / Q = ((hi + 1 - lo : ℕ) : ℚ) / Q := by
    rw [Nat.cast_sub hle]; field_simp; ring
  have hle' : ((lo : ℚ) - c) / Q ≤ (((hi + 1 : ℕ) : ℚ) - c) / Q := by
    have : (0 : ℚ) ≤ ((hi + 1 - lo : ℕ) : ℚ) / Q := by positivity
    linarith
  have hAB : B ≤ A := Int.ceil_mono hle'
  rw [max_eq_left (by omega)] at h
  have hq : |((#{N ∈ Ico lo (hi + 1) | N ≡ c [MOD Q]} : ℕ) : ℚ) - ((hi + 1 - lo : ℕ) : ℚ) / Q| ≤ 1 := by
    have hcast : ((#{N ∈ Ico lo (hi + 1) | N ≡ c [MOD Q]} : ℕ) : ℚ) = ((A - B : ℤ) : ℚ) := by
      exact_mod_cast h
    rw [hcast, abs_le]; push_cast
    constructor <;> linarith
  have := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at this
  convert this using 2

end CollatzCLT
