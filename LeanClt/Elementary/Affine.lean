import LeanClt.Elementary.Orbits

/-!
# Valuation words and the affine identity (§2.2)

A *word* is a sequence `a : ℕ → ℕ`, read from step `0`: step `i` applies
`x ↦ (3x+1)/2^{a i}` (0-based here; the paper's `a_{i+1}`).

* `affIter a r x`: the composite of the first `r` affine steps (the paper's `Aff_{\vec a}`).
* `offset a r`: the paper's `F_r(\vec a)`, defined by the recursion
  `F_0 = 0`, `F_{r+1} = (3 F_r + 1) / 2^{a_r}`; `offset_eq_sum` proves it equals the
  closed form `∑_{j<r} 3^{r-1-j} 2^{-(a_j+⋯+a_{r-1})}` of (2.1).
* **(2.1)** `affIter a r x = 3^r 2^{-S_r} x + F_r`, and `0 ≤ F_r ≤ (3/2)^r - 1`, `F_r > 0` for `r ≥ 1`.
* **(2.1) for orbits:** `U^r(N) = Aff_{\vec a^{(r)}(N)}(N)` with `\vec a^{(r)}(N)` the valuation word.
* **Lemma 2.1, uniqueness:** a word and an endpoint determine the source.
-/

open Function Finset

namespace CollatzCLT

/-- One affine step `x ↦ (3x+1)/2^a` on `ℚ`. -/
def aff (a : ℕ) (x : ℚ) : ℚ := (3 * x + 1) / 2 ^ a

/-- The composite of the first `r` affine steps of the word `a`. -/
def affIter (a : ℕ → ℕ) : ℕ → ℚ → ℚ
  | 0, x => x
  | r + 1, x => aff (a r) (affIter a r x)

/-- Partial sum `S_r = a_0 + ⋯ + a_{r-1}`. -/
def wsum (a : ℕ → ℕ) (r : ℕ) : ℕ := ∑ i ∈ range r, a i

/-- The offset `F_r(\vec a)`, by recursion. -/
def offset (a : ℕ → ℕ) : ℕ → ℚ
  | 0 => 0
  | r + 1 => (3 * offset a r + 1) / 2 ^ a r

/-- **Affine identity (2.1)** for an abstract word. -/
theorem affIter_eq (a : ℕ → ℕ) (r : ℕ) (x : ℚ) :
    affIter a r x = 3 ^ r / 2 ^ wsum a r * x + offset a r := by
  induction r with
  | zero => simp [affIter, wsum, offset]
  | succ r ih =>
    simp only [affIter, aff, ih, offset, wsum, sum_range_succ, pow_add, pow_succ]
    field_simp
    ring

/-- The recursive offset equals the closed form of (2.1). -/
theorem offset_eq_sum (a : ℕ → ℕ) (r : ℕ) :
    offset a r = ∑ j ∈ range r, (3 : ℚ) ^ (r - 1 - j) / 2 ^ (∑ i ∈ Ico j r, a i) := by
  induction r with
  | zero => simp [offset]
  | succ r ih =>
    rw [offset, ih, sum_range_succ, mul_sum, add_div, sum_div]
    congr 1
    · apply sum_congr rfl
      intro j hj
      have hj : j < r := mem_range.mp hj
      rw [sum_Ico_succ_top (by omega : j ≤ r), pow_add]
      have : r + 1 - 1 - j = (r - 1 - j) + 1 := by omega
      rw [this, pow_succ]
      field_simp
    · simp

/-- `0 ≤ F_r` when all letters are `≥ 1` (in fact for any word). -/
lemma offset_nonneg (a : ℕ → ℕ) (r : ℕ) : 0 ≤ offset a r := by
  induction r with
  | zero => simp [offset]
  | succ r ih => simp only [offset]; positivity

/-- `F_r > 0` for `r ≥ 1`. -/
lemma offset_pos (a : ℕ → ℕ) {r : ℕ} (hr : 0 < r) : 0 < offset a r := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt hr
  simp only [zero_add, offset]
  have := offset_nonneg a r
  positivity

/-- `F_r ≤ (3/2)^r - 1` when all letters are `≥ 1`, hence `F_r < 3^r`. -/
lemma offset_le (a : ℕ → ℕ) (ha : ∀ i, 1 ≤ a i) (r : ℕ) :
    offset a r ≤ (3 / 2 : ℚ) ^ r - 1 := by
  induction r with
  | zero => simp [offset]
  | succ r ih =>
    simp only [offset]
    have h2 : (2 : ℚ) ≤ 2 ^ a r := by
      calc (2 : ℚ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a r := pow_le_pow_right₀ (by norm_num) (ha r)
    have hnum : 0 ≤ 3 * offset a r + 1 := by have := offset_nonneg a r; linarith
    calc (3 * offset a r + 1) / 2 ^ a r ≤ (3 * offset a r + 1) / 2 :=
          div_le_div_of_nonneg_left hnum (by norm_num) h2
      _ ≤ (3 * ((3 / 2 : ℚ) ^ r - 1) + 1) / 2 := by gcongr
      _ = (3 / 2 : ℚ) ^ (r + 1) - 1 := by ring

/-- `affIter` only depends on the first `r` letters. -/
lemma affIter_congr {a b : ℕ → ℕ} {r : ℕ} (h : ∀ i < r, a i = b i) (x : ℚ) :
    affIter a r x = affIter b r x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [affIter]
    rw [ih (fun i hi => h i (by omega)), h r (by omega)]

/-! ## The valuation word of an integer -/

/-- The valuation word of `N`: letter `i` is `v₂(3 U^i(N) + 1)`. -/
def vword (N : ℕ) (i : ℕ) : ℕ := padicValNat 2 (3 * U^[i] N + 1)

/-- One Syracuse step is the affine step with letter `v₂(3n+1)` (exact division). -/
lemma U_cast (n : ℕ) : (U n : ℚ) = aff (padicValNat 2 (3 * n + 1)) n := by
  have hdvd : 2 ^ padicValNat 2 (3 * n + 1) ∣ 3 * n + 1 := pow_padicValNat_dvd
  simp only [U, aff]
  rw [Nat.cast_div hdvd (by positivity)]
  push_cast; ring

/-- **Affine identity (2.1) for orbits:** `U^r(N) = Aff_{\vec a^{(r)}(N)}(N)`. -/
theorem U_iterate_eq_affIter (N r : ℕ) : (U^[r] N : ℚ) = affIter (vword N) r N := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [iterate_succ_apply', U_cast, ih]
    rfl

/-- **(2.1)**: `U^r(N) = 3^r 2^{-S_r} N + F_r(\vec a^{(r)}(N))`. -/
theorem U_iterate_affine (N r : ℕ) :
    (U^[r] N : ℚ) = 3 ^ r / 2 ^ wsum (vword N) r * N + offset (vword N) r := by
  rw [U_iterate_eq_affIter, affIter_eq]

/-- **Lemma 2.1, uniqueness.** If `N` and `N'` have the same valuation word of length `r`
and the same `U^r`-image, they are equal. -/
theorem source_unique {N N' r : ℕ} (hw : ∀ i < r, vword N i = vword N' i)
    (hM : U^[r] N = U^[r] N') : N = N' := by
  have h1 := U_iterate_eq_affIter N r
  have h2 := U_iterate_eq_affIter N' r
  rw [affIter_congr hw] at h1
  rw [hM, h2, affIter_eq, affIter_eq] at h1
  have hpos : (0 : ℚ) < 3 ^ r / 2 ^ wsum (vword N') r := by positivity
  have : (N' : ℚ) = N := by
    have := h1; field_simp at this; nlinarith [this]
  exact_mod_cast this.symm

/-- **Lemma 2.1, the inverse formula (2.2).** The source is
`N = 2^S (M - F_r) / 3^r`, where `M = U^r(N)`. -/
theorem source_formula (N r : ℕ) :
    (N : ℚ) = 2 ^ wsum (vword N) r * ((U^[r] N : ℚ) - offset (vword N) r) / 3 ^ r := by
  rw [U_iterate_affine]
  field_simp
  ring

end CollatzCLT
