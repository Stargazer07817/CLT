import LeanClt.Mixing.Imports

/-!
# §3: finite Fourier analysis on `ℤ/3^nℤ`

The proof of Proposition 3.4 (`prop:neardiag`) uses Plancherel on the finite group `ℤ/3^nℤ` and
the fact that `Q_m` is the projection onto the frequencies `ξ` with `3^m ξ = 0`, i.e. the `ξ`
divisible by `3^{n-m}`. Only finite sums occur.

* `chiZ_eq_stdAddChar`: `χ_ξ(x) = e(-(ξx)/3^n)` is Mathlib's standard additive character at
  `-(ξx)`; hence `chiZ_add`, `norm_chiZ`, and the orthogonality `sum_chiZ`.
* `fourierZ Φ ξ = ∑_x χ_ξ(x) Φ(x)` and `plancherel`: `∑_ξ |Φ̂(ξ)|² = 3^n ∑_x |Φ(x)|²`.
* `card_cast_fiber`: each residue mod `3^m` has exactly `3^{n-m}` lifts mod `3^n`.
* `Qs n m Φ`: the operator `Q^{(n)}_m` of (2.4, `eq:Q`) on a single counter slice;
  `fourierZ_Qs`: `(Q_m Φ)^(ξ) = Φ̂(ξ)` if `3^m ξ = 0` and `0` otherwise.
* `l2_sub_Qs_le`: if `Φ̂ = Ψ̂ · T` with `|T(ξ)| ≤ β` at every frequency excluded by `Q_m`, then
  `∑_x |Φ - Q_m Φ|² ≤ β² ∑_x |Ψ|²`. This is the "joint Plancherel" step of Proposition 3.4,
  in the counter-resolved form (one counter slice at a time; no Fourier analysis in the counter).
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

variable {n : ℕ}

/-! ## The characters -/

lemma chiZ_eq_stdAddChar (ξ x : ZMod (3 ^ n)) : chiZ ξ x = ZMod.stdAddChar (-(ξ * x)) := by
  have h : (-(ξ * x) : ZMod (3 ^ n)) = (((-((ξ * x).val : ℤ)) : ℤ) : ZMod (3 ^ n)) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [h, ZMod.stdAddChar_coe, chiZ]
  congr 1
  push_cast
  ring

lemma chiZ_add (ξ x y : ZMod (3 ^ n)) : chiZ ξ (x + y) = chiZ ξ x * chiZ ξ y := by
  rw [chiZ_eq_stdAddChar, chiZ_eq_stdAddChar, chiZ_eq_stdAddChar, mul_add, neg_add,
    AddChar.map_add_eq_mul]

lemma chiZ_zero (ξ : ZMod (3 ^ n)) : chiZ ξ 0 = 1 := by
  rw [chiZ_eq_stdAddChar, mul_zero, neg_zero, AddChar.map_zero_eq_one]

lemma norm_chiZ (ξ x : ZMod (3 ^ n)) : ‖chiZ ξ x‖ = 1 := by
  rw [chiZ_eq_stdAddChar, ZMod.stdAddChar_apply, Circle.norm_coe]

lemma chiZ_mul_conj (ξ x y : ZMod (3 ^ n)) :
    chiZ ξ x * (starRingEnd ℂ) (chiZ ξ y) = chiZ ξ (x - y) := by
  have h : chiZ ξ x = chiZ ξ (x - y) * chiZ ξ y := by rw [← chiZ_add, sub_add_cancel]
  rw [h, mul_assoc, Complex.mul_conj', norm_chiZ]
  simp

/-- `χ_ξ(x) = 1` whenever `ξ x = 0`. -/
lemma chiZ_eq_one_of_mul_eq_zero {ξ x : ZMod (3 ^ n)} (h : ξ * x = 0) : chiZ ξ x = 1 := by
  rw [chiZ_eq_stdAddChar, h, neg_zero, AddChar.map_zero_eq_one]

lemma chiZ_ne_one_of_mul_ne_zero {ξ x : ZMod (3 ^ n)} (h : ξ * x ≠ 0) : chiZ ξ x ≠ 1 := by
  rw [chiZ_eq_stdAddChar, ← AddChar.map_zero_eq_one (ZMod.stdAddChar : AddChar (ZMod (3 ^ n)) ℂ)]
  intro h'
  exact h (neg_eq_zero.mp (ZMod.injective_stdAddChar h'))

/-- **Orthogonality** in the frequency. -/
lemma sum_chiZ (x : ZMod (3 ^ n)) :
    ∑ ξ : ZMod (3 ^ n), chiZ ξ x = if x = 0 then (3 : ℂ) ^ n else 0 := by
  have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod (3 ^ n)) ℂ)) (-x)
    (ZMod.isPrimitive_stdAddChar _)
  simp_rw [chiZ_eq_stdAddChar, ← mul_neg]
  rw [h]
  by_cases hx : x = 0
  · simp [hx, ZMod.card]
  · simp [hx]

/-! ## The Fourier transform and Plancherel -/

/-- The Fourier transform `Φ̂(ξ) = ∑_x χ_ξ(x) Φ(x)` on `ℤ/3^nℤ`. -/
def fourierZ (Φ : ZMod (3 ^ n) → ℂ) (ξ : ZMod (3 ^ n)) : ℂ := ∑ x, chiZ ξ x * Φ x

lemma fourierZ_sub (Φ Ψ : ZMod (3 ^ n) → ℂ) (ξ : ZMod (3 ^ n)) :
    fourierZ (fun x => Φ x - Ψ x) ξ = fourierZ Φ ξ - fourierZ Ψ ξ := by
  unfold fourierZ
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => mul_sub _ _ _

/-- **Plancherel on `ℤ/3^nℤ`.** -/
theorem plancherel (Φ : ZMod (3 ^ n) → ℂ) :
    ∑ ξ, ‖fourierZ Φ ξ‖ ^ 2 = (3 : ℝ) ^ n * ∑ x, ‖Φ x‖ ^ 2 := by
  have key : ∑ ξ, fourierZ Φ ξ * (starRingEnd ℂ) (fourierZ Φ ξ) =
      (3 : ℂ) ^ n * ∑ x, Φ x * (starRingEnd ℂ) (Φ x) := by
    calc ∑ ξ, fourierZ Φ ξ * (starRingEnd ℂ) (fourierZ Φ ξ)
        = ∑ ξ, ∑ x, ∑ y, (Φ x * (starRingEnd ℂ) (Φ y)) *
            (chiZ ξ x * (starRingEnd ℂ) (chiZ ξ y)) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          unfold fourierZ
          rw [map_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [map_mul]; ring
      _ = ∑ x, ∑ y, (Φ x * (starRingEnd ℂ) (Φ y)) * ∑ ξ, chiZ ξ (x - y) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ξ _ => by rw [chiZ_mul_conj]
      _ = ∑ x, (Φ x * (starRingEnd ℂ) (Φ x)) * (3 : ℂ) ^ n := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp_rw [sum_chiZ, sub_eq_zero, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq]
          simp
      _ = (3 : ℂ) ^ n * ∑ x, Φ x * (starRingEnd ℂ) (Φ x) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  simp_rw [Complex.mul_conj'] at key
  exact_mod_cast key

/-! ## Lifts and the operator `Q_m` on one slice -/

/-- Each residue mod `3^m` has exactly `3^{n-m}` lifts mod `3^n`. -/
lemma card_cast_fiber {m : ℕ} (h : m ≤ n) (z : ZMod (3 ^ m)) :
    (univ.filter (fun x : ZMod (3 ^ n) => (ZMod.cast x : ZMod (3 ^ m)) = z)).card =
      3 ^ (n - m) := by
  classical
  set φ := ZMod.castHom (pow_dvd_pow 3 h) (ZMod (3 ^ m)) with hφ
  have hsurj : Function.Surjective φ := ZMod.ringHom_surjective φ
  have hfib : ∀ w : ZMod (3 ^ m), (univ.filter fun x => φ x = w).card =
      (univ.filter fun x => φ x = z).card :=
    fun w => AddMonoidHom.card_fiber_eq_of_mem_range φ.toAddMonoidHom (hsurj w) (hsurj z)
  have htot : ∑ w : ZMod (3 ^ m), (univ.filter fun x => φ x = w).card = 3 ^ n := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => mem_univ (φ x))]
    simp [ZMod.card]
  rw [Finset.sum_congr rfl (fun w _ => hfib w), sum_const, card_univ, ZMod.card,
    smul_eq_mul] at htot
  have h3 : 3 ^ n = 3 ^ m * 3 ^ (n - m) := by rw [← pow_add]; congr 1; omega
  simp only [hφ, ZMod.castHom_apply] at htot
  exact Nat.eq_of_mul_eq_mul_left (by positivity) (htot.trans h3)

lemma cast_add_zmod {m : ℕ} (h : m ≤ n) (x y : ZMod (3 ^ n)) :
    (ZMod.cast (x + y) : ZMod (3 ^ m)) = ZMod.cast x + ZMod.cast y := by
  have := map_add (ZMod.castHom (pow_dvd_pow 3 h) (ZMod (3 ^ m))) x y
  simpa only [ZMod.castHom_apply] using this

lemma cast_three_pow_zmod {m : ℕ} (h : m ≤ n) :
    (ZMod.cast ((3 : ZMod (3 ^ n)) ^ m) : ZMod (3 ^ m)) = 0 := by
  have := map_pow (ZMod.castHom (pow_dvd_pow 3 h) (ZMod (3 ^ m))) 3 m
  rw [ZMod.castHom_apply, map_ofNat] at this
  rw [this, three_pow_eq_zero le_rfl]

/-- An element that is `0` mod `3^m` is a multiple of `3^m`. -/
lemma exists_eq_three_pow_mul {m : ℕ} {z : ZMod (3 ^ n)}
    (hz : (ZMod.cast z : ZMod (3 ^ m)) = 0) : ∃ k : ZMod (3 ^ n), z = 3 ^ m * k := by
  rw [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hz
  obtain ⟨k, hk⟩ := hz
  refine ⟨(k : ZMod (3 ^ n)), ?_⟩
  rw [← ZMod.natCast_zmod_val z, hk]
  push_cast; ring

/-- The character sum over the lifts of a residue. -/
lemma sum_chiZ_fiber {m : ℕ} (h : m ≤ n) (ξ y : ZMod (3 ^ n)) :
    ∑ x : ZMod (3 ^ n), (if (ZMod.cast x : ZMod (3 ^ m)) = ZMod.cast y then chiZ ξ x else 0) =
      if ξ * 3 ^ m = 0 then (3 ^ (n - m) : ℕ) * chiZ ξ y else 0 := by
  classical
  -- shift to the kernel
  have hshift : ∑ x : ZMod (3 ^ n),
      (if (ZMod.cast x : ZMod (3 ^ m)) = ZMod.cast y then chiZ ξ x else 0) =
      chiZ ξ y * ∑ z : ZMod (3 ^ n), (if (ZMod.cast z : ZMod (3 ^ m)) = 0 then chiZ ξ z else 0) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight y)]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [Equiv.coe_addRight, cast_add_zmod h, add_eq_right]
    split_ifs
    · rw [chiZ_add, mul_comm]
    · rw [mul_zero]
  rw [hshift]
  by_cases hξ : ξ * 3 ^ m = 0
  · rw [if_pos hξ]
    have hK : ∑ z : ZMod (3 ^ n), (if (ZMod.cast z : ZMod (3 ^ m)) = 0 then chiZ ξ z else 0) =
        ((3 ^ (n - m) : ℕ) : ℂ) := by
      rw [← card_cast_fiber h 0, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs with hz
      · obtain ⟨k, rfl⟩ := exists_eq_three_pow_mul hz
        rw [chiZ_eq_one_of_mul_eq_zero (by rw [← mul_assoc, hξ, zero_mul]), Nat.cast_one]
      · rfl
    rw [hK, mul_comm]
  · rw [if_neg hξ]
    -- `K` is invariant under the shift by `3^m`, whose character value is not `1`
    set K := ∑ z : ZMod (3 ^ n), (if (ZMod.cast z : ZMod (3 ^ m)) = 0 then chiZ ξ z else 0)
      with hKdef
    have hinv : K = chiZ ξ (3 ^ m) * K := by
      rw [hKdef]
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight ((3 : ZMod (3 ^ n)) ^ m))]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [Equiv.coe_addRight, cast_add_zmod h, cast_three_pow_zmod h, add_zero]
      split_ifs
      · rw [chiZ_add, mul_comm]
      · rw [mul_zero]
    have hne := chiZ_ne_one_of_mul_ne_zero hξ
    have : K * (1 - chiZ ξ (3 ^ m)) = 0 := by rw [mul_sub, mul_one, mul_comm K]; exact sub_eq_zero.mpr hinv
    rcases mul_eq_zero.mp this with hK | hK
    · rw [hK, mul_zero]
    · exact absurd (sub_eq_zero.mp hK).symm hne

/-- The operator `Q^{(n)}_m` of (2.4, `eq:Q`) on a single counter slice. -/
def Qs (n m : ℕ) (Φ : ZMod (3 ^ n) → ℂ) (x : ZMod (3 ^ n)) : ℂ :=
  (((3 : ℝ) ^ ((m : ℤ) - n) : ℝ) : ℂ) *
    ∑ y : ZMod (3 ^ n), if (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast x then Φ y else 0

lemma Qop_eq_Qs (n m : ℕ) (ν : ℕ → ZMod (3 ^ n) → ℝ) (s : ℕ) (x : ZMod (3 ^ n)) :
    ((Qop n m ν s x : ℝ) : ℂ) = Qs n m (fun y => (ν s y : ℂ)) x := by
  unfold Qop Qs
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

lemma zpow_mul_three_pow {m : ℕ} (h : m ≤ n) :
    (3 : ℝ) ^ ((m : ℤ) - n) * ((3 ^ (n - m) : ℕ) : ℝ) = 1 := by
  rw [show ((m : ℤ) - n) = -((n - m : ℕ) : ℤ) by push_cast [Nat.cast_sub h]; ring, zpow_neg,
    zpow_natCast]
  push_cast
  field_simp

/-- **`Q_m` is the projection onto the frequencies `ξ` with `3^m ξ = 0`.** -/
theorem fourierZ_Qs {m : ℕ} (h : m ≤ n) (Φ : ZMod (3 ^ n) → ℂ) (ξ : ZMod (3 ^ n)) :
    fourierZ (Qs n m Φ) ξ = if ξ * 3 ^ m = 0 then fourierZ Φ ξ else 0 := by
  unfold fourierZ Qs
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  have e : ∀ y : ZMod (3 ^ n), (∑ x : ZMod (3 ^ n), if (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast x
      then chiZ ξ x * ((((3 : ℝ) ^ ((m : ℤ) - n) : ℝ) : ℂ) * Φ y) else 0) =
      ((((3 : ℝ) ^ ((m : ℤ) - n) : ℝ) : ℂ) * Φ y) *
        ∑ x : ZMod (3 ^ n), (if (ZMod.cast x : ZMod (3 ^ m)) = ZMod.cast y then chiZ ξ x else 0) := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hxy : (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast x
    · rw [if_pos hxy, if_pos hxy.symm, mul_comm]
    · rw [if_neg hxy, if_neg (Ne.symm hxy), mul_zero]
  rw [Finset.sum_congr rfl (fun y _ => e y)]
  simp_rw [sum_chiZ_fiber h]
  split_ifs with hξ
  · refine Finset.sum_congr rfl fun y _ => ?_
    have := zpow_mul_three_pow (n := n) h
    calc (((3 : ℝ) ^ ((m : ℤ) - n) : ℝ) : ℂ) * Φ y * (((3 ^ (n - m) : ℕ) : ℂ) * chiZ ξ y)
        = ((((3 : ℝ) ^ ((m : ℤ) - n) * ((3 ^ (n - m) : ℕ) : ℝ) : ℝ)) : ℂ) * (chiZ ξ y * Φ y) := by
          push_cast; ring
      _ = chiZ ξ y * Φ y := by rw [this]; simp
  · simp

/-- **The `L²` projection bound.** If `Φ̂ = Ψ̂ · T` and `|T(ξ)| ≤ β` at every frequency with
`3^m ξ ≠ 0`, then `∑_x |Φ(x) - (Q_m Φ)(x)|² ≤ β² ∑_x |Ψ(x)|²`. -/
theorem l2_sub_Qs_le {m : ℕ} (h : m ≤ n) (Φ Ψ T : ZMod (3 ^ n) → ℂ) {β : ℝ}
    (hfac : ∀ ξ, fourierZ Φ ξ = fourierZ Ψ ξ * T ξ)
    (hT : ∀ ξ : ZMod (3 ^ n), ξ * 3 ^ m ≠ 0 → ‖T ξ‖ ≤ β) :
    ∑ x, ‖Φ x - Qs n m Φ x‖ ^ 2 ≤ β ^ 2 * ∑ x, ‖Ψ x‖ ^ 2 := by
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hP := plancherel (fun x => Φ x - Qs n m Φ x)
  have hPΨ := plancherel Ψ
  have hpt : ∀ ξ, ‖fourierZ (fun x => Φ x - Qs n m Φ x) ξ‖ ^ 2 ≤ β ^ 2 * ‖fourierZ Ψ ξ‖ ^ 2 := by
    intro ξ
    rw [fourierZ_sub, fourierZ_Qs h]
    split_ifs with hξ
    · rw [sub_self, norm_zero, zero_pow two_ne_zero]; positivity
    · rw [sub_zero, hfac, norm_mul, mul_pow, mul_comm]
      gcongr
      exact hT ξ hξ
  have hsum := Finset.sum_le_sum (fun ξ (_ : ξ ∈ univ) => hpt ξ)
  rw [← Finset.mul_sum, hP, hPΨ] at hsum
  have : (3 : ℝ) ^ n * ∑ x, ‖Φ x - Qs n m Φ x‖ ^ 2 ≤ (3 : ℝ) ^ n * (β ^ 2 * ∑ x, ‖Ψ x‖ ^ 2) := by
    linarith
  exact le_of_mul_le_mul_left this h3

end CollatzCLT
