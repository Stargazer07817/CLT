import LeanClt.Mixing.NearDiag

/-!
# §3.3: telescoping to all coarse scales, and Theorem 3.1 from Tao's imports

**Credit.** Theorem 3.1 is an averaged variant of the sum-conditioned mixing estimates of
J. Allikvere, *Almost all Collatz orbits attain almost bounded values in natural density* (2026),
Theorems 3.1 and 4.1; the observation that the total valuation is measurable with respect to the
pair sums of Tao's §7 is his. See the README.

* `pushforward_muJ`: target-outward order and independence of the tail,
  `∑_y G(y mod 3^q) μ_{q+t}(S, y) = ∑_{S₁} (∑_w G(w) μ_q(S₁, w)) P(S_t = S - S₁)`; this is the
  projection identity (3.5, `eq:projection`) in weak form.
* `Qop_split'`: `(Q^{(q+t)}_{q'} μ_{q+t})(S, x) = 3^{-t} ∑_{S₁} (Q^{(q)}_{q'} μ_q)(S₁, x mod 3^q) P(S_t = S - S₁)`
  for `q' ≤ q`; together with `Qop_split` (the case `q' = q`) this is the second half of (3.5).
* `telescope_step`: **the contraction (3.6, `eq:telescope-step`)**,
  `‖Q^{(n)}_q μ_n - Q^{(n)}_{q'} μ_n‖₁ ≤ ‖μ_q - Q^{(q)}_{q'} μ_q‖₁` for `q' ≤ q ≤ n`.
* `jointMixing_of_tao`: **Theorem 3.1 (`thm:jointmixing`) from `TaoMajorant` and `TaoPrefix`.**
  The chain `q ↦ ⌈0.9 q⌉` from `n` down to `m` is run as a strong induction with the potential
  `C' m^{-A} + C' λ (m^{-A} - q^{-A})`, `λ = 1/(1 - 0.95^A)`. Each step uses
  `⌈0.9 q⌉ ≤ 0.95 q`, which holds exactly for `q ≥ 10` (no integer lies in `[0.9q, 0.95q]` for
  `q ≤ 9`); the proof uses the crude form `⌈0.9 q⌉ ≤ 0.9 q + 0.9 ≤ 0.95 q` (`q ≥ 18`), available
  once `m ≥ 20`, and covers `m < 20` by the trivial bound `2 ≤ 2 · 20^A m^{-A}` (the "bounded `m`"
  clause of the paper).
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-! ## Distances -/

/-- `‖μ_n - Q^{(n)}_m μ_n‖₁`, the left side of (3.1, `eq:JM`). -/
def mixDist (n m : ℕ) : ℝ :=
  ∑' s, ∑ x : ZMod (3 ^ n), |muJ n s x - Qop n m (muJ n) s x|

/-- `‖Q^{(n)}_q μ_n - Q^{(n)}_{q'} μ_n‖₁`. -/
def dQ (n q q' : ℕ) : ℝ :=
  ∑' s, ∑ x : ZMod (3 ^ n), |Qop n q (muJ n) s x - Qop n q' (muJ n) s x|

lemma Qop_self (n : ℕ) (ν : ℕ → ZMod (3 ^ n) → ℝ) (s : ℕ) (x : ZMod (3 ^ n)) :
    Qop n n ν s x = ν s x := by
  unfold Qop
  simp only [sub_self, zpow_zero, one_mul, ZMod.cast_id', id]
  rw [Finset.sum_ite_eq']
  simp

lemma mixDist_eq_dQ (n m : ℕ) : mixDist n m = dQ n n m := by
  unfold mixDist dQ
  simp_rw [Qop_self]

lemma summable_dQ (n q q' : ℕ) (hq : q ≤ n) (hq' : q' ≤ n) :
    Summable (fun s => ∑ x : ZMod (3 ^ n), |Qop n q (muJ n) s x - Qop n q' (muJ n) s x|) := by
  refine Summable.of_nonneg_of_le (fun s => Finset.sum_nonneg fun x _ => abs_nonneg _)
    (fun s => ?_) ((summable_lawS n).mul_left ((2 : ℝ) * ((3 ^ n : ℕ) : ℝ)))
  calc ∑ x : ZMod (3 ^ n), |Qop n q (muJ n) s x - Qop n q' (muJ n) s x|
      ≤ ∑ x : ZMod (3 ^ n), (2 * lawS n s) := Finset.sum_le_sum fun x _ => by
        have h1 := Qop_nonneg n q s x
        have h2 := Qop_le n q s hq x
        have h3 := Qop_nonneg n q' s x
        have h4 := Qop_le n q' s hq' x
        rw [abs_le]; constructor <;> linarith
    _ = 2 * (3 ^ n : ℕ) * lawS n s := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring

/-- The triangle inequality for `dQ`. -/
lemma dQ_triangle {n a b c : ℕ} (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) :
    dQ n a c ≤ dQ n a b + dQ n b c := by
  unfold dQ
  rw [← (summable_dQ n a b ha hb).tsum_add (summable_dQ n b c hb hc)]
  refine Summable.tsum_le_tsum (fun s => ?_) (summable_dQ n a c ha hc)
    ((summable_dQ n a b ha hb).add (summable_dQ n b c hb hc))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => abs_sub_le _ _ _

/-! ## The projection identity -/

lemma cast_cast_zmod {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (x : ZMod (3 ^ c)) :
    (ZMod.cast (ZMod.cast x : ZMod (3 ^ b)) : ZMod (3 ^ a)) = ZMod.cast x := by
  have h := ZMod.castHom_comp (pow_dvd_pow 3 hab) (pow_dvd_pow 3 hbc)
  have := RingHom.congr_fun h x
  simpa only [RingHom.comp_apply, ZMod.castHom_apply] using this

/-- **Pushforward of `μ_{q+t}` to the residue mod `3^q`** (target-outward order and
independence of the tail). -/
lemma pushforward_muJ (q t S : ℕ) (G : ZMod (3 ^ q) → ℝ) :
    ∑ y : ZMod (3 ^ (q + t)), G (ZMod.cast y) * muJ (q + t) S y =
      ∑ S1 ∈ range (S + 1), (∑ w : ZMod (3 ^ q), G w * muJ q S1 w) * lawS t (S - S1) := by
  have hword : ∀ (r S' : ℕ) (F : ZMod (3 ^ r) → ℝ),
      ∑ y : ZMod (3 ^ r), F y * muJ r S' y = ∑ a ∈ words r S', F (Xmod a) * (1 / 2 : ℝ) ^ S' := by
    intro r S' F
    unfold muJ
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  rw [hword (q + t) S (fun y => G (ZMod.cast y)), sum_words_append q t S]
  refine Finset.sum_congr rfl fun S1 hS1 => ?_
  have hS1 := mem_range.mp hS1
  rw [hword q S1 G, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hc : ∀ v : Fin t → ℕ, (ZMod.cast (Xmod (Fin.append u v)) : ZMod (3 ^ q)) = Xmod u := by
    intro v
    have := cast_Xmod_append u v
    rwa [ZMod.castHom_apply] at this
  simp_rw [hc]
  rw [← sum_words_half, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mul_assoc, ← pow_add]; congr 2; omega

lemma zpow_split (q q' t : ℕ) :
    (3 : ℝ) ^ ((q' : ℤ) - ↑(q + t)) = (1 / 3 ^ t : ℝ) * (3 : ℝ) ^ ((q' : ℤ) - q) := by
  rw [one_div, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (by norm_num)]
  congr 1; push_cast; ring

/-- **The projection identity (3.5, `eq:projection`)** for `Q_{q'}`, `q' ≤ q`:
`(Q^{(q+t)}_{q'} μ_{q+t})(S, x) = 3^{-t} ∑_{S₁} (Q^{(q)}_{q'} μ_q)(S₁, x mod 3^q) P(S_t = S - S₁)`. -/
lemma Qop_split' {q q' : ℕ} (hq : q' ≤ q) (t S : ℕ) (x : ZMod (3 ^ (q + t))) :
    Qop (q + t) q' (muJ (q + t)) S x =
      (1 / 3 ^ t : ℝ) * ∑ S1 ∈ range (S + 1),
        Qop q q' (muJ q) S1 (ZMod.cast x) * lawS t (S - S1) := by
  have hqt : q ≤ q + t := Nat.le_add_right q t
  set G : ZMod (3 ^ q) → ℝ := fun w =>
    if (ZMod.cast w : ZMod (3 ^ q')) = ZMod.cast x then 1 else 0 with hG
  have hL : Qop (q + t) q' (muJ (q + t)) S x = (3 : ℝ) ^ ((q' : ℤ) - ↑(q + t)) *
      ∑ y : ZMod (3 ^ (q + t)), G (ZMod.cast y) * muJ (q + t) S y := by
    unfold Qop
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hG, cast_cast_zmod hq hqt]
    split_ifs <;> simp
  have hR : ∀ S1, Qop q q' (muJ q) S1 (ZMod.cast x) =
      (3 : ℝ) ^ ((q' : ℤ) - q) * ∑ w : ZMod (3 ^ q), G w * muJ q S1 w := by
    intro S1
    unfold Qop
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [hG, cast_cast_zmod hq hqt]
    split_ifs <;> simp
  rw [hL, pushforward_muJ, zpow_split]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S1 _ => ?_
  rw [hR]; ring

/-! ## The contraction -/

/-- Summing a function of the residue mod `3^q` over `ℤ/3^nℤ` counts each residue `3^{n-q}`
times. -/
lemma sum_cast_eq {q n : ℕ} (h : q ≤ n) (F : ZMod (3 ^ q) → ℝ) :
    ∑ x : ZMod (3 ^ n), F (ZMod.cast x) = ((3 ^ (n - q) : ℕ) : ℝ) * ∑ z : ZMod (3 ^ q), F z := by
  classical
  rw [← Finset.sum_fiberwise (univ : Finset (ZMod (3 ^ n))) (fun x => (ZMod.cast x : ZMod (3 ^ q)))
    (fun x => F (ZMod.cast x)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2]), Finset.sum_const,
    card_cast_fiber h z, nsmul_eq_mul]

/-- **The contraction (3.6, `eq:telescope-step`)**: for `q' ≤ q ≤ n`,
`‖Q^{(n)}_q μ_n - Q^{(n)}_{q'} μ_n‖₁ ≤ ‖μ_q - Q^{(q)}_{q'} μ_q‖₁`. -/
theorem telescope_step {n q q' : ℕ} (hq' : q' ≤ q) (hq : q ≤ n) :
    dQ n q q' ≤ mixDist q q' := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hq
  set d : ℕ → ZMod (3 ^ q) → ℝ := fun S1 z => muJ q S1 z - Qop q q' (muJ q) S1 z with hd
  have hd2 : ∀ S1 z, |d S1 z| ≤ 2 * lawS q S1 := by
    intro S1 z
    have h1 := muJ_nonneg q S1 z
    have h2 : muJ q S1 z ≤ lawS q S1 := by
      rw [← sum_muJ]; exact Finset.single_le_sum (fun y _ => muJ_nonneg q S1 y) (mem_univ z)
    have h3 := Qop_nonneg q q' S1 z
    have h4 := Qop_le q q' S1 hq' z
    simp only [hd]; rw [abs_le]; constructor <;> linarith
  have hds : ∀ z, Summable (fun S1 => |d S1 z|) := fun z =>
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun S1 => hd2 S1 z)
      ((summable_lawS q).mul_left 2)
  -- one slice
  have hslice : ∀ S, ∑ x : ZMod (3 ^ (q + t)),
      |Qop (q + t) q (muJ (q + t)) S x - Qop (q + t) q' (muJ (q + t)) S x| ≤
      ∑ z : ZMod (3 ^ q), ∑ S1 ∈ range (S + 1), |d S1 z| * lawS t (S - S1) := by
    intro S
    have hpt : ∀ x : ZMod (3 ^ (q + t)),
        |Qop (q + t) q (muJ (q + t)) S x - Qop (q + t) q' (muJ (q + t)) S x| ≤
        (1 / 3 ^ t : ℝ) * ∑ S1 ∈ range (S + 1), |d S1 (ZMod.cast x)| * lawS t (S - S1) := by
      intro x
      rw [Qop_split, Qop_split' hq', ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_pos (by positivity)]
      gcongr
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun S1 _ => ?_))
      rw [← sub_mul, abs_mul, abs_of_nonneg (lawS_nonneg _ _)]
    calc _ ≤ ∑ x : ZMod (3 ^ (q + t)),
          (1 / 3 ^ t : ℝ) * ∑ S1 ∈ range (S + 1), |d S1 (ZMod.cast x)| * lawS t (S - S1) :=
          Finset.sum_le_sum fun x _ => hpt x
      _ = (1 / 3 ^ t : ℝ) * ∑ x : ZMod (3 ^ (q + t)),
            ∑ S1 ∈ range (S + 1), |d S1 (ZMod.cast x)| * lawS t (S - S1) := by
          rw [Finset.mul_sum]
      _ = _ := by
          rw [sum_cast_eq hq (fun z => ∑ S1 ∈ range (S + 1), |d S1 z| * lawS t (S - S1)),
            Nat.add_sub_cancel_left, ← mul_assoc]
          push_cast
          rw [one_div, inv_mul_cancel₀ (by positivity), one_mul]
  -- sum over the counter
  have hconv : ∀ z, Summable (fun S => ∑ S1 ∈ range (S + 1), |d S1 z| * lawS t (S - S1)) ∧
      ∑' S, ∑ S1 ∈ range (S + 1), |d S1 z| * lawS t (S - S1) = ∑' S1, |d S1 z| :=
    fun z => conv_lawS (hds z) t
  have hsumR : Summable (fun S => ∑ z : ZMod (3 ^ q),
      ∑ S1 ∈ range (S + 1), |d S1 z| * lawS t (S - S1)) :=
    summable_sum fun z _ => (hconv z).1
  unfold dQ mixDist
  calc _ ≤ ∑' S, ∑ z : ZMod (3 ^ q), ∑ S1 ∈ range (S + 1), |d S1 z| * lawS t (S - S1) :=
        Summable.tsum_le_tsum hslice (summable_dQ (q + t) q q' hq (hq'.trans hq)) hsumR
    _ = ∑ z : ZMod (3 ^ q), ∑' S1, |d S1 z| := by
        rw [Summable.tsum_finsetSum (fun z _ => (hconv z).1)]
        exact Finset.sum_congr rfl fun z _ => (hconv z).2
    _ = ∑' S1, ∑ z : ZMod (3 ^ q), |d S1 z| :=
        (Summable.tsum_finsetSum (fun z _ => hds z)).symm

/-! ## Theorem 3.1 -/

/-- **Theorem 3.1 (joint offset/counter mixing, `thm:jointmixing`) from Tao's imports.** -/
theorem jointMixing_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) : JointMixing := by
  intro A hA
  obtain ⟨C, hC⟩ := neardiag hTM hTP hA
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set ρ : ℝ := (0.95 : ℝ) ^ A with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hA
  set lam : ℝ := 1 / (1 - ρ) with hlam
  have hlam0 : 0 ≤ lam := by rw [hlam]; exact div_nonneg zero_le_one (by linarith)
  have hlamρ : lam * (1 - ρ) = 1 := by
    rw [hlam, one_div, inv_mul_cancel₀ (sub_pos.mpr hρ1).ne']
  refine ⟨max (C' * (1 + lam)) (2 * (20 : ℝ) ^ A), fun m n hm hmn => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmA : 0 < (m : ℝ) ^ (-A) := Real.rpow_pos_of_pos hm0 _
  change mixDist n m ≤ _
  by_cases hm20 : m < 20
  · -- bounded `m`: the trivial bound
    have h1 : 1 ≤ (20 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
      rw [Real.rpow_neg hm0.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hm0 _)]
      exact Real.rpow_le_rpow hm0.le (by exact_mod_cast hm20.le) hA.le
    calc mixDist n m ≤ 2 := l1_mix_le_two n m hmn
      _ ≤ 2 * (20 : ℝ) ^ A * (m : ℝ) ^ (-A) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hmA.le
  · push Not at hm20
    -- the near-diagonal bound with a nonnegative constant
    have hND : ∀ a b : ℕ, 1 ≤ a → a ≤ b → 9 * b ≤ 10 * a → mixDist b a ≤ C' * (a : ℝ) ^ (-A) :=
      fun a b ha hab h9 => (hC a b ha hab h9).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by positivity) _))
    -- the potential bound, by strong induction on `q`
    have key : ∀ q : ℕ, m ≤ q → q ≤ n →
        dQ n q m ≤ C' * (m : ℝ) ^ (-A) + C' * lam * ((m : ℝ) ^ (-A) - (q : ℝ) ^ (-A)) := by
      intro q
      induction q using Nat.strong_induction_on with
      | _ q ih =>
        intro hmq hqn
        have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
        have hqA : (q : ℝ) ^ (-A) ≤ (m : ℝ) ^ (-A) :=
          Real.rpow_le_rpow_of_nonpos hm0 (by exact_mod_cast hmq) (by linarith)
        have hpot0 : 0 ≤ C' * lam * ((m : ℝ) ^ (-A) - (q : ℝ) ^ (-A)) :=
          mul_nonneg (mul_nonneg hC'0 hlam0) (by linarith)
        by_cases h9 : 9 * q ≤ 10 * m
        · -- one step reaches `m`
          calc dQ n q m ≤ mixDist q m := telescope_step hmq hqn
            _ ≤ C' * (m : ℝ) ^ (-A) := hND m q hm hmq h9
            _ ≤ _ := le_add_of_nonneg_right hpot0
        · -- step to `q' = ⌈0.9 q⌉`
          push Not at h9
          set q' := (9 * q + 9) / 10 with hq'
          have hq'q : q' < q := by omega
          have hmq' : m ≤ q' := by omega
          have h9' : 9 * q ≤ 10 * q' := by omega
          have h95 : 20 * q' ≤ 19 * q := by omega
          have hq'0 : (0 : ℝ) < q' := by exact_mod_cast (show 0 < q' by omega)
          have hih := ih q' hq'q hmq' (hq'q.le.trans hqn)
          -- `q^{-A} ≤ 0.95^A q'^{-A}`
          have hdecay : (q : ℝ) ^ (-A) ≤ ρ * (q' : ℝ) ^ (-A) := by
            have h1 : (q' : ℝ) / 0.95 ≤ q := by
              rw [div_le_iff₀ (by norm_num)]
              have : (20 * q' : ℝ) ≤ 19 * q := by exact_mod_cast h95
              linarith
            have h2 := Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith : -A ≤ 0)
            rwa [Real.div_rpow hq'0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 0.95),
              div_inv_eq_mul, mul_comm] at h2
          have hstep : dQ n q q' ≤ C' * (q' : ℝ) ^ (-A) :=
            (telescope_step hq'q.le hqn).trans (hND q' q (by omega) hq'q.le h9')
          calc dQ n q m ≤ dQ n q q' + dQ n q' m :=
                dQ_triangle hqn (hq'q.le.trans hqn) (hmq.trans hqn)
            _ ≤ C' * (q' : ℝ) ^ (-A) +
                (C' * (m : ℝ) ^ (-A) + C' * lam * ((m : ℝ) ^ (-A) - (q' : ℝ) ^ (-A))) :=
                add_le_add hstep hih
            _ ≤ C' * (m : ℝ) ^ (-A) + C' * lam * ((m : ℝ) ^ (-A) - (q : ℝ) ^ (-A)) := by
                have hlin : (q' : ℝ) ^ (-A) - lam * (q' : ℝ) ^ (-A) + lam * (q : ℝ) ^ (-A) ≤ 0 := by
                  have h1 : lam * (q : ℝ) ^ (-A) ≤ lam * (ρ * (q' : ℝ) ^ (-A)) :=
                    mul_le_mul_of_nonneg_left hdecay hlam0
                  nlinarith [hlamρ]
                nlinarith [mul_nonneg hC'0 (show (0 : ℝ) ≤ -( (q' : ℝ) ^ (-A) -
                  lam * (q' : ℝ) ^ (-A) + lam * (q : ℝ) ^ (-A)) by linarith)]
    have hn := key n (by omega) le_rfl
    rw [mixDist_eq_dQ]
    calc dQ n n m ≤ C' * (m : ℝ) ^ (-A) + C' * lam * ((m : ℝ) ^ (-A) - (n : ℝ) ^ (-A)) := hn
      _ ≤ C' * (1 + lam) * (m : ℝ) ^ (-A) := by
          have : 0 ≤ C' * lam * (n : ℝ) ^ (-A) :=
            mul_nonneg (mul_nonneg hC'0 hlam0) (Real.rpow_nonneg (by positivity) _)
          nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hmA.le

end CollatzCLT
