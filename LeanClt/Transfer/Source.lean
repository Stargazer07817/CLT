import LeanClt.Transfer.Harmonic
import LeanClt.Transfer.Reverse

/-!
# §5.4: the source count, depth by depth

* `phase q ρ η s M S r = e^{is(q(M) - ρS - ηr)}`.
* `depthSum r = ∑_{N ∈ [Y,2Y] odd} 1{|S_r(N) - 2r| ≤ L^{0.6}, U^r(N) ∈ E} e^{is(⋯)}`: the
  sources counted at depth `r`, with their phase.
* `Gt r S z = ∑_{M ∈ E, M ≡ z (3^r), Y ≤ 2^S M/3^r ≤ 2Y} 2^S e^{is(q(M) - ρS - ηr)}`, which is
  `L_Y G̃_{r,Y}(S, z)` of (5.13, `eq:Gtilde`) (the factor `1/L_Y` is kept outside).

`lhs_decomp`: `L_Y · LHS = ∑_{r ∈ J_Y} depthSum r` up to `(n₀+2) #{N not typical}`
(Lemmas 5.2 and 5.4 identify the depth of a typical source).

`depth_offset` (Lemma 5.7, first half): `depthSum r = ∑_{S typical} 2^{-S} ∑_{a ∈ words r S}
Gt r S (F_r(a))` up to `2Δ + 2`, `Δ = e^{ℓ(n₀ + L^{0.6})}`. The real offset is removed from the
source window; a source is moved across a window endpoint only if it lies within `Δ` of it.
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-- The phase `e^{is(q(M) - ρS - ηr)}`. -/
def phase (q : ℕ → ℝ) (ρ η s : ℝ) (M S r : ℕ) : ℂ :=
  cexp (((s * (q M - ρ * S - η * r) : ℝ) : ℂ) * I)

lemma norm_phase (q : ℕ → ℝ) (ρ η s : ℝ) (M S r : ℕ) : ‖phase q ρ η s M S r‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Typicality of the total at depth `r`: `|S - 2r| ≤ L^{0.6}`. -/
def typT (x : ℝ) (r S : ℕ) : Prop := |(S : ℝ) - 2 * r| ≤ Lx x ^ (0.6 : ℝ)

/-- The simplified source window `Y ≤ 2^S M / 3^r ≤ 2Y`. -/
def win (Y : ℝ) (r S M : ℕ) : Prop :=
  Y ≤ 2 ^ S * (M : ℝ) / 3 ^ r ∧ 2 ^ S * (M : ℝ) / 3 ^ r ≤ 2 * Y

open Classical in
/-- The sources counted at depth `r`, with their phase. -/
def depthSum (x Y : ℝ) (E : Finset ℕ) (q : ℕ → ℝ) (ρ η s : ℝ) (r : ℕ) : ℂ :=
  ∑ N ∈ oddClosed Y, if typT x r (wsum (vword N) r) ∧ U^[r] N ∈ E then
    phase q ρ η s (U^[r] N) (wsum (vword N) r) r else 0

open Classical in
/-- `L_Y G̃_{r,Y}(S, z)` (5.13, `eq:Gtilde`). -/
def Gt (Y : ℝ) (E : Finset ℕ) (q : ℕ → ℝ) (ρ η s : ℝ) (r S : ℕ) (z : ZMod (3 ^ r)) : ℂ :=
  ∑ M ∈ E, if (M : ZMod (3 ^ r)) = z ∧ win Y r S M then (2 : ℂ) ^ S * phase q ρ η s M S r else 0

/-- `Δ = e^{ℓ(n₀ + L^{0.6})}`, a bound for the real offset `2^S F_r / 3^r` of a typical word. -/
def Δx (x : ℝ) : ℝ := Real.exp (ell * (n0 x + Lx x ^ (0.6 : ℝ)))

/-! ## Basic facts for large `x` -/

lemma large_facts {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y) :
    0 < x ∧ 200000 ≤ x ∧ x < Y ∧ 0 < Y := by
  have hx1 := hL.x_gt
  have hx0 : 0 < x := by linarith
  have h1 : 200000 ≤ x := by
    have := Real.add_one_le_exp (Lx x)
    rw [Lx, Real.exp_log hx0] at this
    have := hL.L_ge; unfold Lx at this; linarith
  have h2 : x < Y := (x_lt_rpow_alpha hx1).trans_le hY1
  exact ⟨hx0, h1, h2, by linarith⟩

lemma LY_pos {Y : ℝ} (hY : 4 ≤ Y) : (0 : ℝ) < LY Y := by
  have := LY_ge (show 0 ≤ Y by linarith); linarith

/-! ## Step A: the left side as a sum over depths -/

open Classical in
/-- For a typical source, the first-passage indicator with its phase is the sum over `J_Y` of
the depth indicators: exactly one depth (the first crossing minus `m`) contributes. -/
lemma good_eq {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y) (hY2 : Y ≤ x ^ (alpha ^ 2))
    {E : Finset ℕ} (hE : (↑E : Set ℕ) ⊆ Mset x) (q : ℕ → ℝ) (ρ η s : ℝ) {N : ℕ}
    (hN : N ∈ oddClosed Y) (hG : Good x N) :
    (if Event x E N then phase q ρ η s (U^[passT x N - mT x] N)
        (wsum (vword N) (passT x N - mT x)) (passT x N - mT x) else 0) =
      ∑ r ∈ JY x Y, if typT x r (wsum (vword N) r) ∧ U^[r] N ∈ E then
        phase q ρ η s (U^[r] N) (wsum (vword N) r) r else 0 := by
  obtain ⟨hx0, -, -, hY0⟩ := large_facts hL hY1
  obtain ⟨hNo, hNY, -⟩ := mem_oddClosed hY0.le hN
  have hNx : x ^ alpha ≤ N := hY1.trans hNY
  obtain ⟨hcr, hmp, hpn, hJ, -⟩ := orbit_window hL hY1 hY2 hN hG
  have hJn : ∀ r ∈ JY x Y, r ≤ n0 x := fun r hr => by
    unfold JY at hr; rw [mem_filter, mem_range] at hr; omega
  have key : ∀ r ∈ JY x Y, U^[r] N ∈ E → r = passT x N - mT x := by
    intro r hr hE'
    obtain ⟨-, hp⟩ := converse hL hNo hNx (hJn r hr) (fun j hj => hG j (hj.trans (hJn r hr)))
      (hE hE')
    omega
  by_cases hEv : Event x E N
  · rw [if_pos hEv, Finset.sum_eq_single (passT x N - mT x)]
    · rw [if_pos ⟨hG _ (by omega), hEv.2.2⟩]
    · intro r hr hne
      rw [if_neg]
      rintro ⟨-, h2⟩
      exact hne (key r hr h2)
    · intro h; exact absurd hJ h
  · rw [if_neg hEv]
    symm
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [if_neg]
    rintro ⟨-, h2⟩
    apply hEv
    refine ⟨hcr, hmp, ?_⟩
    rw [← key r hr h2]
    exact h2

lemma card_JY_le (x Y : ℝ) : (JY x Y).card ≤ n0 x + 1 := by
  unfold JY
  exact (Finset.card_filter_le _ _).trans (by simp)

open Classical in
/-- **Step A.** `L_Y · LHS = ∑_{r ∈ J_Y} depthSum r` up to `(n₀ + 2) #{N not typical}`. -/
theorem lhs_decomp {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y) (hY2 : Y ≤ x ^ (alpha ^ 2))
    (E : Finset ℕ) (hE : (↑E : Set ℕ) ⊆ Mset x) (q : ℕ → ℝ) (ρ η s : ℝ) :
    ‖(LY Y : ℂ) * transferLHS x Y E q ρ η s - ∑ r ∈ JY x Y, depthSum x Y E q ρ η s r‖ ≤
      (n0 x + 2) * (((oddClosed Y).filter (fun N => ¬ Good x N)).card : ℝ) := by
  classical
  obtain ⟨hx0, h2e5, hxY, hY0⟩ := large_facts hL hY1
  have hLY0 : (LY Y : ℂ) ≠ 0 := by
    have := LY_pos (show 4 ≤ Y by linarith)
    exact_mod_cast this.ne'
  set f : ℕ → ℂ := fun N => if Event x E N then phase q ρ η s (U^[passT x N - mT x] N)
    (wsum (vword N) (passT x N - mT x)) (passT x N - mT x) else 0 with hf
  set g : ℕ → ℂ := fun N => ∑ r ∈ JY x Y, if typT x r (wsum (vword N) r) ∧ U^[r] N ∈ E then
    phase q ρ η s (U^[r] N) (wsum (vword N) r) r else 0 with hg
  have e1 : (LY Y : ℂ) * transferLHS x Y E q ρ η s = ∑ N ∈ oddClosed Y, f N := by
    unfold transferLHS
    rw [← mul_assoc, show ((oddClosed Y).card : ℂ) = (LY Y : ℂ) from rfl, mul_inv_cancel₀ hLY0,
      one_mul]
    refine Finset.sum_congr rfl fun N _ => ?_
    simp only [hf]
    split_ifs <;> rfl
  have e2 : ∑ r ∈ JY x Y, depthSum x Y E q ρ η s r = ∑ N ∈ oddClosed Y, g N := by
    unfold depthSum
    rw [Finset.sum_comm]
  rw [e1, e2, ← Finset.sum_sub_distrib]
  have hpt : ∀ N ∈ oddClosed Y, ‖f N - g N‖ ≤
      if ¬ Good x N then (n0 x + 2 : ℝ) else 0 := by
    intro N hN
    by_cases hG : Good x N
    · rw [if_neg (not_not.mpr hG), hf, hg]
      simp only
      rw [good_eq hL hY1 hY2 hE q ρ η s hN hG, sub_self, norm_zero]
    · rw [if_pos hG]
      have hf1 : ‖f N‖ ≤ 1 := by
        simp only [hf]; split_ifs
        · rw [norm_phase]
        · simp
      have hg1 : ‖g N‖ ≤ n0 x + 1 := by
        simp only [hg]
        refine (norm_sum_le _ _).trans ?_
        calc ∑ r ∈ JY x Y, ‖(if typT x r (wsum (vword N) r) ∧ U^[r] N ∈ E then
              phase q ρ η s (U^[r] N) (wsum (vword N) r) r else 0)‖
            ≤ ∑ r ∈ JY x Y, (1 : ℝ) := Finset.sum_le_sum fun r _ => by
              split_ifs
              · rw [norm_phase]
              · simp
          _ = (JY x Y).card := by simp
          _ ≤ n0 x + 1 := by exact_mod_cast card_JY_le x Y
      calc ‖f N - g N‖ ≤ ‖f N‖ + ‖g N‖ := norm_sub_le _ _
        _ ≤ 1 + (n0 x + 1) := add_le_add hf1 hg1
        _ = n0 x + 2 := by ring
  calc ‖∑ N ∈ oddClosed Y, (f N - g N)‖ ≤ ∑ N ∈ oddClosed Y, ‖f N - g N‖ := norm_sum_le _ _
    _ ≤ ∑ N ∈ oddClosed Y, if ¬ Good x N then (n0 x + 2 : ℝ) else 0 :=
        Finset.sum_le_sum hpt
    _ = (n0 x + 2) * (((oddClosed Y).filter (fun N => ¬ Good x N)).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

end CollatzCLT
