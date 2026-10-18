import LeanClt.Mixing.Telescope
import LeanClt.Transfer.Scalar

/-!
# (8.1, `eq:A1`): the offset-marginal mixing bound

The proof of Theorem 8.1 [`thm:positivity`] uses exactly one analytic input, (8.1), which the
paper cites as Tao's Prop. 1.14; it is the offset marginal of Theorem 3.1 [`thm:jointmixing`]:

  `‖ρ_q - lift(ρ_m)‖_{L¹(G_q)} ≤ (2/3) C_A m^{-A}`  for `1 ≤ m ≤ q`,

where `μ_q` is the law of `X_q` on `G_q = ℤ/3^qℤ`, `ρ_q = (2/3) 3^q μ_q`, `lift(ρ_m)` is `ρ_m`
composed with reduction modulo `3^m`, and `‖f‖_{L¹(G_q)} = 3^{-q} ∑_y |f(y)|`.

It follows from Theorem 3.1 by summing over the counter:
`μ_q(y) - 3^{m-q} μ_m(y mod 3^m) = ∑_s (μ_q(s,y) - (Q^{(q)}_m μ_q)(s,y))`, because summing the
projection identity (3.5, `eq:projection`) over the counter gives
`∑_s (Q^{(q)}_m μ_q)(s,y) = 3^{m-q} μ_m(y mod 3^m)`; the triangle inequality then bounds the
marginal distance by the joint one.

* `lawX q y = P(X_q = y) = ∑_s μ_q(s, y)`, `rhoX q = ρ_q`, `normL1 q f = ‖f‖_{L¹(G_q)}`.
* `lawX_fiber`: `P(X_{m+t} ≡ x mod 3^m) = P(X_m = x)` (target-outward consistency, in law).
* `tsum_Qop_self`: `∑_s (Q^{(m+t)}_m μ_{m+t})(s, y) = 3^{-t} μ_m(y mod 3^m)`.
* `marginal_le_mixDist`: `∑_y |μ_q(y) - 3^{m-q} μ_m(y mod 3^m)| ≤ ‖μ_q - Q^{(q)}_m μ_q‖₁`.
* `OffsetMixing`: (8.1, `eq:A1`) as a property; `offsetMixing_of_jointMixing`, and
  `offsetMixing_of_tao` from Tao's two imports.
-/

open Real Finset

noncomputable section

namespace CollatzCLT

/-! ## The offset marginal -/

/-- The law of the offset `X_q`: `lawX q y = P(X_q = y) = ∑_s μ_q(s, y)`. -/
def lawX (q : ℕ) (y : ZMod (3 ^ q)) : ℝ := ∑' s : ℕ, muJ q s y

/-- The normalised density `ρ_q = (2/3) 3^q μ_q` of §8, of uniform mean `2/3`. -/
def rhoX (q : ℕ) (y : ZMod (3 ^ q)) : ℝ := 2 / 3 * 3 ^ q * lawX q y

/-- The normalised norm `‖f‖_{L¹(G_q)} = 3^{-q} ∑_y |f(y)|` of §8. -/
def normL1 (q : ℕ) (f : ZMod (3 ^ q) → ℝ) : ℝ := (∑ y : ZMod (3 ^ q), |f y|) / 3 ^ q

/-- **(8.1, `eq:A1`)**, offset-marginal mixing, as a property: for every `A > 0` there is `C_A`
with `‖ρ_q - lift(ρ_m)‖_{L¹(G_q)} ≤ (2/3) C_A m^{-A}` for `1 ≤ m ≤ q`. -/
def OffsetMixing : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ m q : ℕ, 1 ≤ m → m ≤ q →
    normL1 q (fun y => rhoX q y - rhoX m (ZMod.cast y)) ≤ 2 / 3 * C * (m : ℝ) ^ (-A)

lemma summable_muJ (q : ℕ) (y : ZMod (3 ^ q)) : Summable (fun s => muJ q s y) :=
  Summable.of_nonneg_of_le (fun s => muJ_nonneg q s y) (fun s => muJ_le_lawS q s y)
    (summable_lawS q)

lemma lawX_nonneg (q : ℕ) (y : ZMod (3 ^ q)) : 0 ≤ lawX q y :=
  tsum_nonneg fun s => muJ_nonneg q s y

lemma summable_Qop (q m : ℕ) (hmq : m ≤ q) (y : ZMod (3 ^ q)) :
    Summable (fun s => Qop q m (muJ q) s y) :=
  Summable.of_nonneg_of_le (fun s => Qop_nonneg q m s y) (fun s => Qop_le q m s hmq y)
    (summable_lawS q)

/-- **Target-outward consistency, in law:** `P(X_{m+t} ≡ x mod 3^m) = P(X_m = x)`. -/
lemma lawX_fiber (m t : ℕ) (x : ZMod (3 ^ m)) :
    ∑ y : ZMod (3 ^ (m + t)), (if (ZMod.cast y : ZMod (3 ^ m)) = x then lawX (m + t) y else 0) =
      lawX m x := by
  classical
  set G : ZMod (3 ^ m) → ℝ := fun w => if w = x then 1 else 0 with hG
  -- for each counter value, the pushforward of `μ_{m+t}(S, ·)` is a convolution
  have hS : ∀ S, ∑ y : ZMod (3 ^ (m + t)), G (ZMod.cast y) * muJ (m + t) S y =
      ∑ S1 ∈ range (S + 1), muJ m S1 x * lawS t (S - S1) := by
    intro S
    rw [pushforward_muJ]
    refine Finset.sum_congr rfl fun S1 _ => ?_
    congr 1
    simp [hG]
  have hconv := conv_lawS (summable_muJ m x) t
  unfold lawX
  rw [← hconv.2, ← tsum_congr hS]
  rw [Summable.tsum_finsetSum (fun y _ => (summable_muJ (m + t) y).mul_left _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [tsum_mul_left]
  simp only [hG]
  split_ifs <;> simp

/-- Summing the projection identity (3.5, `eq:projection`) over the counter:
`∑_s (Q^{(m+t)}_m μ_{m+t})(s, y) = 3^{-t} μ_m(y mod 3^m)`. -/
lemma tsum_Qop_self (m t : ℕ) (y : ZMod (3 ^ (m + t))) :
    ∑' S : ℕ, Qop (m + t) m (muJ (m + t)) S y = (1 / 3 ^ t : ℝ) * lawX m (ZMod.cast y) := by
  have h : ∀ S, Qop (m + t) m (muJ (m + t)) S y =
      (1 / 3 ^ t : ℝ) * ∑ S1 ∈ range (S + 1), muJ m S1 (ZMod.cast y) * lawS t (S - S1) := by
    intro S
    rw [Qop_split' (le_refl m) t S y]
    simp_rw [Qop_self]
  rw [tsum_congr h, tsum_mul_left, (conv_lawS (summable_muJ m _) t).2]
  rfl

/-- **The marginal distance is at most the joint distance:**
`∑_y |μ_q(y) - 3^{m-q} μ_m(y mod 3^m)| ≤ ‖μ_q - Q^{(q)}_m μ_q‖₁` for `m ≤ q`. -/
theorem marginal_le_mixDist {m q : ℕ} (hmq : m ≤ q) :
    ∑ y : ZMod (3 ^ q), |lawX q y - (3 : ℝ) ^ m / 3 ^ q * lawX m (ZMod.cast y)| ≤
      mixDist q m := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmq
  -- pointwise, the marginal difference is the counter-sum of the joint difference
  have hpt : ∀ y : ZMod (3 ^ (m + t)),
      lawX (m + t) y - (3 : ℝ) ^ m / 3 ^ (m + t) * lawX m (ZMod.cast y) =
        ∑' S : ℕ, (muJ (m + t) S y - Qop (m + t) m (muJ (m + t)) S y) := by
    intro y
    rw [(summable_muJ (m + t) y).tsum_sub (summable_Qop (m + t) m hmq y), tsum_Qop_self]
    unfold lawX
    congr 1
    rw [pow_add]
    field_simp
  have hsum : ∀ y : ZMod (3 ^ (m + t)),
      Summable (fun S => |muJ (m + t) S y - Qop (m + t) m (muJ (m + t)) S y|) := by
    intro y
    exact ((summable_muJ (m + t) y).sub (summable_Qop (m + t) m hmq y)).abs
  calc ∑ y : ZMod (3 ^ (m + t)), |lawX (m + t) y - (3 : ℝ) ^ m / 3 ^ (m + t) * lawX m (ZMod.cast y)|
      ≤ ∑ y : ZMod (3 ^ (m + t)),
          ∑' S : ℕ, |muJ (m + t) S y - Qop (m + t) m (muJ (m + t)) S y| := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [hpt y]
        have := norm_tsum_le_tsum_norm (f := fun S =>
          muJ (m + t) S y - Qop (m + t) m (muJ (m + t)) S y) (by simpa [Real.norm_eq_abs] using hsum y)
        simpa [Real.norm_eq_abs] using this
    _ = mixDist (m + t) m := by
        unfold mixDist
        rw [Summable.tsum_finsetSum (fun y _ => hsum y)]

/-- **(8.1) in unnormalised form**, from Theorem 3.1:
`∑_y |μ_q(y) - 3^{m-q} μ_m(y mod 3^m)| ≤ C_A m^{-A}` for `1 ≤ m ≤ q`. -/
theorem marginal_of_jointMixing (hJM : JointMixing) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ m q : ℕ, 1 ≤ m → m ≤ q →
      ∑ y : ZMod (3 ^ q), |lawX q y - (3 : ℝ) ^ m / 3 ^ q * lawX m (ZMod.cast y)| ≤
        C * (m : ℝ) ^ (-A) := by
  obtain ⟨C, hC⟩ := hJM A hA
  exact ⟨C, fun m q hm hmq => (marginal_le_mixDist hmq).trans (hC m q hm hmq)⟩

/-- The normalised norm of `ρ_q - lift(ρ_m)` is `2/3` times the unnormalised marginal distance. -/
lemma normL1_rho_sub (m q : ℕ) :
    normL1 q (fun y => rhoX q y - rhoX m (ZMod.cast y)) =
      2 / 3 * ∑ y : ZMod (3 ^ q), |lawX q y - (3 : ℝ) ^ m / 3 ^ q * lawX m (ZMod.cast y)| := by
  unfold normL1 rhoX
  have h3 : (0 : ℝ) < 3 ^ q := by positivity
  have hpt : ∀ y : ZMod (3 ^ q), |2 / 3 * 3 ^ q * lawX q y - 2 / 3 * 3 ^ m * lawX m (ZMod.cast y)| =
      2 / 3 * 3 ^ q * |lawX q y - (3 : ℝ) ^ m / 3 ^ q * lawX m (ZMod.cast y)| := by
    intro y
    have : 2 / 3 * 3 ^ q * lawX q y - 2 / 3 * 3 ^ m * lawX m (ZMod.cast y) =
        2 / 3 * 3 ^ q * (lawX q y - (3 : ℝ) ^ m / 3 ^ q * lawX m (ZMod.cast y)) := by
      field_simp
    rw [this, abs_mul, abs_of_pos (by positivity)]
  simp_rw [hpt, ← Finset.mul_sum]
  field_simp

/-- **(8.1, `eq:A1`)** from Theorem 3.1 [`thm:jointmixing`]. -/
theorem offsetMixing_of_jointMixing (hJM : JointMixing) : OffsetMixing := by
  intro A hA
  obtain ⟨C, hC⟩ := marginal_of_jointMixing hJM A hA
  refine ⟨C, fun m q hm hmq => ?_⟩
  rw [normL1_rho_sub, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC m q hm hmq) (by norm_num)

/-- **(8.1, `eq:A1`)** from Tao's two imports (Imported Theorems 2.3 and 2.4). -/
theorem offsetMixing_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) : OffsetMixing :=
  offsetMixing_of_jointMixing (jointMixing_of_tao hTM hTP)

end CollatzCLT
