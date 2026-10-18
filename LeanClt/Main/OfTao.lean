import LeanClt.Transfer.Final
import LeanClt.Mixing.Telescope

/-!
# Theorems 5.10, 6.1 and 1.1 (i)–(iii) with Tao's imports in place of Theorem 3.1

Theorem 3.1 [`thm:jointmixing`] is now proved from Tao's two imports (`jointMixing_of_tao`,
`Mixing/Telescope.lean`). Substituting it into the §5–§6 results removes `JointMixing` from their
hypotheses. What remains:

* `TaoMajorant`, `TaoPrefix`: Imported Theorems 2.3 [`imp:majorant`] and 2.4 [`imp:prefix`];
* `IrrMeasure d ϰ`: Rhin's measure, Imported Theorem 2.6 [`imp:rhin`];
* for Theorem 1.1, positive lower density of the raw predecessor set (Theorem 8.1
  [`thm:positivity`]), as an inline hypothesis.
-/

open Real Finset Complex Filter

namespace CollatzCLT

/-- **Theorem 5.10 [`thm:transfer`]** from Tao's imports. -/
theorem transfer_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) (ρ η A : ℝ) (hA : 0 < A) :
    ∃ C x₀ : ℝ, ∀ x Y : ℝ, x₀ ≤ x → x ^ alpha ≤ Y → Y ≤ x ^ (alpha ^ 2) →
      ∀ E : Finset ℕ, (↑E : Set ℕ) ⊆ Mset x → ∀ (q : ℕ → ℝ) (s : ℝ),
        ‖transferLHS x Y E q ρ η s - transferRHS x Y E q ρ η s‖ ≤ C * Lx x ^ (-A) :=
  transfer (jointMixing_of_tao hTM hTP) ρ η A hA

/-- The scalar form of Theorem 5.10 [`thm:transfer`] from Tao's imports and Rhin's measure. -/
theorem transfer_scalar_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) (ϰ : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ d : ℝ, IrrMeasure d ϰ → ∃ C x₀ : ℝ, ∀ x Y : ℝ, x₀ ≤ x →
      x ^ alpha ≤ Y → Y ≤ x ^ (alpha ^ 2) → ∀ E : Finset ℕ, (↑E : Set ℕ) ⊆ Mset x →
        |eventProb x Y E - 2 / c * ∑ M ∈ E, (3 : ℝ) ^ mT x / M * probXm (mT x) M| ≤
          C * Lx x ^ (-δ₀) :=
  transfer_scalar (jointMixing_of_tao hTM hTP) ϰ

open Classical in
/-- **Lemma 6.1 [`lem:adjacent`]** from Tao's imports and Rhin's measure. -/
theorem adjacent_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {A : Set ℕ} {q : ℕ → ℝ} {ρ η x₀ : ℝ} (htr : Transport A q ρ η x₀) :
    AdjacentScales (oddCF A q ((2 * ρ + η) / c)) ((ρ * bet + η * ell) ^ 2 / c ^ 3) alpha :=
  adjacent_of_transport (jointMixing_of_tao hTM hTP) hθ htr

/-- **Theorem 1.1 [`thm:main`] (i)+(ii), raw clock**, from Tao's imports, Rhin's measure and
positivity. -/
theorem main_T_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b)
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (Pred T b) X).card : ℝ)) :
    (∃ d > 0, HasDensity (Pred T b) d) ∧ CLTOn (Pred T b) (normalised (hit T b) κT VT) :=
  main_T_of_mixing (jointMixing_of_tao hTM hTP) hθ b hb hpos

/-- **Theorem 1.1 [`thm:main`] (i)+(ii), shortcut clock**, from Tao's imports, Rhin's measure and
positivity of `P_T(2b)`. -/
theorem main_F_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b)
    (hposT : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      c * X ≤ ((window (Pred T (2 * b)) X).card : ℝ)) :
    (∃ d > 0, HasDensity (Pred F b) d) ∧ CLTOn (Pred F b) (normalised (hit F b) κF VF) :=
  main_F_of_mixing (jointMixing_of_tao hTM hTP) hθ b hb hposT

/-- **Theorem 1.1 [`thm:main`] (iii), odd clock**, from Tao's imports, Rhin's measure and
positivity of `P_T(b)`, for odd `b`. -/
theorem main_U_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : Odd b)
    (hposT : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (Pred T b) X).card : ℝ)) :
    (∃ d > 0, HasDensity (PredU b) d) ∧ CLTOn (PredU b) (normalised (hit U b) κU VU) :=
  main_U_of_mixing (jointMixing_of_tao hTM hTP) hθ b hb hposT

end CollatzCLT
