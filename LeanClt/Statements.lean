import LeanClt.Defs
import LeanClt.Renewal.Defs
import LeanClt.Mixing.Imports
import LeanClt.Main.OfTao
import LeanClt.Positivity.Main
import LeanClt.Exceptional.Corollaries
import LeanClt.Main.Variants
import LeanClt.Main.Joint
import LeanClt.Main.Rates
import LeanClt.Potential.Main
import LeanClt.Renewal.FixedFreq
import LeanClt.Applications.AntiConc
import LeanClt.Applications.Escape
import LeanClt.Applications.Harmonic
import LeanClt.Applications.ModQ

/-!
# Collatz CLT — statements of the main results

States Theorem 1.1 (i)–(iv) with its closing sentence, Corollaries 1.2, 1.5 and 1.6, and Theorem 1.4.
Its last section names Proposition 4.5 and the results 6.10–6.13, stated in their own files.
Definitions are in `LeanClt/Defs.lean` (for the closing sentence, (iv) and Corollary 1.2 also
`LeanClt/Main/VariantDefs.lean`); those of Corollaries 1.5 and 1.6 are in
`LeanClt/Exceptional/Defs.lean` and `LeanClt/Exceptional/Rays.lean`, over `Merge` and `IsPeriodic`
from `LeanClt/Elementary/Flow.lean`.
The closing sentence of Theorem 1.1 (sampling on `[X, 2X]`; `log X` in place of `log N_X` in the
centring) is stated for (ii) and (iii) after the corollaries (`clt_T_variants`, `clt_F_variants`,
`clt_U_variants`), with the definitions `dyWindow` and `CLTOnDy` of `LeanClt/Main/VariantDefs.lean`.
Theorem 1.1(iv) is `joint_clocks`, with the predicate `JointLaw`, and its closing-sentence variants
are `joint_clocks_variants`. Corollary 1.2 is `rates_T`, `rates_F` and `rates_U`, the last with the
predicate `HasOddDensity`. These come after the corollaries, before Theorem 1.4.
Modelling choices:
* For samples `A ∩ [1, X]` the bound `X` runs over natural numbers (equivalent to real `X`); for
  samples `A ∩ [X, 2X]` (`dyWindow`) it is real.
* Convergence in law to N(0,1) is stated via distribution functions (`CLTOn`, `CLTOnDy`),
  equivalent to convergence in distribution because `Φ` is continuous; the joint law of
  Theorem 1.1(iv) via the joint distribution function at every point of `ℝ³` (`JointLaw`),
  equivalent because its three coefficients are positive.
* Rhin's irrationality measure for `log₂ 3` (the paper's Imported Theorem 2.6, `imp:rhin`) enters as
  an explicit hypothesis `IrrMeasure d ϰ`, as in the paper; it is not proved in Lean. (It is used
  through Theorem 4.1 [`thm:renewal`]; see `Renewal/Theorem41.lean`.)
* Two of Tao's three imports (the paper's Imported Theorems 2.3 and 2.4, `imp:majorant` and
  `imp:prefix`) enter as explicit hypotheses `TaoMajorant` and `TaoPrefix` (`Mixing/Imports.lean`);
  they are not proved in Lean. The third, Imported Theorem 2.5 [`imp:coupling`], is not used.
  `TaoPrefix` is a weakened form of Imported Theorem 2.4, so these targets are
  no weaker than the paper's statement. They feed §3 and, through Theorem 3.1, the input (8.1)
  of §8 (`offsetMixing_of_tao`), where the paper cites Tao's Prop. 1.14 directly.
* Corollaries 1.5 and 1.6: the merging classes are the classes of `mergeSetoid`; the quotient has
  one extra class, that of `0`, whose `classSet` is empty. The divergent clause of Corollary 1.5
  [`cor:dichotomy`] is stated through the conclusions `RayEntryLaw`, `RayJointLaw` and
  `RayMovingLaw` of Theorems 6.7 and 6.8 (`Exceptional/Rays.lean`); its cycle clause is stated for
  every cycle, the trivial one included. In Corollary 1.6 [`cor:unconditional`] a choice of
  reference orbits is a function `ref` with `RefChoice ref` (one exists: `refChoice_exists`), and
  the change-of-reference clause is the separate lemma `ref_change`, stated for every class.

The four theorems for Theorem 1.1 (i)–(iii) (`density_pos`, `clt_T`, `clt_F`, `clt_U`) are proved
from `main_T_of_tao`, `main_F_of_tao`, `main_U_of_tao`
(`Main/OfTao.lean`) and Theorem 8.1 [`thm:positivity`] (`Positivity.positivity_of_tao`,
`Positivity/Main.lean`); the shortcut clock uses positivity of `P_T(2b)`. The closing-sentence
variants, Theorem 1.1(iv) and Corollary 1.2 are proved from `clt_T_variants_of_tao`,
`clt_F_variants_of_tao`, `clt_U_variants_of_tao` (`Main/Variants.lean`), `joint_clocks_of_tao` and
`joint_clocks_variants_of_tao` (`Main/Joint.lean`) and `rates_T_of_tao`, `rates_F_of_tao`,
`rates_U_of_tao` (`Main/Rates.lean`). Corollaries 1.5 and 1.6
are proved from `dichotomy_of_tao` and `unconditional_of_tao` (`Exceptional/Corollaries.lean`),
which take Theorem 1.1 from `main_T_of_tao` directly, so that this file can import them.

Theorem 1.4 [`thm:potential`] is `potential`, after Corollary 1.2. Its definitions `natDens` and
`hpot` are in `LeanClt/Potential/Defs.lean`: `natDens A` is the `limUnder` of the ratio
`#(A ∩ [1, X]) / X` of `HasDensity` (a junk value when there is no limit), and the potential
`h(n) = dens P_T(n)` is `hpot n = natDens (Pred T n)`, pinned by the first conjunct of `potential`.
The statement also uses `IsPeriodic` and `fwdOrbit`; the constants `C, ε` of (iii) are chosen after
`d, ϰ`, which v8's "absolute" treats as fixed. It is proved from `potential_of_tao`
(`Potential/Main.lean`), which assembles the results of §7 in `LeanClt/Potential/`.
-/

open Real

namespace CollatzCLT

/-! ## Theorem 1.1 -/

/-- **Theorem 1.1(i).** For `3 ∤ b`, `P_T(b)` and `P_F(b)` have positive natural densities. -/
theorem density_pos (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    (∃ d > 0, HasDensity (Pred T b) d) ∧ (∃ d > 0, HasDensity (Pred F b) d) :=
  ⟨(main_T_of_tao hTM hTP hθ b hb (Positivity.positivity_of_tao hTM hTP hb h3)).1,
    (main_F_of_tao hTM hTP hθ b hb (Positivity.positivity_of_tao hTM hTP (by omega)
      (fun h => h3 ((Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 3 2)).mp h)))).1⟩

/-- **Theorem 1.1(ii), raw clock.** -/
theorem clt_T (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    CLTOn (Pred T b) (normalised (hit T b) κT VT) :=
  (main_T_of_tao hTM hTP hθ b hb (Positivity.positivity_of_tao hTM hTP hb h3)).2

/-- **Theorem 1.1(ii), shortcut clock.** -/
theorem clt_F (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    CLTOn (Pred F b) (normalised (hit F b) κF VF) :=
  (main_F_of_tao hTM hTP hθ b hb (Positivity.positivity_of_tao hTM hTP (by omega)
    (fun h => h3 ((Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 3 2)).mp h)))).2

/-- **Theorem 1.1(iii), odd clock.** For odd `b` with `3 ∤ b`, sampling from `P_U(b)`. -/
theorem clt_U (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    CLTOn (PredU b) (normalised (hit U b) κU VU) :=
  (main_U_of_tao hTM hTP hθ b hb (Positivity.positivity_of_tao hTM hTP hb.pos h3)).2

/-! ## Sanity checks on the definitions -/

example : T 7 = 22 := by decide
example : F 7 = 11 := by decide

/-! ## Corollaries 1.5 and 1.6 -/

section Corollaries

open Filter Topology Finset

/-- **Corollary 1.5 [`cor:dichotomy`].** The cycle clause is stated for every cycle (the paper: a
non-trivial one). -/
theorem dichotomy (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    (∃ dE : ℝ, HasDensity Exc dE ∧ dE < 1 ∧ (Exc.Nonempty → 0 < dE)) ∧
    (HasDensity (Pred T 1) 1 ↔ Exc = ∅) ∧
    (∀ b ∈ Exc, ¬ 3 ∣ b → Pred T b ⊆ Exc ∧ (∃ d > 0, HasDensity (Pred T b) d) ∧
      CLTOn (Pred T b) (normalised (hit T b) κT VT)) ∧
    (∀ b : ℕ, 0 < b → IsPeriodic b →
      (∃ d > 0, HasDensity (Reach (fwdOrbit b)) d) ∧
      CLTOn (Reach (fwdOrbit b)) (normalised (entry (fwdOrbit b)) κT VT)) ∧
    (∀ a : ℕ, 0 < a → NonRepeating a → RayEntryLaw a ∧ RayJointLaw a ∧ RayMovingLaw a) :=
  dichotomy_of_tao hTM hTP hθ

open Classical in
/-- **Corollary 1.6 [`cor:unconditional`].** -/
theorem unconditional (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {ref : ℕ → ℕ} (href : RefChoice ref) :
    (∀ n : ℕ, 0 < n → ∃ k, T^[k] n ∈ fwdOrbit (ref n)) ∧
    (∀ n0 : ℕ, 0 < n0 → ∃ pC : ℝ, HasDensity (mergeClass n0) pC ∧ ∀ z : ℝ,
      Tendsto (fun X : ℕ => ((((Icc 1 X).filter (fun n => n ∈ mergeClass n0 ∧
          normalised (eps ref) κT VT X n ≤ z)).card : ℝ) / X)) atTop (𝓝 (pC * Φ z))) ∧
    CLTOn {n | 0 < n} (normalised (eps ref) κT VT) ∧
    (∀ c0 : ℝ, HasDensity {n | 0 < n ∧ (eps ref n : ℝ) ≤ c0 * Real.log n}
      (if κT < c0 then 1 else if c0 = κT then 1 / 2 else 0)) ∧
    (∀ n ∈ Pred T 1, eps ref n ≤ hit T 1 n ∧ hit T 1 n ≤ eps ref n + 2) :=
  unconditional_of_tao hTM hTP hθ href

end Corollaries

/-! ## The closing sentence of Theorem 1.1

"The same limits hold for sampling on dyadic intervals `[X, 2X]`, and `log N_X` may be replaced by
`log X` in the centring." Read as applying to the limit laws (ii)–(iv), not to the densities of (i).
For each law, three variants are stated next to the printed one (`[1, X]` with `log N_X`):
`[1, X]` with `log X`; `[X, 2X]` with `log N_X`; `[X, 2X]` with `log X`. On `[X, 2X]` the parameter
`X` is real (`dyWindow`, `CLTOnDy`), because the integer points of `[X, 2X]` are not all of the form
`m, …, 2m`. The proofs for (ii) and (iii) are in `LeanClt/Main/Variants.lean`; those for (iv)
(`joint_clocks_variants`, next section) are in `LeanClt/Main/Joint.lean`. -/

/-- **Theorem 1.1 [`thm:main`], closing sentence, applied to (ii), raw clock**: `[1, X]` with
centring `κ_T log X`; `[X, 2X]` (`X` real) with centring `κ_T log N_X`; `[X, 2X]` with `κ_T log X`. -/
theorem clt_T_variants (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    CLTOn (Pred T b) (fun X n => ((hit T b n : ℝ) - κT * log X) / √(VT * log X)) ∧
    CLTOnDy (Pred T b) (fun X n => ((hit T b n : ℝ) - κT * log n) / √(VT * log X)) ∧
    CLTOnDy (Pred T b) (fun X n => ((hit T b n : ℝ) - κT * log X) / √(VT * log X)) :=
  clt_T_variants_of_tao hTM hTP hθ b hb h3

/-- **Theorem 1.1 [`thm:main`], closing sentence, applied to (ii), shortcut clock**: `[1, X]` with
centring `κ_F log X`; `[X, 2X]` (`X` real) with centring `κ_F log N_X`; `[X, 2X]` with `κ_F log X`. -/
theorem clt_F_variants (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    CLTOn (Pred F b) (fun X n => ((hit F b n : ℝ) - κF * log X) / √(VF * log X)) ∧
    CLTOnDy (Pred F b) (fun X n => ((hit F b n : ℝ) - κF * log n) / √(VF * log X)) ∧
    CLTOnDy (Pred F b) (fun X n => ((hit F b n : ℝ) - κF * log X) / √(VF * log X)) :=
  clt_F_variants_of_tao hTM hTP hθ b hb h3

/-- **Theorem 1.1 [`thm:main`], closing sentence, applied to (iii), odd clock**: sampling from
`P_U(b)`; `[1, X]` with centring `κ_U log X`; `[X, 2X]` (`X` real) with centring `κ_U log N_X`;
`[X, 2X]` with `κ_U log X`. -/
theorem clt_U_variants (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    CLTOn (PredU b) (fun X n => ((hit U b n : ℝ) - κU * log X) / √(VU * log X)) ∧
    CLTOnDy (PredU b) (fun X n => ((hit U b n : ℝ) - κU * log n) / √(VU * log X)) ∧
    CLTOnDy (PredU b) (fun X n => ((hit U b n : ℝ) - κU * log X) / √(VU * log X)) :=
  clt_U_variants_of_tao hTM hTP hθ b hb h3

/-! ## Theorem 1.1(iv)

The joint law is stated through the joint distribution function at every point of `ℝ³`
(`JointLaw`), which is equivalent to convergence in distribution because all three coefficients
are positive. The proofs are in `LeanClt/Main/Joint.lean`. -/

section JointLaw

open Filter

/-- **Theorem 1.1(iv) [`thm:main`].** For odd `b` with `3 ∤ b` and `N_X` uniform on
`P_U(b) ∩ [1, X]`, the three clocks `(τ_U, τ_F, τ_T)(N_X)`, centred at
`(κ_U, κ_F, κ_T) log N_X = (1, 2, 3) c⁻¹ log N_X` and divided by `√(log X)`, converge jointly in law
to `√(2/c³) (ℓ, β, β + ℓ) Z` with `Z ~ N(0,1)`, `ℓ = log 2`, `β = log 3`. -/
theorem joint_clocks (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    JointLaw atTop (window (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * log n) / √(log X))
      (fun X n => ((hit F b n : ℝ) - κF * log n) / √(log X))
      (fun X n => ((hit T b n : ℝ) - κT * log n) / √(log X))
      (√(2 / c ^ 3) * log 2) (√(2 / c ^ 3) * log 3) (√(2 / c ^ 3) * (log 3 + log 2)) :=
  joint_clocks_of_tao hTM hTP hθ b hb h3

/-- **Theorem 1.1 [`thm:main`], closing sentence, applied to (iv)**: `[1, X]` with centring
`(κ_U, κ_F, κ_T) log X`; `[X, 2X]` (`X` real) with centring `(κ_U, κ_F, κ_T) log N_X`; `[X, 2X]` with
`(κ_U, κ_F, κ_T) log X`. -/
theorem joint_clocks_variants (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ}
    (hθ : IrrMeasure d ϰ) (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    JointLaw atTop (window (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * log X) / √(log X))
      (fun X n => ((hit F b n : ℝ) - κF * log X) / √(log X))
      (fun X n => ((hit T b n : ℝ) - κT * log X) / √(log X))
      (√(2 / c ^ 3) * log 2) (√(2 / c ^ 3) * log 3) (√(2 / c ^ 3) * (log 3 + log 2)) ∧
    JointLaw atTop (dyWindow (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * log n) / √(log X))
      (fun X n => ((hit F b n : ℝ) - κF * log n) / √(log X))
      (fun X n => ((hit T b n : ℝ) - κT * log n) / √(log X))
      (√(2 / c ^ 3) * log 2) (√(2 / c ^ 3) * log 3) (√(2 / c ^ 3) * (log 3 + log 2)) ∧
    JointLaw atTop (dyWindow (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * log X) / √(log X))
      (fun X n => ((hit F b n : ℝ) - κF * log X) / √(log X))
      (fun X n => ((hit T b n : ℝ) - κT * log X) / √(log X))
      (√(2 / c ^ 3) * log 2) (√(2 / c ^ 3) * log 3) (√(2 / c ^ 3) * (log 3 + log 2)) :=
  joint_clocks_variants_of_tao hTM hTP hθ b hb h3

end JointLaw

/-! ## Corollary 1.2

`τ_{G,b} = ∞` off `P_G(b)` in the paper, so the sets of the corollary are restricted to `P_G(b)`
(`hit` is `0` there in Lean). `p` is `dens P_G(b)`; the conjunct `p > 0` (Theorem 1.1(i)) is not part
of the printed corollary. `η` is a real function, as printed; it is evaluated at integers. For the
odd clock, densities are taken among the odd integers (`HasOddDensity`), as printed; the existence
and positivity of the odd density of `P_U(b)` itself are not printed (they follow from
`P_T(b) = {2^e u : u ∈ P_U(b)}`). The proofs are in `LeanClt/Main/Rates.lean`. -/

section Rates

open Filter

/-- **Corollary 1.2 [`cor:rates`], raw clock.** With `p = dens P_T(b)`: the set
`{n : τ_{T,b}(n) ≤ c₀ log n}` has density `p`, `p/2` or `0` according as `c₀ > κ_T`, `c₀ = κ_T` or
`c₀ < κ_T`; `{n : τ_{T,b}(n) ≤ κ_T log n + z √(V_T log n)}` has density `Φ(z) p`; and
`{n : τ_{T,b}(n) ≤ (κ_T + η(n)) log n}` has density `p` (respectively `0`) when
`η(x) √(log x) → +∞` (respectively `-∞`). -/
theorem rates_T (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    ∃ p > 0, HasDensity (Pred T b) p ∧
      (∀ c₀ : ℝ, HasDensity {n | n ∈ Pred T b ∧ (hit T b n : ℝ) ≤ c₀ * log n}
        (if κT < c₀ then p else if c₀ = κT then p / 2 else 0)) ∧
      (∀ z : ℝ, HasDensity
        {n | n ∈ Pred T b ∧ (hit T b n : ℝ) ≤ κT * log n + z * √(VT * log n)} (Φ z * p)) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(log x)) atTop atTop →
        HasDensity {n | n ∈ Pred T b ∧ (hit T b n : ℝ) ≤ (κT + η n) * log n} p) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(log x)) atTop atBot →
        HasDensity {n | n ∈ Pred T b ∧ (hit T b n : ℝ) ≤ (κT + η n) * log n} 0) :=
  rates_T_of_tao hTM hTP hθ b hb h3

/-- **Corollary 1.2 [`cor:rates`], shortcut clock**, as `rates_T` with `(κ_F, V_F)` and `P_F(b)`. -/
theorem rates_F (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    ∃ p > 0, HasDensity (Pred F b) p ∧
      (∀ c₀ : ℝ, HasDensity {n | n ∈ Pred F b ∧ (hit F b n : ℝ) ≤ c₀ * log n}
        (if κF < c₀ then p else if c₀ = κF then p / 2 else 0)) ∧
      (∀ z : ℝ, HasDensity
        {n | n ∈ Pred F b ∧ (hit F b n : ℝ) ≤ κF * log n + z * √(VF * log n)} (Φ z * p)) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(log x)) atTop atTop →
        HasDensity {n | n ∈ Pred F b ∧ (hit F b n : ℝ) ≤ (κF + η n) * log n} p) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(log x)) atTop atBot →
        HasDensity {n | n ∈ Pred F b ∧ (hit F b n : ℝ) ≤ (κF + η n) * log n} 0) :=
  rates_F_of_tao hTM hTP hθ b hb h3

/-- **Corollary 1.2 [`cor:rates`], odd clock**, for odd `b`: as `rates_T` with `(κ_U, V_U)`,
`P_U(b)` and densities taken among the odd integers. -/
theorem rates_U (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    ∃ p > 0, HasOddDensity (PredU b) p ∧
      (∀ c₀ : ℝ, HasOddDensity {n | n ∈ PredU b ∧ (hit U b n : ℝ) ≤ c₀ * log n}
        (if κU < c₀ then p else if c₀ = κU then p / 2 else 0)) ∧
      (∀ z : ℝ, HasOddDensity
        {n | n ∈ PredU b ∧ (hit U b n : ℝ) ≤ κU * log n + z * √(VU * log n)} (Φ z * p)) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(log x)) atTop atTop →
        HasOddDensity {n | n ∈ PredU b ∧ (hit U b n : ℝ) ≤ (κU + η n) * log n} p) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(log x)) atTop atBot →
        HasOddDensity {n | n ∈ PredU b ∧ (hit U b n : ℝ) ≤ (κU + η n) * log n} 0) :=
  rates_U_of_tao hTM hTP hθ b hb h3

end Rates

/-! ## Theorem 1.4 -/

section Potential

open Real Filter Topology Finset

/-- **Theorem 1.4 [`thm:potential`].** The conjuncts, in order: the density `h(n)` exists for every
`n ≥ 1`; `h(n) > 0` iff `3 ∤ n`; (i) the flow identity at nonperiodic `n`; (ii) decay along every
backward ray of distinct positive integers; (iii) the finite-orbit approximation, with real weights
and `f_K ≥ 0` as printed; (iv) `h → 0` iff every `T`-orbit is eventually periodic. -/
theorem potential (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    (∀ n : ℕ, 0 < n → HasDensity (Pred T n) (hpot n)) ∧
    (∀ n : ℕ, 0 < n → (0 < hpot n ↔ ¬ 3 ∣ n)) ∧
    (∀ n : ℕ, 0 < n → ¬ IsPeriodic n →
      hpot n = hpot (2 * n) + (if n % 6 = 4 then hpot ((n - 1) / 3) else 0)) ∧
    (∀ v : ℕ → ℕ, (∀ j, 0 < v j) → Function.Injective v → (∀ j, T (v (j + 1)) = v j) →
      Tendsto (fun j => hpot (v j)) atTop (𝓝 0)) ∧
    (∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ K : ℕ, 2 ≤ K → ∃ f : ℕ → ℝ,
      (∃ w : ℕ → ℝ, ∀ n, f n =
        ∑ k ∈ (range (K + 1)).filter Odd, w k * (fwdOrbit k).indicator (fun _ => (1 : ℝ)) n) ∧
      (∀ n, 0 ≤ f n) ∧
      ∀ n : ℕ, 0 < n → 0 ≤ hpot n - f n ∧ hpot n - f n ≤ C * (Real.log K) ^ (-ε)) ∧
    (Tendsto hpot atTop (𝓝 0) ↔ ∀ n : ℕ, 0 < n → ∃ i, IsPeriodic (T^[i] n)) :=
  potential_of_tao hTM hTP hθ

end Potential

/-! ## Proposition 4.5, Theorem 6.10, Corollary 6.11, Proposition 6.12 and Theorem 6.13

Proposition 4.5 and the four labelled results of §6.8–6.9 are not used by the results above. They
are stated and proved in their own files, under the names their statements were audited with
(checkpoint 20); this file imports them and does not restate them. Each carries only the standing
hypotheses its proof uses.

* Proposition 4.5 [`prop:fixedfreq`] is `fixedfreq` (`LeanClt/Renewal/FixedFreq.lean`):
  decay of the twisted kernel `renewalR` at a fixed frequency `s = 2πr/Q₀`, `gcd(r, Q₀) = 1`.
  Hypothesis: `IrrMeasure d ϰ` only.
* Theorem 6.10 [`thm:anticonc`] is `anticonc` (`LeanClt/Applications/AntiConc.lean`):
  anti-concentration of the clocks on `P_G(b)` and of the spatial coordinates of divergent classes.
  Hypotheses: `TaoMajorant` and `TaoPrefix` only (no Diophantine input, as printed).
* Corollary 6.11 [`cor:escape`] is `escape` (`LeanClt/Applications/Escape.lean`):
  deterministic-time escape from a divergent class.
  Hypotheses: `TaoMajorant`, `TaoPrefix` and `IrrMeasure d ϰ`.
* Proposition 6.12 [`prop:harmonicfirsthit`] is `harmonicfirsthit`
  (`LeanClt/Applications/Harmonic.lean`): the first-hit harmonic sums.
  Hypotheses: `TaoMajorant` and `TaoPrefix` only.
* Theorem 6.13 [`thm:modq`] is `modq` (`LeanClt/Applications/ModQ.lean`): equidistribution of
  the hitting times modulo `Q₀`. Hypotheses: `TaoMajorant`, `TaoPrefix` and `IrrMeasure d ϰ`.

The new definitions they use are `levelCount` (`LeanClt/Applications/AntiConc.lean`), the number
of `n ≤ X` in a set at a given level of an integer clock or coordinate, and `coordT` and `coordF`
(`LeanClt/Applications/Coordinates.lean`), the raw and shortcut spatial coordinates of a divergent
class, with the shortcut ray objects `fwdOrbitF`, `entryF` and `rayIndexF`. They also use
`fwdOrbit`, `NonRepeating`, `mergeClass` and `AK` (`LeanClt/Exceptional/Defs.lean`) and `Merge`
(`LeanClt/Elementary/Flow.lean`). A divergent class is `mergeClass a` for a base point `a > 0`
with `NonRepeating a`, as in Corollary 1.5. The pinned kernel `pinnedK`
(`LeanClt/Applications/Kernel.lean`) of the proof of Theorem 6.10 appears in no headline
statement. `IrrMeasure d ϰ` enters `fixedfreq` through Lemma 2.7 with `Q₀` jumps
(`rotation_discrepancy_jumps`) and through the extra-endpoint term `err_extra` of the proof of
Theorem 4.1, which it reuses. The statements fix the order of the constants: in `fixedfreq` the
constant is chosen after `d, ϰ, ρ, η, Q₀` and before `r`; in `escape` after `d, ϰ`, as for
Theorem 1.4; in `anticonc` and the first bound of `harmonicfirsthit` after the Tao hypotheses
alone, and in the second bound of `harmonicfirsthit` after `b` (the printed `O_b`). The docstrings
describe the quantifiers clause by clause. -/

end CollatzCLT
