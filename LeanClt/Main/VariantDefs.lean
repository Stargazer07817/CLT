import LeanClt.Defs

/-!
# Definitions for Theorem 1.1(iv), the closing sentence of Theorem 1.1, and Corollary 1.2

Four definitions, in the style of `window`, `HasDensity` and `CLTOn` (`LeanClt/Defs.lean`):

* `dyWindow A X`: the finite sample `A ∩ [X, 2X]`, for real `X`;
* `CLTOnDy A stat`: the CLT under uniform sampling from `A ∩ [X, 2X]`, as the real `X → ∞`;
* `JointLaw L W S₁ S₂ S₃ a₁ a₂ a₃`: joint convergence in law of three statistics to the rank-one
  Gaussian vector `(a₁, a₂, a₃) Z`, `Z ~ N(0,1)`, under uniform sampling from `W i` along `L`;
* `HasOddDensity A d`: `A` has density `d` among the odd integers.

Modelling choices:
* In `CLTOnDy` and `dyWindow` the parameter `X` is real. Unlike `[1, X]`, whose integer points depend
  only on `⌊X⌋`, the integer points `⌈X⌉, …, ⌊2X⌋` of `[X, 2X]` are not all of the form `m, …, 2m`,
  so a real parameter is used rather than a natural one.
* `JointLaw` is stated through the joint distribution function at every point of `ℝ³`. When all
  `a_k > 0` (the only case used) the limit distribution function
  `z ↦ P(a₁ Z ≤ z₁, a₂ Z ≤ z₂, a₃ Z ≤ z₃) = Φ(min_k z_k / a_k)` is continuous, so this is
  equivalent to convergence in distribution in `ℝ³`.
-/

open Real Filter Topology ProbabilityTheory MeasureTheory

noncomputable section

namespace CollatzCLT

open Classical in
/-- The finite sample `A ∩ [X, 2X]` (`X` real): the members of `A` among `⌈X⌉, …, ⌊2X⌋`. -/
def dyWindow (A : Set ℕ) (X : ℝ) : Finset ℕ := (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter (· ∈ A)

open Classical in
/-- `CLTOnDy A stat`: if `N_X` is uniform on `A ∩ [X, 2X]`, then `stat X N_X` converges in law to
`N(0,1)` as the real `X → ∞`. Distribution-function form: for every real `z`, the proportion of
`n ∈ A ∩ [X, 2X]` with `stat X n ≤ z` tends to `Φ(z)`. -/
def CLTOnDy (A : Set ℕ) (stat : ℝ → ℕ → ℝ) : Prop :=
  ∀ z : ℝ, Tendsto (fun X : ℝ =>
      (((dyWindow A X).filter (fun n => stat X n ≤ z)).card : ℝ) / (dyWindow A X).card)
    atTop (𝓝 (Φ z))

open Classical in
/-- `JointLaw L W S₁ S₂ S₃ a₁ a₂ a₃`: if `N_i` is uniform on the finite sample `W i`, then
`(S₁ i N_i, S₂ i N_i, S₃ i N_i)` converges in law, along `L`, to `(a₁ Z, a₂ Z, a₃ Z)` with
`Z ~ N(0,1)`. Distribution-function form: for all real `z₁, z₂, z₃`, the proportion of `n ∈ W i`
with `S₁ i n ≤ z₁`, `S₂ i n ≤ z₂` and `S₃ i n ≤ z₃` tends to
`P(a₁ Z ≤ z₁, a₂ Z ≤ z₂, a₃ Z ≤ z₃)`. When every `a_k ≠ 0` the limit distribution function is
continuous, so this is equivalent to convergence in law; if some `a_k = 0` it is strictly stronger
(it asks for convergence at the jump `z_k = 0`). -/
def JointLaw {ι : Type*} (L : Filter ι) (W : ι → Finset ℕ) (S₁ S₂ S₃ : ι → ℕ → ℝ)
    (a₁ a₂ a₃ : ℝ) : Prop :=
  ∀ z₁ z₂ z₃ : ℝ, Tendsto (fun i =>
      (((W i).filter (fun n => S₁ i n ≤ z₁ ∧ S₂ i n ≤ z₂ ∧ S₃ i n ≤ z₃)).card : ℝ) / (W i).card)
    L (𝓝 ((gaussianReal 0 1).real {w : ℝ | a₁ * w ≤ z₁ ∧ a₂ * w ≤ z₂ ∧ a₃ * w ≤ z₃}))

/-- `A` has density `d` among the odd integers:
`#({n ∈ A : n odd} ∩ [1,X]) / #({odd} ∩ [1,X]) → d`. -/
def HasOddDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun X : ℕ => ((window {n | n ∈ A ∧ Odd n} X).card : ℝ) / (window {n | Odd n} X).card)
    atTop (𝓝 d)

end CollatzCLT
