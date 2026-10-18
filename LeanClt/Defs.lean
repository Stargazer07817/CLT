import Mathlib

/-!
# Collatz CLT — basic definitions

Shared definitions for the formalization of
"Natural-density central limit theorems for Collatz hitting times".

Conventions: we work on `ℕ`; "positive integer" becomes `0 < n`. The maps are
defined on all of `ℕ` (with `T 0 = 0` and so on), which is harmless because every
statement restricts to positive integers.
-/

open Real Filter Topology

noncomputable section

namespace CollatzCLT

/-! ## The three maps -/

/-- The Collatz map `T(n) = n/2` (n even), `3n+1` (n odd). -/
def T (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n + 1

/-- The shortcut map `F(n) = n/2` (n even), `(3n+1)/2` (n odd). -/
def F (n : ℕ) : ℕ := if Even n then n / 2 else (3 * n + 1) / 2

/-- The Syracuse map `U(n) = (3n+1) / 2^{v₂(3n+1)}`, used on odd `n`. -/
def U (n : ℕ) : ℕ := (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1)

/-! ## Predecessor sets and hitting times -/

/-- `Pred G b`: the positive integers whose `G`-orbit visits `b` (the paper's `P_G(b)`). -/
def Pred (G : ℕ → ℕ) (b : ℕ) : Set ℕ := {n | 0 < n ∧ ∃ k, G^[k] n = b}

/-- `PredU b`: the odd positive integers whose `U`-orbit visits `b` (the paper's `P_U(b)`). -/
def PredU (b : ℕ) : Set ℕ := {n | 0 < n ∧ Odd n ∧ ∃ k, U^[k] n = b}

/-- First hitting time `τ_{G,b}(n) = min {k : G^k(n) = b}`. Only meaningful on `Pred G b`;
off it the set is empty and Lean's convention `sInf ∅ = 0` applies. -/
def hit (G : ℕ → ℕ) (b n : ℕ) : ℕ := sInf {k | G^[k] n = b}

/-! ## Natural density and sampling -/

open Classical in
/-- The finite sample `A ∩ [1, X]`. -/
def window (A : Set ℕ) (X : ℕ) : Finset ℕ := (Finset.Icc 1 X).filter (· ∈ A)

/-- `A` has natural density `d`: `#(A ∩ [1,X]) / X → d`. -/
def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun X : ℕ => ((window A X).card : ℝ) / X) atTop (𝓝 d)

/-! ## Constants ((1.1) for `c`; (1.3) for `κ_T, V_T, κ_F, V_F`; `κ_U, V_U` from Theorem 1.1(iii)) -/

/-- `c = log(4/3) = 2 log 2 - log 3`. -/
def c : ℝ := log (4 / 3)

def κT : ℝ := 3 / c
def VT : ℝ := 2 * (log 3 + log 2) ^ 2 / c ^ 3
def κF : ℝ := 2 / c
def VF : ℝ := 2 * (log 3) ^ 2 / c ^ 3
def κU : ℝ := 1 / c
def VU : ℝ := 2 * (log 2) ^ 2 / c ^ 3

/-- The standard normal distribution function `Φ`. -/
def Φ (z : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) z

/-! ## The CLT predicate -/

open Classical in
/-- `CLTOn A stat`: if `N_X` is uniform on `A ∩ [1,X]`, then `stat X N_X` converges in
law to `N(0,1)`. Distribution-function form: for every real `z`, the proportion of
`n ∈ A ∩ [1,X]` with `stat X n ≤ z` tends to `Φ(z)`. -/
def CLTOn (A : Set ℕ) (stat : ℕ → ℕ → ℝ) : Prop :=
  ∀ z : ℝ, Tendsto (fun X : ℕ =>
      (((window A X).filter (fun n => stat X n ≤ z)).card : ℝ) / (window A X).card)
    atTop (𝓝 (Φ z))

/-- The normalised statistic of (1.2): `(τ(n) - κ log n) / √(V log X)`. -/
def normalised (τ : ℕ → ℕ) (κ V : ℝ) (X n : ℕ) : ℝ :=
  ((τ n : ℝ) - κ * log n) / sqrt (V * log X)

end CollatzCLT
