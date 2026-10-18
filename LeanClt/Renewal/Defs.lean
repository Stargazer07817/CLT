import LeanClt.Defs

/-!
# §4: definitions

* `ell = log 2`, `bet = log 3`, `θ = log₂ 3`.
* `lawS t A = P(S_t = A)` for `S_t` a sum of `t` iid `Geom(2)` variables on `{1, 2, …}`,
  by the convolution recursion `P(S_{t+1} = A) = ∑_{k<A} 2^{-(k+1)} P(S_t = A-1-k)`
  (the `k`-th term is the last letter equal to `k+1`).
* the Gaussian approximation of Lemma 2.2(iii), Rhin's measure as a hypothesis, `Z_t`, and the
  twisted renewal kernel `R^{ρ,η}_s(u)` of (4.2).
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-- `ℓ = log 2`. -/
def ell : ℝ := Real.log 2

/-- `β = log 3`. -/
def bet : ℝ := Real.log 3

/-- `θ = log₂ 3 = β / ℓ`. -/
def θ : ℝ := Real.log 3 / Real.log 2

/-- `lawS t A = P(S_t = A)`, the law of a sum of `t` iid `Geom(2)` variables on `{1, 2, …}`,
by convolution. -/
def lawS : ℕ → ℕ → ℝ
  | 0, A => if A = 0 then 1 else 0
  | t + 1, A => ∑ k ∈ range A, (1 / 2 : ℝ) ^ (k + 1) * lawS t (A - 1 - k)

/-- The Gaussian approximation `(4πn)^{-1/2} exp(-(A-2n)²/(4n))` of Lemma 2.2(iii). -/
def gaussApprox (n A : ℕ) : ℝ :=
  (4 * π * n)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-((A : ℝ) - 2 * n) ^ 2 / (4 * n))

/-- `‖x‖_{ℝ/ℤ}`, the distance to the nearest integer. -/
def distZ (x : ℝ) : ℝ := |x - round x|

/-- **Rhin's irrationality measure (2.8, `eq:rhin`)**, as a hypothesis: constants `0 < d` and
`1 ≤ ϰ` with `‖h log₂3‖ ≥ d h^{-ϰ}` for all integers `h ≥ 1`. -/
def IrrMeasure (d ϰ : ℝ) : Prop :=
  0 < d ∧ 1 ≤ ϰ ∧ ∀ h : ℕ, 1 ≤ h → d * (h : ℝ) ^ (-ϰ) ≤ distZ (h * θ)

/-- `Z_t = ℓ S_t - β t` (4.1, `eq:Z`) evaluated at `S_t = A`. -/
def Zval (t A : ℕ) : ℝ := ell * A - bet * t

/-- **The twisted renewal kernel (4.2, `eq:R`)**
`R^{ρ,η}_s(u) = ∑_{t≥0} E[e^{Z_t - u} e^{-is(ρ S_t + η t)} 1{0 ≤ Z_t - u ≤ ℓ}]`,
with the expectation written against the law of `S_t` (both endpoints included). -/
def renewalR (ρ η s u : ℝ) : ℂ :=
  ∑' t : ℕ, ∑' A : ℕ,
    if 0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell then
      (lawS t A : ℂ) * (Real.exp (Zval t A - u) : ℂ) * cexp (-(((s * (ρ * A + η * t)) : ℝ) : ℂ) * I)
    else 0

end CollatzCLT
