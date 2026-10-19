-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
public import AVRegularity.Statements.Intermediate.CycleComparison.ResidualNorm

/-! The statement of `Providers.cycle_residual_partition_differentiated` (restated verbatim rather
than imported), and the quiet-gap decay statement of the lift recursion. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.QuietDecay

/-- The statement of `Providers.cycle_residual_partition_differentiated`, verbatim. -/
def Statement (Acl N D H kl Ll : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : Prop :=
  1 ≤ Acl →
  ∀ r : ℕ, ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
      (Q : LiftOperatorData ι h D) (π : ι → ℝ)
      (t₀ t₁ e ν B ρ rs E ℓ dstar εc lam : ℝ)
      (_hrs : 0 < rs) (_hrse : rs ≤ e) (_heρ : e ≤ ρ)
      (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ) (b : ι → ι → ℝ) (Θ : ℝ) (kres s0 : ℕ),
      kres = 4 * (N + D) + 2 * Acl + 16 → s0 = Acl + 2 →
      IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V
        H N (s0 + r + D * (H + 1) * N) (kl + r + D * (H + 1) * N)
        (Ll + r + D * (H + 1) * N) qs qf CG Cw Cj b Θ →
      (∃ M : ℕ, e⁻¹ = (M : ℝ)) →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
      IsLiftSequenceFrom Q (s0 + r + D * (H + 1) * N + D + 2)
        (max (kl + r + D * (H + 1) * N + 1) (Ll + r + D * (H + 1) * N + 2))
        t₀ t₁ N H Cc →
      ∀ g d : ℝ, 0 < d → ℓ ^ 2 * t₀ ≤ g → g + d ≤ ℓ ^ 2 * t₁ →
      IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z)
        (Set.Icc (g / ℓ ^ 2) ((g + d) / ℓ ^ 2)) →
      ∀ I : ℕ → ℝ,
      HasQuietEntranceTrace π Cc (g / ℓ ^ 2) lam N H
        (s0 + r + D * (H + 1) * N) (max (kl + r) (Ll + r + 2) + D * (H + 1) * N) I →
      ∀ (ψ : ℝ → ℝ) (M δ : ℝ), 0 ≤ δ → δ ≤ d →
      (∀ t, |ψ t| ≤ M) → Function.support ψ ⊆ Set.Icc (g + δ) (g + d) →
      ∀ hh, hh ≤ H → ∀ a : ℝ → Vec 2 → ∀ i, h i,
      (∀ t, ContDiff ℝ ((kres + r + 1 : ℕ) : ℕ∞) (a t)) →
      (∀ t, AVenhance.IsZ2Periodic (a t)) →
      ∀ j : ℕ, j ≤ r → ∀ β : DerivativeWord2 j,
        residualNorm ν π (Set.Icc g (g + d)) (fun _ _ _ => 0)
          (fun t x => rs ^ j • orderedDerivative β
            (transitionSourceField N hh ℓ ρ e εc ψ Cc a t) x)
        ≤ ENNReal.ofReal
            (C * (∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) *
              M * ℓ * Real.sqrt d * Real.exp (-(c * δ / ℓ ^ 2))) *
          classicalStrongEnergy ρ B π (Set.Icc g (g + d)) (kres + r) a

/-- The quiet-gap decay without the slow scale factor `λ^p` (implied by the decay with that
factor, since `λ ≤ 1`; this is the form used for `Statement`). With the reserve
`R = D(H+1)N`, `J₀ = max k₀ (L₀+2)`: under `IsLiftSetting` at the raised orders
`(K₀+R, k₀+R, L₀+R)` and the lift recursion from its own entrance trace at the raised box orders,
on a quiet interval `[s, s+T]` of the window, the mixed Schur jets (slow order `p ≤ K₀`, fast order
`q ≤ J₀`) of the positive-degree grade-`hh` coefficients at every time `τ` of the interval are at
most `C A_hh e^{-c(τ-s)}`, with `A_hh = ∑_{b ≤ hh} Θ^{hh-b} I_b` and `I_b` the entrance traces
at `s` through `(K₀+R, J₀+R)`. The constants `C ≥ 0`, `c > 0` depend only on the finite orders and
the normalized coefficient bounds. -/
def DecayStatementU (N D H K₀ k₀ L₀ : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : Prop :=
  ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
      (Q : LiftOperatorData ι h D) (π : ι → ℝ)
      (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ)
      (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ) (b : ι → ι → ℝ) (Θ : ℝ),
      IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V
        H N (K₀ + D * (H + 1) * N) (k₀ + D * (H + 1) * N) (L₀ + D * (H + 1) * N)
        qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
      IsLiftSequenceFrom Q (K₀ + D * (H + 1) * N + D + 2)
        (max (k₀ + D * (H + 1) * N + 1) (L₀ + D * (H + 1) * N + 2)) t₀ t₁ N H Cc →
      ∀ s T : ℝ, 0 < T → t₀ ≤ s → s + T ≤ t₁ →
      IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z) (Set.Icc s (s + T)) →
      ∀ I : ℕ → ℝ,
      HasQuietEntranceTrace π Cc s lam N H (K₀ + D * (H + 1) * N)
        (max k₀ (L₀ + 2) + D * (H + 1) * N) I →
      ∀ hh, hh ≤ H → ∀ τ ∈ Set.Icc s (s + T), ∀ p, p ≤ K₀ → ∀ q, q ≤ max k₀ (L₀ + 2) →
        ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.range (n + 1),
            schurMixedCellL2Jet π {τ} p q (Cc hh n m)
          ≤ ENNReal.ofReal (C * (∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) *
            Real.exp (-(c * (τ - s))))

universe u v

end AVRegularity.QuietDecay
