-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
import Mathlib.Algebra.Order.Archimedean.Real.Hom

section
section
section
/-! Facade for the differentiated lifted coarse-flux reconstruction:
`cycle_residual_coarse_flux_differentiated_of_lift` derives
`CoarseFluxDiff.Statement` (the verbatim statement of
`Providers.cycle_residual_coarse_flux_differentiated`) from the lift grading and structure
statements for every order `r`. -/
end

section
/-! Facade for the differentiated tail residual estimate: the statement `TailDiff.Statement` and
its proof `TailDiff.statement_holds`. -/
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Helpers for the presentation of the lifted coarse flux divergence:
the degree-zero lift is the identity at grade
zero and vanishes at positive grade, and the slow dilation chain rule. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- A degree-zero action only reads the value of the coarse field. -/
theorem liftApply_zero_eq_const (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (X z : Vec 2) :
    liftApply 0 c a t X z = liftApply 0 c (fun _ _ => a t X) t X z := by
  funext v
  simp [liftApply, orderedDerivative_zero]

variable [∀ i, FiniteDimensional ℝ (h i)]

/-- The degree-zero lift: identity at grade zero, zero at positive grade. -/
theorem IsLiftSequence.liftApply_zero {D : ℕ} {Q : LiftOperatorData ι h D} {sX sZ : ℕ}
    {t₀ t₁ : ℝ} {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {hh : ℕ} (hhH : hh ≤ H)
    (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) (X z : Vec 2) :
    liftApply 0 (Cc hh 0) a t X z = if hh = 0 then a t X else 0 := by
  rw [liftApply_zero_eq_const]
  split_ifs with hh0
  · subst hh0
    exact hseq.1 (fun _ => a t X) contDiff_const t ht X z
  · funext v
    simp [liftApply, hseq.2.1 hh (Nat.one_le_iff_ne_zero.2 hh0) hhH]

/-- The slow dilation chain rule for a coordinate derivative. -/
theorem fderiv_comp_smul_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Vec 2 → E} (ρ : ℝ) {X : Vec 2} (hg : DifferentiableAt ℝ g (ρ • X)) (v : Vec 2) :
    fderiv ℝ (fun X' => g (ρ • X')) X v = ρ • fderiv ℝ g (ρ • X) v := by
  have hl : HasFDerivAt (fun X' : Vec 2 => ρ • X') (ρ • ContinuousLinearMap.id ℝ (Vec 2)) X :=
    (ContinuousLinearMap.id ℝ (Vec 2)).hasFDerivAt.const_smul ρ
  have hc : HasFDerivAt (fun X' => g (ρ • X'))
      ((fderiv ℝ g (ρ • X)).comp (ρ • ContinuousLinearMap.id ℝ (Vec 2))) X :=
    hg.hasFDerivAt.comp X hl
  rw [hc.fderiv]
  simp

end AVRegularity
end
end
end

section
/-! Facade for the mixed slow/fast tail jets: fast derivatives of a lift action fall on the
coefficients (`Fibre`), and the mixed cell jets are bounded by the energy jets of `fieldEnergyNorm`
(`Energy`). -/
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The statements of `cycle_lift_grading` and `cycle_lift_structure`, copied verbatim as
propositions, so that residual results can be stated conditionally on them. The proofs of the two
theorems have exactly these types. -/

/-- The statement of `cycle_lift_grading` (verbatim). -/
def CycleLiftGradingStatement (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ m, 1 ≤ m → m ≤ n → ∀ j, j ≤ K →
          schurEnergyJet π (Set.Icc t₀ t₁) k j (Cc hh n m)
              ≤ ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - m + j)) ∧
          schurWienerJet π (Set.Icc t₀ t₁) L j (Cc hh n m)
              ≤ ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - m + j))

/-- The statement of `cycle_lift_structure` (verbatim). -/
def CycleLiftStructureStatement (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : Prop :=
  ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        (∀ c0 : ∀ i, h i, ∀ hh, hh ≤ H → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
          (∀ n, 1 ≤ n → n ≤ N → liftApply n (Cc hh n) (fun _ _ => c0) t X z = 0) ∧
          (∀ n, 2 ≤ n → n ≤ N + D → liftMean Q Cc (fun _ _ => c0) hh n t X = 0)) ∧
        (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ hh, hh ≤ H →
          ∀ t ∈ Set.Icc t₀ t₁, ∀ X, liftMean Q Cc (fun _ => a₀) hh 1 t X = 0)

end AVRegularity
end
end
