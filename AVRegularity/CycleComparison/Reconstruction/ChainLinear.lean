-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Assembly.BillBound
public import AVRegularity.Statements.Intermediate.CycleOutput.GluedMean
public import AVRegularity.CycleComparison.Lift.LeftTermsFieldPostcomposition
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
import AVRegularity.Analysis.Convolution
import AVRegularity.CycleComparison.Residual.ChainProject
import AVRegularity.CycleComparison.Residual.TailJets
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.CleanupChain.DataMap
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Reconstruction

/-! The two-scale sampling of the cell operators at a fixed time.

For a box field `Φ(X,z)` its sample at the scales `ρ, e` is `(SΦ)(y) = Φ(ρ⁻¹y, e⁻¹y)`. Then:

1. `∂_j SΦ = S(ρ⁻¹ ∂_{X_j}Φ + e⁻¹ ∂_{z_j}Φ)`;
2. for a slow metric `G(X)`, `div_y(G(ρ⁻¹y) ∇_y SΦ)` is the sample of
   `e⁻² G:∇_z²Φ + e⁻¹ρ⁻¹ {G ∂_z∂_X Φ + ∂_X(G ∂_zΦ)} + ρ⁻² ∂_X(G ∂_XΦ)` (the bracket shapes of
   `cellOperator`, `cellB1`, `cellB2`);
3. for a fast drift `w(z)`, `w(e⁻¹y)·∇_y SΦ = S(ρ⁻¹ w·∇_XΦ + e⁻¹ w·∇_zΦ)`;
4. with `v = c₁ w`, `ℓ² ν e⁻² = 1`, `ε_c √η = ℓ² ν e⁻¹ ρ⁻¹`, `ε_c² η = ℓ² ν ρ⁻²`, `c₁ = ℓ² e⁻¹`,
   the sample of `𝒫₀-part + ε_c ℬ₁ + ε_c² ℬ₂` is `ℓ² (w·∇_y − ν div_y(G∇_y))` applied to `SΦ`.

For the actual scales `ℓ² = e²/ν`, `η = ν/B`, `ε_c = d_*/ρ`, `d_* = e√(B/ν)`: `√η ε_c = e/ρ`, and
`c₁ = ℓ²/e` is the factor of `ocPulseCellDrift`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The diagonal sample `y ↦ Φ(ρ⁻¹y, e⁻¹y)` of a two-scale field. -/
def twoScaleSample (ρ e : ℝ) (Φ : Vec 2 → Vec 2 → E) (y : Vec 2) : E :=
  Φ (ρ⁻¹ • y) (e⁻¹ • y)

/-- `∑_{ij} G_{ij} ∂_{z_i}∂_{z_j} Φ`. -/
def metricFF (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (Φ : Vec 2 → Vec 2 → E) (X z : Vec 2) : E :=
  ∑ i, ∑ j, G X i j • fastPartial i (fastPartial j Φ) X z

/-- `∑_{ij} (G_{ij} ∂_{z_i}∂_{X_j} Φ + ∂_{X_i}(G_{ij} ∂_{z_j} Φ))`. -/
def metricFS (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (Φ : Vec 2 → Vec 2 → E) (X z : Vec 2) : E :=
  ∑ i, ∑ j, (G X i j • fastPartial i (slowPartial j Φ) X z
    + slowPartial i (fun X' z' => G X' i j • fastPartial j Φ X' z') X z)

/-- `∑_{ij} ∂_{X_i}(G_{ij} ∂_{X_j} Φ)`. -/
def metricSS (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (Φ : Vec 2 → Vec 2 → E) (X z : Vec 2) : E :=
  ∑ i, ∑ j, slowPartial i (fun X' z' => G X' i j • slowPartial j Φ X' z') X z

section Sample

variable {Φ : Vec 2 → Vec 2 → E} {sX sZ : ℕ}

/-- The sample of a box field of orders at least one is differentiable. -/
theorem sample_differentiableAt (hΦ : IsBoxSmooth sX sZ Φ) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ)
    (ρ e : ℝ) (y : Vec 2) : DifferentiableAt ℝ (twoScaleSample ρ e Φ) y := by
  have hg : DifferentiableAt ℝ (fun x' : Vec 2 => (ρ⁻¹ • x', e⁻¹ • x')) y := by fun_prop
  exact (hΦ.hasFDerivAt_uncurry hX hZ _).differentiableAt.comp y hg

/-- **Two-scale chain rule.** `∂_j SΦ = ρ⁻¹ (∂_{X_j}Φ)_diag + e⁻¹ (∂_{z_j}Φ)_diag`. -/
theorem sample_fderiv (hΦ : IsBoxSmooth sX sZ Φ) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) (ρ e : ℝ)
    (y : Vec 2) (j : Fin 2) :
    fderiv ℝ (twoScaleSample ρ e Φ) y (basisVec j) =
      ρ⁻¹ • slowPartial j Φ (ρ⁻¹ • y) (e⁻¹ • y) + e⁻¹ • fastPartial j Φ (ρ⁻¹ • y) (e⁻¹ • y) :=
  hΦ.fderiv_diag hX hZ ρ e y (basisVec j)

/-- The chain rule as an identity of functions of `y`. -/
theorem sample_fderiv_fun (hΦ : IsBoxSmooth sX sZ Φ) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) (ρ e : ℝ)
    (j : Fin 2) :
    (fun y => fderiv ℝ (twoScaleSample ρ e Φ) y (basisVec j)) =
      fun y => ρ⁻¹ • twoScaleSample ρ e (slowPartial j Φ) y
        + e⁻¹ • twoScaleSample ρ e (fastPartial j Φ) y :=
  funext fun y => sample_fderiv hΦ hX hZ ρ e y j

/-- **Second derivatives of the sample.** -/
theorem sample_fderiv_fderiv (hΦ : IsBoxSmooth 2 2 Φ) (ρ e : ℝ) (y : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun y' => fderiv ℝ (twoScaleSample ρ e Φ) y' (basisVec j)) y (basisVec i) =
      ρ⁻¹ • (ρ⁻¹ • slowPartial i (slowPartial j Φ) (ρ⁻¹ • y) (e⁻¹ • y)
          + e⁻¹ • fastPartial i (slowPartial j Φ) (ρ⁻¹ • y) (e⁻¹ • y))
        + e⁻¹ • (ρ⁻¹ • slowPartial i (fastPartial j Φ) (ρ⁻¹ • y) (e⁻¹ • y)
          + e⁻¹ • fastPartial i (fastPartial j Φ) (ρ⁻¹ • y) (e⁻¹ • y)) := by
  have h11 : IsBoxSmooth (1 + 1) (1 + 1) Φ := hΦ
  have hS : IsBoxSmooth 1 1 (slowPartial j Φ) := (h11.slowPartial j).mono le_rfl (by norm_num)
  have hF : IsBoxSmooth 1 1 (fastPartial j Φ) := (h11.fastPartial j).mono (by norm_num) le_rfl
  have hdS := sample_differentiableAt hS le_rfl le_rfl ρ e y
  have hdF := sample_differentiableAt hF le_rfl le_rfl ρ e y
  have h1 : DifferentiableAt ℝ (fun y' => ρ⁻¹ • twoScaleSample ρ e (slowPartial j Φ) y') y :=
    hdS.const_smul ρ⁻¹
  have h2 : DifferentiableAt ℝ (fun y' => e⁻¹ • twoScaleSample ρ e (fastPartial j Φ) y') y :=
    hdF.const_smul e⁻¹
  rw [sample_fderiv_fun hΦ (by norm_num) (by norm_num) ρ e j, fderiv_fun_add h1 h2,
    fderiv_fun_const_smul hdS ρ⁻¹, fderiv_fun_const_smul hdF e⁻¹,
    add_apply, smul_apply,
    smul_apply, sample_fderiv hS le_rfl le_rfl ρ e y i,
    sample_fderiv hF le_rfl le_rfl ρ e y i]

end Sample

section Coefficients

/-- The derivative of a slow coefficient read at `ρ⁻¹y`. -/
theorem slowCoeff_hasFDerivAt {g : Vec 2 → ℝ} (ρ : ℝ) (y : Vec 2)
    (hg : DifferentiableAt ℝ g (ρ⁻¹ • y)) :
    HasFDerivAt (fun y' => g (ρ⁻¹ • y'))
      ((fderiv ℝ g (ρ⁻¹ • y)).comp (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 2))) y := by
  have hl : HasFDerivAt (fun y' : Vec 2 => ρ⁻¹ • y') (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)) y :=
    (ContinuousLinearMap.id ℝ (Vec 2)).hasFDerivAt.const_smul ρ⁻¹
  exact hg.hasFDerivAt.comp y hl

/-- `∂_v [g(ρ⁻¹ y)] = ρ⁻¹ (∂_v g)(ρ⁻¹ y)`. -/
theorem slowCoeff_fderiv {g : Vec 2 → ℝ} (ρ : ℝ) (y : Vec 2)
    (hg : DifferentiableAt ℝ g (ρ⁻¹ • y)) (v : Vec 2) :
    fderiv ℝ (fun y' => g (ρ⁻¹ • y')) y v = ρ⁻¹ * fderiv ℝ g (ρ⁻¹ • y) v := by
  rw [(slowCoeff_hasFDerivAt ρ y hg).fderiv, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- Product rule for the slow partial of a slow scalar times a field. -/
theorem slowPartial_slowScalar_smul {g : Vec 2 → ℝ} {F : Vec 2 → Vec 2 → E} (i : Fin 2)
    (X z : Vec 2) (hg : DifferentiableAt ℝ g X)
    (hF : DifferentiableAt ℝ (fun X' => F X' z) X) :
    slowPartial i (fun X' z' => g X' • F X' z') X z =
      g X • slowPartial i F X z + fderiv ℝ g X (basisVec i) • F X z := by
  simp only [slowPartial]
  rw [fderiv_fun_smul hg hF]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]

end Coefficients

section Operators

variable {Φ : Vec 2 → Vec 2 → E}

/-- **Sampled divergence form.** For a slow differentiable metric `G`,
`div_y(G(ρ⁻¹y) ∇_y SΦ)` is the sample of
`e⁻² G:∇_z²Φ + e⁻¹ρ⁻¹ {G ∂_z∂_X Φ + ∂_X(G ∂_zΦ)} + ρ⁻² ∂_X(G ∂_XΦ)`. -/
theorem sample_div_metric (hΦ : IsBoxSmooth 2 2 Φ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ)
    (hG : ∀ i j, Differentiable ℝ (fun X => G X i j)) (ρ e : ℝ) (y : Vec 2) :
    ∑ i, fderiv ℝ (fun y' => ∑ j, G (ρ⁻¹ • y') i j •
        fderiv ℝ (twoScaleSample ρ e Φ) y' (basisVec j)) y (basisVec i) =
      (e⁻¹ * e⁻¹) • (∑ i, ∑ j, G (ρ⁻¹ • y) i j •
          fastPartial i (fastPartial j Φ) (ρ⁻¹ • y) (e⁻¹ • y))
        + (e⁻¹ * ρ⁻¹) • (∑ i, ∑ j, (G (ρ⁻¹ • y) i j •
            fastPartial i (slowPartial j Φ) (ρ⁻¹ • y) (e⁻¹ • y)
          + slowPartial i (fun X' z' => G X' i j • fastPartial j Φ X' z') (ρ⁻¹ • y) (e⁻¹ • y)))
        + (ρ⁻¹ * ρ⁻¹) • (∑ i, ∑ j,
            slowPartial i (fun X' z' => G X' i j • slowPartial j Φ X' z') (ρ⁻¹ • y) (e⁻¹ • y)) := by
  have h11 : IsBoxSmooth (1 + 1) (1 + 1) Φ := hΦ
  have hS : ∀ j, IsBoxSmooth 1 1 (slowPartial j Φ) := fun j =>
    (h11.slowPartial j).mono le_rfl (by norm_num)
  have hF : ∀ j, IsBoxSmooth 1 1 (fastPartial j Φ) := fun j =>
    (h11.fastPartial j).mono (by norm_num) le_rfl
  have hc : ∀ i j, DifferentiableAt ℝ (fun y' => G (ρ⁻¹ • y') i j) y := fun i j =>
    (slowCoeff_hasFDerivAt ρ y ((hG i j) (ρ⁻¹ • y))).differentiableAt
  have hD : ∀ j, DifferentiableAt ℝ
      (fun y' => fderiv ℝ (twoScaleSample ρ e Φ) y' (basisVec j)) y := fun j => by
    rw [sample_fderiv_fun hΦ (by norm_num) (by norm_num) ρ e j]
    exact ((sample_differentiableAt (hS j) le_rfl le_rfl ρ e y).const_smul ρ⁻¹).add
      ((sample_differentiableAt (hF j) le_rfl le_rfl ρ e y).const_smul e⁻¹)
  have hterm : ∀ i j, fderiv ℝ (fun y' => G (ρ⁻¹ • y') i j •
      fderiv ℝ (twoScaleSample ρ e Φ) y' (basisVec j)) y (basisVec i) =
      G (ρ⁻¹ • y) i j • (ρ⁻¹ • (ρ⁻¹ • slowPartial i (slowPartial j Φ) (ρ⁻¹ • y) (e⁻¹ • y)
          + e⁻¹ • fastPartial i (slowPartial j Φ) (ρ⁻¹ • y) (e⁻¹ • y))
        + e⁻¹ • (ρ⁻¹ • slowPartial i (fastPartial j Φ) (ρ⁻¹ • y) (e⁻¹ • y)
          + e⁻¹ • fastPartial i (fastPartial j Φ) (ρ⁻¹ • y) (e⁻¹ • y)))
      + (ρ⁻¹ * fderiv ℝ (fun X => G X i j) (ρ⁻¹ • y) (basisVec i)) •
        (ρ⁻¹ • slowPartial j Φ (ρ⁻¹ • y) (e⁻¹ • y)
          + e⁻¹ • fastPartial j Φ (ρ⁻¹ • y) (e⁻¹ • y)) := by
    intro i j
    rw [fderiv_fun_smul (hc i j) (hD j), add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply,
      sample_fderiv_fderiv hΦ ρ e y i j, slowCoeff_fderiv ρ y ((hG i j) (ρ⁻¹ • y)) (basisVec i),
      sample_fderiv hΦ (by norm_num) (by norm_num) ρ e y j]
  have hsum : ∀ i, fderiv ℝ (fun y' => ∑ j, G (ρ⁻¹ • y') i j •
      fderiv ℝ (twoScaleSample ρ e Φ) y' (basisVec j)) y (basisVec i) =
      ∑ j, fderiv ℝ (fun y' => G (ρ⁻¹ • y') i j •
        fderiv ℝ (twoScaleSample ρ e Φ) y' (basisVec j)) y (basisVec i) := by
    intro i
    have hd : ∀ j ∈ (Finset.univ : Finset (Fin 2)), DifferentiableAt ℝ
        (fun y' => G (ρ⁻¹ • y') i j • fderiv ℝ (twoScaleSample ρ e Φ) y' (basisVec j)) y :=
      fun j _ => (hc i j).smul (hD j)
    rw [fderiv_fun_sum hd, sum_apply]
  have hprodS : ∀ i j, slowPartial i (fun X' z' => G X' i j • slowPartial j Φ X' z')
      (ρ⁻¹ • y) (e⁻¹ • y) =
      G (ρ⁻¹ • y) i j • slowPartial i (slowPartial j Φ) (ρ⁻¹ • y) (e⁻¹ • y)
        + fderiv ℝ (fun X => G X i j) (ρ⁻¹ • y) (basisVec i) •
          slowPartial j Φ (ρ⁻¹ • y) (e⁻¹ • y) := fun i j =>
    slowPartial_slowScalar_smul i _ _ ((hG i j) _)
      (((hS j).contDiff_slow _).differentiable (by norm_num) _)
  have hprodF : ∀ i j, slowPartial i (fun X' z' => G X' i j • fastPartial j Φ X' z')
      (ρ⁻¹ • y) (e⁻¹ • y) =
      G (ρ⁻¹ • y) i j • slowPartial i (fastPartial j Φ) (ρ⁻¹ • y) (e⁻¹ • y)
        + fderiv ℝ (fun X => G X i j) (ρ⁻¹ • y) (basisVec i) •
          fastPartial j Φ (ρ⁻¹ • y) (e⁻¹ • y) := fun i j =>
    slowPartial_slowScalar_smul i _ _ ((hG i j) _)
      (((hF j).contDiff_slow _).differentiable (by norm_num) _)
  refine (Finset.sum_congr rfl fun i _ => (hsum i).trans
    (Finset.sum_congr rfl fun j _ => hterm i j)).trans ?_
  rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hprodF i j, hprodS i j]
  module

/-- **Sampled fast drift.** `w(e⁻¹y)·∇_y SΦ = S(ρ⁻¹ w·∇_XΦ + e⁻¹ w·∇_zΦ)`. -/
theorem sample_fast_drift {sX sZ : ℕ} (hΦ : IsBoxSmooth sX sZ Φ) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ)
    (w : Vec 2 → Vec 2) (ρ e : ℝ) (y : Vec 2) :
    ∑ k, w (e⁻¹ • y) k • fderiv ℝ (twoScaleSample ρ e Φ) y (basisVec k) =
      twoScaleSample ρ e (fun X z => ρ⁻¹ • ∑ k, w z k • slowPartial k Φ X z
        + e⁻¹ • ∑ k, w z k • fastPartial k Φ X z) y := by
  show _ = ρ⁻¹ • ∑ k, w (e⁻¹ • y) k • slowPartial k Φ (ρ⁻¹ • y) (e⁻¹ • y)
    + e⁻¹ • ∑ k, w (e⁻¹ • y) k • fastPartial k Φ (ρ⁻¹ • y) (e⁻¹ • y)
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sample_fderiv hΦ hX hZ ρ e y k]
  module

/-- The scalar bookkeeping of the cell scaling: with `ℓ² ν e⁻² = 1`, `ε_c √η = ℓ² ν e⁻¹ρ⁻¹`,
`ε_c² η = ℓ² ν ρ⁻²` and `c₁ = ℓ² e⁻¹`, the cell combination equals the scaled physical one. -/
theorem cell_scaling_algebra (Wf Ws AA BB CC : E) {η εc ρ e ℓsq ν c₁ : ℝ}
    (h1 : ℓsq * ν * e⁻¹ * e⁻¹ = 1) (h2 : εc * Real.sqrt η = ℓsq * ν * e⁻¹ * ρ⁻¹)
    (h3 : εc ^ 2 * η = ℓsq * ν * ρ⁻¹ * ρ⁻¹) (hc : c₁ = ℓsq * e⁻¹) :
    (c₁ • Wf - AA) + εc • ((Real.sqrt η * c₁) • Ws - Real.sqrt η • BB) + εc ^ 2 • -(η • CC) =
      ℓsq • ((ρ⁻¹ • Ws + e⁻¹ • Wf) -
        ν • ((e⁻¹ * e⁻¹) • AA + (e⁻¹ * ρ⁻¹) • BB + (ρ⁻¹ * ρ⁻¹) • CC)) := by
  have h4 : εc * Real.sqrt η * c₁ = ℓsq * ρ⁻¹ := by
    rw [hc]
    linear_combination (ℓsq * e⁻¹) * h2 + (ℓsq * ρ⁻¹) * h1
  calc (c₁ • Wf - AA) + εc • ((Real.sqrt η * c₁) • Ws - Real.sqrt η • BB) + εc ^ 2 • -(η • CC)
      = c₁ • Wf + (εc * Real.sqrt η * c₁) • Ws - (1 : ℝ) • AA - (εc * Real.sqrt η) • BB
          - (εc ^ 2 * η) • CC := by module
    _ = (ℓsq * e⁻¹) • Wf + (ℓsq * ρ⁻¹) • Ws - (ℓsq * ν * e⁻¹ * e⁻¹) • AA
          - (ℓsq * ν * e⁻¹ * ρ⁻¹) • BB - (ℓsq * ν * ρ⁻¹ * ρ⁻¹) • CC := by
        rw [h4, h1, h2, h3, hc]
    _ = ℓsq • ((ρ⁻¹ • Ws + e⁻¹ • Wf) -
          ν • ((e⁻¹ * e⁻¹) • AA + (e⁻¹ * ρ⁻¹) • BB + (ρ⁻¹ * ρ⁻¹) • CC)) := by module

/-- **Sampled cell operators.** At a fixed time `t`, for the drift `v t = c₁ w` and the slow metric
`G' t`, the sample of `cellOperator + ε_c ℬ₁ + ε_c² ℬ₂` applied to `Φ` is `ℓ²` times the physical
operator `w(e⁻¹y)·∇_y − ν div_y(G'(t, ρ⁻¹y) ∇_y)` applied to the sample `SΦ`. -/
theorem sample_cell_operators (hΦ : IsBoxSmooth 2 2 Φ) (G' : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (hG : ∀ i j, Differentiable ℝ (fun X => G' t X i j))
    (w : Vec 2 → Vec 2) {η εc ρ e ℓsq ν c₁ : ℝ} (hv : ∀ z, v t z = c₁ • w z)
    (h1 : ℓsq * ν * e⁻¹ * e⁻¹ = 1) (h2 : εc * Real.sqrt η = ℓsq * ν * e⁻¹ * ρ⁻¹)
    (h3 : εc ^ 2 * η = ℓsq * ν * ρ⁻¹ * ρ⁻¹) (hc : c₁ = ℓsq * e⁻¹) (y : Vec 2) :
    twoScaleSample ρ e (fun X z => cellOperator (G' t X) (v t) (Φ X) z
        + εc • cellB1 η G' v t Φ X z + εc ^ 2 • cellB2 η G' t Φ X z) y =
      ℓsq • (∑ k, w (e⁻¹ • y) k • fderiv ℝ (twoScaleSample ρ e Φ) y (basisVec k)
        - ν • ∑ i, fderiv ℝ (fun y' => ∑ j, G' t (ρ⁻¹ • y') i j •
            fderiv ℝ (twoScaleSample ρ e Φ) y' (basisVec j)) y (basisVec i)) := by
  rw [sample_fast_drift hΦ (by norm_num) (by norm_num) w ρ e y,
    sample_div_metric hΦ (G' t) hG ρ e y]
  have hfast : ∑ k, v t (e⁻¹ • y) k • fastPartial k Φ (ρ⁻¹ • y) (e⁻¹ • y) =
      c₁ • ∑ k, w (e⁻¹ • y) k • fastPartial k Φ (ρ⁻¹ • y) (e⁻¹ • y) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hv, Pi.smul_apply, smul_eq_mul]
    module
  have hslow : ∑ k, (Real.sqrt η * v t (e⁻¹ • y) k) • slowPartial k Φ (ρ⁻¹ • y) (e⁻¹ • y) =
      (Real.sqrt η * c₁) • ∑ k, w (e⁻¹ • y) k • slowPartial k Φ (ρ⁻¹ • y) (e⁻¹ • y) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hv, Pi.smul_apply, smul_eq_mul]
    module
  show (∑ k, v t (e⁻¹ • y) k • fastPartial k Φ (ρ⁻¹ • y) (e⁻¹ • y)
        - metricFF (G' t) Φ (ρ⁻¹ • y) (e⁻¹ • y))
      + εc • ((∑ k, (Real.sqrt η * v t (e⁻¹ • y) k) • slowPartial k Φ (ρ⁻¹ • y) (e⁻¹ • y))
        - Real.sqrt η • metricFS (G' t) Φ (ρ⁻¹ • y) (e⁻¹ • y))
      + εc ^ 2 • -(η • metricSS (G' t) Φ (ρ⁻¹ • y) (e⁻¹ • y))
    = ℓsq • ((ρ⁻¹ • ∑ k, w (e⁻¹ • y) k • slowPartial k Φ (ρ⁻¹ • y) (e⁻¹ • y)
        + e⁻¹ • ∑ k, w (e⁻¹ • y) k • fastPartial k Φ (ρ⁻¹ • y) (e⁻¹ • y))
      - ν • ((e⁻¹ * e⁻¹) • metricFF (G' t) Φ (ρ⁻¹ • y) (e⁻¹ • y)
        + (e⁻¹ * ρ⁻¹) • metricFS (G' t) Φ (ρ⁻¹ • y) (e⁻¹ • y)
        + (ρ⁻¹ * ρ⁻¹) • metricSS (G' t) Φ (ρ⁻¹ • y) (e⁻¹ • y)))
  rw [hfast, hslow]
  exact cell_scaling_algebra _ _ _ _ _ h1 h2 h3 hc

end Operators

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Bill bookkeeping of the physical reconstruction: scale identities and the terms of the
bill**.

* Scale identities, for abstract reals with `e = ℓ√ν`, `d = ℓ√B` (`d_* = ℓ√B`, `e = ℓ√ν`):
  the flux of the tail `ν⁻¹ (ℓ⁻² (d/ρ)^{N+1} e ρ S)² B⁻¹E² = (d/ρ)^{2N} S² E²`
  (`flux_tail_scale`), of the coarse flux `ν⁻¹ c B Y² = c (B/ν) Y²`, of
  the lifted coarse flux `ν⁻¹ (e/ρ)²(d/ρ)²θ² B Y² = (d/ρ)⁴ θ² Y²` (`flux_lift_scale`), and the
  forces `√(ℓ⁻² (d/ρ)^{N+1} (e/ρ)^A ρ S)² √T B^{-1/2} E = (d/ρ)^N Z S E` (`force_tail_scale`),
  `√((ρ⁻¹(e/ρ)^A)² (d/ρ)² θ²) √T √B Y = (d/ρ)² Z θ Y` (`force_lift_scale`), `Z = (√T/ℓ)(e/ρ)^A`.
* An abstract-real conversion `(√B)⁻¹ √X ≤ Y → X ≤ B Y²` (`sq_le_of_inv_sqrt_mul_sqrt_le`).
* Each of the terms `ε_c^{N'}`, `ε_c^{N'} Z`, `√(B/ν) 𝔱`, `ε_c² 𝔱`, `ε_c² Z 𝔱` and
  `ℓ√(B_p/τ) exp(-cτ/ℓ²)` is at most the bill (`billShape_ge_terms` for the abstract bill,
  `compBill_ge_terms` for `compBill`). -/

section Scales

/-- **The scale of the tail flux.** With `e = ℓ√ν`, `d = ℓ√B`:
`ν⁻¹ (ℓ⁻² (d/ρ)^{N+1} e ρ S)² (E²/B) = (d/ρ)^{2N} S² E²`. -/
theorem flux_tail_scale {ℓ ν B ρ e d S E : ℝ} (N : ℕ) (hℓ : 0 < ℓ) (hν : 0 < ν) (hB : 0 < B)
    (hρ : 0 < ρ) (he : e = ℓ * Real.sqrt ν) (hd : d = ℓ * Real.sqrt B) :
    ν⁻¹ * ((ℓ ^ 2)⁻¹ * (d / ρ) ^ (N + 1) * e * ρ * S) ^ 2 * (E ^ 2 / B) =
      (d / ρ) ^ (2 * N) * S ^ 2 * E ^ 2 := by
  rw [pow_succ (d / ρ) N, pow_mul' (d / ρ) 2 N]
  obtain ⟨w, hw⟩ : ∃ w, (d / ρ) ^ N = w := ⟨_, rfl⟩
  rw [hw]
  subst he hd
  have hℓ2 : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ.ne'
  calc _ = w ^ 2 * S ^ 2 * E ^ 2 * (((ℓ ^ 2)⁻¹ * ℓ ^ 2) ^ 2 * (ρ⁻¹ * ρ) ^ 2 *
        (ν⁻¹ * Real.sqrt ν ^ 2) * (B⁻¹ * Real.sqrt B ^ 2)) := by ring
    _ = w ^ 2 * S ^ 2 * E ^ 2 := by
        rw [Real.sq_sqrt hν.le, Real.sq_sqrt hB.le, inv_mul_cancel₀ hℓ2, inv_mul_cancel₀ hρ.ne',
          inv_mul_cancel₀ hν.ne', inv_mul_cancel₀ hB.ne']
        ring

/-- **The scale of the lifted coarse flux.** With `e = ℓ√ν`, `d = ℓ√B`:
`ν⁻¹ ((e/ρ)² (d/ρ)² θ²) (B Y²) = (d/ρ)⁴ θ² Y²`. -/
theorem flux_lift_scale {ℓ ν B ρ e d θ Y : ℝ} (hν : 0 < ν) (hB : 0 ≤ B)
    (he : e = ℓ * Real.sqrt ν) (hd : d = ℓ * Real.sqrt B) :
    ν⁻¹ * ((e / ρ) ^ 2 * (d / ρ) ^ 2 * θ ^ 2) * (B * Y ^ 2) = (d / ρ) ^ 4 * θ ^ 2 * Y ^ 2 := by
  subst he hd
  calc _ = (ν⁻¹ * Real.sqrt ν ^ 2) *
        ((ℓ * Real.sqrt B / ρ) ^ 2 * (ℓ / ρ) ^ 2 * θ ^ 2 * Y ^ 2 * B) := by ring
    _ = (ℓ * Real.sqrt B / ρ) ^ 2 * (ℓ / ρ) ^ 2 * θ ^ 2 * Y ^ 2 * Real.sqrt B ^ 2 := by
        rw [Real.sq_sqrt hν.le, inv_mul_cancel₀ hν.ne', Real.sq_sqrt hB]
        ring
    _ = (ℓ * Real.sqrt B / ρ) ^ 4 * θ ^ 2 * Y ^ 2 := by ring

/-- **The scale of the tail force.** With `e = ℓ√ν`, `d = ℓ√B` and `S ≥ 0`:
`√((ℓ⁻² (d/ρ)^{N+1} (e/ρ)^A ρ S)²) √T (B^{-1/2} E) = (d/ρ)^N ((√T/ℓ)(e/ρ)^A) S E`. -/
theorem force_tail_scale {ℓ ν B ρ e d S T E : ℝ} (N A : ℕ) (hℓ : 0 < ℓ) (hB : 0 < B)
    (hρ : 0 < ρ) (he : e = ℓ * Real.sqrt ν) (hd : d = ℓ * Real.sqrt B) (hS : 0 ≤ S) :
    Real.sqrt (((ℓ ^ 2)⁻¹ * (d / ρ) ^ (N + 1) * (e / ρ) ^ A * ρ * S) ^ 2) * Real.sqrt T *
        ((Real.sqrt B)⁻¹ * E) =
      (d / ρ) ^ N * (Real.sqrt T / ℓ * (e / ρ) ^ A) * S * E := by
  have hd0 : 0 ≤ d := by
    rw [hd]
    exact mul_nonneg hℓ.le (Real.sqrt_nonneg B)
  have he0 : 0 ≤ e := by
    rw [he]
    exact mul_nonneg hℓ.le (Real.sqrt_nonneg ν)
  rw [pow_succ (d / ρ) N]
  obtain ⟨w, hw⟩ : ∃ w, (d / ρ) ^ N = w := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, (e / ρ) ^ A = z := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by
    rw [← hw]
    exact pow_nonneg (div_nonneg hd0 hρ.le) N
  have hz0 : 0 ≤ z := by
    rw [← hz]
    exact pow_nonneg (div_nonneg he0 hρ.le) A
  rw [hw, hz]
  have hx : 0 ≤ (ℓ ^ 2)⁻¹ * (w * (d / ρ)) * z * ρ * S :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 (sq_nonneg ℓ))
      (mul_nonneg hw0 (div_nonneg hd0 hρ.le))) hz0) hρ.le) hS
  rw [Real.sqrt_sq hx]
  subst hd
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  calc _ = w * (Real.sqrt T / ℓ * z) * S * E *
        (ℓ⁻¹ * ℓ * ((Real.sqrt B)⁻¹ * Real.sqrt B) * (ρ⁻¹ * ρ)) := by ring
    _ = w * (Real.sqrt T / ℓ * z) * S * E := by
        rw [inv_mul_cancel₀ hℓ.ne', inv_mul_cancel₀ hsB.ne', inv_mul_cancel₀ hρ.ne']
        ring

/-- **The scale of the lifted coarse force.** With `e = ℓ√ν`, `d = ℓ√B` and `θ ≥ 0`:
`√((ρ⁻¹ (e/ρ)^A)² (d/ρ)² θ²) √T (√B Y) = (d/ρ)² ((√T/ℓ)(e/ρ)^A) θ Y`. -/
theorem force_lift_scale {ℓ ν B ρ e d θ T Y : ℝ} (A : ℕ) (hℓ : 0 < ℓ) (hρ : 0 ≤ ρ)
    (he : e = ℓ * Real.sqrt ν) (hd : d = ℓ * Real.sqrt B) (hθ : 0 ≤ θ) :
    Real.sqrt ((ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (d / ρ) ^ 2 * θ ^ 2) * Real.sqrt T *
        (Real.sqrt B * Y) =
      (d / ρ) ^ 2 * (Real.sqrt T / ℓ * (e / ρ) ^ A) * θ * Y := by
  have hd0 : 0 ≤ d := by
    rw [hd]
    exact mul_nonneg hℓ.le (Real.sqrt_nonneg B)
  have he0 : 0 ≤ e := by
    rw [he]
    exact mul_nonneg hℓ.le (Real.sqrt_nonneg ν)
  obtain ⟨z, hz⟩ : ∃ z, (e / ρ) ^ A = z := ⟨_, rfl⟩
  have hz0 : 0 ≤ z := by
    rw [← hz]
    exact pow_nonneg (div_nonneg he0 hρ) A
  rw [hz]
  have hx : 0 ≤ ρ⁻¹ * z * (d / ρ) * θ :=
    mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hρ) hz0) (div_nonneg hd0 hρ)) hθ
  have hsq : (ρ⁻¹ * z) ^ 2 * (d / ρ) ^ 2 * θ ^ 2 = (ρ⁻¹ * z * (d / ρ) * θ) ^ 2 := by ring
  rw [hsq, Real.sqrt_sq hx]
  subst hd
  calc _ = ρ⁻¹ * z * (ℓ * Real.sqrt B / ρ) * θ * Real.sqrt T * (Real.sqrt B * Y) *
        (ℓ⁻¹ * ℓ) := by
        rw [inv_mul_cancel₀ hℓ.ne']
        ring
    _ = (ℓ * Real.sqrt B / ρ) ^ 2 * (Real.sqrt T / ℓ * z) * θ * Y := by ring

/-- From `B^{-1/2} √X ≤ Y` (with `B > 0`, `X ≥ 0`): `X ≤ B Y²`. -/
theorem sq_le_of_inv_sqrt_mul_sqrt_le {B X Y : ℝ} (hB : 0 < B) (hX : 0 ≤ X)
    (h : (Real.sqrt B)⁻¹ * Real.sqrt X ≤ Y) : X ≤ B * Y ^ 2 := by
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have h1 : Real.sqrt X ≤ Real.sqrt B * Y := by
    have h2 := mul_le_mul_of_nonneg_left h hsB.le
    rwa [← mul_assoc, mul_inv_cancel₀ hsB.ne', one_mul] at h2
  have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg X) h1 2
  rwa [Real.sq_sqrt hX, mul_pow, Real.sq_sqrt hB.le] at h3

end Scales

section Bill

/-- **Each term of the abstract bill is at most the bill.** With
`Z = (√T/ℓ) r^{A'}` and `𝔱 = E^{2δ(J'+1)} + E^{δp'}`, each of `ε_c^{N'}`, `ε_c^{N'} Z`, `k 𝔱`,
`ε_c² 𝔱`, `ε_c² Z 𝔱` and `ℓ√(B_p/τ) exp(-cτ/ℓ²)` is at most
`billShape = ε_c^{N'}(1+Z) + [k + ε_c²(1+Z)]𝔱 + ℓ√(B_p/τ) exp(-cτ/ℓ²)`. -/
theorem billShape_ge_terms {E δ εc r k ℓ τ T cb Bp : ℝ} {Ac Nc Jc pc : ℕ} (hE : 0 ≤ E)
    (hεc : 0 ≤ εc) (hr : 0 ≤ r) (hk : 0 ≤ k) (hℓ : 0 ≤ ℓ) :
    εc ^ Nc ≤ Assembly.billShape E δ εc r k ℓ τ T cb Bp Ac Nc Jc pc ∧
    εc ^ Nc * (Real.sqrt T / ℓ * r ^ Ac) ≤
      Assembly.billShape E δ εc r k ℓ τ T cb Bp Ac Nc Jc pc ∧
    k * (E ^ (2 * δ * ((Jc : ℝ) + 1)) + E ^ (δ * (pc : ℝ))) ≤
      Assembly.billShape E δ εc r k ℓ τ T cb Bp Ac Nc Jc pc ∧
    εc ^ 2 * (E ^ (2 * δ * ((Jc : ℝ) + 1)) + E ^ (δ * (pc : ℝ))) ≤
      Assembly.billShape E δ εc r k ℓ τ T cb Bp Ac Nc Jc pc ∧
    εc ^ 2 * (Real.sqrt T / ℓ * r ^ Ac) *
        (E ^ (2 * δ * ((Jc : ℝ) + 1)) + E ^ (δ * (pc : ℝ))) ≤
      Assembly.billShape E δ εc r k ℓ τ T cb Bp Ac Nc Jc pc ∧
    ℓ * Real.sqrt (Bp / τ) * Real.exp (-(cb * τ / ℓ ^ 2)) ≤
      Assembly.billShape E δ εc r k ℓ τ T cb Bp Ac Nc Jc pc := by
  have hZ : 0 ≤ Real.sqrt T / ℓ * r ^ Ac :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg T) hℓ) (pow_nonneg hr Ac)
  have ht : 0 ≤ E ^ (2 * δ * ((Jc : ℝ) + 1)) + E ^ (δ * (pc : ℝ)) :=
    add_nonneg (Real.rpow_nonneg hE _) (Real.rpow_nonneg hE _)
  have hN : 0 ≤ εc ^ Nc := pow_nonneg hεc Nc
  have h2 : 0 ≤ εc ^ 2 := pow_nonneg hεc 2
  have hNZ : 0 ≤ εc ^ Nc * (Real.sqrt T / ℓ * r ^ Ac) := mul_nonneg hN hZ
  have hkt : 0 ≤ k * (E ^ (2 * δ * ((Jc : ℝ) + 1)) + E ^ (δ * (pc : ℝ))) := mul_nonneg hk ht
  have h2t : 0 ≤ εc ^ 2 * (E ^ (2 * δ * ((Jc : ℝ) + 1)) + E ^ (δ * (pc : ℝ))) :=
    mul_nonneg h2 ht
  have h2Zt : 0 ≤ εc ^ 2 * (Real.sqrt T / ℓ * r ^ Ac) *
      (E ^ (2 * δ * ((Jc : ℝ) + 1)) + E ^ (δ * (pc : ℝ))) :=
    mul_nonneg (mul_nonneg h2 hZ) ht
  have hP : 0 ≤ ℓ * Real.sqrt (Bp / τ) * Real.exp (-(cb * τ / ℓ ^ 2)) :=
    mul_nonneg (mul_nonneg hℓ (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  unfold Assembly.billShape
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **Each term of the bill `𝔅 = compBill` is at most the bill**:
with `ε_c = d_*/R`, `Z = (√|I|/ℓ)(e/R)^{A'}`, `𝔱 = E^{2δ(J'+1)} + E^{δp'}`, `R = √(Bτ_m'')`,
each of `ε_c^{N'}`, `ε_c^{N'} Z`, `√(B/ν) 𝔱`, `ε_c² 𝔱`, `ε_c² Z 𝔱` and `ℓ√(B_p/τ) exp(-cτ/ℓ²)`
is at most `𝔅`. Only `e = ε_m ≥ 0` and `E = ε_{m-1} ≥ 0` are needed. -/
theorem compBill_ge_terms (α q : ℝ) (Λ m : ℕ) (ν B Tobs cb : ℝ) (Bp Ac Nc Jc pc : ℕ)
    (he : 0 ≤ ocEpsilon q Λ m) (hE : 0 ≤ ocEpsilon q Λ (m - 1)) :
    (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) ^ Nc ≤
        compBill α q Λ m ν B Tobs cb Bp Ac Nc Jc pc ∧
    (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) ^ Nc *
        (Real.sqrt Tobs / ocEll q Λ m ν *
          (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) ^ Ac) ≤
        compBill α q Λ m ν B Tobs cb Bp Ac Nc Jc pc ∧
    Real.sqrt (B / ν) * (ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q * ((Jc : ℝ) + 1)) +
        ocEpsilon q Λ (m - 1) ^ (ocDelta α q * (pc : ℝ))) ≤
        compBill α q Λ m ν B Tobs cb Bp Ac Nc Jc pc ∧
    (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) ^ 2 *
        (ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q * ((Jc : ℝ) + 1)) +
          ocEpsilon q Λ (m - 1) ^ (ocDelta α q * (pc : ℝ))) ≤
        compBill α q Λ m ν B Tobs cb Bp Ac Nc Jc pc ∧
    (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) ^ 2 *
        (Real.sqrt Tobs / ocEll q Λ m ν *
          (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) ^ Ac) *
        (ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q * ((Jc : ℝ) + 1)) +
          ocEpsilon q Λ (m - 1) ^ (ocDelta α q * (pc : ℝ))) ≤
        compBill α q Λ m ν B Tobs cb Bp Ac Nc Jc pc ∧
    ocEll q Λ m ν * Real.sqrt ((Bp : ℝ) / ocTau α q Λ m) *
        Real.exp (-(cb * ocTau α q Λ m / ocEll q Λ m ν ^ 2)) ≤
      compBill α q Λ m ν B Tobs cb Bp Ac Nc Jc pc := by
  have hεc : 0 ≤ ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m) := by
    unfold ocDStar
    exact div_nonneg (mul_nonneg he (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hℓ : 0 ≤ ocEll q Λ m ν := by
    unfold ocEll
    exact div_nonneg he (Real.sqrt_nonneg _)
  have hb : compBill α q Λ m ν B Tobs cb Bp Ac Nc Jc pc =
      Assembly.billShape (ocEpsilon q Λ (m - 1)) (ocDelta α q)
        (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (Real.sqrt (B / ν))
        (ocEll q Λ m ν) (ocTau α q Λ m) Tobs cb (Bp : ℝ) Ac Nc Jc pc := rfl
  rw [hb]
  exact billShape_ge_terms hE hεc (div_nonneg he (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _) hℓ

end Bill

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Bill bookkeeping of the physical reconstruction: composing the bill**.

* Time integration of a two-density pointwise bound `M_r ≤ c·3(aG + bF)` against bounds
  `∫_I G ≤ I_G`, `∫_I F ≤ I_F` (`integral_le_of_two_density`).
* The algebra of the `R`-bill: the flux of the tail, of the coarse flux and of the lifted coarse
  flux, with `∫_I G ≤ X²/B` and `∫_I F ≤ B Y²`, compose to `(√K · bill · M)²`
  (`r_bill_le`), via the scale identities `flux_tail_scale`, `flux_lift_scale`.
* Cauchy–Schwarz on a time window of finite measure: `∫_I √G ≤ |I|^{1/2} (∫_I G)^{1/2}`
  (`integral_sqrt_le_of_integrable`, with `integrableOn_sqrt_of_integrable`), and its
  two-density form `∫_I √(c·2(aG + bF)) ≤ √(2c)(√a|I|^{1/2}√I_G + √b|I|^{1/2}√I_F)`
  (`integral_sqrt_two_density_le`).
* The algebra of the `q`-bill: the tail force and the lifted coarse force compose to
  `√(2c)(√T_F S C_s + √L_F θ C_y) · bill · M` (`q_bill_le`), via the scale identities
  `force_tail_scale`, `force_lift_scale`. -/

section Integration

/-- **Time integral of a two-density bound.** If `M_r ≤ c·3(aG + bF)` on `I` with `c, a, b ≥ 0`
and `∫_I G ≤ I_G`, `∫_I F ≤ I_F`, then `∫_I M_r ≤ c·3(a I_G + b I_F)`. -/
theorem integral_le_of_two_density {I : Set ℝ} {Mr G Fm : ℝ → ℝ} {c a b IG IF : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hI : MeasurableSet I)
    (hMr : IntegrableOn Mr I) (hG : IntegrableOn G I) (hF : IntegrableOn Fm I)
    (hpt : ∀ s ∈ I, Mr s ≤ c * (3 * (a * G s + b * Fm s)))
    (hIG : ∫ s in I, G s ≤ IG) (hIF : ∫ s in I, Fm s ≤ IF) :
    ∫ s in I, Mr s ≤ c * (3 * (a * IG + b * IF)) := by
  have haG : IntegrableOn (fun s => a * G s) I := Integrable.const_mul hG a
  have hbF : IntegrableOn (fun s => b * Fm s) I := Integrable.const_mul hF b
  have hsum : IntegrableOn (fun s => c * (3 * (a * G s + b * Fm s))) I :=
    Integrable.const_mul (Integrable.const_mul (Integrable.fun_add haG hbF) 3) c
  calc ∫ s in I, Mr s ≤ ∫ s in I, c * (3 * (a * G s + b * Fm s)) :=
        setIntegral_mono_on hMr hsum hI hpt
    _ = c * (3 * (a * (∫ s in I, G s) + b * (∫ s in I, Fm s))) := by
        rw [integral_const_mul, integral_const_mul, integral_add haG hbF, integral_const_mul,
          integral_const_mul]
    _ ≤ c * (3 * (a * IG + b * IF)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hIG ha) (mul_le_mul_of_nonneg_left hIF hb))
          (by norm_num)) hc

end Integration

section RBill

/-- **The algebra of the `R`-bill.** With `e = ℓ√ν`, `d = ℓ√B`, the time integrals
`I_G ≤ X²/B`, `I_F ≤ B Y²`, `X ≤ C_s M`, `Y ≤ C_y M 𝔱`, and the bill terms
`(d/ρ)^{N_c}`, `√(B/ν) 𝔱`, `(d/ρ)² 𝔱` at most `bill`:
`ν⁻¹ 2^{r+1}·3 (T_P (ℓ⁻²(d/ρ)^{N_c+1} e ρ S)² I_G + (r!² + L_P (e/ρ)²(d/ρ)²θ²) I_F)
  ≤ (√(2^{r+1}·3 (T_P S² C_s² + (r!² + L_P θ²) C_y²)) · bill · M)²`. -/
theorem r_bill_le {ν B ℓ ρ e d S θ TP LP Cs Cy M X Y tt bill IG IF : ℝ} (r Nc : ℕ)
    (hν : 0 < ν) (hB : 0 < B) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (he : e = ℓ * Real.sqrt ν) (hd : d = ℓ * Real.sqrt B)
    (hTP : 0 ≤ TP) (hLP : 0 ≤ LP) (hCs : 0 ≤ Cs) (hCy : 0 ≤ Cy) (hM : 0 ≤ M)
    (hX0 : 0 ≤ X) (hX : X ≤ Cs * M) (hY0 : 0 ≤ Y) (hY : Y ≤ Cy * M * tt) (htt : 0 ≤ tt)
    (hIG : IG ≤ X ^ 2 / B) (hIF : IF ≤ B * Y ^ 2)
    (hb1 : (d / ρ) ^ Nc ≤ bill) (hb2 : Real.sqrt (B / ν) * tt ≤ bill)
    (hb3 : (d / ρ) ^ 2 * tt ≤ bill) :
    ν⁻¹ * (2 ^ (r + 1) * (3 * (TP * ((ℓ ^ 2)⁻¹ * (d / ρ) ^ (Nc + 1) * e * ρ * S) ^ 2 * IG +
        ((r.factorial : ℝ) ^ 2 + LP * ((e / ρ) ^ 2 * (d / ρ) ^ 2 * θ ^ 2)) * IF))) ≤
      (Real.sqrt (2 ^ (r + 1) * 3 * (TP * S ^ 2 * Cs ^ 2 +
        ((r.factorial : ℝ) ^ 2 + LP * θ ^ 2) * Cy ^ 2)) * bill * M) ^ 2 := by
  have hd0 : 0 ≤ d := by
    rw [hd]
    exact mul_nonneg hℓ.le (Real.sqrt_nonneg B)
  have hw0 : 0 ≤ (d / ρ) ^ Nc := pow_nonneg (div_nonneg hd0 hρ.le) Nc
  have hν0 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hCYM : 0 ≤ Cy * M * tt := mul_nonneg (mul_nonneg hCy hM) htt
  have hY2 : Y * Y ≤ Cy * M * tt * (Cy * M * tt) := mul_le_mul hY hY hY0 hCYM
  -- the flux of the tail
  have hT1 : ν⁻¹ * ((ℓ ^ 2)⁻¹ * (d / ρ) ^ (Nc + 1) * e * ρ * S) ^ 2 * IG ≤
      S ^ 2 * Cs ^ 2 * M ^ 2 * bill ^ 2 := by
    have hfl := flux_tail_scale (S := S) (E := X) Nc hℓ hν hB hρ he hd
    rw [pow_mul' (d / ρ) 2 Nc] at hfl
    have hXw : X * (d / ρ) ^ Nc ≤ Cs * M * bill := mul_le_mul hX hb1 hw0 (mul_nonneg hCs hM)
    have hsq : (X * (d / ρ) ^ Nc) ^ 2 ≤ (Cs * M * bill) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hX0 hw0) hXw 2
    calc _ ≤ ν⁻¹ * ((ℓ ^ 2)⁻¹ * (d / ρ) ^ (Nc + 1) * e * ρ * S) ^ 2 * (X ^ 2 / B) :=
          mul_le_mul_of_nonneg_left hIG (mul_nonneg hν0 (sq_nonneg _))
      _ = ((d / ρ) ^ Nc) ^ 2 * S ^ 2 * X ^ 2 := hfl
      _ = S ^ 2 * (X * (d / ρ) ^ Nc) ^ 2 := by ring
      _ ≤ S ^ 2 * (Cs * M * bill) ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg S)
      _ = S ^ 2 * Cs ^ 2 * M ^ 2 * bill ^ 2 := by ring
  -- the coarse flux
  have hT2 : ν⁻¹ * IF ≤ Cy ^ 2 * M ^ 2 * bill ^ 2 := by
    have hBν : 0 ≤ B / ν := div_nonneg hB.le hν.le
    have hs2 : (Real.sqrt (B / ν) * tt) ^ 2 ≤ bill ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) htt) hb2 2
    calc ν⁻¹ * IF ≤ ν⁻¹ * (B * Y ^ 2) := mul_le_mul_of_nonneg_left hIF hν0
      _ = B / ν * (Y * Y) := by ring
      _ ≤ B / ν * (Cy * M * tt * (Cy * M * tt)) := mul_le_mul_of_nonneg_left hY2 hBν
      _ = Cy ^ 2 * M ^ 2 * (Real.sqrt (B / ν) ^ 2 * tt ^ 2) := by
          rw [Real.sq_sqrt hBν]
          ring
      _ = Cy ^ 2 * M ^ 2 * (Real.sqrt (B / ν) * tt) ^ 2 := by ring
      _ ≤ Cy ^ 2 * M ^ 2 * bill ^ 2 :=
          mul_le_mul_of_nonneg_left hs2 (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- the lifted coarse flux
  have hT3 : ν⁻¹ * ((e / ρ) ^ 2 * (d / ρ) ^ 2 * θ ^ 2) * IF ≤
      θ ^ 2 * Cy ^ 2 * M ^ 2 * bill ^ 2 := by
    have hs3 : ((d / ρ) ^ 2 * tt) ^ 2 ≤ bill ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) htt) hb3 2
    have hc4 : 0 ≤ (d / ρ) ^ 4 * θ ^ 2 :=
      mul_nonneg (pow_nonneg (div_nonneg hd0 hρ.le) 4) (sq_nonneg θ)
    have hcoef : 0 ≤ ν⁻¹ * ((e / ρ) ^ 2 * (d / ρ) ^ 2 * θ ^ 2) :=
      mul_nonneg hν0 (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
    calc _ ≤ ν⁻¹ * ((e / ρ) ^ 2 * (d / ρ) ^ 2 * θ ^ 2) * (B * Y ^ 2) :=
          mul_le_mul_of_nonneg_left hIF hcoef
      _ = (d / ρ) ^ 4 * θ ^ 2 * Y ^ 2 := flux_lift_scale hν hB.le he hd
      _ = (d / ρ) ^ 4 * θ ^ 2 * (Y * Y) := by ring
      _ ≤ (d / ρ) ^ 4 * θ ^ 2 * (Cy * M * tt * (Cy * M * tt)) :=
          mul_le_mul_of_nonneg_left hY2 hc4
      _ = θ ^ 2 * Cy ^ 2 * M ^ 2 * ((d / ρ) ^ 2 * tt) ^ 2 := by ring
      _ ≤ θ ^ 2 * Cy ^ 2 * M ^ 2 * bill ^ 2 :=
          mul_le_mul_of_nonneg_left hs3
            (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
  -- composition
  have hK : (0 : ℝ) ≤ 2 ^ (r + 1) * 3 := by positivity
  have hF2 : (0 : ℝ) ≤ (r.factorial : ℝ) ^ 2 := sq_nonneg _
  have hR : 0 ≤ 2 ^ (r + 1) * 3 * (TP * S ^ 2 * Cs ^ 2 +
      ((r.factorial : ℝ) ^ 2 + LP * θ ^ 2) * Cy ^ 2) :=
    mul_nonneg hK (add_nonneg (mul_nonneg (mul_nonneg hTP (sq_nonneg S)) (sq_nonneg Cs))
      (mul_nonneg (add_nonneg hF2 (mul_nonneg hLP (sq_nonneg θ))) (sq_nonneg Cy)))
  have hRHS : (Real.sqrt (2 ^ (r + 1) * 3 * (TP * S ^ 2 * Cs ^ 2 +
        ((r.factorial : ℝ) ^ 2 + LP * θ ^ 2) * Cy ^ 2)) * bill * M) ^ 2 =
      2 ^ (r + 1) * 3 * (TP * S ^ 2 * Cs ^ 2 + ((r.factorial : ℝ) ^ 2 + LP * θ ^ 2) * Cy ^ 2) *
        bill ^ 2 * M ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hR]
  rw [hRHS]
  calc _ = 2 ^ (r + 1) * 3 *
        (TP * (ν⁻¹ * ((ℓ ^ 2)⁻¹ * (d / ρ) ^ (Nc + 1) * e * ρ * S) ^ 2 * IG) +
          (r.factorial : ℝ) ^ 2 * (ν⁻¹ * IF) +
          LP * (ν⁻¹ * ((e / ρ) ^ 2 * (d / ρ) ^ 2 * θ ^ 2) * IF)) := by ring
    _ ≤ 2 ^ (r + 1) * 3 * (TP * (S ^ 2 * Cs ^ 2 * M ^ 2 * bill ^ 2) +
          (r.factorial : ℝ) ^ 2 * (Cy ^ 2 * M ^ 2 * bill ^ 2) +
          LP * (θ ^ 2 * Cy ^ 2 * M ^ 2 * bill ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hT1 hTP)
          (mul_le_mul_of_nonneg_left hT2 hF2)) (mul_le_mul_of_nonneg_left hT3 hLP)) hK
    _ = 2 ^ (r + 1) * 3 * (TP * S ^ 2 * Cs ^ 2 + ((r.factorial : ℝ) ^ 2 + LP * θ ^ 2) * Cy ^ 2) *
        bill ^ 2 * M ^ 2 := by ring

end RBill

section CauchySchwarz

/-- `2t√x ≤ t² + x` for `x ≥ 0` (from `(t - √x)² ≥ 0`). -/
private theorem two_mul_mul_sqrt_le {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    2 * t * Real.sqrt x ≤ t ^ 2 + x := by
  calc 2 * t * Real.sqrt x = t ^ 2 + Real.sqrt x ^ 2 - (t - Real.sqrt x) ^ 2 := by ring
    _ ≤ t ^ 2 + Real.sqrt x ^ 2 := by linarith [sq_nonneg (t - Real.sqrt x)]
    _ = t ^ 2 + x := by rw [Real.sq_sqrt hx]

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
private theorem sqrt_add_le_sqrt_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y))]
  have h := mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
  calc x + y = Real.sqrt x ^ 2 + Real.sqrt y ^ 2 := by
        rw [Real.sq_sqrt hx, Real.sq_sqrt hy]
    _ ≤ Real.sqrt x ^ 2 + Real.sqrt y ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) := by linarith
    _ = (Real.sqrt x + Real.sqrt y) ^ 2 := by ring

/-- An abstract Cauchy–Schwarz step: if `2tX ≤ t²L + J` for every real `t`, with `L, J ≥ 0`,
then `X ≤ √L √J`. -/
private theorem le_sqrt_mul_sqrt_of_forall {X L J : ℝ} (hL : 0 ≤ L) (hJ : 0 ≤ J)
    (h : ∀ t : ℝ, 2 * t * X ≤ t ^ 2 * L + J) : X ≤ Real.sqrt L * Real.sqrt J := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (mul_nonneg (Real.sqrt_nonneg L) (Real.sqrt_nonneg J))
  rw [← Real.sqrt_mul hL J]
  refine Real.le_sqrt_of_sq_le ?_
  rcases hL.eq_or_lt with hL0 | hLpos
  · -- `L = 0`: the choice `t = J/X + 1` contradicts `X > 0`
    exfalso
    have h1 := h (J * X⁻¹ + 1)
    rw [← hL0, mul_zero, zero_add] at h1
    have e : 2 * (J * X⁻¹ + 1) * X = 2 * J * (X⁻¹ * X) + 2 * X := by ring
    rw [e, inv_mul_cancel₀ hX.ne', mul_one] at h1
    linarith
  · -- `L > 0`: the choice `t = X/L`
    have h1 := h (X * L⁻¹)
    have e1 : 2 * (X * L⁻¹) * X = 2 * (X ^ 2 * L⁻¹) := by ring
    have e2 : (X * L⁻¹) ^ 2 * L = X ^ 2 * L⁻¹ * (L⁻¹ * L) := by ring
    rw [e1, e2, inv_mul_cancel₀ hLpos.ne', mul_one] at h1
    have h2 : X ^ 2 * L⁻¹ ≤ J := by linarith
    calc X ^ 2 = L * (X ^ 2 * L⁻¹) := by
          rw [mul_comm L, mul_assoc, inv_mul_cancel₀ hLpos.ne', mul_one]
      _ ≤ L * J := mul_le_mul_of_nonneg_left h2 hLpos.le

/-- **Integrability of a square root** on a set of finite measure: if `G ≥ 0` is integrable on
`I` and `|I| < ∞`, then `√G` is integrable on `I` (dominated by `1 + G`). -/
theorem integrableOn_sqrt_of_integrable {I : Set ℝ} {G : ℝ → ℝ} (hIfin : volume I < ⊤)
    (hG0 : ∀ s, 0 ≤ G s) (hG : IntegrableOn G I) :
    IntegrableOn (fun s => Real.sqrt (G s)) I := by
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) I := integrableOn_const hIfin.ne
  have hbd : ∀ s, ‖Real.sqrt (G s)‖ ≤ 1 + G s := fun s => by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Assembly.sqrt_le_one_add (hG0 s)
  exact Integrable.mono' (Integrable.fun_add h1 hG)
    (Real.continuous_sqrt.comp_aestronglyMeasurable (Integrable.aestronglyMeasurable hG))
    (ae_of_all _ hbd)

/-- **Cauchy–Schwarz on a set of finite measure**: for `G ≥ 0` integrable on `I` with
`|I| < ∞`, `∫_I √G ≤ |I|^{1/2} (∫_I G)^{1/2}`. -/
theorem integral_sqrt_le_of_integrable {I : Set ℝ} {G : ℝ → ℝ} (hI : MeasurableSet I)
    (hIfin : volume I < ⊤) (hG0 : ∀ s, 0 ≤ G s) (hG : IntegrableOn G I) :
    ∫ s in I, Real.sqrt (G s) ≤ Real.sqrt (volume I).toReal * Real.sqrt (∫ s in I, G s) := by
  have hsG : IntegrableOn (fun s => Real.sqrt (G s)) I :=
    integrableOn_sqrt_of_integrable hIfin hG0 hG
  refine le_sqrt_mul_sqrt_of_forall ENNReal.toReal_nonneg
    (setIntegral_nonneg hI fun s _ => hG0 s) fun t => ?_
  have hct : IntegrableOn (fun _ : ℝ => t ^ 2) I := integrableOn_const hIfin.ne
  have htG : IntegrableOn (fun s => 2 * t * Real.sqrt (G s)) I := Integrable.const_mul hsG _
  have hsum : IntegrableOn (fun s => t ^ 2 + G s) I := Integrable.fun_add hct hG
  have hpt : ∀ s ∈ I, 2 * t * Real.sqrt (G s) ≤ t ^ 2 + G s := fun s _ =>
    two_mul_mul_sqrt_le (hG0 s) t
  calc 2 * t * (∫ s in I, Real.sqrt (G s)) = ∫ s in I, 2 * t * Real.sqrt (G s) :=
        (integral_const_mul (2 * t) fun s => Real.sqrt (G s)).symm
    _ ≤ ∫ s in I, (t ^ 2 + G s) := setIntegral_mono_on htG hsum hI hpt
    _ = t ^ 2 * (volume I).toReal + ∫ s in I, G s := by
        rw [integral_add hct hG, setIntegral_const, smul_eq_mul, measureReal_def]
        ring

/-- **The `q`-bill integral (smooth part).** For `G, F ≥ 0` integrable on `I` with
`|I| < ∞`, `c, a, b ≥ 0`, `∫_I G ≤ I_G` and `∫_I F ≤ I_F`:
`∫_I √(c·2(aG + bF)) ≤ √(2c) (√a |I|^{1/2} √I_G + √b |I|^{1/2} √I_F)`. -/
theorem integral_sqrt_two_density_le {I : Set ℝ} {G Fm : ℝ → ℝ} {c a b IG IF : ℝ}
    (hI : MeasurableSet I) (hIfin : volume I < ⊤) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hG0 : ∀ s, 0 ≤ G s) (hF0 : ∀ s, 0 ≤ Fm s) (hG : IntegrableOn G I) (hF : IntegrableOn Fm I)
    (hIG : ∫ s in I, G s ≤ IG) (hIF : ∫ s in I, Fm s ≤ IF) :
    ∫ s in I, Real.sqrt (c * (2 * (a * G s + b * Fm s))) ≤
      Real.sqrt (2 * c) * (Real.sqrt a * Real.sqrt (volume I).toReal * Real.sqrt IG +
        Real.sqrt b * Real.sqrt (volume I).toReal * Real.sqrt IF) := by
  have h2c : 0 ≤ 2 * c := mul_nonneg zero_le_two hc
  have hrad : ∀ s, 0 ≤ c * (2 * (a * G s + b * Fm s)) := fun s =>
    mul_nonneg hc (mul_nonneg zero_le_two
      (add_nonneg (mul_nonneg ha (hG0 s)) (mul_nonneg hb (hF0 s))))
  have hint : IntegrableOn (fun s => c * (2 * (a * G s + b * Fm s))) I :=
    Integrable.const_mul (Integrable.const_mul
      (Integrable.fun_add (Integrable.const_mul hG a) (Integrable.const_mul hF b)) 2) c
  have hL : IntegrableOn (fun s => Real.sqrt (c * (2 * (a * G s + b * Fm s)))) I :=
    integrableOn_sqrt_of_integrable hIfin hrad hint
  have hsaG : IntegrableOn (fun s => Real.sqrt a * Real.sqrt (G s)) I :=
    Integrable.const_mul (integrableOn_sqrt_of_integrable hIfin hG0 hG) _
  have hsbF : IntegrableOn (fun s => Real.sqrt b * Real.sqrt (Fm s)) I :=
    Integrable.const_mul (integrableOn_sqrt_of_integrable hIfin hF0 hF) _
  have hR : IntegrableOn (fun s => Real.sqrt (2 * c) *
      (Real.sqrt a * Real.sqrt (G s) + Real.sqrt b * Real.sqrt (Fm s))) I :=
    Integrable.const_mul (Integrable.fun_add hsaG hsbF) _
  have hpt : ∀ s ∈ I, Real.sqrt (c * (2 * (a * G s + b * Fm s))) ≤
      Real.sqrt (2 * c) * (Real.sqrt a * Real.sqrt (G s) + Real.sqrt b * Real.sqrt (Fm s)) := by
    intro s _
    have hcomm : c * (2 * (a * G s + b * Fm s)) = 2 * c * (a * G s + b * Fm s) := by ring
    rw [hcomm, Real.sqrt_mul h2c (a * G s + b * Fm s), ← Real.sqrt_mul ha (G s),
      ← Real.sqrt_mul hb (Fm s)]
    exact mul_le_mul_of_nonneg_left
      (sqrt_add_le_sqrt_add_sqrt (mul_nonneg ha (hG0 s)) (mul_nonneg hb (hF0 s)))
      (Real.sqrt_nonneg _)
  have hCG : ∫ s in I, Real.sqrt (G s) ≤ Real.sqrt (volume I).toReal * Real.sqrt IG :=
    (integral_sqrt_le_of_integrable hI hIfin hG0 hG).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hIG) (Real.sqrt_nonneg _))
  have hCF : ∫ s in I, Real.sqrt (Fm s) ≤ Real.sqrt (volume I).toReal * Real.sqrt IF :=
    (integral_sqrt_le_of_integrable hI hIfin hF0 hF).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hIF) (Real.sqrt_nonneg _))
  calc ∫ s in I, Real.sqrt (c * (2 * (a * G s + b * Fm s))) ≤
        ∫ s in I, Real.sqrt (2 * c) *
          (Real.sqrt a * Real.sqrt (G s) + Real.sqrt b * Real.sqrt (Fm s)) :=
        setIntegral_mono_on hL hR hI hpt
    _ = Real.sqrt (2 * c) * (Real.sqrt a * (∫ s in I, Real.sqrt (G s)) +
          Real.sqrt b * (∫ s in I, Real.sqrt (Fm s))) := by
        rw [integral_const_mul, integral_add hsaG hsbF, integral_const_mul, integral_const_mul]
    _ ≤ Real.sqrt (2 * c) * (Real.sqrt a * (Real.sqrt (volume I).toReal * Real.sqrt IG) +
          Real.sqrt b * (Real.sqrt (volume I).toReal * Real.sqrt IF)) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hCG (Real.sqrt_nonneg a))
          (mul_le_mul_of_nonneg_left hCF (Real.sqrt_nonneg b))) (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * c) * (Real.sqrt a * Real.sqrt (volume I).toReal * Real.sqrt IG +
          Real.sqrt b * Real.sqrt (volume I).toReal * Real.sqrt IF) := by ring

end CauchySchwarz

section QBill

/-- **The algebra of the `q`-bill.** With `e = ℓ√ν`, `d = ℓ√B`, `Z = (√T/ℓ)(e/ρ)^A`, the time
integrals `I_G ≤ X²/B`, `I_F ≤ B Y²`, `X ≤ C_s M`, `Y ≤ C_y M 𝔱`, and the bill terms
`(d/ρ)^{N_c} Z`, `(d/ρ)² Z 𝔱` at most `bill`:
`√(2c) (√(T_F (ℓ⁻²(d/ρ)^{N_c+1}(e/ρ)^A ρ S)²) √T √I_G + √(L_F (ρ⁻¹(e/ρ)^A)²(d/ρ)²θ²) √T √I_F)
  ≤ √(2c) (√T_F S C_s + √L_F θ C_y) · bill · M`.
The hypotheses `0 < ν`, `0 ≤ T`, `0 ≤ I_G`, `0 ≤ I_F`, `0 ≤ c` are not needed by the proof. -/
theorem q_bill_le {ν B ℓ ρ e d S θ TF LF Cs Cy M X Y tt bill T IG IF : ℝ} (Nc A : ℕ)
    (_hν : 0 < ν) (hB : 0 < B) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (he : e = ℓ * Real.sqrt ν) (hd : d = ℓ * Real.sqrt B) (hS : 0 ≤ S) (hθ : 0 ≤ θ)
    (hTF : 0 ≤ TF) (hLF : 0 ≤ LF) (hCs : 0 ≤ Cs) (hCy : 0 ≤ Cy) (hM : 0 ≤ M) (_hT : 0 ≤ T)
    (hX0 : 0 ≤ X) (hX : X ≤ Cs * M) (hY0 : 0 ≤ Y) (hY : Y ≤ Cy * M * tt) (htt : 0 ≤ tt)
    (hIG : IG ≤ X ^ 2 / B) (hIF : IF ≤ B * Y ^ 2) (_hIG0 : 0 ≤ IG) (_hIF0 : 0 ≤ IF)
    (hb1 : (d / ρ) ^ Nc * (Real.sqrt T / ℓ * (e / ρ) ^ A) ≤ bill)
    (hb2 : (d / ρ) ^ 2 * (Real.sqrt T / ℓ * (e / ρ) ^ A) * tt ≤ bill) (c : ℝ) (_hc : 0 ≤ c) :
    Real.sqrt (2 * c) *
        (Real.sqrt (TF * ((ℓ ^ 2)⁻¹ * (d / ρ) ^ (Nc + 1) * (e / ρ) ^ A * ρ * S) ^ 2) *
            Real.sqrt T * Real.sqrt IG +
          Real.sqrt (LF * ((ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (d / ρ) ^ 2 * θ ^ 2)) *
            Real.sqrt T * Real.sqrt IF) ≤
      Real.sqrt (2 * c) * (Real.sqrt TF * S * Cs + Real.sqrt LF * θ * Cy) * bill * M := by
  have hd0 : 0 ≤ d := by
    rw [hd]
    exact mul_nonneg hℓ.le (Real.sqrt_nonneg B)
  have he0 : 0 ≤ e := by
    rw [he]
    exact mul_nonneg hℓ.le (Real.sqrt_nonneg ν)
  have hZ0 : 0 ≤ Real.sqrt T / ℓ * (e / ρ) ^ A :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg T) hℓ.le) (pow_nonneg (div_nonneg he0 hρ.le) A)
  have hP0 : 0 ≤ (d / ρ) ^ Nc * (Real.sqrt T / ℓ * (e / ρ) ^ A) :=
    mul_nonneg (pow_nonneg (div_nonneg hd0 hρ.le) Nc) hZ0
  have hQ0 : 0 ≤ (d / ρ) ^ 2 * (Real.sqrt T / ℓ * (e / ρ) ^ A) := mul_nonneg (sq_nonneg _) hZ0
  have hsIG : Real.sqrt IG ≤ (Real.sqrt B)⁻¹ * X :=
    calc Real.sqrt IG ≤ Real.sqrt (X ^ 2 / B) := Real.sqrt_le_sqrt hIG
      _ = (Real.sqrt B)⁻¹ * X := by
          rw [Real.sqrt_div' _ hB.le, Real.sqrt_sq hX0, div_eq_inv_mul]
  have hsIF : Real.sqrt IF ≤ Real.sqrt B * Y :=
    calc Real.sqrt IF ≤ Real.sqrt (B * Y ^ 2) := Real.sqrt_le_sqrt hIF
      _ = Real.sqrt B * Y := by rw [Real.sqrt_mul hB.le, Real.sqrt_sq hY0]
  -- the tail force
  have h1 : Real.sqrt (TF * ((ℓ ^ 2)⁻¹ * (d / ρ) ^ (Nc + 1) * (e / ρ) ^ A * ρ * S) ^ 2) *
      Real.sqrt T * Real.sqrt IG ≤ Real.sqrt TF * (Cs * M * (bill * S)) := by
    have hW0 : 0 ≤ Real.sqrt (((ℓ ^ 2)⁻¹ * (d / ρ) ^ (Nc + 1) * (e / ρ) ^ A * ρ * S) ^ 2) *
        Real.sqrt T := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hPS : (d / ρ) ^ Nc * (Real.sqrt T / ℓ * (e / ρ) ^ A) * S ≤ bill * S :=
      mul_le_mul_of_nonneg_right hb1 hS
    calc _ = Real.sqrt TF *
          (Real.sqrt (((ℓ ^ 2)⁻¹ * (d / ρ) ^ (Nc + 1) * (e / ρ) ^ A * ρ * S) ^ 2) *
            Real.sqrt T * Real.sqrt IG) := by
          rw [Real.sqrt_mul hTF]
          ring
      _ ≤ Real.sqrt TF *
          (Real.sqrt (((ℓ ^ 2)⁻¹ * (d / ρ) ^ (Nc + 1) * (e / ρ) ^ A * ρ * S) ^ 2) *
            Real.sqrt T * ((Real.sqrt B)⁻¹ * X)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsIG hW0) (Real.sqrt_nonneg _)
      _ = Real.sqrt TF * (X * ((d / ρ) ^ Nc * (Real.sqrt T / ℓ * (e / ρ) ^ A) * S)) := by
          rw [force_tail_scale Nc A hℓ hB hρ he hd hS]
          ring
      _ ≤ Real.sqrt TF * (Cs * M * (bill * S)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hX hPS (mul_nonneg hP0 hS) (mul_nonneg hCs hM))
            (Real.sqrt_nonneg _)
  -- the lifted coarse force
  have h2 : Real.sqrt (LF * ((ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (d / ρ) ^ 2 * θ ^ 2)) *
      Real.sqrt T * Real.sqrt IF ≤ Real.sqrt LF * (bill * (θ * (Cy * M))) := by
    have hW0 : 0 ≤ Real.sqrt ((ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (d / ρ) ^ 2 * θ ^ 2) * Real.sqrt T :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hQY : Y * ((d / ρ) ^ 2 * (Real.sqrt T / ℓ * (e / ρ) ^ A) * θ) ≤
        Cy * M * tt * ((d / ρ) ^ 2 * (Real.sqrt T / ℓ * (e / ρ) ^ A) * θ) :=
      mul_le_mul hY le_rfl (mul_nonneg hQ0 hθ) (mul_nonneg (mul_nonneg hCy hM) htt)
    calc _ = Real.sqrt LF * (Real.sqrt ((ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (d / ρ) ^ 2 * θ ^ 2) *
            Real.sqrt T * Real.sqrt IF) := by
          rw [Real.sqrt_mul hLF]
          ring
      _ ≤ Real.sqrt LF * (Real.sqrt ((ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (d / ρ) ^ 2 * θ ^ 2) *
            Real.sqrt T * (Real.sqrt B * Y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsIF hW0) (Real.sqrt_nonneg _)
      _ = Real.sqrt LF * (Y * ((d / ρ) ^ 2 * (Real.sqrt T / ℓ * (e / ρ) ^ A) * θ)) := by
          rw [force_lift_scale A hℓ hρ.le he hd hθ]
          ring
      _ ≤ Real.sqrt LF * (Cy * M * tt * ((d / ρ) ^ 2 * (Real.sqrt T / ℓ * (e / ρ) ^ A) * θ)) :=
          mul_le_mul_of_nonneg_left hQY (Real.sqrt_nonneg _)
      _ = Real.sqrt LF *
          ((d / ρ) ^ 2 * (Real.sqrt T / ℓ * (e / ρ) ^ A) * tt * (θ * (Cy * M))) := by ring
      _ ≤ Real.sqrt LF * (bill * (θ * (Cy * M))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hb2 (mul_nonneg hθ (mul_nonneg hCy hM)))
            (Real.sqrt_nonneg _)
  -- composition
  calc _ ≤ Real.sqrt (2 * c) *
        (Real.sqrt TF * (Cs * M * (bill * S)) + Real.sqrt LF * (bill * (θ * (Cy * M)))) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * c) * (Real.sqrt TF * S * Cs + Real.sqrt LF * θ * Cy) * bill * M := by
        ring

end QBill

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.CycleComparison.Reconstruction

/-! **A pulse mean is the glued mean where the pulse is weighted** (the last sum of the gluing
identity). If at a time `t` of the window every weighted
pulse has the same mean as the pulse `k` (true by the exact quiet mean, since two pulses are
weighted together only at quiet times), the glued mean `∑_j ϖ_j 𝓜_j` equals `𝓜_k` there
(`pulseMeanField_eq_gluedMean`), because the weights sum to one. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- **A pulse mean is the glued mean** at a weighted time where all weighted pulse means agree. -/
theorem pulseMeanField_eq_gluedMean (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (N r : ℕ)
    (Q : ℤ → LiftOperatorData ι h D) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ}
    (hsum : ∑ j ∈ kset, ϖ j t = 1) {k : ℤ}
    (hagree : ∀ j ∈ kset, ϖ j t ≠ 0 → ∀ x,
      pulseMeanField c ρ εc N r (Q j) (Cc j) (chart j) (label j) a t x =
        pulseMeanField c ρ εc N r (Q k) (Cc k) (chart k) (label k) a t x) (x : Vec 2) :
    gluedMean kset ϖ c ρ εc N r Q Cc chart label a t x =
      pulseMeanField c ρ εc N r (Q k) (Cc k) (chart k) (label k) a t x := by
  have hterm : ∀ j ∈ kset, ϖ j t • pulseMeanField c ρ εc N r (Q j) (Cc j) (chart j) (label j)
      a t x = ϖ j t • pulseMeanField c ρ εc N r (Q k) (Cc k) (chart k) (label k) a t x :=
    fun j hj => by
      by_cases hw : ϖ j t = 0
      · rw [hw, zero_smul, zero_smul]
      · rw [hagree j hj hw x]
  simp only [gluedMean]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, hsum, one_smul]

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! # Word sums against permutation-invariant weights

Against weights `w` with `w(A ∘ σ) = w(A)` (ordered derivatives of a smooth field,
`Lift.orderedDerivative_comp_perm`), a sum `∑_A f(A) w(A)` over the words of length `r` sees only
the permutation sums `∑_σ f(A ∘ σ)`: `r! ∑_A f(A) w(A) = ∑_A (∑_σ f(A ∘ σ)) w(A)`. So the
transport identity summed over the permutations of the word (`cycle_comparison`)
gives the same flux as the word-by-word identity (`sum_word_smul_eq_of_perm_sum`). -/

/-- **The ordered derivatives of a `C^m` function are symmetric** in the word of length `m`
(`Analysis.iteratedFDeriv_comp_perm_of_contDiff`). -/
theorem orderedDerivative_comp_perm_of_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {m : ℕ} (A : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) {g : Vec 2 → E}
    (hg : ContDiff ℝ (m : ℕ∞) g) (x : Vec 2) :
    orderedDerivative (A ∘ σ) g x = orderedDerivative A g x := by
  rw [Sampling.orderedDerivative_eq_iteratedFDeriv _ g hg,
    Sampling.orderedDerivative_eq_iteratedFDeriv _ g hg]
  have h := Analysis.iteratedFDeriv_comp_perm_of_contDiff m (ContDiff.of_le hg le_rfl) x
    (fun k => basisVec (A (Fin.rev k))) (Fin.revPerm.trans (σ.trans Fin.revPerm))
  refine Eq.trans ?_ h
  show iteratedFDeriv ℝ m g x (fun k => basisVec ((A ∘ σ) (Fin.rev k))) = _
  congr 1
  funext k
  simp [Fin.revPerm]

/-- `r! ∑_A f(A) w(A) = ∑_A (∑_σ f(A ∘ σ)) w(A)` for permutation-invariant weights `w`. -/
theorem card_perm_smul_sum_word {M : Type*} [AddCommGroup M] [Module ℝ M] {r : ℕ}
    (f : DerivativeWord2 r → ℝ) (w : DerivativeWord2 r → M)
    (hw : ∀ A (σ : Equiv.Perm (Fin r)), w (A ∘ σ) = w A) :
    (Fintype.card (Equiv.Perm (Fin r)) : ℝ) • ∑ A, f A • w A =
      ∑ A, (∑ σ : Equiv.Perm (Fin r), f (A ∘ σ)) • w A := by
  have hp : ∀ σ : Equiv.Perm (Fin r), ∑ A, f (A ∘ σ) • w A = ∑ A, f A • w A := by
    intro σ
    have he := Equiv.sum_comp (Lift.wordPermutationEquiv σ) (fun A => f A • w A)
    simp only [Lift.wordPermutationEquiv, Equiv.coe_fn_mk, hw] at he
    exact he
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  rw [Nat.cast_smul_eq_nsmul]

/-- **Word sums see only permutation sums.** If `∑_σ f(A ∘ σ) = ∑_σ g(A ∘ σ)` for every word
`A` and the weights are permutation invariant, then `∑_A f(A) w(A) = ∑_A g(A) w(A)`. -/
theorem sum_word_smul_eq_of_perm_sum {M : Type*} [AddCommGroup M] [Module ℝ M] {r : ℕ}
    (f g : DerivativeWord2 r → ℝ) (w : DerivativeWord2 r → M)
    (hw : ∀ A (σ : Equiv.Perm (Fin r)), w (A ∘ σ) = w A)
    (hfg : ∀ A, ∑ σ : Equiv.Perm (Fin r), f (A ∘ σ) = ∑ σ : Equiv.Perm (Fin r), g (A ∘ σ)) :
    ∑ A, f A • w A = ∑ A, g A • w A := by
  have hcard : (Fintype.card (Equiv.Perm (Fin r)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  apply smul_right_injective M hcard
  simp only [card_perm_smul_sum_word f w hw, card_perm_smul_sum_word g w hw, hfg]

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Cleanup chains are linear in their data** (`𝒜_z` and `div_X` are linear). The sum of cleanup
chains of two data is a cleanup chain of the sum of the data (`IsCleanupChain.add`), the negative of
a chain is a chain of the negative data (`IsCleanupChain.neg`), hence the difference of two chains
is a chain of the difference of the data (`IsCleanupChain.sub`). With uniqueness
(`isCleanupChain_unique`) this makes the residual presentation of the reconstruction linear in the
coarse field, which is how the presentations of the finite-rank approximants converge. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The cleanup source of a sum of slow-differentiable chains is the sum of the sources. -/
theorem cleanupSource_add {sX : ℕ} (hX : 1 ≤ sX) {V V' : ℕ → Vec 2 → Vec 2 → Fin 2 → E} {j : ℕ}
    (hV : IsSlowSmooth sX (V (j - 1))) (hV' : IsSlowSmooth sX (V' (j - 1))) :
    cleanupSource (fun i X z k => V i X z k + V' i X z k) j =
      fun X z => cleanupSource V j X z + cleanupSource V' j X z := by
  funext X z
  have hsX : ((sX : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : sX ≠ 0)
  simp only [cleanupSource, slowPartial]
  rw [← neg_add, ← Finset.sum_add_distrib]
  refine congrArg Neg.neg (Finset.sum_congr rfl fun k _ => ?_)
  have hd : DifferentiableAt ℝ (fun X' => V (j - 1) X' z k) X :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k).differentiable.comp
      ((hV.1 z).differentiable hsX)) X
  have hd' : DifferentiableAt ℝ (fun X' => V' (j - 1) X' z k) X :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k).differentiable.comp
      ((hV'.1 z).differentiable hsX)) X
  rw [fderiv_fun_add hd hd']
  rfl

/-- **The sum of two cleanup chains is a cleanup chain of the sum of the data.** -/
theorem IsCleanupChain.add {sX sZ A : ℕ} (hX : 1 ≤ sX) (hZ : 1 ≤ sZ)
    {f₀ f₀' : Vec 2 → Vec 2 → E} {F₀ F₀' : Vec 2 → Vec 2 → Fin 2 → E}
    {V V' : ℕ → Vec 2 → Vec 2 → Fin 2 → E} (hF : IsBoxSmooth sX sZ F₀)
    (hF' : IsBoxSmooth sX sZ F₀') (hV : IsCleanupChain sX sZ A f₀ F₀ V)
    (hV' : IsCleanupChain sX sZ A f₀' F₀' V') :
    IsCleanupChain sX sZ A (fun X z => f₀ X z + f₀' X z) (fun X z k => F₀ X z k + F₀' X z k)
      (fun j X z k => V j X z k + V' j X z k) := by
  have hb := IsCleanupChain.isBoxSmooth hF hV
  have hb' := IsCleanupChain.isBoxSmooth hF' hV'
  obtain ⟨⟨W₀, hW₀, hV0⟩, hVj⟩ := hV
  obtain ⟨⟨W₀', hW₀', hV0'⟩, hVj'⟩ := hV'
  refine ⟨⟨fun X z k => W₀ X z k + W₀' X z k,
    AVRegularity.CleanupChain.isCellAntidivergence_add hZ hW₀ hW₀', ?_⟩, fun j hj1 hjA => ?_⟩
  · funext X z k
    show V 0 X z k + V' 0 X z k = F₀ X z k + F₀' X z k + (W₀ X z k + W₀' X z k)
    simp only [hV0, hV0']
    abel
  · rw [cleanupSource_add hX (hb (j - 1) (by omega)).isSlowSmooth
      (hb' (j - 1) (by omega)).isSlowSmooth]
    exact AVRegularity.CleanupChain.isCellAntidivergence_add hZ (hVj j hj1 hjA)
      (hVj' j hj1 hjA)

/-- **The negative of a cleanup chain is a cleanup chain of the negative data.** -/
theorem IsCleanupChain.neg {sX sZ A : ℕ} (hX : 1 ≤ sX) (hZ : 1 ≤ sZ)
    {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E}
    {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E} (hF : IsBoxSmooth sX sZ F₀)
    (hV : IsCleanupChain sX sZ A f₀ F₀ V) :
    IsCleanupChain sX sZ A (fun X z => -f₀ X z) (fun X z k => -F₀ X z k)
      (fun j X z k => -V j X z k) :=
  hV.clm_comp hX hZ hF.isSlowSmooth (-ContinuousLinearMap.id ℝ E)

/-- **The difference of two cleanup chains is a cleanup chain of the difference of the data.** -/
theorem IsCleanupChain.sub {sX sZ A : ℕ} (hX : 1 ≤ sX) (hZ : 1 ≤ sZ)
    {f₀ f₀' : Vec 2 → Vec 2 → E} {F₀ F₀' : Vec 2 → Vec 2 → Fin 2 → E}
    {V V' : ℕ → Vec 2 → Vec 2 → Fin 2 → E} (hF : IsBoxSmooth sX sZ F₀)
    (hF' : IsBoxSmooth sX sZ F₀') (hV : IsCleanupChain sX sZ A f₀ F₀ V)
    (hV' : IsCleanupChain sX sZ A f₀' F₀' V') :
    IsCleanupChain sX sZ A (fun X z => f₀ X z - f₀' X z) (fun X z k => F₀ X z k - F₀' X z k)
      (fun j X z k => V j X z k - V' j X z k) := by
  have hFn : IsBoxSmooth sX sZ (fun X z k => -F₀' X z k) := hF'.neg
  have h := IsCleanupChain.add hX hZ hF hFn hV (IsCleanupChain.neg hX hZ hF' hV')
  simp only [sub_eq_add_neg]
  exact h

end AVRegularity.CycleComparison.Reconstruction
end
end
