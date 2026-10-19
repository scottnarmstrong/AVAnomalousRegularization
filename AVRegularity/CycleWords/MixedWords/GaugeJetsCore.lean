-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.ConstructedFullGalerkinAllOrderEnergy
public import AVRegularity.CycleWords.MixedWords.CellDriftRegGalerkin
import AVRegularity.CycleEvolution.FibreAdjointRowPairingNormalization
import AVRegularity.CycleDamping.ReferenceTimeEquation
import AVRegularity.Analysis.Convolution
import AVRegularity.Proofs.GenSem.CoeffArr.Mean
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! **Smallness-free energy of the reduced transverse Galerkin system**.

For the finite transverse system `cellTransverseGalerkinOperator` (diffusion
`D_θ·(G D_θ ·)`, potential `-i (√η ξ·v)`, scalar `κ`), at every order `K` and with no smallness of
`|ξ|`:

  `2⟪lift_K (T u), lift_K u⟫ + ½ ‖lift_{K+1} u‖² ≤ Γ ‖lift_K u‖²`,

with `Γ = 264 Σ|θ_i|² + 2 P_K + 2 k + ½` for `K ≥ 1` (`P_K` the `H^K` norm of the potential as a
multiplier, from its jets) and `Γ = 264 Σ|θ_i|² + 2 k + 1 + (C_w |ξ|)² + ½` for `K = 0`. The
commutator of the potential at order `K` is bounded by its multiplier norm and goes into `Γ`; it is
never absorbed into the dissipation, so no smallness of `|ξ|` is needed.

For `ξ = 0` there is no shift and no potential, and `Γ` reduces to the scalar part; for `K = 0`
this is the `L²` energy with the `H¹` dissipation. -/

/-- The `H^K` multiplier price of a coefficient with jet bounds `A` (the constant of
`KernelEnergy.torusMultiplier_norm_bound` at radius `1`). -/
def transverseRegMultiplierPrice (K : ℕ) (A : Fin (K + 1) → ℝ) : ℝ :=
  (∑ l : Fin (K + 1), factorialRootWeight 1 l.val * A l) *
    Real.sqrt (factorialWeightMax 1 K) / Real.sqrt (factorialWeightMin 1 K)

theorem transverseRegMultiplierPrice_nonneg (K : ℕ) (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l) :
    0 ≤ transverseRegMultiplierPrice K A := by
  have hs : 0 ≤ ∑ l : Fin (K + 1), factorialRootWeight 1 l.val * A l :=
    Finset.sum_nonneg fun l _ => mul_nonneg (by unfold factorialRootWeight; positivity) (hA l)
  exact div_nonneg (mul_nonneg hs (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

section Energy

variable (K : ℕ) (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
  (hc : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (v t))
  (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x,
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
  (κ : ℝ → ℂ)

/-- The potential is bounded on `H^K` by its multiplier price. -/
theorem transverseRegMultiplier_norm_le (t : ℝ) (u : TorusHk K ℂ) :
    ‖torusNormalizedDriftWindowMultiplierCLM a b η hv ξ hc A hA hb t u‖ ≤
      transverseRegMultiplierPrice K A * ‖u‖ :=
  KernelEnergy.torusMultiplier_norm_bound
    (windowCoefficient a b (normalizedDriftCoefficient η v ξ) t)
    (windowCoefficient_contDiff a b K _
      (fun t ht => normalizedDriftCoefficient_contDiff η v ξ t K (hc t ht)) t)
    (windowCoefficient_periodic a b _ (fun t _ => normalizedDriftCoefficient_periodic η hv ξ t) t)
    A (windowCoefficient_derivative_bound a b K _ A hA hb t) 1 (by norm_num) u

/-- **Order-`K` energy of the transverse generator on smooth periodic functions.** -/
theorem transverseRegSmooth_energy (hG : IsCellMetric (fun t _ => G t)) (t k : ℝ)
    (hk : ‖κ t‖ ≤ k) (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) :
    2 * inner ℝ (torusHigherTransverseWindowSourceCLM K a b η G hv ξ hc A hA hb κ t
        (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
      (1 / 2) * (‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 -
        ‖torusHkValueCLM
          (finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)‖ ^ 2) ≤
      (264 * (∑ i, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2) + 2 * transverseRegMultiplierPrice K A + 2 * k) *
        ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 := by
  have htr : truncateTorusHk (by omega : K ≤ K + 2)
      (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) =
      finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp :=
    finiteSmoothPeriodicHk_truncate (by omega) f hf hp
  have hd := finiteSmoothHigherDiffusion_energy K f hf hp G hG
    (fun j => (Real.sqrt η : ℂ) * ξ j) t
  have hg := finiteSmoothHigherGradientEnergy_native_identity K f hf hp
  have hg0 := finiteSmoothHigherGradientEnergy_nonneg K f hf hp
  let Fk := finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp
  let M := torusNormalizedDriftWindowMultiplierCLM a b η hv ξ hc A hA hb t Fk
  have hM : -inner ℝ (torusHigherScalarCLM K Complex.I M) Fk ≤
      transverseRegMultiplierPrice K A * ‖Fk‖ ^ 2 := by
    have h1 := real_inner_le_norm (-(torusHigherScalarCLM K Complex.I M)) Fk
    rw [inner_neg_left, norm_neg, torusHigherScalarCLM_norm, Complex.norm_I, one_mul] at h1
    have h2 := mul_le_mul_of_nonneg_right
      (transverseRegMultiplier_norm_le K a b η hv ξ hc A hA hb t Fk) (norm_nonneg Fk)
    exact h1.trans (h2.trans_eq (by ring))
  have hκ : inner ℝ (torusHigherScalarCLM K (κ t) Fk) Fk ≤ k * ‖Fk‖ ^ 2 := by
    have h1 := real_inner_le_norm (torusHigherScalarCLM K (κ t) Fk) Fk
    rw [torusHigherScalarCLM_norm] at h1
    exact h1.trans (by nlinarith [norm_nonneg Fk])
  simp only [torusHigherTransverseWindowSourceCLM, add_apply,
    sub_apply, ContinuousLinearMap.comp_apply, inner_add_left,
    inner_sub_left, htr]
  change 2 * (inner ℝ (torusHigherStrongDiffusionCLM K G (fun j => (Real.sqrt η : ℂ) * ξ j) t
      (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)) Fk -
    inner ℝ (torusHigherScalarCLM K Complex.I M) Fk + inner ℝ (torusHigherScalarCLM K (κ t) Fk) Fk) +
      (1 / 2) * (‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 -
        ‖torusHkValueCLM
          (finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)‖ ^ 2) ≤ _
  rw [hg]
  linarith only [hd, hg0, hM, hκ]

end Energy

section Galerkin

variable (N : ℕ) (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
  (ξ : Fin 2 → ℂ) (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
  (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x,
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
  (κ : ℝ → ℂ)

/-- **Order-`K` energy of the finite transverse system, `K ≥ 1`.** -/
theorem transverseRegGalerkin_higher_energy (hG : IsCellMetric (fun t _ => G t)) (Cw : ℝ)
    (hCw : 0 ≤ Cw) (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {K : ℕ} (hK : 1 ≤ K)
    (hcK : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (v t)) (AK : Fin (K + 1) → ℝ) (hAK : ∀ l, 0 ≤ AK l)
    (hbK : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ AK l)
    (t k : ℝ) (ht : t ∈ Icc a b) (hk : ‖κ t‖ ≤ k) (u : CellGalerkinSpace (E := ℂ) N) :
    2 * inner ℝ (cellGalerkinNativeLiftCLM N K
        (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t u))
        (cellGalerkinNativeLiftCLM N K u) +
      (1 / 2) * ‖cellGalerkinNativeLiftCLM N (K + 1) u‖ ^ 2 ≤
      (264 * (∑ i, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2) + 2 * transverseRegMultiplierPrice K AK +
        2 * k + 1 / 2) * ‖cellGalerkinNativeLiftCLM N K u‖ ^ 2 := by
  have hl : rangeSmoothFourierLiftCLM (E := ℂ) hK N
      (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t u) =
      galerkinProj N (torusHigherTransverseWindowSourceCLM K a b η G hv ξ hcK AK hAK hbK κ t
        (rangeSmoothFourierLiftCLM (E := ℂ) (by omega : 1 ≤ K + 2) N u)) := by
    rw [cellTransverseGalerkinOperator_higher_value N a b η G hv ξ hc A hA hb κ Cw hCw hw K hcK
      AK hAK hbK t ht u, cellGalerkinL2Initial_higher_lift hK N]
    rfl
  have hpair : inner ℝ (rangeSmoothFourierLiftCLM (E := ℂ) hK N
      (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t u))
      (rangeSmoothFourierLiftCLM (E := ℂ) hK N u) =
      inner ℝ (torusHigherTransverseWindowSourceCLM K a b η G hv ξ hcK AK hAK hbK κ t
        (rangeSmoothFourierLiftCLM (E := ℂ) (by omega : 1 ≤ K + 2) N u)) (rangeSmoothFourierLiftCLM (E := ℂ) hK N u) := by
    exact (congrArg (fun z : TorusHk K ℂ => inner ℝ z (rangeSmoothFourierLiftCLM (E := ℂ) hK N u))
      hl).trans (torusHigherProjection_retained_inner K N _ _ (rangeSmoothFourierLift_fixed hK N u))
  have he := cellGalerkinSmoothEnergyTransfer hK N u
    (torusHigherTransverseWindowSourceCLM K a b η G hv ξ hcK AK hAK hbK κ t) _
    (transverseRegSmooth_energy K a b η G hv ξ hcK AK hAK hbK κ hG t k hk
      (cellGalerkinSmoothValue N u) (cellGalerkinSmoothValue_contDiff N u)
      (cellGalerkinSmoothValue_periodic N u))
  have hv' := pow_le_pow_left₀ (norm_nonneg (cellGalerkinValue N u))
    (cellGalerkinRangeHigher_value_norm_le hK N u) 2
  have hp := energyGradientDifference_absorb hv'
    ((congrArg (fun x : ℝ => 2 * x + (1 / 2) *
      (‖rangeSmoothFourierLiftCLM (E := ℂ) (by omega : 1 ≤ K + 1) N u‖ ^ 2 -
        ‖cellGalerkinValue N u‖ ^ 2)) hpair).le.trans he)
  simpa only [cellGalerkinNativeLiftCLM_eq_range hK,
    cellGalerkinNativeLiftCLM_eq_range (by omega : 1 ≤ K + 1)] using hp

/-- **`L²` energy of the finite transverse system** (order `0`, with the `H¹` dissipation). -/
theorem transverseRegGalerkin_zeroth_energy (hG : IsCellMetric (fun t _ => G t)) (Cw : ℝ)
    (hCw : 0 ≤ Cw) (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (t k : ℝ) (ht : t ∈ Icc a b) (hk : ‖κ t‖ ≤ k)
    (u : CellGalerkinSpace (E := ℂ) N) :
    2 * inner ℝ (cellGalerkinNativeLiftCLM N 0
        (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t u))
        (cellGalerkinNativeLiftCLM N 0 u) +
      (1 / 2) * ‖cellGalerkinNativeLiftCLM N (0 + 1) u‖ ^ 2 ≤
      (264 * (∑ i, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2) + 2 * k + 1 + (Cw * fibreNorm ξ) ^ 2 + 1 / 2) *
        ‖cellGalerkinNativeLiftCLM N 0 u‖ ^ 2 := by
  let src := -cellScalarCLM Complex.I
    (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t (cellGalerkinValue N u))
  have hp := cellTransverseGalerkinOperator_test_pairing N a b η G hG hv ξ hc A hA hb κ
    Cw hCw hw t ht u u
  rw [cellDualDerivative_pairing] at hp
  have he := cellZeroDrift_generator_scalar_source_energy G hG
    (fun j => (Real.sqrt η : ℂ) * ξ j) κ t u.val src
  have hs : ‖src‖ ≤ Cw * fibreNorm ξ * ‖cellGalerkinValue N u‖ := by
    dsimp only [src]
    rw [norm_neg, cellScalarCLM_norm, Complex.norm_I, one_mul]
    exact cellFibreDriftCouplingCLM_apply_norm_le η Cw hCw hv hw ξ t (cellGalerkinValue N u)
  have hs2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (mul_nonneg hCw (fibreNorm_nonneg ξ)) (norm_nonneg _))).mpr hs
  rw [mul_pow] at hs2
  have hkk := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg ‖cellGalerkinValue N u‖)
  have hd : 0 ≤ ∑ j : Fin 2, ‖cellDerivativeCLM j u.val‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hval : torusHkValueCLM u.val = cellGalerkinValue N u := rfl
  rw [hval] at he
  have hP : 2 * (cellGeneratorForm ⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ hG 0
      measurable_const (by intro t x; simp) t u.val u.val +
      cellSourceFunctional (fun j => (Real.sqrt η : ℂ) * ξ j) src 0 u.val) +
      (3 / 4) * ∑ j, ‖cellDerivativeCLM j u.val‖ ^ 2 ≤
      (264 * (∑ i, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2) + 2 * k + 1 + (Cw * fibreNorm ξ) ^ 2) *
        ‖cellGalerkinValue N u‖ ^ 2 := by
    nlinarith only [he, hs2, hkk]
  have hab := zerothGradientEnergy_absorb hd (cellH1_norm_sq u.val) (hval ▸ hP)
  rw [torusH0_inner_value, cellGalerkinNativeLiftCLM_value, cellGalerkinNativeLiftCLM_value,
    cellGalerkinNativeLiftCLM_zero_norm_sq, zero_add, cellGalerkinNativeLiftCLM_one, hp]
  exact hab

end Galerkin

/-- The jet budget of the potential at order `K` on frequencies `|ξ| ≤ ρ`. -/
def transverseRegJetPrice (K : ℕ) (ρ : ℝ) (J : ℕ → ℝ) : Fin (K + 1) → ℝ :=
  fun l => ((Fintype.card (DerivativeWord2 l.val) : ℝ) * 2 * J l.val) * ρ

/-- **The growth constant of the order-`K` energy**, depending only on `K, ρ, C_w, J`. -/
def transverseRegGamma (K : ℕ) (ρ Cw : ℝ) (J : ℕ → ℝ) : ℝ :=
  264 * ρ ^ 2 + 2 * transverseRegMultiplierPrice K (transverseRegJetPrice K ρ J) + 1 +
    (Cw * ρ) ^ 2 + 1 / 2

theorem transverseRegJetPrice_nonneg (K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (J : ℕ → ℝ)
    (hJ : ∀ l, 0 ≤ J l) (l : Fin (K + 1)) : 0 ≤ transverseRegJetPrice K ρ J l :=
  mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by norm_num)) (hJ _)) hρ

theorem transverseRegGamma_nonneg (K : ℕ) (ρ Cw : ℝ) (hρ : 0 ≤ ρ) (J : ℕ → ℝ)
    (hJ : ∀ l, 0 ≤ J l) : 0 ≤ transverseRegGamma K ρ Cw J := by
  have := transverseRegMultiplierPrice_nonneg K _ (transverseRegJetPrice_nonneg K ρ hρ J hJ)
  unfold transverseRegGamma
  positivity

theorem transverseRegMultiplierPrice_mono (K : ℕ) (A A' : Fin (K + 1) → ℝ)
    (hAA : ∀ l, A l ≤ A' l) :
    transverseRegMultiplierPrice K A ≤ transverseRegMultiplierPrice K A' := by
  unfold transverseRegMultiplierPrice
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
  exact Finset.sum_le_sum fun l _ =>
    mul_le_mul_of_nonneg_left (hAA l) (by unfold factorialRootWeight; positivity)

/-- The twisted frequency is at most the fibre frequency. -/
theorem transverseRegTheta_sq_le (η : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (ξ : Fin 2 → ℂ) (ρ : ℝ)
    (hξ : fibreNorm ξ ≤ ρ) : ∑ i, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2 ≤ ρ ^ 2 := by
  have hs : ∑ i, ‖ξ i‖ ^ 2 = fibreNorm ξ ^ 2 := by
    rw [fibreNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hle : ∑ i, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2 ≤ ∑ i, ‖ξ i‖ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hη0]
    exact mul_le_of_le_one_left (sq_nonneg _) hη
  exact (hle.trans_eq hs).trans (pow_le_pow_left₀ (fibreNorm_nonneg ξ) hξ 2)

/-- **Smallness-free order-`K` energy of the finite transverse system** (no scalar `κ`), with the
constant `transverseRegGamma K ρ C_w J`. -/
theorem transverseRegGalerkin_energy (K N : ℕ) (a b η : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (ρ : ℝ)
    (hξ : fibreNorm ξ ≤ ρ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hfull : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) (J : ℕ → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (t : ℝ) (ht : t ∈ Icc a b) (u : CellGalerkinSpace (E := ℂ) N) :
    2 * inner ℝ (cellGalerkinNativeLiftCLM N K
        (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb (fun _ => 0) t u))
        (cellGalerkinNativeLiftCLM N K u) +
      (1 / 2) * ‖cellGalerkinNativeLiftCLM N (K + 1) u‖ ^ 2 ≤
      transverseRegGamma K ρ Cw J * ‖cellGalerkinNativeLiftCLM N K u‖ ^ 2 := by
  have hθ := transverseRegTheta_sq_le η hη0 hη ξ ρ hξ
  have hρ : 0 ≤ ρ := (fibreNorm_nonneg ξ).trans hξ
  have hk : ‖(fun _ : ℝ => (0 : ℂ)) t‖ ≤ 0 := by simp
  have hJ0 : ∀ l, 0 ≤ J l := fun l => (norm_nonneg _).trans (hj l t ht 0)
  have hP := transverseRegMultiplierPrice_nonneg K _ (transverseRegJetPrice_nonneg K ρ hρ J hJ0)
  have hCwξ : (Cw * fibreNorm ξ) ^ 2 ≤ (Cw * ρ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hCw (fibreNorm_nonneg ξ)) (mul_le_mul_of_nonneg_left hξ hCw) 2
  cases K with
  | zero =>
    have he := transverseRegGalerkin_zeroth_energy N a b η G hv ξ hc A hA hb (fun _ => 0) hG Cw
      hCw hw t 0 ht hk u
    refine he.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    unfold transverseRegGamma
    linarith only [hθ, hP, hCwξ]
  | succ K =>
    have hcK : ∀ t ∈ Icc a b, ContDiff ℝ ((K + 1 : ℕ) : ℕ) (v t) :=
      fun t ht => (hfull t ht).of_le (by exact_mod_cast le_top)
    have hbK := normalizedDriftJetBudget_window_bound (K + 1) a b η v ξ hcK (fun l => J l.val)
      (fun l t ht x => hj l.val t ht x)
    have he := transverseRegGalerkin_higher_energy N a b η G hv ξ hc A hA hb (fun _ => 0) hG Cw
      hCw hw (by omega : 1 ≤ K + 1) hcK _
      (normalizedDriftJetBudget_nonneg (K + 1) (fun l => J l.val) ξ (fun l => hJ0 l.val)) hbK
      t 0 ht hk u
    have hmono := transverseRegMultiplierPrice_mono (K + 1)
      (normalizedDriftJetBudget (K + 1) (fun l => J l.val) ξ) (transverseRegJetPrice (K + 1) ρ J)
      (fun l => by
        unfold normalizedDriftJetBudget transverseRegJetPrice
        exact mul_le_mul_of_nonneg_left hξ (mul_nonneg (mul_nonneg (by positivity) (by norm_num))
          (hJ0 _)))
    refine he.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    unfold transverseRegGamma
    nlinarith only [hθ, hmono, sq_nonneg (Cw * ρ)]

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # from the Galerkin steps to the weak curve (Steps 5, 6)

Copies of `constructedActualWeak_native_short_propagation` and
`constructedActualWeak_native_polynomial_smoothing` with the Galerkin window and smoothing as
hypotheses.  The passage Galerkin → weak solution is `cellActualWeak_native_of_finite_bound`. -/

theorem cellDriftWeakShort (hW : GalerkinWindow) : WeakShort := by
  intro J R P hR hP G hG v hv V hb θ hθ a b hab hJ U slice hU initial hi hshort
  have hθ' := cellDrift_theta_le hθ
  apply AVRegularity.CycleWords.cellActualWeak_native_of_finite_bound hab
    ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V 0 hv.1 hb measurable_const
    (fun _ => by simp) (torusHkValueCLM initial) U slice hU hi J b ⟨hab.le, le_rfl⟩
    (Real.exp 1 * ‖initial‖ ^ 2) (mul_nonneg (Real.exp_pos 1).le (sq_nonneg _))
  intro N y hy hyinit
  have he := (hW J N R P hR hP G hG hv V hb (fun k => (θ k : ℂ)) hθ' hab.le hJ y hy hshort J le_rfl).1
  have hi' : cellGalerkinNativeLiftCLM N J (y a) =
      cellGalerkinNativeLiftCLM N J (cellGalerkinL2Initial N (torusHkValueCLM initial)) := by
    apply TorusHk.ext_value
    change torusHkValueCLM (cellGalerkinNativeLiftCLM N J (y a)) =
      torusHkValueCLM (cellGalerkinNativeLiftCLM N J
        (cellGalerkinL2Initial N (torusHkValueCLM initial)))
    simpa only [cellGalerkinNativeLiftCLM_value] using hyinit
  have hn : ‖cellGalerkinNativeLiftCLM N J (y a)‖ ≤ ‖initial‖ := by
    rw [hi']
    exact cellGalerkinHigherInitial_norm_le N J initial
  exact he.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hn 2) (Real.exp_pos 1).le)

theorem cellDriftWeakSmoothing (hS : GalerkinSmoothing) : WeakSmoothing := by
  intro J R P hR hP G hG v hv V hb θ hθ a b hab hJ U slice hU _ t ht hat
  have hM := cellDriftWindowPrice_one_le J R hR
  set M := cellDriftWindowPrice J R with hMdef
  have hMP : 0 < ((J : ℝ) + 1) * M * P ^ 2 := by positivity
  have hX : 0 ≤ Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * M := by
    have := Real.exp_pos 1
    positivity
  set T := cellDriftSmoothingTime J R P with hT
  have hT0 : 0 < T := by rw [hT]; unfold cellDriftSmoothingTime; positivity
  apply AVRegularity.CycleWords.cellActualWeak_native_of_finite_bound hab
    ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V 0 hv.1 hb measurable_const
    (fun _ => by simp) (U a) U slice hU rfl J t ht
    ((Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * M * P ^ 2) ^ J * ‖U a‖ ^ 2)
    (mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))
  intro N y hy hyinit
  have hbudget : M * P ^ 2 * T ≤ 1 := by
    have : M * P ^ 2 * T = 1 / ((J : ℝ) + 1) := by
      rw [hT]; unfold cellDriftSmoothingTime; rw [← hMdef]; field_simp
    rw [this]
    exact (div_le_one (by positivity)).mpr (by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)])
  have he := hS J N R P hR hP G hG hv V hb θ hθ hab.le hJ y hy T hT0 hbudget t hat ht.2
  have hrate : Real.exp 1 * (2 * Real.exp 1) / T =
      Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * M * P ^ 2 := by
    rw [hT]; unfold cellDriftSmoothingTime; rw [← hMdef]; field_simp
  rw [hrate] at he
  have hi : ‖cellGalerkinValue N (y a)‖ ^ 2 ≤ ‖U a‖ ^ 2 := by
    rw [hyinit]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (cellGalerkinL2Initial_norm_le N (U a))
  exact he.trans (mul_le_mul_of_nonneg_left hi (pow_nonneg (by positivity) _))

end AVRegularity.CycleWords.Assembly
end

section
namespace AVRegularity.CycleWords.Assembly

/-! # polynomial regularity of the cell equation with a smooth drift

The chain: order-`K` Galerkin energy (`cellDriftGalerkinEnergy`) → short window
(`cellDriftGalerkinWindow`) → smoothing with the `L²` contraction (`cellDriftGalerkinSmoothing`) →
weak short propagation and smoothing (`cellDriftWeakShort`, `cellDriftWeakSmoothing`) → (G), (S)
(`cellDriftAssembly`, with `cellDriftWeakContraction`). -/

/-- **Polynomial regularity of the cell equation with a smooth drift**. -/
theorem cellDriftRegularity : CellDriftRegularityStatement := by
  have hW := cellDriftGalerkinWindow cellDriftGalerkinEnergy
  exact cellDriftAssembly (cellDriftWeakShort hW)
    (cellDriftWeakSmoothing (cellDriftGalerkinSmoothing hW cellDriftGalerkinContraction))
    cellDriftWeakContraction

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Filter Topology Homogenization AVRegularity.CycleEvolution
open AVRegularity.CycleWords AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The phase integral on the graph disc

For the symbol of a `FibreScalarData`, the phase integral `Ξ(ξ) = ∫_a^b λ(ξ)` is analytic on the
whole disc `|ξ| < ξ₀` (`phaseIntegral_analyticOnNhd`): at `ξ₁` the coefficients rescaled by
`ξ*_i = |ξ₁,i| + ε` (with `|ξ*| < ξ₀`) form a series absolutely convergent on the unit polydisc,
which is analytic by `fibreBoundedTimeIntegratedSeries_analyticOnNhd`, and a neighbourhood of
`ξ₁` maps into it. It is quadratic, `|Ξ(ζ)| ≤ (b-a)(8 + C_w C_g)|ζ|²`
(`phaseIntegral_norm_le`), and for real `ξ` the gauge is bounded, `|e^Ξ| ≤ 1 + C_g|ξ|`
(`gauge_norm_le_of_real`, from `real_ratio` and the mean of the graph). -/

variable {K : ScalarConstants} {η t0 S : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2}

local instance gaugeAnalyticProbCube :
    IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- The phase integral `ξ ↦ ∫_a^b λ(ξ)` of a symbol family. -/
def phaseIntegral (lam : ℕ × ℕ → ℝ → ℂ) (a b : ℝ) (ξ : Fin 2 → ℂ) : ℂ :=
  ∫ τ in a..b, fibreSeriesC lam ξ τ

theorem blockGauge_eq_phaseIntegral (lam : ℕ × ℕ → ℝ → ℂ) (η a b : ℝ) (θ : Vec 2) :
    blockGauge lam η a b θ = phaseIntegral lam a b (planeFibreFrequency η θ) := rfl

/-- The symbol is integrable on bounded intervals inside the graph disc. -/
theorem symbol_integrableOn (data : FibreScalarData K η G v t0 S) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    {ξ : Fin 2 → ℂ} (hξ : fibreNorm ξ < K.ξ0) (a b : ℝ) :
    IntegrableOn (fibreSeriesC data.lam ξ) (Ioc a b) := by
  refine Integrable.mono' (g := fun _ => (8 + K.Cw * K.Cg) * fibreNorm ξ ^ 2)
    (integrable_const _)
    ((CycleDamping.graph_symbol_aestronglyMeasurable hG hv data.graph ξ hξ).restrict) ?_
  exact Eventually.of_forall fun τ =>
    scalarPackageSymbol_quadratic_bound data hη0 hη1 hCg hCw hG hv hw ξ hξ τ

/-- **The phase integral is quadratic** on the graph disc. -/
theorem phaseIntegral_norm_le (data : FibreScalarData K η G v t0 S) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    {a b : ℝ} (hab : a ≤ b) {ζ : Fin 2 → ℂ} (hζ : fibreNorm ζ < K.ξ0) :
    ‖phaseIntegral data.lam a b ζ‖ ≤ (b - a) * ((8 + K.Cw * K.Cg) * fibreNorm ζ ^ 2) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (C := (8 + K.Cw * K.Cg) * fibreNorm ζ ^ 2) (f := fibreSeriesC data.lam ζ)
    (fun τ _ => scalarPackageSymbol_quadratic_bound data hη0 hη1 hCg hCw hG hv hw ζ hζ τ)
  rw [abs_of_nonneg (sub_nonneg.2 hab)] at h
  rw [phaseIntegral, mul_comm (b - a)]
  exact h

/-- **The phase integral is analytic on the graph disc.** -/
theorem phaseIntegral_analyticOnNhd (data : FibreScalarData K η G v t0 S) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t))
    (hv : IsCellDrift v) (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    {a b : ℝ} (hab : a ≤ b) :
    AnalyticOnNhd ℂ (phaseIntegral data.lam a b) {ξ | fibreNorm ξ < K.ξ0} := by
  intro ξ₁ hξ₁
  change fibreNorm ξ₁ < K.ξ0 at hξ₁
  -- a radius vector strictly beyond `|ξ₁|`, inside the disc
  have hcont : Continuous (fun ε : ℝ => Real.sqrt (∑ i, (‖ξ₁ i‖ + ε) ^ 2)) := by fun_prop
  have h0 : Real.sqrt (∑ i, (‖ξ₁ i‖ + 0) ^ 2) < K.ξ0 := by simpa [fibreNorm] using hξ₁
  obtain ⟨ε, hεlt, hεpos⟩ := ((eventually_nhdsWithin_of_eventually_nhds
    ((hcont.tendsto 0).eventually (gt_mem_nhds h0))).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
  change 0 < ε at hεpos
  have hpos : ∀ i, 0 < ‖ξ₁ i‖ + ε := fun i => by positivity
  set ξs : Fin 2 → ℂ := fun i => ((‖ξ₁ i‖ + ε : ℝ) : ℂ) with hξs
  have hnξs : ∀ i, ‖ξs i‖ = ‖ξ₁ i‖ + ε := fun i => by
    simp only [hξs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos i)]
  have hξsn : fibreNorm ξs < K.ξ0 := by
    have : fibreNorm ξs = Real.sqrt (∑ i, (‖ξ₁ i‖ + ε) ^ 2) := by
      simp only [fibreNorm, hnξs]
    rw [this]
    exact hεlt
  have hξs0 : ∀ i, ξs i ≠ 0 := fun i h => by
    have := hnξs i
    rw [h, norm_zero] at this
    linarith [hpos i]
  -- the rescaled coefficients converge on the unit polydisc
  set a' : ℕ × ℕ → ℝ → ℂ := fun p t => fibreMonomial ξs p * data.lam p t with ha'def
  have ha' : (∑' p, fibreCoefficientWeight (((1 : ℝ≥0) : ℝ≥0∞)) p * ⨆ t, ‖a' p t‖ₑ) < ⊤ := by
    have h := (data.graph.2.1 ξs hξsn).2.1
    have heq : ∀ p, fibreCoefficientWeight (((1 : ℝ≥0) : ℝ≥0∞)) p * ⨆ t, ‖a' p t‖ₑ =
        ENNReal.ofReal ‖fibreMonomial ξs p‖ * ⨆ t, ‖data.lam p t‖ₑ := by
      intro p
      simp only [fibreCoefficientWeight, ENNReal.coe_one, one_pow, one_mul, ha'def, enorm_mul,
        ofReal_norm, ENNReal.mul_iSup]
    rw [tsum_congr heq]
    exact h
  set Φ := fibreBoundedTimeIntegratedSeries (volume.restrict (Ioc a b)) a' 1 one_pos ha'
    with hΦ
  have hΦa : AnalyticOnNhd ℂ Φ (Metric.ball 0 ((1 : ℝ≥0) : ℝ)) :=
    fibreBoundedTimeIntegratedSeries_analyticOnNhd _ a' 1 one_pos ha'
  -- the rescaling map
  set Λ : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
    ContinuousLinearMap.pi fun i => (ξs i)⁻¹ • ContinuousLinearMap.proj i with hΛ
  have hΛapp : ∀ ξ i, Λ ξ i = (ξs i)⁻¹ * ξ i := fun ξ i => by simp [hΛ]
  have hmono : ∀ ξ p, fibreMonomial (Λ ξ) p * fibreMonomial ξs p = fibreMonomial ξ p := by
    intro ξ p
    simp only [fibreMonomial, hΛapp]
    rw [show ((ξs 0)⁻¹ * ξ 0) ^ p.1 * ((ξs 1)⁻¹ * ξ 1) ^ p.2 * (ξs 0 ^ p.1 * ξs 1 ^ p.2) =
        ((ξs 0)⁻¹ * ξs 0 * ξ 0) ^ p.1 * ((ξs 1)⁻¹ * ξs 1 * ξ 1) ^ p.2 by ring,
      inv_mul_cancel₀ (hξs0 0), inv_mul_cancel₀ (hξs0 1), one_mul, one_mul]
  have hseries : ∀ ξ, fibreSeriesC a' (Λ ξ) = fibreSeriesC data.lam ξ := by
    intro ξ
    funext t
    simp only [fibreSeriesC, ha'def]
    refine tsum_congr fun p => ?_
    rw [← mul_assoc, hmono]
  have hΛ1 : Λ ξ₁ ∈ Metric.ball (0 : Fin 2 → ℂ) ((1 : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_one, mem_ball_zero_iff, pi_norm_lt_iff one_pos]
    intro i
    rw [hΛapp, norm_mul, norm_inv, hnξs, inv_mul_lt_iff₀ (hpos i), mul_one]
    linarith
  set V : Set (Fin 2 → ℂ) :=
    Λ ⁻¹' Metric.ball 0 ((1 : ℝ≥0) : ℝ) ∩ {ξ | fibreNorm ξ < K.ξ0} with hV
  have hVo : IsOpen V :=
    (Metric.isOpen_ball.preimage Λ.continuous).inter
      (isOpen_lt fibreNorm_continuous continuous_const)
  have heq : Φ ∘ Λ =ᶠ[𝓝 ξ₁] phaseIntegral data.lam a b := by
    filter_upwards [hVo.mem_nhds ⟨hΛ1, hξ₁⟩] with ξ hξ
    have hball : ‖Λ ξ‖ ≤ ((1 : ℝ≥0) : ℝ) := (mem_ball_zero_iff.1 hξ.1).le
    have hint : Integrable (fibreSeriesC a' (Λ ξ)) (volume.restrict (Ioc a b)) := by
      rw [hseries]
      exact symbol_integrableOn data hη0 hη1 hCg hCw hG hv hw hξ.2 a b
    simp only [Function.comp_apply, hΦ]
    rw [fibreBoundedTimeIntegratedSeries_eq_integral _ a' 1 one_pos ha' (Λ ξ) hball hint,
      hseries, phaseIntegral, intervalIntegral.integral_of_le hab]
  exact ((hΦa (Λ ξ₁) hΛ1).comp (Λ.analyticAt ξ₁)).congr heq

/-- The constant `1` has cell `L²` norm at most one. -/
theorem cellL2Norm_one_le : cellL2Norm (fun _ : Vec 2 => (1 : ℂ)) ≤ 1 := by
  unfold cellL2Norm
  have hμ : (volume.restrict AVenhance.unitCube : Measure (Vec 2)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, cellCube_volume_one]
    exact one_ne_zero
  rw [eLpNorm_const _ (by norm_num) hμ, Measure.restrict_apply_univ, cellCube_volume_one]
  simp

/-- The graph `1 + r` has cell `L²` norm at least one (its mean is one). -/
theorem one_le_cellL2Norm_graph (data : FibreScalarData K η G v t0 S) {ξ : Fin 2 → ℂ}
    (hξ : fibreNorm ξ < K.ξ0) (t : ℝ) :
    1 ≤ cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet data.r ξ) t x) := by
  have hmem : MemLp (fun x => 1 + cellValue (fibreSeriesJet data.r ξ) t x) 2
      (volume.restrict AVenhance.unitCube) :=
    MemLp.add (memLp_const (1 : ℂ)) (scalarPackageGraph_memLp data ξ hξ t)
  have h := cellMean_enorm_le_cellL2Norm
    (fun x => 1 + cellValue (fibreSeriesJet data.r ξ) t x) hmem
  have hm : cellMean (fun x => 1 + cellValue (fibreSeriesJet data.r ξ) t x) = 1 :=
    scalarPackageGraph_mean_one data ξ hξ t
  rwa [hm, enorm_one] at h

/-- The graph `1 + r` has cell `L²` norm at most `1 + C_g|ξ|`. -/
theorem cellL2Norm_graph_le (data : FibreScalarData K η G v t0 S) {ξ : Fin 2 → ℂ}
    (hξ : fibreNorm ξ < K.ξ0) (hCg : 0 ≤ K.Cg) (s : ℝ) :
    cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet data.r ξ) s x) ≤
      ENNReal.ofReal (1 + K.Cg * fibreNorm ξ) := by
  have h1 : cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet data.r ξ) s x) ≤
      cellL2Norm (fun _ : Vec 2 => (1 : ℂ)) +
        cellL2Norm (cellValue (fibreSeriesJet data.r ξ) s) :=
    eLpNorm_add_le (f := fun _ : Vec 2 => (1 : ℂ))
      (g := cellValue (fibreSeriesJet data.r ξ) s) one_le_two
  have h2 : cellL2Norm (cellValue (fibreSeriesJet data.r ξ) s) ≤
      ENNReal.ofReal (K.Cg * fibreNorm ξ) :=
    (cellValue_cellL2Norm_le_energy _ s).trans (data.graph.2.1 ξ hξ).2.2.2.2
  have h3 : ENNReal.ofReal (1 + K.Cg * fibreNorm ξ) = 1 + ENNReal.ofReal (K.Cg * fibreNorm ξ) := by
    rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hCg (fibreNorm_nonneg ξ)), ENNReal.ofReal_one]
  rw [h3]
  exact h1.trans (add_le_add cellL2Norm_one_le h2)

/-- **The gauge is bounded for real frequencies**: `|e^{∫_s^t λ}| ≤ 1 + C_g|ξ|`. -/
theorem gauge_norm_le_of_real (data : FibreScalarData K η G v t0 S) {ξ : Fin 2 → ℂ}
    (hre : ∀ i, (ξ i).im = 0) (hξ : fibreNorm ξ < K.ξ0) (hCg : 0 ≤ K.Cg) {s t : ℝ}
    (hst : s ≤ t) :
    ‖Complex.exp (∫ τ in s..t, fibreSeriesC data.lam ξ τ)‖ ≤ 1 + K.Cg * fibreNorm ξ := by
  set e : ℝ≥0∞ := ENNReal.ofReal ‖Complex.exp (∫ τ in s..t, fibreSeriesC data.lam ξ τ)‖ with he
  have hratio : e * cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet data.r ξ) t x) ≤
      cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet data.r ξ) s x) :=
    (data.real_ratio ξ hre hξ s t hst).1
  have hle : e ≤ ENNReal.ofReal (1 + K.Cg * fibreNorm ξ) :=
    calc e = e * 1 := (mul_one e).symm
      _ ≤ e * cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet data.r ξ) t x) :=
          mul_le_mul_right (one_le_cellL2Norm_graph data hξ t) e
      _ ≤ _ := hratio
      _ ≤ _ := cellL2Norm_graph_le data hξ hCg s
  have hpos : 0 ≤ 1 + K.Cg * fibreNorm ξ := by
    have := mul_nonneg hCg (fibreNorm_nonneg ξ)
    linarith
  exact (ENNReal.ofReal_le_ofReal_iff hpos).1 hle

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Filter Topology Metric Homogenization AVRegularity.CycleEvolution
open AVRegularity.CycleWords AVRegularity.Analysis
namespace AVRegularity.CycleWords.Assembly

/-! # Complex derivatives of the phase integral

On the disc `|ξ| ≤ ρ < ξ₀`, Cauchy's estimate on sup-norm balls of radius `r₀ = (ξ₀ - ρ)/4` and the
quadratic bound `|Ξ(ζ)| ≤ (b-a) C_q |ζ|²` give `‖DⁿΞ(ξ)‖ ≤ (b-a) C_q ξ₀² nⁿ/r₀ⁿ`
(`phaseIntegral_iteratedFDeriv_le`); for the first derivative, balls of radius `|ξ|` give the extra
zero, `‖DΞ(ξ)‖ ≤ (b-a) C_q (9 + (ξ₀/r₀)²)|ξ|` (`phaseIntegral_fderiv_le`). -/

variable {K : ScalarConstants} {η t0 S : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2}

theorem fibreNorm_le_two_mul_norm (w : Fin 2 → ℂ) : fibreNorm w ≤ 2 * ‖w‖ := by
  have h0 := norm_le_pi_norm w 0
  have h1 := norm_le_pi_norm w 1
  have hn : 0 ≤ ‖w‖ := norm_nonneg w
  unfold fibreNorm
  rw [show 2 * ‖w‖ = Real.sqrt ((2 * ‖w‖) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_two]
  nlinarith [norm_nonneg (w 0), norm_nonneg (w 1)]

theorem fibreNorm_le_of_mem_closedBall {ξ ζ : Fin 2 → ℂ} {r : ℝ} (h : ζ ∈ closedBall ξ r) :
    fibreNorm ζ ≤ fibreNorm ξ + 2 * r := by
  have h1 := fibreNorm_add_le ξ (ζ - ξ)
  rw [add_sub_cancel] at h1
  have h2 := fibreNorm_le_two_mul_norm (ζ - ξ)
  rw [mem_closedBall, dist_eq_norm] at h
  linarith

/-- The phase integral is bounded on a sup-norm ball inside the graph disc. -/
theorem phaseIntegral_norm_le_of_closedBall (data : FibreScalarData K η G v t0 S)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw)
    (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    {a b : ℝ} (hab : a ≤ b) {ξ : Fin 2 → ℂ} {r R : ℝ} (hR : fibreNorm ξ + 2 * r ≤ R)
    (hRξ : R < K.ξ0) {ζ : Fin 2 → ℂ} (hζ : ζ ∈ closedBall ξ r) :
    ‖phaseIntegral data.lam a b ζ‖ ≤ (b - a) * ((8 + K.Cw * K.Cg) * R ^ 2) := by
  have hζR : fibreNorm ζ ≤ R := (fibreNorm_le_of_mem_closedBall hζ).trans hR
  have h := phaseIntegral_norm_le data hη0 hη1 hCg hCw hG hv hw hab (hζR.trans_lt hRξ)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 hab))
  have hq : 0 ≤ 8 + K.Cw * K.Cg := by positivity
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (fibreNorm_nonneg ζ) hζR 2) hq

/-- **The iterated derivatives of the phase integral** on the disc `|ξ| ≤ ρ < ξ₀`. -/
theorem phaseIntegral_iteratedFDeriv_le (data : FibreScalarData K η G v t0 S)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw)
    (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    {a b : ℝ} (hab : a ≤ b) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < K.ξ0) (n : ℕ) {ξ : Fin 2 → ℂ}
    (hξ : fibreNorm ξ ≤ ρ) :
    ‖iteratedFDeriv ℂ n (phaseIntegral data.lam a b) ξ‖ ≤
      (b - a) * ((8 + K.Cw * K.Cg) * K.ξ0 ^ 2) * (n : ℝ) ^ n / ((K.ξ0 - ρ) / 4) ^ n := by
  have hr₀ : 0 < (K.ξ0 - ρ) / 4 := by linarith
  have hU : IsOpen {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} :=
    isOpen_lt fibreNorm_continuous continuous_const
  have hR : fibreNorm ξ + 2 * ((K.ξ0 - ρ) / 4) ≤ (ρ + K.ξ0) / 2 := by linarith
  have hRξ : (ρ + K.ξ0) / 2 < K.ξ0 := by linarith
  have hsub : closedBall ξ ((K.ξ0 - ρ) / 4) ⊆ {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} :=
    fun ζ hζ => ((fibreNorm_le_of_mem_closedBall hζ).trans hR).trans_lt hRξ
  have hM : ∀ ζ ∈ closedBall ξ ((K.ξ0 - ρ) / 4),
      ‖phaseIntegral data.lam a b ζ‖ ≤ (b - a) * ((8 + K.Cw * K.Cg) * K.ξ0 ^ 2) := by
    intro ζ hζ
    have h := phaseIntegral_norm_le_of_closedBall data hη0 hη1 hCg hCw hG hv hw hab hR hRξ hζ
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by positivity)) (sub_nonneg.2 hab))
  exact norm_iteratedFDeriv_le_of_closedBall hU
    (phaseIntegral_analyticOnNhd data hη0 hη1 hCg hCw hG hv hw hab) n hr₀ hsub hM

/-- **The first derivative of the phase integral vanishes at `ξ = 0`**, with the zero
`‖DΞ(ξ)‖ ≤ (b-a) C_q (9 + (ξ₀/r₀)²)|ξ|`, `r₀ = (ξ₀ - ρ)/4`. -/
theorem phaseIntegral_fderiv_le (data : FibreScalarData K η G v t0 S)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw)
    (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    {a b : ℝ} (hab : a ≤ b) {ρ : ℝ} (hρ : ρ < K.ξ0) {ξ : Fin 2 → ℂ}
    (hξ : fibreNorm ξ ≤ ρ) :
    ‖iteratedFDeriv ℂ 1 (phaseIntegral data.lam a b) ξ‖ ≤
      (b - a) * ((8 + K.Cw * K.Cg) * (9 + (K.ξ0 / ((K.ξ0 - ρ) / 4)) ^ 2)) * fibreNorm ξ := by
  set r₀ : ℝ := (K.ξ0 - ρ) / 4 with hr₀def
  have hr₀ : 0 < r₀ := by rw [hr₀def]; linarith
  set Cq : ℝ := 8 + K.Cw * K.Cg with hCqdef
  have hCq : 0 ≤ Cq := by positivity
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  have hU : IsOpen {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} :=
    isOpen_lt fibreNorm_continuous continuous_const
  have hΞ := phaseIntegral_analyticOnNhd data hη0 hη1 hCg hCw hG hv hw hab
  set s := fibreNorm ξ with hs
  have hs0 : 0 ≤ s := fibreNorm_nonneg ξ
  -- the estimate on a ball of radius `r ≤ r₀`
  have hball : ∀ r, 0 < r → r ≤ r₀ →
      ‖iteratedFDeriv ℂ 1 (phaseIntegral data.lam a b) ξ‖ ≤
        (b - a) * (Cq * (s + 2 * r) ^ 2) / r := by
    intro r hr hrr
    have hR : fibreNorm ξ + 2 * r ≤ s + 2 * r := le_rfl
    have hRξ : s + 2 * r < K.ξ0 := by rw [hr₀def] at hrr; linarith
    have hsub : closedBall ξ r ⊆ {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} :=
      fun ζ hζ => ((fibreNorm_le_of_mem_closedBall hζ).trans hR).trans_lt hRξ
    have h := norm_iteratedFDeriv_le_of_closedBall hU hΞ 1 hr hsub
      (fun ζ hζ => phaseIntegral_norm_le_of_closedBall data hη0 hη1 hCg hCw hG hv hw hab hR
        hRξ hζ)
    simpa using h
  have hC9 : Cq * 9 ≤ Cq * (9 + (K.ξ0 / r₀) ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (K.ξ0 / r₀)]) hCq
  rcases eq_or_lt_of_le hs0 with hs0' | hspos
  · -- `ξ = 0`: the bound `4(b-a)C_q r` for every small `r`
    rw [← hs0', mul_zero]
    have hlim : Tendsto (fun r : ℝ => (b - a) * (Cq * (s + 2 * r) ^ 2) / r) (𝓝[>] 0)
        (𝓝 0) := by
      have heq : ∀ r : ℝ, 0 < r → (b - a) * (Cq * (s + 2 * r) ^ 2) / r = 4 * (b - a) * Cq * r := by
        intro r hr
        rw [← hs0']
        field_simp
        ring
      have h0 : Tendsto (fun r : ℝ => 4 * (b - a) * Cq * r) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun r : ℝ => 4 * (b - a) * Cq * r) (𝓝 0) (𝓝 (4 * (b - a) * Cq * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine h0.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (heq r hr).symm
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
    exact hball r hr.1 hr.2.le
  · rcases le_or_gt s r₀ with hsr | hsr
    · -- radius `|ξ|`
      have h := hball s hspos hsr
      have heq : (b - a) * (Cq * (s + 2 * s) ^ 2) / s = (b - a) * (Cq * 9) * s := by
        field_simp
        ring
      rw [heq] at h
      refine h.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC9 hba) hs0
    · -- radius `r₀`
      have h := hball r₀ hr₀ le_rfl
      refine h.trans ?_
      have hsr0 : s + 2 * r₀ ≤ K.ξ0 := by rw [hr₀def] at hsr ⊢; linarith
      have h1 : (b - a) * (Cq * (s + 2 * r₀) ^ 2) / r₀ ≤ (b - a) * (Cq * K.ξ0 ^ 2) / r₀ := by
        refine div_le_div_of_nonneg_right ?_ hr₀.le
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCq) hba
        exact pow_le_pow_left₀ (by positivity) hsr0 2
      refine h1.trans ?_
      have h2 : (b - a) * (Cq * K.ξ0 ^ 2) / r₀ = (b - a) * (Cq * (K.ξ0 / r₀) ^ 2) * r₀ := by
        field_simp
      rw [h2]
      have h3 : (b - a) * (Cq * (K.ξ0 / r₀) ^ 2) ≤ (b - a) * (Cq * (9 + (K.ξ0 / r₀) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hCq) hba
      have h4 : 0 ≤ (b - a) * (Cq * (K.ξ0 / r₀) ^ 2) := by positivity
      calc (b - a) * (Cq * (K.ξ0 / r₀) ^ 2) * r₀ ≤ (b - a) * (Cq * (K.ξ0 / r₀) ^ 2) * s :=
            mul_le_mul_of_nonneg_left hsr.le h4
        _ ≤ (b - a) * (Cq * (9 + (K.ξ0 / r₀) ^ 2)) * s :=
            mul_le_mul_of_nonneg_right h3 hs0

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Filter Topology Metric Homogenization AVRegularity.CycleEvolution
open AVRegularity.CycleWords AVRegularity.Analysis
open scoped Nat
namespace AVRegularity.CycleWords.Assembly

/-! # Normalized jets of the gauge in the plane frequency

The gauge `θ ↦ e^{Ξ(θ/√η)}` is the complex-analytic `e^Ξ` composed with the real linear map
`fibreEmbed η : θ ↦ θ/√η` of norm `≤ 1/√η`. Its real derivatives are bounded by the complex ones
(`norm_iteratedFDeriv_comp_clm_le`), and those by Faà di Bruno with `‖Dⁱ exp‖ = |exp|`
(`norm_iteratedFDeriv_cexp_comp_le`). With the phase bounds
(`‖DΞ‖ ≤ C(b-a)|ξ|`, `‖DⁱΞ‖ ≤ C_i(b-a)`) and `b - a ≤ C_H S`, the normalized derivatives are at
most `k! Bᵏ (1 + x_ξ)ᵏ |e^Ξ|`, `x_ξ = √S|ξ| = |θ|/ϖ` (`gauge_normalized_jet_le`). -/

variable {K : ScalarConstants} {η t0 S : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2}

/-- The embedding `θ ↦ θ/√η` of plane frequencies into fibre frequencies. -/
def fibreEmbed (η : ℝ) : Vec 2 →L[ℝ] (Fin 2 → ℂ) :=
  (Real.sqrt η)⁻¹ • ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

theorem fibreEmbed_apply (η : ℝ) (θ : Vec 2) : fibreEmbed η θ = planeFibreFrequency η θ := by
  funext i
  simp [fibreEmbed, planeFibreFrequency, div_eq_inv_mul]

theorem norm_fibreEmbed_le {η : ℝ} (hη : 0 < η) : ‖fibreEmbed η‖ ≤ (Real.sqrt η)⁻¹ := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun θ => ?_
  rw [fibreEmbed_apply]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  show ‖((θ i / Real.sqrt η : ℝ) : ℂ)‖ ≤ (Real.sqrt η)⁻¹ * ‖θ‖
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hs, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm θ i)
    (inv_nonneg.2 hs.le)

theorem fibreNorm_planeFibreFrequency_eq_div {η : ℝ} (hη : 0 < η) (θ : Vec 2) :
    fibreNorm (planeFibreFrequency η θ) = Real.sqrt (vecDot θ θ) / Real.sqrt η := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  rw [← Real.sqrt_div' _ hη.le]
  unfold fibreNorm vecDot planeFibreFrequency
  congr 1
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hη.le,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem planeFibreFrequency_im (η : ℝ) (θ : Vec 2) (i : Fin 2) :
    (planeFibreFrequency η θ i).im = 0 := Complex.ofReal_im _

theorem norm_iteratedFDeriv_cexp (i : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℂ i Complex.exp z‖ = ‖Complex.exp z‖ := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
    Complex.iter_deriv_exp]

/-- **Faà di Bruno for `e^f`**: `‖Dᵏ e^f(ξ)‖ ≤ k! |e^{f(ξ)}| Dᵏ` when `‖Dⁱf(ξ)‖ ≤ Dⁱ`. -/
theorem norm_iteratedFDeriv_cexp_comp_le {f : (Fin 2 → ℂ) → ℂ} {U : Set (Fin 2 → ℂ)}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) {ξ : Fin 2 → ℂ} (hξ : ξ ∈ U) (k : ℕ) {D : ℝ}
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℂ i f ξ‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℂ k (fun z => Complex.exp (f z)) ξ‖ ≤ k ! * ‖Complex.exp (f ξ)‖ * D ^ k := by
  have hfC : ContDiffOn ℂ (⊤ : ℕ∞) f U := hf.contDiffOn hU.uniqueDiffOn
  have hexp : ContDiffOn ℂ (⊤ : ℕ∞) Complex.exp univ := Complex.contDiff_exp.contDiffOn
  have h := norm_iteratedFDerivWithin_comp_le (n := k) hexp hfC (by exact_mod_cast le_top)
    uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ _ _) hξ (C := ‖Complex.exp (f ξ)‖) (D := D)
    (fun i _ => by rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_cexp])
    (fun i hi1 hik => by rw [iteratedFDerivWithin_of_isOpen i hU hξ]; exact hD i hi1 hik)
  rwa [iteratedFDerivWithin_of_isOpen k hU hξ] at h

/-- The real derivatives of a complex-analytic map composed with a real linear map. -/
theorem norm_iteratedFDeriv_comp_clm_le {E' : (Fin 2 → ℂ) → ℂ} {U : Set (Fin 2 → ℂ)}
    (hU : IsOpen U) (hE : AnalyticOnNhd ℂ E' U) (L : Vec 2 →L[ℝ] (Fin 2 → ℂ)) {θ : Vec 2}
    (hθ : L θ ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun θ' => E' (L θ')) θ‖ ≤ ‖iteratedFDeriv ℂ k E' (L θ)‖ * ‖L‖ ^ k := by
  have hEC : ContDiffOn ℂ (⊤ : ℕ∞) E' U := hE.contDiffOn hU.uniqueDiffOn
  have hER : ContDiffOn ℝ (⊤ : ℕ∞) E' U := hEC.restrict_scalars ℝ
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have h1 : iteratedFDeriv ℝ k (fun θ' => E' (L θ')) θ =
      iteratedFDerivWithin ℝ k (E' ∘ L) (L ⁻¹' U) θ :=
    (iteratedFDerivWithin_of_isOpen k hpre hθ).symm
  rw [h1, L.iteratedFDerivWithin_comp_right hER hU.uniqueDiffOn hpre.uniqueDiffOn hθ
    (by exact_mod_cast le_top), iteratedFDerivWithin_of_isOpen k hU hθ]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hres := ((hEC.contDiffAt (hU.mem_nhds hθ)).of_le
    (by exact_mod_cast le_top)).restrictScalars_iteratedFDeriv (𝕜 := ℝ) (n := k)
  rw [← hres, Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars]

end AVRegularity.CycleWords.Assembly
end
