-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.PulseIdentity
import AVRegularity.CycleComparison.Charts.ChartDeviation
public import AVRegularity.Statements.Intermediate.CycleOutput.GluedLift
public import AVRegularity.Statements.Intermediate.CycleOutput.PulseLiftData
public import AVRegularity.CycleComparison.Reconstruction.PulseChart
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
import AVRegularity.CycleComparison.TailConstructed.RawFluxOrderZero
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import AVRegularity.EntryWeak.WeakCarrierAppend
public import AVRegularity.Statements.Intermediate.CycleOutput.OcChartInv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVenhance
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The glued lift at the start of the window** (`û(t_p) = 𝑷f`). Every observed pulse weighted at
the start `t_A` of the observation window has its lift window starting at `t_A`, where its lift is
the coarse field (`labelLift_start`); the weights sum to one, so the glued lift of a coarse field
`a` is `a(t_A)` there (`gluedLift_start`). -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- **The glued lift at the start of the window is the coarse field.** -/
theorem gluedLift_start {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {φs : ℝ → Vec 2 → ℝ}
    (hφs : IsAdmissibleStream φs) {ν B ρ lam : ℝ} (hℓ : ocEll q Λ m ν ≠ 0) (hρ : ρ ≠ 0)
    {D : ℕ}
    (edge : ℤ → ConstituentEdges D h) {tA tZ : ℝ} (htAZ : tA ≤ tZ) (ϖ : ℤ → ℝ → ℝ)
    {quiet : Set ℝ} {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) ϖ (ocPulseWindow α q Λ m) quiet
      (Icc tA tZ) (ocTau α q Λ m) Cpart)
    (sX sZ N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ φs hφs ν B ρ lam k (edge k)) sX sZ
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    (εc : ℝ) (a : ℝ → Vec 2 → ∀ i, h i) (ha : ContDiff ℝ (⊤ : ℕ∞) (a tA)) (x : Vec 2) :
    gluedLift (ocObsPulses α q Λ m tA tZ) ϖ (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) εc N H Cc
      (fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
      (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a tA x = a tA x := by
  have hc : ocEll q Λ m ν ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  have hmem : tA ∈ Icc tA tZ := ⟨le_rfl, htAZ⟩
  have hterm : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      ϖ k tA • pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) εc N H (Cc k)
        (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a tA x = ϖ k tA • a tA x := by
    intro k hk
    by_cases hw : ϖ k tA = 0
    · rw [hw, zero_smul, zero_smul]
    · have hwin : tA ∈ ocPulseWindow α q Λ m k := hpart.2.2.2.1 k hk tA hw
      have hwin' : ((k : ℝ) - 61 / 48) * ocTau α q Λ m ≤ tA ∧
          tA ≤ ((k : ℝ) + 61 / 48) * ocTau α q Λ m := hwin
      have hmax : max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA = tA := max_eq_right hwin'.1
      set t₀ := max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2 with ht₀
      have hct : ocEll q Λ m ν ^ 2 * t₀ = tA := by rw [ht₀, hmax, mul_div_cancel₀ _ hc]
      have hle : t₀ ≤ min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2 := by
        rw [ht₀, hmax]
        exact div_le_div_of_nonneg_right (le_min hwin'.2 htAZ) (sq_nonneg _)
      have hf : ContDiff ℝ (⊤ : ℕ∞) (fun X => a (ocEll q Λ m ν ^ 2 * t₀)
          (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * t₀)
            (ρ • X))) := by
        rw [hct]
        have hχ : ContDiff ℝ (⊤ : ℕ∞)
            (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) tA) :=
          (Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)).comp
            (contDiff_const.prodMk contDiff_id)
        exact ha.comp (hχ.comp (contDiff_const_smul ρ))
      have hs := labelLift_start (hseq k hk) hle εc
        (fun s X => a (ocEll q Λ m ν ^ 2 * s)
          (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s)
            (ρ • X))) hf ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) hc
        (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) tA x)
      rw [hct] at hs
      have hpl : pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) εc N H (Cc k)
          (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
          (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) a tA x =
          labelLift (Cc k) N H εc (fun s X => a (ocEll q Λ m ν ^ 2 * s)
            (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s)
              (ρ • X))) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) tA
            (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) tA x) := rfl
      rw [hpl, hs, smul_smul, mul_inv_cancel₀ hρ, one_smul, Charts.ocChart_ocChartInv]
  simp only [gluedLift]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, hpart.2.2.1 tA hmem, one_smul]

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
open scoped Matrix
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The label density in physical operators**. The label
density of the lift (`labelDensity`) is, on the window, the label drift and the label diffusion of
the label lift `V(t, ·)` plus `c⁻¹` times the rest (`labelRest`: sources, lifted means, tail and the
lift of the material derivative of the coarse field), `labelDensity_split`. Read at the labels
`y = ψ(x)` of a volume-preserving chart `χ` with material metric `G = (Dχ)⁻¹(Dχ)⁻ᵀ`, the label
drift is the physical drift by the pushed-forward pulse velocity and the label diffusion is the
physical Laplacian (`chart_drift`, `chart_laplacian`), so the density is
`-b_k·∇𝒯 + ν Δ𝒯 + c⁻¹ (rest)(ψ x)` for the physical lift `𝒯 = V ∘ ψ`
(`labelDensity_physical`). -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

/-- The rest of the label density: sources, lifted means, tail and the lift of the material
derivative of the coarse field, summed over the grades. -/
def labelRest {D : ℕ} (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ)
    (ε : ℝ) (f df : ℝ → Vec 2 → ∀ i, h i) (ρs es c : ℝ) (t : ℝ) (y : Vec 2) : ∀ i, h i :=
  ∑ hh ∈ Finset.range (H + 1),
    ((if hh = 0 then 0 else sourceOp Q.edge Q.η ε (c⁻¹ * t)
        (liftPolyField Cc N ε (hh - 1) (fun _ => f (c⁻¹ * t)) (c⁻¹ * t)) (ρs⁻¹ • y) (es⁻¹ • y)) +
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftPolyField Cc N ε p.1 (liftMeanPoly Q Cc N ε (fun _ => f (c⁻¹ * t)) p.2)
          (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y)) +
      (∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ n •
        liftTailCoeff Q Cc N (fun _ => f (c⁻¹ * t)) hh n (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y)) +
      liftPolyField Cc N ε hh df (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y))

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A continuous linear map of a finite sum of fields commutes with directional derivatives. -/
theorem fderiv_clm_sum_apply {J : Type*} (S : Finset J) (L : E →L[ℝ] F) (U : J → Vec 2 → E)
    {y : Vec 2} (hU : ∀ j ∈ S, DifferentiableAt ℝ (U j) y) (e : Vec 2) :
    fderiv ℝ (fun y' => L (∑ j ∈ S, U j y')) y e = ∑ j ∈ S, L (fderiv ℝ (U j) y e) := by
  have hs : HasFDerivAt (fun y' => ∑ j ∈ S, U j y') (∑ j ∈ S, fderiv ℝ (U j) y) y :=
    HasFDerivAt.fun_sum fun j hj => (hU j hj).hasFDerivAt
  have hc : HasFDerivAt (fun y' => L (∑ j ∈ S, U j y')) (L.comp (∑ j ∈ S, fderiv ℝ (U j) y)) y :=
    L.hasFDerivAt.comp y hs
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
    map_sum]

end Calculus

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
/-- **The label density splits into label drift, label diffusion and the rest.** -/
theorem labelDensity_split {D : ℕ} (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (N H : ℕ) (ε : ℝ) (f df : ℝ → Vec 2 → ∀ i, h i) (w : ℝ → Vec 2 → Vec 2)
    (ρs es c νs : ℝ) (hc : c ≠ 0) (t : ℝ)
    (hbox : ∀ hh ∈ Finset.range (H + 1),
      IsBoxSmooth 2 2 (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t)))
    (hG : ∀ i j, Differentiable ℝ (fun X => Q.G (c⁻¹ * t) X i j)) (y : Vec 2) (v : ι) :
    labelDensity Q Cc N H ε f df w ρs es c νs t y v =
      -(∑ k, w (c⁻¹ * t) (es⁻¹ • y) k •
          fderiv ℝ (fun y' => labelLift Cc N H ε f ρs es c t y' v) y (basisVec k)) +
        νs • ∑ i, fderiv ℝ (fun y' => ∑ j, Q.G (c⁻¹ * t) (ρs⁻¹ • y') i j •
          fderiv ℝ (fun y'' => labelLift Cc N H ε f ρs es c t y'' v) y' (basisVec j))
            y (basisVec i) +
        c⁻¹ • labelRest Q Cc N H ε f df ρs es c t y v := by
  classical
  set s := c⁻¹ * t with hs
  set U : ℕ → Vec 2 → ∀ i, h i := fun hh =>
    twoScaleSample ρs es (liftPolyField Cc N ε hh (fun _ => f s) s) with hU
  set L : (∀ i, h i) →L[ℝ] h v := ContinuousLinearMap.proj (R := ℝ) (φ := h) v with hL
  have hlift : ∀ y', labelLift Cc N H ε f ρs es c t y' v =
      L (∑ hh ∈ Finset.range (H + 1), U hh y') := by
    intro y'
    simp only [labelLift, hL, hU, twoScaleSample, ContinuousLinearMap.proj_apply,
      Finset.sum_apply]
    rfl
  have hC2 : ∀ hh ∈ Finset.range (H + 1), ContDiff ℝ 2 (U hh) := fun hh hhm =>
    CoarseFluxDiff.contDiff_sample (hbox hh hhm) le_rfl le_rfl ρs es
  have hd1 : ∀ hh ∈ Finset.range (H + 1), ∀ y', DifferentiableAt ℝ (U hh) y' := fun hh hhm y' =>
    ((hC2 hh hhm).differentiable (by norm_num)) y'
  have hsm : Differentiable ℝ (fun y' : Vec 2 => ρs⁻¹ • y') := by fun_prop
  have hGd : ∀ i j, Differentiable ℝ (fun y' => Q.G s (ρs⁻¹ • y') i j) := fun i j =>
    (hG i j).comp hsm
  have hDU : ∀ hh ∈ Finset.range (H + 1), ∀ j, Differentiable ℝ
      (fun y' => fderiv ℝ (U hh) y' (basisVec j)) := fun hh hhm j =>
    (((hC2 hh hhm).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).clm_apply
      (differentiable_const _)
  -- first derivatives of the label lift
  have hfun : (fun y'' => labelLift Cc N H ε f ρs es c t y'' v) =
      fun y'' => L (∑ hh ∈ Finset.range (H + 1), U hh y'') := funext hlift
  have hfd : ∀ y' e', fderiv ℝ (fun y'' => labelLift Cc N H ε f ρs es c t y'' v) y' e' =
      ∑ hh ∈ Finset.range (H + 1), L (fderiv ℝ (U hh) y' e') := by
    intro y' e'
    rw [hfun]
    exact fderiv_clm_sum_apply _ L U (fun hh hhm => hd1 hh hhm y') e'
  -- the metric flux of the label lift
  have hflux : ∀ i, (fun y' => ∑ j, Q.G s (ρs⁻¹ • y') i j •
      fderiv ℝ (fun y'' => labelLift Cc N H ε f ρs es c t y'' v) y' (basisVec j)) =
      fun y' => L (∑ hh ∈ Finset.range (H + 1),
        ∑ j, Q.G s (ρs⁻¹ • y') i j • fderiv ℝ (U hh) y' (basisVec j)) := by
    intro i
    funext y'
    simp only [hfd, map_sum, map_smul, Finset.smul_sum]
    exact Finset.sum_comm
  have hdiv : ∀ i, fderiv ℝ (fun y' => ∑ j, Q.G s (ρs⁻¹ • y') i j •
      fderiv ℝ (fun y'' => labelLift Cc N H ε f ρs es c t y'' v) y' (basisVec j)) y (basisVec i) =
      ∑ hh ∈ Finset.range (H + 1), L (fderiv ℝ (fun y' => ∑ j, Q.G s (ρs⁻¹ • y') i j •
        fderiv ℝ (U hh) y' (basisVec j)) y (basisVec i)) := by
    intro i
    rw [hflux i]
    exact fderiv_clm_sum_apply _ L
      (fun hh y' => ∑ j, Q.G s (ρs⁻¹ • y') i j • fderiv ℝ (U hh) y' (basisVec j))
      (fun hh hhm => DifferentiableAt.fun_sum fun j _ => ((hGd i j).smul (hDU hh hhm j)) y)
      (basisVec i)
  simp only [hdiv]
  simp only [hfd]
  unfold labelDensity labelRest
  simp only [hL, hU, ContinuousLinearMap.proj_apply, Finset.sum_apply, Pi.add_apply,
    Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_add, smul_neg, smul_sub, smul_smul,
    Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  simp only [inv_mul_cancel_left₀ hc, hs]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 2))),
    Finset.sum_comm (s := (Finset.univ : Finset (Fin 2)))]
  abel

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
/-- **The label density in physical operators.** Read at the labels `ψ x` of a volume-preserving
chart `χ` whose material metric is the slow metric of the lift, the label density is the physical
drift by the pushed-forward pulse velocity `b`, the physical Laplacian, and `c⁻¹` times the rest. -/
theorem labelDensity_physical {D : ℕ} (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (N H : ℕ) (ε : ℝ) (f df : ℝ → Vec 2 → ∀ i, h i) (w : ℝ → Vec 2 → Vec 2)
    (ρs es c νs : ℝ) (hc : c ≠ 0) (t : ℝ)
    (hbox : ∀ hh ∈ Finset.range (H + 1),
      IsBoxSmooth 2 2 (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t)))
    (hG : ∀ i j, Differentiable ℝ (fun X => Q.G (c⁻¹ * t) X i j))
    {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : Differentiable ℝ ψ)
    (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (hd : ∀ y, (jacMatrix χ y).det = 1)
    (hGχ : ∀ y, (fun i j => Q.G (c⁻¹ * t) (ρs⁻¹ • y) i j) =
      (jacMatrix χ y)⁻¹ * ((jacMatrix χ y)⁻¹)ᵀ)
    (b : Vec 2 → Vec 2)
    (hwb : ∀ x, (jacMatrix χ (ψ x)).mulVec (w (c⁻¹ * t) (es⁻¹ • ψ x)) = b x) (x : Vec 2) (v : ι) :
    labelDensity Q Cc N H ε f df w ρs es c νs t (ψ x) v =
      -(∑ k, b x k • fderiv ℝ (fun x' => labelLift Cc N H ε f ρs es c t (ψ x') v) x
          (basisVec k)) +
        νs • ∑ k, fderiv ℝ (fun x' => fderiv ℝ (fun x'' => labelLift Cc N H ε f ρs es c t
          (ψ x'') v) x' (basisVec k)) x (basisVec k) +
        c⁻¹ • labelRest Q Cc N H ε f df ρs es c t (ψ x) v := by
  classical
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hV2 : ContDiff ℝ 2 (fun y => labelLift Cc N H ε f ρs es c t y v) := by
    have he : (fun y => labelLift Cc N H ε f ρs es c t y v) = fun y =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) (∑ hh ∈ Finset.range (H + 1),
          twoScaleSample ρs es (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t)) y) := by
      funext y
      simp only [labelLift, twoScaleSample, ContinuousLinearMap.proj_apply, Finset.sum_apply]
      rfl
    rw [he]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).contDiff.comp
      (ContDiff.sum fun hh hhm => CoarseFluxDiff.contDiff_sample (hbox hh hhm) le_rfl le_rfl ρs es)
  have hV1 : Differentiable ℝ (fun y => labelLift Cc N H ε f ρs es c t y v) :=
    hV2.differentiable (by norm_num)
  have hsm : Differentiable ℝ (fun y' : Vec 2 => ρs⁻¹ • y') := by fun_prop
  have hGd : ∀ i j, Differentiable ℝ
      (fun y => (fun i j => Q.G (c⁻¹ * t) (ρs⁻¹ • y) i j) i j) := fun i j => (hG i j).comp hsm
  rw [labelDensity_split Q Cc N H ε f df w ρs es c νs hc t hbox hG (ψ x) v,
    chart_drift hχd hψ hψχ hχψ hV1 (fun y => w (c⁻¹ * t) (es⁻¹ • y)) b hwb x]
  have hlap := chart_laplacian hχ hψ hψχ hχψ hd (fun y i j => Q.G (c⁻¹ * t) (ρs⁻¹ • y) i j)
    hGχ hGd hV2 x
  rw [← hlap]

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The parts of the rest of one pulse**. The rest
`labelRest` of a pulse lift splits into its source part (`restSource`), its mean part
(`restMean`), its tail (`restTail`) and the lift of the material derivative of the coarse field
(`labelRest_split`). The mean part regrades (depth truncation, `setting_meanPart_grade_sum`), so
that the mean part and the material part together are the label lift of the single cell field
`df + ∑_r 𝓜_r f` (`setting_restMean_add_lift`): the lift `𝒯_k` applied to the coarse defect in
the chart frame, once the means are identified with the glued mean. -/

section
section Parts

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

/-- The source part of the rest. -/
def restSource (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε : ℝ)
    (f : ℝ → Vec 2 → ∀ i, h i) (ρs es c : ℝ) (t : ℝ) (y : Vec 2) : ∀ i, h i :=
  ∑ hh ∈ Finset.range (H + 1),
    (if hh = 0 then 0 else sourceOp Q.edge Q.η ε (c⁻¹ * t)
      (liftPolyField Cc N ε (hh - 1) (fun _ => f (c⁻¹ * t)) (c⁻¹ * t)) (ρs⁻¹ • y) (es⁻¹ • y))

/-- The mean part of the rest. -/
def restMean (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε : ℝ)
    (f : ℝ → Vec 2 → ∀ i, h i) (ρs es c : ℝ) (t : ℝ) (y : Vec 2) : ∀ i, h i :=
  ∑ hh ∈ Finset.range (H + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
    liftPolyField Cc N ε p.1 (liftMeanPoly Q Cc N ε (fun _ => f (c⁻¹ * t)) p.2)
      (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y)

/-- The tail of the rest. -/
def restTail (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε : ℝ)
    (f : ℝ → Vec 2 → ∀ i, h i) (ρs es c : ℝ) (t : ℝ) (y : Vec 2) : ∀ i, h i :=
  ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ n •
    liftTailCoeff Q Cc N (fun _ => f (c⁻¹ * t)) hh n (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y)

/-- **The rest splits into its four parts.** -/
theorem labelRest_split (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ)
    (ε : ℝ) (f df : ℝ → Vec 2 → ∀ i, h i) (ρs es c : ℝ) (t : ℝ) (y : Vec 2) :
    labelRest Q Cc N H ε f df ρs es c t y =
      restSource Q Cc N H ε f ρs es c t y + restMean Q Cc N H ε f ρs es c t y +
        restTail Q Cc N H ε f ρs es c t y + labelLift Cc N H ε df ρs es c t y := by
  simp only [labelRest, restSource, restMean, restTail, labelLift, Finset.sum_add_distrib]

omit [∀ i, InnerProductSpace ℝ (h i)] in
/-- The lift of a sum of two inputs. -/
theorem liftPolyField_add_input [∀ i, NormedSpace ℝ (h i)] (Cc : ℕ → ℕ → LiftCoeff ι h) (N : ℕ)
    (ε : ℝ) (q : ℕ) (A B : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (hA : ContDiff ℝ (N : ℕ∞) (A t))
    (hB : ContDiff ℝ (N : ℕ∞) (B t)) (X z : Vec 2) :
    liftPolyField Cc N ε q (fun s X' => A s X' + B s X') t X z =
      liftPolyField Cc N ε q A t X z + liftPolyField Cc N ε q B t X z := by
  have h2 := liftPolyField_sum_input Cc N ε q (Finset.range 2)
    (fun r => if r = 0 then A else B) t
    (fun r _ => by
      by_cases hr : r = 0
      · simp only [hr, ↓reduceIte]; exact hA
      · simp only [hr, ↓reduceIte]; exact hB) X z
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ↓reduceIte,
    Nat.one_ne_zero] using h2

end Parts

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The mean part and the material part of the rest form one lift**: the label lift of the
cell field `df + ∑_{r ≤ H} 𝓜_r f`. -/
theorem setting_restMean_add_lift (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    (f df : ℝ → Vec 2 → ∀ i, h i) (ρs es c t : ℝ) (hs : c⁻¹ * t ∈ Icc a b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (f (c⁻¹ * t))) (hdf : ContDiff ℝ (N : ℕ∞) (df (c⁻¹ * t)))
    (y : Vec 2) :
    restMean Q Cc N H ε f ρs es c t y + labelLift Cc N H ε df ρs es c t y =
      labelLift Cc N H ε (fun s X => df s X +
        ∑ r ∈ Finset.range (H + 1), liftMeanPoly Q Cc N ε (fun _ => f (c⁻¹ * t)) r s X)
        ρs es c t y := by
  have hM : ContDiff ℝ (N : ℕ∞) (fun X => ∑ r ∈ Finset.range (H + 1),
      liftMeanPoly Q Cc N ε (fun _ => f (c⁻¹ * t)) r (c⁻¹ * t) X) :=
    ContDiff.sum fun r hr => setting_liftMeanPoly_contDiff P hsX hsZ hseq ε
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)) _ hf hs
  simp only [restMean, labelLift]
  rw [setting_meanPart_grade_sum P hsX hsZ hseq ε _ hf hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [liftPolyField_add_input Cc N ε q df (fun s X => ∑ r ∈ Finset.range (H + 1),
    liftMeanPoly Q Cc N ε (fun _ => f (c⁻¹ * t)) r s X) (c⁻¹ * t) hdf hM, add_comm]
end

/-! **The mean and material parts of a pulse rest as one physical lift**. For a finite-rank coarse
field `a = ∑_j c_j φ_j`, at a time `t` where the means of the pulse equal given fields `M_r` (the
glued means, by the exact quiet mean), the mean part and the material part of the rest, read at the
labels `ψ x` and scaled by `c⁻¹`, are the physical lift of the pulse applied to the coarse defect
field `∂_t a + W · ∇a + ∑_r M_r` (`setting_pulse_meanPart_lift`). -/

section
section Input

end Input

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The label lift scales with its input. -/
theorem labelLift_smul_input (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε k : ℝ)
    (A : ℝ → Vec 2 → ∀ i, h i) (ρs es c t : ℝ) (hA : ContDiff ℝ (N : ℕ∞) (A (c⁻¹ * t)))
    (y : Vec 2) :
    labelLift Cc N H ε (fun s X => k • A s X) ρs es c t y =
      k • labelLift Cc N H ε A ρs es c t y := by
  simp only [labelLift, liftPolyField, Finset.smul_sum]
  refine Finset.sum_congr rfl fun hh _ => Finset.sum_congr rfl fun n hn => ?_
  have hnN : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  have h1 := liftApply_input_finite_synthesis n (Cc hh n) (J := Unit) (fun _ => k)
    (fun _ => A (c⁻¹ * t)) (fun _ => hA.of_le (by exact_mod_cast hnN)) (c⁻¹ * t) (ρs⁻¹ • y)
    (es⁻¹ • y)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h1
  rw [liftApply_congr_time (c₁ := Cc hh n) (c₂ := Cc hh n) (a := fun s X => k • A s X)
      (b := fun _ Y => k • A (c⁻¹ * t) Y) (t := c⁻¹ * t) (fun _ _ _ _ => rfl) rfl, h1,
    liftApply_congr_time (c₁ := Cc hh n) (c₂ := Cc hh n) (a := A) (b := fun _ => A (c⁻¹ * t))
      (t := c⁻¹ * t) (fun _ _ _ _ => rfl) rfl, smul_comm]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The label lift only sees its input at the cell time of `t`. -/
theorem labelLift_congr_input (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε : ℝ)
    {A B : ℝ → Vec 2 → ∀ i, h i} (ρs es c t : ℝ) (hAB : A (c⁻¹ * t) = B (c⁻¹ * t))
    (y : Vec 2) :
    labelLift Cc N H ε A ρs es c t y = labelLift Cc N H ε B ρs es c t y := by
  simp only [labelLift, liftPolyField]
  refine Finset.sum_congr rfl fun hh _ => Finset.sum_congr rfl fun n _ => ?_
  rw [liftApply_congr_time (c₁ := Cc hh n) (c₂ := Cc hh n) (a := A) (b := B) (t := c⁻¹ * t)
    (fun _ _ _ _ => rfl) hAB]

variable {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The mean and material parts of a pulse rest are the pulse lift of the coarse defect.** -/
theorem setting_pulse_meanPart_lift (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) (χ ψ W : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2))
    (hψχ : ∀ t y, ψ t (χ t y) = y) {c ρs : ℝ} (hc : c ≠ 0) (hρ : ρs ≠ 0) (es : ℝ) (t : ℝ)
    (hs : c⁻¹ * t ∈ Icc a b) (Mr : ℕ → Vec 2 → ∀ i, h i)
    (hMr : ∀ r ∈ Finset.range (H + 1), ContDiff ℝ (N : ℕ∞) (Mr r))
    (hmean : ∀ r ∈ Finset.range (H + 1), ∀ x, pulseMeanField c ρs ε N r Q Cc χ ψ
      (fun t' x' => ∑ j, cf j t' • φ j x') t x = Mr r x)
    (hW : ContDiff ℝ (⊤ : ℕ∞) (W t)) (x : Vec 2) :
    c⁻¹ • (restMean Q Cc N H ε (chartField cf φ χ c ρs) ρs es c t (ψ t x) +
        labelLift Cc N H ε (chartFieldDot cf dcf φ χ W c ρs) ρs es c t (ψ t x)) =
      pulsePhysicalLift c ρs es ε N H Cc χ ψ (fun t' x' =>
        (∑ j, dcf j t' • φ j x' + ∑ j, cf j t' • fderiv ℝ (φ j) x' (W t' x')) +
          ∑ r ∈ Finset.range (H + 1), Mr r x') t x := by
  have hct : c * (c⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  set s := c⁻¹ * t with hsdef
  have hf : ContDiff ℝ (⊤ : ℕ∞) (chartField cf φ χ c ρs s) :=
    chartField_contDiff cf φ hφ χ hχ c ρs s
  have hχt : ContDiff ℝ (⊤ : ℕ∞) (χ t) := hχ.comp (contDiff_const.prodMk contDiff_id)
  have hpos : ContDiff ℝ (⊤ : ℕ∞) (fun X : Vec 2 => χ t (ρs • X)) :=
    hχt.comp (contDiff_const_smul ρs)
  -- the coarse defect field in the chart frame at the cell time
  set T : ℝ → Vec 2 → ∀ i, h i := fun t' x' =>
    (∑ j, dcf j t' • φ j x' + ∑ j, cf j t' • fderiv ℝ (φ j) x' (W t' x')) +
      ∑ r ∈ Finset.range (H + 1), Mr r x' with hTdef
  have hT1 : ContDiff ℝ (⊤ : ℕ∞) (fun x' => ∑ j, dcf j t • φ j x') :=
    ContDiff.sum fun j _ => (hφ j).const_smul (dcf j t)
  have hT2 : ContDiff ℝ (⊤ : ℕ∞) (fun x' => ∑ j, cf j t • fderiv ℝ (φ j) x' (W t x')) :=
    ContDiff.sum fun j _ =>
      (((hφ j).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply hW).const_smul
        (cf j t)
  have hT3 : ContDiff ℝ (N : ℕ∞) (fun x' => ∑ r ∈ Finset.range (H + 1), Mr r x') :=
    ContDiff.sum fun r hr => hMr r hr
  have hTt : ContDiff ℝ (N : ℕ∞) (T t) :=
    ((hT1.add hT2).of_le (by exact_mod_cast le_top)).add hT3
  have hdfe : chartFieldDot cf dcf φ χ W c ρs s = fun X => c • (∑ j, dcf j t • φ j (χ t (ρs • X)) +
      ∑ j, cf j t • fderiv ℝ (φ j) (χ t (ρs • X)) (W t (χ t (ρs • X)))) := by
    funext X
    simp only [chartFieldDot, hct, smul_add, Finset.smul_sum, smul_smul, mul_comm c]
  have hdf : ContDiff ℝ (N : ℕ∞) (chartFieldDot cf dcf φ χ W c ρs s) := by
    have hD1 : ContDiff ℝ (⊤ : ℕ∞) (fun X => ∑ j, dcf j t • φ j (χ t (ρs • X))) :=
      hT1.comp hpos
    have hD2 : ContDiff ℝ (⊤ : ℕ∞)
        (fun X => ∑ j, cf j t • fderiv ℝ (φ j) (χ t (ρs • X)) (W t (χ t (ρs • X)))) :=
      hT2.comp hpos
    rw [hdfe]
    exact ((hD1.add hD2).const_smul c).of_le (by exact_mod_cast le_top)
  rw [setting_restMean_add_lift P sX sZ hsX hsZ Cc hseq ε _ _ ρs es c t hs hf hdf (ψ t x)]
  -- the means of the pulse at the cell time
  have hm : ∀ r ∈ Finset.range (H + 1), ∀ X,
      liftMeanPoly Q Cc N ε (fun _ => chartField cf φ χ c ρs s) r s X =
        c • Mr r (χ t (ρs • X)) := fun r hr X => by
    have h1 := hmean r hr (χ t (ρs • X))
    simp only [pulseMeanField] at h1
    rw [hψχ, smul_smul, inv_mul_cancel₀ hρ, one_smul] at h1
    rw [← h1, smul_smul, mul_inv_cancel₀ hc, one_smul]
    simp only [liftMeanPoly]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
  -- the combined input at the cell time is `c` times the coarse defect in the chart frame
  have hinput : (fun X => chartFieldDot cf dcf φ χ W c ρs s X +
      ∑ r ∈ Finset.range (H + 1), liftMeanPoly Q Cc N ε (fun _ => chartField cf φ χ c ρs s)
        r s X) = fun X => c • T (c * s) (χ (c * s) (ρs • X)) := by
    funext X
    rw [Finset.sum_congr rfl fun r hr => hm r hr X, hdfe, hct]
    simp only [hTdef, smul_add, Finset.smul_sum]
  rw [labelLift_congr_input Cc N H ε ρs es c t (B := fun s' X => c • T (c * s')
      (χ (c * s') (ρs • X))) hinput,
    labelLift_smul_input Cc N H ε c (fun s' X => T (c * s') (χ (c * s') (ρs • X))) ρs es c t
      (by rw [hct]; exact hTt.comp (hpos.of_le (by exact_mod_cast le_top))),
    smul_smul, inv_mul_cancel₀ hc, one_smul]
  rfl
end

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Jets of the label lift**. The label lift
`V(t, y) = ∑_{hh ≤ H} ∑_{n ≤ N} ε^n (C_n^{(hh)} a)(t/c, y/ρ, y/e)` of a coarse field `a` is a finite
sum of lift coefficients, sampled on the diagonal `(X, z) = (y/ρ, y/e)`, applied to word derivatives
of `a` of order at most `N` read at `y/ρ`. All jets below are full Fréchet jets (`iteratedFDeriv`).

* The jets of the diagonal sample of a box-smooth field with bounded mixed jets are bounded
  (`norm_iteratedFDeriv_sample_le`): the joint jets are bounded by the mixed ones and the sampling
  map `y ↦ (y/ρ, y/e)` is linear.
* The spatial jets of order `j ≤ J` of the label lift at `y` are bounded by a constant times the
  jets of order at most `N + j` of the coarse field at `y/ρ`, uniformly on the lift window, and
  the label lift of a coarse field of class `C^{N+J}` is of class `C^J`
  (`setting_labelLift_jets`, `setting_labelLift_jet_bound`, `setting_labelLift_contDiff_finite`).
* The jets of a field read in a chart are bounded by the jets of the field at the image point
  (`norm_iteratedFDeriv_comp_chart_le`, `norm_iteratedFDeriv_chartRead_le`).
* The label lift is additive in the coarse field (`labelLift_add_input`,
  `labelLift_sub_input`). -/

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A power of a nonnegative real is at most the larger power of its maximum with one. -/
theorem pow_le_max_one_pow {x : ℝ} (hx : 0 ≤ x) {i k : ℕ} (hik : i ≤ k) :
    x ^ i ≤ (max x 1) ^ k :=
  (pow_le_pow_left₀ hx (le_max_left x 1) i).trans (pow_le_pow_right₀ (le_max_right x 1) hik)

/-- The linear map `y ↦ (ρ⁻¹ y, e⁻¹ y)` of the two-scale sampling. -/
def sampleMap (ρ e : ℝ) : Vec 2 →L[ℝ] Vec 2 × Vec 2 :=
  (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)).prod (e⁻¹ • ContinuousLinearMap.id ℝ (Vec 2))

/-- The value of the sampling map. -/
theorem sampleMap_apply (ρ e : ℝ) (y : Vec 2) : sampleMap ρ e y = (ρ⁻¹ • y, e⁻¹ • y) := by
  rfl

/-- The norm of the sampling map. -/
theorem norm_sampleMap_le (ρ e : ℝ) : ‖sampleMap ρ e‖ ≤ |ρ⁻¹| + |e⁻¹| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    fun y => ?_
  rw [sampleMap_apply, Prod.norm_mk, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg _)) (norm_nonneg _))

/-- A finite sum of fields whose jets are bounded by multiples of one quantity. -/
theorem norm_iteratedFDeriv_sum_le_mul {κ : Type*} (s : Finset κ) {f : κ → E → F} {p : ℕ}
    {x : E} {b : κ → ℝ} {S : ℝ} (hf : ∀ k ∈ s, ContDiff ℝ (p : ℕ∞) (f k))
    (hb : ∀ k ∈ s, ‖iteratedFDeriv ℝ p (f k) x‖ ≤ b k * S) :
    ‖iteratedFDeriv ℝ p (fun z => ∑ k ∈ s, f k z) x‖ ≤ (∑ k ∈ s, b k) * S :=
  (AVRegularity.norm_iteratedFDeriv_sum_le' s hf x).trans
    ((Finset.sum_le_sum hb).trans_eq (Finset.sum_mul s b S).symm)

/-- A constant multiple of a field whose jet is bounded by a multiple of a quantity. -/
theorem norm_iteratedFDeriv_const_smul_le_mul {f : E → F} {p : ℕ} {x : E} {b S : ℝ} (r : ℝ)
    (hf : ContDiff ℝ (p : ℕ∞) f) (hb : ‖iteratedFDeriv ℝ p f x‖ ≤ b * S) :
    ‖iteratedFDeriv ℝ p (fun z => r • f z) x‖ ≤ |r| * b * S := by
  rw [iteratedFDeriv_const_smul_apply' hf.contDiffAt, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (abs_nonneg r)

/-- **Leibniz bound with uniform factors.** If the jets of order at most `j` of an operator field
and of a vector field at a point are bounded by `A` and `B`, the jet of order `j` of the operator
applied to the vector is bounded by `2 ^ j * A * B`. -/
theorem norm_iteratedFDeriv_clm_apply_le_two_pow {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E → F →L[ℝ] G} {g : E → F} {J j : ℕ} (hf : ContDiff ℝ (J : ℕ∞) f)
    (hg : ContDiff ℝ (J : ℕ∞) g) (hj : j ≤ J) (x : E) {A B : ℝ}
    (hA : ∀ p ≤ j, ‖iteratedFDeriv ℝ p f x‖ ≤ A) (hB : ∀ p ≤ j, ‖iteratedFDeriv ℝ p g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun y => f y (g y)) x‖ ≤ 2 ^ j * A * B := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le j))
  have he : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B) = 2 ^ j * A * B := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hn : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    rw [hn]
  refine (norm_iteratedFDeriv_clm_apply hf hg x (by exact_mod_cast hj)).trans ?_
  rw [← he]
  refine Finset.sum_le_sum fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hA i hij) (Nat.cast_nonneg _))
    (hB (j - i) (Nat.sub_le j i)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA0)

/-- The jets of a composition with a continuous linear map on the right. -/
theorem norm_iteratedFDeriv_comp_clm_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : G →L[ℝ] E) {f : E → F} {j : ℕ} (hf : ContDiff ℝ (j : ℕ∞) f) (x : G) :
    ‖iteratedFDeriv ℝ j (f ∘ T) x‖ ≤ ‖iteratedFDeriv ℝ j f (T x)‖ * ‖T‖ ^ j := by
  rw [T.iteratedFDeriv_comp_right hf x (le_refl _)]
  refine ((iteratedFDeriv ℝ j f (T x)).norm_compContinuousLinearMap_le
    (fun _ : Fin j => T)).trans_eq ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The jets of a field read through a dilation. -/
theorem norm_iteratedFDeriv_comp_smul_le {f : Vec 2 → F} {j : ℕ} (hf : ContDiff ℝ (j : ℕ∞) f)
    (r : ℝ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun x' => f (r • x')) x‖ ≤ ‖iteratedFDeriv ℝ j f (r • x)‖ * |r| ^ j := by
  have he : (fun x' : Vec 2 => f (r • x')) = f ∘ (r • ContinuousLinearMap.id ℝ (Vec 2)) := by
    funext x'; simp
  have hx : (r • ContinuousLinearMap.id ℝ (Vec 2)) x = r • x := by simp
  have hT : ‖r • ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ |r| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg r) ContinuousLinearMap.norm_id_le
  have h1 := norm_iteratedFDeriv_comp_clm_le (r • ContinuousLinearMap.id ℝ (Vec 2)) hf x
  rw [hx] at h1
  rw [he]
  exact h1.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hT j) (norm_nonneg _))

/-- **Jets of the diagonal sample of a box-smooth field.** If the mixed jets
`D_X^r D_z^s c` of total order `r + s ≤ j` are bounded by `Mc`, the jet of order `j` of the sample
`y ↦ c(y/ρ, y/e)` is bounded by `(2 (|ρ⁻¹| + |e⁻¹|)) ^ j * Mc`. -/
theorem norm_iteratedFDeriv_sample_le {p q j : ℕ} {c : Vec 2 → Vec 2 → F}
    (hc : IsBoxSmooth p q c) (hp : j ≤ p) (hq : j ≤ q) (ρs es : ℝ) {Mc : ℝ}
    (hM : ∀ r s, r + s ≤ j → ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (c Y) z) X‖ ≤ Mc) (y : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y' : Vec 2 => c (ρs⁻¹ • y') (es⁻¹ • y')) y‖ ≤
      (2 * (|ρs⁻¹| + |es⁻¹|)) ^ j * Mc := by
  have hM0 : 0 ≤ Mc := (norm_nonneg _).trans (hM 0 0 (by omega) 0 0)
  have hbox : IsBoxSmooth j j c := hc.mono hp hq
  have hjoint : ContDiff ℝ (j : ℕ∞) (Function.uncurry c) := hbox.contDiff_uncurry le_rfl le_rfl
  have he : (fun y' : Vec 2 => c (ρs⁻¹ • y') (es⁻¹ • y')) =
      Function.uncurry c ∘ sampleMap ρs es := by
    funext y'
    rw [Function.comp_apply, sampleMap_apply, Function.uncurry_apply_pair]
  have h1 := norm_iteratedFDeriv_comp_clm_le (sampleMap ρs es) hjoint y
  have h2 := AVRegularity.EntryWeakProofs.box_joint_derivative_bound j F c hbox Mc hM0 hM
    (sampleMap ρs es y)
  rw [he]
  refine (h1.trans (mul_le_mul h2
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sampleMap_le ρs es) j)
    (pow_nonneg (norm_nonneg _) j) (mul_nonneg (pow_nonneg zero_le_two j) hM0))).trans_eq ?_
  rw [mul_pow, mul_right_comm]

/-- The jets of the diagonal sample of a box-smooth field, uniformly in the order `j ≤ J`. -/
theorem norm_iteratedFDeriv_sample_le_uniform {p q J : ℕ} {c : Vec 2 → Vec 2 → F}
    (hc : IsBoxSmooth p q c) (hp : J ≤ p) (hq : J ≤ q) (ρs es : ℝ) {Mc : ℝ}
    (hM : ∀ r s, r + s ≤ J → ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (c Y) z) X‖ ≤ Mc) {j : ℕ} (hj : j ≤ J)
    (y : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y' : Vec 2 => c (ρs⁻¹ • y') (es⁻¹ • y')) y‖ ≤
      (max (2 * (|ρs⁻¹| + |es⁻¹|)) 1) ^ J * Mc := by
  have hM0 : 0 ≤ Mc := (norm_nonneg _).trans (hM 0 0 (by omega) 0 0)
  have hR : (0 : ℝ) ≤ 2 * (|ρs⁻¹| + |es⁻¹|) :=
    mul_nonneg zero_le_two (add_nonneg (abs_nonneg _) (abs_nonneg _))
  exact (norm_iteratedFDeriv_sample_le hc (hj.trans hp) (hj.trans hq) ρs es
    (fun r s hrs => hM r s (hrs.trans hj)) y).trans
    (mul_le_mul_of_nonneg_right (pow_le_max_one_pow hR hj) hM0)

/-- **Jets of a composition with a chart.** If the jets of orders `1, …, J` of the chart `ψ` are
bounded by `Cψ ≥ 1`, the jet of order `j ≤ J` of `Φ ∘ ψ` at `x` is bounded by `j! Cψ ^ j` times the
sum of the jets of orders at most `j` of `Φ` at `ψ x`. -/
theorem norm_iteratedFDeriv_comp_chart_le {J : ℕ} {Φ : Vec 2 → F} (hΦ : ContDiff ℝ (J : ℕ∞) Φ)
    {ψ : Vec 2 → Vec 2} (hψ : ContDiff ℝ (J : ℕ∞) ψ) {Cψ : ℝ} (hC : 1 ≤ Cψ)
    (hψb : ∀ i, 1 ≤ i → i ≤ J → ∀ x, ‖iteratedFDeriv ℝ i ψ x‖ ≤ Cψ) {j : ℕ} (hj : j ≤ J)
    (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (Φ ∘ ψ) x‖ ≤
      (j.factorial : ℝ) * Cψ ^ j * ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i Φ (ψ x)‖ := by
  have hS : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i Φ (ψ x)‖ ≤
      ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i Φ (ψ x)‖ := fun i hi =>
    Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i Φ (ψ x)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have hD : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i ψ x‖ ≤ Cψ ^ i := fun i hi hij =>
    (hψb i hi (hij.trans hj) x).trans (le_self_pow₀ hC (by omega))
  exact (norm_iteratedFDeriv_comp_le hΦ hψ (by exact_mod_cast hj) x hS hD).trans_eq (by ring)

/-- **Jets of a field read in a chart.** For a chart `χ` whose jets of orders `1, …, J` are bounded
by `Cχ ≥ 1`, the jet of order `j ≤ J` of `X ↦ a₀(χ(ρ X))` at `X` is bounded by
`j! Cχ ^ j |ρ| ^ j` times the sum of the jets of orders at most `j` of `a₀` at `χ(ρ X)`. -/
theorem norm_iteratedFDeriv_chartRead_le {J : ℕ} {a₀ : Vec 2 → F} (ha : ContDiff ℝ (J : ℕ∞) a₀)
    {χ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (J : ℕ∞) χ) {Cχ : ℝ} (hC : 1 ≤ Cχ)
    (hχb : ∀ i, 1 ≤ i → i ≤ J → ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ Cχ) (ρ : ℝ) {j : ℕ}
    (hj : j ≤ J) (X : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun X' : Vec 2 => a₀ (χ (ρ • X'))) X‖ ≤
      (j.factorial : ℝ) * Cχ ^ j * |ρ| ^ j *
        ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i a₀ (χ (ρ • X))‖ := by
  have hcomp : ContDiff ℝ (j : ℕ∞) (a₀ ∘ χ) := (ha.comp hχ).of_le (by exact_mod_cast hj)
  refine (norm_iteratedFDeriv_comp_smul_le hcomp ρ X).trans ?_
  refine (mul_le_mul_of_nonneg_right
    (norm_iteratedFDeriv_comp_chart_le ha hχ hC hχb hj (ρ • X))
    (pow_nonneg (abs_nonneg ρ) j)).trans_eq ?_
  ring

end Generic

section LiftSum

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The jets of a component are bounded by the jets of the field. -/
theorem norm_iteratedFDeriv_pi_apply_le {g : Vec 2 → ∀ i, h i} {p : ℕ}
    (hg : ContDiff ℝ (p : ℕ∞) g) (u : ι) (X : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => g Y u) X‖ ≤ ‖iteratedFDeriv ℝ p g X‖ := by
  have hP : ‖ContinuousLinearMap.proj (R := ℝ) (φ := h) u‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      rw [one_mul]; exact norm_le_pi_norm w u
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).norm_iteratedFDeriv_comp_left
    (hg.contDiffAt (x := X)) (n := p) (by exact_mod_cast le_rfl)
  exact h1.trans
    (le_of_le_of_eq (mul_le_mul_of_nonneg_right hP (norm_nonneg _)) (one_mul _))

/-- A word derivative of order at most `N` of a `C^{N+J}` coarse field, read at the slow scale, is
of class `C^J`. -/
theorem contDiff_wordSample {J N m : ℕ} (hm : m ≤ N) (α : DerivativeWord2 m)
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ ((N + J : ℕ) : ℕ∞) a₀) (u : ι) (ρs : ℝ) :
    ContDiff ℝ (J : ℕ∞) (fun y' : Vec 2 => orderedDerivative α a₀ (ρs⁻¹ • y') u) := by
  have ha' : ContDiff ℝ ((J + m : ℕ) : ℕ∞) a₀ :=
    ha.of_le (by exact_mod_cast (by omega : J + m ≤ N + J))
  have h1 : ContDiff ℝ (J : ℕ∞) (fun X => orderedDerivative α a₀ X u) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp
      (AVRegularity.contDiff_orderedDerivative α ha')
  exact h1.comp (contDiff_const_smul ρs⁻¹)

/-- The jets of a word derivative of a coarse field read at the slow scale are bounded by the jets
of the field at the same point. -/
theorem norm_iteratedFDeriv_wordSample_le {m p : ℕ} (α : DerivativeWord2 m)
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ ((p + m : ℕ) : ℕ∞) a₀) (u : ι) (ρs : ℝ)
    (y : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun y' : Vec 2 => orderedDerivative α a₀ (ρs⁻¹ • y') u) y‖ ≤
      ‖iteratedFDeriv ℝ (p + m) a₀ (ρs⁻¹ • y)‖ * |ρs⁻¹| ^ p := by
  have h1 : ContDiff ℝ (p : ℕ∞) (orderedDerivative α a₀) :=
    AVRegularity.contDiff_orderedDerivative α ha
  have h2 : ContDiff ℝ (p : ℕ∞) (fun X => orderedDerivative α a₀ X u) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp h1
  refine (norm_iteratedFDeriv_comp_smul_le h2 ρs⁻¹ y).trans ?_
  exact mul_le_mul_of_nonneg_right
    ((norm_iteratedFDeriv_pi_apply_le h1 u (ρs⁻¹ • y)).trans
      (AVRegularity.norm_iteratedFDeriv_orderedDerivative_le α ha (ρs⁻¹ • y)))
    (pow_nonneg (abs_nonneg _) p)

/-- One summand of the label lift, an operator field applied to a word derivative of the coarse
field read at the slow scale, is of class `C^J`. -/
theorem contDiff_liftTerm {J N m : ℕ} (hm : m ≤ N) (α : DerivativeWord2 m) {u v : ι}
    {f : Vec 2 → h u →L[ℝ] h v} (hf : ContDiff ℝ (J : ℕ∞) f) {a₀ : Vec 2 → ∀ i, h i}
    (ha : ContDiff ℝ ((N + J : ℕ) : ℕ∞) a₀) (ρs : ℝ) :
    ContDiff ℝ (J : ℕ∞) (fun y' : Vec 2 => f y' (orderedDerivative α a₀ (ρs⁻¹ • y') u)) :=
  hf.clm_apply (contDiff_wordSample hm α ha u ρs)

/-- **Jets of one summand of the label lift.** If the jets of order at most `J` of the operator
field are bounded by `A`, the jet of order `j ≤ J` of the summand at `y` is bounded by a constant
times the sum of the jets of orders at most `N + j` of the coarse field at `y/ρ`. -/
theorem norm_iteratedFDeriv_liftTerm_le {J N m : ℕ} (hm : m ≤ N) (α : DerivativeWord2 m)
    {u v : ι} {f : Vec 2 → h u →L[ℝ] h v} (hf : ContDiff ℝ (J : ℕ∞) f) {A : ℝ}
    (hA : ∀ j ≤ J, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ A) {a₀ : Vec 2 → ∀ i, h i}
    (ha : ContDiff ℝ ((N + J : ℕ) : ℕ∞) a₀) (ρs : ℝ) {j : ℕ} (hj : j ≤ J) (y : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y' : Vec 2 => f y' (orderedDerivative α a₀ (ρs⁻¹ • y') u)) y‖ ≤
      2 ^ J * A * (max |ρs⁻¹| 1) ^ J *
        ∑ i ∈ Finset.range (N + j + 1), ‖iteratedFDeriv ℝ i a₀ (ρs⁻¹ • y)‖ := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le J) y)
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (N + j + 1), ‖iteratedFDeriv ℝ i a₀ (ρs⁻¹ • y)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hR0 : 0 ≤ (max |ρs⁻¹| 1) ^ J :=
    pow_nonneg (le_trans zero_le_one (le_max_right _ _)) J
  have hw : ContDiff ℝ (J : ℕ∞) (fun y' : Vec 2 => orderedDerivative α a₀ (ρs⁻¹ • y') u) :=
    contDiff_wordSample hm α ha u ρs
  have hB : ∀ p ≤ j,
      ‖iteratedFDeriv ℝ p (fun y' : Vec 2 => orderedDerivative α a₀ (ρs⁻¹ • y') u) y‖ ≤
        (∑ i ∈ Finset.range (N + j + 1), ‖iteratedFDeriv ℝ i a₀ (ρs⁻¹ • y)‖) *
          (max |ρs⁻¹| 1) ^ J := by
    intro p hp
    have hap : ContDiff ℝ ((p + m : ℕ) : ℕ∞) a₀ :=
      ha.of_le (by exact_mod_cast (by omega : p + m ≤ N + J))
    refine (norm_iteratedFDeriv_wordSample_le α hap u ρs y).trans ?_
    refine mul_le_mul ?_ (pow_le_max_one_pow (abs_nonneg _) (hp.trans hj))
      (pow_nonneg (abs_nonneg _) p) hS0
    exact Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i a₀ (ρs⁻¹ • y)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have h1 := norm_iteratedFDeriv_clm_apply_le_two_pow hf hw hj y
    (fun p hp => hA p (hp.trans hj) y) hB
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ one_le_two hj
  refine h1.trans ?_
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hA0)
    (mul_nonneg hS0 hR0)).trans_eq ?_
  ring

/-- **The coefficient sum of the label lift is of class `C^J`** when the sampled coefficients are
`C^J` and the coarse field is `C^{N+J}`. -/
theorem contDiff_liftSum (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε ρs es τ : ℝ) (v : ι)
    {J : ℕ}
    (hcoef : ∀ hh ≤ H, ∀ n ≤ N, ∀ q : LiftActionIndex ι n, ContDiff ℝ (J : ℕ∞)
      (fun y : Vec 2 => Cc hh n q.1.val q.2.1 τ (ρs⁻¹ • y) (es⁻¹ • y) v q.2.2))
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ ((N + J : ℕ) : ℕ∞) a₀) :
    ContDiff ℝ (J : ℕ∞) (fun y : Vec 2 => ∑ hh ∈ Finset.range (H + 1),
      ∑ n ∈ Finset.range (N + 1), ε ^ n • ∑ q : LiftActionIndex ι n,
        Cc hh n q.1.val q.2.1 τ (ρs⁻¹ • y) (es⁻¹ • y) v q.2.2
          (orderedDerivative q.2.1 a₀ (ρs⁻¹ • y) q.2.2)) :=
  ContDiff.sum fun hh hhm => ContDiff.sum fun n hnm => ContDiff.const_smul (ε ^ n)
    (ContDiff.sum fun q _ => contDiff_liftTerm
      ((Nat.lt_succ_iff.1 q.1.isLt).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hnm))) q.2.1
      (hcoef hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) n
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hnm)) q) ha ρs)

/-- **Jets of the coefficient sum of the label lift.** If the jets of order at most `J` of the
sampled coefficients are bounded by `A hh n q`, the jet of order `j ≤ J` of the coefficient sum at
`y` is bounded by an explicit constant times the sum of the jets of orders at most `N + j` of the
coarse field at `y/ρ`. -/
theorem norm_iteratedFDeriv_liftSum_le (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ)
    (ε ρs es τ : ℝ) (v : ι) {J : ℕ} (A : ℕ → (n : ℕ) → LiftActionIndex ι n → ℝ)
    (hcoef : ∀ hh ≤ H, ∀ n ≤ N, ∀ q : LiftActionIndex ι n,
      ContDiff ℝ (J : ℕ∞)
        (fun y : Vec 2 => Cc hh n q.1.val q.2.1 τ (ρs⁻¹ • y) (es⁻¹ • y) v q.2.2) ∧
      ∀ j ≤ J, ∀ y, ‖iteratedFDeriv ℝ j
        (fun y' : Vec 2 => Cc hh n q.1.val q.2.1 τ (ρs⁻¹ • y') (es⁻¹ • y') v q.2.2) y‖ ≤
          A hh n q)
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ ((N + J : ℕ) : ℕ∞) a₀) {j : ℕ} (hj : j ≤ J)
    (y : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y' : Vec 2 => ∑ hh ∈ Finset.range (H + 1),
        ∑ n ∈ Finset.range (N + 1), ε ^ n • ∑ q : LiftActionIndex ι n,
          Cc hh n q.1.val q.2.1 τ (ρs⁻¹ • y') (es⁻¹ • y') v q.2.2
            (orderedDerivative q.2.1 a₀ (ρs⁻¹ • y') q.2.2)) y‖ ≤
      (∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1), |ε ^ n| *
        ∑ q : LiftActionIndex ι n, 2 ^ J * A hh n q * (max |ρs⁻¹| 1) ^ J) *
        ∑ i ∈ Finset.range (N + j + 1), ‖iteratedFDeriv ℝ i a₀ (ρs⁻¹ • y)‖ := by
  have hterm : ∀ hh ≤ H, ∀ n ≤ N, ∀ q : LiftActionIndex ι n, ContDiff ℝ (j : ℕ∞)
      (fun y' : Vec 2 => Cc hh n q.1.val q.2.1 τ (ρs⁻¹ • y') (es⁻¹ • y') v q.2.2
        (orderedDerivative q.2.1 a₀ (ρs⁻¹ • y') q.2.2)) := fun hh hhh n hn q =>
    (contDiff_liftTerm ((Nat.lt_succ_iff.1 q.1.isLt).trans hn) q.2.1 (hcoef hh hhh n hn q).1 ha
      ρs).of_le (by exact_mod_cast hj)
  have hinner : ∀ hh ≤ H, ∀ n ≤ N, ContDiff ℝ (j : ℕ∞)
      (fun y' : Vec 2 => ∑ q : LiftActionIndex ι n,
        Cc hh n q.1.val q.2.1 τ (ρs⁻¹ • y') (es⁻¹ • y') v q.2.2
          (orderedDerivative q.2.1 a₀ (ρs⁻¹ • y') q.2.2)) := fun hh hhh n hn =>
    ContDiff.sum fun q _ => hterm hh hhh n hn q
  refine norm_iteratedFDeriv_sum_le_mul _ (fun hh hhm => ContDiff.sum fun n hnm =>
    (hinner hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) n
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hnm))).const_smul (ε ^ n)) (fun hh hhm => ?_)
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
  refine norm_iteratedFDeriv_sum_le_mul _ (fun n hnm =>
    (hinner hh hhh n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hnm))).const_smul (ε ^ n))
    (fun n hnm => ?_)
  have hn : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hnm)
  refine norm_iteratedFDeriv_const_smul_le_mul (ε ^ n) (hinner hh hhh n hn) ?_
  refine norm_iteratedFDeriv_sum_le_mul _ (fun q _ => hterm hh hhh n hn q) (fun q _ => ?_)
  exact norm_iteratedFDeriv_liftTerm_le ((Nat.lt_succ_iff.1 q.1.isLt).trans hn) q.2.1
    (hcoef hh hhh n hn q).1 (hcoef hh hhh n hn q).2 ha ρs hj y

end LiftSum

section Linear

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

/-- The label lift of a sum of two coarse fields of class `C^N` at the cell time. -/
theorem labelLift_add_input (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε : ℝ)
    (A B : ℝ → Vec 2 → ∀ i, h i) (ρs es c t : ℝ) (hA : ContDiff ℝ (N : ℕ∞) (A (c⁻¹ * t)))
    (hB : ContDiff ℝ (N : ℕ∞) (B (c⁻¹ * t))) (y : Vec 2) :
    labelLift Cc N H ε (fun s X => A s X + B s X) ρs es c t y =
      labelLift Cc N H ε A ρs es c t y + labelLift Cc N H ε B ρs es c t y := by
  simp only [labelLift]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun hh _ =>
    liftPolyField_add_input Cc N ε hh A B (c⁻¹ * t) hA hB (ρs⁻¹ • y) (es⁻¹ • y)

/-- The label lift of a difference of two coarse fields of class `C^N` at the cell time. -/
theorem labelLift_sub_input (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε : ℝ)
    (g₁ g₂ : ℝ → Vec 2 → ∀ i, h i) (ρs es c t : ℝ)
    (hg₁ : ContDiff ℝ (N : ℕ∞) (g₁ (c⁻¹ * t))) (hg₂ : ContDiff ℝ (N : ℕ∞) (g₂ (c⁻¹ * t)))
    (y : Vec 2) :
    labelLift Cc N H ε (fun s X => g₁ s X - g₂ s X) ρs es c t y =
      labelLift Cc N H ε g₁ ρs es c t y - labelLift Cc N H ε g₂ ρs es c t y := by
  have he : (fun s X => g₁ s X - g₂ s X) = fun s X => g₁ s X + (-1 : ℝ) • g₂ s X := by
    funext s X
    rw [neg_one_smul, sub_eq_add_neg]
  rw [he, labelLift_add_input Cc N H ε g₁ (fun s X => (-1 : ℝ) • g₂ s X) ρs es c t hg₁
      (hg₂.const_smul (-1 : ℝ)) y,
    labelLift_smul_input Cc N H ε (-1) g₂ ρs es c t hg₂ y, neg_one_smul, sub_eq_add_neg]

end Linear

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

variable {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **Jets of the sampled lift coefficients.** On the lift window the diagonal sample of a lift
coefficient is of class `C^J` and its jets of order at most `J` are bounded, for `J` below the
slow and fast reserves of the coefficients. -/
theorem setting_coeffSample_jet_bound (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ρs es : ℝ) {J : ℕ}
    (hJp : J ≤ K + N + 2 * D + 2) (hJq : J ≤ max k (L + 2) + 2 * D) (hh : ℕ) (hhh : hh ≤ H)
    (n m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ τ ∈ Icc a b,
      ContDiff ℝ (J : ℕ∞) (fun y : Vec 2 => Cc hh n m α τ (ρs⁻¹ • y) (es⁻¹ • y) v u) ∧
      ∀ j ≤ J, ∀ y, ‖iteratedFDeriv ℝ j
        (fun y' : Vec 2 => Cc hh n m α τ (ρs⁻¹ • y') (es⁻¹ • y') v u) y‖ ≤ A := by
  have data := TailConstructed.setting_tailRaw_coefficient_data P sX sZ hsZ Cc hseq J J hJp hJq
    hh hhh n
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  obtain ⟨Mvu, hMvu, hbox, hbd⟩ : ∃ Mvu : ℝ, 0 ≤ Mvu ∧
      (∀ τ ∈ Icc a b, IsBoxSmooth J J (fun X z => Cc hh n m α τ X z v u)) ∧
      ∀ r ≤ J, ∀ s ≤ J, ∀ τ ∈ Icc a b, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun z' => Cc hh n m α τ Y z' v u) z)
          X‖ ≤ Mvu * lam ^ (n - m + r) :=
    ⟨_, data.nonneg v u, data.box m hm α v u, data.bound m hm α v u⟩
  have hM0 : 0 ≤ Mvu * (max lam 1) ^ (n + J) :=
    mul_nonneg hMvu (pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _)
  refine ⟨(max (2 * (|ρs⁻¹| + |es⁻¹|)) 1) ^ J * (Mvu * (max lam 1) ^ (n + J)),
    mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _) hM0,
    fun τ hτ => ⟨CoarseFluxDiff.contDiff_sample (hbox τ hτ) le_rfl le_rfl ρs es,
      fun j hj y => ?_⟩⟩
  have hM : ∀ r s, r + s ≤ J → ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun z' => Cc hh n m α τ Y z' v u) z)
        X‖ ≤ Mvu * (max lam 1) ^ (n + J) := fun r s hrs X z =>
    (hbd r (by omega) s (by omega) τ hτ X z).trans
      (mul_le_mul_of_nonneg_left (pow_le_max_one_pow hlam (by omega)) hMvu)
  exact norm_iteratedFDeriv_sample_le_uniform (hbox τ hτ) le_rfl le_rfl ρs es hM hj y

include P in
/-- **Jets of the label lift.** For `J` below the reserves of the lift coefficients there is a
constant `M`, independent of the coarse field, the time and the label, such that for every coarse
field `g` of class `C^{N+J}` at a cell time `t/c` of the lift window the label lift is of class
`C^J` in the label and its jet of order `j ≤ J` at `y` is bounded by `M` times the sum of the jets
of orders at most `N + j` of `g(t/c, ·)` at `y/ρ`. -/
theorem setting_labelLift_jets (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε ρs es c : ℝ) {J : ℕ}
    (hJp : J ≤ K + N + 2 * D + 2) (hJq : J ≤ max k (L + 2) + 2 * D) (v : ι) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : ℝ → Vec 2 → ∀ i, h i) (t : ℝ), c⁻¹ * t ∈ Icc a b →
      ContDiff ℝ ((N + J : ℕ) : ℕ∞) (g (c⁻¹ * t)) →
      ContDiff ℝ (J : ℕ∞) (fun y : Vec 2 => labelLift Cc N H ε g ρs es c t y v) ∧
      ∀ j ≤ J, ∀ y,
        ‖iteratedFDeriv ℝ j (fun y' : Vec 2 => labelLift Cc N H ε g ρs es c t y' v) y‖ ≤
          M * ∑ i ∈ Finset.range (N + j + 1),
            ‖iteratedFDeriv ℝ i (g (c⁻¹ * t)) (ρs⁻¹ • y)‖ := by
  have hcoef : ∀ (hh n : ℕ) (q : LiftActionIndex ι n), ∃ A : ℝ, 0 ≤ A ∧ (hh ≤ H →
      ∀ τ ∈ Icc a b, ContDiff ℝ (J : ℕ∞)
        (fun y : Vec 2 => Cc hh n q.1.val q.2.1 τ (ρs⁻¹ • y) (es⁻¹ • y) v q.2.2) ∧
      ∀ j ≤ J, ∀ y, ‖iteratedFDeriv ℝ j
        (fun y' : Vec 2 => Cc hh n q.1.val q.2.1 τ (ρs⁻¹ • y') (es⁻¹ • y') v q.2.2) y‖ ≤
          A) := by
    intro hh n q
    by_cases hhh : hh ≤ H
    · obtain ⟨A, hA0, hA⟩ := setting_coeffSample_jet_bound P sX sZ hsZ Cc hseq ρs es hJp hJq
        hh hhh n q.1.val (Nat.lt_succ_iff.1 q.1.isLt) q.2.1 v q.2.2
      exact ⟨A, hA0, fun _ => hA⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hhh⟩
  choose A hA0 hA using hcoef
  refine ⟨∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1), |ε ^ n| *
    ∑ q : LiftActionIndex ι n, 2 ^ J * A hh n q * (max |ρs⁻¹| 1) ^ J, ?_,
    fun g t ht hg => ?_⟩
  · exact Finset.sum_nonneg fun hh _ => Finset.sum_nonneg fun n _ =>
      mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun q _ =>
        mul_nonneg (mul_nonneg (pow_nonneg zero_le_two _) (hA0 hh n q))
          (pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _))
  · have he : (fun y' : Vec 2 => labelLift Cc N H ε g ρs es c t y' v) = fun y' : Vec 2 =>
        ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1), ε ^ n •
          ∑ q : LiftActionIndex ι n, Cc hh n q.1.val q.2.1 (c⁻¹ * t) (ρs⁻¹ • y') (es⁻¹ • y') v
            q.2.2 (orderedDerivative q.2.1 (g (c⁻¹ * t)) (ρs⁻¹ • y') q.2.2) :=
      funext fun y' => labelLift_coeff_sum Cc N H ε g ρs es c t y' v
    refine ⟨?_, fun j hj y => ?_⟩
    · rw [he]
      exact contDiff_liftSum Cc N H ε ρs es (c⁻¹ * t) v
        (fun hh hhh n _ q => (hA hh n q hhh _ ht).1) hg
    · rw [he]
      exact norm_iteratedFDeriv_liftSum_le Cc N H ε ρs es (c⁻¹ * t) v A
        (fun hh hhh n _ q => hA hh n q hhh _ ht) hg hj y

include P in
/-- **Jet bound of the label lift.** The spatial jets of order `j ≤ J` of the label lift at `y`
are bounded by a constant, independent of the coarse field, the time and the label, times the sum
of the jets of orders at most `N + j` of the coarse field at `y/ρ`, uniformly on the lift
window. -/
theorem setting_labelLift_jet_bound (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε ρs es c : ℝ) {J : ℕ}
    (hJp : J ≤ K + N + 2 * D + 2) (hJq : J ≤ max k (L + 2) + 2 * D) (v : ι) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : ℝ → Vec 2 → ∀ i, h i) (t : ℝ), c⁻¹ * t ∈ Icc a b →
      ContDiff ℝ ((N + J : ℕ) : ℕ∞) (g (c⁻¹ * t)) → ∀ j ≤ J, ∀ y,
        ‖iteratedFDeriv ℝ j (fun y' : Vec 2 => labelLift Cc N H ε g ρs es c t y' v) y‖ ≤
          M * ∑ i ∈ Finset.range (N + j + 1),
            ‖iteratedFDeriv ℝ i (g (c⁻¹ * t)) (ρs⁻¹ • y)‖ := by
  obtain ⟨M, hM0, hM⟩ := setting_labelLift_jets P sX sZ hsZ Cc hseq ε ρs es c hJp hJq v
  exact ⟨M, hM0, fun g t ht hg => (hM g t ht hg).2⟩

include P in
/-- **Finite smoothness of the components of the label lift.** The components of the label lift of
a coarse field of class `C^{N+J}` at a cell time of the lift window are of class `C^J` in the
label. -/
theorem setting_labelLift_apply_contDiff_finite (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε ρs es c : ℝ)
    {J : ℕ} (hJp : J ≤ K + N + 2 * D + 2) (hJq : J ≤ max k (L + 2) + 2 * D) (v : ι)
    (g : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ht : c⁻¹ * t ∈ Icc a b)
    (hg : ContDiff ℝ ((N + J : ℕ) : ℕ∞) (g (c⁻¹ * t))) :
    ContDiff ℝ (J : ℕ∞) (fun y : Vec 2 => labelLift Cc N H ε g ρs es c t y v) := by
  obtain ⟨_, -, hM⟩ := setting_labelLift_jets P sX sZ hsZ Cc hseq ε ρs es c hJp hJq v
  exact (hM g t ht hg).1

include P in
/-- **Finite smoothness of the label lift.** The label lift of a coarse field of class `C^{N+J}`
at a cell time of the lift window is of class `C^J` in the label. -/
theorem setting_labelLift_contDiff_finite (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε ρs es c : ℝ)
    {J : ℕ} (hJp : J ≤ K + N + 2 * D + 2) (hJq : J ≤ max k (L + 2) + 2 * D)
    (g : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ht : c⁻¹ * t ∈ Icc a b)
    (hg : ContDiff ℝ ((N + J : ℕ) : ℕ∞) (g (c⁻¹ * t))) :
    ContDiff ℝ (J : ℕ∞) (labelLift Cc N H ε g ρs es c t) :=
  contDiff_pi.2 fun v => setting_labelLift_apply_contDiff_finite P sX sZ hsZ Cc hseq ε ρs es c
    hJp hJq v g t ht hg

end AVRegularity.CycleComparison.Reconstruction
end
