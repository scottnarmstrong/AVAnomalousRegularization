-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.PulseIdentity
public import AVRegularity.CycleComparison.Reconstruction.LiftJetBound
import AVRegularity.CycleComparison.Reconstruction.PiolaTested
public import AVRegularity.CycleComparison.Reconstruction.CoarseRescale
public import AVRegularity.CycleComparison.Reconstruction.TailSample
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import AVRegularity.CycleComparison.Lift.SettingLiftPolyTimeIntegral
public import AVRegularity.CycleComparison.Lift.SettingLiftSourceBlockCoefficient
public import AVRegularity.CycleComparison.LiftMeanEntrywise.Letter
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
import AVenhance.Infra.Classical.Drift
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
open scoped Matrix
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The weak identity of one pulse lift**. For a
smooth periodic test `φ`, the physical lift `𝒯(t, x) = V(t, ψ(t, x))` of one pulse satisfies on the
physical window
`d/dt ∫ ⟪𝒯, φ⟫ = -∫ ⟪(b_k + b) · ∇𝒯, φ⟫ - ν ∫ ⟪∇𝒯, ∇φ⟫ + c⁻¹ ∫ ⟪(rest)(ψ x), φ⟫`
(`setting_pulse_weak`), where `b = b_{m-1}` is the background velocity of the chart flow and
`b_k` the pushed-forward pulse velocity (`b_k + b = b_m` where only the pulse is active). The label
density is read in physical operators (`labelDensity_physical`), and the Laplacian and the
transport of the test are integrated by parts on the cell (`cell_ibp_laplacian`,
`cell_ibp_transport`). -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

/-- The physical lift of one pulse: the label lift read at the labels of the pulse's chart. -/
def pulseLift (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε : ℝ) (f : ℝ → Vec 2 → ∀ i, h i)
    (ρs es c : ℝ) (ψ : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : ∀ i, h i :=
  labelLift Cc N H ε f ρs es c t (ψ t x)

/-- **Combining the weak forms on the cell.** If `L = -(bk · ∇U) + ν ΔU + c⁻¹ R` pointwise, for a
`C²` periodic `U`, a `C¹` periodic divergence-free `b`, a continuous `bk`, and the tested `L` is
integrable, then the tested `L` plus the transport of the test by `b` is the weak form of
`-(bk + b) · ∇U + ν ΔU + c⁻¹ R`. -/
theorem cell_weak_combine {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {U : Vec 2 → E} (hU : ContDiff ℝ 2 U) (hUp : IsZ2Periodic U)
    {φt : Vec 2 → E} (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt)
    {b : Vec 2 → Vec 2} (hb : ContDiff ℝ 1 b) (hbp : IsZ2Periodic b)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (fun y => b y k) x (basisVec k) = 0)
    {bk : Vec 2 → Vec 2} (hbk : Continuous bk) {νs c : ℝ} (hc : c ≠ 0) (L R : Vec 2 → E)
    (hL : ∀ x, L x = -(∑ k, bk x k • fderiv ℝ U x (basisVec k)) +
      νs • ∑ k, fderiv ℝ (fun y => fderiv ℝ U y (basisVec k)) x (basisVec k) + c⁻¹ • R x)
    (hLi : Integrable (fun x => inner ℝ (L x) (φt x)) (volume.restrict AVenhance.unitCube)) :
    ∫ x in AVenhance.unitCube, (inner ℝ (L x) (φt x) +
        inner ℝ (U x) (∑ k : Fin 2, b x k • fderiv ℝ φt x (basisVec k))) =
      -(∫ x in AVenhance.unitCube,
          inner ℝ (∑ k, (bk x k + b x k) • fderiv ℝ U x (basisVec k)) (φt x)) -
        νs * (∫ x in AVenhance.unitCube, ∑ k,
          inner ℝ (fderiv ℝ U x (basisVec k)) (fderiv ℝ φt x (basisVec k))) +
        c⁻¹ * ∫ x in AVenhance.unitCube, inner ℝ (R x) (φt x) := by
  have hdU : ∀ k : Fin 2, Continuous (fun x => fderiv ℝ U x (basisVec k)) := fun k =>
    (hU.continuous_fderiv two_ne_zero).clm_apply continuous_const
  have hLU : Continuous (fun x => ∑ k : Fin 2,
      fderiv ℝ (fun y => fderiv ℝ U y (basisVec k)) x (basisVec k)) :=
    continuous_finsetSum _ fun k _ =>
      (((hU.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
        one_ne_zero).clm_apply continuous_const
  have hbc : ∀ k : Fin 2, Continuous (fun x => b x k) := fun k =>
    (continuous_apply k).comp hb.continuous
  have hbkc : ∀ k : Fin 2, Continuous (fun x => bk x k) := fun k => (continuous_apply k).comp hbk
  have hdφ : ∀ k : Fin 2, Continuous (fun x => fderiv ℝ φt x (basisVec k)) := fun k =>
    (hφt.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφc := hφt.continuous
  have hA : Integrable (fun x => inner ℝ (∑ k, bk x k • fderiv ℝ U x (basisVec k)) (φt x))
      (volume.restrict AVenhance.unitCube) :=
    CoupledEnergy.Galerkin.continuous_cell_integrable _
      ((continuous_finsetSum _ fun k _ => (hbkc k).smul (hdU k)).inner hφc)
  have hB : Integrable (fun x => inner ℝ (∑ k : Fin 2,
      fderiv ℝ (fun y => fderiv ℝ U y (basisVec k)) x (basisVec k)) (φt x))
      (volume.restrict AVenhance.unitCube) :=
    CoupledEnergy.Galerkin.continuous_cell_integrable _ (hLU.inner hφc)
  have hS : Integrable (fun x => inner ℝ (∑ k, b x k • fderiv ℝ U x (basisVec k)) (φt x))
      (volume.restrict AVenhance.unitCube) :=
    CoupledEnergy.Galerkin.continuous_cell_integrable _
      ((continuous_finsetSum _ fun k _ => (hbc k).smul (hdU k)).inner hφc)
  have hT : Integrable (fun x => inner ℝ (U x) (∑ k : Fin 2, b x k • fderiv ℝ φt x (basisVec k)))
      (volume.restrict AVenhance.unitCube) :=
    CoupledEnergy.Galerkin.continuous_cell_integrable _
      (hU.continuous.inner (continuous_finsetSum _ fun k _ => (hbc k).smul (hdφ k)))
  have hpt : ∀ x, inner ℝ (L x) (φt x) =
      -inner ℝ (∑ k, bk x k • fderiv ℝ U x (basisVec k)) (φt x) +
        νs * inner ℝ (∑ k : Fin 2,
          fderiv ℝ (fun y => fderiv ℝ U y (basisVec k)) x (basisVec k)) (φt x) +
        c⁻¹ * inner ℝ (R x) (φt x) := fun x => by
    rw [hL x, inner_add_left, inner_add_left, inner_neg_left, real_inner_smul_left,
      real_inner_smul_left]
  have hR : Integrable (fun x => inner ℝ (R x) (φt x)) (volume.restrict AVenhance.unitCube) := by
    refine (((hLi.add hA).sub (hB.const_mul νs)).const_mul c).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hpt x]
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
    linear_combination inner ℝ (R x) (φt x) * hcc
  have hAn : Integrable (fun x => -inner ℝ (∑ k, bk x k • fderiv ℝ U x (basisVec k)) (φt x))
      (volume.restrict AVenhance.unitCube) := hA.neg
  have hB' : Integrable (fun x => νs * inner ℝ (∑ k : Fin 2,
      fderiv ℝ (fun y => fderiv ℝ U y (basisVec k)) x (basisVec k)) (φt x))
      (volume.restrict AVenhance.unitCube) := hB.const_mul νs
  have hR' : Integrable (fun x => c⁻¹ * inner ℝ (R x) (φt x))
      (volume.restrict AVenhance.unitCube) := hR.const_mul c⁻¹
  have hLsplit : ∫ x in AVenhance.unitCube, inner ℝ (L x) (φt x) =
      -(∫ x in AVenhance.unitCube, inner ℝ (∑ k, bk x k • fderiv ℝ U x (basisVec k)) (φt x)) +
        νs * (∫ x in AVenhance.unitCube, inner ℝ (∑ k : Fin 2,
          fderiv ℝ (fun y => fderiv ℝ U y (basisVec k)) x (basisVec k)) (φt x)) +
        c⁻¹ * ∫ x in AVenhance.unitCube, inner ℝ (R x) (φt x) := by
    have hAB : Integrable (fun x => -inner ℝ (∑ k, bk x k • fderiv ℝ U x (basisVec k)) (φt x) +
        νs * inner ℝ (∑ k : Fin 2,
          fderiv ℝ (fun y => fderiv ℝ U y (basisVec k)) x (basisVec k)) (φt x))
        (volume.restrict AVenhance.unitCube) := hAn.add hB'
    simp only [hpt]
    rw [integral_add hAB hR', integral_add hAn hB', integral_neg, integral_const_mul,
      integral_const_mul]
  have hsplit : ∫ x in AVenhance.unitCube,
      inner ℝ (∑ k, (bk x k + b x k) • fderiv ℝ U x (basisVec k)) (φt x) =
      (∫ x in AVenhance.unitCube, inner ℝ (∑ k, bk x k • fderiv ℝ U x (basisVec k)) (φt x)) +
        ∫ x in AVenhance.unitCube, inner ℝ (∑ k, b x k • fderiv ℝ U x (basisVec k)) (φt x) := by
    rw [← integral_add hA hS]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [add_smul, Finset.sum_add_distrib, inner_add_left]
  rw [integral_add hLi hT, hLsplit, hsplit, cell_ibp_laplacian hU hUp hφt hφtp,
    cell_ibp_transport hb hbp hdiv (hU.of_le (by norm_num)) hUp hφt hφtp]
  ring

include P in
/-- **The weak identity of one pulse lift** for a smooth periodic test. -/
theorem setting_pulse_weak (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (hφp : ∀ k, IsZ2Periodic (φ k))
    (α q : ℝ) (Λ m : ℕ) {φs : ℝ → Vec 2 → ℝ} (hφs : IsAdmissibleStream φs) (l : ℤ)
    {c ρs : ℝ} (hc : 0 < c) (hρ : 0 < ρs) (A₀ B₀ : ℝ) (hA : A₀ ≤ c * a) (hB : c * b ≤ B₀)
    (hcf : ∀ k, IsPrimOn A₀ B₀ (cf k) (dcf k))
    (hG : ∀ s i j, Differentiable ℝ (fun X => Q.G s X i j))
    (w : ℝ → Vec 2 → Vec 2) {es νs c₁ : ℝ}
    (hv : ∀ s z, Q.v s z = c₁ • w s z)
    (h1 : c * νs * es⁻¹ * es⁻¹ = 1) (h2 : ε * Real.sqrt Q.η = c * νs * es⁻¹ * ρs⁻¹)
    (h3 : ε ^ 2 * Q.η = c * νs * ρs⁻¹ * ρs⁻¹) (hc₁ : c₁ = c * es⁻¹) (M : ℕ) (hM : es⁻¹ = M)
    (hGs : ∀ (n : Fin 2 → ℤ) t X i j, Q.G t (X + ρs⁻¹ • latticeShift n) i j = Q.G t X i j)
    (hcs : ∀ (n : Fin 2 → ℤ) v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
      γ.coeff α t (X + ρs⁻¹ • latticeShift n) z = γ.coeff α t X z)
    (hGχ : ∀ t ∈ Icc (c * a) (c * b), ∀ y, (fun i j => Q.G (c⁻¹ * t) (ρs⁻¹ • y) i j) =
      (jacMatrix (ocChart α q Λ m φs hφs l t) y)⁻¹ *
        ((jacMatrix (ocChart α q Λ m φs hφs l t) y)⁻¹)ᵀ)
    (bk : ℝ → Vec 2 → Vec 2) (hbk : ∀ t ∈ Icc (c * a) (c * b), Continuous (bk t))
    (hwb : ∀ t ∈ Icc (c * a) (c * b), ∀ x,
      (jacMatrix (ocChart α q Λ m φs hφs l t) (ocChartInv α q Λ m φs hφs l t x)).mulVec
        (w (c⁻¹ * t) (es⁻¹ • ocChartInv α q Λ m φs hφs l t x)) = bk t x)
    (v : ι) (φt : Vec 2 → h v) (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt) :
    IsPrimOn (c * a) (c * b)
      (fun t => ∫ x in AVenhance.unitCube, inner ℝ
        (pulseLift Cc N H ε (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs) ρs es c
          (ocChartInv α q Λ m φs hφs l) t x v) (φt x))
      (fun t => -(∫ x in AVenhance.unitCube, inner ℝ (∑ k, (bk t x k + streamVel φs t x k) •
          fderiv ℝ (fun x' => pulseLift Cc N H ε (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs)
            ρs es c (ocChartInv α q Λ m φs hφs l) t x' v) x (basisVec k)) (φt x)) -
        νs * (∫ x in AVenhance.unitCube, ∑ k, inner ℝ
          (fderiv ℝ (fun x' => pulseLift Cc N H ε (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs)
            ρs es c (ocChartInv α q Λ m φs hφs l) t x' v) x (basisVec k))
          (fderiv ℝ φt x (basisVec k))) +
        c⁻¹ * ∫ x in AVenhance.unitCube, inner ℝ
          (labelRest Q Cc N H ε (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs)
            (chartFieldDot cf dcf φ (ocChart α q Λ m φs hφs l) (streamVel φs) c ρs) ρs es c t
            (ocChartInv α q Λ m φs hφs l t x) v) (φt x)) := by
  classical
  have := isFiniteMeasure_restrict_unitCube
  have hab : a ≤ b := P.window
  have hcab : c * a ≤ c * b := mul_le_mul_of_nonneg_left hab hc.le
  have hmem : ∀ t ∈ Icc (c * a) (c * b), c⁻¹ * t ∈ Icc a b := fun t ht =>
    ⟨by rw [le_inv_mul_iff₀ hc]; exact ht.1, by rw [inv_mul_le_iff₀ hc]; exact ht.2⟩
  have hvel := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφs
  have hχj := Charts.contDiff_ocChart_joint hφs α q Λ m l
  refine (setting_pulse_tested P sX sZ hsX hsZ Cc hseq ε cf dcf φ hφ hφp α q Λ m hφs l hc hρ A₀ B₀
    hA hB hcf hG w hv h1 h2 h3 hc₁ M hM hGs hcs v φt hφt hφtp).congr hcab (fun t _ => rfl)
    (fun t ht => ?_)
  have hs := hmem t ht
  -- the chart and the labels at time `t`
  have hχs : ContDiff ℝ (⊤ : ℕ∞) (ocChart α q Λ m φs hφs l t) :=
    hχj.comp (contDiff_const.prodMk contDiff_id)
  have hψs : ContDiff ℝ (⊤ : ℕ∞) (ocChartInv α q Λ m φs hφs l t) :=
    (Charts.contDiff_ocChartInv_joint hφs α q Λ m l).comp (contDiff_const.prodMk contDiff_id)
  have hψd : Differentiable ℝ (ocChartInv α q Λ m φs hφs l t) := hψs.differentiable (by simp)
  -- the label lift at time `t`
  have hbox : ∀ hh ∈ Finset.range (H + 1), IsBoxSmooth 2 2 (liftPolyField Cc N ε hh
      (fun _ => chartField cf φ (ocChart α q Λ m φs hφs l) c ρs (c⁻¹ * t)) (c⁻¹ * t)) :=
    fun hh hhm => setting_liftPolyField_box P sX sZ Cc hseq hh
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) ε _
      (chartField_contDiff cf φ hφ _ hχj c ρs _) (c⁻¹ * t) hs (by omega)
  have hL2 : ContDiff ℝ 2 (fun y => labelLift Cc N H ε
      (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs) ρs es c t y v) := by
    have he : (fun y => labelLift Cc N H ε (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs)
        ρs es c t y v) = fun y => (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
          (∑ hh ∈ Finset.range (H + 1), twoScaleSample ρs es (liftPolyField Cc N ε hh
            (fun _ => chartField cf φ (ocChart α q Λ m φs hφs l) c ρs (c⁻¹ * t)) (c⁻¹ * t)) y) := by
      funext y
      simp only [labelLift, twoScaleSample, ContinuousLinearMap.proj_apply, Finset.sum_apply]
      rfl
    rw [he]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).contDiff.comp
      (ContDiff.sum fun hh hhm => CoarseFluxDiff.contDiff_sample (hbox hh hhm) le_rfl le_rfl ρs es)
  set U : Vec 2 → h v := fun x' => pulseLift Cc N H ε
    (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs) ρs es c (ocChartInv α q Λ m φs hφs l) t x' v
    with hUdef
  have hU2 : ContDiff ℝ 2 U := hL2.comp (hψs.of_le (by simp))
  have hUp : IsZ2Periodic U := fun n x => by
    simp only [hUdef, pulseLift, ocChartInv]
    rw [CycleReference.streamFlow_lattice_equivariant hφs _ t x n]
    exact setting_labelLift_periodic P sX sZ Cc hseq ε _
      (fun s => chartField_contDiff cf φ hφ _ hχj c ρs s) M hM
      (fun s X n' => chartField_periodic cf φ hφp _
        (fun t' y n'' => Charts.ocChart_latticeShift hφs α q Λ m l t' n'' y) hρ s X n')
      hGs hcs t hs v n _
  -- the label density in physical operators
  have hpt : ∀ x, labelDensity Q Cc N H ε (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs)
      (chartFieldDot cf dcf φ (ocChart α q Λ m φs hφs l) (streamVel φs) c ρs) w ρs es c νs t
      (ocChartInv α q Λ m φs hφs l t x) v =
      -(∑ k, bk t x k • fderiv ℝ U x (basisVec k)) +
        νs • ∑ k, fderiv ℝ (fun y => fderiv ℝ U y (basisVec k)) x (basisVec k) +
        c⁻¹ • labelRest Q Cc N H ε (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs)
          (chartFieldDot cf dcf φ (ocChart α q Λ m φs hφs l) (streamVel φs) c ρs) ρs es c t
          (ocChartInv α q Λ m φs hφs l t x) v := fun x =>
    labelDensity_physical Q Cc N H ε _ _ w ρs es c νs hc.ne' t hbox (fun i j => hG _ i j) hχs hψd
      (Charts.ocChartInv_ocChart α q Λ m φs hφs l t) (Charts.ocChart_ocChartInv α q Λ m φs hφs l t)
      (Charts.ocChart_det hφs α q Λ m l t) (hGχ t ht) (bk t) (hwb t ht) x v
  -- the tested label density is integrable
  obtain ⟨hLm, MLd, hMLd⟩ := setting_labelDensity_section P sX sZ hsX hsZ Cc hseq ε cf dcf φ hφ hφp
    (ocChart α q Λ m φs hφs l) (streamVel φs) hχj hvel.smooth
    (fun t' y n => Charts.ocChart_latticeShift hφs α q Λ m l t' n y)
    (fun t' n x => by simpa using hvel.periodic 0 n t' x) hc hρ A₀ B₀ hA hB hcf hG w hv h1 h2 h3
    hc₁ v t ht
  obtain ⟨Mφ, hMφ⟩ := exists_bound_periodic_field hφt.continuous hφtp
  have hm1 := hLm.comp hψs.continuous.measurable
  simp only [Function.comp_def] at hm1
  have hILd : Integrable (fun x => inner ℝ (labelDensity Q Cc N H ε
      (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs)
      (chartFieldDot cf dcf φ (ocChart α q Λ m φs hφs l) (streamVel φs) c ρs) w ρs es c νs t
      (ocChartInv α q Λ m φs hφs l t x) v) (φt x)) (volume.restrict AVenhance.unitCube) := by
    refine Integrable.mono' (integrable_const (MLd * Mφ))
      (hm1.inner hφt.continuous.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (hMLd _) (hMφ x) (norm_nonneg _) ((norm_nonneg _).trans (hMLd 0))
  -- the chart velocity is smooth, periodic and divergence-free
  have hsv : ContDiff ℝ 1 (streamVel φs t) :=
    (hvel.smooth.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hsvp : IsZ2Periodic (streamVel φs t) := fun n x => by simpa using hvel.periodic 0 n t x
  have hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (fun y => streamVel φs t y k) x (basisVec k) = 0 :=
    fun x => AVenhance.Infra.Classical.streamVel_vecDiv_eq_zero φs hφs t x
  have hdrift : ∀ x, fderiv ℝ φt x (streamVel φs t x) =
      ∑ k : Fin 2, streamVel φs t x k • fderiv ℝ φt x (basisVec k) := fun x => by
    conv_lhs => rw [vec_eq_sum_smul_basisVec (streamVel φs t x)]
    simp only [map_sum, map_smul]
  simp only [hdrift]
  exact cell_weak_combine hU2 hUp hφt hφtp hsv hsvp hdiv (hbk t ht) hc.ne' _ _ hpt hILd

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The tested edge term of one pulse**. The label edge flux
of a piece applied to a periodic field is `C¹` (it is a sample of a box-smooth source flux,
`setting_labelEdgeFlux_labelLift_contDiff`) and `ℤ²`-periodic in the label for a torus-compatible
family with `e⁻¹ ∈ ℕ` (`labelEdgeFlux_periodic`). Hence the source part of a pulse rest, read at
the labels of an area-preserving lattice-equivariant chart and tested against a `C¹` periodic
`φ`, is minus the pairing of the physical edge flux of the pulse lift with `∇φ`
(`setting_pulse_edge_tested`), once the physical flux is the Piola transport of the label flux. -/

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ} {Pc : Type*} {Ctx : Pc → Type*}

/-- The two-scale sample of a source flux with `(1, 1)` box smooth coefficients applied to a
`(D, D)` box smooth field is `C¹`. -/
theorem sample_sourceFlux_contDiff (edge : ConstituentEdges D h) (η ε s ρ e : ℝ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth 1 1 (fun X z => γ.coeff α s X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : IsBoxSmooth D D Φ) (k : Fin 2) :
    ContDiff ℝ 1 (twoScaleSample ρ e (sourceFlux edge η ε s Φ k)) :=
  CoarseFluxDiff.contDiff_sample (isBoxSmooth_sourceFlux edge η ε s Φ k hΓ hΦ (by omega))
    le_rfl le_rfl ρ e

/-- **The label edge flux of a sampled field is `C¹`.** -/
theorem labelEdgeFlux_sample_contDiff (F : ChartedFamily ι h D Pc Ctx) (ν e E : ℝ)
    (p : Pc) (c : Ctx p) {η ε ρ cℓ lam : ℝ} (he : e ≠ 0) (hν : ν ≠ 0)
    (hscale : Real.sqrt η * ε = e * ρ⁻¹) (hlam : lam * ρ⁻¹ = E⁻¹) {s τ : ℝ} (hτ : cℓ * s = τ)
    (hΓ : ∀ v u d, ∀ γ ∈ liftEdges cℓ lam (F.fiber p c) v u d, ∀ α,
      IsBoxSmooth 1 1 (fun X z => γ.coeff α s X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : IsBoxSmooth D D Φ) (v : ι) (k : Fin 2) :
    ContDiff ℝ 1 (fun y' => labelEdgeFlux F ν e E p c τ (twoScaleSample ρ e Φ) v y' k) := by
  subst hτ
  have h1 := contDiff_pi.1
    (sample_sourceFlux_contDiff (liftEdges cℓ lam (F.fiber p c)) η ε s ρ e hΓ hΦ k) v
  rw [← scaledLabelEdgeFlux_eq_sample F ν e E p c cℓ he hν hscale hlam s hΦ k] at h1
  have h2 : ContDiff ℝ 1 (fun y' => (e / ν)⁻¹ •
      ((e / ν) • labelEdgeFlux F ν e E p c (cℓ * s) (twoScaleSample ρ e Φ) v y' k)) :=
    h1.const_smul (e / ν)⁻¹
  have hinv : (e / ν)⁻¹ * (e / ν) = 1 := inv_mul_cancel₀ (div_ne_zero he hν)
  simp only [smul_smul, hinv, one_smul] at h2
  exact h2

/-- **The label edge flux of a periodic field is periodic** in the label, for a torus-compatible
family and an integer fast frequency `e⁻¹`. -/
theorem labelEdgeFlux_periodic (F : ChartedFamily ι h D Pc Ctx) (ν e E : ℝ)
    (actual : ∀ p, Ctx p) (htorus : IsTorusCompatible F actual E) (p : Pc) (t : ℝ)
    {V : Vec 2 → ∀ i, h i}
    (hV : ∀ u (m : ℕ), m ≤ D → ∀ (I : DerivativeWord2 m) (y : Vec 2) (n : Fin 2 → ℤ),
      orderedDerivative I (fun y' => V y' u) (y + latticeShift n) =
        orderedDerivative I (fun y' => V y' u) y)
    (M : ℕ) (hM : e⁻¹ = M) (v : ι) (i₀ : Fin 2) :
    IsZ2Periodic (fun y => labelEdgeFlux F ν e E p (actual p) t V v y i₀) := by
  intro n y
  have hfast : e⁻¹ • (y + latticeShift n) =
      e⁻¹ • y + latticeShift (fun i => (M : ℤ) * n i) := by
    rw [smul_add, hM, natCast_smul_latticeShift]
  have hflux : ∀ u (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)),
      F.dimFlux ν e E p (actual p) v u γ d I t (y + latticeShift n)
        (e⁻¹ • (y + latticeShift n)) = F.dimFlux ν e E p (actual p) v u γ d I t y (e⁻¹ • y) :=
    fun u γ d I => by
      simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux, hfast]
      rw [F.flux_periodic p (actual p) v u γ d I t _ _ (e⁻¹ • y)]
      exact congrArg (fun z => (ν * e ^ (d - 2)) • z) (htorus.2 p t v u γ d I (e⁻¹ • y) n y)
  simp only [labelEdgeFlux]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun γ _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun I _ => ?_
  have hdD : d - 1 ≤ D := by
    have h1 := (F.identity v u γ).le_D
    have h2 := (Finset.mem_Icc.1 hd).2
    omega
  rw [hflux u γ d I, hV u (d - 1) hdD I y n]

end Family

section Setting

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K₀ k₀ L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {t₀ t₁ e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : Fin 2} {Vsh : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bE : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π t₀ t₁ e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ par Vsh H N K₀ k₀ L qs qf CG
    Cw Cj bE Θ)
  {Pc : Type*} {Ctx : Pc → Type*}

include P in
/-- The label edge flux of a piece applied to the label lift is `C¹` in the label. -/
theorem setting_labelEdgeFlux_labelLift_contDiff (F : ChartedFamily ι h D Pc Ctx)
    (ν e E : ℝ) (p₀ : Pc) (c₀ : Ctx p₀) {c lam : ℝ}
    (hQe : Q.edge = liftEdges c lam (F.fiber p₀ c₀)) (hc : c ≠ 0) (he : e ≠ 0) (hν : ν ≠ 0)
    {ε ρs : ℝ} (hscale : Real.sqrt Q.η * ε = e * ρs⁻¹) (hlam : lam * ρs⁻¹ = E⁻¹) {sX sZ : ℕ}
    (hsZ : 1 ≤ sZ) {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    (f : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) (f (c⁻¹ * t)))
    (ht : c⁻¹ * t ∈ Set.Icc t₀ t₁) (v : ι) (i₀ : Fin 2) :
    ContDiff ℝ 1
      (fun y => labelEdgeFlux F ν e E p₀ c₀ t (labelLift Cc N H ε f ρs e c t) v y i₀) := by
  have hfun : (fun y => labelEdgeFlux F ν e E p₀ c₀ t (labelLift Cc N H ε f ρs e c t) v y i₀) =
      fun y => ∑ hh ∈ Finset.range (H + 1), labelEdgeFlux F ν e E p₀ c₀ t
        (twoScaleSample ρs e (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t))) v y
          i₀ :=
    funext fun y => setting_labelEdgeFlux_labelLift_eq_sum P F ν e E p₀ c₀ hsZ hseq ε f ρs e hf
      ht t v y i₀
  refine (congrArg (fun g : Vec 2 → h v => ContDiff ℝ 1 g) hfun).mpr ?_
  exact ContDiff.sum fun hh hhm => labelEdgeFlux_sample_contDiff F ν e E p₀ c₀ he hν hscale hlam
    (mul_inv_cancel_left₀ hc t) (setting_liftedEdge_coeff_box P F p₀ c₀ hQe ht)
    (setting_liftPolyField_boxD P hsZ hseq (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) ε _ hf
      ht) v i₀

include P in
/-- **The tested edge term of one pulse.** If the physical edge flux of the pulse lift
`U = V ∘ ψ` is the Piola transport of the label edge flux of the piece `p₀` (one active piece, or
a quiet overlap), the source part of the rest at the labels `ψ x`, scaled by `c⁻¹` and tested
against a `C¹` periodic `φ`, is minus the pairing of the physical edge flux with `∇φ`. -/
theorem setting_pulse_edge_tested (F : ChartedFamily ι h D Pc Ctx) (ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (p₀ : Pc) {c lam : ℝ}
    (hQe : Q.edge = liftEdges c lam (F.fiber p₀ (actual p₀))) (hc : c ≠ 0) (he : e ≠ 0)
    (hν : ν ≠ 0) {ε ρs : ℝ} (hscale : Real.sqrt Q.η * ε = e * ρs⁻¹) (hlam : lam * ρs⁻¹ = E⁻¹)
    (hsc : c⁻¹ * (e * (e / ν)) = 1) {sX sZ : ℕ} (hsZ : 1 ≤ sZ) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (f : ℝ → Vec 2 → ∀ i, h i) {t : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) (f (c⁻¹ * t))) (ht : c⁻¹ * t ∈ Set.Icc t₀ t₁)
    (htorus : IsTorusCompatible F actual E) (M : ℕ) (hM : e⁻¹ = M)
    (hVp : IsZ2Periodic (labelLift Cc N H ε f ρs e c t))
    {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (hd : ∀ y, (jacMatrix χ y).det = 1)
    (hψl : ∀ x (n : Fin 2 → ℤ), ψ (x + latticeShift n) = ψ x + latticeShift n) (v : ι)
    (hflux : ∀ x' (a₀ : Fin 2), physEdgeFluxVec F ν e E actual K t
        (fun y => labelLift Cc N H ε f ρs e c t (ψ y)) v x' a₀ =
      ∑ i₀ : Fin 2, chartInvJacobian ψ x' a₀ i₀ •
        labelEdgeFlux F ν e E p₀ (actual p₀) t (labelLift Cc N H ε f ρs e c t) v (ψ x') i₀)
    {φt : Vec 2 → h v} (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt) :
    ∫ x in unitCube, inner ℝ (c⁻¹ • labelSourcePart Q Cc N H ε f ρs e c t (ψ x) v) (φt x) =
      -∫ x in unitCube, ∑ a₀ : Fin 2, inner ℝ (physEdgeFluxVec F ν e E actual K t
        (fun y => labelLift Cc N H ε f ρs e c t (ψ y)) v x a₀) (fderiv ℝ φt x (basisVec a₀)) := by
  have hpt : ∀ x, c⁻¹ • labelSourcePart Q Cc N H ε f ρs e c t (ψ x) v =
      ∑ i₀ : Fin 2, fderiv ℝ (fun y' => labelEdgeFlux F ν e E p₀ (actual p₀) t
        (labelLift Cc N H ε f ρs e c t) v y' i₀) (ψ x) (basisVec i₀) := fun x =>
    source_part_label_div P F ν e E p₀ (actual p₀) hQe hc he hν hscale hlam hsc hsZ hseq f hf ht
      (ψ x) v
  have hVD : ContDiff ℝ (D : ℕ∞) (labelLift Cc N H ε f ρs e c t) :=
    setting_labelLift_contDiff P hsZ hseq ε f ρs e hf ht
  have hVd : ∀ u (m : ℕ), m ≤ D → ∀ (I : DerivativeWord2 m) (y : Vec 2) (n : Fin 2 → ℤ),
      orderedDerivative I (fun y' => labelLift Cc N H ε f ρs e c t y' u) (y + latticeShift n) =
        orderedDerivative I (fun y' => labelLift Cc N H ε f ρs e c t y' u) y :=
    fun u m hm I y n => orderedDerivative_periodic
      (((ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp hVD).of_le
        (by exact_mod_cast hm)) (latticeShift n)
      (fun Y => congrFun (hVp n Y) u) I y
  simp only [hpt, hflux]
  exact tested_label_div hχ hψ hψχ hχψ hd hψl
    (G := fun y i₀ => labelEdgeFlux F ν e E p₀ (actual p₀) t (labelLift Cc N H ε f ρs e c t) v y
      i₀)
    (fun l => setting_labelEdgeFlux_labelLift_contDiff P F ν e E p₀ (actual p₀) hQe hc he hν
      hscale hlam hsZ hseq f hf ht v l)
    (fun l => labelEdgeFlux_periodic F ν e E actual htorus p₀ t hVd M hM v l) hφt hφtp

end Setting

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.LiftMeanEntrywise
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Slow invariance of the tail of a pulse lift**.

Let `T` be a slow translation leaving the metric `Q.G` and the source coefficients invariant
(for the pulse lift: `T = ρ⁻¹ n`, `n ∈ ℤ²`). On the window:

* `liftTailCoeff_congr_time`, `liftTailCoeff_slowShift`, `setting_liftTailCoeff_slowShift_eq`:
  the tail coefficient `R_n^{(hh)}` at a time depends on the lift coefficients only at that time,
  and it commutes with `T` (the lift coefficients are `T`-invariant,
  `setting_liftSequence_slowShift_invariant`);
* `setting_tailLeftCoefficient_slowShift`: the symmetric coefficient array of the tail is
  `T`-invariant (its action on smooth tests commutes with `T`, and a symmetric array is determined
  by its action, `symmetric_lift_coefficient_eq_of_operator_eq`);
* `setting_tailFluxCoefficient_slowShift`: so is the explicit flux array
  `tailFluxCoefficient` of the tail presentation (`setting_tail_presentation`), which is the
  centered transverse primitive of the positive part of that array;
* `setting_tailFluxField_slowShift`: the divided tail flux of a `T`-invariant coarse field is
  `T`-invariant (`tailFluxField_slow_invariant`, `liftApply_slow_invariant`); the divided scalar
  tail vanishes identically in the presentation;
* `setting_tail_cleanupChain_slowShift`: every cleanup chain of the divided tail is `T`-invariant
  (`isCleanupChain_slow_invariant`). -/

section Lift

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The tail coefficient at a time depends on the lift coefficients only at that time and at the
grades `≤ hh`. -/
theorem liftTailCoeff_congr_time (Q : LiftOperatorData ι h D)
    {Cc₁ Cc₂ : ℕ → ℕ → LiftCoeff ι h} (N : ℕ) (a : ℝ → Vec 2 → ∀ i, h i) {hh : ℕ} (n : ℕ)
    {t : ℝ} (hc : ∀ p ≤ hh, ∀ q m α X z, Cc₁ p q m α t X z = Cc₂ p q m α t X z) :
    liftTailCoeff Q Cc₁ N a hh n t = liftTailCoeff Q Cc₂ N a hh n t := by
  funext X z
  simp only [liftTailCoeff, liftA_congr_time Q a n hc]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hg : r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D
  · rw [ite_eq_left hg, ite_eq_left hg]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpp := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    rw [liftApply_congr_time (b := liftMean Q Cc₂ a p.2 (n - r))
      (hc p.1 (by omega) r) (liftMean_congr_time Q a (n - r) fun p' hp' => hc p' (by omega))]
  · rw [ite_eq_right hg, ite_eq_right hg]

/-- **The tail coefficient commutes with a slow translation** leaving the metric and the source
coefficients invariant, the lift sequence being read at the translated position. -/
theorem liftTailCoeff_slowShift (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (N : ℕ) (f g : ℝ → Vec 2 → ∀ i, h i) (T : Vec 2) (hfg : ∀ s Y, g s Y = f s (Y + T))
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (hh n : ℕ) (t : ℝ) (X z : Vec 2) :
    liftTailCoeff Q (slowShiftSequence T Cc) N g hh n t X z =
      liftTailCoeff Q Cc N f hh n t (X + T) z := by
  have hT (r : ℕ) (p : ℕ × ℕ) : liftApply r (slowShiftSequence T Cc p.1 r)
      (liftMean Q (slowShiftSequence T Cc) g p.2 (n - r)) t X z =
      liftApply r (Cc p.1 r) (liftMean Q Cc f p.2 (n - r)) t (X + T) z :=
    liftApply_slowShift r (Cc p.1 r) _ _ T t
      (fun Y => liftMean_slowShift Q Cc f g T hfg hG hc p.2 (n - r) t Y) X z
  simp only [liftTailCoeff, liftA_slowShift Q Cc f g T hfg hG hc, hT]

/-- A lift action at a time is invariant under a slow translation leaving the coefficients and
the coarse field at that time invariant. -/
theorem liftApply_slow_invariant (n : ℕ) (c : LiftCoeff ι h) (A : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (s : Vec 2) (hc : ∀ m (α : DerivativeWord2 m) X z v u, c m α t (X + s) z v u = c m α t X z v u)
    (hA : ∀ X, A t (X + s) = A t X) (X z : Vec 2) :
    liftApply n c A t (X + s) z = liftApply n c A t X z := by
  rw [← liftApply_slowShift n c A A s t (fun Y => (hA Y).symm) X z]
  exact congrFun (congrFun (liftApply_congr_time (n := n) (c₁ := slowShiftCoeff s c) (c₂ := c)
    (a := A) (b := A) (t := t) (fun m α X' z' => by
      funext v u
      exact hc m α X' z' v u) rfl) X) z

end Lift

section Fields

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The divided scalar tail of a slow-invariant coarse field with slow-invariant arrays is
slow invariant. -/
theorem tailScalarField_slow_invariant (f : ℕ → LiftCoeff ι h) (N D : ℕ) (ε : ℝ)
    (A : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ) (s : Vec 2)
    (hf : ∀ n, N + 1 ≤ n → n ≤ 2 * N + D → ∀ m (α : DerivativeWord2 m) X z v u,
      f n m α τ (X + s) z v u = f n m α τ X z v u)
    (hA : ∀ X, A τ (X + s) = A τ X) (X : Vec 2) :
    tailScalarField f N D ε A τ (X + s) = tailScalarField f N D ε A τ X := by
  funext z
  show ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ (n - N - 1) •
      liftApply (2 * N + D) (f n) A τ (X + s) z =
    ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ (n - N - 1) • liftApply (2 * N + D) (f n) A τ X z
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
  rw [liftApply_slow_invariant (2 * N + D) (f n) A τ s (hf n hn1 hn2) hA X z]

/-- The divided tail flux of a slow-invariant coarse field with slow-invariant arrays is slow
invariant. -/
theorem tailFluxField_slow_invariant (F : ℕ → Fin 2 → LiftCoeff ι h) (N D : ℕ) (ε : ℝ)
    (A : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ) (s : Vec 2)
    (hF : ∀ n, N + 1 ≤ n → n ≤ 2 * N + D → ∀ kk m (α : DerivativeWord2 m) X z v u,
      F n kk m α τ (X + s) z v u = F n kk m α τ X z v u)
    (hA : ∀ X, A τ (X + s) = A τ X) (X : Vec 2) :
    tailFluxField F N D ε A τ (X + s) = tailFluxField F N D ε A τ X := by
  funext z kk
  show ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ (n - N - 1) •
      liftApply (2 * N + D) (F n kk) A τ (X + s) z =
    ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ (n - N - 1) •
      liftApply (2 * N + D) (F n kk) A τ X z
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
  rw [liftApply_slow_invariant (2 * N + D) (F n kk) A τ s (hF n hn1 hn2 kk) hA X z]

end Fields

section Setting

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- **The tail coefficient of a translated coarse field is the translated tail coefficient** on
the window. -/
theorem setting_liftTailCoeff_slowShift_eq (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (T : Vec 2)
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (f g : ℝ → Vec 2 → ∀ i, h i) (hfg : ∀ s Y, g s Y = f s (Y + T))
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftTailCoeff Q Cc N g hh n t X z = liftTailCoeff Q Cc N f hh n t (X + T) z := by
  rw [← liftTailCoeff_slowShift Q Cc N f g T hfg hG hc hh n t X z,
    liftTailCoeff_congr_time Q N g n (Cc₂ := slowShiftSequence T Cc) fun p hp q m α X' z' => ?_]
  funext v u
  exact (setting_liftSequence_slowShift_invariant P sX sZ Cc hseq T hG hc p (hp.trans hhh) q m α
    t ht X' z' v u).symm

include P in
/-- **The coefficient array of the tail is slow invariant** on the window, for every slow
translation leaving the metric and the source coefficients invariant. -/
theorem setting_tailLeftCoefficient_slowShift (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (T : Vec 2)
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (m : ℕ) (α : DerivativeWord2 m) (X z : Vec 2) (v u : ι) :
    tailLeftCoefficient Q Cc N hh n m α t (X + T) z v u =
      tailLeftCoefficient Q Cc N hh n m α t X z v u := by
  by_cases hm : m ≤ 2 * N + D
  · have hperm : ∀ (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
        slowShiftCoeff T (tailLeftCoefficient Q Cc N hh n) m (β ∘ σ) =
          slowShiftCoeff T (tailLeftCoefficient Q Cc N hh n) m β := by
      intro β σ
      show (fun s Y y => tailLeftCoefficient Q Cc N hh n m (β ∘ σ) s (Y + T) y) =
        fun s Y y => tailLeftCoefficient Q Cc N hh n m β s (Y + T) y
      rw [tailLeftCoefficient_perm Q Cc N hh n m β σ]
    refine symmetric_lift_coefficient_eq_of_operator_eq (2 * N + D) m hm
      (slowShiftCoeff T (tailLeftCoefficient Q Cc N hh n)) (tailLeftCoefficient Q Cc N hh n)
      hperm (tailLeftCoefficient_perm Q Cc N hh n m) t X z v u (fun a₀ ha₀ => ?_) α
    have ha₁ : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => a₀ (Y - T)) :=
      ha₀.comp (contDiff_id.sub contDiff_const)
    have hshift : ∀ s Y, (fun (_ : ℝ) => a₀) s Y =
        (fun (_ : ℝ) (Y' : Vec 2) => a₀ (Y' - T)) s (Y + T) := by
      intro s Y
      simp only [add_sub_cancel_right]
    rw [liftApply_slowShift (2 * N + D) (tailLeftCoefficient Q Cc N hh n)
        (fun _ Y => a₀ (Y - T)) (fun _ => a₀) T t (hshift t) X z,
      setting_tailLeftCoefficient_apply P sX sZ hsX hsZ Cc hseq hh hhh n hn hnR
        (fun Y => a₀ (Y - T)) ha₁ t ht (X + T) z,
      setting_tailLeftCoefficient_apply P sX sZ hsX hsZ Cc hseq hh hhh n hn hnR a₀ ha₀ t ht X z,
      setting_liftTailCoeff_slowShift_eq P sX sZ Cc hseq T hG hc (fun _ Y => a₀ (Y - T))
        (fun _ => a₀) hshift hh hhh n t ht X z]
  · rw [tailLeftCoefficient_above_order Q Cc N hh n hn m (by omega) α t (X + T) z v u,
      tailLeftCoefficient_above_order Q Cc N hh n hn m (by omega) α t X z v u]

include P in
/-- **The explicit tail flux array is slow invariant** on the window (T1): the flux array
`tailFluxCoefficient` of the tail presentation is the centered transverse primitive, in the fast
variable, of the positive part of the slow-invariant coefficient array of the tail. -/
theorem setting_tailFluxCoefficient_slowShift (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (T : Vec 2)
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (kk : Fin 2) (m : ℕ) (α : DerivativeWord2 m) (X z : Vec 2)
    (v u : ι) :
    tailFluxCoefficient par Q Cc N hh n kk m α t (X + T) z v u =
      tailFluxCoefficient par Q Cc N hh n kk m α t X z v u := by
  have hL : ∀ z', tailLeftCoefficient Q Cc N hh n m α t (X + T) z' v u =
      tailLeftCoefficient Q Cc N hh n m α t X z' v u := fun z' =>
    setting_tailLeftCoefficient_slowShift P sX sZ hsX hsZ Cc hseq T hG hc hh hhh n hn hnR t ht m
      α X z' v u
  simp only [tailFluxCoefficient, positiveFluxLiftCoefficient, centeredFluxLiftCoefficient,
    positiveLiftCoefficient, hL]

include P in
/-- **The divided tail flux of a slow-invariant coarse field is slow invariant** at a window
time. -/
theorem setting_tailFluxField_slowShift (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (T : Vec 2)
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (hh : ℕ) (hhh : hh ≤ H) (ε : ℝ) (A : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ)
    (hτ : τ ∈ Set.Icc a b) (hA : ∀ X, A τ (X + T) = A τ X) (X : Vec 2) :
    tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ (X + T) =
      tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ X :=
  tailFluxField_slow_invariant (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ T
    (fun n hn1 hn2 kk m α X' z v u => setting_tailFluxCoefficient_slowShift P sX sZ hsX hsZ Cc
      hseq T hG hc hh hhh n (by omega) hn2 τ hτ kk m α X' z v u) hA X

include P in
/-- **The cleanup chains of the divided tail of a slow-invariant coarse field are slow
invariant** at a window time (the scalar part of the presentation is `0`). -/
theorem setting_tail_cleanupChain_slowShift (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (T : Vec 2)
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (hh : ℕ) (hhh : hh ≤ H) {sXc sZc Acl : ℕ} (hZc : 1 ≤ sZc) (ε : ℝ)
    (A : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ) (hτ : τ ∈ Set.Icc a b) (hA : ∀ X, A τ (X + T) = A τ X)
    {W : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hW : IsCleanupChain sXc sZc Acl (tailScalarField (fun _ => 0) N D ε A τ)
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ) W) :
    ∀ j, j < Acl → ∀ X, W j (X + T) = W j X :=
  isCleanupChain_slow_invariant hZc T
    (tailScalarField_slow_invariant (fun _ => (0 : LiftCoeff ι h)) N D ε A τ T
      (fun _ _ _ _ _ _ _ _ _ => rfl) hA)
    (setting_tailFluxField_slowShift P sX sZ hsX hsZ Cc hseq T hG hc hh hhh ε A τ hτ hA) hW

end Setting

end AVRegularity.CycleComparison.Reconstruction
end
