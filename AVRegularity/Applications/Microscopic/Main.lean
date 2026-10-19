-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Microscopic.DilationTests
import AVRegularity.Applications.Caloric.Interior
import AVRegularity.Applications.HeatReplacement.Main
import AVRegularity.Applications.Microscopic.RescaleHyp
import Homogenization.Ambient.BlockMatrix
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import AVRegularity.Applications.LocalEnergy.Caccioppoli

section
@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # The forcing of the heat replacement

`F = K∇U - (U - c) d` is square integrable on `Q_{3/4}` with
`∫_{Q_{3/4}} |F|² ≤ 2η² (∫_{Q_{3/4}} |∇U|² + ∫_{Q₁} (U - c)²)`. -/

section
theorem openCyl_three_quarters_subset : openCyl 0 (3 / 4) ⊆ openCyl 0 1 := by
  rintro ⟨τ, y⟩ ⟨⟨h1, h2⟩, h3⟩
  refine ⟨⟨?_, h2⟩, ?_⟩
  · simp only [Prod.fst_zero] at h1 ⊢; nlinarith
  · simp only [euclidBall, Set.mem_ofPred_eq, Prod.snd_zero] at h3 ⊢; nlinarith

theorem integrable_vecNormSq_of_memLp {μ : Measure (ℝ × Vec 2)} {G : ℝ × Vec 2 → Vec 2}
    (hG : ∀ i : Fin 2, MemLp (fun p => G p i) 2 μ) : Integrable (fun p => vecNormSq (G p)) μ := by
  have h : (fun p => vecNormSq (G p)) = fun p => ∑ i : Fin 2, (G p i) ^ 2 := by
    funext p; simp [vecNormSq, vecDot, pow_two]
  rw [h]
  exact integrable_finsetSum _ fun i _ => (hG i).integrable_sq

/-- The forcing `F = K∇U - (U-c)d`. -/
def skewForcing (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
    (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) (c : ℝ) : ℝ × Vec 2 → Vec 2 :=
  fun p => (K p).mulVec (DU p) - (U p - c) • d p

theorem skewForcing_pointwise {K : Matrix (Fin 2) (Fin 2) ℝ} {e dv : Vec 2} {u η kK kd : ℝ}
    (hkK : 0 ≤ kK) (hkd : 0 ≤ kd) (hη : kK + kd ≤ η)
    (hK : ∀ v : Vec 2, vecNormSq (K.mulVec v) ≤ kK ^ 2 * vecNormSq v)
    (hd : vecNormSq dv ≤ kd ^ 2) :
    vecNormSq (K.mulVec e - u • dv) ≤ 2 * η ^ 2 * (vecNormSq e + u ^ 2) := by
  have h1 := vecNormSq_sub_le (K.mulVec e) (u • dv)
  have h2 := hK e
  have h3 : vecNormSq (u • dv) ≤ u ^ 2 * kd ^ 2 := by
    rw [vecNormSq_smul]; exact mul_le_mul_of_nonneg_left hd (sq_nonneg u)
  have hkK2 : kK ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hkK (by linarith) 2
  have hkd2 : kd ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hkd (by linarith) 2
  have he := vecNormSq_nonneg e
  nlinarith [mul_le_mul_of_nonneg_right hkK2 he, mul_le_mul_of_nonneg_left hkd2 (sq_nonneg u)]

variable {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {d : ℝ × Vec 2 → Vec 2}
  {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2} {kK kd η : ℝ}

theorem skewForcing_memLp (hcoef : IsSkewDriftCoeff K d kK kd) (hkK : 0 ≤ kK) (hkd : 0 ≤ kd)
    (hη : kK + kd ≤ η) (hU : IsEnergyClassQ1 U DU) (c : ℝ) (i : Fin 2) :
    MemLp (fun p => skewForcing K d U DU c p i) 2 (volume.restrict (openCyl 0 1)) := by
  obtain ⟨hKm, hdm, hb⟩ := hcoef
  obtain ⟨hU2, hDU2, -, -⟩ := hU
  have hmeas : AEStronglyMeasurable (fun p => skewForcing K d U DU c p i)
      (volume.restrict (openCyl 0 1)) := by
    have hKDU : AEStronglyMeasurable (fun p => ((K p).mulVec (DU p)) i)
        (volume.restrict (openCyl 0 1)) := by
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      exact ((hKm i 0).mul (hDU2 0).aestronglyMeasurable).add
        ((hKm i 1).mul (hDU2 1).aestronglyMeasurable)
    have hVd : AEStronglyMeasurable (fun p => ((U p - c) • d p) i)
        (volume.restrict (openCyl 0 1)) := by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (hU2.aestronglyMeasurable.sub aestronglyMeasurable_const).mul (hdm i)
    exact hKDU.sub hVd
  rw [memLp_two_iff_integrable_sq hmeas]
  have hdom : Integrable (fun p => 2 * η ^ 2 * (vecNormSq (DU p) + (U p - c) ^ 2))
      (volume.restrict (openCyl 0 1)) := by
    have hV : MemLp (fun p => U p - c) 2 (volume.restrict (openCyl 0 1)) := by
      have hfin : IsFiniteMeasure (volume.restrict (openCyl 0 1)) := by
        refine isFiniteMeasure_restrict.mpr ?_
        rw [← Measure.restrict_apply_univ, restrict_openCyl_eq, Measure.restrict_apply_univ]
        exact cylinder_volume_ne_top 0 one_pos
      exact hU2.sub (memLp_const c)
    exact ((integrable_vecNormSq_of_memLp hDU2).add hV.integrable_sq).const_mul _
  refine hdom.mono' (hmeas.pow 2) ?_
  filter_upwards [hb] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_apply_le_vecNormSq _ i).trans
    (skewForcing_pointwise hkK hkd hη hp.1 hp.2)

theorem skewForcing_bound (hcoef : IsSkewDriftCoeff K d kK kd) (hkK : 0 ≤ kK) (hkd : 0 ≤ kd)
    (hη : kK + kd ≤ η) (hU : IsEnergyClassQ1 U DU) (c : ℝ) :
    ∫ p in openCyl 0 (3 / 4), vecNormSq (skewForcing K d U DU c p) ≤
      2 * η ^ 2 * ((∫ p in openCyl 0 (3 / 4), vecNormSq (DU p)) +
        ∫ p in openCyl 0 1, (U p - c) ^ 2) := by
  obtain ⟨hKm, hdm, hb⟩ := hcoef
  have hU2 := hU.1
  have hDU2 := hU.2.1
  have hsub := openCyl_three_quarters_subset
  have hfin : IsFiniteMeasure (volume.restrict (openCyl 0 1)) := by
    refine isFiniteMeasure_restrict.mpr ?_
    rw [← Measure.restrict_apply_univ, restrict_openCyl_eq, Measure.restrict_apply_univ]
    exact cylinder_volume_ne_top 0 one_pos
  have hV : MemLp (fun p => U p - c) 2 (volume.restrict (openCyl 0 1)) := hU2.sub (memLp_const c)
  have hVi : Integrable (fun p => (U p - c) ^ 2) (volume.restrict (openCyl 0 1)) :=
    hV.integrable_sq
  have hDi : Integrable (fun p => vecNormSq (DU p)) (volume.restrict (openCyl 0 1)) :=
    integrable_vecNormSq_of_memLp hDU2
  have hFi : Integrable (fun p => vecNormSq (skewForcing K d U DU c p))
      (volume.restrict (openCyl 0 1)) :=
    integrable_vecNormSq_of_memLp
      (skewForcing_memLp ⟨hKm, hdm, hb⟩ hkK hkd hη hU c)
  have hpt : ∫ p in openCyl 0 (3 / 4), vecNormSq (skewForcing K d U DU c p) ≤
      ∫ p in openCyl 0 (3 / 4), 2 * η ^ 2 * (vecNormSq (DU p) + (U p - c) ^ 2) := by
    refine integral_mono_ae (hFi.mono_measure (Measure.restrict_mono hsub le_rfl))
      ((hDi.add hVi).const_mul _ |>.mono_measure (Measure.restrict_mono hsub le_rfl)) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hb] with p hp
    exact skewForcing_pointwise hkK hkd hη hp.1 hp.2
  refine hpt.trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [integral_add (hDi.mono_measure (Measure.restrict_mono hsub le_rfl))
    (hVi.mono_measure (Measure.restrict_mono hsub le_rfl))]
  refine add_le_add le_rfl ?_
  exact setIntegral_mono_set hVi (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall hsub)
end

/-! # The caloric part `H - c = U - Z - c`

If `U` solves the small skew/drift problem in flux form and `Z` solves the heat equation with
the forcing `div F`, `F = K∇U - (U-c)d`, on `Q_{3/4}`, then `U - Z - c` is weakly caloric. -/

theorem openCyl_three_quarters_prod :
    openCyl 0 (3 / 4) = Set.Ioo (-(9 / 16) : ℝ) 0 ×ˢ euclidBall 0 (3 / 4) := by
  simp only [openCyl, Prod.fst_zero, Prod.snd_zero]
  norm_num

theorem integrable_mul_cont {S : Set (ℝ × Vec 2)} {f g : ℝ × Vec 2 → ℝ}
    (hf : IntegrableOn f S) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun p => f p * g p) (volume.restrict S) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  exact hf.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)

theorem integrable_vecDot_grad {S : Set (ℝ × Vec 2)} {G : ℝ × Vec 2 → Vec 2}
    {φ : ℝ × Vec 2 → ℝ} (hG : ∀ i : Fin 2, IntegrableOn (fun p => G p i) S)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    Integrable (fun p => vecDot (G p) (stSpaceGrad φ p)) (volume.restrict S) := by
  have h : (fun p => vecDot (G p) (stSpaceGrad φ p)) =
      fun p => G p 0 * fderiv ℝ φ p (0, basisVec 0) + G p 1 * fderiv ℝ φ p (0, basisVec 1) := by
    funext p; simp [vecDot, stSpaceGrad, Fin.sum_univ_two]
  rw [h]
  exact (integrable_mul_cont (hG 0) (contDiff_fderiv_apply_of_smooth hφ _).continuous
      (hasCompactSupport_fderiv_apply hcs _)).add
    (integrable_mul_cont (hG 1) (contDiff_fderiv_apply_of_smooth hφ _).continuous
      (hasCompactSupport_fderiv_apply hcs _))

theorem integrableOn_of_memLp_two {S : Set (ℝ × Vec 2)} (hS : volume S ≠ ⊤)
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 (volume.restrict S)) : IntegrableOn f S := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS
  exact hf.integrable one_le_two

theorem openCyl_volume_ne_top (z : ℝ × Vec 2) {r : ℝ} (hr : 0 < r) : volume (openCyl z r) ≠ ⊤ :=
  ne_top_of_le_ne_top (cylinder_volume_ne_top z hr) (measure_mono (openCyl_subset_cylinder z r))

theorem continuous_stSpaceLap {φ : ℝ × Vec 2 → ℝ} (hsm : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Continuous (stSpaceLap φ) := by
  have h : stSpaceLap φ = fun p =>
      fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec 0)) p (0, basisVec 0) +
        fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec 1)) p (0, basisVec 1) := by
    funext p; simp [stSpaceLap, Fin.sum_univ_two]
  rw [h]
  exact (contDiff_fderiv_apply_of_smooth (contDiff_fderiv_apply_of_smooth hsm _) _).continuous.add
    (contDiff_fderiv_apply_of_smooth (contDiff_fderiv_apply_of_smooth hsm _) _).continuous

theorem hasCompactSupport_stSpaceLap {φ : ℝ × Vec 2 → ℝ} (hcs : HasCompactSupport φ) :
    HasCompactSupport (stSpaceLap φ) := by
  have h : stSpaceLap φ = fun p =>
      fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec 0)) p (0, basisVec 0) +
        fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec 1)) p (0, basisVec 1) := by
    funext p; simp [stSpaceLap, Fin.sum_univ_two]
  rw [h]
  exact (hasCompactSupport_fderiv_apply (hasCompactSupport_fderiv_apply hcs _) _).add
    (hasCompactSupport_fderiv_apply (hasCompactSupport_fderiv_apply hcs _) _)

theorem caloric_part (hflux : SkewDriftFluxStmt)
    {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {d : ℝ × Vec 2 → Vec 2}
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2} {kK kd : ℝ}
    (hcoef : IsSkewDriftCoeff K d kK kd) (hdiv : IsDivFreeQ1 d) (hU : IsEnergyClassQ1 U DU)
    (hw : IsSkewDriftWeak K d U DU) (c : ℝ) {Z : ℝ × Vec 2 → ℝ} {DZ : ℝ × Vec 2 → Vec 2}
    (hZ : MemLp Z 2 (volume.restrict (openCyl 0 (3 / 4))))
    (hDZ : ∀ i : Fin 2, MemLp (fun p => DZ p i) 2 (volume.restrict (openCyl 0 (3 / 4))))
    (hZgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo (-(9 / 16) : ℝ) 0)),
      HasWeakGradientOn (euclidBall 0 (3 / 4)) (fun y => Z (τ, y)) (fun y => DZ (τ, y)))
    (hFi : ∀ i : Fin 2, MemLp (fun p => skewForcing K d U DU c p i) 2
      (volume.restrict (openCyl 0 (3 / 4))))
    (hZeq : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (openCyl 0 (3 / 4)) φ →
      ∫ p in openCyl 0 (3 / 4), (-(Z p * stTimeDeriv φ p) + vecDot (DZ p) (stSpaceGrad φ p)) =
        -∫ p in openCyl 0 (3 / 4), vecDot (skewForcing K d U DU c p) (stSpaceGrad φ p))
    (φ : ℝ × Vec 2 → ℝ) (hφ : IsSTTest (openCyl 0 (3 / 4)) φ) :
    ∫ p in openCyl 0 (3 / 4), (U p - Z p - c) * (stTimeDeriv φ p + stSpaceLap φ p) = 0 := by
  set S := openCyl 0 (3 / 4)
  have hsub : S ⊆ openCyl 0 1 := openCyl_three_quarters_subset
  have hSfin : volume S ≠ ⊤ := openCyl_volume_ne_top 0 (by norm_num)
  have hres : ∀ {f : ℝ × Vec 2 → ℝ}, MemLp f 2 (volume.restrict (openCyl 0 1)) →
      IntegrableOn f S := fun hf =>
    integrableOn_of_memLp_two hSfin (hf.mono_measure (Measure.restrict_mono hsub le_rfl))
  have hUi : IntegrableOn U S := hres hU.1
  have hDUi : ∀ i : Fin 2, IntegrableOn (fun p => DU p i) S := fun i => hres (hU.2.1 i)
  have hZi : IntegrableOn Z S := integrableOn_of_memLp_two hSfin hZ
  have hDZi : ∀ i : Fin 2, IntegrableOn (fun p => DZ p i) S :=
    fun i => integrableOn_of_memLp_two hSfin (hDZ i)
  have hFii : ∀ i : Fin 2, IntegrableOn (fun p => skewForcing K d U DU c p i) S :=
    fun i => integrableOn_of_memLp_two hSfin (hFi i)
  have hsm := hφ.1
  have hcs := hφ.2.1
  have htc : Continuous (stTimeDeriv φ) := (contDiff_fderiv_apply_of_smooth hsm _).continuous
  have htcs : HasCompactSupport (stTimeDeriv φ) := hasCompactSupport_fderiv_apply hcs _
  have hlc : Continuous (stSpaceLap φ) := continuous_stSpaceLap hsm
  have hlcs : HasCompactSupport (stSpaceLap φ) := hasCompactSupport_stSpaceLap hcs
  -- the flux identity on `Q_{3/4}`
  have hflux1 := hflux K d U DU kK kd hcoef hdiv hU hw c φ ⟨hsm, hcs, hφ.2.2.trans hsub⟩
  have hvan : ∀ p ∈ openCyl 0 1 \ S, -(U p * stTimeDeriv φ p)
      + vecDot ((1 + K p).mulVec (DU p) - (U p - c) • d p) (stSpaceGrad φ p) = 0 := by
    intro p hp
    have hp' : p ∉ tsupport φ := fun h => hp.2 (hφ.2.2 h)
    have hfd : fderiv ℝ φ p = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hp'
    have hgrad : stSpaceGrad φ p = 0 := by funext i; simp [stSpaceGrad, hfd]
    simp [stTimeDeriv, hfd, hgrad, vecDot]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (openCyl_measurable 0 1) hsub hvan]
    at hflux1
  have hsplit : ∀ p, vecDot ((1 + K p).mulVec (DU p) - (U p - c) • d p) (stSpaceGrad φ p) =
      vecDot (DU p) (stSpaceGrad φ p) + vecDot (skewForcing K d U DU c p) (stSpaceGrad φ p) := by
    intro p
    rw [← vecDot_add_left]
    congr 1
    simp only [skewForcing, Matrix.add_mulVec, Matrix.one_mulVec]
    abel
  simp only [hsplit] at hflux1
  have iUt := integrable_mul_cont hUi htc htcs
  have iZt := integrable_mul_cont hZi htc htcs
  have iUl := integrable_mul_cont hUi hlc hlcs
  have iZl := integrable_mul_cont hZi hlc hlcs
  have iDU := integrable_vecDot_grad hDUi hsm hcs
  have iDZ := integrable_vecDot_grad hDZi hsm hcs
  have iF := integrable_vecDot_grad hFii hsm hcs
  have hfl : ∫ p in S, U p * stTimeDeriv φ p =
      (∫ p in S, vecDot (DU p) (stSpaceGrad φ p)) +
        ∫ p in S, vecDot (skewForcing K d U DU c p) (stSpaceGrad φ p) := by
    have e1 := integral_add (μ := volume.restrict S) (f := fun x => -(U x * stTimeDeriv φ x))
      (g := fun x => vecDot (DU x) (stSpaceGrad φ x) +
        vecDot (skewForcing K d U DU c x) (stSpaceGrad φ x)) iUt.neg (iDU.add iF)
    have e2 := integral_add (μ := volume.restrict S) (f := fun x => vecDot (DU x) (stSpaceGrad φ x))
      (g := fun x => vecDot (skewForcing K d U DU c x) (stSpaceGrad φ x)) iDU iF
    have e3 := integral_neg (μ := volume.restrict S) (fun x => U x * stTimeDeriv φ x)
    linarith
  have hzl : ∫ p in S, Z p * stTimeDeriv φ p =
      (∫ p in S, vecDot (DZ p) (stSpaceGrad φ p)) +
        ∫ p in S, vecDot (skewForcing K d U DU c p) (stSpaceGrad φ p) := by
    have := hZeq φ hφ
    have e1 := integral_add (μ := volume.restrict S) (f := fun x => -(Z x * stTimeDeriv φ x))
      (g := fun x => vecDot (DZ x) (stSpaceGrad φ x)) iZt.neg iDZ
    have e3 := integral_neg (μ := volume.restrict S) (fun x => Z x * stTimeDeriv φ x)
    linarith
  -- slice integration by parts for the Laplacian terms
  have hφ' : IsSTTest (Set.Ioo (-(9 / 16) : ℝ) 0 ×ˢ euclidBall 0 (3 / 4)) φ := by
    rw [← openCyl_three_quarters_prod]; exact hφ
  have hUgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo (-(9 / 16) : ℝ) 0)),
      HasWeakGradientOn (euclidBall 0 (3 / 4)) (fun y => U (τ, y)) (fun y => DU (τ, y)) := by
    have h1 := ae_restrict_of_ae_restrict_of_subset
      (Set.Ioo_subset_Ioo_left (by norm_num : (-1 : ℝ) ≤ -(9 / 16))) hU.2.2.1
    filter_upwards [h1] with τ hτ
    have hball : euclidBall (0 : Vec 2) (3 / 4) ⊆ euclidBall 0 1 := by
      intro y hy
      simp only [euclidBall, Set.mem_ofPred_eq] at hy ⊢
      nlinarith
    exact HasWeakGradientOn.mono_set hball (External.Campanato.euclidBall_measurable 0 1) hτ
  have hUlap := integral_mul_stSpaceLap (H := U) (DH := DU)
    (by rw [← openCyl_three_quarters_prod]; exact hUi)
    (fun i => by rw [← openCyl_three_quarters_prod]; exact hDUi i) hUgrad hφ'
  have hZlap := integral_mul_stSpaceLap (H := Z) (DH := DZ)
    (by rw [← openCyl_three_quarters_prod]; exact hZi)
    (fun i => by rw [← openCyl_three_quarters_prod]; exact hDZi i) hZgrad hφ'
  rw [← openCyl_three_quarters_prod] at hUlap hZlap
  have h0t : ∫ p in S, stTimeDeriv φ p = 0 := integral_stTimeDeriv_eq_zero hφ
  have h0l : ∫ p in S, stSpaceLap φ p = 0 := integral_stSpaceLap_eq_zero hφ
  have hexp : (fun p => (U p - Z p - c) * (stTimeDeriv φ p + stSpaceLap φ p)) =
      fun p => (U p * stTimeDeriv φ p + U p * stSpaceLap φ p) -
        (Z p * stTimeDeriv φ p + Z p * stSpaceLap φ p) -
        c * (stTimeDeriv φ p + stSpaceLap φ p) := by
    funext p; ring
  have ict : Integrable (fun p => stTimeDeriv φ p) (volume.restrict S) :=
    (htc.integrable_of_hasCompactSupport htcs).integrableOn
  have icl : Integrable (fun p => stSpaceLap φ p) (volume.restrict S) :=
    (hlc.integrable_of_hasCompactSupport hlcs).integrableOn
  have j1 := integral_sub (μ := volume.restrict S)
    (f := fun p => (U p * stTimeDeriv φ p + U p * stSpaceLap φ p) -
      (Z p * stTimeDeriv φ p + Z p * stSpaceLap φ p))
    (g := fun p => c * (stTimeDeriv φ p + stSpaceLap φ p))
    ((iUt.add iUl).sub (iZt.add iZl)) ((ict.add icl).const_mul c)
  have j2 := integral_sub (μ := volume.restrict S)
    (f := fun p => U p * stTimeDeriv φ p + U p * stSpaceLap φ p)
    (g := fun p => Z p * stTimeDeriv φ p + Z p * stSpaceLap φ p) (iUt.add iUl) (iZt.add iZl)
  have j3 := integral_add (μ := volume.restrict S) (f := fun p => U p * stTimeDeriv φ p)
    (g := fun p => U p * stSpaceLap φ p) iUt iUl
  have j4 := integral_add (μ := volume.restrict S) (f := fun p => Z p * stTimeDeriv φ p)
    (g := fun p => Z p * stSpaceLap φ p) iZt iZl
  have j5 := integral_const_mul (μ := volume.restrict S) c
    (fun p => stTimeDeriv φ p + stSpaceLap φ p)
  have j6 := integral_add (μ := volume.restrict S) (f := fun p => stTimeDeriv φ p)
    (g := fun p => stSpaceLap φ p) ict icl
  rw [hexp, j1, j2, j3, j4, j5, j6, h0t, h0l, hfl, hzl, hUlap, hZlap]
  ring

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVRegularity.External.Campanato
namespace AVRegularity.Applications

/-! # One-step decay of the excess

`E(0,λ) ≤ C₂ (λ² + λ⁻⁴ η²) E(0,1)` for `0 < λ ≤ 1/2`. The flux form and the Caccioppoli inequality enter as the explicit
statements `SkewDriftFluxStmt`, `SkewDriftCaccioppoliStmt`. -/

theorem cylinder_mono_radius {ρ σ : ℝ} (h0 : 0 ≤ ρ) (hρσ : ρ ≤ σ) (z : ℝ × Vec 2) :
    cylinder z ρ ⊆ cylinder z σ := by
  rintro ⟨τ, y⟩ ⟨⟨h1, h2⟩, h3⟩
  refine ⟨⟨?_, h2⟩, ?_⟩
  · have : ρ ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ h0 hρσ 2
    simp only at h1 ⊢; linarith
  · simp only [euclidBall, Set.mem_ofPred_eq] at h3 ⊢
    have : ρ ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ h0 hρσ 2
    linarith

theorem openCyl_mono_radius {ρ σ : ℝ} (h0 : 0 ≤ ρ) (hρσ : ρ ≤ σ) (z : ℝ × Vec 2) :
    openCyl z ρ ⊆ openCyl z σ := by
  rintro ⟨τ, y⟩ ⟨⟨h1, h2⟩, h3⟩
  refine ⟨⟨?_, h2⟩, ?_⟩
  · have : ρ ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ h0 hρσ 2
    simp only at h1 ⊢; linarith
  · simp only [euclidBall, Set.mem_ofPred_eq] at h3 ⊢
    have : ρ ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ h0 hρσ 2
    linarith

theorem cylinderExcess_nonneg' (f : ℝ × Vec 2 → ℝ) (z : ℝ × Vec 2) (r : ℝ) :
    0 ≤ cylinderExcess f z r :=
  setAverage_nonneg_of_nonneg fun _ => sq_nonneg _

theorem integral_sq_eq_volume_mul_excess {U : ℝ × Vec 2 → ℝ} :
    ∫ p in openCyl 0 1, (U p - cylinderMean U 0 1) ^ 2 =
      volume.real (cylinder 0 1) * cylinderExcess U 0 1 := by
  have hV := cylinder_volume_pos (0 : ℝ × Vec 2) one_pos
  rw [cylinderExcess, setAverage_eq, smul_eq_mul, restrict_openCyl_eq]
  field_simp

theorem mem_cylinder_bounds {lam : ℝ} (hlam : 0 < lam) {p : ℝ × Vec 2}
    (hp : p ∈ cylinder 0 lam) : |p.1| ≤ lam ^ 2 ∧ Real.sqrt (vecNormSq p.2) < lam := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  simp only [Prod.fst_zero, zero_sub] at h1 h2
  simp only [euclidBall, Set.mem_ofPred_eq, Prod.snd_zero, sub_zero] at h3
  refine ⟨by rw [abs_le]; constructor <;> linarith, ?_⟩
  rw [show lam = Real.sqrt (lam ^ 2) by rw [Real.sqrt_sq hlam.le]]
  exact Real.sqrt_lt_sqrt (vecNormSq_nonneg _) h3

theorem real_combine {P Q X Y : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    P * X + Q * Y ≤ (P + Q) * (X + Y) := by
  nlinarith [mul_nonneg hP hY, mul_nonneg hQ hX]

/-- The excess on `Q_λ` of `U = c + ĥ + Z` with `ĥ` Lipschitz. -/
theorem excess_le_of_split {U Z hh : ℝ × Vec 2 → ℝ} {c L lam : ℝ} (hlam : 0 < lam)
    (hlam2 : lam ≤ 1 / 2) (hL : 0 ≤ L)
    (hU : MemLp U 2 (volume.restrict (openCyl 0 1)))
    (hZ : MemLp Z 2 (volume.restrict (openCyl 0 (3 / 4))))
    (hsplit : ∀ᵐ p ∂(volume.restrict (cylinder (0 : ℝ × Vec 2) (1 / 2))),
      U p = c + hh p + Z p)
    (hlip : ∀ z ∈ cylinder (0 : ℝ × Vec 2) (1 / 2), ∀ w ∈ cylinder (0 : ℝ × Vec 2) (1 / 2),
      |hh z - hh w| ≤ L * (|z.1 - w.1| + Real.sqrt (vecNormSq (z.2 - w.2)))) :
    cylinderExcess U 0 lam ≤
      8 * L ^ 2 * lam ^ 2 + 2 * (lam ^ 4)⁻¹ * ∫ p in openCyl 0 (3 / 4), Z p ^ 2 := by
  have hlamsub : cylinder (0 : ℝ × Vec 2) lam ⊆ cylinder 0 (1 / 2) :=
    cylinder_mono_radius hlam.le hlam2 0
  have h0mem : (0 : ℝ × Vec 2) ∈ cylinder 0 (1 / 2) := by
    refine ⟨⟨by norm_num, le_rfl⟩, ?_⟩
    simp [euclidBall, vecNormSq, vecDot]
  set m := c + hh 0
  have hpt : ∀ᵐ p ∂(volume.restrict (cylinder (0 : ℝ × Vec 2) lam)),
      (U p - m) ^ 2 ≤ 8 * L ^ 2 * lam ^ 2 + 2 * Z p ^ 2 := by
    have hae := ae_restrict_of_ae_restrict_of_subset hlamsub hsplit
    filter_upwards [hae, ae_restrict_mem (cylinder_measurable 0 lam)] with p hp hpm
    have hlp := hlip p (hlamsub hpm) 0 h0mem
    obtain ⟨hp1, hp2⟩ := mem_cylinder_bounds hlam hpm
    have hdist : |p.1 - (0 : ℝ × Vec 2).1| + Real.sqrt (vecNormSq (p.2 - (0 : ℝ × Vec 2).2)) ≤
        2 * lam := by
      simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
      nlinarith
    have hdiff : |hh p - hh 0| ≤ L * (2 * lam) :=
      hlp.trans (mul_le_mul_of_nonneg_left hdist hL)
    have hUeq : U p - m = (hh p - hh 0) + Z p := by
      simp only [m, hp]; ring
    rw [hUeq]
    have habs : (hh p - hh 0) ^ 2 ≤ (L * (2 * lam)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hdiff 2
    nlinarith [sq_nonneg (hh p - hh 0 - Z p)]
  have hUlam : MemLp U 2 (volume.restrict (cylinder (0 : ℝ × Vec 2) lam)) := by
    refine hU.mono_measure ?_
    rw [restrict_openCyl_eq]
    exact Measure.restrict_mono (cylinder_mono_radius hlam.le (by linarith) 0) le_rfl
  have hex := cylinderExcess_le U 0 hlam hUlam m
  have hlam34 : openCyl (0 : ℝ × Vec 2) lam ⊆ openCyl 0 (3 / 4) :=
    openCyl_mono_radius hlam.le (by linarith) 0
  have hZlam : MemLp Z 2 (volume.restrict (cylinder (0 : ℝ × Vec 2) lam)) := by
    rw [← restrict_openCyl_eq]
    exact hZ.mono_measure (Measure.restrict_mono hlam34 le_rfl)
  have hVlam := cylinder_volume_pos (0 : ℝ × Vec 2) hlam
  have hVlamge := cylinder_volumeReal_ge (0 : ℝ × Vec 2) hlam
  have hfinlam : IsFiniteMeasure (volume.restrict (cylinder (0 : ℝ × Vec 2) lam)) :=
    isFiniteMeasure_restrict.mpr (cylinder_volume_ne_top 0 hlam)
  refine hex.trans ?_
  rw [setAverage_eq, smul_eq_mul]
  have hint : ∫ p in cylinder 0 lam, (U p - m) ^ 2 ≤
      ∫ p in cylinder 0 lam, (8 * L ^ 2 * lam ^ 2 + 2 * Z p ^ 2) :=
    integral_mono_ae (hUlam.sub (memLp_const m)).integrable_sq
      ((integrable_const _).add (hZlam.integrable_sq.const_mul 2)) hpt
  have hsplit2 := integral_add (μ := volume.restrict (cylinder (0 : ℝ × Vec 2) lam))
    (f := fun _ => 8 * L ^ 2 * lam ^ 2) (g := fun p => 2 * Z p ^ 2)
    (integrable_const _) (hZlam.integrable_sq.const_mul 2)
  rw [hsplit2, setIntegral_const, integral_const_mul, smul_eq_mul] at hint
  have hZcyl : ∫ p in cylinder 0 lam, Z p ^ 2 ≤ ∫ p in openCyl 0 (3 / 4), Z p ^ 2 := by
    rw [← restrict_openCyl_eq]
    exact setIntegral_mono_set hZ.integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) (Filter.Eventually.of_forall hlam34)
  have hinv : (volume.real (cylinder (0 : ℝ × Vec 2) lam))⁻¹ ≤ (lam ^ 4)⁻¹ :=
    inv_anti₀ (by positivity) hVlamge
  have hZcylnn : 0 ≤ ∫ p in cylinder 0 lam, Z p ^ 2 := setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  calc (volume.real (cylinder (0 : ℝ × Vec 2) lam))⁻¹ * ∫ p in cylinder 0 lam, (U p - m) ^ 2
      ≤ (volume.real (cylinder (0 : ℝ × Vec 2) lam))⁻¹ *
          (volume.real (cylinder (0 : ℝ × Vec 2) lam) * (8 * L ^ 2 * lam ^ 2) +
            2 * ∫ p in cylinder 0 lam, Z p ^ 2) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hVlam.le)
    _ = 8 * L ^ 2 * lam ^ 2 +
          2 * (volume.real (cylinder (0 : ℝ × Vec 2) lam))⁻¹ * ∫ p in cylinder 0 lam, Z p ^ 2 := by
        field_simp
    _ ≤ 8 * L ^ 2 * lam ^ 2 + 2 * (lam ^ 4)⁻¹ * ∫ p in openCyl 0 (3 / 4), Z p ^ 2 := by
        gcongr

/-- `∫_{Q_{3/4}} (U - Z - c)² ≤ 2 ∫_{Q₁}(U - c)² + 2 ∫_{Q_{3/4}} Z²`. -/
theorem integral_sq_sub_le {U Z : ℝ × Vec 2 → ℝ} {c : ℝ}
    (hU : MemLp U 2 (volume.restrict (openCyl 0 1)))
    (hZ : MemLp Z 2 (volume.restrict (openCyl 0 (3 / 4)))) :
    ∫ p in openCyl 0 (3 / 4), (U p - Z p - c) ^ 2 ≤
      2 * (∫ p in openCyl 0 1, (U p - c) ^ 2) + 2 * ∫ p in openCyl 0 (3 / 4), Z p ^ 2 := by
  have hsub34 := openCyl_three_quarters_subset
  have hfin1 : IsFiniteMeasure (volume.restrict (openCyl (0 : ℝ × Vec 2) 1)) :=
    isFiniteMeasure_restrict.mpr (openCyl_volume_ne_top 0 one_pos)
  have hfin34 : IsFiniteMeasure (volume.restrict (openCyl (0 : ℝ × Vec 2) (3 / 4))) :=
    isFiniteMeasure_restrict.mpr (openCyl_volume_ne_top 0 (by norm_num))
  have hU34 : MemLp U 2 (volume.restrict (openCyl 0 (3 / 4))) :=
    hU.mono_measure (Measure.restrict_mono hsub34 le_rfl)
  have hV34 : MemLp (fun p => U p - c) 2 (volume.restrict (openCyl 0 (3 / 4))) :=
    hU34.sub (memLp_const c)
  have hh2 : MemLp (fun p => U p - Z p - c) 2 (volume.restrict (openCyl 0 (3 / 4))) :=
    (hU34.sub hZ).sub (memLp_const c)
  have hpt : ∀ p, (U p - Z p - c) ^ 2 ≤ 2 * (U p - c) ^ 2 + 2 * Z p ^ 2 := by
    intro p; nlinarith [sq_nonneg (U p - c + Z p)]
  have hmono : ∫ p in openCyl 0 (3 / 4), (U p - Z p - c) ^ 2 ≤
      ∫ p in openCyl 0 (3 / 4), (2 * (U p - c) ^ 2 + 2 * Z p ^ 2) :=
    integral_mono hh2.integrable_sq
      ((hV34.integrable_sq.const_mul 2).add (hZ.integrable_sq.const_mul 2)) hpt
  have hsplit := integral_add (μ := volume.restrict (openCyl (0 : ℝ × Vec 2) (3 / 4)))
    (f := fun p => 2 * (U p - c) ^ 2) (g := fun p => 2 * Z p ^ 2)
    (hV34.integrable_sq.const_mul 2) (hZ.integrable_sq.const_mul 2)
  rw [hsplit, integral_const_mul, integral_const_mul] at hmono
  have hV1 : ∫ p in openCyl 0 (3 / 4), (U p - c) ^ 2 ≤ ∫ p in openCyl 0 1, (U p - c) ^ 2 :=
    setIntegral_mono_set (hU.sub (memLp_const c)).integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) (Filter.Eventually.of_forall hsub34)
  linarith

theorem openCyl34_volumeReal_le : volume.real (openCyl (0 : ℝ × Vec 2) (3 / 4)) ≤ 4 := by
  have h1 : volume.real (openCyl (0 : ℝ × Vec 2) (3 / 4)) ≤
      volume.real (cylinder (0 : ℝ × Vec 2) (3 / 4)) :=
    measureReal_mono (openCyl_subset_cylinder 0 _) (cylinder_volume_ne_top 0 (by norm_num))
  have h2 := cylinder_volumeReal_le (0 : ℝ × Vec 2) (by norm_num : (0 : ℝ) < 3 / 4)
  nlinarith

/-- The arithmetic of the one-step decay. -/
theorem decay_arith {C₁ A E1 I1 L Zi lam η : ℝ} (hA : 0 ≤ A) (hE1 : 0 ≤ E1)
    (hI1 : I1 ≤ 4 * E1) (hL2 : L ^ 2 ≤ 4 * C₁ ^ 2 * (2 + 2 * A) * I1)
    (hZ : Zi ≤ A * η ^ 2 * I1) (hlam : 0 < lam) :
    8 * L ^ 2 * lam ^ 2 + 2 * (lam ^ 4)⁻¹ * Zi ≤
      (128 * C₁ ^ 2 * (2 + 2 * A) + 8 * A) * (lam ^ 2 + η ^ 2 / lam ^ 4) * E1 := by
  have hB : 0 ≤ 4 * C₁ ^ 2 * (2 + 2 * A) := by positivity
  have hL2' : L ^ 2 ≤ 16 * C₁ ^ 2 * (2 + 2 * A) * E1 := by
    have := mul_le_mul_of_nonneg_left hI1 hB
    linarith
  have hZ' : Zi ≤ 4 * A * η ^ 2 * E1 := by
    have := mul_le_mul_of_nonneg_left hI1 (by positivity : (0 : ℝ) ≤ A * η ^ 2)
    linarith
  have hinv : 0 ≤ (lam ^ 4)⁻¹ := by positivity
  have t1 : 8 * L ^ 2 * lam ^ 2 ≤ 128 * C₁ ^ 2 * (2 + 2 * A) * E1 * lam ^ 2 := by
    have := mul_le_mul_of_nonneg_right hL2' (sq_nonneg lam)
    linarith
  have t2 : 2 * (lam ^ 4)⁻¹ * Zi ≤ 8 * A * E1 * (η ^ 2 / lam ^ 4) := by
    have := mul_le_mul_of_nonneg_left hZ' (by positivity : (0 : ℝ) ≤ 2 * (lam ^ 4)⁻¹)
    rw [div_eq_mul_inv]
    linarith
  have hcomb := real_combine (by positivity : (0 : ℝ) ≤ 128 * C₁ ^ 2 * (2 + 2 * A) * E1)
    (by positivity : (0 : ℝ) ≤ 8 * A * E1) (sq_nonneg lam)
    (by positivity : (0 : ℝ) ≤ η ^ 2 / lam ^ 4)
  calc 8 * L ^ 2 * lam ^ 2 + 2 * (lam ^ 4)⁻¹ * Zi
      ≤ 128 * C₁ ^ 2 * (2 + 2 * A) * E1 * lam ^ 2 + 8 * A * E1 * (η ^ 2 / lam ^ 4) := by
        linarith
    _ ≤ _ := hcomb
    _ = _ := by ring

/-- **One-step decay** (Step 2 of the proof of Lemma 3.3 of the paper, display (8.6)). -/
theorem one_step_decay (hflux : SkewDriftFluxStmt) (hcacc : SkewDriftCaccioppoliStmt) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
      (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) (kK kd η : ℝ),
      0 ≤ kK → 0 ≤ kd → kK + kd ≤ η → η ≤ 1 → IsSkewDriftCoeff K d kK kd →
      (∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p) →
      IsDivFreeQ1 d → IsEnergyClassQ1 U DU → IsSkewDriftWeak K d U DU →
      ∀ lam : ℝ, 0 < lam → lam ≤ 1 / 2 →
        cylinderExcess U 0 lam ≤ C₂ * (lam ^ 2 + η ^ 2 / lam ^ 4) * cylinderExcess U 0 1 := by
  obtain ⟨C₀, hC₀, hcac⟩ := hcacc
  obtain ⟨Ch, hCh, hheat⟩ := heat_replacement
  obtain ⟨C₁, hC₁, hcal⟩ := caloric_interior_lipschitz
  set A : ℝ := 2 * Ch * (C₀ + 1)
  have hA : 0 ≤ A := by positivity
  refine ⟨128 * C₁ ^ 2 * (2 + 2 * A) + 8 * A, by positivity, ?_⟩
  intro K d U DU kK kd η hkK hkd hη hη1 hcoef hskew hdiv hU hw lam hlam hlam2
  set c := cylinderMean U 0 1
  set I1 := ∫ p in openCyl 0 1, (U p - c) ^ 2
  set E1 := cylinderExcess U 0 1
  have hE1 : 0 ≤ E1 := cylinderExcess_nonneg' U 0 1
  have hI1 : I1 ≤ 4 * E1 := by
    have h := integral_sq_eq_volume_mul_excess (U := U)
    have hv := cylinder_volumeReal_le (0 : ℝ × Vec 2) one_pos
    rw [one_pow, mul_one] at hv
    change I1 = _ at h
    rw [h]
    exact mul_le_mul_of_nonneg_right hv hE1
  have hI1nn : 0 ≤ I1 := setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have hη0 : 0 ≤ η := le_trans (add_nonneg hkK hkd) hη
  have hη2 : η ^ 2 ≤ 1 := by nlinarith
  -- Caccioppoli and forcing
  have hcacU := hcac K d U DU kK kd hkK hkd (hη.trans hη1) hcoef hskew hdiv hU hw c
  have hsub34 := openCyl_three_quarters_subset
  have hFi : ∀ i : Fin 2, MemLp (fun p => skewForcing K d U DU c p i) 2
      (volume.restrict (openCyl 0 (3 / 4))) := fun i =>
    (skewForcing_memLp hcoef hkK hkd hη hU c i).mono_measure
      (Measure.restrict_mono hsub34 le_rfl)
  have hFb := skewForcing_bound hcoef hkK hkd hη hU c
  obtain ⟨Z, DZ, hZ, hDZ, hZgrad, hZbound, hZeq⟩ := hheat (skewForcing K d U DU c) hFi
  have hZ2 : ∫ p in openCyl 0 (3 / 4), Z p ^ 2 ≤ A * η ^ 2 * I1 := by
    refine hZbound.trans ?_
    calc Ch * ∫ p in openCyl 0 (3 / 4), vecNormSq (skewForcing K d U DU c p)
        ≤ Ch * (2 * η ^ 2 * (C₀ * I1 + I1)) :=
          mul_le_mul_of_nonneg_left (hFb.trans (by gcongr)) hCh
      _ = A * η ^ 2 * I1 := by simp only [A]; ring
  have hZ2' : ∫ p in openCyl 0 (3 / 4), Z p ^ 2 ≤ A * I1 :=
    hZ2.trans (by nlinarith [mul_nonneg hA hI1nn])
  -- the caloric part and its Lipschitz representative
  have hcaloric := caloric_part hflux hcoef hdiv hU hw c hZ hDZ hZgrad hFi hZeq
  have hS34 : volume (openCyl (0 : ℝ × Vec 2) (3 / 4)) ≠ ⊤ :=
    openCyl_volume_ne_top 0 (by norm_num)
  have hfin34 : IsFiniteMeasure (volume.restrict (openCyl (0 : ℝ × Vec 2) (3 / 4))) :=
    isFiniteMeasure_restrict.mpr hS34
  have hh2 : MemLp (fun p => U p - Z p - c) 2 (volume.restrict (openCyl 0 (3 / 4))) :=
    ((hU.1.mono_measure (Measure.restrict_mono hsub34 le_rfl)).sub hZ).sub (memLp_const c)
  obtain ⟨hh, hhae, hlip⟩ := hcal (fun p => U p - Z p - c) (hh2.integrable one_le_two) hcaloric
  set L := C₁ * ∫ p in openCyl 0 (3 / 4), |U p - Z p - c|
  have hL0 : 0 ≤ L := mul_nonneg hC₁ (setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall fun _ => abs_nonneg _))
  have hL2 : L ^ 2 ≤ 4 * C₁ ^ 2 * (2 + 2 * A) * I1 := by
    have hcs := sq_setIntegral_abs_le hS34 hh2
    have hhb := integral_sq_sub_le (c := c) hU.1 hZ
    have hhi2 : 0 ≤ ∫ p in openCyl 0 (3 / 4), (U p - Z p - c) ^ 2 :=
      setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    have hvol := openCyl34_volumeReal_le
    have hb2 : ∫ p in openCyl 0 (3 / 4), (U p - Z p - c) ^ 2 ≤ (2 + 2 * A) * I1 := by
      linarith
    simp only [L, mul_pow]
    calc C₁ ^ 2 * (∫ p in openCyl 0 (3 / 4), |U p - Z p - c|) ^ 2
        ≤ C₁ ^ 2 * (volume.real (openCyl (0 : ℝ × Vec 2) (3 / 4)) *
            ∫ p in openCyl 0 (3 / 4), (U p - Z p - c) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ ≤ C₁ ^ 2 * (4 * ((2 + 2 * A) * I1)) := by gcongr
      _ = 4 * C₁ ^ 2 * (2 + 2 * A) * I1 := by ring
  have hsplitU : ∀ᵐ p ∂(volume.restrict (cylinder (0 : ℝ × Vec 2) (1 / 2))),
      U p = c + hh p + Z p := by
    filter_upwards [hhae] with p hp
    rw [hp]; ring
  have hlip' : ∀ z ∈ cylinder (0 : ℝ × Vec 2) (1 / 2), ∀ w ∈ cylinder (0 : ℝ × Vec 2) (1 / 2),
      |hh z - hh w| ≤ L * (|z.1 - w.1| + Real.sqrt (vecNormSq (z.2 - w.2))) := by
    intro z hz w hw
    calc |hh z - hh w| ≤ _ := hlip z hz w hw
      _ = L * (|z.1 - w.1| + Real.sqrt (vecNormSq (z.2 - w.2))) := by simp only [L]; ring
  have hex := excess_le_of_split hlam hlam2 hL0 hU.1 hZ hsplitU hlip'
  calc cylinderExcess U 0 lam ≤ _ := hex
    _ ≤ _ := decay_arith hA hE1 hI1 hL2 hZ2 hlam

/-! # Iteration of the excess decay

Choosing `λ` and then `η`, the one-step decay and the rescaling
give `E(z, r) ≤ C₃ r^{2a'} E(0,1)` for all `z ∈ Q_{1/2}` and `0 < r < 1/4`. -/

/-- Choice of `λ`: `C₂ λ² ≤ λ^{2a'}/2`. -/
theorem exists_decay_lam {C₂ a' : ℝ} (hC₂ : 0 ≤ C₂) (ha₁ : a' < 1) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 / 2 ∧ C₂ * lam ^ 2 ≤ (1 / 2) * lam ^ (2 * a') := by
  set e : ℝ := 2 - 2 * a'
  have he : 0 < e := by simp only [e]; linarith
  set B : ℝ := (2 * C₂ + 1)⁻¹
  have hB : 0 < B := by positivity
  set lam : ℝ := min (1 / 2) (B ^ (1 / e))
  have hlam : 0 < lam := lt_min (by norm_num) (Real.rpow_pos_of_pos hB _)
  refine ⟨lam, hlam, min_le_left _ _, ?_⟩
  have hpow : lam ^ e ≤ B := by
    calc lam ^ e ≤ (B ^ (1 / e)) ^ e :=
          Real.rpow_le_rpow hlam.le (min_le_right _ _) he.le
      _ = B := by rw [← Real.rpow_mul hB.le, one_div_mul_cancel he.ne', Real.rpow_one]
  have hsplit : lam ^ (2 : ℝ) = lam ^ (2 * a') * lam ^ e := by
    rw [← Real.rpow_add hlam]; congr 1; simp only [e]; ring
  have hsq : lam ^ 2 = lam ^ (2 : ℝ) := by norm_cast
  rw [hsq, hsplit]
  have hCB : C₂ * B ≤ 1 / 2 := by
    simp only [B]
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  have hpos : 0 ≤ lam ^ (2 * a') := Real.rpow_nonneg hlam.le _
  calc C₂ * (lam ^ (2 * a') * lam ^ e) = lam ^ (2 * a') * (C₂ * lam ^ e) := by ring
    _ ≤ lam ^ (2 * a') * (C₂ * B) := by gcongr
    _ ≤ lam ^ (2 * a') * (1 / 2) := by gcongr
    _ = (1 / 2) * lam ^ (2 * a') := by ring

/-- Choice of `η` after `λ`: `C₂ η² λ⁻⁴ ≤ λ^{2a'}/2`, `0 < η ≤ 1`. -/
theorem exists_decay_eta {C₂ lam a' : ℝ} (hC₂ : 0 ≤ C₂) (hlam : 0 < lam) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ C₂ * (η ^ 2 / lam ^ 4) ≤ (1 / 2) * lam ^ (2 * a') := by
  set X : ℝ := lam ^ (2 * a') * lam ^ 4 / (2 * C₂ + 1)
  have hX : 0 < X := by positivity
  set η : ℝ := min 1 (Real.sqrt X)
  have hη : 0 < η := lt_min one_pos (Real.sqrt_pos.mpr hX)
  refine ⟨η, hη, min_le_left _ _, ?_⟩
  have hη2 : η ^ 2 ≤ X := by
    have h1 : η ≤ Real.sqrt X := min_le_right _ _
    calc η ^ 2 ≤ (Real.sqrt X) ^ 2 := pow_le_pow_left₀ hη.le h1 2
      _ = X := Real.sq_sqrt hX.le
  have hl4 : 0 < lam ^ 4 := by positivity
  have hpos : 0 ≤ lam ^ (2 * a') := Real.rpow_nonneg hlam.le _
  calc C₂ * (η ^ 2 / lam ^ 4) ≤ C₂ * (X / lam ^ 4) := by gcongr
    _ = lam ^ (2 * a') * (C₂ / (2 * C₂ + 1)) := by
        simp only [X]; field_simp
    _ ≤ lam ^ (2 * a') * (1 / 2) := by
        have h : C₂ / (2 * C₂ + 1) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; linarith
        exact mul_le_mul_of_nonneg_left h hpos
    _ = (1 / 2) * lam ^ (2 * a') := by ring

theorem euclidBall_half_add {y c : Vec 2} {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hy : vecNormSq (y - c) < r ^ 2) (hc : vecNormSq c < (1 / 2) ^ 2) : vecNormSq y < 1 := by
  have hdecomp : y = (y - c) + c := by abel
  have hsum := vecNormSq_add_le (y - c) c
  rw [← hdecomp] at hsum
  have hr2 : r ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ hr0 hr 2
  nlinarith

theorem openCyl_subset_of_mem_half {z : ℝ × Vec 2} (hz : z ∈ cylinder (0 : ℝ × Vec 2) (1 / 2))
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) : openCyl z r ⊆ openCyl 0 1 := by
  obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
  simp only [Prod.fst_zero, zero_sub] at hz1 hz2
  simp only [euclidBall, Set.mem_ofPred_eq, Prod.snd_zero, sub_zero] at hz3
  rintro ⟨τ, y⟩ ⟨⟨h1, h2⟩, h3⟩
  simp only [euclidBall, Set.mem_ofPred_eq] at h3
  have hr4 : r ^ 2 ≤ 1 / 4 := by nlinarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Prod.fst_zero, zero_sub, one_pow]; nlinarith
  · simp only [Prod.fst_zero]; linarith
  · simp only [euclidBall, Set.mem_ofPred_eq, Prod.snd_zero, sub_zero, one_pow]
    exact euclidBall_half_add hr.le hr2 h3 hz3

theorem cylinder_subset_of_mem_half {z : ℝ × Vec 2} (hz : z ∈ cylinder (0 : ℝ × Vec 2) (1 / 2))
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) : cylinder z r ⊆ cylinder 0 1 := by
  obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
  simp only [Prod.fst_zero, zero_sub] at hz1 hz2
  simp only [euclidBall, Set.mem_ofPred_eq, Prod.snd_zero, sub_zero] at hz3
  rintro ⟨τ, y⟩ ⟨⟨h1, h2⟩, h3⟩
  simp only [euclidBall, Set.mem_ofPred_eq] at h3
  have hr4 : r ^ 2 ≤ 1 / 4 := by nlinarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Prod.fst_zero, zero_sub, one_pow]; nlinarith
  · simp only [Prod.fst_zero]; linarith
  · simp only [euclidBall, Set.mem_ofPred_eq, Prod.snd_zero, sub_zero, one_pow]
    exact euclidBall_half_add hr.le hr2 h3 hz3

/-- The excess over a smaller cylinder is controlled by the excess over a larger one. -/
theorem cylinderExcess_le_ratio {U : ℝ × Vec 2 → ℝ} {z w : ℝ × Vec 2} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hsub : cylinder z r ⊆ cylinder w R)
    (hU : MemLp U 2 (volume.restrict (cylinder w R))) :
    cylinderExcess U z r ≤ (4 * R ^ 4 / r ^ 4) * cylinderExcess U w R := by
  have hUr : MemLp U 2 (volume.restrict (cylinder z r)) :=
    hU.mono_measure (Measure.restrict_mono hsub le_rfl)
  have h1 := cylinderExcess_le U z hr hUr (cylinderMean U w R)
  have hfinR : IsFiniteMeasure (volume.restrict (cylinder w R)) :=
    isFiniteMeasure_restrict.mpr (cylinder_volume_ne_top w hR)
  have hint : IntegrableOn (fun p => (U p - cylinderMean U w R) ^ 2) (cylinder w R) :=
    (hU.sub (memLp_const _)).integrable_sq
  have h2 := setAverage_le_measure_ratio (μ := volume) hsub (cylinder_volume_pos z hr)
    (cylinder_volume_pos w hR) hint (fun _ => sq_nonneg _)
  have hratio : (volume (cylinder w R)).toReal / (volume (cylinder z r)).toReal ≤
      4 * R ^ 4 / r ^ 4 := by
    have hu := cylinder_volumeReal_le w hR
    have hl := cylinder_volumeReal_ge z hr
    simp only [measureReal_def] at hu hl
    have hzpos := cylinder_volume_pos z hr
    simp only [measureReal_def] at hzpos
    rw [div_le_div_iff₀ hzpos (by positivity)]
    nlinarith [pow_pos hr 4, pow_pos hR 4]
  have hE : 0 ≤ cylinderExcess U w R := cylinderExcess_nonneg' U w R
  calc cylinderExcess U z r ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ (4 * R ^ 4 / r ^ 4) * cylinderExcess U w R := by
        unfold cylinderExcess
        gcongr

/-! # The Campanato decay `E(z,r) ≤ C₃ r^{2a'} E(0,1)` -/

/-- The rescaled one-step decay `E(z, rλ) ≤ λ^{2a'} E(z, r)`. -/
theorem rescaled_step {C₂ : ℝ}
    (hdecay : ∀ (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
      (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) (kK kd η : ℝ),
      0 ≤ kK → 0 ≤ kd → kK + kd ≤ η → η ≤ 1 → IsSkewDriftCoeff K d kK kd →
      (∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p) →
      IsDivFreeQ1 d → IsEnergyClassQ1 U DU → IsSkewDriftWeak K d U DU →
      ∀ lam : ℝ, 0 < lam → lam ≤ 1 / 2 →
        cylinderExcess U 0 lam ≤ C₂ * (lam ^ 2 + η ^ 2 / lam ^ 4) * cylinderExcess U 0 1)
    {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {d : ℝ × Vec 2 → Vec 2}
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2} {kK kd η lam : ℝ}
    (hkK : 0 ≤ kK) (hkd : 0 ≤ kd) (hη : kK + kd ≤ η) (hη1 : η ≤ 1)
    (hcoef : IsSkewDriftCoeff K d kK kd)
    (hskew : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p)
    (hdiv : IsDivFreeQ1 d) (hU : IsEnergyClassQ1 U DU) (hw : IsSkewDriftWeak K d U DU)
    (hlam : 0 < lam) (hlam2 : lam ≤ 1 / 2)
    {z : ℝ × Vec 2} (hz : z ∈ cylinder (0 : ℝ × Vec 2) (1 / 2)) {r : ℝ} (hr : 0 < r)
    (hr2 : r ≤ 1 / 2) :
    cylinderExcess U z (r * lam) ≤ C₂ * (lam ^ 2 + η ^ 2 / lam ^ 4) * cylinderExcess U z r := by
  have hsub := openCyl_subset_of_mem_half hz hr hr2
  obtain ⟨hKm, hdm, hb⟩ := hcoef
  have hcoef' : IsSkewDriftCoeff (rsK K z r) (rsd d z r) kK (r * kd) :=
    ⟨rescale_measurableK hr hsub hKm, rescale_measurabled hr hsub hdm, rescale_bound hr hsub hb⟩
  have hr1 : r ≤ 1 := by linarith
  have hkd' : 0 ≤ r * kd := mul_nonneg hr.le hkd
  have hη' : kK + r * kd ≤ η := by nlinarith
  have h := hdecay (rsK K z r) (rsd d z r) (rsU U z r) (rsDU DU z r) kK (r * kd) η hkK hkd' hη'
    hη1 hcoef' (rescale_skew hr hsub hskew) (rescale_divFree hr hsub hdiv)
    (rescale_energyClass hr hsub hU) (rescale_weak hr hsub hw) lam hlam hlam2
  have e1 := cylinderExcess_parDil z hr (ρ := lam) U
  have e2 := cylinderExcess_parDil z hr (ρ := 1) U
  rw [mul_one] at e2
  change cylinderExcess (fun p => U (parDil z r p)) 0 lam ≤
    C₂ * (lam ^ 2 + η ^ 2 / lam ^ 4) * cylinderExcess (fun p => U (parDil z r p)) 0 1 at h
  rw [e1, e2] at h
  exact h

theorem tendsto_pow_lam {lam : ℝ} (hlam : 0 < lam) (hlam2 : lam ≤ 1 / 2) :
    Filter.Tendsto (fun k : ℕ => lam ^ k) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one hlam.le (by linarith)

theorem rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (k : ℕ) : (x ^ a) ^ k = (x ^ k) ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast (x := x), ← Real.rpow_mul hx, ← Real.rpow_mul hx,
    mul_comm]

/-- **Campanato decay** (Step 3 of the proof of Lemma 3.3 of the paper, display (8.7)). -/
theorem campanato_decay (hflux : SkewDriftFluxStmt) (hcacc : SkewDriftCaccioppoliStmt)
    {a' : ℝ} (ha₀ : 0 < a') (ha₁ : a' < 1) :
    ∃ η C₃ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 ≤ C₃ ∧
      ∀ (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
        (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) (kK kd : ℝ),
        0 ≤ kK → 0 ≤ kd → kK + kd ≤ η → IsSkewDriftCoeff K d kK kd →
        (∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p) →
        IsDivFreeQ1 d → IsEnergyClassQ1 U DU → IsSkewDriftWeak K d U DU →
        ∀ z ∈ cylinder (0 : ℝ × Vec 2) (1 / 2), ∀ r : ℝ, 0 < r → r < 1 / 4 →
          cylinderExcess U z r ≤ (C₃ * cylinderExcess U 0 1) * r ^ (2 * a') := by
  obtain ⟨C₂, hC₂, hdecay⟩ := one_step_decay hflux hcacc
  obtain ⟨lam, hlam, hlam2, hlamC⟩ := exists_decay_lam hC₂ ha₁
  obtain ⟨η, hη, hη1, hηC⟩ := exists_decay_eta (a' := a') hC₂ hlam
  have hkey : C₂ * (lam ^ 2 + η ^ 2 / lam ^ 4) ≤ lam ^ (2 * a') := by
    have := add_le_add hlamC hηC
    linarith [mul_add C₂ (lam ^ 2) (η ^ 2 / lam ^ 4)]
  set q : ℝ := lam ^ (2 * a')
  have hq : 0 ≤ q := Real.rpow_nonneg hlam.le _
  refine ⟨η, 256 / lam ^ 4 * (2 / lam) ^ (2 * a'), hη, hη1, by positivity, ?_⟩
  intro K d U DU kK kd hkK hkd hkη hcoef hskew hdiv hU hw z hz r hr hr4
  have hstep : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 →
      cylinderExcess U z (ρ * lam) ≤ q * cylinderExcess U z ρ := by
    intro ρ hρ hρ2
    have h := rescaled_step hdecay hkK hkd hkη hη1 hcoef hskew hdiv hU hw hlam hlam2
      hz hρ hρ2
    exact h.trans (mul_le_mul_of_nonneg_right hkey (cylinderExcess_nonneg' U z ρ))
  -- iterate along `λ^k / 2`
  have hlam1 : lam < 1 := by linarith
  have hiter : ∀ k : ℕ, cylinderExcess U z (lam ^ k / 2) ≤ q ^ k * cylinderExcess U z (1 / 2) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk0 : 0 < lam ^ k / 2 := by positivity
      have hk2 : lam ^ k / 2 ≤ 1 / 2 := by
        have : lam ^ k ≤ 1 := pow_le_one₀ hlam.le hlam1.le
        linarith
      have h := hstep (lam ^ k / 2) hk0 hk2
      rw [show lam ^ k / 2 * lam = lam ^ (k + 1) / 2 by ring] at h
      calc cylinderExcess U z (lam ^ (k + 1) / 2) ≤ q * cylinderExcess U z (lam ^ k / 2) := h
        _ ≤ q * (q ^ k * cylinderExcess U z (1 / 2)) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (k + 1) * cylinderExcess U z (1 / 2) := by ring
  -- base bound `E(z, 1/2) ≤ 64 E(0,1)`
  have hU1 : MemLp U 2 (volume.restrict (cylinder (0 : ℝ × Vec 2) 1)) := by
    rw [← restrict_openCyl_eq]; exact hU.1
  have hbase : cylinderExcess U z (1 / 2) ≤ 64 * cylinderExcess U 0 1 := by
    have h := cylinderExcess_le_ratio (by norm_num : (0 : ℝ) < 1 / 2) one_pos
      (cylinder_subset_of_mem_half hz (by norm_num) le_rfl) hU1
    norm_num at h
    exact h
  -- the scale `k`
  have hexists : ∃ k : ℕ, lam ^ (k + 1) / 2 < r := by
    have ht := tendsto_pow_lam hlam hlam2
    have hev := (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 2 * r)))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    exact ⟨N, by have := hN (N + 1) (by omega); linarith⟩
  classical
  set k := Nat.find hexists
  have hk : lam ^ (k + 1) / 2 < r := Nat.find_spec hexists
  have hrk : r ≤ lam ^ k / 2 := by
    by_cases hk0 : k = 0
    · rw [hk0]; simp; linarith
    · have hmin := Nat.find_min hexists (show k - 1 < k by omega)
      push Not at hmin
      rw [show k - 1 + 1 = k by omega] at hmin
      exact hmin
  have hk0 : 0 < lam ^ k / 2 := by positivity
  have hUk : MemLp U 2 (volume.restrict (cylinder z (lam ^ k / 2))) := by
    refine hU1.mono_measure (Measure.restrict_mono ?_ le_rfl)
    refine (cylinder_mono_radius hk0.le ?_ z).trans
      (cylinder_subset_of_mem_half hz (by norm_num) le_rfl)
    have : lam ^ k ≤ 1 := pow_le_one₀ hlam.le hlam1.le
    linarith
  have hratio := cylinderExcess_le_ratio hr hk0 (cylinder_mono_radius hr.le hrk z) hUk
  have hlt : lam ^ k / 2 < r / lam := by
    rw [lt_div_iff₀ hlam]
    calc lam ^ k / 2 * lam = lam ^ (k + 1) / 2 := by ring
      _ < r := hk
  have hratio' : 4 * (lam ^ k / 2) ^ 4 / r ^ 4 ≤ 4 / lam ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (lam ^ k / 2) ^ 4 ≤ (r / lam) ^ 4 := pow_le_pow_left₀ hk0.le hlt.le 4
    have h2 : (r / lam) ^ 4 * lam ^ 4 = r ^ 4 := by field_simp
    nlinarith [pow_pos hlam 4]
  have hqk : q ^ k ≤ (2 / lam) ^ (2 * a') * r ^ (2 * a') := by
    rw [rpow_pow_comm hlam.le, ← Real.mul_rpow (by positivity) hr.le]
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    have : lam ^ k < 2 * r / lam := by
      have h2 : lam ^ k / 2 * 2 < r / lam * 2 := by linarith
      calc lam ^ k = lam ^ k / 2 * 2 := by ring
        _ < r / lam * 2 := h2
        _ = 2 * r / lam := by ring
    calc lam ^ k ≤ 2 * r / lam := this.le
      _ = 2 / lam * r := by ring
  have hE0 := cylinderExcess_nonneg' U 0 1
  have hEk := cylinderExcess_nonneg' U z (lam ^ k / 2)
  calc cylinderExcess U z r ≤ 4 * (lam ^ k / 2) ^ 4 / r ^ 4 * cylinderExcess U z (lam ^ k / 2) :=
        hratio
    _ ≤ 4 / lam ^ 4 * (q ^ k * (64 * cylinderExcess U 0 1)) := by
        gcongr
        exact (hiter k).trans (mul_le_mul_of_nonneg_left hbase (pow_nonneg hq k))
    _ ≤ 4 / lam ^ 4 * ((2 / lam) ^ (2 * a') * r ^ (2 * a') * (64 * cylinderExcess U 0 1)) := by
        gcongr
    _ = (256 / lam ^ 4 * (2 / lam) ^ (2 * a') * cylinderExcess U 0 1) * r ^ (2 * a') := by
        ring

end AVRegularity.Applications
end

section
open MeasureTheory
open Filter Topology Homogenization AVRegularity.External.Campanato
namespace AVRegularity.Applications

/-! # The microscopic oscillation lemma from the Caccioppoli step

`oc_microscopic_of_tools` proves `OcMicroscopicStatement` from the flux form and the
Caccioppoli inequality (`SkewDriftFluxStmt`, `SkewDriftCaccioppoliStmt`). -/

theorem cylinderMean_sub_le {U : ℝ × Vec 2 → ℝ} {x : ℝ × Vec 2} {r : ℝ} (hr : 0 < r)
    (hsub : cylinder x r ⊆ cylinder 0 1)
    (hU : MemLp U 2 (volume.restrict (cylinder (0 : ℝ × Vec 2) 1))) :
    |cylinderMean U x r - cylinderMean U 0 1| ≤
      Real.sqrt ((4 / r ^ 4) * cylinderExcess U 0 1) := by
  set c := cylinderMean U 0 1
  have hUr : MemLp U 2 (volume.restrict (cylinder x r)) :=
    hU.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hfin : IsFiniteMeasure (volume.restrict (cylinder x r)) :=
    isFiniteMeasure_restrict.mpr (cylinder_volume_ne_top x hr)
  have hV0 : volume (cylinder x r) ≠ 0 := by
    have := cylinder_volume_pos x hr
    rw [measureReal_def] at this
    exact (ENNReal.toReal_pos_iff.1 this).1.ne'
  have hmean : ⨍ p in cylinder x r, (U p - c) = cylinderMean U x r - c := by
    unfold cylinderMean
    rw [setAverage_eq, setAverage_eq, integral_sub (hUr.integrable one_le_two)
      (integrable_const c), setIntegral_const, smul_sub]
    simp only [smul_eq_mul]
    have hpos := cylinder_volume_pos x hr
    field_simp
  have h1 := setAverage_abs_le_sqrt_setAverage_sq hV0 (cylinder_volume_ne_top x hr)
    (fun p => U p - c) (hUr.sub (memLp_const c))
  rw [hmean] at h1
  refine h1.trans (Real.sqrt_le_sqrt ?_)
  have hfin1 : IsFiniteMeasure (volume.restrict (cylinder (0 : ℝ × Vec 2) 1)) :=
    isFiniteMeasure_restrict.mpr (cylinder_volume_ne_top 0 one_pos)
  have h2 := setAverage_le_measure_ratio (μ := volume) hsub (cylinder_volume_pos x hr)
    (cylinder_volume_pos 0 one_pos) ((hU.sub (memLp_const c)).integrable_sq)
    (fun p => sq_nonneg (U p - c))
  have hratio : (volume (cylinder (0 : ℝ × Vec 2) 1)).toReal / (volume (cylinder x r)).toReal ≤
      4 / r ^ 4 := by
    have hu := cylinder_volumeReal_le (0 : ℝ × Vec 2) one_pos
    have hl := cylinder_volumeReal_ge x hr
    have hp := cylinder_volume_pos x hr
    simp only [measureReal_def, one_pow, mul_one] at hu hl hp
    rw [div_le_div_iff₀ hp (by positivity)]
    nlinarith [pow_pos hr 4]
  refine h2.trans ?_
  unfold cylinderExcess
  exact mul_le_mul_of_nonneg_right hratio (setAverage_nonneg_of_nonneg fun _ => sq_nonneg _)

theorem cylinder_half_prod :
    cylinder (0 : ℝ × Vec 2) (1 / 2) = Set.Ioc (-(1 / 4) : ℝ) 0 ×ˢ euclidBall 0 (1 / 2) := by
  simp only [cylinder, Prod.fst_zero, Prod.snd_zero]
  norm_num

theorem euclidBall_volume_ne_top (c : Vec 2) (r : ℝ) : volume (euclidBall c r) ≠ ⊤ := by
  have hsub : euclidBall c r ⊆ Metric.closedBall c |r| := by
    intro y hy
    simp only [euclidBall, Set.mem_ofPred_eq] at hy
    rw [Metric.mem_closedBall, dist_pi_le_iff (abs_nonneg r)]
    intro i
    have := sq_apply_le_vecNormSq (y - c) i
    rw [Real.dist_eq, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs r]
    exact Real.sqrt_le_sqrt (by simp only [Pi.sub_apply] at this; nlinarith)
  exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hsub)

/-- **The microscopic oscillation lemma** from the Caccioppoli step. -/
theorem oc_microscopic_of_tools (hflux : SkewDriftFluxStmt) (hcacc : SkewDriftCaccioppoliStmt) :
    OcMicroscopicStatement := by
  intro a' ha₀ ha₁
  obtain ⟨η, C₃, hη, hη1, hC₃, hdec⟩ := campanato_decay hflux hcacc ha₀ ha₁
  set KH := campanatoHolderConstant a'
  set KC := campanatoConstant a'
  have hKH : 0 ≤ KH := by
    simp only [KH, campanatoHolderConstant]
    have := campanatoLocalConstant_pos ha₀
    have h12 : 0 ≤ (12 : ℝ) ^ a' := Real.rpow_nonneg (by norm_num) a'
    positivity
  have hKC : 0 ≤ KC := (campanatoConstant_pos ha₀).le
  set C : ℝ := KH * Real.sqrt C₃ + KC * Real.sqrt C₃ * (1 / 8 : ℝ) ^ a' + Real.sqrt 16384
  refine ⟨η, C, hη, by positivity, ?_⟩
  intro K d U DU hKm hdm hskew ⟨kK, kd, hkK, hkd, hkη, hb⟩ hdiv hU hw
  have hcoef : IsSkewDriftCoeff K d kK kd := ⟨hKm, hdm, hb⟩
  set E1 := cylinderExcess U 0 1
  have hE1 : 0 ≤ E1 := cylinderExcess_nonneg' U 0 1
  set M := C₃ * E1
  have hM : 0 ≤ M := mul_nonneg hC₃ hE1
  have hcamp : ∀ z ∈ halfWindow (0 : ℝ × Vec 2), ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess U z r ≤ M * r ^ (2 * a') :=
    fun z hz r hr hr4 => hdec K d U DU kK kd hkK hkd hkη hcoef hskew hdiv hU hw z hz r hr hr4
  have hU1 : MemLp U 2 (volume.restrict (window (0 : ℝ × Vec 2))) := by
    change MemLp U 2 (volume.restrict (cylinder 0 1))
    rw [← restrict_openCyl_eq]; exact hU.1
  obtain ⟨hcont, hae, hhold⟩ := campanato_morrey_characterization hU1 ha₀ ha₁ hcamp
  set Ut := campanatoRepresentative ((window (0 : ℝ × Vec 2)).indicator U)
  -- amplitude
  have hf : MemLp ((window (0 : ℝ × Vec 2)).indicator U) 2 volume := by
    rw [memLp_indicator_iff_restrict (window_measurable 0)]
    exact hU1
  have hamp : ∀ x ∈ cylinder (0 : ℝ × Vec 2) (1 / 2),
      |Ut x - cylinderMean U 0 1| ≤ (KC * Real.sqrt C₃ * (1 / 8 : ℝ) ^ a' + Real.sqrt 16384) *
        Real.sqrt E1 := by
    intro x hx
    have hcampx : ∀ r, 0 < r → r < 1 / 4 → cylinderExcess ((window (0 : ℝ × Vec 2)).indicator U)
        x r ≤ M * r ^ (2 * a') := by
      intro r hr hr4
      rw [cylinderExcess_indicator_eq 0 x U (cylinder_subset_window 0 x hx hr hr4)]
      exact hcamp x hx r hr hr4
    have htail := campanatoRepresentative_tail hf hM hcampx ha₀ 0
    have hsub8 : cylinder x (1 / 8) ⊆ window (0 : ℝ × Vec 2) :=
      cylinder_subset_window 0 x hx (by norm_num) (by norm_num)
    have havg : campanatoAverages ((window (0 : ℝ × Vec 2)).indicator U) x 0 =
        cylinderMean U x (1 / 8) := by
      simp only [campanatoAverages, campanatoScale, pow_zero, mul_one]
      exact cylinderMean_indicator_eq 0 x U hsub8
    rw [havg] at htail
    have hmean := cylinderMean_sub_le (by norm_num : (0 : ℝ) < 1 / 8) hsub8 hU1
    have h4 : (4 : ℝ) / (1 / 8) ^ 4 = 16384 := by norm_num
    rw [h4, Real.sqrt_mul (by norm_num)] at hmean
    have hsc : campanatoScale 0 = 1 / 8 := by simp [campanatoScale]
    rw [hsc, Real.sqrt_mul hC₃] at htail
    calc |Ut x - cylinderMean U 0 1|
        ≤ |Ut x - cylinderMean U x (1 / 8)| + |cylinderMean U x (1 / 8) - cylinderMean U 0 1| :=
          abs_sub_le _ _ _
      _ ≤ KC * (Real.sqrt C₃ * Real.sqrt E1) * (1 / 8 : ℝ) ^ a' +
            Real.sqrt 16384 * Real.sqrt E1 := add_le_add htail hmean
      _ = (KC * Real.sqrt C₃ * (1 / 8 : ℝ) ^ a' + Real.sqrt 16384) * Real.sqrt E1 := by ring
  -- excess bounded by any constant
  have hE1c : ∀ c : ℝ, Real.sqrt E1 ≤ Real.sqrt (⨍ p in openCyl 0 1, (U p - c) ^ 2) := by
    intro c
    apply Real.sqrt_le_sqrt
    have h := cylinderExcess_le U 0 one_pos (by rw [← restrict_openCyl_eq]; exact hU.1) c
    simpa only [setAverage_eq, measureReal_def, restrict_openCyl_eq] using h
  refine ⟨Ut, hcont, hae, ?_, ?_⟩
  · -- top trace
    have hprod : (volume.restrict (cylinder (0 : ℝ × Vec 2) (1 / 2))) =
        (volume.restrict (Set.Ioc (-(1 / 4) : ℝ) 0)).prod
          (volume.restrict (euclidBall (0 : Vec 2) (1 / 2))) := by
      rw [cylinder_half_prod, Measure.volume_eq_prod, Measure.prod_restrict]
    have hae' : ∀ᵐ z ∂(volume.restrict (cylinder (0 : ℝ × Vec 2) (1 / 2))), Ut z = U z := hae
    rw [hprod] at hae'
    have hslice := Measure.ae_ae_of_ae_prod hae'
    set V := (volume (euclidBall (0 : Vec 2) (1 / 2))).toReal
    set g : ℝ → ℝ := fun τ => V * (KH * Real.sqrt M) ^ 2 * |τ| ^ a'
    have hg : Tendsto g (𝓝[<] 0 ⊓ ae volume) (𝓝 0) := by
      have hc : Continuous g := by
        simp only [g]
        exact continuous_const.mul (continuous_abs.rpow_const fun _ => Or.inr ha₀.le)
      have h0 : g 0 = 0 := by simp [g, Real.zero_rpow ha₀.ne']
      have := hc.tendsto 0
      rw [h0] at this
      exact this.mono_left (inf_le_left.trans nhdsWithin_le_nhds)
    refine squeeze_zero' (Eventually.of_forall fun τ => setIntegral_nonneg_of_ae_restrict
      (Eventually.of_forall fun _ => sq_nonneg _)) ?_ hg
    have hgood : {τ : ℝ | τ ∈ Set.Ioc (-(1 / 4) : ℝ) 0 → ∀ᵐ y ∂(volume.restrict
        (euclidBall (0 : Vec 2) (1 / 2))), Ut (τ, y) = U (τ, y)} ∈ ae volume :=
      (ae_restrict_iff' measurableSet_Ioc).1 hslice
    have hnear : Set.Ioo (-(1 / 4) : ℝ) 0 ∈ 𝓝[<] (0 : ℝ) :=
      Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [Filter.inter_mem_inf hnear hgood] with τ ⟨hτ, hτg⟩
    have hτ' : τ ∈ Set.Ioc (-(1 / 4) : ℝ) 0 := ⟨hτ.1, hτ.2.le⟩
    have heq := hτg hτ'
    have hint : ∫ y in euclidBall 0 (1 / 2), (U (τ, y) - Ut (0, y)) ^ 2 =
        ∫ y in euclidBall 0 (1 / 2), (Ut (τ, y) - Ut (0, y)) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [heq] with y hy
      rw [hy]
    rw [hint]
    have hball : ∀ y ∈ euclidBall (0 : Vec 2) (1 / 2),
        (Ut (τ, y) - Ut (0, y)) ^ 2 ≤ (KH * Real.sqrt M) ^ 2 * |τ| ^ a' := by
      intro y hy
      have hz : ((τ, y) : ℝ × Vec 2) ∈ halfWindow (0 : ℝ × Vec 2) := by
        refine ⟨⟨?_, hτ'.2⟩, hy⟩
        simp only [Prod.fst_zero]; norm_num; linarith [hτ'.1]
      have hw : ((0, y) : ℝ × Vec 2) ∈ halfWindow (0 : ℝ × Vec 2) := by
        refine ⟨⟨by norm_num, le_rfl⟩, hy⟩
      have hh := hhold _ hz _ hw
      have hdist : parabolicHolderDistance (τ, y) (0, y) = Real.sqrt |τ| := by
        simp [parabolicHolderDistance, vecNormSq, vecDot]
      rw [hdist] at hh
      have hsq : (Real.sqrt |τ|) ^ a' = (|τ| ^ a') ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg τ), ← Real.rpow_mul (abs_nonneg τ)]
        ring_nf
      have hbd : |Ut (τ, y) - Ut (0, y)| ≤ KH * Real.sqrt M * Real.sqrt (|τ| ^ a') := by
        rw [Real.sqrt_eq_rpow (|τ| ^ a'), ← hsq]; exact hh
      calc (Ut (τ, y) - Ut (0, y)) ^ 2 = |Ut (τ, y) - Ut (0, y)| ^ 2 := (sq_abs _).symm
        _ ≤ (KH * Real.sqrt M * Real.sqrt (|τ| ^ a')) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hbd 2
        _ = (KH * Real.sqrt M) ^ 2 * |τ| ^ a' := by
            rw [mul_pow, Real.sq_sqrt (Real.rpow_nonneg (abs_nonneg τ) _)]
    have hfinB : IsFiniteMeasure (volume.restrict (euclidBall (0 : Vec 2) (1 / 2))) :=
      isFiniteMeasure_restrict.mpr (euclidBall_volume_ne_top 0 _)
    calc ∫ y in euclidBall 0 (1 / 2), (Ut (τ, y) - Ut (0, y)) ^ 2
        ≤ ∫ _y in euclidBall (0 : Vec 2) (1 / 2), (KH * Real.sqrt M) ^ 2 * |τ| ^ a' :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
            (integrable_const _)
            ((ae_restrict_iff' (External.Campanato.euclidBall_measurable 0 _)).2
              (Eventually.of_forall hball))
      _ = g τ := by
          rw [setIntegral_const, smul_eq_mul]
          simp only [g, V, measureReal_def]
          ring
  · -- Hölder plus amplitude
    intro c x hx z hz w hw hzw
    have hδ : 0 < parabolicHolderDistance z w := by
      have h1 := parabolicDist_le_parabolicHolderDistance z w
      have h2 : 0 < parabolicDist z w := by
        rcases lt_or_eq_of_le (parabolicDist_nonneg z w) with h | h
        · exact h
        · exact absurd ((parabolicDist_eq_zero_iff).1 h.symm) hzw
      linarith
    have hδa : 0 < parabolicHolderDistance z w ^ a' := Real.rpow_pos_of_pos hδ _
    have hh := hhold z hz w hw
    have hquot : |Ut z - Ut w| / parabolicHolderDistance z w ^ a' ≤
        KH * Real.sqrt C₃ * Real.sqrt E1 := by
      rw [div_le_iff₀ hδa]
      calc |Ut z - Ut w| ≤ KH * Real.sqrt M * parabolicHolderDistance z w ^ a' := hh
        _ = KH * Real.sqrt C₃ * Real.sqrt E1 * parabolicHolderDistance z w ^ a' := by
            rw [show M = C₃ * E1 from rfl, Real.sqrt_mul hC₃]; ring
    have hampx := hamp x hx
    have hsE := hE1c c
    have hsE0 : 0 ≤ Real.sqrt E1 := Real.sqrt_nonneg _
    calc |Ut z - Ut w| / parabolicHolderDistance z w ^ a' + |Ut x - cylinderMean U 0 1|
        ≤ KH * Real.sqrt C₃ * Real.sqrt E1 +
            (KC * Real.sqrt C₃ * (1 / 8 : ℝ) ^ a' + Real.sqrt 16384) * Real.sqrt E1 :=
          add_le_add hquot hampx
      _ = C * Real.sqrt E1 := by simp only [C]; ring
      _ ≤ C * Real.sqrt (⨍ p in openCyl 0 1, (U p - c) ^ 2) :=
          mul_le_mul_of_nonneg_left hsE (by positivity)

end AVRegularity.Applications
end
end
end
end

section
@[expose] public section
namespace AVRegularity.Applications

/-! # The microscopic oscillation lemma, unconditionally

The flux form and the Caccioppoli inequality (`AVRegularity.Applications.Construction`)
discharge the two statements used by the Campanato assembly. -/

theorem skewDriftFluxStmt_holds : SkewDriftFluxStmt := by
  intro K d U DU kK kd hcoef hdiv hU hw c φ hφ
  exact skewDrift_flux_form hcoef.1 hcoef.2.1 hcoef.2.2 hdiv hU hw c φ hφ

theorem skewDriftCaccioppoliStmt_holds : SkewDriftCaccioppoliStmt := by
  obtain ⟨C₀, hC₀, h⟩ := skewDrift_caccioppoli
  exact ⟨C₀, hC₀, fun K d U DU kK kd hkK hkd hs hcoef hskew hdiv hU hw c =>
    h K d U DU kK kd hkK hkd hs hcoef.1 hcoef.2.1 hskew hcoef.2.2 hdiv hU hw c⟩

/-- **Microscopic oscillation**. Lemma 3.3 of the paper follows from it. -/
theorem ocMicroscopicStatement_holds : OcMicroscopicStatement :=
  oc_microscopic_of_tools skewDriftFluxStmt_holds skewDriftCaccioppoliStmt_holds

end AVRegularity.Applications
end
end
