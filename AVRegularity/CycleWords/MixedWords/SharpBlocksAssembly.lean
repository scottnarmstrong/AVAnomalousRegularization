-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.AmplitudeIdWeakProduct
import AVRegularity.Construction.FastProfile.Integral
import AVRegularity.CycleJoint.PointwiseMolecularMaterialSampleBudget
import AVRegularity.CycleEvolution.CellLimitMoments
public import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
import AVRegularity.CycleJoint.PlaneImageJetMomentNorm
import AVRegularity.CycleWords.MixedWords.TransformBoundSchur
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleJointProofs AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords.Assembly

/-! Transfer and assembly of the actual forced moment fibre. -/

private theorem amplitudeId_radial_endpoint_pairing
    (X : PlaneHk Set.univ 0 ℂ) (U : TorusHk 0 ℂ)
    (hm : MemLp (fun y => (1 + ‖y‖) ^ 4 • X.toFunction.jet (valueIndex2 0) y) 2 volume)
    (hr : U.toFunction.jet (valueIndex2 0) =ᵐ[volume]
      periodizeRawJet X.toFunction.jet (valueIndex2 0))
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Z : TorusHk 1 ℂ) :
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 Z
    Summable (fun n : Fin 2 → ℤ => ∫ y,
      inner ℝ ((planeCarrierTranslation 0 (AVenhance.latticeShift n) X).toFunction.jet (valueIndex2 0) y)
        (ψ.toFunction.jet (valueIndex2 1) y)) ∧
      (∑' n : Fin 2 → ℤ, ∫ y,
        inner ℝ ((planeCarrierTranslation 0 (AVenhance.latticeShift n) X).toFunction.jet (valueIndex2 0) y)
          (ψ.toFunction.jet (valueIndex2 1) y)) =
        ∫ y, inner ℝ (U.toFunction.jet (valueIndex2 0) y) (ψ.toFunction.jet (valueIndex2 1) y) := by
  dsimp only
  let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 Z
  let M := (eLpNorm (fun y => (1 + ‖y‖) ^ 4 • X.toFunction.jet (valueIndex2 0) y) 2 volume).toReal
  have hb : eLpNorm (fun y => (1 + ‖y - (0 : Vec 2)‖) ^ 4 •
      X.toFunction.jet (valueIndex2 0) y) 2 volume ≤ ENNReal.ofReal M := by
    simp only [sub_zero]
    rw [ENNReal.ofReal_toReal hm.eLpNorm_ne_top]
  have hs := planeImageJetCLM_radial_enorm_tsum_lt_top (Metric.ball (0 : Vec 2) 2) 2
    (by norm_num) Set.Subset.rfl 0 (valueIndex2 0) X M ENNReal.toReal_nonneg
    (by simpa only [sub_zero] using hm.aestronglyMeasurable) hb
  have hψ := unitPatchLocalization_jet_ball_support_ae hζ 1 Z (valueIndex2 1)
  refine ⟨translated_compact_jet_pairing_summable _ X _ ψ _ hψ hs, ?_⟩
  refine (summed_compact_jet_pairing _ X _ ψ _ hψ hs).trans (integral_congr_ae ?_)
  filter_upwards [hr] with y hy
  rw [hy]

/-- One radial plane atom has the full compact spacetime transfer, including genuine
integrability on both sides and the absolute integer-image time budget. -/
theorem amplitudeId_radial_atom_transfer {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (f : ℝ → Vec 2 → ℂ)
    (P : AmplitudeIdPlaneRadialCurve (volume.restrict (Icc a b)) f)
    (U : ℝ → TorusHk 0 ℂ)
    (hU : ∀ᵐ r ∂volume.restrict (Icc a b),
      (U r).toFunction.jet (valueIndex2 0) =ᵐ[volume]
        periodizeRawJet (P.value r).toFunction.jet (valueIndex2 0))
    (c : ℝ) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Z : TorusHk 1 ℂ) (α : JetIndex2 1) :
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 Z
    let A := fun (n : Fin 2 → ℤ) r => ∫ y,
      inner ℝ (c • (planeCarrierTranslation 0 (AVenhance.latticeShift n) (P.value r)).toFunction.jet
        (valueIndex2 0) y) (ψ.toFunction.jet α y)
    let B := fun r => ∫ y,
      inner ℝ (c • (U r).toFunction.jet (valueIndex2 0) y) (ψ.toFunction.jet α y)
    (∀ n, IntegrableOn (A n) (Ioc s t)) ∧
      Summable (fun n => ∫ r in Ioc s t, ‖A n r‖) ∧
      IntegrableOn B (Ioc s t) ∧
      (∑' n, ∫ r in Ioc s t, A n r) = ∫ r in Ioc s t, B r := by
  let μ := volume.restrict (Ioc s t)
  have hsub : Ioc s t ⊆ Icc a b := fun r hr => ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
  have hμ : μ ≤ volume.restrict (Icc a b) := Measure.restrict_mono_set volume hsub
  let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 Z
  let C := fun (_ : ℝ) (_ : Vec 2) => c • ContinuousLinearMap.id ℝ ℂ
  have hc (r : ℝ) : Continuous (C r) := continuous_const
  have hj : Measurable (Function.uncurry C) := measurable_const
  have hb (r : ℝ) (y : Vec 2) : ‖C r y‖ ≤ |c| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left
      (show ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 from ContinuousLinearMap.norm_id_le)
      (abs_nonneg c)).trans_eq (mul_one _)
  obtain ⟨M, hM, hbudget⟩ := P.budget
  have hw : ∀ᵐ r ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - (0 : Vec 2)‖) ^ 4 • (P.value r).toFunction.jet (valueIndex2 0) y) volume :=
    (ae_restrict_of_ae_restrict_of_subset hsub hbudget).mono (fun _ hr => by
      simpa only [sub_zero] using hr.1)
  have hbound : ∀ᵐ r ∂μ, eLpNorm
      (fun y => (1 + ‖y - (0 : Vec 2)‖) ^ 4 • (P.value r).toFunction.jet (valueIndex2 0) y) 2 volume ≤
        ENNReal.ofReal ‖M r‖ :=
    (ae_restrict_of_ae_restrict_of_subset hsub hbudget).mono (fun _ hr => by
      simpa only [sub_zero] using hr.2)
  have hψ := unitPatchLocalization_jet_ball_support_ae hζ 1 Z α
  have hi := fun n : Fin 2 → ℤ => translated_coefficient_pairing_time_integrable μ
    C hc hj |c| (abs_nonneg _) hb P.value (P.mem.mono_measure hμ)
      (AVenhance.latticeShift n) (valueIndex2 0) ψ α
  have hsum := translated_coefficient_pairing_time_summable μ (Metric.ball (0 : Vec 2) 2)
    2 (by norm_num) Set.Subset.rfl C hc hj |c| (abs_nonneg _) hb
    P.value (P.mem.mono_measure hμ) 0 (valueIndex2 0) ψ α hψ M (hM.mono_measure hμ) hw hbound
  have he := translated_coefficient_pairing_spacetime_transfer μ (Metric.ball (0 : Vec 2) 2)
    2 (by norm_num) Set.Subset.rfl C hc hj |c| (abs_nonneg _) hb
    P.value (P.mem.mono_measure hμ) 0 (valueIndex2 0) ψ α hψ M (hM.mono_measure hμ) hw hbound
  have hp := periodized_coefficient_pairing_time_integrable μ (Metric.ball (0 : Vec 2) 2)
    2 (by norm_num) Set.Subset.rfl C hc hj |c| (abs_nonneg _) hb
    P.value (P.mem.mono_measure hμ) 0 (valueIndex2 0) ψ α hψ M (hM.mono_measure hμ) hw hbound
  have hread : (fun r => ∫ y, inner ℝ (C r y
      (periodizeRawJet (P.value r).toFunction.jet (valueIndex2 0) y)) (ψ.toFunction.jet α y)) =ᵐ[μ]
      fun r => ∫ y, inner ℝ (c • (U r).toFunction.jet (valueIndex2 0) y) (ψ.toFunction.jet α y) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hU] with r hr
    apply integral_congr_ae
    filter_upwards [hr] with y hy
    rw [hy]
    rfl
  dsimp only
  exact ⟨hi, hsum, hp.congr hread, he.trans (integral_congr_ae hread)⟩

/-- A genuine radial plane source/flux balance yields the periodic cell balance.
The image premise is the plane equation tested by the translated compact cell test. -/
theorem amplitudeId_radial_balance_periodizes {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (Xs Xt : PlaneHk Set.univ 0 ℂ) (Us Ut : TorusHk 0 ℂ)
    (hXs : MemLp (fun y => (1 + ‖y‖) ^ 4 • Xs.toFunction.jet (valueIndex2 0) y) 2 volume)
    (hXt : MemLp (fun y => (1 + ‖y‖) ^ 4 • Xt.toFunction.jet (valueIndex2 0) y) 2 volume)
    (hUs : Us.toFunction.jet (valueIndex2 0) =ᵐ[volume]
      periodizeRawJet Xs.toFunction.jet (valueIndex2 0))
    (hUt : Ut.toFunction.jet (valueIndex2 0) =ᵐ[volume]
      periodizeRawJet Xt.toFunction.jet (valueIndex2 0))
    (h : ℝ → Vec 2 → ℂ) (qv : Fin 2 → ℝ → Vec 2 → ℂ)
    (H : AmplitudeIdPlaneRadialCurve (volume.restrict (Icc a b)) h)
    (Q : ∀ i, AmplitudeIdPlaneRadialCurve (volume.restrict (Icc a b)) (qv i))
    (HT : ℝ → TorusHk 0 ℂ) (QT : Fin 2 → ℝ → TorusHk 0 ℂ)
    (hHT : ∀ᵐ r ∂volume.restrict (Icc a b), HT r |>.toFunction.jet (valueIndex2 0) =ᵐ[volume]
      periodizeRawJet (H.value r).toFunction.jet (valueIndex2 0))
    (hQT : ∀ i, ∀ᵐ r ∂volume.restrict (Icc a b), QT i r |>.toFunction.jet (valueIndex2 0) =ᵐ[volume]
      periodizeRawJet ((Q i).value r).toFunction.jet (valueIndex2 0))
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Z : TorusHk 1 ℂ)
    (himage : let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 Z
      ∀ n : Fin 2 → ℤ,
        (∫ y, inner ℝ ((planeCarrierTranslation 0 (AVenhance.latticeShift n) Xt).toFunction.jet
          (valueIndex2 0) y) (ψ.toFunction.jet (valueIndex2 1) y)) -
        (∫ y, inner ℝ ((planeCarrierTranslation 0 (AVenhance.latticeShift n) Xs).toFunction.jet
          (valueIndex2 0) y) (ψ.toFunction.jet (valueIndex2 1) y)) =
        ∫ r in Ioc s t,
          (∫ y, inner ℝ ((planeCarrierTranslation 0 (AVenhance.latticeShift n) (H.value r)).toFunction.jet
            (valueIndex2 0) y) (ψ.toFunction.jet (valueIndex2 1) y)) -
          ∑ i : Fin 2, ∫ y, inner ℝ
            ((planeCarrierTranslation 0 (AVenhance.latticeShift n) ((Q i).value r)).toFunction.jet
              (valueIndex2 0) y) (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y)) :
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) 0 s t (fun _ _ => 0)
      (Ut.toFunction.jet (valueIndex2 0)) (Us.toFunction.jet (valueIndex2 0))
      (Z.toFunction.jet (valueIndex2 1))
      (fun i => Z.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩)
      (fun _ _ _ => 0)
      (fun r y => WithLp.toLp 2 (fun i : Fin 2 => (QT i r).toFunction.jet (valueIndex2 0) y))
      (fun _ _ => 0) (fun r => (HT r).toFunction.jet (valueIndex2 0)) := by
  classical
  let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 Z
  let flux := fun r y => WithLp.toLp 2 (fun i : Fin 2 => (QT i r).toFunction.jet (valueIndex2 0) y)
  let src := fun r => (HT r).toFunction.jet (valueIndex2 0)
  let P : Option (Fin 2) → ℝ → PlaneHk Set.univ 0 ℂ :=
    fun j => j.elim H.value (fun i => (Q i).value)
  let R : Option (Fin 2) → ℝ → TorusHk 0 ℂ := fun j => j.elim HT QT
  let c : Option (Fin 2) → ℝ := fun j => j.elim 1 (fun _ => -1)
  let α : Option (Fin 2) → JetIndex2 1 :=
    fun j => j.elim (valueIndex2 1) (fun i => ⟨⟨1, by decide⟩, fun _ => i⟩)
  let A := fun j (n : Fin 2 → ℤ) r => ∫ y,
    inner ℝ (c j • (planeCarrierTranslation 0 (AVenhance.latticeShift n) (P j r)).toFunction.jet
      (valueIndex2 0) y) (ψ.toFunction.jet (α j) y)
  let B := fun j r => ∫ y,
    inner ℝ (c j • (R j r).toFunction.jet (valueIndex2 0) y) (ψ.toFunction.jet (α j) y)
  have htr (j : Option (Fin 2)) :
      (∀ n, IntegrableOn (A j n) (Ioc s t)) ∧
        Summable (fun n => ∫ r in Ioc s t, ‖A j n r‖) ∧
        IntegrableOn (B j) (Ioc s t) ∧
        (∑' n, ∫ r in Ioc s t, A j n r) = ∫ r in Ioc s t, B j r := by
    cases j with
    | none => exact amplitudeId_radial_atom_transfer hs ht h H HT hHT 1 hζ Z (valueIndex2 1)
    | some i =>
      exact amplitudeId_radial_atom_transfer hs ht (qv i) (Q i) (QT i) (hQT i) (-1)
        hζ Z ⟨⟨1, by decide⟩, fun _ => i⟩
  have hp (F : TorusHk 0 ℂ) := periodic_unitPatch_test_pairings_integrable
    (F.toFunction.jet (valueIndex2 0)) (periodicJetRepresentative_memL2 F.val _)
    (periodicJetRepresentative_periodic F.val _) hζ Z
  have hpoint (r : ℝ) : weakIdentityRhs 0 (fun _ _ => 0)
      (ψ.toFunction.jet (valueIndex2 1)) (fun i => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩)
      (fun _ _ _ => 0) flux (fun _ _ => 0) src r = fun y =>
        -(∑ i : Fin 2, inner ℝ ((QT i r).toFunction.jet (valueIndex2 0) y)
          (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y)) +
          inner ℝ ((HT r).toFunction.jet (valueIndex2 0) y) (ψ.toFunction.jet (valueIndex2 1) y) := by
    funext y
    simp only [weakIdentityRhs, flux, src, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      neg_zero, zero_sub, PiLp.zero_apply, add_zero]
  have hir (r : ℝ) : Integrable (weakIdentityRhs 0 (fun _ _ => 0)
      (ψ.toFunction.jet (valueIndex2 1)) (fun i => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩)
      (fun _ _ _ => 0) flux (fun _ _ => 0) src r) volume := by
    rw [hpoint]
    exact (integrable_finsetSum Finset.univ (fun i _ => (hp (QT i r)).2 i)).neg.add (hp (HT r)).1
  have hr (r : ℝ) : (∫ y, weakIdentityRhs 0 (fun _ _ => 0)
      (ψ.toFunction.jet (valueIndex2 1)) (fun i => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩)
      (fun _ _ _ => 0) flux (fun _ _ => 0) src r y) = ∑ j : Option (Fin 2), B j r := by
    have hh : Integrable (fun y => inner ℝ ((HT r).toFunction.jet (valueIndex2 0) y)
        (ψ.toFunction.jet (valueIndex2 1) y)) volume := (hp (HT r)).1
    have hq (i : Fin 2) : Integrable (fun y =>
        inner ℝ ((QT i r).toFunction.jet (valueIndex2 0) y)
          (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y)) volume := (hp (QT i r)).2 i
    rw [hpoint]
    have hn : Integrable (fun y => -(∑ i : Fin 2, inner ℝ
        ((QT i r).toFunction.jet (valueIndex2 0) y)
        (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y))) volume := by
      exact (integrable_finsetSum Finset.univ (fun i _ => hq i)).neg.congr
        (Filter.Eventually.of_forall (fun y => rfl))
    rw [integral_add hn hh, integral_neg,
      integral_finsetSum Finset.univ (fun i _ => hq i)]
    simp only [B, R, c, α, Fintype.sum_option, Option.elim_none, Option.elim_some,
      one_smul, neg_one_smul, inner_neg_left, integral_neg, Finset.sum_neg_distrib]
    ring
  have he (n : Fin 2 → ℤ) :
      (∫ y, inner ℝ ((planeCarrierTranslation 0 (AVenhance.latticeShift n) Xt).toFunction.jet
        (valueIndex2 0) y) (ψ.toFunction.jet (valueIndex2 1) y)) -
      (∫ y, inner ℝ ((planeCarrierTranslation 0 (AVenhance.latticeShift n) Xs).toFunction.jet
        (valueIndex2 0) y) (ψ.toFunction.jet (valueIndex2 1) y)) =
      ∫ r in Ioc s t, ∑ j : Option (Fin 2), A j n r := by
    convert himage n using 1
    congr 1
    funext r
    simp only [A, P, c, α, Fintype.sum_option, Option.elim_none, Option.elim_some,
      one_smul, neg_one_smul, inner_neg_left, integral_neg, Finset.sum_neg_distrib]
    ring
  obtain ⟨hsum, hsread⟩ := amplitudeId_radial_endpoint_pairing Xs Us hXs hUs hζ Z
  obtain ⟨htsum, htread⟩ := amplitudeId_radial_endpoint_pairing Xt Ut hXt hUt hζ Z
  have hlocal := coupledWeakIdentity_integral_image_assembly volume 0 s t (fun _ _ => 0)
    (Ut.toFunction.jet (valueIndex2 0)) (Us.toFunction.jet (valueIndex2 0))
    (ψ.toFunction.jet (valueIndex2 1)) (fun i => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩)
    (fun _ _ _ => 0) flux (fun _ _ => 0) src (hp Ut).1 (hp Us).1 (fun r _ => hir r)
    Finset.univ _ _ htsum hsum htread hsread A
    (fun j _ => (htr j).1) (fun j _ => (htr j).2.1) he B
    (fun j _ => (htr j).2.2.1) (fun j _ => (htr j).2.2.2)
    (Filter.Eventually.of_forall hr)
  have hlocal' := coupledWeakIdentity_test_congr volume 0 s t (fun _ _ => 0)
    (Ut.toFunction.jet (valueIndex2 0)) (Us.toFunction.jet (valueIndex2 0))
    (ψ.toFunction.jet (valueIndex2 1))
    (fun y => spatialPatchCutoff ζ 1 0 y • Z.toFunction.jet (valueIndex2 1) y)
    (fun i => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩)
    (fun i y => fderiv ℝ (spatialPatchCutoff ζ 1 0) y (basisVec i) •
      Z.toFunction.jet (valueIndex2 1) y +
      spatialPatchCutoff ζ 1 0 y • Z.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y)
    (fun _ _ _ => 0) flux (fun _ _ => 0) src
    (spatialPatchLocalization_value_ae hζ 1 (by norm_num) 0 Z)
    (fun i => spatialPatchLocalization_gradient_ae hζ 1 (by norm_num) 0 Z i) hlocal
  exact periodic_cellL2_weakIdentity_transfer hζ 0 s t (fun _ _ => 0) _ _ _ _
    (fun _ _ _ => 0) flux (fun _ _ => 0) src
    (periodicJetRepresentative_memL2 Ut.val _) (periodicJetRepresentative_memL2 Us.val _)
    (periodicJetRepresentative_memL2 Z.val _) (fun _ => periodicJetRepresentative_memL2 Z.val _)
    (periodicJetRepresentative_periodic Ut.val _) (periodicJetRepresentative_periodic Us.val _)
    (periodicJetRepresentative_periodic Z.val _) (fun _ => periodicJetRepresentative_periodic Z.val _)
    (fun _ _ => continuous_const) (fun _ _ => ⟨0, le_rfl, fun _ => by simp⟩)
    (fun _ _ _ _ => rfl) (fun _ _ _ => MemLp.zero')
    (fun r _ i => periodicJetRepresentative_memL2 (QT i r).val _)
    (fun _ _ _ => MemLp.zero') (fun r _ => periodicJetRepresentative_memL2 (HT r).val _)
    (fun _ _ _ _ _ => rfl)
    (fun r _ n y => by ext i; exact periodicJetRepresentative_periodic (QT i r).val _ n y)
    (fun _ _ _ _ => rfl) (fun r _ => periodicJetRepresentative_periodic (HT r).val _) hlocal'

/-- The translated cutoff and conjugate periodic test are precisely the translated
conjugate compact test, at both value and gradient order. -/
theorem amplitudeId_translated_conjugate_test {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (Z : TorusHk 1 ℂ) (n : Fin 2 → ℤ) :
    let q := spatialPatchCutoff ζ 1 0
    let z := AVenhance.latticeShift n
    let Zc := KernelEnergy.mapTorusHk Complex.conjCLE.toContinuousLinearMap Z
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 Z
    (∀ᵐ y ∂volume, (q (y - z) : ℂ) * Zc.toFunction.jet (valueIndex2 1) y =
      star (ψ.toFunction.jet (valueIndex2 1) (y - z))) ∧
    ∀ i : Fin 2, ∀ᵐ y ∂volume,
      (q (y - z) : ℂ) * Zc.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y +
        (fderiv ℝ (fun x => q (x - z)) y (basisVec i) : ℂ) *
          Zc.toFunction.jet (valueIndex2 1) y =
      star (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ (y - z)) := by
  dsimp only
  let q := spatialPatchCutoff ζ 1 0
  let z := AVenhance.latticeShift n
  let Zc := KernelEnergy.mapTorusHk Complex.conjCLE.toContinuousLinearMap Z
  let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 Z
  have hc (a : JetIndex2 1) : Zc.toFunction.jet a =ᵐ[volume]
      fun y => star (Z.toFunction.jet a y) := by
    apply periodic_ae_eq_global _ _ (periodicJetRepresentative_periodic Zc.val a)
      (fun k y => congrArg star (periodicJetRepresentative_periodic Z.val a k y))
    exact KernelEnergy.mapTorusHk_toFunction_jet_ae Complex.conjCLE.toContinuousLinearMap Z a
  have hper (a : JetIndex2 1) (y : Vec 2) :
      Z.toFunction.jet a y = Z.toFunction.jet a (y - z) := by
    have hn : AVenhance.latticeShift (-n) = -z := by
      funext i
      simp only [AVenhance.latticeShift, Pi.neg_apply, Int.cast_neg, z]
    have h := periodicJetRepresentative_periodic Z.val a (-n) y
    rw [hn, ← sub_eq_add_neg] at h
    exact h.symm
  have hmp := (measurePreserving_add_right (volume : Measure (Vec 2)) (-z)).quasiMeasurePreserving
  have hv := hmp.ae_eq_comp (spatialPatchLocalization_value_ae hζ 1 (by norm_num) 0 Z)
  have hd (i : Fin 2) := hmp.ae_eq_comp
    (spatialPatchLocalization_gradient_ae hζ 1 (by norm_num) 0 Z i)
  constructor
  · filter_upwards [hc (valueIndex2 1), hv] with y hcy hvy
    change _ = star (ψ.toFunction.jet (valueIndex2 1) (y - z))
    change ψ.toFunction.jet (valueIndex2 1) (y + -z) = _ at hvy
    dsimp only [Function.comp_def] at hvy
    rw [← sub_eq_add_neg] at hvy
    rw [hvy, hcy, hper (valueIndex2 1) y]
    simp only [Complex.real_smul, Complex.star_def, map_mul, Complex.conj_ofReal]
    rfl
  · intro i
    filter_upwards [hc (valueIndex2 1), hc ⟨⟨1, by decide⟩, fun _ => i⟩, hd i]
      with y hcy hcdy hdy
    change _ = star (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ (y - z))
    change ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ (y + -z) = _ at hdy
    dsimp only [Function.comp_def] at hdy
    rw [← sub_eq_add_neg] at hdy
    rw [hdy, hcy, hcdy, hper (valueIndex2 1) y,
      hper ⟨⟨1, by decide⟩, fun _ => i⟩ y, fderiv_comp_sub]
    simp only [Complex.real_smul, Complex.star_def, map_add, map_mul, Complex.conj_ofReal]
    ring

/-- Translating a native plane atom is the same as translating its bilinear test. -/
theorem amplitudeId_translated_pair (X : PlaneHk Set.univ 0 ℂ)
    (ψ : PlaneHk Set.univ 1 ℂ) (α : JetIndex2 1) (z : Vec 2) :
    Integrable (fun y => X.toFunction.jet (valueIndex2 0) y *
      star (ψ.toFunction.jet α (y - z))) volume ∧
    (∫ y, X.toFunction.jet (valueIndex2 0) y * star (ψ.toFunction.jet α (y - z))).re =
      ∫ y, inner ℝ ((planeCarrierTranslation 0 z X).toFunction.jet (valueIndex2 0) y)
        (ψ.toFunction.jet α y) := by
  have hX : MemLp (X.toFunction.jet (valueIndex2 0)) 2 volume := by
    simpa only [Measure.restrict_univ] using X.toFunction.memL2 (valueIndex2 0)
  have hψ : MemLp (fun y => ψ.toFunction.jet α (y - z)) 2 volume := by
    have hψ : MemLp (ψ.toFunction.jet α) 2 volume := by
      simpa only [Measure.restrict_univ] using ψ.toFunction.memL2 α
    simpa only [Function.comp_def, sub_eq_add_neg] using
      hψ.comp_measurePreserving (measurePreserving_add_right volume (-z))
  have hi : Integrable (fun y => X.toFunction.jet (valueIndex2 0) y *
      star (ψ.toFunction.jet α (y - z))) volume :=
    (hX.integrable_mul hψ.star).congr (Filter.Eventually.of_forall (fun y => rfl))
  refine ⟨hi, ?_⟩
  change Complex.reCLM (∫ y, X.toFunction.jet (valueIndex2 0) y *
    star (ψ.toFunction.jet α (y - z))) = _
  rw [← Complex.reCLM.integral_comp_comm hi]
  calc
    _ = ∫ y, inner ℝ (X.toFunction.jet (valueIndex2 0) y) (ψ.toFunction.jet α (y - z)) := by
      congr 1
      funext y
      rw [real_inner_comm, Complex.inner]
      rfl
    _ = ∫ y, inner ℝ (X.toFunction.jet (valueIndex2 0) (y + z)) (ψ.toFunction.jet α y) := by
      symm
      simpa only [add_sub_cancel_right] using integral_add_right_eq_self
        (fun y => inner ℝ (X.toFunction.jet (valueIndex2 0) y) (ψ.toFunction.jet α (y - z))) z
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [planeCarrierTranslation_jet_ae z X (valueIndex2 0)] with y hy
      rw [hy]

/-- Ordinary divergence flux of one native phase-moment slice. -/
def amplitudeId_momentOrdinaryFlux (G : Matrix (Fin 2) (Fin 2) ℝ)
    (θ : Vec 2) (β : ℕ × ℕ) (W : PlaneHk Set.univ 1 ℝ) (S : PlaneFluxL2 ℝ)
    (i : Fin 2) (y : Vec 2) : ℂ :=
  amplitudeId_momentPlaneFlux G θ β W S i y +
    ∑ k : Fin 2, (G k i : ℂ) * amplitudeId_momentPlaneGradient θ β W k y

/-- Ordinary scalar source, including the frequency terms moved out of the divergence. -/
def amplitudeId_momentOrdinarySource (G : Matrix (Fin 2) (Fin 2) ℝ)
    (v : Vec 2 → Vec 2) (θ : Vec 2) (β : ℕ × ℕ)
    (W : PlaneHk Set.univ 1 ℝ) (S : PlaneFluxL2 ℝ) (y : Vec 2) : ℂ :=
  amplitudeId_momentPlaneSource G v θ β W S y +
    ∑ i : Fin 2, -(v y i : ℂ) * amplitudeId_momentPlaneGradient θ β W i y +
    ∑ i : Fin 2, Complex.I * (θ i : ℂ) * amplitudeId_momentOrdinaryFlux G θ β W S i y

/-- The real projection of the translated moment integrand consists of the actual
translated native source and flux atoms. -/
theorem amplitudeId_moment_image_rhs
    (G : Matrix (Fin 2) (Fin 2) ℝ) (v : Vec 2 → Vec 2) (θ : Vec 2) (β : ℕ × ℕ)
    (W : PlaneHk Set.univ 1 ℝ) (S : PlaneFluxL2 ℝ)
    (H : PlaneHk Set.univ 0 ℂ) (Q : Fin 2 → PlaneHk Set.univ 0 ℂ)
    (hH : H.toFunction.jet (valueIndex2 0) =ᵐ[volume]
      amplitudeId_momentOrdinarySource G v θ β W S)
    (hQ : ∀ i, (Q i).toFunction.jet (valueIndex2 0) =ᵐ[volume]
      amplitudeId_momentOrdinaryFlux G θ β W S i)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Z : TorusHk 1 ℂ) (n : Fin 2 → ℤ) :
    let q := spatialPatchCutoff ζ 1 0
    let z := AVenhance.latticeShift n
    let Zc := KernelEnergy.mapTorusHk Complex.conjCLE.toContinuousLinearMap Z
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 Z
    (∫ y, amplitudeId_momentWeakRhs G v θ (momentWeight β) W S Zc (fun x => q (x - z)) y).re =
      (∫ y, inner ℝ ((planeCarrierTranslation 0 z H).toFunction.jet (valueIndex2 0) y)
        (ψ.toFunction.jet (valueIndex2 1) y)) -
      ∑ i : Fin 2, ∫ y, inner ℝ ((planeCarrierTranslation 0 z (Q i)).toFunction.jet (valueIndex2 0) y)
        (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y) := by
  classical
  dsimp only
  let q := spatialPatchCutoff ζ 1 0
  let z := AVenhance.latticeShift n
  let Zc := KernelEnergy.mapTorusHk Complex.conjCLE.toContinuousLinearMap Z
  let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 Z
  obtain ⟨hc, hdc⟩ := amplitudeId_translated_conjugate_test hζ Z n
  have he : amplitudeId_momentWeakRhs G v θ (momentWeight β) W S Zc (fun x => q (x - z)) =ᵐ[volume]
      fun y => H.toFunction.jet (valueIndex2 0) y * star (ψ.toFunction.jet (valueIndex2 1) (y - z)) -
        ∑ i : Fin 2, (Q i).toFunction.jet (valueIndex2 0) y *
          star (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ (y - z)) := by
    filter_upwards [hH, ae_all_iff.mpr hQ, hc, ae_all_iff.mpr hdc] with y hHy hQy hcy hdcy
    rw [amplitudeId_moment_rhs_balance (fun _ => G) (fun _ => v) θ β (fun _ => W) (fun _ => S) Zc
      (fun x => q (x - z)) 0 y]
    change amplitudeId_momentOrdinarySource G v θ β W S y * (q (y - z) : ℂ) *
      Zc.toFunction.jet (valueIndex2 1) y -
      ∑ i, amplitudeId_momentOrdinaryFlux G θ β W S i y * _ = _
    rw [mul_assoc, ← hHy, hcy]
    apply congrArg₂ (· - ·) rfl
    apply Finset.sum_congr rfl
    intro i _
    rw [← hQy i, hdcy i]
  have hHpair := amplitudeId_translated_pair H ψ (valueIndex2 1) z
  have hQpair (i : Fin 2) := amplitudeId_translated_pair (Q i) ψ ⟨⟨1, by decide⟩, fun _ => i⟩ z
  rw [integral_congr_ae he, integral_sub hHpair.1
    (integrable_finsetSum Finset.univ (fun i _ => (hQpair i).1)),
    integral_finsetSum Finset.univ (fun i _ => (hQpair i).1), Complex.sub_re, Complex.re_sum,
    hHpair.2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (hQpair i).2

/-- The actual plane weak equation supplies every translated compact moment balance. -/
theorem amplitudeId_moment_image_increment {a b s t : ℝ}
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : ∀ r, (G r).IsSymm)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (C : ℝ) (hC : ∀ r i y, ‖cellDriftTorusSymbol v r i y‖ ≤ C)
    (u : ℝ → Lp ℝ 2 (volume : Measure (Vec 2)))
    (W : ℝ → PlaneHk Set.univ 1 ℝ) (S : ℝ → PlaneFluxL2 ℝ)
    (h : PlaneWeakHilbertCurve a b u W (fun r =>
      planeRealBlochGeneratorDual (G r) v hv r C (hC r) (W r) + planeSourceDual 0 (S r)))
    (θ : Vec 2) (β : ℕ × ℕ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (Xs Xt : PlaneHk Set.univ 0 ℂ)
    (hXs : Xs.toFunction.jet (valueIndex2 0) =ᵐ[volume]
      fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight β y * u s y : ℝ))
    (hXt : Xt.toFunction.jet (valueIndex2 0) =ᵐ[volume]
      fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight β y * u t y : ℝ))
    (H : AmplitudeIdPlaneRadialCurve (volume.restrict (Icc a b))
      (fun r => amplitudeId_momentOrdinarySource (G r) (v r) θ β (W r) (S r)))
    (Q : ∀ i, AmplitudeIdPlaneRadialCurve (volume.restrict (Icc a b))
      (fun r => amplitudeId_momentOrdinaryFlux (G r) θ β (W r) (S r) i))
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Z : TorusHk 1 ℂ) (n : Fin 2 → ℤ) :
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 Z
    let z := AVenhance.latticeShift n
    (∫ y, inner ℝ ((planeCarrierTranslation 0 z Xt).toFunction.jet (valueIndex2 0) y)
      (ψ.toFunction.jet (valueIndex2 1) y)) -
    (∫ y, inner ℝ ((planeCarrierTranslation 0 z Xs).toFunction.jet (valueIndex2 0) y)
      (ψ.toFunction.jet (valueIndex2 1) y)) =
    ∫ r in Ioc s t,
      (∫ y, inner ℝ ((planeCarrierTranslation 0 z (H.value r)).toFunction.jet (valueIndex2 0) y)
        (ψ.toFunction.jet (valueIndex2 1) y)) -
      ∑ i : Fin 2, ∫ y,
        inner ℝ ((planeCarrierTranslation 0 z ((Q i).value r)).toFunction.jet (valueIndex2 0) y)
          (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y) := by
  dsimp only
  let q := spatialPatchCutoff ζ 1 0
  let z := AVenhance.latticeShift n
  let qn := fun y => q (y - z)
  let Zc := KernelEnergy.mapTorusHk Complex.conjCLE.toContinuousLinearMap Z
  let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 Z
  have hqn : ContDiff ℝ (⊤ : ℕ∞) qn :=
    (spatialPatchCutoff_smooth hζ 1 0).comp (contDiff_id.sub contDiff_const)
  have hqc : HasCompactSupport qn := by
    simpa only [qn, q, Homeomorph.coe_addRight, Function.comp_def, sub_eq_add_neg] using
      (spatialPatchCutoff_compact hζ 1 (by norm_num) 0).comp_homeomorph (Homeomorph.addRight (-z))
  have he := amplitudeId_localized_moment_increment G hG v hv C hC u W S h θ
    (momentWeight β) qn (amplitudeId_moment_contDiff β) hqn hqc Zc hs ht hst
  have hi := amplitudeId_localized_moment_time_integrable G hG v hv C hC u W S h θ
    (momentWeight β) qn (amplitudeId_moment_contDiff β) hqn hqc Zc hs ht hst
  have hep (r : ℝ) (X : PlaneHk Set.univ 0 ℂ)
      (hx : X.toFunction.jet (valueIndex2 0) =ᵐ[volume]
        fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight β y * u r y : ℝ)) :
      (∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight β y * u r y : ℝ) *
        (qn y : ℂ) * Zc.toFunction.jet (valueIndex2 1) y).re =
      ∫ y, inner ℝ ((planeCarrierTranslation 0 z X).toFunction.jet (valueIndex2 0) y)
        (ψ.toFunction.jet (valueIndex2 1) y) := by
    refine (congrArg Complex.re (integral_congr_ae ?_)).trans
      (amplitudeId_translated_pair X ψ (valueIndex2 1) z).2
    filter_upwards [hx, (amplitudeId_translated_conjugate_test hζ Z n).1] with y hxy hzy
    rw [hxy, ← hzy]
    dsimp only [qn, q, z, Zc]
    ring
  have hre := congrArg Complex.re he
  rw [Complex.sub_re, hep t Xt hXt, hep s Xs hXs] at hre
  have hcomm := Complex.reCLM.intervalIntegral_comp_comm hi
  change (∫ r in s..t, (∫ y, amplitudeId_momentWeakRhs (G r) (v r) θ
    (momentWeight β) (W r) (S r) Zc qn y).re) =
    (∫ r in s..t, ∫ y, amplitudeId_momentWeakRhs (G r) (v r) θ
      (momentWeight β) (W r) (S r) Zc qn y).re at hcomm
  rw [← hcomm, intervalIntegral.integral_of_le hst] at hre
  refine hre.trans (integral_congr_ae ?_)
  have hsub : Ioc s t ⊆ Icc a b := fun r hr => ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub H.readout,
    ae_restrict_of_ae_restrict_of_subset hsub (ae_all_iff.mpr (fun i => (Q i).readout))]
      with r hHr hQr
  exact amplitudeId_moment_image_rhs (G r) (v r) θ β (W r) (S r) (H.value r)
    (fun i => (Q i).value r) hHr hQr hζ Z n

open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

/-- The covariant derivative of the native periodic state. -/
def amplitudeId_cellGradient (C : CellCoefficients) (W : TorusHk 1 ℂ) (i : Fin 2) (y : Vec 2) : ℂ :=
  W.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y +
    Complex.I * C.θ i * W.toFunction.jet (valueIndex2 1) y

/-- The ordinary flux associated with the actual cell generator and its forcing. -/
def amplitudeId_cellOrdinaryFlux (C : CellCoefficients) (r : ℝ) (W : TorusHk 1 ℂ)
    (F : Fin 2 → ComplexCellL2) (i : Fin 2) (y : Vec 2) : ℂ :=
  F i y + ∑ k : Fin 2, (C.G r y k i : ℂ) * amplitudeId_cellGradient C W k y

/-- The corresponding ordinary scalar source, including the frequency and potential. -/
def amplitudeId_cellOrdinarySource (C : CellCoefficients) (r : ℝ) (W : TorusHk 1 ℂ)
    (R : ComplexCellL2) (F : Fin 2 → ComplexCellL2) (y : Vec 2) : ℂ :=
  R y + ∑ i : Fin 2, -(C.v r y i : ℂ) * amplitudeId_cellGradient C W i y +
    ∑ i : Fin 2, Complex.I * C.θ i * amplitudeId_cellOrdinaryFlux C r W F i y +
    C.κ r * W.toFunction.jet (valueIndex2 1) y

/-- The ordinary periodic balance reads exactly the actual Riesz derivative of the fibre PDE. -/
theorem amplitudeId_cell_balance_pairing
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (r : ℝ) (W Z : TorusHk 1 ℂ) (R : ComplexCellL2) (F : Fin 2 → ComplexCellL2)
    (HT : TorusHk 0 ℂ) (QT : Fin 2 → TorusHk 0 ℂ)
    (hHT : HT.toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube]
      amplitudeId_cellOrdinarySource C r W R F)
    (hQT : ∀ i, (QT i).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube]
      amplitudeId_cellOrdinaryFlux C r W F i) :
    (∫ y in AVenhance.unitCube, weakIdentityRhs 0 (fun _ _ => 0)
      (Z.toFunction.jet (valueIndex2 1))
      (fun i => Z.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩) (fun _ _ _ => 0)
      (fun _ y => WithLp.toLp 2 (fun i : Fin 2 => (QT i).toFunction.jet (valueIndex2 0) y))
      (fun _ _ => 0) (fun _ => HT.toFunction.jet (valueIndex2 0)) r y) =
      inner ℝ (cellDualDerivative C hG V hv hb r W R F) Z := by
  let ψ := fun y => star (Z.toFunction.jet (valueIndex2 1) y)
  let dψ := fun i y => star (Z.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y)
  let flux := fun y => WithLp.toLp 2 (fun i : Fin 2 => F i y)
  have hu : (torusHkValueCLM W : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      W.toFunction.jet (valueIndex2 1) := (periodicJetRepresentative_ae W.val _).symm
  have hdu (i : Fin 2) : (cellDerivativeCLM i W : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      W.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ := (periodicJetRepresentative_ae W.val _).symm
  have hz : (torusHkValueCLM Z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] star ψ := by
    filter_upwards [(periodicJetRepresentative_ae Z.val (valueIndex2 1)).symm] with y hy
    change Z.val (valueIndex2 1) y = star (star (Z.toFunction.jet (valueIndex2 1) y))
    rw [star_star]
    exact hy
  have hdz (i : Fin 2) : (cellDerivativeCLM i Z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      star (dψ i) := by
    filter_upwards [(periodicJetRepresentative_ae Z.val ⟨⟨1, by decide⟩, fun _ => i⟩).symm] with y hy
    change Z.val ⟨⟨1, by decide⟩, fun _ => i⟩ y =
      star (star (Z.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y))
    rw [star_star]
    exact hy
  have hs := cellComplexSpatial_literal_ae C hG V hv hb r W Z R F
    (W.toFunction.jet (valueIndex2 1)) (fun i => W.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩)
    ψ dψ R flux hu hdu hz hdz Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
  have he : (fun y => weakIdentityRhs 0 (fun _ _ => 0)
      (Z.toFunction.jet (valueIndex2 1))
      (fun i => Z.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩) (fun _ _ _ => 0)
      (fun _ y => WithLp.toLp 2 (fun i : Fin 2 => (QT i).toFunction.jet (valueIndex2 0) y))
      (fun _ _ => 0) (fun _ => HT.toFunction.jet (valueIndex2 0)) r y) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => (cellComplexSpatial C hG V hv hb r W Z R F y).re := by
    filter_upwards [hHT, ae_all_iff.mpr hQT, hs] with y hHy hQy hsy
    rw [hsy]
    simp only [weakIdentityRhs, Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero,
      zero_sub, PiLp.zero_apply, add_zero, hHy, hQy, amplitudeId_cellOrdinarySource,
      amplitudeId_cellOrdinaryFlux, amplitudeId_cellGradient, cellLiteralRHS, ψ, dψ, flux,
      Fin.sum_univ_two, Complex.inner, Complex.star_def, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, add_zero, sub_zero]
    ring
  rw [integral_congr_ae he]
  have hcomm := Complex.reCLM.integral_comp_comm (cellComplexSpatial_integrable C hG V hv hb r W Z R F)
  change (∫ y in AVenhance.unitCube, (cellComplexSpatial C hG V hv hb r W Z R F y).re) =
    (∫ y in AVenhance.unitCube, cellComplexSpatial C hG V hv hb r W Z R F y).re at hcomm
  rw [hcomm]
  change (∫ y in AVenhance.unitCube, cellComplexSpatial C hG V hv hb r W Z R F y).re = _
  rw [cellComplexSpatial_integral, Complex.add_re, cellComplexGenerator_re,
    cellComplexSource_re, cellDualDerivative_pairing]

/-- Native Bochner forcing classes suffice for the public raw cell solution; joint
representatives are chosen and then removed by genuine almost-everywhere source congruence. -/
theorem amplitudeId_native_cell_exists_raw {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (R : ℝ → ComplexCellL2) (hR : MemLp R 2 (volume.restrict (Icc a b)))
    (Q : Fin 2 → ℝ → ComplexCellL2) (hQ : ∀ i, MemLp (Q i) 2 (volume.restrict (Icc a b)))
    (u : ℝ → ComplexCellL2) (W : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u W (fun r => cellDualDerivative C hG V hv hb r
      (W r) (R r) (fun i => Q i r))) :
    ∃ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Icc a b) C (fun r y => R r y)
        (fun r y => WithLp.toLp 2 (fun i : Fin 2 => Q i r y)) D ∧
      ∀ t, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t := by
  classical
  obtain ⟨src, hsrc, hsr⟩ := cellBochner_exists_joint_realization (Icc a b) R hR
  have hex (i : Fin 2) := cellBochner_exists_joint_realization (Icc a b) (Q i) (hQ i)
  choose flux hflux hfr using hex
  let F := fun r y => WithLp.toLp 2 (fun i : Fin 2 => flux i r y)
  have hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) :=
    memLp_piLp_iff.mpr (fun i => hflux i)
  have hrclass : ∀ᵐ r ∂volume.restrict (Icc a b), R r = cellSourceSlice src r := by
    filter_upwards [hsr, cellSource_memLp_slices (Icc a b) src hsrc] with r hr hm
    exact Lp.ext (hr.trans (cellSourceSlice_ae src r hm).symm)
  have hfclass (i : Fin 2) : ∀ᵐ r ∂volume.restrict (Icc a b),
      Q i r = cellSourceSlice (fun t y => F t y i) r := by
    filter_upwards [hfr i, cellSource_memLp_slices (Icc a b) (flux i) (hflux i)] with r hr hm
    exact Lp.ext (hr.trans (cellSourceSlice_ae (flux i) r hm).symm)
  have hw := h.dual_congr (show (fun r => cellDualDerivative C hG V hv hb r
      (W r) (R r) (fun i => Q i r)) =ᵐ[volume.restrict (Icc a b)]
      (fun r => cellDualDerivative C hG V hv hb r (W r) (cellSourceSlice src r)
        (fun i => cellSourceSlice (fun t y => F t y i) r)) from by
    filter_upwards [hrclass, ae_all_iff.mpr hfclass] with r hr hq
    rw [hr]
    exact congrArg (cellDualDerivative C hG V hv hb r (W r) (cellSourceSlice src r)) (funext hq))
  obtain ⟨D, hD, htrace⟩ := cellWeakHilbert_exists_raw_solution C hG V hv hb src F hsrc hF u W hw
  refine ⟨D, cellSolution_source_congr_sections (Icc a b) C src (fun r y => R r y)
    F (fun r y => WithLp.toLp 2 (fun i : Fin 2 => Q i r y)) D (hsr.mono (fun _ h => h.symm)) ?_ hD, htrace⟩
  filter_upwards [ae_all_iff.mpr hfr] with r hr
  filter_upwards [ae_all_iff.mpr hr] with y hy
  apply PiLp.ext
  intro i
  exact (hy i).symm

/-- The cell coefficients with the physical, radian frequency already normalized. -/
def amplitudeId_cellCoefficients (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (θ : Vec 2) : CellCoefficients :=
  ⟨fun t _ => G t, v, fun i => (θ i : ℂ), fun _ => 0⟩

/-- The plane balance and its periodic carriers, with both native and literal generator readouts. -/
structure AmplitudeIdBalanceData (a b : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (θ : Vec 2) (β : ℕ × ℕ)
    (W : ℝ → PlaneHk Set.univ 1 ℝ) (S : ℝ → PlaneFluxL2 ℝ)
    (Wc : ℝ → TorusHk 1 ℂ) (Rc : ℝ → ComplexCellL2) (Fc : Fin 2 → ℝ → ComplexCellL2) where
  H : AmplitudeIdPlaneRadialCurve (volume.restrict (Icc a b))
    (fun t => amplitudeId_momentOrdinarySource (G t) (v t) θ β (W t) (S t))
  Q : ∀ i, AmplitudeIdPlaneRadialCurve (volume.restrict (Icc a b))
    (fun t => amplitudeId_momentOrdinaryFlux (G t) θ β (W t) (S t) i)
  HT : ℝ → TorusHk 0 ℂ
  QT : Fin 2 → ℝ → TorusHk 0 ℂ
  source_raw : ∀ᵐ t ∂volume.restrict (Icc a b), (HT t).toFunction.jet (valueIndex2 0) =ᵐ[volume]
    periodizeRawJet (H.value t).toFunction.jet (valueIndex2 0)
  flux_raw : ∀ i, ∀ᵐ t ∂volume.restrict (Icc a b), (QT i t).toFunction.jet (valueIndex2 0) =ᵐ[volume]
    periodizeRawJet ((Q i).value t).toFunction.jet (valueIndex2 0)
  source_cell : ∀ᵐ t ∂volume.restrict (Icc a b),
    (HT t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube]
      amplitudeId_cellOrdinarySource (amplitudeId_cellCoefficients G v θ) t (Wc t) (Rc t) (fun i => Fc i t)
  flux_cell : ∀ i, ∀ᵐ t ∂volume.restrict (Icc a b),
    (QT i t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube]
      amplitudeId_cellOrdinaryFlux (amplitudeId_cellCoefficients G v θ) t (Wc t) (fun i => Fc i t) i

/-- Radial moment source and flux carriers produce the ordinary cell balance with the exact generator. -/
theorem amplitudeId_balance_data {a b : ℝ}
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hvs : ∀ t, Continuous (v t))
    (θ : Vec 2) (β : ℕ × ℕ) (W : ℝ → PlaneHk Set.univ 1 ℝ) (S : ℝ → PlaneFluxL2 ℝ)
    (PB : ∀ i, AmplitudeIdPlaneRadialCurve (volume.restrict (Icc a b))
      (fun t => amplitudeId_momentPlaneGradient θ β (W t) i))
    (PF : ∀ i, AmplitudeIdPlaneRadialCurve (volume.restrict (Icc a b))
      (fun t => amplitudeId_momentPlaneFlux (G t) θ β (W t) (S t) i))
    (PR : AmplitudeIdPlaneRadialCurve (volume.restrict (Icc a b))
      (fun t => amplitudeId_momentPlaneSource (G t) (v t) θ β (W t) (S t)))
    (Wc : ℝ → TorusHk 1 ℂ) (Rc : ℝ → ComplexCellL2) (Fc : Fin 2 → ℝ → ComplexCellL2)
    (hB : ∀ i, ∀ᵐ t ∂volume.restrict (Icc a b),
      amplitudeId_cellGradient (amplitudeId_cellCoefficients G v θ) (Wc t) i =ᵐ[volume.restrict AVenhance.unitCube]
        latticePeriodization (amplitudeId_momentPlaneGradient θ β (W t) i))
    (hF : ∀ i, ∀ᵐ t ∂volume.restrict (Icc a b), Fc i t =ᵐ[volume.restrict AVenhance.unitCube]
      latticePeriodization (amplitudeId_momentPlaneFlux (G t) θ β (W t) (S t) i))
    (hR : ∀ᵐ t ∂volume.restrict (Icc a b), Rc t =ᵐ[volume.restrict AVenhance.unitCube]
      latticePeriodization (amplitudeId_momentPlaneSource (G t) (v t) θ β (W t) (S t))) :
    Nonempty (AmplitudeIdBalanceData a b G v θ β W S Wc Rc Fc) := by
  classical
  let μ := volume.restrict (Icc a b)
  let B := fun i t => amplitudeId_momentPlaneGradient θ β (W t) i
  let F := fun i t => amplitudeId_momentPlaneFlux (G t) θ β (W t) (S t) i
  let R := fun t => amplitudeId_momentPlaneSource (G t) (v t) θ β (W t) (S t)
  let Bc := fun i t => amplitudeId_cellGradient (amplitudeId_cellCoefficients G v θ) (Wc t) i
  obtain ⟨hQ, ⟨H⟩⟩ := amplitudeId_covariant_balance_carriers μ G hG v hv hvs θ B F R PB PF PR
  let Q := fun i => Classical.choice (hQ i)
  obtain ⟨HT, _, hHT⟩ := amplitudeId_radial_cell_curve μ _ H
  have heQ (i : Fin 2) := amplitudeId_radial_cell_curve μ _ (Q i)
  choose QT _ hQT using heQ
  have hc := amplitudeId_covariant_cell_readouts μ G v hv.2.2.1 θ B F R PB PF PR Q
    Bc (fun i t y => Fc i t y) (fun t y => Rc t y) hB hF hR
    (fun i t => (QT i t).toFunction.jet (valueIndex2 0))
    (fun t => (HT t).toFunction.jet (valueIndex2 0))
    (fun i => (hQT i).mono (fun _ h => h.restrict)) (hHT.mono (fun _ h => h.restrict))
  refine ⟨⟨H, Q, HT, QT, ?_, ?_, ?_, ?_⟩⟩
  · filter_upwards [hHT, H.readout] with t ht hr
    exact ht.trans (amplitudeId_latticePeriodization_congr hr).symm
  · intro i
    filter_upwards [hQT i, (Q i).readout] with t ht hr
    exact ht.trans (amplitudeId_latticePeriodization_congr hr).symm
  · filter_upwards [hc.2] with t ht
    filter_upwards [ht] with y hy
    rw [hy]
    simp only [amplitudeId_covariantSource, amplitudeId_covariantFlux, amplitudeId_cellOrdinarySource,
      amplitudeId_cellOrdinaryFlux, amplitudeId_cellCoefficients, zero_mul, add_zero, Bc]
  · intro i
    exact hc.1 i

section WordBalance
universe u v
variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- The actual word coordinate provides the complete radial plane-to-cell balance data. -/
theorem amplitudeId_word_balance_data
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (θ : Vec 2) (β : ℕ × ℕ)
    (A : AmplitudeIdWordCellData F j x e θ β)
    (rS : ℝ) (hrS : 0 < rS)
    (V : ℝ → PlaneHk Set.univ (F.κ j x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hV : MemLp V 2 (volume.restrict (Icc F.a F.b)))
    (heV : ∀ n, (∫⁻ t in Icc F.a F.b,
      weightedFactorialNormSq n F.ϖ 0 rS (F.κ j x) (V t)) ≠ ⊤)
    (hVr : ∀ᵐ t ∂volume.restrict (Icc F.a F.b), planeValue (V t) =ᵐ[volume]
      fun y => wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ
        (fun p => F.w p.1 p.2 t) (j, x) t y) :
    Nonempty (AmplitudeIdBalanceData F.a F.b F.G F.v θ β
      (amplitudeId_wordCoordinateSlice F j x e)
      (fun t => planeFluxFiberCoordinateCLM e (planeFluxValueOperator (F.κ j x) (V t)))
      A.state A.scalar A.flux) := by
  classical
  let μ := volume.restrict (Icc F.a F.b)
  let W := amplitudeId_wordCoordinateSlice F j x e
  let S := fun t => planeFluxFiberCoordinateCLM e (planeFluxValueOperator (F.κ j x) (V t))
  obtain ⟨hM, hS⟩ := amplitudeId_wordCoordinate_plane_families F j x e θ rS hrS V hV heV
  let Mu := fun γ => Classical.choice (hM (valueIndex2 1) γ)
  let MS := fun i γ => Classical.choice (hS i γ)
  have hdu (i : Fin 2) (γ : ℕ × ℕ) : Nonempty (AmplitudeIdPlaneRadialCurve μ (fun t y =>
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        (momentWeight γ y * planeH1GradientOperator (W t) i y : ℝ))) := by
    let P := Classical.choice (hM ⟨⟨1, by decide⟩, fun _ => i⟩ γ)
    refine ⟨P.congr (Filter.Eventually.of_forall (fun t => ?_))⟩
    have hg : planeH1GradientOperator (W t) i =ᵐ[volume]
        (W t).toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ := univToPlane_ae _
    filter_upwards [hg] with y hy
    rw [hy]
  let Mdu := fun i γ => Classical.choice (hdu i γ)
  have hPB := amplitudeId_plane_moment_gradient μ θ β
    (fun t => (W t).toFunction.jet (valueIndex2 1))
    (fun i t => planeH1GradientOperator (W t) i) Mu Mdu
  let PB := fun i => Classical.choice (hPB i)
  obtain ⟨⟨PR⟩, hPF⟩ := amplitudeId_plane_moment_forcing μ F.G F.piece.hGm F.v F.piece.hv
    (fun t => (F.piece.hvs t).continuous) θ β
    (fun t => (W t).toFunction.jet (valueIndex2 1)) (fun i t => S t i) Mu MS
  let PF := fun i => Classical.choice (hPF i)
  have hr := A.forcing_readouts V hVr
  exact amplitudeId_balance_data F.G F.piece.hGm F.v F.piece.hv
    (fun t => (F.piece.hvs t).continuous) θ β W S PB PF PR A.state A.scalar A.flux
    (fun i => A.covariant_readout.mono (fun _ ht => ht i))
    (fun i => hr.mono (fun _ ht => ht.2 i)) (hr.mono (fun _ ht => ht.1))

/-- The order-zero carrier of the continuous cell trace has the global endpoint lattice readout. -/
theorem amplitudeId_word_endpoint_periodizes
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (θ : Vec 2) (β : ℕ × ℕ)
    (A : AmplitudeIdWordCellData F j x e θ β)
    (t : ℝ) (ht : t ∈ Icc F.a F.b)
    (X : PlaneHk Set.univ 0 ℂ)
    (hX : X.toFunction.jet (valueIndex2 0) =ᵐ[volume]
      fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        (momentWeight β y * inner ℝ e (planeValue (F.u j x t) y) : ℝ)) :
    (Construction.Preservation.FullLift.torusZeroCarrier (A.value t)).toFunction.jet
      (valueIndex2 0) =ᵐ[volume] periodizeRawJet X.toFunction.jet (valueIndex2 0) := by
  let U := Construction.Preservation.FullLift.torusZeroCarrier (A.value t)
  have hu : U.toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y)) :=
    (periodicJetRepresentative_ae U.val (valueIndex2 0)).trans (A.trace t ht)
  have hp := amplitudeId_latticePeriodization_congr hX
  have he : latticePeriodization (fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
      (momentWeight β y * inner ℝ e (planeValue (F.u j x t) y) : ℝ)) =
      planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y)) := rfl
  apply periodic_ae_eq_global _ _ (periodicJetRepresentative_periodic U.val (valueIndex2 0))
    (latticePeriodization_periodic _)
  exact hu.trans (by simpa only [he] using hp.restrict.symm)

private theorem amplitudeId_endpoint_pairing (u : ComplexCellL2) (Z : TorusHk 1 ℂ) :
    (∫ y in AVenhance.unitCube,
      inner ℝ ((Construction.Preservation.FullLift.torusZeroCarrier u).toFunction.jet (valueIndex2 0) y)
        (Z.toFunction.jet (valueIndex2 1) y)) = inner ℝ u (torusHkValueCLM Z) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [periodicJetRepresentative_ae
    (Construction.Preservation.FullLift.torusZeroCarrier u).val (valueIndex2 0),
    periodicJetRepresentative_ae Z.val (valueIndex2 1)] with y hu hz
  exact congrArg₂ (inner ℝ) hu hz

/-- The periodic moment trace satisfies the actual cell Hilbert weak equation. -/
theorem amplitudeId_word_cell_weak_curve
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (θ : Vec 2) (β : ℕ × ℕ)
    (A : AmplitudeIdWordCellData F j x e θ β)
    (V : ℝ → PlaneHk Set.univ (F.κ j x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (C : ℝ) (hC : ∀ t i z, ‖cellDriftTorusSymbol F.v t i z‖ ≤ C)
    (hw : PlaneWeakHilbertCurve F.a F.b (amplitudeId_wordCoordinateTrace F j x e)
      (amplitudeId_wordCoordinateSlice F j x e) (fun t =>
        planeRealBlochGeneratorDual (F.G t) F.v F.piece.hv t C (hC t)
          (amplitudeId_wordCoordinateSlice F j x e t) +
        planeSourceDual 0 (planeFluxFiberCoordinateCLM e (planeFluxValueOperator (F.κ j x) (V t)))))
    (B : AmplitudeIdBalanceData F.a F.b F.G F.v θ β (amplitudeId_wordCoordinateSlice F j x e)
      (fun t => planeFluxFiberCoordinateCLM e (planeFluxValueOperator (F.κ j x) (V t)))
      A.state A.scalar A.flux)
    (Vd : ℝ) (hb : ∀ t y, ∑ i, F.v t y i ^ 2 ≤ Vd ^ 2) :
    CellWeakHilbertCurve F.a F.b A.value A.state (fun r =>
      cellDualDerivative (amplitudeId_cellCoefficients F.G F.v θ) F.piece.hGm Vd
        F.piece.hv.1 hb r (A.state r) (A.scalar r) (fun i => A.flux i r)) := by
  let Cc := amplitudeId_cellCoefficients F.G F.v θ
  have hζ : IsFastProfile FastProfile.fastProfile :=
    ⟨FastProfile.contDiff_fastProfile, FastProfile.fastProfile_even, FastProfile.tsupport_fastProfile_subset,
      fun t => ⟨FastProfile.fastProfile_nonneg t, FastProfile.fastProfile_le_one t⟩,
      FastProfile.fastProfile_periodization, FastProfile.fastProfile_integral_sq⟩
  refine ⟨A.continuous, A.state_mem, ?_, A.agrees, ?_⟩
  · exact cellDualDerivative_memLp Cc F.piece.hGm Vd 0 F.piece.hv.1 hb
      measurable_const (fun _ => by simp only [Cc, amplitudeId_cellCoefficients, norm_zero, le_refl])
      A.state A.state_mem A.scalar A.scalar_mem (fun r i => A.flux i r) A.flux_mem
  · intro s hs t ht hst Z
    obtain ⟨Xs, hXs, hrXs⟩ := amplitudeId_word_endpoint_carrier F j x e θ β s hs
    obtain ⟨Xt, hXt, hrXt⟩ := amplitudeId_word_endpoint_carrier F j x e θ β t ht
    let Us := Construction.Preservation.FullLift.torusZeroCarrier (A.value s)
    let Ut := Construction.Preservation.FullLift.torusZeroCarrier (A.value t)
    have hxs : Xs.toFunction.jet (valueIndex2 0) =ᵐ[volume]
        (fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
          (momentWeight β y * amplitudeId_wordCoordinateTrace F j x e s y : ℝ)) := by
      filter_upwards [hXs, (amplitudeId_wordCoordinate_readouts F j x e s).1] with y hy hz
      rw [hy, hz]
    have hxt : Xt.toFunction.jet (valueIndex2 0) =ᵐ[volume]
        (fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
          (momentWeight β y * amplitudeId_wordCoordinateTrace F j x e t y : ℝ)) := by
      filter_upwards [hXt, (amplitudeId_wordCoordinate_readouts F j x e t).1] with y hy hz
      rw [hy, hz]
    have hi := amplitudeId_radial_balance_periodizes hs ht Xs Xt Us Ut hrXs hrXt
      (amplitudeId_word_endpoint_periodizes F j x e θ β A s hs Xs hXs)
      (amplitudeId_word_endpoint_periodizes F j x e θ β A t ht Xt hXt)
      _ _ B.H B.Q B.HT B.QT B.source_raw B.flux_raw hζ Z (fun n =>
        amplitudeId_moment_image_increment F.G (fun r => F.piece.hGm.2.2.1 r 0) F.v F.piece.hv
          C hC _ _ _ hw θ β hs ht hst Xs Xt hxs hxt B.H B.Q hζ Z n)
    have he := hi.2.2.2.2
    rw [amplitudeId_endpoint_pairing, amplitudeId_endpoint_pairing] at he
    rw [intervalIntegral.integral_of_le hst]
    refine he.trans (integral_congr_ae ?_)
    have hsub : Ioc s t ⊆ Icc F.a F.b := fun r hr => ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub B.source_cell,
      ae_restrict_of_ae_restrict_of_subset hsub (ae_all_iff.mpr B.flux_cell)] with r hR hF
    exact amplitudeId_cell_balance_pairing Cc F.piece.hGm Vd F.piece.hv.1 hb r
      (A.state r) Z (A.scalar r) (fun i => A.flux i r) (B.HT r) (fun i => B.QT i r) hR hF

/-- The physical fibre frequency induces precisely the radian cell shift. -/
theorem amplitudeId_fibreCoefficients_eq (η : ℝ) (hη : 0 < η)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (θ : Vec 2) :
    fibreCoefficients η G v (planeFibreFrequency η θ) (fun _ => 0) =
      amplitudeId_cellCoefficients G v θ := by
  have hs : (Real.sqrt η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hη).ne'
  simp only [fibreCoefficients, planeFibreFrequency, amplitudeId_cellCoefficients, neg_zero]
  congr 1
  funext i
  push_cast
  field_simp

/-- Every moment Bloch trace of the given word solves its literal forced cell problem. -/
theorem amplitudeIdFibres : AmplitudeIdFibresStatement.{u, v} := by
  intro K g₁ ι _ h _ _ _ _ _ _ D Nw F j x e θ β
  obtain ⟨A⟩ := amplitudeId_word_cell_data F j x e θ β
  obtain ⟨rS, hrS, V, hV, heV, hVr, C, _, hC, hw⟩ := amplitudeId_word_native_coordinate F j x e
  obtain ⟨B⟩ := amplitudeId_word_balance_data F j x e θ β A rS hrS V hV heV hVr
  obtain ⟨Vd, hb⟩ := F.piece.hv.2.1
  have hweak := amplitudeId_word_cell_weak_curve F j x e θ β A V C hC hw B Vd hb
  obtain ⟨Draw, hDraw, htrace⟩ := amplitudeId_native_cell_exists_raw
    (amplitudeId_cellCoefficients F.G F.v θ) F.piece.hGm Vd F.piece.hv.1 hb
    A.scalar A.scalar_mem A.flux A.flux_mem A.value A.state hweak
  refine ⟨Draw, ?_, fun t ht => (htrace t).symm.trans (A.trace t ht)⟩
  rw [amplitudeId_fibreCoefficients_eq F.η F.piece.hη]
  apply cellSolution_source_congr_sections (Icc F.a F.b)
    (amplitudeId_cellCoefficients F.G F.v θ) (fun r y => A.scalar r y)
    (fun r => planeBlochC θ (amplitudeId_wordMomentScalar F j x e β r))
    (fun r y => WithLp.toLp 2 (fun i : Fin 2 => A.flux i r y))
    (fun r y => WithLp.toLp 2 (fun i : Fin 2 =>
      planeBlochC θ (amplitudeId_wordMomentFlux F j x e β i r) y))
    Draw A.scalar_readout ?_ hDraw
  filter_upwards [ae_all_iff.mpr A.flux_readout] with r hr
  filter_upwards [ae_all_iff.mpr hr] with y hy
  exact PiLp.ext hy

/-- The exact amplitude identification, including every polynomial-moment forced fibre. -/
theorem amplitudeIdentification : AmplitudeIdentificationStatement.{u, v} :=
  amplitudeIdentification_of_ingredients amplitudeIdMoments amplitudeIdFibres

end WordBalance

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # the pairing `⟨1 + R, ·⟩` on `H^n`, and the slow test

The functional `sharpPair R U = ⟨1 + R, U⟩` is additive, bounded by `(‖R‖ + 1) ‖U‖`, and equals the
mean of `U` plus a term bounded by `‖R‖ ‖U‖`.  The constant tests `torusHigherConstant` scale
with complex multiplication, and have norm `‖E‖` times the norm of the constant `1`. -/

/-- The value map of `H^n` has norm at most one. -/
theorem sharp_value_norm_le {n : ℕ} (U : TorusHk n ℂ) : ‖torusHkValueCLM U‖ ≤ ‖U‖ := by
  change ‖(U.val : PiLp 2 _) _‖ ≤ ‖U.val‖
  exact PiLp.norm_apply_le _ _

/-- The pairing `⟨1 + R, U⟩` of the sharp families. -/
def sharpPair {n : ℕ} (R : ComplexCellL2) (U : TorusHk n ℂ) : ℂ :=
  cellComplexPair (R + cellConstantCLM 1) (torusHkValueCLM U)

theorem sharpPair_add {n : ℕ} (R : ComplexCellL2) (U V : TorusHk n ℂ) :
    sharpPair R (U + V) = sharpPair R U + sharpPair R V := by
  unfold sharpPair
  rw [map_add, cellComplexPair_add_right]

theorem sharpPair_zero {n : ℕ} (R : ComplexCellL2) : sharpPair R (0 : TorusHk n ℂ) = 0 := by
  unfold sharpPair
  rw [map_zero, cellComplexPair_zero_right]

theorem sharpPair_sum {n : ℕ} {J : Type*} (R : ComplexCellL2) (s : Finset J)
    (U : J → TorusHk n ℂ) : sharpPair R (∑ j ∈ s, U j) = ∑ j ∈ s, sharpPair R (U j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sharpPair_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sharpPair_add, ih]

theorem sharpPair_norm_le {n : ℕ} (R : ComplexCellL2) (U : TorusHk n ℂ) :
    ‖sharpPair R U‖ ≤ (‖R‖ + 1) * ‖U‖ := by
  unfold sharpPair
  refine (cellComplexPair_norm_le _ _).trans ?_
  refine mul_le_mul ?_ (sharp_value_norm_le U) (norm_nonneg _) (by positivity)
  refine (norm_add_le _ _).trans ?_
  rw [cellConstantCLM_norm, norm_one]

/-- The pairing is the mean plus a term bounded by `‖R‖ ‖U‖`. -/
theorem sharpPair_le_mean {n : ℕ} (R : ComplexCellL2) (U : TorusHk n ℂ) :
    ‖sharpPair R U‖ ≤ ‖cellMeanCLM (torusHkValueCLM U)‖ + ‖R‖ * ‖U‖ := by
  unfold sharpPair
  rw [cellComplexPair_add_left]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖cellComplexPair (cellConstantCLM 1) (torusHkValueCLM U)‖ =
      ‖cellMeanCLM (torusHkValueCLM U)‖ := by
    rw [cellComplexPair_symm, ← cellComplexPair_const_one, norm_star]
  have h2 := cellComplexPair_norm_le R (torusHkValueCLM U)
  have h3 := mul_le_mul_of_nonneg_left (sharp_value_norm_le U) (norm_nonneg R)
  rw [h1]
  linarith

theorem torusHigherConstant_smul (K : ℕ) (β E : ℂ) :
    torusHigherScalarCLM K β (torusHigherConstant K E) = torusHigherConstant K (β * E) := by
  apply TorusHk.ext_value
  change torusHkValueCLM (torusHigherScalarCLM K β (torusHigherConstant K E)) =
    torusHkValueCLM (torusHigherConstant K (β * E))
  rw [torusHigherScalarCLM_value, torusHigherConstant_value, torusHigherConstant_value]
  apply Lp.ext
  filter_upwards [cellScalarCLM_ae β (cellConstantCLM E), cellConstantCLM_ae E,
    cellConstantCLM_ae (β * E)] with x h1 h2 h3
  rw [h1, h3]
  simp [h2]

theorem torusHigherConstant_norm (K : ℕ) (E : ℂ) :
    ‖torusHigherConstant K E‖ = ‖E‖ * ‖torusHigherConstant K 1‖ := by
  have := torusHigherScalarCLM_norm K E (torusHigherConstant K 1)
  rw [torusHigherConstant_smul, mul_one] at this
  exact this

/-! # the Schur assembly of the sharp families

From pairwise operators `T i i'` with weights `w₁` (norm), `w₂` (slow test, norm), `w₃` (slow test,
pairing), the Schur test gives the four sums of the sharp families: the `ℓ²` bound, the slow–fast
pairing, and the two slow-test bounds (the families and the slow–slow pairing). A complex weight
`β_i` of the slow test is absorbed into the test: `β (E + D) = (βE) + βD`. -/

/-- Pairwise data for the sharp assembly. -/
structure SharpPairData {I : Type*} (S S' : Finset I) {N n : ℕ}
    (T : I → I → TorusHk N ℂ →L[ℝ] TorusHk n ℂ) (Mx Rb A1 B1 A2 B2 A3 B3 : ℝ)
    (w1 w2 w3 : I → I → ℝ) : Prop where
  nn1 : ∀ i i', 0 ≤ w1 i i'
  nn2 : ∀ i i', 0 ≤ w2 i i'
  nn3 : ∀ i i', 0 ≤ w3 i i'
  hB1 : 0 ≤ B1
  hB2 : 0 ≤ B2
  hB3 : 0 ≤ B3
  hRb : 0 ≤ Rb
  row1 : ∀ i ∈ S, ∑ i' ∈ S', w1 i i' ≤ A1
  col1 : ∀ i' ∈ S', ∑ i ∈ S, w1 i i' ≤ B1
  row2 : ∀ i ∈ S, ∑ i' ∈ S', w2 i i' ≤ A2
  col2 : ∀ i' ∈ S', ∑ i ∈ S, w2 i i' ≤ B2
  row3 : ∀ i ∈ S, ∑ i' ∈ S', w3 i i' ≤ A3
  col3 : ∀ i' ∈ S', ∑ i ∈ S, w3 i i' ≤ B3
  hN : ∀ i ∈ S, ∀ i' ∈ S', ∀ ψ, ‖T i i' ψ‖ ≤ w1 i i' * ‖ψ‖
  hS : ∀ i ∈ S, ∀ i' ∈ S', ∀ (E : ℂ) (D : TorusHk N ℂ), ‖D‖ ≤ Mx * ‖E‖ →
    ‖T i i' (torusHigherConstant N E + D)‖ ≤ w2 i i' * ‖E‖
  hP : ∀ R : ComplexCellL2, ‖R‖ ≤ Rb → ∀ i ∈ S, ∀ i' ∈ S', ∀ (E : ℂ) (D : TorusHk N ℂ),
    ‖D‖ ≤ Mx * ‖E‖ → ‖sharpPair R (T i i' (torusHigherConstant N E + D))‖ ≤ w3 i i' * ‖E‖

theorem sharp_assembly_norm {I : Type*} {S S' : Finset I} {N n : ℕ}
    {T : I → I → TorusHk N ℂ →L[ℝ] TorusHk n ℂ} {Mx Rb A1 B1 A2 B2 A3 B3 : ℝ} {w1 w2 w3 : I → I → ℝ}
    (hd : SharpPairData S S' T Mx Rb A1 B1 A2 B2 A3 B3 w1 w2 w3) (ψ : I → TorusHk N ℂ) :
    ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (ψ i)‖ ^ 2 ≤ A1 * B1 * ∑ i ∈ S, ‖ψ i‖ ^ 2 :=
  elem_schur S S' (fun i i' => T i i' (ψ i)) w1 (fun i => ‖ψ i‖) hd.nn1
    (fun i hi i' hi' => hd.hN i hi i' hi' _) hd.row1 hd.col1 hd.hB1

theorem sharp_assembly_pair {I : Type*} {S S' : Finset I} {N n : ℕ}
    {T : I → I → TorusHk N ℂ →L[ℝ] TorusHk n ℂ} {Mx Rb A1 B1 A2 B2 A3 B3 : ℝ} {w1 w2 w3 : I → I → ℝ}
    (hd : SharpPairData S S' T Mx Rb A1 B1 A2 B2 A3 B3 w1 w2 w3) (ψ : I → TorusHk N ℂ)
    (R : ComplexCellL2) (hR : ‖R‖ ≤ Rb) :
    ∑ i' ∈ S', ‖sharpPair R (∑ i ∈ S, T i i' (ψ i))‖ ^ 2 ≤
      (Rb + 1) ^ 2 * (A1 * B1) * ∑ i ∈ S, ‖ψ i‖ ^ 2 := by
  have hc : 0 ≤ Rb + 1 := by linarith [hd.hRb]
  have key := elem_schur (H := fun _ => ℂ) S S' (fun i i' => sharpPair R (T i i' (ψ i)))
    (fun i i' => (Rb + 1) * w1 i i') (fun i => ‖ψ i‖)
    (fun i i' => mul_nonneg hc (hd.nn1 i i'))
    (fun i hi i' hi' => by
      refine (sharpPair_norm_le R _).trans ?_
      calc (‖R‖ + 1) * ‖T i i' (ψ i)‖ ≤ (Rb + 1) * (w1 i i' * ‖ψ i‖) :=
            mul_le_mul (by linarith) ((hd.hN i hi i' hi' _)) (norm_nonneg _) hc
        _ = _ := by ring)
    (A := (Rb + 1) * A1) (B := (Rb + 1) * B1)
    (fun i hi => by
      rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hd.row1 i hi) hc)
    (fun i' hi' => by
      rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hd.col1 i' hi') hc)
    (mul_nonneg hc hd.hB1)
  simp only [sharpPair_sum]
  calc _ ≤ (Rb + 1) * A1 * ((Rb + 1) * B1) * ∑ i ∈ S, ‖ψ i‖ ^ 2 := key
    _ = _ := by ring

/-- A complex weight is absorbed into the slow test. -/
theorem slow_absorb {N : ℕ} (E β : ℂ) (D : TorusHk N ℂ) :
    torusHigherScalarCLM N β (torusHigherConstant N E + D) =
      torusHigherConstant N (β * E) + torusHigherScalarCLM N β D := by
  rw [map_add, torusHigherConstant_smul]

theorem slow_absorb_norm {N : ℕ} (E β : ℂ) (D : TorusHk N ℂ) (Mx : ℝ)
    (hD : ‖D‖ ≤ Mx * ‖E‖) : ‖torusHigherScalarCLM N β D‖ ≤ Mx * ‖β * E‖ := by
  rw [torusHigherScalarCLM_norm, norm_mul]
  calc ‖β‖ * ‖D‖ ≤ ‖β‖ * (Mx * ‖E‖) := mul_le_mul_of_nonneg_left hD (norm_nonneg _)
    _ = _ := by ring

theorem sharp_assembly_slow_norm {I : Type*} {S S' : Finset I} {N n : ℕ}
    {T : I → I → TorusHk N ℂ →L[ℝ] TorusHk n ℂ} {Mx Rb A1 B1 A2 B2 A3 B3 : ℝ} {w1 w2 w3 : I → I → ℝ}
    (hd : SharpPairData S S' T Mx Rb A1 B1 A2 B2 A3 B3 w1 w2 w3) (ψ : I → TorusHk N ℂ) (E : ℂ) (β : I → ℂ)
    (D : TorusHk N ℂ) (hD : ‖D‖ ≤ Mx * ‖E‖)
    (hψ : ∀ i ∈ S, ψ i = torusHigherScalarCLM N (β i) (torusHigherConstant N E + D)) :
    ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (ψ i)‖ ^ 2 ≤ A2 * B2 * ‖E‖ ^ 2 * ∑ i ∈ S, ‖β i‖ ^ 2 := by
  have key := elem_schur S S' (fun i i' => T i i' (ψ i)) w2 (fun i => ‖β i‖ * ‖E‖) hd.nn2
    (fun i hi i' hi' => by
      rw [hψ i hi, slow_absorb]
      refine (hd.hS i hi i' hi' (β i * E) _ (slow_absorb_norm E (β i) D Mx hD)).trans ?_
      rw [norm_mul])
    hd.row2 hd.col2 hd.hB2
  refine key.trans (le_of_eq ?_)
  simp only [mul_pow]
  rw [← Finset.sum_mul]
  ring

theorem sharp_assembly_slow_pair {I : Type*} {S S' : Finset I} {N n : ℕ}
    {T : I → I → TorusHk N ℂ →L[ℝ] TorusHk n ℂ} {Mx Rb A1 B1 A2 B2 A3 B3 : ℝ} {w1 w2 w3 : I → I → ℝ}
    (hd : SharpPairData S S' T Mx Rb A1 B1 A2 B2 A3 B3 w1 w2 w3) (ψ : I → TorusHk N ℂ) (E : ℂ) (β : I → ℂ)
    (D : TorusHk N ℂ) (hD : ‖D‖ ≤ Mx * ‖E‖)
    (hψ : ∀ i ∈ S, ψ i = torusHigherScalarCLM N (β i) (torusHigherConstant N E + D))
    (R : ComplexCellL2) (hR : ‖R‖ ≤ Rb) :
    ∑ i' ∈ S', ‖sharpPair R (∑ i ∈ S, T i i' (ψ i))‖ ^ 2 ≤
      A3 * B3 * ‖E‖ ^ 2 * ∑ i ∈ S, ‖β i‖ ^ 2 := by
  have key := elem_schur (H := fun _ => ℂ) S S' (fun i i' => sharpPair R (T i i' (ψ i))) w3
    (fun i => ‖β i‖ * ‖E‖) hd.nn3
    (fun i hi i' hi' => by
      rw [hψ i hi, slow_absorb]
      refine (hd.hP R hR i hi i' hi' (β i * E) _ (slow_absorb_norm E (β i) D Mx hD)).trans ?_
      rw [norm_mul])
    hd.row3 hd.col3 hd.hB3
  simp only [sharpPair_sum]
  refine key.trans (le_of_eq ?_)
  simp only [mul_pow]
  rw [← Finset.sum_mul]
  ring

/-- The transversality defect: if the pairwise operators commute with the projections, the defect
of the output is the output of the defect. -/
theorem sharp_assembly_transverse {I : Type*} {S S' : Finset I} {N n : ℕ}
    {T : I → I → TorusHk N ℂ →L[ℝ] TorusHk n ℂ} {Mx Rb A1 B1 A2 B2 A3 B3 : ℝ}
    {w1 w2 w3 : I → I → ℝ}
    (hd : SharpPairData S S' T Mx Rb A1 B1 A2 B2 A3 B3 w1 w2 w3) (ψ : I → TorusHk N ℂ)
    (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ) (Pn : TorusHk n ℂ →L[ℝ] TorusHk n ℂ)
    (hc : ∀ i i' (φ : TorusHk N ℂ), Pn (T i i' φ) = T i i' (PN φ)) :
    ∑ i' ∈ S', ‖(∑ i ∈ S, T i i' (ψ i)) - Pn (∑ i ∈ S, T i i' (ψ i))‖ ^ 2 ≤
      A1 * B1 * ∑ i ∈ S, ‖ψ i - PN (ψ i)‖ ^ 2 := by
  have e : ∀ i', (∑ i ∈ S, T i i' (ψ i)) - Pn (∑ i ∈ S, T i i' (ψ i)) =
      ∑ i ∈ S, T i i' (ψ i - PN (ψ i)) := by
    intro i'
    rw [map_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hc, map_sub]
  simp only [e]
  exact sharp_assembly_norm hd (fun i => ψ i - PN (ψ i))

end AVRegularity.CycleWords.Assembly
end
