-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePairing
import Homogenization.Sobolev.H1.BasicLemmas

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Parabolic.WeakUniqueness
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The actual gradient of a finite Fourier field, with all ordered spatial derivatives. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Assemble the two gradient directions after each ordered derivative word. -/
def coupledPlainGradientJet (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (j : ℕ) (w : DerivativeWord2 j) : Vec 2 → PiLp 2 (fun _ : Fin 2 => h i) :=
  fun x => ∑ k : Fin 2, tensorEntryCLM k (coupledPlainRawJet N c i (j + 1) (Fin.snoc w k) x)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Every gradient jet is smooth. -/
theorem coupledPlainGradientJet_contDiff (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (j : ℕ) (w : DerivativeWord2 j) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (coupledPlainGradientJet N c i j w) := by
  apply ContDiff.sum
  intro k _
  exact (tensorEntryCLM k).contDiff.comp (coupledPlainRawJet_contDiff N c i (j + 1) _)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Differentiating the assembled gradient commutes the final two smooth partials. -/
theorem coupledPlainGradientJet_fderiv (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (j : ℕ) (w : DerivativeWord2 j) (l : Fin 2) (x : Vec 2) :
    fderiv ℝ (coupledPlainGradientJet N c i j w) x (basisVec l) =
      coupledPlainGradientJet N c i (j + 1) (Fin.snoc w l) x := by
  unfold coupledPlainGradientJet
  rw [fderiv_fun_sum (A := fun k y => tensorEntryCLM (E := h i) k
    (coupledPlainRawJet N c i (j + 1) (Fin.snoc w k) y)) (fun k _ => ((tensorEntryCLM (E := h i) k).contDiff.comp
    (coupledPlainRawJet_contDiff N c i (j + 1) (Fin.snoc w k))).differentiable (by simp) x)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hd := (tensorEntryCLM (E := h i) k).hasFDerivAt.comp x
    ((coupledPlainRawJet_contDiff N c i (j + 1) (Fin.snoc w k)).differentiable (by simp) x).hasFDerivAt
  change (fderiv ℝ ((tensorEntryCLM (E := h i) k) ∘
    coupledPlainRawJet N c i (j + 1) (Fin.snoc w k)) x) (basisVec l) = _
  rw [hd.fderiv]
  change tensorEntryCLM k (fderiv ℝ (coupledPlainRawJet N c i (j + 1) (Fin.snoc w k)) x
    (basisVec l)) = _
  rw [coupledPlainRawJet_fderiv, coupledPlainRawJet_snoc_swap]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The assembled gradient jet is periodic. -/
theorem coupledPlainGradientJet_periodic (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (j : ℕ) (w : DerivativeWord2 j) :
    AVenhance.IsZ2Periodic (coupledPlainGradientJet N c i j w) := by
  intro n x
  unfold coupledPlainGradientJet
  apply Finset.sum_congr rfl
  intro k _
  rw [coupledPlainRawJet_periodic]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Each assembled gradient jet is cell L². -/
theorem coupledPlainGradientJet_memLp (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (j : ℕ) (w : DerivativeWord2 j) :
    MemLp (coupledPlainGradientJet N c i j w) 2 (volume.restrict AVenhance.unitCube) := by
  have ht (k : Fin 2) : MemLp
      (fun x => tensorEntryCLM (E := h i) k
        (coupledPlainRawJet N c i (j + 1) (Fin.snoc w k) x))
      2 (volume.restrict AVenhance.unitCube) :=
    (tensorEntryCLM (E := h i) k).comp_memLp'
      (coupledPlainRawJet_memLp N c i (j + 1) (Fin.snoc w k))
  exact memLp_finsetSum Finset.univ (fun k _ => ht k)

/-- The gradient array as a finite ordered raw jet. -/
def coupledPlainGradientRawJet (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) : RawJet2 K (PiLp 2 (fun _ : Fin 2 => h i)) :=
  fun a => coupledPlainGradientJet N c i a.1.val a.2

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Classical mixed derivatives give the actual ordered weak gradient jet. -/
theorem coupledPlainGradientRawJet_hasWeakJet (N : ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) (K : ℕ) :
    HasOrderedWeakJetOn (K := K) Set.univ (coupledPlainGradientRawJet N c i K) := by
  intro j w k e
  let L := InnerProductSpace.toDual ℝ (PiLp 2 (fun _ : Fin 2 => h i)) e
  have hc : ContDiff ℝ (1 : WithTop ℕ∞)
      (fun x => inner ℝ e (coupledPlainGradientJet N c i j.val w x)) :=
    (L.contDiff.comp (coupledPlainGradientJet_contDiff N c i j.val w)).of_le (by simp)
  have hd : (fun x => fderiv ℝ
      (fun y => inner ℝ e (coupledPlainGradientJet N c i j.val w y)) x (basisVec k)) =
      fun x => inner ℝ e (coupledPlainGradientJet N c i (j.val + 1) (Fin.snoc w k) x) := by
    funext x
    have hf := ((coupledPlainGradientJet_contDiff N c i j.val w).differentiable
      (by simp) x).hasFDerivAt
    have hl := L.hasFDerivAt.comp x hf
    change (fderiv ℝ (L ∘ coupledPlainGradientJet N c i j.val w) x) (basisVec k) = _
    rw [hl.fderiv]
    change inner ℝ e (fderiv ℝ (coupledPlainGradientJet N c i j.val w) x (basisVec k)) = _
    rw [coupledPlainGradientJet_fderiv]
  have hw := HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := k) hc
  rw [hd] at hw
  exact hw

/-- Bundle the genuine smooth gradient jet as a torus carrier. -/
def coupledPlainGradientHk (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) : TorusHk K (PiLp 2 (fun _ : Fin 2 => h i)) :=
  TorusHkFunction.toHk
    { jet := coupledPlainGradientRawJet N c i K
      hasPeriodicWeakJet := ⟨fun a => coupledPlainGradientJet_periodic N c i a.1.val a.2,
        fun a => coupledPlainGradientJet_memLp N c i a.1.val a.2,
        coupledPlainGradientRawJet_hasWeakJet N c i K⟩ }

/-- The bundled gradient retains its literal raw jet almost everywhere. -/
theorem coupledPlainGradientHk_jet_ae (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) (a : JetIndex2 K) :
    (coupledPlainGradientHk N c i K).val a =ᵐ[volume.restrict AVenhance.unitCube]
      coupledPlainGradientJet N c i a.1.val a.2 :=
  torusJetToL2_ae _ _ a

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open AVenhance.Infra.Parabolic.FourierGalerkin AVenhance.Infra.Torus
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Identifying the explicit scalar-mode synthesis with the existing orthogonal cutoff. -/

local instance plainProjectionBridgeMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance plainProjectionBridgeAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- A plain value mode is exactly the transported vector-valued torus Fourier mode. -/
theorem cellToTorus_plainMode (N : ℕ) (i : ι)
    (p : VectorFourierIndex N (h i)) :
    cellToTorus (plainModeCellLp N ⟨i, p⟩ i 0 Fin.elim0) =
      vectorFourierMode (E := h i) N p.1 p.2 := by
  apply Lp.ext
  have hcell := cellToTorus_ae (plainModeCellLp N ⟨i, p⟩ i 0 Fin.elim0)
  have hrep := measurePreserving_unitTorusRepresentative_cell.quasiMeasurePreserving.ae
    (plainModeCellLp_ae N ⟨i, p⟩ i 0 Fin.elim0)
  have hvec := ContinuousLinearMap.coeFn_compLpL
    (L := (ContinuousLinearMap.id ℝ ℝ).smulRight ((stdOrthonormalBasis ℝ (h i)) p.2))
    (realFourierModeL2 N p.1)
  have hscalar := (realFourierModeFin_memLp N p.1).coeFn_toLp
  have hmeasure : ae torusMeasure ≤ ae (volume : Measure (UnitAddTorus (Fin 2))) :=
    le_of_eq (congrArg (fun μ : Measure (UnitAddTorus (Fin 2)) => ae μ)
      coupledEnergy_torusMeasure_eq_volume)
  filter_upwards [hcell, hrep, hvec.filter_mono hmeasure, hscalar.filter_mono hmeasure] with y hy hr hv hs
  rw [hy]
  change plainModeCellLp N ⟨i, p⟩ i 0 Fin.elim0 (unitTorusRepresentative 2 y) = _
  rw [hr]
  simp only [coupledModeJet, dite_true]
  change coupledModeScalarDerivative N ⟨i, p⟩ 0 Fin.elim0 (unitTorusRepresentative 2 y) •
    ((stdOrthonormalBasis ℝ (h i)) p.2) = _
  change _ = (((ContinuousLinearMap.id ℝ ℝ).smulRight
    ((stdOrthonormalBasis ℝ (h i)) p.2)).compLpL 2 volume (realFourierModeL2 N p.1)) y
  rw [hv]
  have hs' : realFourierModeL2 N p.1 y = realFourierModeFin N p.1 y := hs
  rw [hs', realFourierModeFin_eq_periodicToTorus]
  rfl


omit [Fintype ι] in
/-- Explicit value-mode expansion of the transported orthogonal cutoff. -/
theorem cellVectorFourierProjection_eq_plain_sum (N : ℕ) (i : ι)
    (f : ComponentL2 (volume.restrict AVenhance.unitCube) (h i)) :
    cellVectorFourierProjection N f = ∑ p : VectorFourierIndex N (h i),
      inner ℝ (plainModeCellLp N ⟨i, p⟩ i 0 Fin.elim0) f •
        plainModeCellLp N ⟨i, p⟩ i 0 Fin.elim0 := by
  apply (cellToTorus (E := h i)).injective
  rw [cellToTorus_cellVectorFourierProjection, map_sum]
  simp_rw [map_smul, cellToTorus_plainMode]
  have hcoeff (p : VectorFourierIndex N (h i)) :
      inner ℝ (plainModeCellLp N ⟨i, p⟩ i 0 Fin.elim0) f =
        inner ℝ (cellToTorus f) (vectorFourierMode N p.1 p.2) := by
    rw [← cellToTorus_plainMode N i p, real_inner_comm]
    exact ((cellToTorus (E := h i)).inner_map_map f _).symm
  simp_rw [hcoeff]
  change vectorFourierProjection N (torusLpToVolume (cellToTorus f)) =
    ∑ p : VectorFourierIndex N (h i),
      inner ℝ (torusLpToVolume (cellToTorus f)) (vectorFourierMode N p.1 p.2) •
        vectorFourierMode N p.1 p.2
  rw [vectorFourierProjection, finiteOrthonormalProjection_apply]
  rfl

end AVRegularity.CoupledEnergy.Galerkin
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Reconstruct the full differential form against an arbitrary finite test. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- The literal spatial weak form of the finite trial and finite test fields. -/
def plainSpatialTestIntegrand (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (v : Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (c z : CoupledPlainCoefficients (h := h) N) (x : Vec 2) : ℝ :=
  (-ν * ∑ i, ∑ k : Fin 2,
    inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
      (coupledPlainRawJet N z i 1 (fun _ => k) x)) +
  (-∑ i, ∑ k : Fin 2, v x k *
    inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
      (coupledPlainRawJet N z i 0 Fin.elim0 x)) +
  (-∑ i, ∑ i', ∑ d : admissibleOrders K D i i', ∑ k : Fin 2,
    inner ℝ (A i i' d x (coupledPlainRawTensor N c i' (d.1 - 1) x) k)
      (coupledPlainRawJet N z i 1 (fun _ => k) x))

/-- Contracting every Fourier row gives the full literal spatial weak form. -/
theorem plainSpatialRow_test_contraction (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (v : Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (c z : CoupledPlainCoefficients (h := h) N) (x : Vec 2) :
    (∑ r, z r * plainSpatialRowIntegrand N D ν K v A r c x) =
      plainSpatialTestIntegrand N D ν K v A c z x := by
  have hdiff : (∑ r, z r * (-ν * ∑ i, ∑ k : Fin 2,
      inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
        (coupledModeJet N r i 1 (fun _ => k) x))) =
      -ν * ∑ i, ∑ k : Fin 2,
        inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
          (coupledPlainRawJet N z i 1 (fun _ => k) x) := by
    rw [← plainTestGradient_inner_sum N z (fun i k => coupledPlainRawJet N c i 1 (fun _ => k) x) x,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp only [plainSpatialRowIntegrand, plainSpatialTestIntegrand, mul_add, Finset.sum_add_distrib]
  rw [hdiff]
  simp only [mul_neg, Finset.sum_neg_distrib]
  rw [plainTestDrift_inner_sum, plainTestCoupling_inner_sum]

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Fixed Hilbert readouts keep spectral band forcing expressions small
and give measurable, integrably dominated scalar energy increments. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def torusBandJetCLM (K N M : ℕ) (j : JetIndex2 K) : TorusHk K E →L[ℝ]
    ComponentL2 (volume.restrict AVenhance.unitCube) E :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K =>
    ComponentL2 (volume.restrict AVenhance.unitCube) E) j).comp
      ((torusHkGraph (E := E) K).toSubmodule.subtypeL.comp (galerkinProj N - galerkinProj M))

@[simp] theorem torusBandJetCLM_apply (K N M : ℕ) (j : JetIndex2 K) (u : TorusHk K E) :
    torusBandJetCLM K N M j u = (galerkinProj N u).val j - (galerkinProj M u).val j := rfl

def torusBandSourceIntegrand {K : ℕ} (N M : ℕ) {j : ℕ} (hj : j ≤ K) (word : DerivativeWord2 j)
    (H u : ℝ → TorusHk K E) (S : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    (w : ℝ → TorusHk (K + 1) E) (t : ℝ) : ℝ :=
  2 * (inner ℝ (torusBandJetCLM K N M ⟨⟨j, by omega⟩, word⟩ (H t))
    (torusBandJetCLM K N M ⟨⟨j, by omega⟩, word⟩ (u t)) - ∑ k : Fin 2,
      inner ℝ (torusBandJetCLM K N M ⟨⟨j, by omega⟩, word⟩
        (mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S t)))
        (torusBandJetCLM (K + 1) N M ⟨⟨j + 1, by omega⟩, Fin.snoc word k⟩ (w t)))

theorem torusBandSourceIntegrand_aestronglyMeasurable {K : ℕ} (N M : ℕ)
    {j : ℕ} (hj : j ≤ K) (word : DerivativeWord2 j) (a b : ℝ)
    (H u : ℝ → TorusHk K E) (S : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    (w : ℝ → TorusHk (K + 1) E)
    (hH : AEStronglyMeasurable H (volume.restrict (Set.Icc a b)))
    (hu : AEStronglyMeasurable u (volume.restrict (Set.Icc a b)))
    (hS : AEStronglyMeasurable S (volume.restrict (Set.Icc a b)))
    (hw : AEStronglyMeasurable w (volume.restrict (Set.Icc a b))) :
    AEStronglyMeasurable (torusBandSourceIntegrand N M hj word H u S w) (volume.restrict (Set.Icc a b)) := by
  have hh := ((torusBandJetCLM K N M ⟨⟨j, by omega⟩, word⟩).continuous.comp_aestronglyMeasurable hH).inner (𝕜 := ℝ)
    ((torusBandJetCLM K N M ⟨⟨j, by omega⟩, word⟩).continuous.comp_aestronglyMeasurable hu)
  have hs := Finset.univ.aestronglyMeasurable_fun_sum (fun k _ =>
    (((torusBandJetCLM K N M ⟨⟨j, by omega⟩, word⟩).comp
      (mapTorusHkCLM K (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k))).continuous.comp_aestronglyMeasurable hS).inner (𝕜 := ℝ)
      ((torusBandJetCLM (K + 1) N M ⟨⟨j + 1, by omega⟩, Fin.snoc word k⟩).continuous.comp_aestronglyMeasurable hw))
  simpa only [torusBandSourceIntegrand, Function.comp_def, ContinuousLinearMap.comp_apply,
    mapTorusHkCLM_apply, Pi.sub_apply] using! (hh.sub hs).const_mul 2

theorem torusBandSourceIntegrand_abs_le {K : ℕ} (N M : ℕ) {j : ℕ} (hj : j ≤ K)
    (word : DerivativeWord2 j) (R : ℝ)
    (H u : ℝ → TorusHk K E) (S : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    (w : ℝ → TorusHk (K + 1) E) (t : ℝ) (hu : ‖u t‖ ≤ R) :
    |torusBandSourceIntegrand N M hj word H u S w t| ≤
      torusSourceTailMajorant N R H S w t + torusSourceTailMajorant M R H S w t := by
  have hh := galerkinBand_source_pairing_bound N M (H t) (u t)
    (fun k => mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S t)) (w t) R hu hj word
  simp only [torusBandSourceIntegrand, torusBandJetCLM_apply, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply hh.trans_eq
  unfold torusSourceTailMajorant
  simp only [add_mul, Finset.sum_add_distrib]
  ring

end AVRegularity.CoupledEnergy.Galerkin
end
