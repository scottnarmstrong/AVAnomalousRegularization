-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.CentreFlowWindow
public import AVRegularity.CycleJoint.PeriodizedFamilyGlobalReadout
import AVRegularity.CycleJoint.PathReduction.Premises
import AVRegularity.CycleJoint.WindowCoverConstructedRetainedActualTaylorLinearEndpointAllMomentsBound
import AVRegularity.CycleJoint.PreparationReferenceNormalizedHilbertCurve
import AVRegularity.CycleComparison.Error.WeakSolution

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs.Assembly
namespace AVRegularity.CycleJointProofs.PlaneTorus

/-! Scale ordering follows from the actual window cover and the monotone diffusivity chain. -/

section
/-- Cell-length and diffusion-radius bounds force the fine wavelength below its parent. -/
theorem wavelength_order_from_cover_lengths (e E ν B T : ℝ)
    (he : 0 ≤ e) (hE : 0 ≤ E) (hν : 0 < ν) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hνB : ν ≤ B) (hell : (e / Real.sqrt ν) ^ 2 ≤ T)
    (hR : Real.sqrt (B * T) ≤ E) : e ≤ E := by
  have hcell := mul_le_mul_of_nonneg_left hell hν.le
  have hcancel : ν * (e / Real.sqrt ν) ^ 2 = e ^ 2 := by
    rw [div_pow, Real.sq_sqrt hν.le]
    field_simp
  rw [hcancel] at hcell
  have hparent := (sq_le_sq₀ (Real.sqrt_nonneg _) hE).mpr hR
  rw [Real.sq_sqrt (mul_nonneg hB hT)] at hparent
  exact (sq_le_sq₀ he hE).mp
    (hcell.trans ((mul_le_mul_of_nonneg_right hνB hT).trans hparent))

universe u v w x

variable (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (g₀ : ℝ) (H D Kmax Ks Ls Jm qJ Jchart : ℕ)
    (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (ρold : ℝ)

variable {α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb cMol cOld COld Crat
  Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold}

variable (hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold)



include hprem in
/-- The scale-order premise of the preparation PDE lemmas follows without admissibility of q. -/
theorem jointPremises_wavelength_order (hΛ : 128 ≤ Λ) (hζ : IsFastProfile ζ) :
    ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) := by
  have hΛ1 : 1 ≤ Λ := by omega
  have hνB : ν ≤ B := by
    rw [← hprem.hν, ← hprem.hB]
    exact CycleReference.bandChain_step_ge hΛ1 hζ hprem.hband
      (by have hh := hprem.hm2; omega) hprem.hmM
  exact wavelength_order_from_cover_lengths _ _ _ _ _
    (Construction.Stream.ocEpsilon_pos hΛ1).le (Construction.Stream.ocEpsilon_pos hΛ1).le
    hprem.cov.pos.1 hprem.cov.pos.2.1.le (Construction.Stream.ocTauPP_pos hΛ1).le
    hνB hprem.cov.ellT hprem.cov.RE
end

/-! An edge-free family retains its preparation premises at zero Sobolev slots. -/

section
section Empty
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {P' : Type*} {Ctx : P' → Type*}

/-- An empty edge graph has the molecular envelope at every reserve. -/
theorem empty_molecular_envelope (F : ChartedFamily ι h D P' Ctx)
    (he : ∀ v u, IsEmpty (F.Γ v u)) (π : ι → ℝ) (K : ι → ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (Cm : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ) :
    IsMolecularEnvelope F π K dom ν e E ρ Cm J b := by
  refine ⟨fun _ _ v u γ => False.elim ((he v u).false γ), ?_⟩
  intro v u j _
  let := he v u
  simp only [Fintype.sum_empty, mul_zero]
  exact zero_le

/-- An empty edge graph also has the pointwise molecular envelope at every reserve. -/
theorem empty_pointwise_molecular_envelope (F : ChartedFamily ι h D P' Ctx)
    (he : ∀ v u, IsEmpty (F.Γ v u)) (π : ι → ℝ) (K : ι → ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (Cm : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ) :
    IsPointwiseMolecularEnvelope F π K dom ν e E ρ Cm J b := by
  refine ⟨fun _ _ v u γ => False.elim ((he v u).false γ), ?_⟩
  intro v u j _
  let := he v u
  simp only [Fintype.sum_empty, mul_zero]
  exact zero_le

end Empty

universe u v w x

variable (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (g₀ : ℝ) (H D Kmax Ks Ls Jm qJ Jchart : ℕ)
    (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (ρold : ℝ)

variable {α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb cMol cOld COld Crat
  Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold}

variable (hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold)




include hprem in
/-- Edge-free preparation data satisfy the same certificate at slot zero. -/
theorem jointPremises_zeroSlots_of_edgeFree (he : ∀ v u, IsEmpty (F.Γ v u)) :
    JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      π (fun _ => 0) Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold := by
  exact {
    hπ := hprem.hπ
    hK := fun _ => Nat.zero_le Kmax
    hΦ := hprem.hΦ
    hband := hprem.hband
    hm2 := hprem.hm2
    hmStar := hprem.hmStar
    hmM := hprem.hmM
    hν := hprem.hν
    hB := hprem.hB
    cov := hprem.cov
    hwmeas := hprem.hwmeas
    hprep := hprem.hprep
    hdepth := hprem.hdepth
    hdesc := fun v u γ => False.elim ((he v u).false γ)
    htorus := hprem.htorus
    hcover := hprem.hcover
    hmeas := hprem.hmeas
    hΘ₀ := hprem.hΘ₀
    hΘ₁ := hprem.hΘ₁
    henv := {
      nonneg := hprem.henv.nonneg
      row_sum := hprem.henv.row_sum
      col_sum := hprem.henv.col_sum
      analytic := hprem.henv.analytic
      molecular := empty_molecular_envelope F he π (fun _ => 0) _ _ _ _ _ Cm Jm _ }
    hpointwise := empty_pointwise_molecular_envelope F he π (fun _ => 0) _ _ _ _ _ Cm Jm _
    htrans := hprem.htrans
    hquiet := hprem.hquiet
    hTcons := hprem.hTcons
    hTcov := hprem.hTcov
    hTq := hprem.hTq
    hρold := hprem.hρold
    hρrat := hprem.hρrat }
end

end AVRegularity.CycleJointProofs.PlaneTorus
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.PlaneTorus

/-! The patch data have finite polynomial energy, and radial moments can be recentered. -/

section
/-- Moving a radial centre changes its fourth-power weight by a bounded factor. -/
theorem radial_weight_recenter (y z z' : Vec 2) :
    (1 + ‖y - z'‖) ^ 4 ≤ (1 + ‖z - z'‖) ^ 4 * (1 + ‖y - z‖) ^ 4 := by
  have ht : ‖y - z'‖ ≤ ‖y - z‖ + ‖z - z'‖ := by
    rw [← sub_add_sub_cancel y z z']
    exact norm_add_le _ _
  have hmul : 0 ≤ ‖z - z'‖ * ‖y - z‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hh : 1 + ‖y - z'‖ ≤ (1 + ‖z - z'‖) * (1 + ‖y - z‖) := by
    nlinarith only [ht, hmul]
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖y - z'‖) hh 4
  simpa only [mul_pow] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

/-- Finite radial moments around any centre imply them around every other centre. -/
theorem radial_moments_recenter (f : PlaneHk Set.univ K E) (z z' : Vec 2)
    (hf : HasRadialPlaneMoments f z) : HasRadialPlaneMoments f z' := by
  intro a
  have hm : AEStronglyMeasurable (f.toFunction.jet a) volume := by
    simpa only [Measure.restrict_univ] using (f.toFunction.memL2 a).aestronglyMeasurable
  have hw : Continuous (fun y : Vec 2 => (1 + ‖y - z'‖) ^ 4) := by fun_prop
  apply (hf a).of_le_mul (c := (1 + ‖z - z'‖) ^ 4) (hw.aestronglyMeasurable.smul hm)
  filter_upwards with y
  change ‖(1 + ‖y - z'‖) ^ 4 • f.toFunction.jet a y‖ ≤
    (1 + ‖z - z'‖) ^ 4 * ‖(1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y‖
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (1 + ‖y - z'‖) ^ 4),
    abs_of_nonneg (by positivity : 0 ≤ (1 + ‖y - z‖) ^ 4)]
  exact (mul_le_mul_of_nonneg_right (radial_weight_recenter y z z')
    (norm_nonneg _)).trans_eq (mul_assoc _ _ _)

variable [FiniteDimensional ℝ E]

/-- Each localized patch has finite polynomial energy at its spatial patch centre. -/
theorem localized_patch_energy_ne_top {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N) (f : TorusHk K E) (ρ : ℝ) :
    weightedFactorialNormSq 4 1 (spatialPatchCenter N (fun k => (j k : ℤ))) ρ K
      (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) K f) ≠ ⊤ := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hh := spatialPatchLocalization_weightedFactorialNormSq_bound hζ N hN
    (fun k => (j k : ℤ)) f ρ 4 1 1 zero_le_one zero_le_one (div_le_self zero_le_one hNreal)
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hh
end

/-! The finite mesh of localized periodic data reconstructs its full torus initial trace. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The lattice periodizations of the mesh patches reconstruct the original order-zero class. -/
theorem spatialPatches_periodized_value_ae {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) {K : ℕ} (f : TorusHk K E) :
    (fun x => ∑ j : Fin 2 → Fin N,
      periodizeRawJet (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) K f).toFunction.jet
        (valueIndex2 K) x) =ᵐ[volume.restrict AVenhance.unitCube] f.val (valueIndex2 K) := by
  have hprod (j : Fin 2 → Fin N) :
      (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) K f).toFunction.jet (valueIndex2 K) =ᵐ[volume]
      (fun x => spatialPatchCutoff ζ N (fun k => (j k : ℤ)) x • f.toFunction.jet (valueIndex2 K) x) := by
    have hh := localizeTorusCarrier_value_ae f
      (spatialPatchCoefficient (E := E) ζ N (fun k => (j k : ℤ)))
      (spatialPatchCoefficient_smooth hζ N (fun k => (j k : ℤ)) K)
      (spatialPatchCoefficient_compact hζ N hN (fun k => (j k : ℤ)))
    change (localizeTorusCarrier f
      (spatialPatchCoefficient (E := E) ζ N (fun k => (j k : ℤ)))
      (spatialPatchCoefficient_smooth hζ N (fun k => (j k : ℤ)) K)
      (spatialPatchCoefficient_compact hζ N hN (fun k => (j k : ℤ)))).toFunction.jet
        (valueIndex2 K) =ᵐ[volume] _
    simpa only [spatialPatchCoefficient, smul_apply, ContinuousLinearMap.id_apply] using hh
  have hperiod (j : Fin 2 → Fin N) :
      latticePeriodization
        ((spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) K f).toFunction.jet (valueIndex2 K)) =ᵐ[
          volume.restrict AVenhance.unitCube]
      latticePeriodization (fun x => spatialPatchCutoff ζ N (fun k => (j k : ℤ)) x •
        f.toFunction.jet (valueIndex2 K) x) :=
    ae_restrict_of_ae (latticePeriodization_congr_ae (hprod j))
  have hall := ae_all_iff.mpr hperiod
  filter_upwards [hall, periodicJetRepresentative_ae f.val (valueIndex2 K)] with x hx hf
  calc
    _ = ∑ j : Fin 2 → Fin N, ∑' k : Fin 2 → ℤ,
        spatialPatchCutoff ζ N (fun i => (j i : ℤ)) (x + AVenhance.latticeShift k) •
          f.toFunction.jet (valueIndex2 K) (x + AVenhance.latticeShift k) :=
      Finset.sum_congr rfl (fun j _ => hx j)
    _ = f.toFunction.jet (valueIndex2 K) x := periodic_spatialPatch_reconstruction hζ N hN _
      (f.toFunction.hasPeriodicWeakJet.1 _) x
    _ = _ := hf

section Family
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
/-- The sum of periodized patch solutions starts from the original full Sobolev datum. -/
theorem periodizedPatches_initial_trace {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (K : ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (f : ∀ i, TorusHk (K i) (h i))
    (u : (Fin 2 → Fin N) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : (Fin 2 → Fin N) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (U : (Fin 2 → Fin N) → ∀ i, ℝ → TorusHk (K i) (h i))
    (W : (Fin 2 → Fin N) → ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hu0 : ∀ j i, u j i a = spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i))
    (hp : ∀ j, IsPeriodizedFamilyPair K a b (u j) (w j) (U j) (W j)) :
    ∀ i, (∑ j, U j i a) = f i := by
  intro i
  apply TorusHk.ext_value
  apply Lp.ext
  have hread (j : Fin 2 → Fin N) :
      (U j i a).toFunction.jet (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
      periodizeRawJet (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i)).toFunction.jet
        (valueIndex2 (K i)) := by
    apply (periodicJetRepresentative_ae (U j i a).val (valueIndex2 (K i))).trans
    simpa only [hu0 j i] using (hp j).2.2.2.1 i a ⟨le_rfl, hab⟩ (valueIndex2 (K i))
  have hall := ae_all_iff.mpr hread
  filter_upwards [periodicJetRepresentative_ae (∑ j, U j i a).val (valueIndex2 (K i)),
    PathReduction.torusCarrier_jet_sum_ae Finset.univ (fun j => U j i a) (valueIndex2 (K i)),
    hall, spatialPatches_periodized_value_ae hζ N hN (f i)] with x hx hsum hj hrec
  exact hx.symm.trans (hsum.trans ((Finset.sum_congr rfl (fun j _ => hj j)).trans hrec))

end Family
end

end AVRegularity.CycleJointProofs.PlaneTorus
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs.Assembly
namespace AVRegularity.CycleJointProofs.PlaneTorus

/-! Genuine patch solution pairs, with radial moments and uniqueness on the preparation window. -/

section
section Pair
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A physical patch solution and its genuine periodic solution, including the radial domain. -/
structure PatchPair (D : ℕ) (K : ι → ℕ) (ν a b : ℝ) (drift : ℝ → Vec 2 → Vec 2)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N)
    (j : Fin 2 → Fin N) (f : ∀ i, TorusHk (K i) (h i)) where
  plane : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)
  planeLift : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)
  torus : ∀ i, ℝ → TorusHk (K i) (h i)
  torusLift : ∀ i, ℝ → TorusHk (K i + 1) (h i)
  plane_sol : IsCoupledWeakSolutionPlane ν a b drift D K A
    (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i))
    (fun _ _ => 0) (fun _ _ => 0) plane planeLift
  pair : IsPeriodizedFamilyPair K a b plane planeLift torus torusLift
  torus_sol : IsCoupledWeakSolutionTorus ν a b drift D K A
    (fun i => torus i a) (fun _ _ => 0) (fun _ _ => 0) torus torusLift
  moments : ∀ i, ∀ t ∈ Set.Icc a b,
    HasRadialPlaneMoments (plane i t) (spatialPatchCenter N (fun k => (j k : ℤ)))

end Pair

universe u v w x

variable (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (g₀ : ℝ) (H D Kmax Ks Ls Jm qJ Jchart : ℕ)
    (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (ρold : ℝ)

variable {α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb cMol cOld COld Crat
  Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold}

variable (hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold)




include hprem in
/-- Every mesh patch has a genuine physical solution and a matching periodic solution. -/
theorem existsPreparationPatchPair (hΛ : 128 ≤ Λ) (hζ : IsFastProfile ζ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N) (f : ∀ i, TorusHk (K i) (h i)) :
    Nonempty (PatchPair D K ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m))
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      hζ N hN j f) := by
  have hT := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) (show 1 ≤ Λ by omega)
  have hab : tS ≤ tS + 2 * ocTauPP α q Λ m := by linarith only [hT]
  have hA (v u : ι) : 0 ≤ A v u := (mul_nonneg_iff_of_pos_left
    (Real.sqrt_pos.mpr (div_pos (hprem.hπ u) (hprem.hπ v)))).mp (hprem.henv.nonneg v u)
  let z := spatialPatchCenter N (fun k => (j k : ℤ))
  let fP := fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i)
  have hfP (i : ι) : weightedFactorialNormSq 4 1 z (ocRhoMol α q Λ m cMol ν) (K i) (fP i) ≠ ⊤ :=
    localized_patch_energy_ne_top hζ N hN j (f i) _
  obtain ⟨u, w, U, W, hs, he, hp, hcell⟩ := exists_actualPreparation_homogeneous_plane_and_torus
    K Kmax hprem.hK (ocRhoMol α q Λ m cMol ν) ν hprem.cov.pos.2.2 hprem.cov.pos.1
    tS (tS + 2 * ocTauPP α q Λ m) hab D F H hprem.hdepth α q Λ m Φ ζ hζ hprem.hΦ
    (Φ (m - 1)) hφ Cpad Cage Npad Jchart Cchart l₀ P hprem.hprep
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual hprem.hmeas hprem.hwmeas rfl
    hprem.cov.rho_e (jointPremises_wavelength_order hprem hΛ hζ) Jm hchart hmol
    Cm π hprem.hπ A hA rfl hprem.htorus hprem.hpointwise fP 1 zero_lt_one z hfP
  exact ⟨⟨u, w, U, W, hs, hp, hcell,
    finite_geometry_trajectory_radial_moments π hprem.hπ K 1 zero_lt_one z
      (ocRhoMol α q Λ m cMol ν) tS (tS + 2 * ocTauPP α q Λ m) hprem.cov.pos.2.2 u w he⟩⟩

include hprem in
/-- Every initial subwindow has uniqueness with only the stated preparation premises. -/
theorem preparation_torus_unique (hΛ : 128 ≤ Λ) (hζ : IsFastProfile ζ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (τ : ℝ) (hτ : τ ∈ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
    (f : ∀ i, TorusHk (K i) (h i))
    (u u' : ∀ i, ℝ → TorusHk (K i) (h i)) (w w' : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionTorus ν tS τ (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      f (fun _ _ => 0) (fun _ _ => 0) u w)
    (hs' : IsCoupledWeakSolutionTorus ν tS τ (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      f (fun _ _ => 0) (fun _ _ => 0) u' w') : ∀ i, ∀ t ∈ Set.Icc tS τ, u i t = u' i t := by
  have hFzero (i : ι) : MemLp (fun _ : ℝ =>
      (0 : TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))) 2 (volume.restrict (Set.Icc tS τ)) :=
    MemLp.zero' (ε := TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
  have hgzero (i : ι) : Integrable (fun _ : ℝ => (0 : TorusHk (K i) (h i)))
      (volume.restrict (Set.Icc tS τ)) :=
    integrable_zero ℝ (TorusHk (K i) (h i)) (volume.restrict (Set.Icc tS τ))
  exact actualPreparation_torusWeakSolution_subwindow_unique K Kmax hprem.hK
    (ocRhoMol α q Λ m cMol ν) ν hprem.cov.pos.2.2 hprem.cov.pos.1
    tS (tS + 2 * ocTauPP α q Λ m) D F H hprem.hdepth α q Λ m Φ ζ hprem.hΦ
    (Φ (m - 1)) hφ Cpad Cage Npad Jchart Cchart l₀ P hprem.hprep
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual rfl hprem.htorus hprem.hmeas hprem.hwmeas
    rfl hprem.cov.rho_e (jointPremises_wavelength_order hprem hΛ hζ) Jm hchart hmol Cm π hprem.hπ
    (fun v u => Real.sqrt (π u / π v) * A v u) hprem.henv.nonneg hprem.hpointwise
    τ hτ.1 hτ.2 (fun _ _ => 0) (fun _ _ => 0) hFzero hgzero f u u' w w' hs hs'
end

/-! The finite patch sum solves the original periodic system and agrees with every torus solution. -/

section
section Restrict
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {ν a b c : ℝ} {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
  {A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}

/-- Restricting the final time preserves the physical-plane weak solution. -/
theorem planeWeakSolution_restrict_left (hcb : c ≤ b)
    {f : ∀ i, PlaneHk Set.univ (K i) (h i)}
    {F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
    {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    IsCoupledWeakSolutionPlane ν a c v D K A f F g u w := by
  have hsub : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hcb
  exact ⟨fun i => (hs.1 i).mono hsub,
    fun i => (hs.2.1 i).mono_measure (Measure.restrict_mono hsub le_rfl),
    fun i => ae_restrict_of_ae_restrict_of_subset hsub (hs.2.2.1 i), hs.2.2.2.1,
    fun i t ht φ => hs.2.2.2.2 i t (hsub ht) φ⟩

end Restrict

universe u v w x

variable (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (g₀ : ℝ) (H D Kmax Ks Ls Jm qJ Jchart : ℕ)
    (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (ρold : ℝ)

variable {α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb cMol cOld COld Crat
  Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold}

variable (hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold)




include hprem in
/-- Localized plane solutions produce a torus solution and the exact endpoint periodization
identity for every torus solution from the original datum. -/
theorem preparation_plane_torus_datum (hΛ : 128 ≤ Λ) (hζ : IsFastProfile ζ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (N : ℕ) (hN : 0 < N) (f : ∀ i, TorusHk (K i) (h i)) :
    ∃ (U : (Fin 2 → Fin N) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (W : (Fin 2 → Fin N) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      (∀ j, IsCoupledWeakSolutionPlane ν tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m)
        (streamVel (Φ m)) D K
        (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
        (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i))
        (fun _ _ => 0) (fun _ _ => 0) (U j) (W j)) ∧
      ∃ hmU : ∀ j i, HasRadialPlaneMoments
        (U j i (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m))
        (patchOutputCentre (Φ (m - 1)) hφ tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) N j),
      (∃ (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
        IsCoupledWeakSolutionTorus ν tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m)
          (streamVel (Φ m)) D K
          (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
          f (fun _ _ => 0) (fun _ _ => 0) u w) ∧
      ∀ (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
        IsCoupledWeakSolutionTorus ν tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m)
          (streamVel (Φ m)) D K
          (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
          f (fun _ _ => 0) (fun _ _ => 0) u w →
        ∀ i, u i (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) = ∑ j,
          periodizeRadialPlaneCarrier (U j i (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m))
            (patchOutputCentre (Φ (m - 1)) hφ tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) N j)
            (hmU j i) := by
  classical
  let PP (j : Fin 2 → Fin N) := Classical.choice (existsPreparationPatchPair hprem hΛ hζ hchart hmol N hN j f)
  have hT := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) (show 1 ≤ Λ by omega)
  have hab : tS ≤ tS + 2 * ocTauPP α q Λ m := by linarith only [hT]
  have htp := (PathReduction.preparation_endpoint hprem hΛ).1
  let U0 : ∀ i, ℝ → TorusHk (K i) (h i) := fun i t => ∑ j, (PP j).torus i t
  let W0 : ∀ i, ℝ → TorusHk (K i + 1) (h i) := fun i t => ∑ j, (PP j).torusLift i t
  have hin : (fun i => ∑ j, (PP j).torus i tS) = f := by
    funext i
    exact periodizedPatches_initial_trace hζ N hN K tS (tS + 2 * ocTauPP α q Λ m) hab f
      (fun j => (PP j).plane) (fun j => (PP j).planeLift)
      (fun j => (PP j).torus) (fun j => (PP j).torusLift)
      (fun j => (PP j).plane_sol.2.2.2.1) (fun j => (PP j).pair) i
  have hsum := PathReduction.torusWeakSolution_finset_sum
    (ν := ν) (a := tS) (b := tS + 2 * ocTauPP α q Λ m) (v := streamVel (Φ m))
    (D := D) (K := K)
    (A := edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
    (fun j i => (PP j).torus i tS) (fun _ _ _ => 0) (fun _ _ _ => 0)
    (fun j => (PP j).torus) (fun j => (PP j).torusLift) (fun j => (PP j).torus_sol)
    Finset.univ ⟨(fun _ => (⟨0, hN⟩ : Fin N)), Finset.mem_univ _⟩
  rw [hin] at hsum
  have hs : IsCoupledWeakSolutionTorus ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      f (fun _ _ => 0) (fun _ _ => 0) U0 W0 := by
    simpa only [Finset.sum_const_zero] using hsum
  have hs0 := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left htp.2 hs
  let hmU (j : Fin 2 → Fin N) (i : ι) := radial_moments_recenter _ _
    (patchOutputCentre (Φ (m - 1)) hφ tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) N j)
    ((PP j).moments i _ ⟨htp.1.le, htp.2⟩)
  refine ⟨(fun j => (PP j).plane), (fun j => (PP j).planeLift),
    (fun j => planeWeakSolution_restrict_left htp.2 (PP j).plane_sol), hmU,
    ⟨U0, W0, hs0⟩, ?_⟩
  intro u w hu i
  have he := preparation_torus_unique hprem hΛ hζ hchart hmol
    (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) ⟨htp.1.le, htp.2⟩ f u U0 w W0 hu hs0 i
    (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) ⟨htp.1.le, le_rfl⟩
  apply he.trans
  exact Finset.sum_congr rfl (fun j _ => torusCarrier_eq_periodization _ _ _ (hmU j i)
    ((PP j).pair.2.2.2.1 i _ ⟨htp.1.le, htp.2⟩))
end

end AVRegularity.CycleJointProofs.PlaneTorus
end
