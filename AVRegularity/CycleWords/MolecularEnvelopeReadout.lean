-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.JointDiagonalChainRule
public import AVRegularity.Analysis.Convolution.Kernel.PairedSmoothing
public import AVRegularity.Statements.Intermediate.Families.IsMolecularEnvelope

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The actual scalar Bloch transform is a complex linear isometry. -/

local instance planeScalarBlochComplexLinearMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem scalarFibreSynthesis_complex_smul (c : ℂ) (F : lp (fun _ : Fin 2 → ℤ => ℂ) 2) :
    scalarFibreSynthesis (c • F) = c • scalarFibreSynthesis F := by
  change (mFourierBasis (d := Fin 2)).repr.symm (c • F) =
    c • (mFourierBasis (d := Fin 2)).repr.symm F
  exact (mFourierBasis (d := Fin 2)).repr.symm.map_smul c F

theorem scalarFibreSynthesisLift_complex_smul (μ : Measure (Vec 2)) (c : ℂ)
    (F : Lp (lp (fun _ : Fin 2 → ℤ => ℂ) 2) 2 μ) :
    liftLinearIsometryL2 μ scalarFibreSynthesis (c • F) =
      c • liftLinearIsometryL2 μ scalarFibreSynthesis F := by
  apply Lp.ext
  filter_upwards [liftLinearIsometryL2_ae μ scalarFibreSynthesis (c • F),
    Lp.coeFn_smul c F, liftLinearIsometryL2_ae μ scalarFibreSynthesis F,
    Lp.coeFn_smul c (liftLinearIsometryL2 μ scalarFibreSynthesis F)] with θ h₁ h₂ h₃ h₄
  change (c • F) θ = c • F θ at h₂
  change (c • liftLinearIsometryL2 μ scalarFibreSynthesis F) θ =
    c • liftLinearIsometryL2 μ scalarFibreSynthesis F θ at h₄
  rw [h₁, h₂, h₄, h₃, scalarFibreSynthesis_complex_smul]

theorem planeBlochCoefficients_complex_smul (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (c : ℂ) (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    planeBlochCoefficients a P hP (c • f) = c • planeBlochCoefficients a P hP f := by
  change planeFrequencyFibreL2 a P hP (fourierL2 (c • f)) =
    c • planeFrequencyFibreL2 a P hP (fourierL2 f)
  rw [map_smul, planeFrequencyFibreL2_complex_smul]

theorem planeScalarBlochTransform_complex_smul (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (c : ℂ) (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    planeScalarBlochTransform a P hP (c • f) = c • planeScalarBlochTransform a P hP f := by
  change liftLinearIsometryL2 (volume.restrict (planeFrequencyCell a P)) scalarFibreSynthesis
    (planeBlochCoefficients a P hP (c • f)) =
    c • liftLinearIsometryL2 (volume.restrict (planeFrequencyCell a P)) scalarFibreSynthesis
      (planeBlochCoefficients a P hP f)
  rw [planeBlochCoefficients_complex_smul, scalarFibreSynthesisLift_complex_smul]

def planeScalarBlochComplexIsometry (a : Vec 2) (P : ℝ) (hP : 0 < P) :
    Lp ℂ 2 (volume : Measure (Vec 2)) →ₗᵢ[ℂ]
      Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P)) where
  toFun := planeScalarBlochTransform a P hP
  map_add' := (planeScalarBlochTransform a P hP).map_add
  map_smul' := planeScalarBlochTransform_complex_smul a P hP
  norm_map' := (planeScalarBlochTransform a P hP).norm_map

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Weak measurability for the separable plane Sobolev carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_time_aestronglyMeasurable_of_weak
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : ℕ)
    (F : X → PlaneHk Set.univ K E)
    (hF : ∀ e : PlaneHk Set.univ K E,
      AEStronglyMeasurable (fun t => inner ℝ e (F t)) μ) :
    AEStronglyMeasurable F μ := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : SecondCountableTopology (ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) E) :=
    Lp.SecondCountableTopology
  let : SecondCountableTopology (JetL2 (volume.restrict (Set.univ : Set (Vec 2))) K E) :=
    PiLp.secondCountableTopology 2 _
  exact hilbert_time_aestronglyMeasurable_of_weak μ F hF

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory UnitAddTorus AVRegularity.CoupledEnergyPlane
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Multiplication by an actual torus Fourier mode shifts the actual Fourier coefficients. -/

local instance scalarTorusIntegerModulationMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem scalarTorusFourierMode_memLp_top (m : Fin 2 → ℤ) :
    MemLp (mFourier m) ∞ (volume : Measure (UnitAddTorus (Fin 2))) := by
  apply memLp_top_of_bound (mFourier m).continuous.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro z
  exact (mFourier m).norm_coe_le_norm z |>.trans (le_of_eq mFourier_norm)

def scalarTorusIntegerModulationOperator (m : Fin 2 → ℤ) : ScalarTorusL2 →L[ℂ] ScalarTorusL2 :=
  L2Multiplier.operator (mFourier m) (scalarTorusFourierMode_memLp_top m)

theorem scalarTorusIntegerModulationOperator_ae (m : Fin 2 → ℤ) (u : ScalarTorusL2) :
    scalarTorusIntegerModulationOperator m u =ᵐ[volume] fun z => mFourier m z * u z :=
  L2Multiplier.operator_ae _ _ u

theorem scalarTorusIntegerModulationOperator_fourierCoeff (m n : Fin 2 → ℤ)
    (u : ScalarTorusL2) :
    mFourierCoeff (scalarTorusIntegerModulationOperator m u) n = mFourierCoeff u (n - m) := by
  unfold mFourierCoeff
  apply integral_congr_ae
  filter_upwards [scalarTorusIntegerModulationOperator_ae m u] with z hz
  rw [hz]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← mFourier_add]
  have he : -n + m = -(n - m) := by abel
  rw [he]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! The native whole-plane isometry identifies literal L2 classes across the univ restriction. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
theorem univToPlane_toLp_field (f : Vec 2 → E)
    (hr : MemLp f 2 (volume.restrict Set.univ)) (hv : MemLp f 2 volume) :
    univToPlane (hr.toLp f) = hv.toLp f := by
  apply Lp.ext
  have ha := hr.coeFn_toLp
  simp only [Measure.restrict_univ] at ha
  exact (univToPlane_ae (hr.toLp f)).trans (ha.trans hv.coeFn_toLp.symm)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual product L2 class viewed as a Bochner L2 family of slice classes. -/

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def bochnerL2Curry (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]
    (F : Lp E 2 (μ.prod ν)) : Lp (Lp E 2 ν) 2 μ :=
  (bochnerL2TotalSlice_memLp μ ν (fun x y => F (x, y))
    (Lp.stronglyMeasurable F) (Lp.memLp F)).toLp
      (bochnerL2TotalSlice ν (fun x y => F (x, y)))

theorem bochnerL2Curry_ae (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]
    (F : Lp E 2 (μ.prod ν)) :
    bochnerL2Curry μ ν F =ᵐ[μ] bochnerL2TotalSlice ν (fun x y => F (x, y)) :=
  (bochnerL2TotalSlice_memLp μ ν (fun x y => F (x, y))
    (Lp.stronglyMeasurable F) (Lp.memLp F)).coeFn_toLp

theorem bochnerL2Curry_dist (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]
    (F G : Lp E 2 (μ.prod ν)) :
    dist (bochnerL2Curry μ ν F) (bochnerL2Curry μ ν G) = dist F G := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [L2_dist_sq_integral, L2_dist_sq_integral]
  have hmem : MemLp (fun p : X × Y => F p - G p) 2 (μ.prod ν) :=
    (Lp.memLp F).sub (Lp.memLp G)
  rw [integral_prod _ (hmem.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))]
  apply integral_congr_ae
  filter_upwards [bochnerL2Curry_ae μ ν F, bochnerL2Curry_ae μ ν G,
    bochnerL2Product_memLp_slices μ ν (fun x y => F (x, y)) (Lp.memLp F),
    bochnerL2Product_memLp_slices μ ν (fun x y => G (x, y)) (Lp.memLp G)] with x hx hy hf hg
  rw [hx, hy, ← dist_eq_norm, L2_dist_sq_integral]
  apply integral_congr_ae
  filter_upwards [bochnerL2TotalSlice_ae ν (fun x y => F (x, y)) x hf,
    bochnerL2TotalSlice_ae ν (fun x y => G (x, y)) x hg] with y hy hz
  rw [hy, hz]

theorem bochnerL2Curry_isometry (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)] :
    Isometry (bochnerL2Curry (E := E) μ ν) :=
  Isometry.of_dist_eq (bochnerL2Curry_dist μ ν)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.FastJets
namespace AVRegularity.CycleWords

/-! Diagonal word expansion with a total joint reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_odL_diag_eq {N : ℕ} {W : Vec 2 → Vec 2 → E} (hW : ContDiff ℝ (N : ℕ) (Function.uncurry W)) (ρ e : ℝ) :
    ∀ l : List (Fin 2), l.length ≤ N →
      odL l (fun x => W (ρ⁻¹ • x) (e⁻¹ • x)) =
        fun x => ((splitTerms l).map fun p => diagTerm W ρ e p x).sum := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro _
    funext x
    simp [splitTerms, diagTerm, termCoef, mixL]
  | append_singleton l i ih =>
    intro hl
    have hl' : l.length < N := by simpa using hl
    rw [odL_append_singleton, ih hl'.le]
    funext x
    have hdiff : ∀ p ∈ splitTerms l, DifferentiableAt ℝ (diagTerm W ρ e p) x := fun p hp =>
      joint_differentiableAt_diagTerm hW ρ e p (by have := splitTerms_length_sum l p hp; omega) x
    obtain ⟨-, hfd⟩ := hasFDerivAt_list_sum_map (splitTerms l) (diagTerm W ρ e) x hdiff
    rw [hfd, list_sum_clm_apply, splitTerms_append_singleton, list_sum_flatMap]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    rw [joint_fderiv_diagTerm hW ρ e p (by have := splitTerms_length_sum l p hp; omega) x i]
    simp [splitStep, diagTerm, termCoef, smul_add, smul_smul, pow_succ]
    congr 1 <;> congr 1 <;> ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Every finite coordinate projection belongs to the lattice rearrangement range. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem planeFrequency_coordinate_product_mem_range (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Lp (lp (fun _ : Fin 2 → ℤ => E) 2) 2 (volume.restrict (planeFrequencyCell a P)))
    (m : Fin 2 → ℤ) :
    ((lp.singleContinuousLinearMap ℝ (fun _ : Fin 2 → ℤ => E) 2 m).comp
      (lp.evalCLM ℝ (fun _ : Fin 2 → ℤ => E) 2 m)).compLp f ∈
      Set.range (planeFrequencyL2Isometry a P hP) := by
  let L := lp.singleContinuousLinearMap ℝ (fun _ : Fin 2 → ℤ => E) 2 m
  let R := lp.evalCLM ℝ (fun _ : Fin 2 → ℤ => E) 2 m
  have he : (L.comp R).compLp f = L.compLp (R.compLp f) := by
    apply Lp.ext
    filter_upwards [(L.comp R).coeFn_compLp f, L.coeFn_compLp (R.compLp f),
      R.coeFn_compLp f] with θ hθ hL hR
    rw [hθ, hL, hR]
    rfl
  rw [he]
  exact planeFrequencyL2Isometry_single_mem_range a P hP (R.compLp f) m

theorem planeFrequency_projection_mem_range (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Lp (lp (fun _ : Fin 2 → ℤ => E) 2) 2 (volume.restrict (planeFrequencyCell a P)))
    (s : Finset (Fin 2 → ℤ)) :
    (lpCoordinateProjection s).compLp f ∈ Set.range (planeFrequencyL2Isometry a P hP) := by
  let B := ContinuousLinearMap.id ℝ
    (lp (fun _ : Fin 2 → ℤ => E) 2 →L[ℝ] lp (fun _ : Fin 2 → ℤ => E) 2)
  have he : (lpCoordinateProjection s).compLp f =
      ∑ m ∈ s, ((lp.singleContinuousLinearMap ℝ (fun _ : Fin 2 → ℤ => E) 2 m).comp
        (lp.evalCLM ℝ (fun _ : Fin 2 → ℤ => E) 2 m)).compLp f := by
    change B.compLpL₂ 2 (volume.restrict (planeFrequencyCell a P))
      (lpCoordinateProjection s) f = _
    unfold lpCoordinateProjection
    rw [map_sum]
    simp only [sum_apply, ContinuousLinearMap.compLpL₂_apply_apply, B,
      ContinuousLinearMap.id_apply]
  rw [he]
  exact (planeFrequencyL2Isometry a P hP).toLinearMap.range.sum_mem
    (fun m _ => planeFrequency_coordinate_product_mem_range a P hP f m)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter TopologicalSpace
namespace AVRegularity.CycleWords

/-! Every Bochner L2 field has an actual joint product L2 realization. -/

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem bochnerL2Curry_simple (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]
    (s : SimpleFunc X (Lp E 2 ν)) (hs : MemLp s 2 μ) :
    bochnerL2Curry μ ν
      ((bochnerSimpleJoint_memLp μ ν s hs).toLp (fun p : X × Y => s p.1 p.2)) =
      hs.toLp s := by
  let hj := bochnerSimpleJoint_memLp μ ν s hs
  let F := hj.toLp (fun p : X × Y => s p.1 p.2)
  have ha : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, F (x, y) = s x y :=
    Measure.ae_ae_of_ae_prod hj.coeFn_toLp
  apply Lp.ext
  filter_upwards [bochnerL2Curry_ae μ ν F, hs.coeFn_toLp, ha,
    bochnerL2Product_memLp_slices μ ν (fun x y => F (x, y)) (Lp.memLp F)]
    with x hx hs' ha' hmem
  rw [hx, hs']
  apply Lp.ext
  filter_upwards [bochnerL2TotalSlice_ae ν (fun x y => F (x, y)) x hmem, ha']
    with y hy ha''
  exact hy.trans ha''

theorem bochnerL2Curry_surjective (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)] [CompleteSpace E] :
    Function.Surjective (bochnerL2Curry (E := E) μ ν) := by
  have his := bochnerL2Curry_isometry (E := E) μ ν
  have hc : IsClosed (range (bochnerL2Curry (E := E) μ ν)) :=
    his.antilipschitzWith.isClosed_range his.uniformContinuous
  intro f
  have hd := Lp.simpleFunc.denseRange (E := Lp E 2 ν) (p := 2) (μ := μ)
    (by norm_num : (2 : ENNReal) ≠ ⊤)
  change f ∈ range (bochnerL2Curry (E := E) μ ν)
  apply hd.induction_on (p := fun z => z ∈ range (bochnerL2Curry (E := E) μ ν)) f hc
  intro q
  let s := Lp.simpleFunc.toSimpleFunc q
  have hs : MemLp s 2 μ := Lp.simpleFunc.memLp q
  have he : hs.toLp s = (q : Lp (Lp E 2 ν) 2 μ) := by
    apply Lp.ext
    filter_upwards [hs.coeFn_toLp, Lp.simpleFunc.toSimpleFunc_eq_toFun q] with x hx hq
    exact hx.trans hq
  refine ⟨(bochnerSimpleJoint_memLp μ ν s hs).toLp (fun p : X × Y => s p.1 p.2), ?_⟩
  exact (bochnerL2Curry_simple μ ν s hs).trans he

end AVRegularity.CycleWords
end
end

section
public section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Classical cell Sobolev norms obey the triangle inequality and constant scalar homogeneity. -/

theorem cellSobolevNorm_add_le (j : ℕ) (f g : Vec 2 → ℂ)
    (hf : ContDiff ℝ (j : ℕ∞) f) (hg : ContDiff ℝ (j : ℕ∞) g) :
    cellSobolevNorm j (f + g) ≤ cellSobolevNorm j f + cellSobolevNorm j g := by
  unfold cellSobolevNorm cellL2Norm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b hb
  have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
  have hfb : ContDiff ℝ (b : ℕ∞) f := hf.of_le (by exact_mod_cast hbj)
  have hgb : ContDiff ℝ (b : ℕ∞) g := hg.of_le (by exact_mod_cast hbj)
  have hadd : ContDiff ℝ (b : ℕ∞) (f + g) := hfb.add hgb
  rw [eLpNorm_norm _ (ContDiff.continuous_iteratedFDeriv' hadd).aestronglyMeasurable.restrict,
    iteratedFDeriv_add hfb hgb,
    eLpNorm_norm _ (ContDiff.continuous_iteratedFDeriv' hfb).aestronglyMeasurable.restrict,
    eLpNorm_norm _ (ContDiff.continuous_iteratedFDeriv' hgb).aestronglyMeasurable.restrict]
  exact eLpNorm_add_le (by norm_num)

theorem cellSobolevNorm_const_smul (j : ℕ) (c : ℂ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (j : ℕ∞) f) :
    cellSobolevNorm j (c • f) = ENNReal.ofReal ‖c‖ * cellSobolevNorm j f := by
  unfold cellSobolevNorm cellL2Norm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hfb : ContDiff ℝ (b : ℕ∞) f := hf.of_le
    (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hb))
  have he : iteratedFDeriv ℝ b (c • f) = c • iteratedFDeriv ℝ b f := by
    funext x
    exact iteratedFDeriv_const_smul_apply hfb.contDiffAt
  have hsm : ContDiff ℝ (b : ℕ∞) (c • f) := hfb.const_smul c
  rw [eLpNorm_norm _ (ContDiff.continuous_iteratedFDeriv' hsm).aestronglyMeasurable.restrict,
    he]
  change eLpNorm (c • iteratedFDeriv ℝ b f) 2 (volume.restrict AVenhance.unitCube) = _
  rw [eLpNorm_norm _ (ContDiff.continuous_iteratedFDeriv' hfb).aestronglyMeasurable.restrict]
  simpa only [ofReal_norm] using eLpNorm_const_smul c (iteratedFDeriv ℝ b f) 2 (volume.restrict AVenhance.unitCube)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! Priced normal-form steps retain constituent amplitudes through multiplication and differentiation. -/

variable {I V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

inductive FrequencyNormalPriceStep (I V E : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] where
  | multiply (A : V → E →L[ℝ] E) (Θ : ℝ) (C : ℕ → ℝ)
  | differentiate (word : List I)

def FrequencyNormalPriceStep.step (s : FrequencyNormalPriceStep I V E) : FrequencyOperatorStep I V E :=
  match s with
  | .multiply A _ _ => .multiply A
  | .differentiate w => .differentiate w

def frequencyJetConvolution (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * B (n - i)

def FrequencyNormalPriceStep.price (s : FrequencyNormalPriceStep I V E)
    (direction : I → V) (Θ : ℝ) (B : ℕ → ℝ) : ℝ × (ℕ → ℝ) :=
  match s with
  | .multiply _ ΘA CA => (ΘA * Θ, frequencyJetConvolution CA B)
  | .differentiate w => (Θ, frequencyOrderedJetPrice direction w B)

def FrequencyNormalPriceStep.valid (s : FrequencyNormalPriceStep I V E) (x : V) : Prop :=
  match s with
  | .multiply A Θ C => ContDiff ℝ (⊤ : ℕ∞) A ∧ 0 ≤ Θ ∧
      (∀ n, 0 ≤ C n) ∧ (∀ n, ‖iteratedFDeriv ℝ n A x‖ ≤ Θ * C n)
  | .differentiate _ => True

theorem FrequencyNormalPriceStep.price_nonneg (s : FrequencyNormalPriceStep I V E)
    (direction : I → V) (x : V) (hs : s.valid x)
    (Θ : ℝ) (B : ℕ → ℝ) (hΘ : 0 ≤ Θ) (hB : ∀ n, 0 ≤ B n) :
    0 ≤ (s.price direction Θ B).1 ∧ ∀ n, 0 ≤ (s.price direction Θ B).2 n := by
  cases s with
  | multiply A ΘA CA =>
    refine ⟨mul_nonneg hs.2.1 hΘ, fun n => ?_⟩
    change 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CA i * B (n - i)
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (by positivity) (hs.2.2.1 i)) (hB (n - i))
  | differentiate w => exact ⟨hΘ, frequencyOrderedJetPrice_nonneg direction w B hB⟩

theorem FrequencyNormalPriceStep.smooth (s : FrequencyNormalPriceStep I V E)
    (x : V) (hs : s.valid x) : s.step.smooth := by
  cases s with
  | multiply A Θ C => exact hs.1
  | differentiate w => trivial

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter TopologicalSpace
namespace AVRegularity.CycleWords

/-! A genuine joint realization of every Bochner field, with exact slices and norm. -/

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def bochnerL2Joint (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)] [CompleteSpace E]
    (u : Lp (Lp E 2 ν) 2 μ) : Lp E 2 (μ.prod ν) :=
  Classical.choose (bochnerL2Curry_surjective μ ν u)

theorem bochnerL2Curry_joint (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)] [CompleteSpace E]
    (u : Lp (Lp E 2 ν) 2 μ) : bochnerL2Curry μ ν (bochnerL2Joint μ ν u) = u :=
  Classical.choose_spec (bochnerL2Curry_surjective μ ν u)

theorem bochnerL2Joint_slices (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)] [CompleteSpace E]
    (u : Lp (Lp E 2 ν) 2 μ) :
    ∀ᵐ x ∂μ, (u x : Y → E) =ᵐ[ν] fun y => bochnerL2Joint μ ν u (x, y) := by
  let F := bochnerL2Joint μ ν u
  have hc : bochnerL2Curry μ ν F = u := bochnerL2Curry_joint μ ν u
  filter_upwards [bochnerL2Curry_ae μ ν F,
    bochnerL2Product_memLp_slices μ ν (fun x y => F (x, y)) (Lp.memLp F)] with x hx hm
  rw [hc] at hx
  rw [hx]
  exact bochnerL2TotalSlice_ae ν (fun x y => F (x, y)) x hm

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! The full differential normal form retains the product of all original amplitudes. -/

section
variable {I V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def FrequencyNormalPriceStep.amplitude (s : FrequencyNormalPriceStep I V E) : ℝ :=
  match s with
  | .multiply _ Θ _ => Θ
  | .differentiate _ => 1
end

/-! Normal-form prices consume only the fixed frequency reserve plus the literal differential orders. -/

section
variable {I V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def FrequencyNormalPriceStep.reserve (s : FrequencyNormalPriceStep I V E) : ℕ :=
  match s with
  | .multiply _ _ _ => 0
  | .differentiate w => w.length
end

/-! Admissible physical marks give separated cell-time marks of exactly the same cardinality. -/

theorem interior_cell_marks {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (ν B Θ θ ta T : ℝ) (hL : 0 < ocEll q Λ m ν ^ 2)
    (hadm : IsOCAdmissibleInterval α q Λ ζ m ν B Θ θ ta T) :
    ∃ marks : Fin 2 → Finset ℝ,
      (∀ j, (1 - Real.exp (-2)) / 288 * (T / ocEll q Λ m ν ^ 2) / θ ≤
        ((marks j).card : ℝ)) ∧
      (∀ j, ∀ a ∈ marks j, ta / ocEll q Λ m ν ^ 2 ≤ a ∧
        a + θ ≤ (ta + T) / ocEll q Λ m ν ^ 2) ∧
      (∀ j, ∀ a ∈ marks j, ∀ b ∈ marks j, a ≠ b →
        a + θ ≤ b ∨ b + θ ≤ a) ∧
      ∀ j, ∀ a ∈ marks j, ∃ k : ℤ,
        k % 4 = (if j = 0 then 3 else 1) ∧
        IsOCCompleteCore α q Λ m (ocLabel α q Λ m k) k ∧
        ((k : ℝ) - 1 / 3) * ocTau α q Λ m ≤ ocEll q Λ m ν ^ 2 * a ∧
        ocEll q Λ m ν ^ 2 * (a + θ) ≤ ((k : ℝ) + 1 / 3) * ocTau α q Λ m := by
  classical
  choose physical hn hin hsep using hadm.2.2.2
  let L := ocEll q Λ m ν ^ 2
  let scale : ℝ → ℝ := fun a => a / L
  have hinj : Function.Injective scale := by
    intro a b hab
    exact (div_left_inj' hL.ne').mp hab
  have hscale (a : ℝ) : L * scale a = a := by
    dsimp only [scale]
    exact mul_div_cancel₀ a hL.ne'
  have hscale_add (a : ℝ) : L * (scale a + θ) = a + θ * L := by
    rw [mul_add, hscale, mul_comm L θ]
  refine ⟨fun j => (physical j).image scale, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [Finset.card_image_of_injective _ hinj]
    exact hn j
  · intro j a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hlo, hhi, _⟩ := hin j x hx
    refine ⟨div_le_div_of_nonneg_right hlo hL.le, ?_⟩
    apply (le_div_iff₀ hL).mpr
    rw [mul_comm, hscale_add]
    exact hhi
  · intro j a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    have hxy : x ≠ y := fun he => hab (congrArg scale he)
    rcases hsep j x hx y hy hxy with h | h
    · left
      apply (mul_le_mul_iff_right₀ hL).mp
      change L * (scale x + θ) ≤ L * scale y
      rw [hscale_add, hscale]
      exact h
    · right
      apply (mul_le_mul_iff_right₀ hL).mp
      change L * (scale y + θ) ≤ L * scale x
      rw [hscale_add, hscale]
      exact h
  · intro j a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨_, _, k, hk, hcore, hlo, hhi⟩ := hin j x hx
    refine ⟨k, hk, hcore, ?_, ?_⟩
    · change _ ≤ L * scale x
      rw [hscale]
      exact hlo
    · change L * (scale x + θ) ≤ _
      rw [hscale_add]
      exact hhi

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Each original constituent and word retains its positive molecular envelope budget. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem molecularEnvelope_constituent_term_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (dom : F.Domain) (ν e E ρ : ℝ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (hf : IsMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (j : ℕ) (hj : j ≤ J) :
    ENNReal.ofReal (Real.sqrt (π u / π v)) * ENNReal.ofReal ‖(F.identity v u γ).map‖ *
      (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
          (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
            ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) ≤
      ENNReal.ofReal (C j * (E ^ j)⁻¹ * b v u) := by
  let term : ∀ γ : F.Γ v u, ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ≥0∞ := fun γ d I =>
    molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
        (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
          ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))
  have hb := hf.2 v u j hj
  have hh := positive_constituent_term_le
    (ENNReal.ofReal (Real.sqrt (π u / π v)))
    (fun γ : F.Γ v u => ENNReal.ofReal ‖(F.identity v u γ).map‖)
    (fun γ => Finset.Icc 2 (F.identity v u γ).maxOrder) term γ d hd I
  exact hh.trans hb

end AVRegularity.CycleWords
end
end
