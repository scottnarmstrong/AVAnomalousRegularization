-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.BufferedHigherTrace
import AVRegularity.KernelEnergy.TorusKernelStrongTraceExistence
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! A separable constant-preservation input for the common preparation route.
The source orders start at two, so spatially constant component data create
no coupling flux. The actual native equation and uniqueness must identify
the already chosen trace with these constants; no replacement evolution is
permitted.

The degenerate cases are included: empty families give equality of empty functions, singleton
families allow diagonal identities, D=2 still has a differentiated source, and a
one-point time window gives the actual initial trace. Zero/constants,
identity geometry and an edgeless seed need no division or extra hypothesis. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*}
  [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
  [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
  [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
  {a b ρ ν : ℝ} {D : ℕ}

/-- Every realized native trace fixes componentwise spatial constants on
its whole solution window, independently of the mass used to certify it. -/
def NativeConstantTraceStatement
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (c : ℝ) : Prop :=
  IsAdmissibleStream φ →
  ∀ L, NativeEnergyPathRealizes P φ c L →
  ∀ (f : ∀ i, TorusHk 0 (h i)) (cv : ∀ i, h i),
    (∀ i, (f i).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
      fun _ => cv i) →
    ∀ t : Set.Icc a b, (L f).1 t = f
end

/-! The physical weighted path seminorm uses the same graph projection as the
actual kernel source, even on off-graph ambient inputs. The trace is one
whole-family supremum; the gradient is one whole-family time L2 norm.

The degenerate cases are included: empty and singleton families, zero data or edges, identity
geometry, order zero and degenerate windows use these same fixed maps.
No division by a datum norm or choice of a linear time representative occurs. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationResponseNativeNormed preparationResponseNativeModule
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

local instance preparationWeightedCarrierSMul (i : ι) : SMul ℝ (TorusHk 0 (h i)) :=
  (preparationResponseNativeModule (E := h i) 0).toDistribMulAction.toDistribSMul.toSMul
local instance preparationWeightedLowSMul : SMul ℝ (∀ i, TorusHk 0 (h i)) := Pi.instSMul
local instance preparationWeightedLowSpace : NormedSpace ℝ (∀ i, TorusHk 0 (h i)) :=
  Pi.normedSpace
/-- The kernel's fixed native graph projection followed by the weighted gradient. -/
def preparationWeightedGradientCLM (ρ : ℝ) (π : ι → ℝ) :
    CoupledHighHilbert (h := h) (fun _ => 0) →L[ℝ]
      PiLp 2 (fun i => JetL2 (volume.restrict unitCube) 0 (PiLp 2 (fun _ : Fin 2 => h i))) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun i => JetL2 (volume.restrict unitCube) 0 (PiLp 2 (fun _ : Fin 2 => h i)))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (Real.sqrt ((π i)⁻¹) • KernelEnergy.torusFactorialGradientReadout (E := h i) ρ 0).comp
        ((KernelEnergy.torusGraphProjection (E := h i) 1).comp
          (PiLp.proj (𝕜 := ℝ) 2
            (fun i => JetL2 (volume.restrict unitCube) 1 (h i)) i))))

omit [Fintype ι] [DecidableEq ι] in
/-- On arbitrary ambient inputs the readout uses exactly the kernel's graph projection. -/
theorem preparation_weighted_gradient_apply (ρ : ℝ) (π : ι → ℝ)
    (U : CoupledHighHilbert (h := h) (fun _ => 0)) :
    preparationWeightedGradientCLM ρ π U = massWeightedCarrierCLM (fun _ => 0) ρ π
      (fun i => torusGradientTensor
        (KernelEnergy.TorusKernelOperator.ambientCarrierCLM (h := h) (k := 0) U i)) := by
  apply WithLp.ofLp_injective 2
  funext i
  change Real.sqrt ((π i)⁻¹) • KernelEnergy.torusFactorialGradientReadout ρ 0
    (KernelEnergy.torusGraphProjection 1 (U i)) = _
  simp only [KernelEnergy.torusFactorialGradientReadout_apply, massWeightedCarrierCLM_apply]
  rfl

omit [DecidableEq ι] in
/-- Exact gradient square of the projected input, including off-graph inputs. -/
theorem preparation_weighted_gradient_normSq (ρ : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (U : CoupledHighHilbert (h := h) (fun _ => 0)) :
    ‖preparationWeightedGradientCLM ρ π U‖ ^ 2 = massGradNormSq ρ π
      (fun i => (KernelEnergy.TorusKernelOperator.ambientCarrierCLM (h := h) (k := 0) U i).val) := by
  rw [preparation_weighted_gradient_apply, massWeightedCarrierCLM_normSq _ _ _ hπ]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun x : ℝ => (π i)⁻¹ * x)
    (torusGradientTensor_factorialNormSq ρ _))

omit [Fintype ι] [DecidableEq ι] in
/-- On actual higher carriers the gradient readout is the genuine weighted gradient. -/
theorem preparation_weighted_gradient_graph (ρ : ℝ) (π : ι → ℝ)
    (W : ∀ i, TorusHk 1 (h i)) :
    preparationWeightedGradientCLM ρ π
      (coupledCarrierHighJets (fun _ => 0) W) =
      massWeightedCarrierCLM (fun _ => 0) ρ π (fun i => torusGradientTensor (W i)) := by
  apply WithLp.ofLp_injective 2
  funext i
  change Real.sqrt ((π i)⁻¹) • KernelEnergy.torusFactorialGradientReadout ρ 0
    (KernelEnergy.torusGraphProjection 1 (W i).val) = _
  rw [KernelEnergy.torusGraphProjection_carrier]
  simp only [KernelEnergy.torusFactorialGradientReadout_apply, massWeightedCarrierCLM_apply]
  rfl

omit [DecidableEq ι] in
/-- Exact mass-gradient square `massGradNormSq` on every actual higher carrier. -/
theorem preparation_weighted_gradient_graph_normSq (ρ : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (W : ∀ i, TorusHk 1 (h i)) :
    ‖preparationWeightedGradientCLM ρ π (coupledCarrierHighJets (fun _ => 0) W)‖ ^ 2 =
      massGradNormSq ρ π (fun i => (W i).val) := by
  rw [preparation_weighted_gradient_graph, massWeightedCarrierCLM_normSq _ _ _ hπ]
  exact Finset.sum_congr rfl (fun i _ =>
    congrArg (fun x : ℝ => (π i)⁻¹ * x) (torusGradientTensor_factorialNormSq ρ (W i)))

/-- Weighted physical energy on the common whole-window/post-buffer carrier. -/
def preparationWeightedPathEnergy (ρ : ℝ) (π : ι → ℝ) (ν a b c : ℝ) :
    Seminorm ℝ (PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c) :=
  preparationPathEnergy (V := CoupledHighHilbert (h := h) (fun _ => 0))
    a b c (massWeightedCarrierCLM (E := h) (fun _ => 0) ρ π)
    (preparationWeightedGradientCLM (h := h) ρ π) ν

omit [DecidableEq ι] in
/-- The exact mass norm of each time trace has leading constant one. -/
theorem preparation_weighted_trace_le_energy (ρ : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (ν a b c : ℝ)
    (x : PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c) (t : Set.Icc a b) :
    Real.sqrt (massNormSq ρ π (fun i => (x.1 t i).val)) ≤
      preparationWeightedPathEnergy ρ π ν a b c x := by
  rw [← massWeightedCarrierCLM_norm (fun _ => 0) ρ π hπ]
  exact preparation_path_trace_le_energy (massWeightedCarrierCLM (E := h) (fun _ => 0) ρ π)
    (preparationWeightedGradientCLM (h := h) ρ π) ν x t

omit [DecidableEq ι] in
/-- The ambient gradient class norm is its actual squared time integral. -/
theorem preparation_weighted_gradient_class_normSq (ρ : ℝ) (π : ι → ℝ) (c b : ℝ)
    (U : CoupledHighTime (h := h) (fun _ => 0) c b) :
    ‖(preparationWeightedGradientCLM ρ π).compLpL 2
      (volume.restrict (Set.Icc c b)) U‖ ^ 2 =
      ∫ t in Set.Icc c b, ‖preparationWeightedGradientCLM ρ π (U t)‖ ^ 2 := by
  let A := preparationWeightedGradientCLM (h := h) ρ π
  have hm := A.comp_memLp' (Lp.memLp U)
  have he : A.compLpL 2 (volume.restrict (Set.Icc c b)) U =
      hm.toLp (fun t => A (U t)) := by
    apply Lp.ext
    exact (A.coeFn_compLpL U).trans hm.coeFn_toLp.symm
  rw [he, timeL2_toLp_norm_square]

omit [DecidableEq ι] in
/-- The post-buffer gradient L2 class is the actual mass-gradient integral. -/
theorem preparation_weighted_gradient_time_normSq (ρ : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (c b : ℝ)
    (U : CoupledHighTime (h := h) (fun _ => 0) c b)
    (W : ∀ i, ℝ → TorusHk 1 (h i))
    (hU : U =ᵐ[volume.restrict (Set.Icc c b)]
      fun t => coupledCarrierHighJets (fun _ => 0) (fun i => W i t)) :
    ‖(preparationWeightedGradientCLM ρ π).compLpL 2
      (volume.restrict (Set.Icc c b)) U‖ ^ 2 =
      ∫ t in Set.Icc c b, massGradNormSq ρ π (fun i => (W i t).val) := by
  let A := preparationWeightedGradientCLM (h := h) ρ π
  have hm := A.comp_memLp' (Lp.memLp U)
  have he : A.compLpL 2 (volume.restrict (Set.Icc c b)) U =
      hm.toLp (fun t => A (U t)) := by
    apply Lp.ext
    exact (A.coeFn_compLpL U).trans hm.coeFn_toLp.symm
  rw [he, timeL2_toLp_norm_square]
  apply integral_congr_ae
  filter_upwards [hU] with t ht
  rw [ht]
  exact preparation_weighted_gradient_graph_normSq ρ π hπ _

/-- The actual scalar source map on the physical ambient energy carrier. -/
abbrev PreparationKernelSourceMap (a b : ℝ) :=
  CoupledHighTime (h := h) (fun _ => 0) a b →ₗ[ℝ]
    PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b a
end

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The scalar zero-data response to the actual kernel source, as one linear
continuous-trace/ambient-higher energy path. The forcing is a genuine Sobolev
carrier at every time. Its linear time class feeds the scalar response;
uniqueness removes arbitrary choices of representatives.

Zero forcing, empty or singleton families, edgeless seeds and zero-length windows preserve
the zero initial value. This is the actual kernel insertion before its weighted energy bound,
not a new PDE existence theorem or a linear representative section. -/

attribute [local instance] preparationResponseNativeNormed preparationResponseNativeModule
  preparationScalarFluxModule preparationScalarFluxSMul
  preparationClassFluxAdd preparationClassFluxMonoid preparationClassFluxModule
  preparationClassDatumAdd preparationClassDatumMonoid preparationClassDatumModule preparationClassDatumSMul
  preparationNativeFamilyNormed preparationNativeFamilyModule preparationNativeContinuousModule

/-- Window-pointwise replacement of a scalar trace preserves its actual forced row. -/
theorem preparation_scalar_trace_congr {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {ν a b : ℝ} (hab : a ≤ b) {v : ℝ → Vec 2 → Vec 2} {f : TorusHk 0 E}
    {F : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => E))}
    {u u' : ℝ → TorusHk 0 E} {w : ℝ → TorusHk 1 E}
    (hs : IsTorusForcedRow ν a b v 2 0 f F (fun _ => 0) u w)
    (hu : ∀ t ∈ Set.Icc a b, u' t = u t) :
    IsTorusForcedRow ν a b v 2 0 f F (fun _ => 0) u' w := by
  refine ⟨fun i => (hs.1 i).congr (fun t ht => hu t ht), hs.2.1, ?_, ?_, ?_⟩
  · intro i
    filter_upwards [hs.2.2.1 i, ae_restrict_mem measurableSet_Icc] with t hwt ht
    exact hwt.trans (hu t ht).symm
  · intro i
    exact (hu a ⟨le_rfl, hab⟩).trans (hs.2.2.2.1 i)
  · intro i t ht φ
    simpa only [hu t ht] using hs.2.2.2.2 i t ht φ

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {a b ρ ν : ℝ}

/-- The actual scalar equations and higher class realized by a family path map. -/
def ScalarFamilyEnergyPathRealizes {X : Type*} [AddCommGroup X] [Module ℝ X]
    (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (x : ∀ i, X → PreparationScalarDatum (h i) 0 a b)
    (J : X →ₗ[ℝ] PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b a) : Prop :=
    ∀ U, (J U).1 ⟨a, le_rfl, hab⟩ = (fun i => (x i U).1) ∧
      ∃ w : ∀ i, ℝ → TorusHk 1 (h i),
        (∀ i, IsTorusForcedRow ν a b v 2 0 (x i U).1 (x i U).2.val (fun _ => 0)
          (fun t => (J U).1 (Set.projIcc a b hab t) i) (w i)) ∧
        ((J U).2 =ᵐ[volume.restrict (Set.Icc a b)]
          fun t => coupledCarrierHighJets (fun _ => 0) (fun i => w i t))

/-- A linear family of actual scalar data classes has one physical energy response.
The actual representatives need not depend linearly on the input. -/
def ScalarFamilyEnergyPathStatement {X : Type*} [AddCommGroup X] [Module ℝ X]
    (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (x : ∀ i, X → PreparationScalarDatum (h i) 0 a b) : Prop :=
  ∃ J : X →ₗ[ℝ] PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b a,
    ScalarFamilyEnergyPathRealizes (ν := ν) hab v x J

/-- Time-class linearity gives the physical scalar family response for both
homogeneous initial evolution and zero-data kernel insertion. -/
theorem scalar_family_energy_path_of_drift {X : Type*} [AddCommGroup X] [Module ℝ X]
    {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν)
    (K : ∀ i, X →ₗ[ℝ] PreparationScalarClassDatum (h i) 0 a b)
    (x : ∀ i, X → PreparationScalarDatum (h i) 0 a b)
    (hx : ∀ i U, preparationScalarDatumClass (E := h i) 0 a b (x i U) = K i U) :
    ScalarFamilyEnergyPathStatement (ν := ν) hab v x := by
  classical
  let R (i : ι) := Classical.choice (preparation_scalar_response_exists (E := h i)
    hd hab hρ hν (Nat.zero_le Kmax))
  choose A B hc hi ht hh using fun i => preparation_scalar_time_class_response
    hd hab hρ hν (Nat.zero_le Kmax) (R i)
  let L := LinearMap.pi (fun i => (A i).comp (K i))
  let W := fun U i => (R i).gradient (x i U)
  have htrace : ∀ U i, ∀ t ∈ Set.Icc a b,
      L U i t = (R i).trace (x i U) t := by
    intro U i t ht'
    have he := ht i (x i U) t ht'
    rw [hx i U] at he
    exact he
  let V := preparation_native_continuous_trace L (fun U i => hc i (K i U))
  have ha : ∀ U i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncateTorusHk (Nat.zero_le 1) (W U i t) = L U i t := by
    intro U i
    filter_upwards [(R i).solution (x i U) |>.2.2.1 0,
      ae_restrict_mem measurableSet_Icc] with t hw ht'
    exact hw.trans (htrace U i t ht').symm
  have hob1 := preparation_native_higher_time_class a b L W
    (fun U i => (R i).gradient_memLp (x i U)) ha
  obtain ⟨H, hH⟩ := hob1
  refine ⟨V.prod H, fun U => ⟨?_, W U, ?_, hH U⟩⟩
  · funext i
    exact (hi i (K i U)).trans (congrArg Prod.fst (hx i U)).symm
  · intro i
    apply preparation_scalar_trace_congr hab ((R i).solution (x i U))
    intro t ht'
    change L U i (Set.projIcc a b hab t) = (R i).trace (x i U) t
    rw [Set.projIcc_of_mem hab ht']
    exact htrace U i t ht'

/-- Homogeneous scalar evolution is the initial-data instance of the same family response. -/
theorem scalar_homogeneous_energy_path_of_drift
    {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) :
    ScalarFamilyEnergyPathStatement (ν := ν) hab v
      (fun i (f : ∀ j, TorusHk 0 (h j)) => (f i, 0)) := by
  let K : ∀ i, (∀ j, TorusHk 0 (h j)) →ₗ[ℝ] PreparationScalarClassDatum (h i) 0 a b :=
    fun i => (LinearMap.proj i).prod 0
  exact scalar_family_energy_path_of_drift hd hab hρ hν K _
    (fun i f => preparation_scalar_zero_forcing_class 0 a b (f i))

variable {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {D : ℕ}
variable (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)

/-- The ambient scalar datum depends linearly on the higher kernel-input class. -/
def preparationKernelScalarClassDatum (i : ι) :
    CoupledHighTime (h := h) (fun _ => 0) a b →ₗ[ℝ]
      PreparationScalarClassDatum (h i) 0 a b :=
  (0 : CoupledHighTime (h := h) (fun _ => 0) a b →ₗ[ℝ] TorusHk 0 (h i)).prod
    (preparationAmbientKernelTimeFlux P i).toLinearMap

/-- One actual scalar response before the input class or its weight is chosen. -/
def ScalarKernelEnergyPathStatement (v : ℝ → Vec 2 → Vec 2) : Prop :=
  ∃ J : CoupledHighTime (h := h) (fun _ => 0) a b →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b a,
    ∀ U, (J U).1 ⟨a, le_rfl, P.htime⟩ = 0 ∧
      ∃ w : ∀ i, ℝ → TorusHk 1 (h i),
        (∀ i, IsTorusForcedRow ν a b v 2 0 0
          (fun t => P.clampedAmbientFluxCLM i t (U t)) (fun _ => 0)
          (fun t => (J U).1 (Set.projIcc a b P.htime t) i) (w i)) ∧
        ((J U).2 =ᵐ[volume.restrict (Set.Icc a b)]
          fun t => coupledCarrierHighJets (fun _ => 0) (fun i => w i t))

/-- The scalar time-class response realizes the actual kernel source in the energy carrier. -/
theorem scalar_kernel_energy_path_of_drift {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ}
    (hd : TorusDriftData ν ρ a b v Kmax) : ScalarKernelEnergyPathStatement P v := by
  have hob2 := scalar_family_energy_path_of_drift hd P.htime P.radius_pos P.diffusivity_pos
    (preparationKernelScalarClassDatum P) (preparationKernelScalarDatum P)
    (preparation_kernel_scalar_datum_class P)
  obtain ⟨J, hJ⟩ := hob2
  exact ⟨J, hJ⟩

/-- Two actual scalar solutions, driven respectively by the full initial datum
and the ambient actual kernel source, reconstruct the native kernel trace. -/
theorem preparation_kernel_scalar_two_trace {k : ℕ}
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
    {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ}
    (hd : TorusDriftData ν ρ a b v Kmax) (hk : k ≤ Kmax)
    {f : ∀ i, TorusHk k (h i)} {u : ∀ i, ℝ → TorusHk k (h i)}
    {w : ∀ i, ℝ → TorusHk (k + 1) (h i)}
    {y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)}
    (hs : IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S f 0 0 u w y)
    (U : CoupledHighTime (h := h) (fun _ => k) a b)
    (hU : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i, (w i t).val = U t i)
    {u₀ uk : ∀ i, ℝ → TorusHk k (h i)}
    {w₀ wk : ∀ i, ℝ → TorusHk (k + 1) (h i)}
    (hs₀ : ∀ i, IsTorusForcedRow ν a b v 2 k (f i) (fun _ => 0) (fun _ => 0) (u₀ i) (w₀ i))
    (hsk : ∀ i, IsTorusForcedRow ν a b v 2 k 0
      (fun t => P.clampedAmbientFluxCLM i t (U t)) (fun _ => 0) (uk i) (wk i)) :
    ∀ i, ∀ t ∈ Set.Icc a b, u i t = u₀ i t + uk i t := by
  intro i
  have hn : IsTorusForcedRow ν a b v 2 k (f i) (P.carrierFlux w i)
      (fun _ => 0) (u i) (w i) := preparation_kernel_scalar_row P hd hs i
  have hflux : (fun t => P.clampedAmbientFluxCLM i t (U t))
      =ᵐ[volume.restrict (Set.Icc a b)] P.carrierFlux w i :=
    P.carrierFlux_eq_ambient_ae U w hU i
  exact preparation_scalar_zero_source_split (E := h i) (k := k) hd P.htime P.radius_pos
    P.diffusivity_pos hk (f := f i) (F := P.carrierFlux w i)
    (Q := fun t => P.clampedAmbientFluxCLM i t (U t))
    (P.carrierFlux_memLp_of_family w hs.2.1 i) hflux
    (u := u i) (u₀ := u₀ i) (uk := uk i) (w := w i) (w₀ := w₀ i) (wk := wk i)
    hn (hs₀ i) (hsk i)

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual scalar kernel response is unchanged when its ambient input
class is read through a genuine preceding-copy higher lift. Its physical
carrier flux has time MemLp, and time-a.e. forcing equality transfers the
actual weak row while retaining its continuous trace and higher class.

The degenerate cases are included: empty and singleton families, zero data and constants, D=2,
identity geometry, edgeless seeds and degenerate windows. No second solution, additional
integrability premise or mass-dependent response is selected. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*}
  [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
  [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
  [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
  {a b ρ ν : ℝ} {D : ℕ} {v : ℝ → Vec 2 → Vec 2}

/-- The SAME response realizes the physical source on any actual higher
representative of its ambient input class, with its full time regularity. -/
def KernelResponseActualRowsStatement
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (v : ℝ → Vec 2 → Vec 2)
    (J : CoupledHighTime (h := h) (fun _ => 0) a b →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b a) : Prop :=
  ∀ (X : CoupledHighTime (h := h) (fun _ => 0) a b)
    (V : ∀ i, ℝ → TorusHk 1 (h i)),
    (X =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      coupledCarrierHighJets (fun _ => 0) (fun i => V i t)) →
    (∀ i, MemLp (P.carrierFlux V i) 2 (volume.restrict (Set.Icc a b))) ∧
    (J X).1 ⟨a, le_rfl, P.htime⟩ = 0 ∧
    ∃ W : ∀ i, ℝ → TorusHk 1 (h i),
      (∀ i, IsTorusForcedRow ν a b v 2 0 0 (P.carrierFlux V i) (fun _ => 0)
        (fun t => (J X).1 (Set.projIcc a b P.htime t) i) (W i)) ∧
      ((J X).2 =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        coupledCarrierHighJets (fun _ => 0) (fun i => W i t))

/-- Graph readout and forcing congruence assemble the actual source rows
of the existing scalar response. Every analytic input is discharged by
the carrier-flux and scalar-row lemmas. -/
theorem kernel_response_actual_rows
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (J : CoupledHighTime (h := h) (fun _ => 0) a b →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b a)
    (hJ : ScalarFamilyEnergyPathRealizes (ν := ν) P.htime v
      (preparationKernelScalarDatum P) J) : KernelResponseActualRowsStatement P v J := by
  intro X V hX
  have hraw : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i, (V i t).val = X t i := by
    filter_upwards [hX] with t ht
    intro i
    exact (congrArg (fun z : CoupledHighHilbert (h := h) (fun _ => 0) => z i) ht).symm
  have hob3 := hJ X
  obtain ⟨hstart, W, hrows, hW⟩ := hob3
  refine ⟨fun i => P.carrierFlux_memLp X V hraw i, hstart, W, ?_, hW⟩
  intro i
  exact CycleJointProofs.PathReduction.torusRowSolution_forcing_congr
    (E := h i) ν a b v 2 0 0
    (fun t => P.clampedAmbientFluxCLM i t (X t)) (P.carrierFlux V i)
    (fun t => (J X).1 (Set.projIcc a b P.htime t) i) (W i)
    (P.carrierFlux_eq_ambient_ae X V hraw i) (hrows i)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual buffered native evolution is a fixed point of scalar kernel
insertion. All maps retain their actual PDE realizations. The initial path
uses the full native value at the buffer, rather than a plain-layer surrogate.

The degenerate cases are included: empty and singleton families, identity geometry, zero datum or
edges, order zero, and a zero-length post-buffer interval use the same maps.
The trace identity covers the whole window; the higher identity is in the
ambient post-buffer L2 class. -/

section
attribute [local instance] preparationScalarFluxModule preparationScalarFluxSMul preparationRestartFluxAdd
  preparationResponseNativeNormed preparationResponseNativeModule
  preparationResponseDatumAdd preparationResponseDatumMonoid preparationResponseDatumModule
  preparationNativeFamilyNormed preparationNativeFamilyModule preparationNativeContinuousModule
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν : ℝ} {D : ℕ}

/-- PDE realizations of all three maps in buffered insertion. -/
def BufferedKernelMapsRealizes
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c) : Prop :=
  let Q := Buffer.kernelOperator_time_restrict P (Set.Icc_subset_Icc hac le_rfl) hcb
  NativeEnergyPathRealizes P φ c M.full ∧
    ScalarFamilyEnergyPathRealizes (h := h) (ν := ν) hcb (streamVel φ)
      (fun i (f : ∀ j, TorusHk 0 (h j)) => (f i, 0)) M.homogeneous ∧
    ScalarFamilyEnergyPathRealizes (h := h) (ν := ν) hcb (streamVel φ)
      (preparationKernelScalarDatum Q) M.source
end

/-! Exact assembly of the weighted bounds for the actual buffered fixed point.
The two estimates assumed here concern the already constructed maps, so the same maps
can subsequently be priced with both masses. This is one step in the proof of common
preparation.

Empty or singleton families, zero datum or edges, and degenerate windows retain the actual
initial trace. Neither
estimate divides by an input norm or sums componentwise trace suprema. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν c : ℝ} {D : ℕ}

/-- Native homogeneous contraction and dissipation price any realized full map. -/
def NativePathEnergyBoundStatement
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (c : ℝ) : Prop :=
  ∀ F, NativeEnergyPathRealizes P φ c F → ∀ f,
    preparationWeightedPathEnergy ρ P.π ν a b c (F f) ≤
      2 * Real.sqrt (massNormSq ρ P.π (fun i => (f i).val))

/-- The actual zero-data scalar response prices insertion on every ambient input. -/
def KernelInsertionEnergyBoundStatement
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (hac : a ≤ c) (hcb : c ≤ b) : Prop :=
  ∀ M, BufferedKernelMapsRealizes P φ hac hcb M → ∀ x,
    preparationWeightedPathEnergy ρ P.π ν a b c
      (preparationBufferedKernelMap hcb M.source x) ≤
      7 * |P.θ| * preparationWeightedPathEnergy ρ P.π ν a b c x
end

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The native homogeneous path has energy at most twice its initial weighted
mass norm, for any actual realization of the fixed linear map. This reuses the
native interval contraction and dissipation, with no new drift budget.

Empty or singleton families, zero datum or edges, and degenerate post-buffer windows
retain the same bound. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedLowSMul preparationWeightedLowSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν c : ℝ} {D : ℕ}

private theorem preparation_native_sqrt_gradient {ν M g : ℝ}
    (hν : 0 ≤ ν) (hM : 0 ≤ M) (hg : 0 ≤ g) (he : ν * g ^ 2 ≤ M) :
    Real.sqrt ν * g ≤ Real.sqrt M := by
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg ν) hg) (Real.sqrt_nonneg M)).mp
  rw [mul_pow, Real.sq_sqrt hν, Real.sq_sqrt hM]
  exact he

omit [DecidableEq ι] in
/-- The full native map has a uniform physical bound at the same mass as its operator. -/
theorem native_path_energy_bound
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (hac : a ≤ c) :
    NativePathEnergyBoundStatement P φ c := by
  intro F hF f
  let hn := hF f
  let W := Classical.choose hn
  let hy := Classical.choose_spec hn
  let Y := Classical.choose hy
  have hs := (Classical.choose_spec hy).1
  have hW := (Classical.choose_spec hy).2
  let u := fun i t => (F f).1 (Set.projIcc a b P.htime t) i
  obtain ⟨hv, _hp, _hd, ⟨V, hb⟩, _hm⟩ := Buffer.stream_kernel_drift_data hφ a b
  have hV : 0 ≤ max V 0 := le_max_right _ _
  have hbV : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ max V 0 :=
    fun t ht x => (hb t ht x).trans (le_max_left _ _)
  have hforced₀ := P.kernelWeakSolution_forcedWeakSolution (streamVel φ) hv
    (max V 0) hV hbV f 0 0 u W Y hs
  have hforced : IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => 0)
      KernelEnergy.TorusKernelOperator.noLocalCoefficient f (P.carrierFlux W)
      (fun _ _ => 0) u W := by
    simpa only [Pi.zero_def, Pi.zero_apply, zero_add] using hforced₀
  have hall := Buffer.TorusKernelOperator.stream_homogeneous_interval P hφ
    (max V 0) hV hbV f W u hforced
  have hi : (fun i => (u i a).val) = (fun i => (f i).val) :=
    funext (fun i => congrArg Subtype.val (hs.2.2.2.1 i))
  have htrace (t : Set.Icc a b) :
      ‖massWeightedCarrierCLM (fun _ => 0) ρ P.π ((F f).1 t)‖ ≤
        Real.sqrt (massNormSq ρ P.π (fun i => (f i).val)) := by
    rw [massWeightedCarrierCLM_norm _ _ _ P.hπ]
    have he := hall a ⟨le_rfl, P.htime⟩ t t.property t.property.1
    rw [hi] at he
    have hnon : 0 ≤ (5 * ν / 4) * (∫ r in Set.Ioc a (t : ℝ),
        massGradNormSq ρ P.π (fun i => (W i r).val)) := mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) P.diffusivity_pos.le)
        (by norm_num : (0 : ℝ) ≤ 4))
      (integral_nonneg (fun r => massGradNormSq_nonneg ρ P.π P.hπ _))
    have hh := (le_add_of_nonneg_right (a := massNormSq ρ P.π
      (fun i => (u i t).val)) hnon).trans he
    simp only [u, Set.projIcc_of_mem P.htime t.property] at hh
    exact Real.sqrt_le_sqrt hh
  let A := preparationWeightedGradientCLM (h := h) ρ P.π
  let Z := A.compLpL 2 (volume.restrict (Set.Icc c b)) (F f).2
  have hZ : ‖Z‖ ^ 2 = ∫ t in Set.Icc c b,
      massGradNormSq ρ P.π (fun i => (W i t).val) :=
    preparation_weighted_gradient_time_normSq ρ P.π P.hπ c b (F f).2 W hW
  have hpost : ‖Z‖ ^ 2 ≤ ∫ t in Set.Icc a b,
      massGradNormSq ρ P.π (fun i => (W i t).val) := by
    rw [hZ]
    exact setIntegral_mono_set (Buffer.kernel_gradient_time_integrable a b ρ P.π W hs.2.1)
      (Filter.Eventually.of_forall (fun t => massGradNormSq_nonneg ρ P.π P.hπ _))
      (Filter.Eventually.of_forall (fun _ ht => ⟨hac.trans ht.1, ht.2⟩))
  have hdiss := Buffer.TorusKernelOperator.stream_homogeneous_dissipation P hφ
    (max V 0) hV hbV f W u hforced
  have hgrad : ν * ‖Z‖ ^ 2 ≤ massNormSq ρ P.π (fun i => (f i).val) := by
    calc
      _ ≤ ν * (∫ t in Set.Icc a b,
          massGradNormSq ρ P.π (fun i => (W i t).val)) :=
        mul_le_mul_of_nonneg_left hpost P.diffusivity_pos.le
      _ ≤ (5 * ν / 4) * (∫ t in Set.Icc a b,
          massGradNormSq ρ P.π (fun i => (W i t).val)) :=
        mul_le_mul_of_nonneg_right (by linarith only [P.diffusivity_pos])
          (integral_nonneg (fun t => massGradNormSq_nonneg ρ P.π P.hπ _))
      _ ≤ _ := hdiss
  have hg := preparation_native_sqrt_gradient P.diffusivity_pos.le
    (massNormSq_nonneg ρ P.π P.hπ _) (norm_nonneg Z) hgrad
  rw [preparationWeightedPathEnergy, preparation_path_energy_eq]
  have ht := (ContinuousMap.norm_le
    (ContinuousLinearMap.compLeftContinuous ℝ (Set.Icc a b)
      (massWeightedCarrierCLM (E := h) (fun _ => 0) ρ P.π) (F f).1)
    (Real.sqrt_nonneg (massNormSq ρ P.π (fun i => (f i).val)))).mpr htrace
  exact (add_le_add ht hg).trans_eq (two_mul _).symm

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Actual scalar kernel insertion has physical path-energy norm at most
7 |theta| times that of its input. At the nonnegative stage budgets this is
7 theta. The absolute value also covers the vacuous Schur bound on an empty family. The fixed graph
projection is shared by the forcing and gradient readouts, so arbitrary ambient inputs are allowed.

The degenerate cases are included: empty and singleton families, zero data or edges, identity
geometry, order zero and a zero-length post-buffer window use the same maps. There is
no componentwise trace supremum sum, second flux price, or division by data. -/

/-- Zero-initial post-buffer extension does not increase the physical path energy. -/
theorem preparation_post_energy_extension_le {H V Q Z : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {a b c : ℝ} (hcb : c ≤ b) (L : H →L[ℝ] Q) (G : V →L[ℝ] Z) (ν : ℝ)
    (z : PreparationEnergyPath H V c b c) (hz : z.1 ⟨c, le_rfl, hcb⟩ = 0) :
    preparationPathEnergy a b c L G ν (preparationPostEnergyExtension hcb z) ≤
      preparationPathEnergy c b c L G ν z := by
  have hc : ContinuousLinearMap.compLeftContinuous ℝ (Set.Icc a b) L
      (preparationPostExtension hcb z.1) = preparationPostExtension hcb
        (ContinuousLinearMap.compLeftContinuous ℝ (Set.Icc c b) L z.1) := by
    apply ContinuousMap.ext
    intro t
    change L (z.1 (Set.projIcc c b hcb t) - z.1 ⟨c, le_rfl, hcb⟩) =
      L (z.1 (Set.projIcc c b hcb t)) - L (z.1 ⟨c, le_rfl, hcb⟩)
    exact L.map_sub _ _
  have hz' : (ContinuousLinearMap.compLeftContinuous ℝ (Set.Icc c b) L z.1)
      ⟨c, le_rfl, hcb⟩ = 0 := by
    change L (z.1 ⟨c, le_rfl, hcb⟩) = 0
    rw [hz, map_zero]
  rw [preparation_path_energy_eq, preparation_path_energy_eq]
  change ‖ContinuousLinearMap.compLeftContinuous ℝ (Set.Icc a b) L
    (preparationPostExtension hcb z.1)‖ + _ ≤ _
  rw [hc]
  exact add_le_add (preparation_post_extension_norm_le hcb _ hz') le_rfl

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul
  preparationWeightedLowSMul preparationWeightedLowSpace
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν c : ℝ} {D : ℕ}

private theorem preparation_source_trace_gradient {ν s r T G : ℝ}
    (hν : 0 ≤ ν) (hs : 0 ≤ s) (hsq : s ^ 2 = ν) (hr : 0 ≤ r)
    (hT : 0 ≤ T) (hG : 0 ≤ G) (he : T ^ 2 + ν / 2 * G ^ 2 ≤ 8 * r ^ 2) :
    T ≤ 3 * r ∧ s * G ≤ 4 * r := by
  have hgrad : 0 ≤ ν / 2 * G ^ 2 := mul_nonneg (div_nonneg hν (by norm_num)) (sq_nonneg G)
  constructor
  · apply (sq_le_sq₀ hT (mul_nonneg (by norm_num) hr)).mp
    nlinarith only [he, hgrad, sq_nonneg r]
  · apply (sq_le_sq₀ (mul_nonneg hs hG) (mul_nonneg (by norm_num) hr)).mp
    rw [mul_pow, hsq]
    nlinarith only [he, sq_nonneg T]

private theorem preparation_source_price_identity {ν : ℝ} (hν : 0 < ν) (θ z : ℝ) :
    8 / ν * ((ν * θ) ^ 2 * z ^ 2) = 8 * (Real.sqrt ν * |θ| * z) ^ 2 := by
  simp only [mul_pow, Real.sq_sqrt hν.le, sq_abs]
  field_simp [hν.ne']

/-- A whole-family trace bound and the matching integrated gradient bound
give physical path energy, with no sum of component suprema. -/
theorem preparation_path_energy_of_squares {H V Q Z : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {a b ν r : ℝ} (hab : a ≤ b) (L : H →L[ℝ] Q) (G : V →L[ℝ] Z)
    (hν : 0 ≤ ν) (z : PreparationEnergyPath H V a b a) (hr : 0 ≤ r)
    (he : ∀ t : Set.Icc a b, ‖L (z.1 t)‖ ^ 2 + ν / 2 *
      ‖G.compLpL 2 (volume.restrict (Set.Icc a b)) z.2‖ ^ 2 ≤ 8 * r ^ 2) :
    preparationPathEnergy a b a L G ν z ≤ 7 * r := by
  have hb (t : Set.Icc a b) := preparation_source_trace_gradient hν
    (Real.sqrt_nonneg ν) (Real.sq_sqrt hν) hr (norm_nonneg _)
    (norm_nonneg _) (he t)
  have ht := (ContinuousMap.norm_le
    (ContinuousLinearMap.compLeftContinuous ℝ (Set.Icc a b) L z.1)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hr)).mpr (fun t => (hb t).1)
  rw [preparation_path_energy_eq]
  calc
    _ ≤ 3 * r + 4 * r := add_le_add ht (hb ⟨a, le_rfl, hab⟩).2
    _ = _ := by ring

/-- The source time energy is priced by the very same projected gradient class. -/
theorem preparation_kernel_source_integral_le
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (U : CoupledHighTime (h := h) (fun _ => 0) a b) :
    (∫ t in Set.Icc a b, massNormSq ρ P.π
      (fun i => (P.clampedAmbientFluxCLM i t (U t)).val)) ≤
      (ν * P.θ) ^ 2 * ‖(preparationWeightedGradientCLM (h := h) ρ P.π).compLpL 2
        (volume.restrict (Set.Icc a b)) U‖ ^ 2 := by
  let A := preparationWeightedGradientCLM (h := h) ρ P.π
  have hFi := massNormSq_integrable ρ P.π P.hπ
    (fun i => (torusHkGraph (E := PiLp 2 (fun _ : Fin 2 => h i)) 0).toSubmodule.subtypeL.comp_memLp'
      (P.limitFlux_memLp U i))
  have hAi := (A.comp_memLp' (Lp.memLp U)).norm.integrable_sq
  rw [preparation_weighted_gradient_class_normSq, ← integral_const_mul]
  apply integral_mono_ae hFi (hAi.const_mul ((ν * P.θ) ^ 2))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change massNormSq ρ P.π (fun i => (P.clampedAmbientFluxCLM i t (U t)).val) ≤
    (ν * P.θ) ^ 2 * ‖preparationWeightedGradientCLM (h := h) ρ P.π (U t)‖ ^ 2
  rw [preparation_weighted_gradient_normSq ρ P.π P.hπ]
  simp only [preparation_clamped_kernel_flux_eq P _ t ht]
  exact P.flux_mass_bound t ht
    (KernelEnergy.TorusKernelOperator.ambientCarrierCLM (h := h) (k := 0) (U t))

/-- A realized scalar kernel response has the coarse sharp-enough physical price. -/
theorem scalar_kernel_path_energy_bound
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (J : PreparationKernelSourceMap (h := h) a b)
    (hJ : ScalarFamilyEnergyPathRealizes (ν := ν) P.htime v (preparationKernelScalarDatum P) J)
    (U : CoupledHighTime (h := h) (fun _ => 0) a b) :
    preparationWeightedPathEnergy (h := h) ρ P.π ν a b a (J U) ≤
      7 * |P.θ| * (Real.sqrt ν * ‖(preparationWeightedGradientCLM (h := h) ρ P.π).compLpL 2
        (volume.restrict (Set.Icc a b)) U‖) := by
  let hn := (hJ U).2
  let W := Classical.choose hn
  have hs := (Classical.choose_spec hn).1
  have hW := (Classical.choose_spec hn).2
  let A := preparationWeightedGradientCLM (h := h) ρ P.π
  let Z := A.compLpL 2 (volume.restrict (Set.Icc a b)) U
  let Y := A.compLpL 2 (volume.restrict (Set.Icc a b)) (J U).2
  let r := Real.sqrt ν * |P.θ| * ‖Z‖
  have hr : 0 ≤ r := mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg ν) (abs_nonneg P.θ)) (norm_nonneg Z)
  have hprice : 8 / ν * ((ν * P.θ) ^ 2 * ‖Z‖ ^ 2) = 8 * r ^ 2 :=
    preparation_source_price_identity P.diffusivity_pos P.θ ‖Z‖
  have hY : ‖Y‖ ^ 2 = ∫ t in Set.Icc a b,
      massGradNormSq ρ P.π (fun i => (W i t).val) :=
    preparation_weighted_gradient_time_normSq ρ P.π P.hπ a b (J U).2 W hW
  have he (t : Set.Icc a b) :
      ‖massWeightedCarrierCLM (fun _ => 0) ρ P.π ((J U).1 t)‖ ^ 2 +
        ν / 2 * ‖Y‖ ^ 2 ≤ 8 * r ^ 2 := by
    rw [massWeightedCarrierCLM_normSq _ _ _ P.hπ, hY]
    have hh := preparation_scalar_family_energy hd P.htime P.radius_pos P.diffusivity_pos
      (Nat.zero_le Kmax) P.π P.hπ (fun i => P.limitFlux_memLp U i) hs t t.property
    simp only [preparationKernelScalarDatum, torusMassNormSq_zero (fun _ => 0) ρ P.π P.hπ,
      mul_zero, zero_add, Set.projIcc_of_mem P.htime t.property] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (preparation_kernel_source_integral_le P U)
      (div_nonneg (by norm_num) P.diffusivity_pos.le)).trans_eq hprice)
  have hb := preparation_path_energy_of_squares P.htime
    (massWeightedCarrierCLM (E := h) (fun _ => 0) ρ P.π) A P.diffusivity_pos.le (J U) hr he
  exact hb.trans_eq (by change 7 * (Real.sqrt ν * |P.θ| * ‖Z‖) = _; ring)

/-- Zero extension and the scalar forced estimate give insertion's physical norm bound. -/
theorem kernel_insertion_energy_bound
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    {φ : ℝ → Vec 2 → ℝ} (hac : a ≤ c) (hcb : c ≤ b) {Kmax : ℕ}
    (hd : TorusDriftData ν ρ c b (streamVel φ) Kmax) :
    KernelInsertionEnergyBoundStatement P φ hac hcb := by
  intro M hM x
  let Q := Buffer.kernelOperator_time_restrict P (Set.Icc_subset_Icc hac le_rfl) hcb
  have hreal : ScalarFamilyEnergyPathRealizes (ν := ν) hcb (streamVel φ)
      (preparationKernelScalarDatum Q) M.source := hM.2.2
  have hz : (M.source x.2).1 ⟨c, le_rfl, hcb⟩ = 0 := by
    simpa only [preparationKernelScalarDatum, Pi.zero_def] using (hreal x.2).1
  have hs := scalar_kernel_path_energy_bound Q hd M.source hreal x.2
  have hp : Real.sqrt ν * ‖(preparationWeightedGradientCLM (h := h) ρ P.π).compLpL 2
      (volume.restrict (Set.Icc c b)) x.2‖ ≤
      preparationWeightedPathEnergy (h := h) ρ P.π ν a b c x := by
    rw [preparationWeightedPathEnergy, preparation_path_energy_eq]
    exact le_add_of_nonneg_left (norm_nonneg _)
  calc
    _ ≤ preparationWeightedPathEnergy (h := h) ρ P.π ν c b c (M.source x.2) :=
      preparation_post_energy_extension_le hcb (massWeightedCarrierCLM (E := h) (fun _ => 0) ρ P.π)
        (preparationWeightedGradientCLM (h := h) ρ P.π) ν _ hz
    _ ≤ 7 * |P.θ| * (Real.sqrt ν * ‖(preparationWeightedGradientCLM (h := h) ρ P.π).compLpL 2
        (volume.restrict (Set.Icc c b)) x.2‖) := hs
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) (abs_nonneg P.θ))

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
