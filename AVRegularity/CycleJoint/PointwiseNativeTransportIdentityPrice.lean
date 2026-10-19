-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneComponentAllMomentGradientBudget
import AVRegularity.CoupledEnergyPlane.PlaneWeakSolutionUniqueness
import AVRegularity.CycleJoint.ScalarPlaneUniformMassSquaredEnergy
public import AVRegularity.CycleWords.ConstructedCoreRawContraction
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The true localized input chart is linear and has every polynomial moment. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

def preparationReferenceCellLocalizedInitialLinearMap
    (hab : a ≤ b) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) :
    TorusHk J E →ₗ[ℝ] PlaneHk univ J E :=
  (planeCarrierAffineOperator J e he yc).toLinearMap.comp
    ((preparationReferenceHkWindowPullOperator hc hcover hTau ha J hJ a
      ⟨le_refl a, hab⟩).toLinearMap.comp
      (spatialPatchLocalization hζ Npatch hNpatch patch J))

theorem preparationReferenceCellLocalizedInitialLinearMap_apply
    (hab : a ≤ b) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (f : TorusHk J E) :
    preparationReferenceCellLocalizedInitialLinearMap hc hcover hTau ha J hJ
      hab hζ Npatch hNpatch patch e he yc f =
      planeCarrierAffine e he yc (preparationReferenceHkWindowPull hc hcover hTau ha J hJ a
        (spatialPatchLocalization hζ Npatch hNpatch patch J f)) := by
  change planeCarrierAffine e he yc
    (preparationReferenceHkWindowPullOperator hc hcover hTau ha J hJ a ⟨le_refl a, hab⟩
      (spatialPatchLocalization hζ Npatch hNpatch patch J f)) = _
  exact congrArg (fun V : PlaneHk univ J E => planeCarrierAffine e he yc V)
    (preparationReferenceHkWindowPullOperator_apply hc hcover hTau ha J hJ a
      (show a ∈ Icc a b from ⟨le_refl a, hab⟩)
      (spatialPatchLocalization hζ Npatch hNpatch patch J f))

theorem preparationReferenceCellLocalizedInitialLinearMap_all_moments
    (hab : a ≤ b) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (f : TorusHk J E)
    (n : ℕ) (ϖ ρ : ℝ) :
    AVRegularity.weightedFactorialNormSq n ϖ 0 (ρ / e) J
      (preparationReferenceCellLocalizedInitialLinearMap hc hcover hTau ha J hJ
        hab hζ Npatch hNpatch patch e he yc f) ≠ ⊤ := by
  rw [preparationReferenceCellLocalizedInitialLinearMap_apply]
  exact preparationReferenceCell_localized_initial_moments hc hcover hTau ha J hJ hab
    hζ Npatch hNpatch patch f e he yc n ϖ ρ

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The finite preparation source acts on the actual reference-chart carriers by conjugation with the certified inverse Sobolev pullback. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

variable (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ u, K u ≤ Jchart) (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)

def preparationReferenceNativeFluxOperator :
    (∀ u, PlaneHk Set.univ (K u + 1) (h u)) →L[ℝ] PlaneFluxL2 (h v) :=
  (planeFluxChartPull hφ t ((l₀ : ℝ) * ocTauPP α q Λ m)).comp
    ((preparationPhysicalNativeFluxOperator F K ν e E a b n hs actual hT he t ht v).comp
      (ContinuousLinearMap.pi (fun u =>
        (preparationReferenceHkInverse hprep hcover hTau ha (K u + 1)
          (Nat.add_le_add_right (hK u) 1) t ht).comp (ContinuousLinearMap.proj u))))

theorem preparationReferenceNativeFluxOperator_windowPull
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    preparationReferenceNativeFluxOperator F K hprep hcover hTau ha hK ν e E n hs actual hT he
      t ht v (fun u => preparationReferenceHkWindowPull hprep hcover hTau ha (K u + 1)
        (Nat.add_le_add_right (hK u) 1) t (U u)) =
      planeFluxChartPull hφ t ((l₀ : ℝ) * ocTauPP α q Λ m)
        (preparationPhysicalNativeFlux F K ν e E a b n hs actual hT he t ht v U) := by
  have hi : (fun u => preparationReferenceHkInverse hprep hcover hTau ha (K u + 1)
      (Nat.add_le_add_right (hK u) 1) t ht
      (preparationReferenceHkWindowPull hprep hcover hTau ha (K u + 1)
        (Nat.add_le_add_right (hK u) 1) t (U u))) = U := by
    funext u
    exact preparationReferenceHkInverse_windowPull hprep hcover hTau ha (K u + 1)
      (Nat.add_le_add_right (hK u) 1) t ht (U u)
  change planeFluxChartPull hφ t ((l₀ : ℝ) * ocTauPP α q Λ m)
    (preparationPhysicalNativeFluxOperator F K ν e E a b n hs actual hT he t ht v
      (fun u => preparationReferenceHkInverse hprep hcover hTau ha (K u + 1)
        (Nat.add_le_add_right (hK u) 1) t ht
        (preparationReferenceHkWindowPull hprep hcover hTau ha (K u + 1)
          (Nat.add_le_add_right (hK u) 1) t (U u)))) = _
  rw [hi, preparationPhysicalNativeFluxOperator_apply]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! The actual homogeneous plane solution transfers to the literal torus unit-cell weak identity. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem periodizedHomogeneous_torus_weakIdentity (K : ι → ℕ) (D : ℕ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (ν a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hvp : ∀ s, AVenhance.IsZ2Periodic (v s))
    (hv : ∀ s ∈ Set.Icc a b, Continuous (v s)) (hvm : Measurable (Function.uncurry v))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ s ∈ Set.Icc a b, ∀ x, ‖v s x‖ ≤ V)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAp : ∀ i i' d s, AVenhance.IsZ2Periodic (A i i' d s))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (U : ∀ i, ℝ → TorusHk (K i) (h i)) (W : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hp : IsPeriodizedFamilyPair K a b u w U W)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (he : geometryEnergyNorm π K 4 ϖ z ρ a b u w < ⊤)
    (i : ι)
    (hc : ∀ i' d s, s ∈ Set.Icc a b → Continuous (A i i' d s))
    (hj : ∀ i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (MC : ∀ i', admissibleOrders K D i i' → ℝ) (hMC : ∀ i' d, 0 ≤ MC i' d)
    (hbA : ∀ i' d s, s ∈ Set.Icc a b → ∀ x, ‖A i i' d s x‖ ≤ MC i' d)
    (t : ℝ) (ht : t ∈ Set.Icc a b) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (φ : TorusHk 1 (h i)) :
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν a t v
      ((U i t).toFunction.jet (valueIndex2 (K i)))
      ((U i a).toFunction.jet (valueIndex2 (K i)))
      (φ.toFunction.jet (valueIndex2 1))
      (fun k => φ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩)
      (fun s k => (W i s).toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
      (fun s => torusRawCouplingFlux K D s A (fun j => W j s) i) 0 0 := by
  have hcpt := periodizedHomogeneous_compact_weakIdentity K D π hπ ν a b hab v hvp hv hvm
    V hV hbv A hAp f u w hs U W hp ϖ hϖ z ρ hρ he i hc hj MC hMC hbA t ht hζ φ
  let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
  let du := fun s k => (W i s).toFunction.jet
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
  let flux := fun s => torusRawCouplingFlux K D s A (fun j => W j s) i
  have hlocal := coupledWeakIdentity_test_congr volume ν a t v
    ((U i t).toFunction.jet (valueIndex2 (K i))) ((U i a).toFunction.jet (valueIndex2 (K i)))
    (ψ.toFunction.jet (valueIndex2 1))
    (fun x => spatialPatchCutoff ζ 1 0 x • φ.toFunction.jet (valueIndex2 1) x)
    (fun k => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩)
    (fun k x => fderiv ℝ (spatialPatchCutoff ζ 1 0) x (basisVec k) •
      φ.toFunction.jet (valueIndex2 1) x + spatialPatchCutoff ζ 1 0 x •
        φ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩ x)
    du flux 0 0 (spatialPatchLocalization_value_ae hζ 1 (by norm_num) 0 φ)
    (fun k => spatialPatchLocalization_gradient_ae hζ 1 (by norm_num) 0 φ k) hcpt
  have hsub : Set.Ioc a t ⊆ Set.Icc a b := fun s hs' => ⟨hs'.1.le, hs'.2.trans ht.2⟩
  apply periodic_cellL2_weakIdentity_transfer hζ ν a t v _ _ _ _ du flux 0 0
    (periodicJetRepresentative_memL2 (U i t).val _) (periodicJetRepresentative_memL2 (U i a).val _)
    (periodicJetRepresentative_memL2 φ.val _) (fun k => periodicJetRepresentative_memL2 φ.val _)
    (periodicJetRepresentative_periodic (U i t).val _) (periodicJetRepresentative_periodic (U i a).val _)
    (periodicJetRepresentative_periodic φ.val _) (fun k => periodicJetRepresentative_periodic φ.val _)
    (fun s hs' => hv s (hsub hs')) (fun s hs' => ⟨V, hV, hbv s (hsub hs')⟩)
    (fun s _ => hvp s) (fun s _ k => periodicJetRepresentative_memL2 (W i s).val _)
    (fun s hs' k => torusRawCouplingFlux_component_memLp K D s A i
      (fun i' d => hc i' d s (hsub hs')) MC hMC (fun i' d => hbA i' d s (hsub hs'))
      (fun j => W j s) k)
    (fun _ _ _ => by simp) (fun _ _ => MemLp.zero')
    (fun s _ k => periodicJetRepresentative_periodic (W i s).val _)
    (fun s _ => torusRawCouplingFlux_periodic K D s A i (fun i' d => hAp i i' d s) (fun j => W j s))
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) hlocal

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Genuine component response estimates sum with the original family masses and no cardinality factor. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance familyBudgetFluxNormed (i : ι) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => E i)) := componentCertificateFluxNormed
local instance familyBudgetFluxInner (i : ι) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => E i)) := componentCertificateFluxInner
local instance familyBudgetNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance familyBudgetNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (E i)) := allMomentTimeNativeModule k
local instance familyBudgetFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E i))) :=
  allMomentTimeNativeNormed k
local instance familyBudgetFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E i))) :=
  allMomentTimeNativeModule k

theorem planeComponentAllMomentResponse_family_gradient_budget
    (a b : ℝ) (hab : a ≤ b) (K : ι → ℕ) (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hMm : Measurable M)
    (g : ℝ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4)
    (hnear : IsMetricNearIdentity (fun t _ => M t) g)
    (hsym : ∀ t ∈ Icc a b, (M t).IsSymm)
    (t₀ S ϖ : ℝ) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun t _ => M t) v t₀ S ϖ 0 N Cw) (hm : m ≤ N)
    (ρ L : ℝ) (hρ : 0 < ρ) (hL : 1 ≤ L)
    (hsmall : B * ρ / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * ρ ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S)
    (π : ι → ℝ) (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 (volume.restrict (Icc a b)))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := E i) M v (K i) a b ϖ ρ (R i))
    (x : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
      (volume.restrict (Icc a b))) :
    (∫⁻ t in Icc a b, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedGradFactorialNormSq m ϖ 0 ρ (K i)
      (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 (volume.restrict (Icc a b)) (R i (x i)) t)) ≤
      ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
        (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
          ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
        (16 * ∫⁻ t in Icc a b, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq m ϖ 0 ρ (K i)
          (planeTimeAllMomentCarrierToLp (K i) ϖ ρ 0 (volume.restrict (Icc a b)) (x i) t)) := by
  let μ := volume.restrict (Icc a b)
  let A := ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
    (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
      ENNReal.ofReal (3 * Real.exp (18 * Cw m)))
  change planeAllMomentFamilyGradientEnergy (E := E) K m ϖ ρ μ π (fun i => R i (x i)) ≤
    A * (16 * planeAllMomentFamilyEnergy (E := fun i => PiLp 2 (fun _ : Fin 2 => E i))
      K m ϖ ρ μ π x)
  rw [← mul_assoc]
  apply planeAllMomentFamily_gradient_energy_of_component_budget (E := E)
    K m ϖ ρ μ π x (fun i => R i (x i)) (A * 16)
  intro i
  have he := planeComponentAllMomentResponse_gradient_budget (E := E i)
    a b hab (K i) Kmax (hK i) v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N m Cw C hm ρ L hρ hL hsmall
    hstrainSmall hreserve hdiv hwa hwb (R i) (hR i) (x i)
  simpa only [A, μ, mul_assoc] using he

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Exact localization, reference pullback and dilation on the whole input family. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Jchart + 1)
    (hab : a ≤ b) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2)

def preparationReferenceCellLocalizedInitialFamilyLinearMap :
    (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i)) :=
  LinearMap.pi (fun i =>
    (preparationReferenceCellLocalizedInitialLinearMap hc hcover hTau ha (K i) (hK i)
      hab hζ Npatch hNpatch patch e he yc).comp (LinearMap.proj i))

theorem preparationReferenceCellLocalizedInitialFamilyLinearMap_apply
    (f : ∀ i, TorusHk (K i) (h i)) (i : ι) :
    preparationReferenceCellLocalizedInitialFamilyLinearMap hc hcover hTau ha K hK
      hab hζ Npatch hNpatch patch e he yc f i =
      planeCarrierAffine e he yc (preparationReferenceHkWindowPull hc hcover hTau ha
        (K i) (hK i) a (spatialPatchLocalization hζ Npatch hNpatch patch (K i) (f i))) := by
  exact preparationReferenceCellLocalizedInitialLinearMap_apply hc hcover hTau ha
    (K i) (hK i) hab hζ Npatch hNpatch patch e he yc (f i)

theorem preparationReferenceCellLocalizedInitialFamilyLinearMap_all_moments
    (f : ∀ i, TorusHk (K i) (h i)) (n : ℕ) (ϖ ρ : ℝ) (i : ι) :
    AVRegularity.weightedFactorialNormSq n ϖ 0 (ρ / e) (K i)
      (preparationReferenceCellLocalizedInitialFamilyLinearMap hc hcover hTau ha K hK
        hab hζ Npatch hNpatch patch e he yc f i) ≠ ⊤ := by
  exact preparationReferenceCellLocalizedInitialLinearMap_all_moments hc hcover hTau ha
    (K i) (hK i) hab hζ Npatch hNpatch patch e he yc (f i) n ϖ ρ

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The reference source operator has the exact physical readout after its certified inverse Sobolev action. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationReferenceNativeFluxOperator_apply
    (F : ChartedFamily ι h D P' Ctx) (K : ι → ℕ)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ u, K u ≤ Jchart) (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)
    (V : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    preparationReferenceNativeFluxOperator F K hprep hcover hTau ha hK ν e E n hs actual hT he
      t ht v V = planeFluxChartPull hφ t ((l₀ : ℝ) * ocTauPP α q Λ m)
        (preparationPhysicalNativeFlux F K ν e E a b n hs actual hT he t ht v
          (fun u => preparationReferenceHkInverse hprep hcover hTau ha (K u + 1)
            (Nat.add_le_add_right (hK u) 1) t ht (V u))) := by
  change planeFluxChartPull hφ t ((l₀ : ℝ) * ocTauPP α q Λ m)
    (preparationPhysicalNativeFluxOperator F K ν e E a b n hs actual hT he t ht v _) = _
  rw [preparationPhysicalNativeFluxOperator_apply]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Uniqueness of genuine frozen-metric response solutions with their complete native data. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem frozenMetricPlaneWeakSolution_unique (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ strain B lam : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hM : Measurable M)
    (εg : ℝ) (hεg : 0 ≤ εg) (hεgsmall : 4 * εg ≤ 1 / 8)
    (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        εg * ∑ i, ξ i ^ 2)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))

    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane 1 a b v 2 K
      (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1)) f F g u w)
    (u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs' : IsCoupledWeakSolutionPlane 1 a b v 2 K
      (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1)) f F g u' w') :
    ∀ i, ∀ t ∈ Set.Icc a b, u i t = u' i t := by
  exact AVRegularity.CoupledEnergyPlane.planeWeakSolution_unique K Kmax hK
    ρ strain B lam 1 hρ hstrain0 hB hlam zero_lt_one hsmall hstrain
    (fun _ => 1) (fun _ => zero_lt_one) a b hab v hv hvm V hV hbv hdiv hjets 2
    (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1))
    (frozenMetric_diagonal_coefficients_finite K M ρ a b εg hεg hsym hquad)
    (fun i j d t _ => frozenMetric_diagonal_coefficient_contDiff K M i j d t)
    (frozenMetric_diagonal_coefficient_measurable K M hM a b)
    (frozenMetric_diagonal_schurCondition K (fun _ => 1) (fun _ => zero_lt_one) M ρ a b εg
      hεg hεgsmall hsym hquad)
    F g hF hg f u w hs u' w' hs'

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The finite preparation source acts on the actual reference-chart carriers by conjugation with the certified inverse Sobolev pullback. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

variable (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ u, K u ≤ Jchart) (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)

def preparationWindowReferenceNativeFluxOperator :
    (∀ u, PlaneHk Set.univ (K u + 1) (h u)) →L[ℝ] PlaneFluxL2 (h v) :=
  (planeFluxChartPull hφ t σ).comp
    ((preparationPhysicalNativeFluxOperator F K ν e E a b n hs actual hT he t ht v).comp
      (ContinuousLinearMap.pi (fun u =>
        (preparationWindowReferenceHkInverse hprep hcover σ hσ ha (K u + 1)
          (Nat.add_le_add_right (hK u) 1) t ht).comp (ContinuousLinearMap.proj u))))

theorem preparationWindowReferenceNativeFluxOperator_windowPull
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    preparationWindowReferenceNativeFluxOperator F K hprep hcover σ hσ ha hK ν e E n hs actual hT he
      t ht v (fun u => preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K u + 1)
        (Nat.add_le_add_right (hK u) 1) t (U u)) =
      planeFluxChartPull hφ t σ
        (preparationPhysicalNativeFlux F K ν e E a b n hs actual hT he t ht v U) := by
  have hi : (fun u => preparationWindowReferenceHkInverse hprep hcover σ hσ ha (K u + 1)
      (Nat.add_le_add_right (hK u) 1) t ht
      (preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K u + 1)
        (Nat.add_le_add_right (hK u) 1) t (U u))) = U := by
    funext u
    exact preparationWindowReferenceHkInverse_windowPull hprep hcover σ hσ ha (K u + 1)
      (Nat.add_le_add_right (hK u) 1) t ht (U u)
  change planeFluxChartPull hφ t σ
    (preparationPhysicalNativeFluxOperator F K ν e E a b n hs actual hT he t ht v
      (fun u => preparationWindowReferenceHkInverse hprep hcover σ hσ ha (K u + 1)
        (Nat.add_le_add_right (hK u) 1) t ht
        (preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K u + 1)
          (Nat.add_le_add_right (hK u) 1) t (U u)))) = _
  rw [hi, preparationPhysicalNativeFluxOperator_apply]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The reference source operator has the exact physical readout after its certified inverse Sobolev action. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationWindowReferenceNativeFluxOperator_apply
    (F : ChartedFamily ι h D P' Ctx) (K : ι → ℕ)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ u, K u ≤ Jchart) (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)
    (V : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    preparationWindowReferenceNativeFluxOperator F K hprep hcover σ hσ ha hK ν e E n hs actual hT he
      t ht v V = planeFluxChartPull hφ t σ
        (preparationPhysicalNativeFlux F K ν e E a b n hs actual hT he t ht v
          (fun u => preparationWindowReferenceHkInverse hprep hcover σ hσ ha (K u + 1)
            (Nat.add_le_add_right (hK u) 1) t ht (V u))) := by
  change planeFluxChartPull hφ t σ
    (preparationPhysicalNativeFluxOperator F K ν e E a b n hs actual hT he t ht v _) = _
  rw [preparationPhysicalNativeFluxOperator_apply]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Uniqueness of genuine frozen-metric response solutions with their complete native data. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem frozenMetricPlaneWeakSolution_unique_lift (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ strain B lam : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hM : Measurable M)
    (εg : ℝ) (hεg : 0 ≤ εg) (hεgsmall : 4 * εg ≤ 1 / 8)
    (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        εg * ∑ i, ξ i ^ 2)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))

    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane 1 a b v 2 K
      (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1)) f F g u w)
    (u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs' : IsCoupledWeakSolutionPlane 1 a b v 2 K
      (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1)) f F g u' w') :
    (∀ i, ∀ t ∈ Set.Icc a b, u i t = u' i t) ∧
      ∀ i, w i =ᵐ[volume.restrict (Set.Icc a b)] w' i := by
  have hu := frozenMetricPlaneWeakSolution_unique K Kmax hK ρ strain B lam hρ hstrain0 hB
    hlam hsmall hstrain a b hab v hv V hV hbv hdiv hjets M hM εg hεg hεgsmall hsym hquad
    F g hF hg f hvm u w hs u' w' hs'
  refine ⟨hu, ?_⟩
  intro i
  filter_upwards [hs.2.2.1 i, hs'.2.2.1 i, ae_restrict_mem measurableSet_Icc] with t ht ht' hmem
  apply truncatePlaneHk_injective (Nat.le_succ (K i))
  exact ht.trans ((hu i t hmem).trans ht'.symm)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! Homogeneous plane solutions with finite geometry energy yield genuine coupled torus solutions. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem periodizedHomogeneous_torus_solution (K : ι → ℕ) (D : ℕ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (ν a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hvp : ∀ s, AVenhance.IsZ2Periodic (v s))
    (hv : ∀ s ∈ Set.Icc a b, Continuous (v s)) (hvm : Measurable (Function.uncurry v))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ s ∈ Set.Icc a b, ∀ x, ‖v s x‖ ≤ V)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAp : ∀ i i' d s, AVenhance.IsZ2Periodic (A i i' d s))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (U : ∀ i, ℝ → TorusHk (K i) (h i)) (W : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hp : IsPeriodizedFamilyPair K a b u w U W)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (he : geometryEnergyNorm π K 4 ϖ z ρ a b u w < ⊤)
    (hc : ∀ i i' d s, s ∈ Set.Icc a b → Continuous (A i i' d s))
    (hj : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (MC : ∀ i i', admissibleOrders K D i i' → ℝ) (hMC : ∀ i i' d, 0 ≤ MC i i' d)
    (hbA : ∀ i i' d s, s ∈ Set.Icc a b → ∀ x, ‖A i i' d s x‖ ≤ MC i i' d)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    IsCoupledWeakSolutionTorus ν a b v D K A (fun i => U i a)
      (fun _ _ => 0) (fun _ _ => 0) U W := by
  refine ⟨hp.1, hp.2.1, hp.2.2.1, fun _ => rfl, ?_⟩
  intro i t ht φ
  exact torusHomogeneous_forcing_readout (K i) ν a t v _ _ _ _ _ _
    (periodizedHomogeneous_torus_weakIdentity K D π hπ ν a b hab v hvp hv hvm V hV hbv
      A hAp f u w hs U W hp ϖ hϖ z ρ hρ he i (hc i) (hj i) (MC i) (hMC i) (hbA i) t ht hζ φ)
end

/-! Homogeneous plane solutions with finite geometry energy yield genuine coupled torus solutions. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_periodizedHomogeneous_torus_solution (K : ι → ℕ) (D : ℕ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (ν a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hvp : ∀ s, AVenhance.IsZ2Periodic (v s))
    (hv : ∀ s ∈ Set.Icc a b, Continuous (v s)) (hvm : Measurable (Function.uncurry v))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ s ∈ Set.Icc a b, ∀ x, ‖v s x‖ ≤ V)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAp : ∀ i i' d s, AVenhance.IsZ2Periodic (A i i' d s))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (he : geometryEnergyNorm π K 4 ϖ z ρ a b u w < ⊤)
    (hc : ∀ i i' d s, s ∈ Set.Icc a b → Continuous (A i i' d s))
    (hj : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (MC : ∀ i i', admissibleOrders K D i i' → ℝ) (hMC : ∀ i i' d, 0 ≤ MC i i' d)
    (hbA : ∀ i i' d s, s ∈ Set.Icc a b → ∀ x, ‖A i i' d s x‖ ≤ MC i i' d)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ (U : ∀ i, ℝ → TorusHk (K i) (h i)) (W : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsPeriodizedFamilyPair K a b u w U W ∧
      IsCoupledWeakSolutionTorus ν a b v D K A (fun i => U i a)
        (fun _ _ => 0) (fun _ _ => 0) U W := by
  obtain ⟨U, W, hp⟩ := exists_finiteGeometry_family_periodization π hπ K a b ϖ hϖ z ρ hρ
    u w hs.1 hs.2.1 hs.2.2.1 he
  exact ⟨U, W, hp, periodizedHomogeneous_torus_solution K D π hπ ν a b hab v hvp hv hvm
    V hV hbv A hAp f u w hs U W hp ϖ hϖ z ρ hρ he hc hj MC hMC hbA hζ⟩
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The homogeneous scalar base response has a native family gradient budget
controlled by the original mass-weighted initial data. -/

theorem scalarPlane_homogeneous_family_gradient_energy (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ta tb : ℝ) (_ht : ta ≤ tb) (rstar δ : ℝ) (_hrstar : 0 < rstar) (_hδ : 0 ≤ δ)
        (_hrδ : rstar * δ ≤ 1)
        (v : ℝ → Vec 2 → Vec 2)
        (_hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C)
        (_hv_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
        (_hv_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hv_div : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
        (a B₀ lam : ℝ) (_ha : 0 ≤ a) (_hB₀ : 1 ≤ B₀) (_hlam : 0 < lam)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc ta tb, ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
        (_hB : B₀ * rstar / lam ≤ 1 / 2) (_hab : a * B₀ * rstar ^ 2 ≤ 1 / 8)
        (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
        (_hG_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
        (_hG_symm : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm)
        (_hG_near : IsMetricNearIdentity G g)
        (_hG_smooth : ∀ t ∈ Set.Icc ta tb, ∀ a' k : Fin 2,
          ContDiff ℝ (max Kmax 1 : ℕ) (fun z => G t z a' k))
        (_hG_jets : ∀ t ∈ Set.Icc ta tb, ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ Kmax →
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ CG j * g * δ ^ j)
        (tw S ϖ : ℝ) (zc : Vec 2) (_htw : tw ≤ ta) (_htb : tb ≤ tw + S)
        (_W : ChartWeights G v tw S ϖ zc n Cw)
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (π : ι → ℝ),
        ∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x))
            (Z : ∀ x, PlaneTimeAllMomentCarrier (E := h x) (Kslot x + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb))),
          IsPlaneChainFrom (geometryScalarData 2 G) (fun _ x => Kslot x) ta tb v
            (fun _ x => V₀ x) (fun _ _ _ => 0) (fun _ x => V x) (fun _ x => Vw x) →
          (∀ x, PlaneTimeAllMomentRepresents (Kslot x + 1) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)) (Z x) (Vw x)) →
          zc = 0 →
          planeAllMomentFamilyGradientEnergy Kslot n ϖ rstar
            (volume.restrict (Set.Icc ta tb)) π Z ≤
          ENNReal.ofReal C * ∑ x, ENNReal.ofReal ((π x)⁻¹) *
            weightedFactorialNormSq n ϖ 0 rstar (Kslot x) (V₀ x) := by
  obtain ⟨C, hC, hbound⟩ := scalarPlane_uniform_squared_energy n Kmax CG Cw
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W V₀ π V Vw Z hs hZ hzc
  subst zc
  apply planeAllMomentFamily_gradient_energy_of_represented_initial_budget
    Kslot n ϖ rstar (volume.restrict (Set.Icc ta tb)) π Z Vw hZ
    (fun x => weightedFactorialNormSq n ϖ 0 rstar (Kslot x) (V₀ x)) (ENNReal.ofReal C)
  intro x
  have hb := hbound Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ 0 htw htb W V₀ (fun _ _ => 0)
    (fun x => planeHk_zero_time_memLp (Kslot x) (volume.restrict (Set.Icc ta tb))) V Vw hs x
  simp only [weightedFactorialNormSq_zero_carrier, lintegral_zero, mul_zero, add_zero] at hb
  exact (le_add_left (le_refl _)).trans hb

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Quantitative initial polynomial energy in the actual preparation reference
chart, with the center chosen as the inverse image of the physical patch center. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

theorem preparationReference_family_initial_return_energy_le
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hE : 0 < ocEpsilon q Λ (m - 1))
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Jchart + 1) (t : ℝ) (ht : t ∈ Icc a b)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N)
    (k : Fin 2 → ℤ) (f : ∀ i, TorusHk (K i) (h i))
    (π : ι → ℝ) (n : ℕ) (ϖ R ρ e Creturn : ℝ) (he : e ≠ 0)
    (hϖ : 0 ≤ ϖ / e) (hR : 0 ≤ R) (hmesh : (ϖ / e) / (N : ℝ) ≤ R)
    (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1)) :
    let yc := streamFlow φ hφ ((l₀ : ℝ) * ocTauPP α q Λ m) (spatialPatchCenter N k) t
    let U := fun i => preparationReferenceHkWindowPull hc hcover hTau ha (K i) (hK i) t
      (spatialPatchLocalization hζ N hN k (K i) (f i))
    ENNReal.ofReal ((Creturn * |e|) ^ 2) *
      (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K i)
        (planeCarrierAffine e he yc (U i))) ≤
      ENNReal.ofReal (Creturn ^ 2) *
      ENNReal.ofReal ((1 + 2 * (preparationPieceFlowJetBudget Cchart
        (ocEpsilon q Λ (m - 1)) 1 * R) ^ 2) ^ n) *
      ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1)) ^ 2) *
      ∑ i, ENNReal.ofReal ((π i)⁻¹) * ENNReal.ofReal
        (factorialNormSq ρ (spatialPatchLocalization hζ N hN k (K i) (f i)).val) := by
  intro yc U
  rw [planeAffine_family_initial_return_price]
  let M := ENNReal.ofReal ((1 + 2 * (preparationPieceFlowJetBudget Cchart
    (ocEpsilon q Λ (m - 1)) 1 * R) ^ 2) ^ n)
  let C := ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1)) ^ 2)
  have hb (i : ι) : weightedFactorialNormSq n (ϖ / e) yc ρ (K i) (U i) ≤
      M * C * ENNReal.ofReal (factorialNormSq ρ
        (spatialPatchLocalization hζ N hN k (K i) (f i)).val) := by
    have hp := preparationReference_localized_energy_le hc hcover hTau ha hE
      (K i) (hK i) t ht hζ N hN k (f i) n (ϖ / e) R ρ hϖ hR hmesh hρ hρE
    have hm := (sq_le_sq₀ (compositionFactorialNormBound_nonneg _ _)
      (compositionFactorialNormBound_nonneg _ _)).mpr
      (compositionFactorialNormBound_mono (preparationFlowJetConstant Cchart) (hK i))
    exact hp.trans (mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hm)) le_rfl)
  have hs : (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n (ϖ / e) yc ρ (K i) (U i)) ≤
      M * C * ∑ i, ENNReal.ofReal ((π i)⁻¹) * ENNReal.ofReal
        (factorialNormSq ρ (spatialPatchLocalization hζ N hN k (K i) (f i)).val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul' (le_refl (ENNReal.ofReal ((π i)⁻¹))) (hb i)
    exact hh.trans_eq (mul_left_comm _ _ _)
  have hh := mul_le_mul' (le_refl (ENNReal.ofReal (Creturn ^ 2))) hs
  simpa only [mul_assoc] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A spatially frozen homogeneous base response has a uniform initial gradient
budget using only the certified time window of the metric. -/

theorem frozenWindow_homogeneous_family_gradient_energy (n Kmax : ℕ) (Cw : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      (K : ι → ℕ) (_hK : ∀ i, K i ≤ Kmax) (a b ρ : ℝ) (_hab : a ≤ b) (_hρ : 0 < ρ)
      (v : ℝ → Vec 2 → Vec 2)
      (_hvm : Measurable fun p : Set.Icc a b × Vec 2 => v p.1 p.2)
      (_hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
      (_hbv : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
      (_hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
      (strain B lam : ℝ) (_hs0 : 0 ≤ strain) (_hB : 1 ≤ B) (_hlam : 0 < lam)
      (_hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc a b, ∀ x,
        ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
          strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
      (_hscale : B * ρ / lam ≤ 1 / 2) (_hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
      (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (_hM : Measurable M)
      (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
      (_hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
      (_hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
        |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
          g * ∑ i, ξ i ^ 2)
      (ϖ : ℝ) (_W : ChartWeights (fun t _ => M t) v a (b - a) ϖ 0 n Cw)
      (π : ι → ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
      (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
      (Z : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
      (_hs : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
        (fun _ i => f i) (fun _ _ _ => 0) (fun _ i => u i) (fun _ i => w i))
      (_hZ : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) (Z i) (w i)),
      planeAllMomentFamilyGradientEnergy K n ϖ ρ (volume.restrict (Set.Icc a b)) π Z ≤
        ENNReal.ofReal C * ∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq n ϖ 0 ρ (K i) (f i) := by
  obtain ⟨C, hC, hb⟩ := scalarPlane_homogeneous_family_gradient_energy n Kmax (fun _ => 0) Cw
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ K hK a b ρ hab hρ v hvm hv hbv hdiv strain B lam hs0 hB hlam
    hjets hscale hstrain M hM g hg hg4 hsym hquad ϖ W π f u w Z hs hZ
  let Mc : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => M (max a (min t b))
  have hMc : Measurable Mc := matrix_time_clamp_measurable hM a b
  have hsc : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => Mc t))
      (fun _ i => K i) a b v (fun _ i => f i) (fun _ _ _ => 0)
      (fun _ i => u i) (fun _ i => w i) := by
    apply isPlaneChainFrom_geometryScalarData_congr _ hs
    intro t ht
    exact metricClamp_of_mem (fun t _ => M t) ht
  apply hb K hK a b hab ρ 0 hρ le_rfl (by simp only [mul_zero]; norm_num)
    v hbv hvm hv hdiv strain B lam hs0 hB hlam hjets hscale hstrain
    (fun t _ => Mc t) g hg hg4 _
    (fun t _ _ => hsym _ (clampTime_mem hab t))
    (fun t _ ξ => hquad _ (clampTime_mem hab t) ξ)
    (fun _ _ _ _ => contDiff_const) _
    a (b - a) ϖ 0 le_rfl (by rw [add_sub_cancel])
    (chartWeightsMetricClamp W) f π u w Z hsc hZ rfl
  · exact hMc.comp measurable_fst.subtype_val
  · intro t ht z j hj hjmax k l
    rw [iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
    simp only [Pi.zero_apply, norm_zero, zero_mul, le_refl]

/-! A named family-independent constant for the homogeneous frozen base energy. -/

def frozenWindowHomogeneousGradientConstant.{u, v} (n Kmax : ℕ) (Cw : ℕ → ℝ) : ℝ :=
  Classical.choose (frozenWindow_homogeneous_family_gradient_energy.{u, v} n Kmax Cw)

theorem frozenWindowHomogeneousGradientConstant_spec.{u, v} (n Kmax : ℕ) (Cw : ℕ → ℝ) :
    0 ≤ frozenWindowHomogeneousGradientConstant.{u, v} n Kmax Cw ∧
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      (K : ι → ℕ) (_hK : ∀ i, K i ≤ Kmax) (a b ρ : ℝ) (_hab : a ≤ b) (_hρ : 0 < ρ)
      (v : ℝ → Vec 2 → Vec 2)
      (_hvm : Measurable fun p : Set.Icc a b × Vec 2 => v p.1 p.2)
      (_hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
      (_hbv : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
      (_hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
      (strain B lam : ℝ) (_hs0 : 0 ≤ strain) (_hB : 1 ≤ B) (_hlam : 0 < lam)
      (_hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc a b, ∀ x,
        ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
          strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
      (_hscale : B * ρ / lam ≤ 1 / 2) (_hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
      (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (_hM : Measurable M)
      (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
      (_hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
      (_hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
        |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
          g * ∑ i, ξ i ^ 2)
      (ϖ : ℝ) (_W : ChartWeights (fun t _ => M t) v a (b - a) ϖ 0 n Cw)
      (π : ι → ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
      (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
      (Z : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
      (_hs : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
        (fun _ i => f i) (fun _ _ _ => 0) (fun _ i => u i) (fun _ i => w i))
      (_hZ : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) (Z i) (w i)),
      planeAllMomentFamilyGradientEnergy K n ϖ ρ (volume.restrict (Set.Icc a b)) π Z ≤
        ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} n Kmax Cw) * ∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq n ϖ 0 ρ (K i) (f i) :=
  Classical.choose_spec (frozenWindow_homogeneous_family_gradient_energy.{u, v} n Kmax Cw)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
open AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The true preparation native traces transfer across the renewal with the existing uniform reserved polynomial-moment price. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable (hc : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

theorem preparationReferenceCellNativeCurve_renewal_polynomial_energy_le
    (s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hm : 1 ≤ m)
    (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Icc a b)
    (ν : ℝ) (hν : ν ≠ 0) (he : ocEpsilon q Λ m ≠ 0) (y₀ : Vec 2)
    (U : ℝ → PlaneHk univ J E) (t : ℝ) (ht : t ∈ Icc a b)
    (n M Jmax : ℕ) (hn : n ≤ M) (hmax : J ≤ Jmax)
    (ϖ r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    let seed := ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀
    let yc := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 1
    let yc' := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 2
    weightedFactorialNormSq n ϖ 0 r J
      (preparationWindowReferenceCellNativeCurve hc hcover
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext ha J hJ
        ν (ocEpsilon q Λ m) he yc' U (((ocEpsilon q Λ m)⁻¹) ^ 2 * (ν * t))) ≤
      ENNReal.ofReal (cellTransitionMomentBudget Jmax M) * weightedFactorialNormSq n ϖ 0 r J
        (preparationReferenceCellNativeCurve hc hcover hTau ha J hJ
          ν (ocEpsilon q Λ m) he yc U (((ocEpsilon q Λ m)⁻¹) ^ 2 * (ν * t))) := by
  intro seed yc yc'
  have hv := preparationReferenceCellNativeCurve_renewal_value_ae hc hcover hTau ha J hJ
    hnext ν hν he yc yc' U t ht
  have hv' : planeValue (preparationWindowReferenceCellNativeCurve hc hcover
      (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext ha J hJ
      ν (ocEpsilon q Λ m) he yc' U (((ocEpsilon q Λ m)⁻¹) ^ 2 * (ν * t))) =ᵐ[volume]
      fun z => planeValue (preparationReferenceCellNativeCurve hc hcover hTau ha J hJ
        ν (ocEpsilon q Λ m) he yc U (((ocEpsilon q Λ m)⁻¹) ^ 2 * (ν * t)))
        (ocCellTransition α q Λ m (Φ (m - 1)) hφ ((l₀ - 1) + (1 : ℕ)) yc yc' z) := by
    simpa only [Nat.cast_one, sub_add_cancel] using hv
  exact cellTransition_polynomial_factorial_energy_reserved α s hα₀ hα₁ hs₀ hs₁ q hq
    ζ hζ Λ hΛ Φ hseq m hm hφ (l₀ - 1) seed 1 ϖ n M hn hmax _ _ r hr hr1 hv'

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Uniform native Piola array prices are paid by the original identity's
pointwise molecular price, preserving its full positive graph sum. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem pointwiseOriginalIdentityRemainderPrice_lower_order_sum_le
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (Ks Kmax : ℕ) (dom : F.Domain)
    (ν e E ρ CR ζ : ℝ) (hν : 0 ≤ ν) (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (hCR : 0 ≤ CR) (hζ : 0 ≤ ζ)
    (v u : ι) (γ : F.Γ v u) (r : ℕ) (hr : 1 ≤ r) :
    (Real.sqrt (multiplicationDensityBudget (K v)) * CR * (Kmax.factorial : ℝ) ^ 2 * ζ ^ (Ks + 1)) *
      (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
          E ^ (Ks + 1) * molecularRealPrice ν ρ (K v) (d - 2)
            (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => dom x.1 x.2)
              (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))) * ‖(F.identity v u γ).map‖ ≤
      pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u γ := by
  unfold pointwiseOriginalIdentityRemainderPrice
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  · intro d _ _
    apply Finset.sum_nonneg
    intro I _
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (pow_nonneg hE _) (molecularRealPrice_nonneg ν ρ hν hρ _ _ _)

theorem nativeArray_pointwise_identity_remainder_price_le
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (Ks Kmax : ℕ) (hK : ∀ v, K v ≤ Kmax)
    (dom : F.Domain) (ν e E ρ Cnat ζ : ℝ)
    (hν : 0 ≤ ν) (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (hCnat : 0 ≤ Cnat) (hζ : 0 ≤ ζ)
    (N : ℕ) (Cpiola : ℝ) (hCp : 0 ≤ Cpiola) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (hr : 1 ≤ r) (hrD : r ≤ D) :
    (∑ _β : Fin 2 × DerivativeWord2 r, Real.sqrt (multiplicationDensityBudget (K v)) *
      (transportedPolynomialUniformReservePrice N D (K v) Cpiola *
        (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
            Cnat * ζ ^ (Ks + 1) * ((Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) *
              molecularRealPrice ν ρ (K v) (d - 2)
                (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => dom x.1 x.2)
                  (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)))) * ‖(F.identity v u γ).map‖)) ≤
      pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E ρ
        (nativeArrayUniformTransportPrice N D Kmax Cpiola * Cnat) ζ v u γ := by
  classical
  let q := fun d (I : DerivativeWord2 (d - 1)) => E ^ (Ks + 1) *
    molecularRealPrice ν ρ (K v) (d - 2)
      (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  let S := ∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
    ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
      Cnat * ζ ^ (Ks + 1) * ((Kmax.factorial : ℝ) ^ 2 * q d I)
  have hq d I : 0 ≤ q d I :=
    mul_nonneg (pow_nonneg hE _) (molecularRealPrice_nonneg ν ρ hν hρ _ _ _)
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro d _
    apply Finset.sum_nonneg
    intro I _
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg hCnat (pow_nonneg hζ _)) (mul_nonneg (sq_nonneg _) (hq d I))
  have heq : S = Cnat * ζ ^ (Ks + 1) * (Kmax.factorial : ℝ) ^ 2 *
      (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2, q d I) := by
    dsimp only [S]
    simp only [mul_assoc, ← Finset.mul_sum]
  have hprice := nativeArray_uniform_transport_sum_le N D Kmax r (K v) hrD (hK v)
    Cpiola S ‖(F.identity v u γ).map‖ hCp hS (norm_nonneg _)
  have hh := pointwiseOriginalIdentityRemainderPrice_lower_order_sum_le F K Ks Kmax dom ν e E ρ
    (nativeArrayUniformTransportPrice N D Kmax Cpiola * Cnat) ζ hν hE hρ
    (mul_nonneg (nativeArrayUniformTransportPrice_nonneg N D Kmax Cpiola hCp) hCnat) hζ v u γ r hr
  calc
    _ ≤ Real.sqrt (multiplicationDensityBudget (K v)) *
        (nativeArrayUniformTransportPrice N D Kmax Cpiola * S * ‖(F.identity v u γ).map‖) := by
      simpa only [S, q, mul_assoc] using hprice
    _ ≤ _ := by
      rw [heq]
      convert hh using 1
      dsimp only [q]
      ring

end AVRegularity.CycleJointProofs
end
end
