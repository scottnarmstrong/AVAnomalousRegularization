-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.NativeRawOriginalFamilyTaylorSplitEdges
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import AVRegularity.CycleJoint.FamilyNaturalTimeRemainderReservedJets
public import AVRegularity.CycleJoint.PlaneAllMomentNativeResidualBudget
import AVRegularity.CycleJoint.PreparationScaledFlowBudget

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! The original window-restricted measurability suffices for every actual homogeneous atom transfer. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem homogeneousIntegralAtoms_actual_time_transfer_of_restricted (K : ι → ℕ) (D : ℕ) (i : ι)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (S : Set ℝ) (hS : MeasurableSet S)
    (hSae : ∀ᵐ t ∂μ, t ∈ S)
    (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ S, Continuous (v t))
    (hvm : Measurable (Function.uncurry v))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ S, ∀ x, ‖v t x‖ ≤ V)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hc : ∀ i' d t, t ∈ S → Continuous (A i i' d t))
    (hj : ∀ i' d, Measurable (fun p : S × Vec 2 => A i i' d p.1 p.2))
    (MC : ∀ i', admissibleOrders K D i i' → ℝ)
    (hMC : ∀ i' d, 0 ≤ MC i' d)
    (hbA : ∀ i' d t, t ∈ S → ∀ x, ‖A i i' d t x‖ ≤ MC i' d)
    (hpA : ∀ i' d t, t ∈ S → AVenhance.IsZ2Periodic (A i i' d t))
    (f : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hf : ∀ i, MemLp (f i) 2 μ) (z : Vec 2)
    (M : ι → ℝ → ℝ) (hM : ∀ i, MemLp (M i) 2 μ)
    (hw : ∀ i α, ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f i t).toFunction.jet α y) volume)
    (hb : ∀ i α, ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f i t).toFunction.jet α y) 2 volume ≤ ENNReal.ofReal ‖M i t‖)
    (T : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hr : ∀ i α, ∀ᵐ t ∂μ, (T i t).toFunction.jet α =ᵐ[volume]
      periodizeRawJet (f i t).toFunction.jet α)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (φ : TorusHk 1 (h i)) :
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
    let G := fun j (n : Fin 2 → ℤ) => planeHomogeneousIntegralAtom K D ν v A
      (fun i t => planeCarrierTranslation (K i + 1) (AVenhance.latticeShift n) (f i t)) i ψ j
    let P := torusHomogeneousIntegralAtom K D ν v A T i ψ
    ∀ j : Fin 3, (∀ n, Integrable (G j n) μ) ∧
      Summable (fun n => ∫ t, ‖G j n t‖ ∂μ) ∧ Integrable (P j) μ ∧
      (∑' n, ∫ t, G j n t ∂μ) = ∫ t, P j t ∂μ := by
  dsimp only
  let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
  let Aw := fun i₁ i₂ d => windowedPhysicalCoefficient S (A i₁ i₂ d)
  have heq (i₁ i₂ : ι) (d : admissibleOrders K D i₁ i₂) (t : ℝ) (ht : t ∈ S) :
      Aw i₁ i₂ d t = A i₁ i₂ d t := windowedPhysicalCoefficient_eq S (A i₁ i₂ d) t ht
  have hcW (i' : ι) (d : admissibleOrders K D i i') (t : ℝ) (ht : t ∈ S) :
      Continuous (Aw i i' d t) := by
    rw [heq i i' d t ht]
    exact hc i' d t ht
  have hjW (i' : ι) (d : admissibleOrders K D i i') : Measurable (Function.uncurry (Aw i i' d)) :=
    windowedPhysicalCoefficient_joint_measurable_of_restricted S hS (A i i' d) (hj i' d)
  have hbW (i' : ι) (d : admissibleOrders K D i i') (t : ℝ) (ht : t ∈ S) (x : Vec 2) :
      ‖Aw i i' d t x‖ ≤ MC i' d := by
    rw [heq i i' d t ht]
    exact hbA i' d t ht x
  have hpW (i' : ι) (d : admissibleOrders K D i i') (t : ℝ) (ht : t ∈ S) :
      AVenhance.IsZ2Periodic (Aw i i' d t) := by
    rw [heq i i' d t ht]
    exact hpA i' d t ht
  have hprior := homogeneousIntegralAtoms_actual_time_transfer K D i μ S hS hSae
    ν v hv hvm V hV hbv Aw hcW hjW MC hMC hbW hpW f hf z M hM hw hb T hr hζ φ
  have hG (j : Fin 3) (n : Fin 2 → ℤ) :
      planeHomogeneousIntegralAtom K D ν v Aw
        (fun i t => planeCarrierTranslation (K i + 1) (AVenhance.latticeShift n) (f i t)) i ψ j =ᵐ[μ]
      planeHomogeneousIntegralAtom K D ν v A
        (fun i t => planeCarrierTranslation (K i + 1) (AVenhance.latticeShift n) (f i t)) i ψ j :=
    hSae.mono (fun t ht => planeHomogeneousIntegralAtom_coefficients_congr K D ν v Aw A _ i ψ j t
      (fun i' d => heq i i' d t ht))
  have hP (j : Fin 3) : torusHomogeneousIntegralAtom K D ν v Aw T i ψ j =ᵐ[μ]
      torusHomogeneousIntegralAtom K D ν v A T i ψ j :=
    hSae.mono (fun t ht => torusHomogeneousIntegralAtom_coefficients_congr K D ν v Aw A T i ψ j t
      (fun i' d => heq i i' d t ht))
  intro j
  refine ⟨fun n => ((hprior j).1 n).congr (hG j n), ?_,
    (hprior j).2.2.1.congr (hP j), ?_⟩
  · exact (hprior j).2.1.congr (fun n => integral_congr_ae
      ((hG j n).mono (fun _ hx => congrArg norm hx)))
  · calc
      _ = ∑' n : Fin 2 → ℤ, ∫ t, planeHomogeneousIntegralAtom K D ν v Aw
          (fun i t => planeCarrierTranslation (K i + 1) (AVenhance.latticeShift n) (f i t)) i ψ j t ∂μ :=
        tsum_congr (fun n => integral_congr_ae (hG j n).symm)
      _ = ∫ t, torusHomogeneousIntegralAtom K D ν v Aw T i ψ j t ∂μ := (hprior j).2.2.2
      _ = _ := integral_congr_ae (hP j)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! An affine native response identity yields the actual weak solution for its prescribed forcing and lift. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance affineInputNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance affineInputNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance affineInputCarrierAdd (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance affineInputCarrierModule (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance

variable (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
  (K : ι → ℕ) (a b ϖ ρ : ℝ)
  (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
  (Q : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
    (volume.restrict (Set.Icc a b)))
  (f : ∀ i, PlaneHk Set.univ (K i) (h i))
  (u₀ : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
  (w₀ : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
  (Z W : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)))

theorem planeComponentAllMomentResponse_affine_input
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (K i) a b ϖ ρ (R i))
    (hbase : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ _ _ => 0) (fun _ i => u₀ i) (fun _ i => w₀ i))
    (hZ : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Z i) (w₀ i))
    (hfixed : W = Z + (fun i => R i (Q i))) :
    ∃ (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
      (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
        (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) ∧
      ∀ i, PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (Q i) (F i) ∧
        PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (W i) (w i) := by
  obtain ⟨F, u, w, hs, hrep⟩ := planeComponentAllMomentResponse_assemble M v K a b ϖ ρ R hR
    Q
  have hb := scalarPlaneChain_diagonalMetric_solution K a b v (fun t _ => M t)
    f (fun _ _ => 0) u₀ w₀ hbase
  have hy := scalarPlaneChain_diagonalMetric_solution K a b v (fun t _ => M t)
    (fun _ => 0) F u w hs
  have hsum := planeWeakSolution_add K 2 1 a b v
    (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1))
    f (fun _ => 0) (fun _ _ => 0) F (fun _ _ => 0) (fun _ _ => 0)
    u₀ u w₀ w hb hy
  simp only [add_zero, zero_add] at hsum
  refine ⟨F, fun i t => u₀ i t + u i t, fun i t => w₀ i t + w i t,
    planeDiagonalMetric_scalar_solution K a b v (fun t _ => M t) _ _ _ _ hsum, ?_⟩
  intro i
  refine ⟨(hrep i).1, ?_⟩
  have hi : W i = Z i + R i (Q i) := congrFun hfixed i
  rw [hi]
  exact planeTimeAllMomentRepresents_add (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
    (Z i) (R i (Q i)) (w₀ i) (w i) (hZ i) (hrep i).2

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! A transport time derivative of a compact test yields the exact physical transport pairing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_test_transport_correction (u : PlaneHk univ 1 E) (e : E)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ (fun y => v y i) x (basisVec i) = 0)
    (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) (t : ℝ)
    (hd : ∀ x, deriv (fun r => f (r, x)) t =
      -vecDot (spaceGrad (fun y => f (t, y)) x) (v x)) :
    (∫ x, deriv (fun r => f (r, x)) t * inner ℝ (planeHkValueOperator 1 u x) e) =
      ∫ x, f (t, x) * ∑ i : Fin 2, v x i * inner ℝ (planeH1GradientOperator u i x) e := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun x => f (t, x)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hc := compactSpacetime_slice_compact f hs t
  have hp := planeH1_compact_weak_transport u e v hv hdiv (fun x => f (t, x)) hq hc
  have hcomm : (fun x => inner ℝ e (planeHkValueOperator 1 u x)) =
      (fun x => inner ℝ (planeHkValueOperator 1 u x) e) := by
    funext x
    exact real_inner_comm _ _
  have hgcomm : (fun i x => inner ℝ e (planeH1GradientOperator u i x)) =
      (fun i x => inner ℝ (planeH1GradientOperator u i x) e) := by
    funext i x
    exact real_inner_comm _ _
  change (∫ x, f (t, x) * ∑ i : Fin 2, v x i *
      (fun i x => inner ℝ e (planeH1GradientOperator u i x)) i x) =
    -(∫ x, (∑ i : Fin 2, v x i * fderiv ℝ (fun y => f (t, y)) x (basisVec i)) *
      (fun x => inner ℝ e (planeHkValueOperator 1 u x)) x) at hp
  rw [hcomm, hgcomm] at hp
  apply Eq.trans _ hp.symm
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [hd]
    simp only [vecDot, spaceGrad, Fin.sum_univ_two]
    ring

end AVRegularity.CycleJointProofs
end
end

section
/-! The genuine normalized source flux splits into the finite natural Taylor
flux and the very same padded original remainder arrays used in the mass budget. -/

@[expose] public noncomputable section

open Homogenization AVenhance AVRegularity.Sobolev
  AVRegularity.CoupledEnergyPlane.Variational

namespace AVRegularity.CycleJointProofs

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationReferenceCellSourceFlux_constructed_split
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hν : ν ≠ 0) (he : 0 < e) (actual : ∀ p, Ctx p)
    (K : ι → ℕ) (hdesc : F.IsDescending K) (v : ι) (Ks : ℕ) (s : ℝ)
    (yc z : Vec 2) (a b τ : ℝ) (hτ : τ ∈ Set.Icc a b)
    (htime : ν⁻¹ * (e ^ 2 * τ) ∈ Set.Icc tS tZ)
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    planeRawCouplingFlux K D τ
      (preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc) U v z =
    (∑ u, ∑ γ : F.Γ v u, ∑ j : Fin D, ∑ p ∈ (F.locally_finite tS tZ).toFinset,
      naturalFamilyTaylorNativeArray Ks F p (actual p) v u γ (ν⁻¹ * e ^ 2) hφ
        (F.piece p).anchor s e E yc (j.val + 1) τ z
        (WithLp.toLp 2 (fun I => planeJetOrder (U u) (j.val + 1) I z))) +
    (∑ u, ∑ γ : F.Γ v u, ∑ j : Fin D, ∑ p ∈ (F.locally_finite tS tZ).toFinset,
      naturalFamilyRemainderNativeArray Ks F p (actual p) v u γ (ν⁻¹ * e ^ 2) a b hφ
        (F.piece p).anchor s e E yc (j.val + 1) τ z
        (WithLp.toLp 2 (fun I => planeJetOrder (U u) (j.val + 1) I z))) := by
  classical
  let H := fun u (γ : F.Γ v u) r =>
    ∑ p ∈ (F.locally_finite tS tZ).toFinset,
      (naturalFamilyTaylorNativeArray Ks F p (actual p) v u γ (ν⁻¹ * e ^ 2) hφ
        (F.piece p).anchor s e E yc r τ z +
      naturalFamilyRemainderNativeArray Ks F p (actual p) v u γ (ν⁻¹ * e ^ 2) a b hφ
        (F.piece p).anchor s e E yc r τ z)
        (WithLp.toLp 2 (fun I => planeJetOrder (U u) r I z))
  have hz (u : ι) (γ : F.Γ v u) (r : ℕ) (hr : (F.identity v u γ).maxOrder ≤ r) :
      H u γ r = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    rw [naturalFamilyTaylorNativeArray_zero_at_or_above _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr,
      naturalFamilyRemainderNativeArray_zero_at_or_above _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr]
    simp only [add_zero, zero_apply]
  have hread : planeRawCouplingFlux K D τ
      (preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc) U v z =
      ∑ u, ∑ d : admissibleOrders K D v u, ∑ γ : F.Γ v u, H u γ (d.val - 1) := by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro d _
    rw [preparationReferenceCellSourceCoefficient_constructed_split F hc ν e E hν he actual
      K v u d Ks s yc z a b τ hτ htime]
    have hdres : d.val - 1 ≤ K u + 1 := by
      have hh := admissibleOrders_reserve K D v u d
      omega
    simp only [sum_apply, H, planeJetOrder, dite_eq_left hdres]
  rw [hread]
  have horders (u : ι) :
      (∑ d : admissibleOrders K D v u, ∑ γ : F.Γ v u, H u γ (d.val - 1)) =
        ∑ γ : F.Γ v u, ∑ j : Fin D, H u γ (j.val + 1) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun γ _ => originalNativeOrder_admissible_eq_padded F K hdesc
      v u γ (H u γ) (hz u γ))
  simp_rw [horders]
  simp only [H, add_apply, Finset.sum_add_distrib]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The literal full coefficient rows construct the actual coupled residual of a scalar weak response. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {a b : ℝ} {K : ι → ℕ} {D : ℕ} {v : ℝ → Vec 2 → Vec 2}

variable (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (hD : 2 ≤ D)
  (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
  {A' : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
  {f : ∀ i, PlaneHk Set.univ (K i) (h i)}
  {F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
  {u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
  {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}

variable
  (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b
    (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1) i j d) ≠ ⊤)
  (hA' : ∀ i j d, coefficientSeminorm ρ (K i) a b (A' i j d) ≠ ⊤)
  (hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ)
    (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1) i j d t))
  (hC' : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A' i j d t))

include hab hρ hD hA hA' hC hC' in
theorem scalarPlaneChain_native_residual_construction
    (hs : IsPlaneChainFrom (geometryScalarData 2 G) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i)) :
    let Ffull := planeCouplingFluxRow hab ρ hρ K D A' hA' hC' w
    let Fdiag := planeCouplingFluxRow hab ρ hρ K D
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1)) hA hC w
    IsCoupledWeakSolutionPlane 1 a b v D K A' f
      (fun i t => F i t - Ffull i t + Fdiag i t) (fun _ _ => 0) u w := by
  apply scalarPlaneChain_native_residual_order_assembly ρ hρ hD G hA hA' hC hC' _ hs
  intro i
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  let Ffull := planeCouplingFluxRow hab ρ hρ K D A' hA' hC' w
  let Fdiag := planeCouplingFluxRow hab ρ hρ K D
    (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1)) hA hC w
  have hr := planeCouplingFluxRow_planeValue_ae hab ρ hρ K D A' hA' hC' w i t ht
  have hd := planeCouplingFluxRow_planeValue_ae hab ρ hρ K D
    (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1)) hA hC w i t ht
  have he : ∀ᵐ z ∂volume, planeValue (F i t) z =
      planeRawCouplingFlux K D t A' (fun j => w j t) i z -
        planeRawCouplingFlux K D t
          (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1))
          (fun j => w j t) i z + planeValue (F i t - Ffull i t + Fdiag i t) z := by
    filter_upwards [hr, hd, planeValue_sub_ae (F i t) (Ffull i t),
      planeValue_add_ae (F i t - Ffull i t) (Fdiag i t)] with z hzr hzd hzs hza
    rw [hza, hzs, hzr, hzd]
    abel
  filter_upwards [he] with z hz
  simpa only [planeValue_eq_rawValue, Ffull, Fdiag] using hz

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Positive assembly of actual retained native piece maps preserves their common density price without counting pieces. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

theorem familyPositive_allMoment_map_density_le
    (F : ChartedFamily ι h D P Ctx) (S : Finset P)
    (K : ℕ) (s ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (T : S → X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (B : X → ℝ → Vec 2 → ℝ)
    (hB : ∀ x, ∀ᵐ t ∂μ, ∀ z, 0 ≤ B x t z)
    (hb : ∀ p x, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (T p x) t) z ≤
        F.weight p.val (s * t) ^ 2 * B x t z) :
    ∀ x, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ
        (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ ((∑ p, T p) x) t) z ≤ B x t z := by
  classical
  intro x
  have hh := familyWeighted_native_sum_density_le F S s ρ μ
    (fun p t => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (T p x) t) (B x) (hB x)
    (fun p => hb p x)
  have he := planeTimeAllMomentCarrier_sum_ae K ϖ ρ zc μ (fun p => T p x)
  simp only [LinearMap.sum_apply]
  filter_upwards [hh, he] with t ht heq
  rw [heq]
  exact ht

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleReference AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The preparation chart certificate transports rough native factorial norms with a fixed reserve-only constant. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem preparation_planeHk_factorial_pullback
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hE : 0 < ocEpsilon q Λ (m - 1))
    (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    {K : ℕ} (hK : K ≤ Jchart + 1) (U : PlaneHk univ K E) :
    ∃ V : PlaneHk univ K E,
      planeValue V =ᵐ[volume] (fun y => planeValue U (AVRegularity.streamFlow φ hφ r y σ)) ∧
      Real.sqrt (factorialNormSq ρ V.val) ≤
        compositionFactorialNormBound (preparationFlowJetConstant Cchart) K *
          Real.sqrt (factorialNormSq ρ U.val) := by
  let B := fun j => preparationFlowJetConstant Cchart j * (ocEpsilon q Λ (m - 1))⁻¹ ^ (j - 1)
  have hB j (_ : 1 ≤ j) (_ : j ≤ K) : 0 ≤ B j :=
    mul_nonneg (preparationFlowJetConstant_nonneg Cchart j) (pow_nonneg (inv_nonneg.mpr hE.le) _)
  have hb j (hj : 1 ≤ j) (hjK : j ≤ K) (x : Vec 2) :
      ‖iteratedFDeriv ℝ j (fun y => AVRegularity.streamFlow φ hφ r y σ) x‖ ≤ B j :=
    preparation_flow_positive_jets hc ha r σ hr hσ hage j hj (hjK.trans hK) x
  let X := streamFlowHomeomorph hφ r σ
  let hX := streamFlow_spatial_smooth hφ r σ
  let hμ := streamFlow_measurePreserving hφ r σ
  refine ⟨planeHkSmoothPullback X hX hμ B hB hb U,
    planeHkSmoothPullback_value_ae X hX hμ B hB hb U, ?_⟩
  exact planeHkScaledPullback_factorial_norm_le X hX hμ B hB hb hρ
    (preparationFlowJetConstant Cchart)
    (fun j _ _ => preparation_scaled_flow_budget hE hρ hρE Cchart j) U

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual retained source array has all qualitative coefficient data on each smaller cell-time window. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationReferenceCellSourceCoefficient_subwindow_data
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hν : 0 < ν) (he : e ≠ 0) (hE : E ≠ 0) (K : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E K)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (s : ℝ) (yc : Vec 2)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (ρ r C : ℝ) (hρ : 0 < ρ)
    (B : ι → ι → ℝ)
    (hsamp : IsSampledEnvelope (referenceChartedFamily F hφ s) π K actual a b ν e E ρ C B)
    (u0 u1 : ℝ)
    (hsub : Set.Icc u0 u1 ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b))) :
    let A := preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc
    (∀ v u d, coefficientSeminorm r (K v) u0 u1 (A v u d) ≠ ⊤) ∧
    (∀ v u d t, t ∈ Set.Icc u0 u1 → ContDiff ℝ (K v : ℕ) (A v u d t)) ∧
    (∀ v u d, Measurable (fun p : Set.Icc u0 u1 × Vec 2 => A v u d p.1 p.2)) ∧
    (∀ v u, ¬ Nonempty (F.Γ v u) → ∀ d t z, t ∈ Set.Icc u0 u1 → A v u d t z = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v u d
    exact ne_top_of_le_ne_top
      (preparationReferenceCellSourceCoefficient_seminorm_ne_top F hφ s ν e E actual K yc
        π hπ a b ρ r C hν hρ he B hsamp v u d)
      (coefficientSeminorm_time_mono r (K v) u0 u1
        ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b)) hsub _)
  · intro v u d t ht
    exact preparationReferenceCellSourceCoefficient_contDiff F hc ν e E hν he hE K hs
      actual s yc v u d t (hsub ht)
  · intro v u d
    exact jointMeasurable_subwindow u0 u1
      ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b)) hsub _
      (preparationReferenceCellSourceCoefficient_joint_measurable F hc ν e E hν he K hs
        hmeas hwmeas actual s yc v u d)
  · intro v u hΓ d t z _
    have hz := preparationReferenceCellSourceCoefficient_zero_of_no_edge
      F hφ s ν e E actual K yc v u d hΓ
    exact congrFun (congrFun hz t) z

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The entire physical family flux reads its actual bounded native row operators, with all scalar budgets proved from the supplied smooth envelope and torus compatibility. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem planeRawCouplingFlux_family_actual_operators
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (ν e E a b : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι) (k : Fin 2)
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    (fun x => planeRawCouplingFlux K D t (edgeCoefficient F ν e E actual K) U v x k) =ᵐ[volume]
      fun x => ∑ u, ∑ γ : F.Γ v u, ∑ p : (F.locally_finite t t).toFinset,
        F.weight p t • activePieceTransportedScalarRowOperator F ν e E a b n hs actual hT he
          t ht p v u γ (K u + 1) k (mapPlaneHk (F.identity v u γ).map (U u)) x := by
  let c (u : ι) (γ : F.Γ v u) (p : (F.locally_finite t t).toFinset) :=
    pieceTransportedNativeScalarJetCoefficient F ν e E p (actual p) v u γ t (K u + 1) k
  have hc (u : ι) (γ : F.Γ v u) (p : (F.locally_finite t t).toFinset) :
      ∀ j, Continuous (c u γ p j) :=
    (active_piece_native_scalar_rows_continuous F ν e E a b n hs t ht p (actual p)
      v u γ (K u + 1)).2 k
  have hp (u : ι) (γ : F.Γ v u) (p : (F.locally_finite t t).toFinset) :
      ∀ j, AVenhance.IsZ2Periodic (c u γ p j) :=
    pieceTransportedNativeScalarJetCoefficient_periodic F ν e E actual hT he p v u γ t (K u + 1) k
  let budget (u : ι) (γ : F.Γ v u) (p : (F.locally_finite t t).toFinset) :=
    periodicScalarRow_exists_budget (c u γ p) (hc u γ p) (hp u γ p)
  exact planeRawCouplingFlux_family_native_rows F K hdesc ν e E actual t v k hc
    (fun u γ p => (budget u γ p).choose)
    (fun u γ p => (budget u γ p).choose_spec.1)
    (fun u γ p => (budget u γ p).choose_spec.2) U

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The independent active piece rows assemble into a genuine Hilbert-valued physical flux, with the exact literal coupled readout. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

variable (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (ν e E a b : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u))

def preparationPhysicalNativeFlux : PlaneFluxL2 (h v) :=
  WithLp.toLp 2 (fun k => ∑ u, ∑ γ : F.Γ v u, ∑ p : (F.locally_finite t t).toFinset,
    F.weight p t • activePieceTransportedScalarRowOperator F ν e E a b n hs actual hT he
      t ht p v u γ (K u + 1) k (mapPlaneHk (F.identity v u γ).map (U u)))

theorem preparationPhysicalNativeFlux_ae (hdesc : F.IsDescending K) (k : Fin 2) :
    (preparationPhysicalNativeFlux F K ν e E a b n hs actual hT he t ht v U k : Vec 2 → h v)
      =ᵐ[volume] fun x =>
        planeRawCouplingFlux K D t (edgeCoefficient F ν e E actual K) U v x k := by
  classical
  let row (u : ι) (γ : F.Γ v u) (p : (F.locally_finite t t).toFinset) :=
    activePieceTransportedScalarRowOperator F ν e E a b n hs actual hT he
      t ht p v u γ (K u + 1) k (mapPlaneHk (F.identity v u γ).map (U u))
  have hp (u : ι) (γ : F.Γ v u) :
      (∑ p : (F.locally_finite t t).toFinset, F.weight p t • row u γ p : Lp (h v) 2 volume)
        =ᵐ[volume] fun x => ∑ p : (F.locally_finite t t).toFinset,
          F.weight p t • row u γ p x :=
    planeLp_weighted_fintype_sum_ae (J := (F.locally_finite t t).toFinset)
      (fun p => F.weight p t) (row u γ)
  have hγ (u : ι) :
      (∑ γ : F.Γ v u, ∑ p : (F.locally_finite t t).toFinset, F.weight p t • row u γ p
        : Lp (h v) 2 volume) =ᵐ[volume] fun x =>
          ∑ γ : F.Γ v u, ∑ p : (F.locally_finite t t).toFinset,
            F.weight p t • row u γ p x := by
    apply (Lp.coeFn_fun_finsetSum _ _).trans
    have hh := eventuallyEq_sum (s := Finset.univ) (fun γ _ => hp u γ)
    filter_upwards [hh] with x hx
    simpa only [Finset.sum_apply] using hx
  have hu :
      (∑ u, ∑ γ : F.Γ v u, ∑ p : (F.locally_finite t t).toFinset,
        F.weight p t • row u γ p : Lp (h v) 2 volume) =ᵐ[volume] fun x =>
          ∑ u, ∑ γ : F.Γ v u, ∑ p : (F.locally_finite t t).toFinset,
            F.weight p t • row u γ p x := by
    apply (Lp.coeFn_fun_finsetSum _ _).trans
    have hh := eventuallyEq_sum (s := Finset.univ) (fun u _ => hγ u)
    filter_upwards [hh] with x hx
    simpa only [Finset.sum_apply] using hx
  exact hu.trans (planeRawCouplingFlux_family_actual_operators F K hdesc ν e E a b n hs
    actual hT he t ht v k U).symm
end

/-! The entire finite preparation source is one genuine continuous linear operator on the product of native energy carriers. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

variable (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (ν e E a b : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)


def preparationPhysicalNativeFluxOperator :
    (∀ u, PlaneHk Set.univ (K u + 1) (h u)) →L[ℝ] PlaneFluxL2 (h v) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => Lp (h v) 2 (volume : Measure (Vec 2)))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun k => ∑ u, ∑ γ : F.Γ v u,
        ∑ p : (F.locally_finite t t).toFinset,
          F.weight p t • (activePieceTransportedScalarRowOperator F ν e E a b n hs actual hT he
            t ht p v u γ (K u + 1) k).comp
              ((mapPlaneHkOperator (K u + 1) (F.identity v u γ).map).comp
                (ContinuousLinearMap.proj u))))

theorem preparationPhysicalNativeFluxOperator_apply
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    preparationPhysicalNativeFluxOperator F K ν e E a b n hs actual hT he t ht v U =
      preparationPhysicalNativeFlux F K ν e E a b n hs actual hT he t ht v U := by
  apply PiLp.ext
  intro k
  change (∑ u, ∑ γ : F.Γ v u, ∑ p : (F.locally_finite t t).toFinset,
    F.weight p t • (activePieceTransportedScalarRowOperator F ν e E a b n hs actual hT he
      t ht p v u γ (K u + 1) k).comp
        ((mapPlaneHkOperator (K u + 1) (F.identity v u γ).map).comp
          (ContinuousLinearMap.proj u))) U = _
  change _ = ∑ u, ∑ γ : F.Γ v u, ∑ p : (F.locally_finite t t).toFinset,
    F.weight p t • activePieceTransportedScalarRowOperator F ν e E a b n hs actual hT he
      t ht p v u γ (K u + 1) k (mapPlaneHk (F.identity v u γ).map (U u))
  simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, mapPlaneHkOperator_apply]
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleJointProofs

/-! The genuine physical preparation flux is exactly the finite weighted sum of its actual active constituent flux tensors. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem preparationPhysicalNativeFlux_eq_piece_sum
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (ν e E a b : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    preparationPhysicalNativeFlux F K ν e E a b n hs actual hT he t ht v U =
      ∑ u, ∑ γ : F.Γ v u, ∑ p : (F.locally_finite t t).toFinset,
        F.weight p t • WithLp.toLp 2 (fun k =>
          activePieceTransportedScalarRowOperator F ν e E a b n hs actual hT he
            t ht p v u γ (K u + 1) k (mapPlaneHk (F.identity v u γ).map (U u))) := by
  apply PiLp.ext
  intro k
  simp only [preparationPhysicalNativeFlux, WithLp.ofLp_sum, WithLp.ofLp_smul,
    WithLp.ofLp_toLp, Finset.sum_apply, Pi.smul_apply]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Finite mixed native response sums produce an actual scalar weak class with the terminal metric forcing retained. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance mixedScalarNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance mixedScalarNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance mixedScalarCarrierAdd (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance mixedScalarCarrierModule (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance

variable (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
  (K : ι → ℕ) (a b ϖ ρ : ℝ)
  (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
  (Lmetric Lsource : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
  (f : ∀ i, PlaneHk Set.univ (K i) (h i))
  (u₀ : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
  (w₀ : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
  (Z : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)))

variable {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem planeComponentAllMomentResponse_finite_mixed_solution
    (family : ChartedFamily ι h D P Ctx)
    (H J : ℕ) (hdepth : family.HasDepthAtMost H)
    (hM : HasSourceDegreeOn family 0 (nativeComponentResponseOperator R Lmetric))
    (hS : HasSourceDegreeOn family 1 (nativeComponentResponseOperator R Lsource))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (K i) a b ϖ ρ (R i))
    (hbase : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ _ _ => 0) (fun _ i => u₀ i) (fun _ i => w₀ i))
    (hZ : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Z i) (w₀ i)) :
    let U := finiteResponse 1 (nativeComponentResponseOperator R Lmetric)
      (nativeComponentResponseOperator R Lsource) Z
    let W := ∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n
    let T := ∑ n ∈ Finset.range (H + 1), U J n
    let Q := fun i => Lmetric i W + Lsource i W - Lmetric i T
    ∃ (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
      (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
        (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) ∧
      ∀ i, PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (Q i) (F i) ∧
        PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (W i) (w i) := by
  exact planeComponentAllMomentResponse_affine_input M v K a b ϖ ρ R _ f u₀ w₀ Z _
    hR hbase hZ
    (finiteNativeResponse_affine_forcing_identity family R Lmetric Lsource hM hS H J hdepth Z)
end

/-! Diagonal metric maps and retained original edge maps produce the finite coupled weak class with its terminal metric residual. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance retainedMixedScalarNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance retainedMixedScalarNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance retainedMixedScalarCarrierAdd (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance retainedMixedScalarCarrierModule (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance

variable (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
  (K : ι → ℕ) (a b ϖ ρ : ℝ)
  (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
  (Lmetric : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
  (Ledge : ∀ i j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
  (f : ∀ i, PlaneHk Set.univ (K i) (h i))
  (u₀ : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
  (w₀ : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
  (Z : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)))

variable {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem planeComponentAllMomentResponse_retained_edge_mixed_solution
    (family : ChartedFamily ι h D P Ctx)
    (H J : ℕ) (hdepth : family.HasDepthAtMost H)
    (hS : HasSourceDegreeOn family 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (K i) a b ϖ ρ (R i))
    (hbase : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ _ _ => 0) (fun _ i => u₀ i) (fun _ i => w₀ i))
    (hZ : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Z i) (w₀ i)) :
    let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
      (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z
    let W := ∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n
    let T := ∑ n ∈ Finset.range (H + 1), U J n
    let Q := fun i => Lmetric i (W i) + nativeFamilyEdgeForcingMap Ledge i W - Lmetric i (T i)
    ∃ (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
      (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
        (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) ∧
      ∀ i, PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (Q i) (F i) ∧
        PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (W i) (w i) := by
  exact planeComponentAllMomentResponse_finite_mixed_solution M v K a b ϖ ρ R
    (fun i => (Lmetric i).comp (LinearMap.proj i))
    (nativeFamilyEdgeForcingMap Ledge) f u₀ w₀ Z family H J hdepth
    (nativeDiagonalResponseOperator_sourceDegree family R Lmetric) hS hR hbase hZ
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Inverse material-chart tests are admissible strong H1 time tests for coupled solutions. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def materialChartTestField {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (η : ℝ × Vec 2 → ℝ) : ℝ × Vec 2 → ℝ :=
  fun p => η (p.1, AVRegularity.streamFlow φ hφ s p.2 p.1)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] in
theorem materialChartTestField_smooth {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (η : ℝ × Vec 2 → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContDiff ℝ (⊤ : ℕ∞) (materialChartTestField hφ s η) := by
  exact inverseStreamFlow_test_smooth hφ s (η := fun t x => η (t, x)) hη

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] in
theorem materialChartTestField_compact {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (η : ℝ × Vec 2 → ℝ) (hcη : HasCompactSupport η) :
    HasCompactSupport (materialChartTestField hφ s η) := by
  exact inverseStreamFlow_test_compact hφ s (η := fun t x => η (t, x)) hcη

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The finite mixed endpoint retains a genuine all-moment forcing representative for endpoint moment propagation. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance mixedEndpointForcingScalarNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance mixedEndpointForcingScalarNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance mixedEndpointForcingScalarCarrierAdd (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance mixedEndpointForcingScalarCarrierModule (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

variable (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
  (K : ι → ℕ) (a b ϖ ρ : ℝ)
  (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
  (Lmetric Lsource : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
  (lf : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
  (u₀ : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
  (w₀ : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
  (Z : X →ₗ[ℝ] (∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b))))

variable {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem planeComponentAllMomentResponse_finite_mixed_endpoint_with_forcing_linearMap
    (family : ChartedFamily ι h D P Ctx) (H J : ℕ) (hdepth : family.HasDepthAtMost H)
    (hM : HasSourceDegreeOn family 0 (nativeComponentResponseOperator R Lmetric))
    (hS : HasSourceDegreeOn family 1 (nativeComponentResponseOperator R Lsource))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (K i) a b ϖ ρ (R i))
    (hbase : ∀ x, IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t))
      (fun _ i => K i) a b v (fun _ i => lf x i) (fun _ _ _ => 0)
      (fun _ i => u₀ x i) (fun _ i => w₀ x i))
    (hZ : ∀ x i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (Z x i) (w₀ x i))
    (hab : a < b) (τ : ℝ) (hτ : τ ∈ Set.Icc a b) :
    let W : X →ₗ[ℝ] (∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1)
      ϖ ρ 0 (volume.restrict (Set.Icc a b))) :=
      (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1),
        finiteResponseOperator 1 (nativeComponentResponseOperator R Lmetric)
          (nativeComponentResponseOperator R Lsource) j n).comp Z
    ∃ T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
      ∀ x, ∃ (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
        (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
        (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
        IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
          (fun _ i => lf x i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) ∧
        (∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (W x i) (w i)) ∧
        (∀ i, ∃ Q : PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
          (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)),
          PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)) Q (F i)) ∧
        ∀ i, T x i = u i τ := by
  classical
  dsimp only
  let W : X →ₗ[ℝ] (∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1)
      ϖ ρ 0 (volume.restrict (Set.Icc a b))) :=
      (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1),
        finiteResponseOperator 1 (nativeComponentResponseOperator R Lmetric)
          (nativeComponentResponseOperator R Lsource) j n).comp Z
  have hW (x : X) : W x =
      ∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1),
        finiteResponse 1 (nativeComponentResponseOperator R Lmetric)
          (nativeComponentResponseOperator R Lsource) (Z x) j n := by
    simp only [W, LinearMap.comp_apply, LinearMap.sum_apply, finiteResponseOperator_apply]
  choose F u w hs hr using fun x =>
    planeComponentAllMomentResponse_finite_mixed_solution M v K a b ϖ ρ R
      Lmetric Lsource (lf x) (u₀ x) (w₀ x) (Z x) family H J hdepth hM hS hR
      (hbase x) (hZ x)
  have hw (x : X) (i : ι) : PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (W x i) (w x i) := by
    rw [hW]
    exact (hr x i).2
  choose T hT using fun i => planeAllMoment_continuous_trace_linearMap
    (K i) ϖ ρ a b hab 0 ((LinearMap.proj i).comp W)
    (fun x => u x i) (fun x => w x i)
    (fun x => (hs x).1 (0, i)) (fun x => (hs x).2.2.1 (0, i))
    (fun x => hw x i) τ hτ
  refine ⟨LinearMap.pi T, ?_⟩
  intro x
  exact ⟨F x, u x, w x, hs x, hw x, fun i => ⟨_, (hr x i).1⟩, fun i => hT i x⟩
end

/-! The datum-independent retained endpoint and the genuine coupled-error
construction agree through their literal all-moment carrier. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeRetained_endpoint_trace_identification
    (ν a b ϖ ρ : ℝ) (hab : a < b) (v : ℝ → Vec 2 → Vec 2) (D : ℕ) (K : ι → ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (ferr FT : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (uH u uT : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wH w wT : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (W : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) uH wH)
    (he : IsCoupledWeakSolutionPlane ν a b v D K A (fun _ => 0) ferr (fun _ _ => 0)
      (fun i t => uH i t - u i t) (fun i t => wH i t - w i t))
    (hT : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i)
      a b v (fun _ i => f i) (fun _ i => FT i) (fun _ i => uT i) (fun _ i => wT i))
    (hw : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (W i) (w i))
    (hwT : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (W i) (wT i)) :
    ∀ i, Set.EqOn (uT i) (u i) (Set.Icc a b) := by
  have hr := planeCoupled_error_retained_trace ν a b v D K A f ferr uH u wH w hs he
  intro i
  exact planeAllMoment_same_carrier_continuous_traces (K i) ϖ ρ a b hab 0 (W i)
    (uT i) (u i) (wT i) (w i) (hT.1 (0, i)) (hr.1 i)
    (hT.2.2.1 (0, i)) (hr.2 i) (hwT i) (hw i)
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The literal actual coefficient source row has the all-window inverse-mass gradient Schur bound. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeCouplingFluxRow_weighted_gradient_time_schur_budget
    (a b : ℝ) (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i u, (d : admissibleOrders K D i u) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i u d, coefficientSeminorm ρ (K i) a b (A i u d) ≠ ⊤)
    (hc : ∀ i u d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i u d t))
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (θ : ℝ)
    (hrow : ∀ i, ∑ u, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (hcol : ∀ u, ∑ i, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (w : ∀ u, ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (hw : ∀ u, MemLp (w u) 2 (volume.restrict (Set.Icc a b)))
    (he : ∀ u, (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ zc ρ (K u) (w u t)) ≠ ⊤) :
    (∫⁻ t in Set.Icc a b, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n ϖ zc ρ (K i) (planeCouplingFluxRow hab ρ hρ K D A hA hc w i t)) ≤
      ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * θ) ^ 2) *
        ∫⁻ t in Set.Icc a b, ∑ u, ENNReal.ofReal ((π u)⁻¹) *
          weightedGradFactorialNormSq n ϖ zc ρ (K u) (w u t) := by
  have hf : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ u,
      weightedGradFactorialNormSq n ϖ zc ρ (K u) (w u t) ≠ ⊤ := by
    apply ae_all_iff.mpr
    intro u
    exact (ae_lt_top' (weightedGradFactorialNormSq_time_aemeasurable
      n ϖ zc ρ _ (w u) (hw u)) (he u)).mono (fun _ ht => ht.ne)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc, hf] with t ht hft
  have hb := planeCouplingSourceRow_weighted_gradient_schur_budget
    ρ hρ K D a b A hA t ht (fun i u d => hc i u d t ht)
    π hπ θ hrow hcol n ϖ zc (fun u => w u t) hft
  simpa only [planeCouplingFluxRow, AVRegularity.CoupledEnergyPlane.clampPoint,
    max_eq_right ht.1, min_eq_right ht.2] using hb

end AVRegularity.CycleJointProofs
end
end
