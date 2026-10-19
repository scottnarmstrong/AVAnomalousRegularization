-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.KernelEnergy.TorusKernelResidualODE
import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
import AVenhance.Infra.Section5.Integration.BigBound.Centered
import AVRegularity.Construction.StrainPhysical.Context
import AVRegularity.CycleReference.ChartCorrectionIntegrability
import AVenhance.Infra.Classical.Drift
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Copy-adapt the kernel closed trace, retaining molecular smoothing from rough initial data. -/

open KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν δt : ℝ} {K D : ℕ}

theorem kernel_rough_exists_buffered_weakTrace
    (PP : (j : Fin (K + 1)) →
      TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν j.val D)
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (hP : PP ⟨0, Nat.zero_lt_succ K⟩ = P)
    (π : ι → ℝ) (hπ : ∀ j, (PP j).π = π)
    (hBdata : ∀ j, (PP j).B = (PP (Fin.last K)).B)
    (hCdata : ∀ j, (PP j).C = (PP (Fin.last K)).C)
    (hSdata : ∀ j, (PP j).S = (PP (Fin.last K)).S)
    (hb : 0 < δt) (hbT : a + δt ≤ b) (hr : ρ ^ 2 ≤ (5 * ν / 4) * δt)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x,
      ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ K → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun z : Set.Icc a b × Vec 2 => v z.1 z.2))
    (f : ∀ i, TorusHk 0 (h i)) :
    let F := fun i (_ : ℝ) => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)))
    let g := fun i (_ : ℝ) => (0 : TorusHk 0 (h i))
    ∃ (U : CoupledHighTime (h := h) (fun _ => 0) a b) (u : ∀ i, ℝ → TorusHk (0) (h i)),
      (∀ i, MemLp (fun r => coupledHighGraphReadout (fun _ => 0) i (U r)) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i, (coupledHighGraphReadout (fun _ => 0) i (U r)).val = U r i) ∧
      (∀ i, u i a = f i) ∧
      (∃ R : ℝ, ∀ i, ∀ r ∈ Set.Icc a b, ‖u i r‖ ≤ R) ∧
      (∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
        inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
          inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
          P.kernelIntegratedRhs t v F g U i φ) ∧
      (∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
        (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b)) ∧
      (∀ i, MemLp (u i) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
        u i t = truncateTorusHk (Nat.le_succ (0)) (coupledHighGraphReadout (fun _ => 0) i (U t))) ∧
      (∀ j ≤ K, ∀ t ∈ Set.Icc (a + δt) b, ∃ W : ∀ i, TorusHk j (h i),
        (∀ i, truncateTorusHk (Nat.zero_le j) (W i) = u i t) ∧
        Real.sqrt (massNormSq ρ π (fun i => (W i).val)) ≤
          Real.sqrt (bufferEnergyCost j * massNormSq ρ π (fun i => (f i).val))) := by
  let F := fun i (_ : ℝ) => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)))
  let g := fun i (_ : ℝ) => (0 : TorusHk 0 (h i))
  have hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)) := fun i => timeMemLp_zero (E := TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i))) _ 2
  have hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)) := fun i => timeIntegrable_zero (E := TorusHk 0 (h i)) _


  obtain ⟨y, n, U, u, hmem, hgraph, hi, hbound, hid, hcont, hlowmem, halign, _hn, hy, hpair⟩ :=
    kernel_exists_weakTrace_with_value_sequence P v hv hvp F g αv B lam hα hB hlam
      hsmall hstrain hd (fun _ _ l hl hl0 _ => by omega) hv_bdd hv_meas f hF hg
  refine ⟨U, u, hmem, hgraph, hi, hbound, hid, hcont, hlowmem, halign, ?_⟩
  intro j hj t ht
  have ht0 : t ∈ Set.Icc a b := ⟨(le_add_of_nonneg_right hb.le).trans ht.1, ht.2⟩
  apply exists_higher_carrier_of_order_zero_kernel_sequence PP π hπ hBdata hCdata hSdata
    hb hbT hr v hv hvp αv B lam hα hB hlam hsmall hstrain hd hjets hv_bdd hv_meas
    f n (fun m => y (n m))
    (fun m => by simpa only [hP, F, g, plainKernelZeroSource] using hy (n m))
    j hj t ht (fun i => u i t)
  intro i ψ
  simpa only [hP] using hpair t ht0 i ψ

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance
open AVRegularity.CycleReference AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.Buffer

/-! Literal periodic inverse-flow tests satisfy the material cancellation equation. -/

def periodicMaterialTestField {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (ψ : Vec 2 → ℝ) : ℝ × Vec 2 → ℝ :=
  fun p => ψ (AVRegularity.streamFlow φ hφ s p.2 p.1)

theorem periodicMaterialTestField_smooth {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (periodicMaterialTestField hφ s ψ) :=
  inverseStreamFlow_test_smooth hφ s (η := fun _ x => ψ x) (hψ.comp contDiff_snd)

theorem periodicMaterialTestField_periodic {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (ψ : Vec 2 → ℝ) (hp : IsZ2Periodic ψ) (t : ℝ) :
    IsZ2Periodic (fun x => periodicMaterialTestField hφ s ψ (t, x)) := by
  intro k x
  dsimp only [periodicMaterialTestField]
  rw [streamFlow_lattice_equivariant, hp k]

theorem periodicMaterialTestField_transport {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (t : ℝ) (x : Vec 2) :
    spacetimeDirectionalField (periodicMaterialTestField hφ s ψ) (1, 0) (t, x) +
      vecDot (spaceGrad (fun y => periodicMaterialTestField hφ s ψ (t, y)) x)
        (streamVel φ t x) = 0 := by
  let F := periodicMaterialTestField hφ s ψ
  let y := AVRegularity.streamFlow φ hφ s x t
  have hs := periodicMaterialTestField_smooth hφ s ψ hψ
  have hchain := streamFlow_test_time_chain hφ s t y (η := fun r z => F (r, z)) hs
  have he : (fun r => F (r, AVRegularity.streamFlow φ hφ r y s)) = fun _ => ψ y := by
    funext r
    exact congrArg ψ ((streamFlowHomeomorph hφ r s).left_inv y)
  have hx : AVRegularity.streamFlow φ hφ t y s = x :=
    (streamFlowHomeomorph hφ t s).right_inv x
  rw [he, deriv_const, hx, spacetime_time_partial_eq F (hs.of_le (by simp))] at hchain
  exact hchain.symm

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleJointProofs AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.Buffer

/-! Bundle the literal material test in a fixed Hilbert direction. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def periodicMaterialHilbertTest {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (ψ : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hpψ : IsZ2Periodic ψ) (e : E) (t : ℝ) : TorusHk 1 E :=
  mapTorusHkCLM 1 ((ContinuousLinearMap.id ℝ ℝ).smulRight e)
    (smoothScalarTorusH1 (periodicMaterialTestField hφ s ψ)
      (periodicMaterialTestField_smooth hφ s ψ hψ)
      (periodicMaterialTestField_periodic hφ s ψ hpψ) t)

def periodicMaterialHilbertTestDerivative {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (ψ : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hpψ : IsZ2Periodic ψ) (e : E) (t : ℝ) : TorusHk 1 E :=
  let F := periodicMaterialTestField hφ s ψ
  mapTorusHkCLM 1 ((ContinuousLinearMap.id ℝ ℝ).smulRight e)
    (smoothScalarTorusH1 (spacetimeDirectionalField F (1, 0))
      (spacetimeDirectionalField_smooth F (periodicMaterialTestField_smooth hφ s ψ hψ) (1, 0))
      (spacetime_directional_periodic F (periodicMaterialTestField_periodic hφ s ψ hpψ) (1, 0)) t)

theorem periodicMaterialHilbertTest_strong_time {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ) (e : E)
    {a b : ℝ} (hab : a ≤ b) :
    CycleEvolution.StrongTimeRegularity a b (periodicMaterialHilbertTest hφ s ψ hψ hpψ e)
      (periodicMaterialHilbertTestDerivative hφ s ψ hψ hpψ e) :=
  (smoothScalarTorusH1_strong_time _ (periodicMaterialTestField_smooth hφ s ψ hψ)
    (periodicMaterialTestField_periodic hφ s ψ hpψ) hab).map
      (mapTorusHkCLM 1 ((ContinuousLinearMap.id ℝ ℝ).smulRight e))

theorem periodicMaterialHilbertTest_value_ae {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ) (e : E) (t : ℝ) :
    (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t).val (valueIndex2 1)
      =ᵐ[volume.restrict unitCube] fun x => periodicMaterialTestField hφ s ψ (t, x) • e := by
  let L := (ContinuousLinearMap.id ℝ ℝ).smulRight e
  let z := smoothScalarTorusH1 (periodicMaterialTestField hφ s ψ)
    (periodicMaterialTestField_smooth hφ s ψ hψ)
    (periodicMaterialTestField_periodic hφ s ψ hpψ) t
  change (mapTorusHkCLM 1 L z).val (valueIndex2 1) =ᵐ[_] _
  rw [mapTorusHkCLM_apply, mapTorusHk_jet_eq_compLp]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL L (z.val (valueIndex2 1)),
    smoothScalarTorusH1_value_ae _ (periodicMaterialTestField_smooth hφ s ψ hψ)
      (periodicMaterialTestField_periodic hφ s ψ hpψ) t] with x hx hz
  rw [hx, hz]
  rfl

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleReference
namespace AVRegularity.Construction.Preservation.Buffer

/-! Material transport preserves the normalized Fourier test's physical L2 norm. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem material_test_value_norm {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    (hnorm : (∫ x in unitCube, ψ x ^ 2) = 1) (e : E) :
    ‖torusHkValueCLM (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t)‖ = ‖e‖ := by
  let z := torusHkValueCLM (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t)
  have hz : z =ᵐ[volume.restrict unitCube] fun x => periodicMaterialTestField hφ s ψ (t, x) • e :=
    periodicMaterialHilbertTest_value_ae hφ s ψ hψ hpψ e t
  have hsquare : ‖z‖ ^ 2 = ‖e‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    calc
      _ = ∫ x in unitCube, (periodicMaterialTestField hφ s ψ (t, x)) ^ 2 * ‖e‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hz] with x hx
        rw [hx, real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ = (∫ x in unitCube, ψ (AVRegularity.streamFlow φ hφ s x t) ^ 2) * ‖e‖ ^ 2 := by
        rw [integral_mul_const]
        rfl
      _ = ‖e‖ ^ 2 := by
        rw [streamFlow_cell_integral hφ s t (fun x => ψ x ^ 2)
          (by intro k x; exact congrArg (fun a : ℝ => a ^ 2) (hpψ k x)), hnorm, one_mul]
  exact (sq_eq_sq₀ (norm_nonneg z) (norm_nonneg e)).mp hsquare

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.Buffer

/-! The strong-time material test derivative has the literal transport derivative as value. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem periodicMaterialHilbertTestDerivative_value_ae {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ) (e : E) (t : ℝ) :
    (periodicMaterialHilbertTestDerivative hφ s ψ hψ hpψ e t).val (valueIndex2 1)
      =ᵐ[volume.restrict unitCube] fun x =>
        spacetimeDirectionalField (periodicMaterialTestField hφ s ψ) (1, 0) (t, x) • e := by
  let L := (ContinuousLinearMap.id ℝ ℝ).smulRight e
  let F := periodicMaterialTestField hφ s ψ
  let D := spacetimeDirectionalField F (1, 0)
  have hF := periodicMaterialTestField_smooth hφ s ψ hψ
  have hpF := periodicMaterialTestField_periodic hφ s ψ hpψ
  have hD := spacetimeDirectionalField_smooth F hF (1, 0)
  have hpD := spacetime_directional_periodic F hpF (1, 0)
  let z := smoothScalarTorusH1 D hD hpD t
  change (mapTorusHkCLM 1 L z).val (valueIndex2 1) =ᵐ[_] _
  rw [mapTorusHkCLM_apply, mapTorusHk_jet_eq_compLp]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL L (z.val (valueIndex2 1)),
    smoothScalarTorusH1_value_ae D hD hpD t] with x hx hz
  rw [hx, hz]
  rfl

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Restrict the literal native order-zero solution without choosing a new carrier flux. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_end_restrict (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {ν a b c : ℝ} (hcb : c ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ i : CompIn G.comps, TorusHk 0 (hr i.1.root))
    (U : ∀ i : CompIn G.comps, ℝ → TorusHk 0 (hr i.1.root))
    (W : ∀ i : CompIn G.comps, ℝ → TorusHk 1 (hr i.1.root))
    (Y : ∀ i j (_ : G.fam.Γ i j), ℝ → TorusHk (0 + Dm - 1) (hr j.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν v 0 a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y) :
    G.IsRegSolution P seedK freshK φ₀ hφ₀ ν v 0 a c f
      (fun _ _ => 0) (fun _ _ => 0) U W Y := by
  have hsub : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hcb
  exact ⟨fun i => (hsol.1 i).mono hsub,
    fun i => (hsol.2.1 i).mono_measure (Measure.restrict_mono hsub le_rfl),
    fun i => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.1 i),
    hsol.2.2.2.1,
    fun i j α => (hsol.2.2.2.2.1 i j α).mono_measure (Measure.restrict_mono hsub le_rfl),
    fun i j α => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.2.2.2.1 i j α),
    fun i t ht z => hsol.2.2.2.2.2.2 i t (hsub ht) z⟩

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.Buffer

/-! Literal value and spatial derivative readouts of the bundled material test. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem periodicMaterialHilbertTest_first_jet_ae {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ) (e : E)
    (t : ℝ) (i : Fin 2) :
    (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t).val
      ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =ᵐ[volume.restrict unitCube]
      fun x => (fderiv ℝ (periodicMaterialTestField hφ s ψ) (t, x) (0, basisVec i)) • e := by
  let L := (ContinuousLinearMap.id ℝ ℝ).smulRight e
  let z := smoothScalarTorusH1 (periodicMaterialTestField hφ s ψ)
    (periodicMaterialTestField_smooth hφ s ψ hψ)
    (periodicMaterialTestField_periodic hφ s ψ hpψ) t
  change (mapTorusHkCLM 1 L z).val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =ᵐ[_] _
  rw [mapTorusHkCLM_apply, mapTorusHk_jet_eq_compLp]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL L (z.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩),
    smoothScalarTorusH1_gradient_ae _ (periodicMaterialTestField_smooth hφ s ψ hψ)
      (periodicMaterialTestField_periodic hφ s ψ hpψ) t (fun _ => i)] with x hx hz
  rw [hx, hz]
  rfl

theorem periodicMaterialHilbertTest_gradient_ae {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ) (e : E) (t : ℝ) :
    torusH1GradientL2CLM (E := E) (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t)
      =ᵐ[volume.restrict unitCube] fun x => WithLp.toLp 2
        (fun i : Fin 2 => (fderiv ℝ (periodicMaterialTestField hφ s ψ)
          (t, x) (0, basisVec i)) • e) := by
  have hj : ∀ᵐ x ∂volume.restrict unitCube, ∀ i : Fin 2,
      (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t).val
        ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ x =
        (fderiv ℝ (periodicMaterialTestField hφ s ψ) (t, x) (0, basisVec i)) • e := by
    rw [ae_all_iff]
    exact periodicMaterialHilbertTest_first_jet_ae hφ s ψ hψ hpψ e t
  filter_upwards [torusH1GradientL2CLM_ae (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t),
    hj] with x hx hix
  rw [hx]
  apply PiLp.ext
  exact hix

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.Buffer

/-! Read a prepared carrier's literal scalar material pairing as the physical L2 inner product. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem materialCarrier_pairing_readout {K : ℕ} (U : TorusHk K E)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s t : ℝ)
    (ψ : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hpψ : IsZ2Periodic ψ) (e : E) :
    (∫ x in unitCube, inner ℝ e (U.toFunction.jet (valueIndex2 K) x) *
      periodicMaterialTestField hφ s ψ (t, x)) =
      inner ℝ (torusHkValueCLM U)
        (torusHkValueCLM (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [torusRawValue_ae U,
    periodicMaterialHilbertTest_value_ae hφ s ψ hψ hpψ e t] with x hu hz
  have hzx : (torusHkValueCLM (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t)) x =
      periodicMaterialTestField hφ s ψ (t, x) • e := hz
  rw [hu, hzx, inner_smul_right, real_inner_comm]
  exact mul_comm _ _

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.Construction.Preservation.Buffer

/-! The material test itself supplies a normalized rough datum with initial pairing one. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def materialInitialDatum {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (ψ : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hpψ : IsZ2Periodic ψ) (e : E) : TorusHk 0 E :=
  truncateTorusHk (Nat.zero_le 1) (periodicMaterialHilbertTest hφ s ψ hψ hpψ e s)

theorem materialInitialDatum_pairing {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    (hnorm : (∫ x in unitCube, ψ x ^ 2) = 1) (e : E) (he : ‖e‖ = 1) :
    inner ℝ (torusHkValueCLM (materialInitialDatum hφ s ψ hψ hpψ e))
      (torusHkValueCLM (periodicMaterialHilbertTest hφ s ψ hψ hpψ e s)) = 1 := by
  rw [materialInitialDatum, torusHkValue_truncate, real_inner_self_eq_norm_sq,
    material_test_value_norm hφ s s ψ hψ hpψ hnorm e, he, one_pow]

theorem materialInitialDatum_factorial {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    (hnorm : (∫ x in unitCube, ψ x ^ 2) = 1) (e : E) (he : ‖e‖ = 1) (ρ : ℝ) :
    factorialNormSq ρ (materialInitialDatum hφ s ψ hψ hpψ e).val = 1 := by
  rw [CycleJointProofs.factorialNormSq_order_zero_measure,
    CycleJointProofs.zeroOrderJet_norm_sq]
  change ‖torusHkValueCLM (materialInitialDatum hφ s ψ hψ hpψ e)‖ ^ 2 = 1
  rw [materialInitialDatum, torusHkValue_truncate,
    material_test_value_norm hφ s s ψ hψ hpψ hnorm e, he, one_pow]

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! A rough datum supported in one component retains its exact inverse mass weight. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem singleComponent_mass (ρ : ℝ) (π : ι → ℝ) (i : ι) (f : TorusHk 0 (h i)) :
    massNormSq ρ π (fun j => ((Pi.single i f : ∀ j, TorusHk 0 (h j)) j).val) =
      (π i)⁻¹ * factorialNormSq ρ f.val := by
  unfold massNormSq
  rw [Finset.sum_eq_single i]
  · dsimp only
    rw [Pi.single_eq_same]
  · intro j _ hji
    dsimp only
    rw [Pi.single_eq_of_ne hji, CycleJointProofs.factorialNormSq_order_zero_measure]
    change (π j)⁻¹ * ‖(0 : JetL2 (volume.restrict unitCube) 0 (h j))‖ ^ 2 = 0
    rw [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem materialInitialDatum_single_mass {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    (hnorm : (∫ x in unitCube, ψ x ^ 2) = 1) (i : ι) (e : h i)
    (he : ‖e‖ = 1) (ρ : ℝ) (π : ι → ℝ) :
    massNormSq ρ π
      (fun j => ((Pi.single i (materialInitialDatum hφ s ψ hψ hpψ e) : ∀ j, TorusHk 0 (h j)) j).val) = (π i)⁻¹ := by
  rw [singleComponent_mass, materialInitialDatum_factorial hφ s ψ hψ hpψ hnorm e he ρ, mul_one]

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleReference
namespace AVRegularity.Construction.Preservation.Buffer

/-! The material test's gradient costs only the scalar frequency and the flow derivative. -/

theorem material_test_spatial_derivative_le {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {C L : ℝ} (hC : 0 ≤ C)
    (hψbound : ∀ x, ‖fderiv ℝ ψ x‖ ≤ C)
    (hX : ∀ x, ‖fderiv ℝ (fun y => AVRegularity.streamFlow φ hφ s y t) x‖ ≤ L)
    (x : Vec 2) (i : Fin 2) :
    ‖fderiv ℝ (periodicMaterialTestField hφ s ψ) (t, x) (0, basisVec i)‖ ≤ C * L := by
  have hF := periodicMaterialTestField_smooth hφ s ψ hψ
  rw [← CycleWords.joint_spatial_gradient_eq _ (hF.of_le (by simp)) t x i]
  change ‖fderiv ℝ (ψ ∘ fun y => AVRegularity.streamFlow φ hφ s y t) x (basisVec i)‖ ≤ _
  rw [fderiv_comp x (hψ.differentiable (by simp) _)
    ((streamFlow_spatial_smooth hφ s t).differentiable (by simp) x),
    ContinuousLinearMap.comp_apply]
  have hb : ‖basisVec i‖ = 1 := by simp [basisVec, Pi.norm_single]
  have hx := (fderiv ℝ (fun y => AVRegularity.streamFlow φ hφ s y t) x).le_opNorm (basisVec i)
  rw [hb, mul_one] at hx
  exact ((fderiv ℝ ψ _).le_opNorm _).trans
    (mul_le_mul (hψbound _) (hx.trans (hX x)) (norm_nonneg _) hC)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem material_test_gradient_pointwise_le {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {C L : ℝ} (hC : 0 ≤ C)
    (hψbound : ∀ x, ‖fderiv ℝ ψ x‖ ≤ C)
    (hX : ∀ x, ‖fderiv ℝ (fun y => AVRegularity.streamFlow φ hφ s y t) x‖ ≤ L)
    (e : E) (x : Vec 2) :
    ‖WithLp.toLp 2 (fun i : Fin 2 => (fderiv ℝ (periodicMaterialTestField hφ s ψ)
      (t, x) (0, basisVec i)) • e)‖ ≤ 2 * C * L * ‖e‖ := by
  have hi (i : Fin 2) :
      ‖(fderiv ℝ (periodicMaterialTestField hφ s ψ) (t, x) (0, basisVec i)) • e‖ ≤
        C * L * ‖e‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right
      (material_test_spatial_derivative_le hφ s t ψ hψ hC hψbound hX x i) (norm_nonneg _)
  exact (Weighted.finitePiLp_norm_le_sum _).trans
    ((Finset.sum_le_sum (fun i _ => hi i)).trans_eq (by simp; ring))

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.Buffer

/-! The material test gradient has its frequency-flow bound in the actual L2 test space. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem material_test_gradient_L2_le {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hψbound : ∀ x, ‖fderiv ℝ ψ x‖ ≤ C)
    (hX : ∀ x, ‖fderiv ℝ (fun y => AVRegularity.streamFlow φ hφ s y t) x‖ ≤ L)
    (e : E) :
    ‖torusH1GradientL2CLM (E := E) (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t)‖ ≤
      2 * C * L * ‖e‖ := by
  have hb : ∀ᵐ x ∂volume.restrict unitCube,
      ‖(torusH1GradientL2CLM (E := E)
        (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t)) x‖ ≤ 2 * C * L * ‖e‖ := by
    filter_upwards [periodicMaterialHilbertTest_gradient_ae hφ s ψ hψ hpψ e t] with x hx
    rw [hx]
    exact material_test_gradient_pointwise_le hφ s t ψ hψ hC hψbound hX e x
  have hn := Lp.norm_le_of_ae_bound (by positivity : 0 ≤ 2 * C * L * ‖e‖) hb
  have hm : measureUnivNNReal (volume.restrict unitCube) = 1 := by
    apply NNReal.eq
    simp [measureUnivNNReal, Infra.Section5.Integration.volume_unitCube]
  simpa only [hm, NNReal.coe_one, Real.one_rpow, one_mul] using hn

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! The buffered rough kernel trace has the existing strong continuous representative. -/

open KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν δt : ℝ} {K D : ℕ}

theorem kernel_rough_exists_buffered_strongTrace
    (PP : (j : Fin (K + 1)) →
      TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν j.val D)
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (hP : PP ⟨0, Nat.zero_lt_succ K⟩ = P)
    (π : ι → ℝ) (hπ : ∀ j, (PP j).π = π)
    (hBdata : ∀ j, (PP j).B = (PP (Fin.last K)).B)
    (hCdata : ∀ j, (PP j).C = (PP (Fin.last K)).C)
    (hSdata : ∀ j, (PP j).S = (PP (Fin.last K)).S)
    (hb : 0 < δt) (hbT : a + δt ≤ b) (hr : ρ ^ 2 ≤ (5 * ν / 4) * δt)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x,
      ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ K → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun z : Set.Icc a b × Vec 2 => v z.1 z.2))
    (f : ∀ i, TorusHk 0 (h i)) :
    let F := fun i (_ : ℝ) => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)))
    let g := fun i (_ : ℝ) => (0 : TorusHk 0 (h i))
    ∃ (U : CoupledHighTime (h := h) (fun _ => 0) a b) (u : ∀ i, ℝ → TorusHk (0) (h i)),
      (∀ i, MemLp (fun r => coupledHighGraphReadout (fun _ => 0) i (U r)) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i, (coupledHighGraphReadout (fun _ => 0) i (U r)).val = U r i) ∧
      (∀ i, u i a = f i) ∧
      (∃ R : ℝ, ∀ i, ∀ r ∈ Set.Icc a b, ‖u i r‖ ≤ R) ∧
      (∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
        inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
          inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
          P.kernelIntegratedRhs t v F g U i φ) ∧
      (∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
        (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b)) ∧
      (∀ i, MemLp (u i) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
        u i t = truncateTorusHk (Nat.le_succ (0)) (coupledHighGraphReadout (fun _ => 0) i (U t))) ∧
      (∀ j ≤ K, ∀ t ∈ Set.Icc (a + δt) b, ∃ W : ∀ i, TorusHk j (h i),
        (∀ i, truncateTorusHk (Nat.zero_le j) (W i) = u i t) ∧
        Real.sqrt (massNormSq ρ π (fun i => (W i).val)) ≤
          Real.sqrt (bufferEnergyCost j * massNormSq ρ π (fun i => (f i).val))) ∧ (∀ i, ContinuousOn (u i) (Set.Icc a b)) := by
  let F := fun i (_ : ℝ) => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)))
  let g := fun i (_ : ℝ) => (0 : TorusHk 0 (h i))
  have hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)) :=
    fun i => timeMemLp_zero (E := TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i))) _ 2
  have hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)) :=
    fun i => timeIntegrable_zero (E := TorusHk 0 (h i)) _
  obtain ⟨U, u, hmem, hgraph, hi, hbound, hid, hcont, hlowmem, halign, hbuffer⟩ :=
    kernel_rough_exists_buffered_weakTrace PP P hP π hπ hBdata hCdata hSdata hb hbT hr
      v hv hvp αv B lam hα hB hlam hsmall hstrain hd hjets hv_bdd hv_meas f
  obtain ⟨R, hR⟩ := hbound
  refine ⟨U, u, hmem, hgraph, hi, ⟨R, hR⟩, hid, hcont, hlowmem, halign, hbuffer, ?_⟩
  obtain ⟨V, hV⟩ := hv_bdd
  exact P.kernelNativeTrace_continuousOn v hv_meas hv hvp (max V 0) (le_max_right _ _)
    (fun t ht x => (hV t ht x).trans (le_max_left _ _)) αv B lam
    (fun _ _ _ l hl hl0 _ => by omega)
    F g hF hg U hgraph u f hid hcont R hR halign

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.Buffer

/-! A short flow interval controls the actual inverse-flow material test gradient. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem short_time_material_gradient_le {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hψbound : ∀ x, ‖fderiv ℝ ψ x‖ ≤ C)
    (hDv : ∀ r x, ‖Infra.Flow.jointSpatialFDeriv (streamVel φ) r x‖ ≤ L)
    (hsmall : L * |t - s| ≤ 1) (e : E) :
    ‖torusH1GradientL2CLM (E := E) (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t)‖ ≤
      6 * C * ‖e‖ := by
  have hX (x : Vec 2) : ‖fderiv ℝ (fun y => AVRegularity.streamFlow φ hφ s y t) x‖ ≤ 3 :=
    short_time_flow_derivative_le_three (Infra.Construction.smoothPeriodic_streamVel hφ)
      (StrainPhysical.isFlow_stream hφ) hL hDv t s (by rwa [abs_sub_comm]) x
  have hb := material_test_gradient_L2_le hφ s t ψ hψ hpψ hC (by norm_num) hψbound hX e
  exact hb.trans_eq (by ring)

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual rough kernel buffer survives passage to the literal forced weak equation. -/

open KernelEnergy TorusKernelOperator
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν δt : ℝ} {K D : ℕ}

theorem kernel_rough_exists_buffered_forcedWeakSolution
    (PP : (j : Fin (K + 1)) →
      TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν j.val D)
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (hP : PP ⟨0, Nat.zero_lt_succ K⟩ = P)
    (π : ι → ℝ) (hπ : ∀ j, (PP j).π = π)
    (hBdata : ∀ j, (PP j).B = (PP (Fin.last K)).B)
    (hCdata : ∀ j, (PP j).C = (PP (Fin.last K)).C)
    (hSdata : ∀ j, (PP j).S = (PP (Fin.last K)).S)
    (hb : 0 < δt) (hbT : a + δt ≤ b) (hr : ρ ^ 2 ≤ (5 * ν / 4) * δt)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x,
      ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ K → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun z : Set.Icc a b × Vec 2 => v z.1 z.2))
    (f : ∀ i, TorusHk 0 (h i)) :
    let F := fun i (_ : ℝ) => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)))
    let g := fun i (_ : ℝ) => (0 : TorusHk 0 (h i))
    ∃ (u : ∀ i, ℝ → TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i)),
      IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => 0) noLocalCoefficient f
        (fun i r => F i r + P.carrierFlux w i r) g u w ∧
      (∀ i, MemLp (P.carrierFlux w i) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ j ≤ K, ∀ t ∈ Set.Icc (a + δt) b, ∃ W : ∀ i, TorusHk j (h i),
        (∀ i, truncateTorusHk (Nat.zero_le j) (W i) = u i t) ∧
        Real.sqrt (massNormSq ρ π (fun i => (W i).val)) ≤
          Real.sqrt (bufferEnergyCost j * massNormSq ρ π (fun i => (f i).val))) := by
  let F := fun i (_ : ℝ) => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)))
  let g := fun i (_ : ℝ) => (0 : TorusHk 0 (h i))
  have hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)) :=
    fun i => timeMemLp_zero (E := TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i))) _ 2
  have hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)) :=
    fun i => timeIntegrable_zero (E := TorusHk 0 (h i)) _
  obtain ⟨U, u, hmem, hgraph, hinit, _, hid, _, _, huw, hbuffer, hstrong⟩ :=
    kernel_rough_exists_buffered_strongTrace PP P hP π hπ hBdata hCdata hSdata hb hbT hr
      v hv hvp αv B lam hα hB hlam hsmall hstrain hd hjets hv_bdd hv_meas f
  let w := fun i t => coupledHighGraphReadout (fun _ => 0) i (U t)
  have hQ (i : ι) : MemLp (P.carrierFlux w i) 2 (volume.restrict (Set.Icc a b)) :=
    P.carrierFlux_memLp U w hgraph i
  have hforce (i : ι) : MemLp (fun r => F i r + P.carrierFlux w i r) 2
      (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_add (volume.restrict (Set.Icc a b)) 2 (F i) (P.carrierFlux w i) (hF i) (hQ i)
  have heq (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) (φ : TorusHk 1 (h i)) :
      inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
        inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
      coupledIntegratedRhs (fun _ => 0) 0 ν a t v noLocalCoefficient
        (fun i r => F i r + P.carrierFlux w i r) g U i φ := by
    rw [P.kernelIntegratedRhs_eq_forcedRhs t ht v F g hF U w hgraph i φ]
    exact hid i t ht φ
  obtain ⟨V, hV⟩ := hv_bdd
  have hidentity := torusNativeEquation_implies_rawWeakIdentity (fun _ => 0) 0 ν ρ P.radius_pos
    P.htime v hv_meas (fun t ht => (hv t ht).continuous) V hV noLocalCoefficient
    (fun i j d => (noLocalOrders (k := 0) i j d).elim)
    (fun i j d => (noLocalOrders (k := 0) i j d).elim)
    (fun t ht i j d => (noLocalOrders (k := 0) i j d).elim)
    (fun i r => F i r + P.carrierFlux w i r) g hforce hg U w hgraph u f heq
  refine ⟨u, w, ⟨hstrong, hmem, ?_, hinit, ?_⟩, hQ, hbuffer⟩
  · intro i
    exact huw.mono (fun t ht => (ht i).symm)
  · intro i t ht φ
    simpa only [torusRawCouplingFlux] using! hidentity i t ht φ

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory
open scoped Matrix
open AVRegularity.CycleReference
namespace AVRegularity.Construction.Preservation.Buffer

/-! A prepared H1 field pairs weakly with a material Fourier derivative. -/

theorem periodic_material_primitive_pairing {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2} (hu : IsPeriodicH1With u Du)
    (η ψ : Vec 2 → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hpη : IsZ2Periodic η) (hpψ : IsZ2Periodic ψ)
    (i : Fin 2) {ell : ℝ} (hell : 0 < ell)
    (hder : ∀ x, spaceGrad η x i = ell * ψ x) :
    |∫ x in unitCube, u x * periodicMaterialTestField hφ s ψ (t, x)| ≤
      (Real.sqrt (∫ y in unitCube,
        (((jacMatrix (fun z => AVRegularity.streamFlow φ hφ t z s) y)ᵀ.mulVec
          (Du (AVRegularity.streamFlow φ hφ t y s))) i) ^ 2) *
        Real.sqrt (∫ y in unitCube, η y ^ 2)) / ell := by
  have hper : IsZ2Periodic (fun x => u x * periodicMaterialTestField hφ s ψ (t, x)) := by
    intro k x
    dsimp only
    exact congrArg₂ (fun a b : ℝ => a * b) (hu.1 k x)
      (periodicMaterialTestField_periodic hφ s ψ hpψ t k x)
  have hm := streamFlow_cell_integral hφ t s _ hper
  have he : (fun y => u (AVRegularity.streamFlow φ hφ t y s) *
      periodicMaterialTestField hφ s ψ (t, AVRegularity.streamFlow φ hφ t y s)) =
      fun y => u (AVRegularity.streamFlow φ hφ t y s) * ψ y := by
    funext y
    change u _ * ψ (AVRegularity.streamFlow φ hφ s
      (AVRegularity.streamFlow φ hφ t y s) t) = _
    exact congrArg (fun z => u (AVRegularity.streamFlow φ hφ t y s) * ψ z)
      ((streamFlowHomeomorph hφ t s).left_inv y)
  rw [he] at hm
  rw [← hm]
  exact periodic_primitive_pairing_bound (streamFlow_periodicH1 hφ t s hu)
    η ψ hη hpη i hell hder

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.Construction.Preservation.Buffer

/-! The material primitive pairing has an explicit flow-derivative price. -/

theorem periodic_material_primitive_budget {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2} (hu : IsPeriodicH1With u Du)
    (η ψ : Vec 2 → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hpη : IsZ2Periodic η) (hpψ : IsZ2Periodic ψ)
    (i : Fin 2) {ell : ℝ} (hell : 0 < ell)
    (hder : ∀ x, spaceGrad η x i = ell * ψ x)
    {L : ℝ} (hX : ∀ x, ‖fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ t z s) x‖ ≤ L) :
    |∫ x in unitCube, u x * periodicMaterialTestField hφ s ψ (t, x)| ≤
      (Real.sqrt (2 * L ^ 2 * ∑ j : Fin 2, ∫ y in unitCube, Du y j ^ 2) *
        Real.sqrt (∫ y in unitCube, η y ^ 2)) / ell := by
  have hp := periodic_material_primitive_pairing hφ s t hu η ψ hη hpη hpψ i hell hder
  have hg := Real.sqrt_le_sqrt (streamFlow_pullback_gradient_integral_le hφ t s hu hX i)
  exact hp.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hg (Real.sqrt_nonneg _)) hell.le)

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Enhanced factorial control gives a dimension-free bound for a material Fourier pairing. -/

theorem scalar_carrier_material_primitive_pairing {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) {K : ℕ} (hK : 1 ≤ K) (U : TorusHk K ℝ)
    (η ψ : Vec 2 → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hpη : IsZ2Periodic η) (hpψ : IsZ2Periodic ψ)
    (i : Fin 2) {ell ρ L : ℝ} (hell : 0 < ell) (hρ : 0 < ρ)
    (hder : ∀ x, spaceGrad η x i = ell * ψ x)
    (hnorm : (∫ y in unitCube, η y ^ 2) = 1)
    (hX : ∀ x, ‖fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ t z s) x‖ ≤ L) :
    |∫ x in unitCube, U.toFunction.jet (valueIndex2 K) x *
      periodicMaterialTestField hφ s ψ (t, x)| ≤
      Real.sqrt (2 * L ^ 2) * Real.sqrt (factorialNormSq ρ U.val) / (ρ * ell) := by
  have hp := periodic_material_primitive_budget hφ s t (scalar_first_jet_periodicH1 hK U)
    η ψ hη hpη hpψ i hell hder hX
  rw [hnorm, Real.sqrt_one, mul_one,
    Real.sqrt_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg L))] at hp
  have he := Real.sqrt_le_sqrt (scalar_first_jet_scaled_energy hK U ρ)
  rw [Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq_eq_abs, abs_of_pos hρ] at he
  apply (le_div_iff₀ (mul_pos hρ hell)).mpr
  calc
    _ = (|∫ x in unitCube, U.toFunction.jet (valueIndex2 K) x *
        periodicMaterialTestField hφ s ψ (t, x)| * ell) * ρ := by ring
    _ ≤ (Real.sqrt (2 * L ^ 2) *
        Real.sqrt (∑ i : Fin 2, ∫ x in unitCube,
          U.toFunction.jet ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ : Fin 1 => i⟩ x ^ 2)) * ρ :=
      mul_le_mul_of_nonneg_right ((le_div_iff₀ hell).mp hp) hρ.le
    _ = Real.sqrt (2 * L ^ 2) * (ρ *
        Real.sqrt (∑ i : Fin 2, ∫ x in unitCube,
          U.toFunction.jet ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ : Fin 1 => i⟩ x ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)

/-! The actual Hilbert carrier has the same material Fourier estimate in any fixed direction. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem hilbert_carrier_material_primitive_pairing {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) {K : ℕ} (hK : 1 ≤ K) (U : TorusHk K E) (e : E)
    (η ψ : Vec 2 → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hpη : IsZ2Periodic η) (hpψ : IsZ2Periodic ψ)
    (i : Fin 2) {ell ρ L : ℝ} (hell : 0 < ell) (hρ : 0 < ρ)
    (hder : ∀ x, spaceGrad η x i = ell * ψ x)
    (hnorm : (∫ y in unitCube, η y ^ 2) = 1)
    (hX : ∀ x, ‖fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ t z s) x‖ ≤ L) :
    |∫ x in unitCube, inner ℝ e (U.toFunction.jet (valueIndex2 K) x) *
      periodicMaterialTestField hφ s ψ (t, x)| ≤
      Real.sqrt (2 * L ^ 2) * ‖e‖ * Real.sqrt (factorialNormSq ρ U.val) / (ρ * ell) := by
  let Q := CoupledEnergy.Variational.mapTorusHk (innerSL ℝ e) U
  have hpair := scalar_carrier_material_primitive_pairing hφ s t hK Q
    η ψ hη hpη hpψ i hell hρ hder hnorm hX
  have hroot := variational_map_factorialRoot_le ρ (innerSL ℝ e) U
  rw [innerSL_apply_norm] at hroot
  have he : (∫ x in unitCube, inner ℝ e (U.toFunction.jet (valueIndex2 K) x) *
      periodicMaterialTestField hφ s ψ (t, x)) =
      ∫ x in unitCube, Q.toFunction.jet (valueIndex2 K) x *
        periodicMaterialTestField hφ s ψ (t, x) := by
    apply integral_congr_ae
    filter_upwards [variational_map_raw_jet_ae (innerSL ℝ e) U (valueIndex2 K)] with x hx
    exact congrArg (fun a : ℝ => a * periodicMaterialTestField hφ s ψ (t, x)) hx.symm
  rw [he]
  calc
    _ ≤ Real.sqrt (2 * L ^ 2) * Real.sqrt (factorialNormSq ρ Q.val) / (ρ * ell) := hpair
    _ ≤ Real.sqrt (2 * L ^ 2) * (‖e‖ * Real.sqrt (factorialNormSq ρ U.val)) / (ρ * ell) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)) (mul_pos hρ hell).le
    _ = _ := by ring
end

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory
open AVRegularity.CycleReference AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.Buffer

/-! Weak periodic integration by parts gives the material-test drift cancellation. -/

theorem periodic_material_drift_cancellation {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2} (hu : IsPeriodicH1With u Du) :
    (∫ x in unitCube, -vecDot (streamVel φ t x) (Du x) *
      periodicMaterialTestField hφ s ψ (t, x)) +
    (∫ x in unitCube, u x *
      spacetimeDirectionalField (periodicMaterialTestField hφ s ψ) (1, 0) (t, x)) = 0 := by
  have hv := Infra.Construction.smoothPeriodic_streamVel hφ
  have hF := periodicMaterialTestField_smooth hφ s ψ hψ
  have hpF := periodicMaterialTestField_periodic hφ s ψ hpψ t
  have hpair := periodicH1_divFree_cell_pairing hu
    (hv.smooth.comp (contDiff_const.prodMk contDiff_id))
    (by intro k x; simpa using hv.periodic 0 k t x)
    (Infra.Classical.streamVel_vecDiv_eq_zero φ hφ t)
    (hF.comp (contDiff_const.prodMk contDiff_id)) hpF
  have hdt (x : Vec 2) :
      spacetimeDirectionalField (periodicMaterialTestField hφ s ψ) (1, 0) (t, x) =
      -vecDot (streamVel φ t x)
        (spaceGrad (fun y => periodicMaterialTestField hφ s ψ (t, y)) x) := by
    have he := periodicMaterialTestField_transport hφ s ψ hψ t x
    have hc : vecDot (spaceGrad (fun y => periodicMaterialTestField hφ s ψ (t, y)) x)
        (streamVel φ t x) = vecDot (streamVel φ t x)
          (spaceGrad (fun y => periodicMaterialTestField hφ s ψ (t, y)) x) := by
      simp only [vecDot, mul_comm]
    rw [hc] at he
    linarith
  simp_rw [hdt, neg_mul, mul_neg]
  rw [integral_neg, integral_neg]
  simp only [Function.comp_def, Function.uncurry, id_eq] at hpair
  linarith

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CycleReference AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual weighted native piece has a finite coefficient seminorm. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_weighted_piece_coefficientSeminorm_finite
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (a b mres : ℝ) (N : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn (G.innerDomain (Set.Icc a b) mres) (D.eps (G.level - 1)) N)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ D.eps (G.level - 1))
    (n r : ℕ) (hn : n ≤ N v) :
    coefficientSeminorm ρ n a b (fun t x => G.fam.weight p t •
      nativeArrayAssembly r (G.fam.identity v u γ).map
        (fun i A => transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material t).symm)
          (G.fam.identity v u γ).maxOrder
          (fun d I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
            (((G.fam.piece p).material t).symm x)
            (e⁻¹ • ((G.fam.piece p).material t).symm x)) r A x i)) ≠ ⊤ := by
  let KK := fun t => naturalPreparationJacobian (D.hΦ (G.level - 1))
    (D.slotAnchor G.level p.1) t
  let B := fun t d I => nativeWeightedSampledFlux G ν e p v u γ d I t
  obtain ⟨MB, hMB, hB, hBj⟩ := native_weighted_sampled_scalar_budgets hG hpar hnat
    hi hj hb hε a b mres N hs p v u γ hm hm2 ν e ρ hρ.le n hn
  let L := n + (G.fam.identity v u γ).maxOrder
  obtain ⟨C, hC, hKC⟩ := naturalPreparationJacobian_compact_scaled_jets
    (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) (Set.Icc a b) isCompact_Icc
    (D.eps (G.level - 1)) hε.le L
  have hK (t : ℝ) (_ht : t ∈ Set.Icc a b) (i j : Fin 2) :
      ContDiff ℝ (⊤ : ℕ∞) (fun x => KK t x i j) :=
    (naturalPreparationJacobian_entry_smooth (D.hΦ (G.level - 1))
      (D.slotAnchor G.level p.1) i j).comp (contDiff_const.prodMk contDiff_id)
  have hf := native_transport_coefficientSeminorm_finite a b KK hK L
    (G.fam.identity v u γ).maxOrder n r C (D.eps (G.level - 1)) ρ hC hε hρ hρε
    le_rfl hKC B hB MB hMB
    (fun t ht d _ I i j hjn x => hBj t ht d I i j hjn x) (G.fam.identity v u γ).map
  apply ne_top_of_le_ne_top hf
  apply le_of_eq
  congr 1
  funext t x
  rw [native_inverse_jacobian_eq_natural hnat p t, native_inverse_material_eq_flow hnat p t]
  exact (weighted_native_array_assembly (KK t) (G.fam.identity v u γ).maxOrder r
    (fun d I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
      (streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) x t)
      (e⁻¹ • streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
        (D.slotAnchor G.level p.1) x t))
    (G.fam.weight p t) (G.fam.identity v u γ).map x).symm

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.Buffer

/-! Actual Hilbert-valued carriers satisfy the material-test drift cancellation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem material_carrier_drift_cancellation {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    {K : ℕ} (hK : 1 ≤ K) (U : TorusHk K E) (e : E) :
    (∫ x in unitCube, -(∑ i : Fin 2, streamVel φ t x i *
      inner ℝ e (U.toFunction.jet ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ => i⟩ x)) *
        periodicMaterialTestField hφ s ψ (t, x)) +
    (∫ x in unitCube, inner ℝ e (U.toFunction.jet (valueIndex2 K) x) *
      spacetimeDirectionalField (periodicMaterialTestField hφ s ψ) (1, 0) (t, x)) = 0 := by
  let Q := CoupledEnergy.Variational.mapTorusHk (innerSL ℝ e) U
  have hc := periodic_material_drift_cancellation hφ s t ψ hψ hpψ
    (scalar_first_jet_periodicH1 hK Q)
  have hv : Q.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict unitCube]
      fun x => inner ℝ e (U.toFunction.jet (valueIndex2 K) x) :=
    variational_map_raw_jet_ae (innerSL ℝ e) U (valueIndex2 K)
  have hd : ∀ᵐ x ∂volume.restrict unitCube, ∀ i : Fin 2,
      Q.toFunction.jet ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ => i⟩ x =
        inner ℝ e (U.toFunction.jet ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ => i⟩ x) := by
    rw [ae_all_iff]
    intro i
    exact variational_map_raw_jet_ae (innerSL ℝ e) U _
  have he1 : (∫ x in unitCube, -vecDot (streamVel φ t x)
      (fun i => Q.toFunction.jet ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ => i⟩ x) *
        periodicMaterialTestField hφ s ψ (t, x)) =
      ∫ x in unitCube, -(∑ i : Fin 2, streamVel φ t x i *
        inner ℝ e (U.toFunction.jet ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ => i⟩ x)) *
          periodicMaterialTestField hφ s ψ (t, x) := by
    apply integral_congr_ae
    filter_upwards [hd] with x hx
    simp only [vecDot, hx]
  have he2 : (∫ x in unitCube, Q.toFunction.jet (valueIndex2 K) x *
      spacetimeDirectionalField (periodicMaterialTestField hφ s ψ) (1, 0) (t, x)) =
      ∫ x in unitCube, inner ℝ e (U.toFunction.jet (valueIndex2 K) x) *
        spacetimeDirectionalField (periodicMaterialTestField hφ s ψ) (1, 0) (t, x) := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    exact congrArg (fun a : ℝ => a *
      spacetimeDirectionalField (periodicMaterialTestField hφ s ψ) (1, 0) (t, x)) hx
  rw [he1, he2] at hc
  exact hc

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Normalize the literal weighted preparation norm before entering the construction context. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem weighted_material_initial_norm {S : Finset Comp} (π w : CompIn S → ℝ)
    (v : CompIn S) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (ψ : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    (hnorm : (∫ x in unitCube, ψ x ^ 2) = 1) (e : hr v.1.root) (he : ‖e‖ = 1) :
    weightedNorm 1 π w (Pi.single v (materialInitialDatum hφ s ψ hψ hpψ e) :
      ∀ u : CompIn S, TorusHk 0 (hr u.1.root)) = Real.sqrt (π v / w v ^ 2)⁻¹ := by
  unfold weightedNorm
  exact congrArg Real.sqrt
    (materialInitialDatum_single_mass (h := fun u : CompIn S => hr u.1.root)
      hφ s ψ hψ hpψ hnorm v e he 1 (fun u => π u / w u ^ 2))

end AVRegularity.Construction.Preservation.Buffer
end
