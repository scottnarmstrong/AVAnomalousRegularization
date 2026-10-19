-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Buffer.WeightedMaterialInitialNorm
import AVRegularity.KernelEnergy.TorusKernelComponentSup
import AVRegularity.KernelEnergy.TorusKernelStrongTraceExistence
public import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
public import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
public import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Genuine native coefficient jets give a finite seminorm for the actual physical coefficient. -/

open CycleJointProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_constituentPhysical_coefficientSeminorm_finite
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (a b mres : ℝ) (N : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn (G.innerDomain (Set.Icc a b) mres) (D.eps (G.level - 1)) N)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ D.eps (G.level - 1))
    (n d : ℕ) (hn : n ≤ N v) :
    coefficientSeminorm ρ n a b
      (constituentPhysical G.fam ν e (D.eps (G.level - 1)) G.actual v u γ d) ≠ ⊤ := by
  let A := fun p t x => G.fam.weight p t •
    nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map
      (fun i W => transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material t).symm)
        (G.fam.identity v u γ).maxOrder
        (fun d' I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d' I t
          (((G.fam.piece p).material t).symm x)
          (e⁻¹ • ((G.fam.piece p).material t).symm x)) (d - 1) W x i)
  have hf := coefficientSeminorm_sum_ne_top (G.fam.locally_finite a b).toFinset A ρ n a b
    (fun p _ t ht => (native_weighted_piece_spatial_smooth hnat hi hj ν e
      (D.eps (G.level - 1)) a b mres hε.ne' N hs p v u γ (d - 1) t ht).of_le
        (by exact_mod_cast hn))
    (fun p _ => native_weighted_piece_coefficientSeminorm_finite hG hpar hnat hi hj hb
      hε a b mres N hs p v u γ hm hm2 ν e ρ hρ hρε n (d - 1) hn)
  have he (t : ℝ) (ht : t ∈ Set.Icc a b) :
      constituentPhysical G.fam ν e (D.eps (G.level - 1)) G.actual v u γ d t =
        fun x => ∑ p ∈ (G.fam.locally_finite a b).toFinset, A p t x := by
    funext x
    exact constituentPhysical_eq_window_sum G.fam ν e (D.eps (G.level - 1)) G.actual
      a b t ht v u γ d x
  rw [coefficientSeminorm_window_congr ρ n a b _ _ he]
  exact hf


theorem native_physCoeff_coefficientSeminorm_finite
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (a b mres : ℝ) (N : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn (G.innerDomain (Set.Icc a b) mres) (D.eps (G.level - 1)) N)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ D.eps (G.level - 1))
    (n d : ℕ) (hn : n ≤ N v) :
    coefficientSeminorm ρ n a b (G.physCoeff v u γ d) ≠ ⊤ :=
  native_constituentPhysical_coefficientSeminorm_finite hG hpar hnat hi hj hb hε
    a b mres N hs v u γ hm hm2 (D.kap G.level) (D.eps G.level) ρ hρ hρε n d hn

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Uniqueness transfers the rough-data buffer to every actual order-zero kernel solution. -/

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

theorem kernel_rough_solution_buffer
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
    (f : ∀ i, TorusHk 0 (h i))
    (u : ∀ i, ℝ → TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (0 + D - 1) (G i j α))
    (hsol : IsKernelWeakSolutionTorus ν a b v 0 D P.B P.C P.S f
      (fun _ _ => 0) (fun _ _ => 0) u w y) :
    ∀ j ≤ K, ∀ t ∈ Set.Icc (a + δt) b, ∃ W : ∀ i, TorusHk j (h i),
      (∀ i, truncateTorusHk (Nat.zero_le j) (W i) = u i t) ∧
      Real.sqrt (massNormSq ρ π (fun i => (W i).val)) ≤
        Real.sqrt (bufferEnergyCost j * massNormSq ρ π (fun i => (f i).val)) := by
  let F := fun i (_ : ℝ) => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)))
  let g := fun i (_ : ℝ) => (0 : TorusHk 0 (h i))
  have hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)) :=
    fun i => timeMemLp_zero (E := TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i))) _ 2
  have hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)) :=
    fun i => timeIntegrable_zero (E := TorusHk 0 (h i)) _
  obtain ⟨u', w', hsol', _hflux, hbuffer⟩ :=
    kernel_rough_exists_buffered_forcedWeakSolution PP P hP π hπ hBdata hCdata hSdata
      hb hbT hr v hv hvp αv B lam hα hB hlam hsmall hstrain hd hjets hv_bdd hv_meas f
  obtain ⟨V, hV⟩ := hv_bdd
  let V₀ := max V 0
  have hV₀ : 0 ≤ V₀ := le_max_right _ _
  have hvb (t : ℝ) (ht : t ∈ Set.Icc a b) (x : Vec 2) : ‖v t x‖ ≤ V₀ :=
    (hV t ht x).trans (le_max_left _ _)
  have hforced := P.kernelWeakSolution_forcedWeakSolution v hv V₀ hV₀ hvb f F g u w y hsol
  have heq := P.kernelForcedWeakSolution_unique v hv hvp F g αv B lam hα hB hlam
    hsmall hstrain hd (fun _ _ l hl hl0 _ => by omega) hv_meas V₀ hV₀ hvb
    (fun _ => driftCarrierBudget 0 V₀ αv B lam)
    (fun t ht _ => driftCarrierBudget_bounds 0 (v t) V₀ αv B lam hV₀ (hvb t ht)
      (fun l hl hl0 _ => by omega))
    w' w u' u f hF hg hsol' hforced
  intro j hj t ht
  have ht0 : t ∈ Set.Icc a b := ⟨(le_add_of_nonneg_right hb.le).trans ht.1, ht.2⟩
  obtain ⟨W, hW, hbound⟩ := hbuffer j hj t ht
  exact ⟨W, fun i => (hW i).trans (heq i t ht0), hbound⟩

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.Buffer

/-! The literal L2 drift source cancels the strong material-test time derivative. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem window_material_cancellation {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    {a b : ℝ} (hab : a ≤ b) (s : ℝ) (ψ : Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ V)
    (w : ℝ → TorusHk 1 E) (e : E) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    let hv := (Infra.Construction.smoothPeriodic_streamVel hφ).smooth.continuous
    inner ℝ (windowDriftSource hab (streamVel φ) hv V hV hb w t)
      (torusHkValueCLM (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t)) +
    inner ℝ (torusHkValueCLM (w t))
      (torusHkValueCLM (periodicMaterialHilbertTestDerivative hφ s ψ hψ hpψ e t)) = 0 := by
  dsimp only
  let hv := (Infra.Construction.smoothPeriodic_streamVel hφ).smooth.continuous
  have hc := material_carrier_drift_cancellation hφ s t ψ hψ hpψ le_rfl (w t) e
  have he1 : inner ℝ (windowDriftSource hab (streamVel φ) hv V hV hb w t)
      (torusHkValueCLM (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t)) =
      ∫ x in unitCube, -(∑ i : Fin 2, streamVel φ t x i *
        inner ℝ e ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ x)) *
          periodicMaterialTestField hφ s ψ (t, x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [windowDriftSource_raw_ae hab (streamVel φ) hv V hV hb w t ht,
      periodicMaterialHilbertTest_value_ae hφ s ψ hψ hpψ e t] with x hs hz
    have hzx : (torusHkValueCLM (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t)) x =
      periodicMaterialTestField hφ s ψ (t, x) • e := hz
    rw [hs, hzx]
    simp only [inner_neg_left, inner_smul_right, inner_sum,
      real_inner_comm]
    exact mul_comm _ _
  have he2 : inner ℝ (torusHkValueCLM (w t))
      (torusHkValueCLM (periodicMaterialHilbertTestDerivative hφ s ψ hψ hpψ e t)) =
      ∫ x in unitCube, inner ℝ e ((w t).toFunction.jet (valueIndex2 1) x) *
        spacetimeDirectionalField (periodicMaterialTestField hφ s ψ) (1, 0) (t, x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [CoupledEnergy.Variational.torusRawValue_ae (w t),
      periodicMaterialHilbertTestDerivative_value_ae hφ s ψ hψ hpψ e t] with x hw hd
    have hdx : (torusHkValueCLM (periodicMaterialHilbertTestDerivative hφ s ψ hψ hpψ e t)) x =
      spacetimeDirectionalField (periodicMaterialTestField hφ s ψ) (1, 0) (t, x) • e := hd
    rw [hdx, ← hw, inner_smul_right, real_inner_comm]
    exact mul_comm _ _
  rw [he1, he2]
  exact hc

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.Construction.Preservation.Buffer

/-! Material cancellation transfers from the energy carrier to its weak value trace. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem window_material_cancellation_ae {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) {a b : ℝ} (hab : a ≤ b)
    (s : ℝ) (ψ : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hpψ : IsZ2Periodic ψ) (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ V)
    (w : ℝ → TorusHk 1 E) (u : ℝ → TorusHk 0 E)
    (hu : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncateTorusHk (Nat.zero_le 1) (w t) = u t) (e : E) :
    let hv := (Infra.Construction.smoothPeriodic_streamVel hφ).smooth.continuous
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      inner ℝ (windowDriftSource hab (streamVel φ) hv V hV hb w t)
        (torusHkValueCLM (periodicMaterialHilbertTest hφ s ψ hψ hpψ e t)) +
      inner ℝ (torusHkValueCLM (u t))
        (torusHkValueCLM (periodicMaterialHilbertTestDerivative hφ s ψ hψ hpψ e t)) = 0 := by
  dsimp only
  filter_upwards [hu, ae_restrict_mem measurableSet_Icc] with t hut ht
  rw [← hut, torusHkValue_truncate]
  exact window_material_cancellation hφ hab s ψ hψ hpψ V hV hb w e t ht

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! A component material test is controlled by the actual weighted preparation norm. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem weighted_material_primitive_pairing {S : Finset Comp} {K : ℕ} (hK : 1 ≤ K)
    (U : ∀ v : CompIn S, TorusHk K (hr v.1.root)) (π w : CompIn S → ℝ)
    (hπw : ∀ v, 0 < π v / w v ^ 2) (v : CompIn S) (e : hr v.1.root)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s t : ℝ)
    (η ψ : Vec 2 → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hpη : IsZ2Periodic η) (hpψ : IsZ2Periodic ψ)
    (i : Fin 2) {ell ρ L : ℝ} (hell : 0 < ell) (hρ : 0 < ρ)
    (hder : ∀ x, spaceGrad η x i = ell * ψ x)
    (hnorm : (∫ y in unitCube, η y ^ 2) = 1)
    (hX : ∀ x, ‖fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ t z s) x‖ ≤ L) :
    |∫ x in unitCube, inner ℝ e ((U v).toFunction.jet (valueIndex2 K) x) *
      periodicMaterialTestField hφ s ψ (t, x)| ≤
      Real.sqrt (2 * L ^ 2) * ‖e‖ * Real.sqrt (π v / w v ^ 2) *
        weightedNorm ρ π w U / (ρ * ell) := by
  have hp := hilbert_carrier_material_primitive_pairing hφ s t hK (U v) e
    η ψ hη hpη hpψ i hell hρ hder hnorm hX
  have hc := KernelEnergy.componentFactorialRoot_le_mass ρ (fun v => π v / w v ^ 2)
    hπw (fun v => (U v).val) v
  change Real.sqrt (factorialNormSq ρ (U v).val) ≤
    Real.sqrt (π v / w v ^ 2) * weightedNorm ρ π w U at hc
  calc
    _ ≤ Real.sqrt (2 * L ^ 2) * ‖e‖ * Real.sqrt (factorialNormSq ρ (U v).val) /
        (ρ * ell) := hp
    _ ≤ Real.sqrt (2 * L ^ 2) * ‖e‖ *
        (Real.sqrt (π v / w v ^ 2) * weightedNorm ρ π w U) / (ρ * ell) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg e))) (mul_pos hρ hell).le
    _ = _ := by ring
end

/-! The common preparation's enhanced bound controls a literal material Fourier test. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]

theorem common_preparation_material_primitive_pairing {D : OCData} {Dm j₀ : ℕ} {b : ℝ}
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm b j₀)
    {cr Q CQ C : ℝ} {p Nout Naux : ℕ} {s tf tp : ℝ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ C p Nout Naux s tf tp Preg)
    (hN : 1 ≤ Nout) (w : CompIn G.comps → ℝ)
    (hw : (w = fun _ => 1) ∨ w = G.marker law)
    (hπw : ∀ v, 0 < G.mass law v / w v ^ 2)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root))
    (v : CompIn G.comps) (e : hr v.1.root)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (η ψ : Vec 2 → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hpη : IsZ2Periodic η) (hpψ : IsZ2Periodic ψ)
    (i : Fin 2) {ell L : ℝ} (hell : 0 < ell) (hρ : 0 < rhoEnh D cr G.level)
    (hder : ∀ x, spaceGrad η x i = ell * ψ x)
    (hnorm : (∫ y in unitCube, η y ^ 2) = 1)
    (hX : ∀ x, ‖fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ tp z s) x‖ ≤ L) :
    |∫ x in unitCube, inner ℝ e ((Preg f v).toFunction.jet (valueIndex2 Nout) x) *
      periodicMaterialTestField hφ s ψ (tp, x)| ≤
      Real.sqrt (2 * L ^ 2) * ‖e‖ * Real.sqrt (G.mass law v / w v ^ 2) *
        (CQ * weightedNorm 1 (G.mass law) w f) / (rhoEnh D cr G.level * ell) := by
  have hb := (hprep.2.2.2.2 w hw f).2.2.1
  have hm := weighted_material_primitive_pairing hN (Preg f) (G.mass law) w hπw v e
    hφ s tp η ψ hη hpη hpψ i hell hρ hder hnorm hX
  exact hm.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg _)))
    (mul_pos hρ hell).le)
end

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Order-zero dissipation for the actual stream requires no positive-order drift budget. -/

section
open AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergy.Galerkin
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)

/-- Order-zero native energy contracts on every subinterval of the solution window. -/
theorem stream_homogeneous_interval {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ V)
    (f : ∀ i, TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i))
    (u : ∀ i, ℝ → TorusHk 0 (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => 0)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient f
      (P.carrierFlux w) (fun _ _ => 0) u w) :
    ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
      massNormSq ρ P.π (fun i => (u i t).val) +
        (5 * ν / 4) * (∫ r in Set.Ioc s t,
          massGradNormSq ρ P.π (fun i => (w i r).val)) ≤
        massNormSq ρ P.π (fun i => (u i s).val) := by
  classical
  obtain ⟨hv, hp, hd, _hb, hm⟩ := stream_kernel_drift_data hφ a b
  have hsmall : 1 * ρ / (2 * ρ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) P.radius_pos)).mpr
    ring_nf
    exact le_rfl
  have hs : IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => 0)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient f
      (fun i t => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i))) + P.carrierFlux w i t)
      (fun _ _ => 0) u w := by
    simpa only [zero_add] using hsol
  exact P.kernelForcedWeakSolution_homogeneous_interval (streamVel φ) hv hp
    0 1 (2 * ρ) le_rfl le_rfl (mul_pos (by norm_num) P.radius_pos) hsmall
    (by simp only [zero_mul]; exact (div_nonneg P.diffusivity_pos.le (by norm_num)))
    hd (fun _ _ l hl hl0 _ => by omega) hm V hV hb
    (fun _ => driftCarrierBudget 0 V 0 1 (2 * ρ))
    (fun t ht _ => driftCarrierBudget_bounds 0 (streamVel φ t) V 0 1 (2 * ρ) hV
      (hb t ht) (fun l hl hl0 _ => by omega)) w u f hs


/-- The whole-window native dissipation follows from interval contraction. -/
theorem stream_homogeneous_dissipation {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ V)
    (f : ∀ i, TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i))
    (u : ∀ i, ℝ → TorusHk 0 (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => 0)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient f
      (P.carrierFlux w) (fun _ _ => 0) u w) :
    (5 * ν / 4) * (∫ t in Set.Icc a b,
      massGradNormSq ρ P.π (fun i => (w i t).val)) ≤
      massNormSq ρ P.π (fun i => (f i).val) := by
  have he := stream_homogeneous_interval P hφ V hV hb f w u hsol
    a ⟨le_rfl, P.htime⟩ b ⟨P.htime, le_rfl⟩ P.htime
  have hinit : (fun i => (u i a).val) = (fun i => (f i).val) :=
    funext (fun i => congrArg Subtype.val (hsol.2.2.2.1 i))
  rw [hinit] at he
  rw [integral_Icc_eq_integral_Ioc]
  exact (le_add_of_nonneg_left (massNormSq_nonneg ρ P.π P.hπ (fun i => (u i b).val))).trans he

end TorusKernelOperator
end

/-! Order-zero dissipation for the actual stream requires no positive-order drift budget. -/

section
open AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergy.Galerkin
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)

theorem stream_homogeneous_mass_at {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ V)
    (f : ∀ i, TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i))
    (u : ∀ i, ℝ → TorusHk 0 (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => 0)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient f
      (P.carrierFlux w) (fun _ _ => 0) u w)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    massNormSq ρ P.π (fun i => (u i t).val) ≤
      massNormSq ρ P.π (fun i => (f i).val) := by
  classical
  obtain ⟨hv, hp, hd, _hb, hm⟩ := stream_kernel_drift_data hφ a b
  have hsmall : 1 * ρ / (2 * ρ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) P.radius_pos)).mpr
    ring_nf
    exact le_rfl
  have hs : IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => 0)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient f
      (fun i t => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i))) + P.carrierFlux w i t)
      (fun _ _ => 0) u w := by
    simpa only [zero_add] using hsol
  have he := P.kernelForcedWeakSolution_homogeneous_interval (streamVel φ) hv hp
    0 1 (2 * ρ) le_rfl le_rfl (mul_pos (by norm_num) P.radius_pos) hsmall
    (by simp only [zero_mul]; exact (div_nonneg P.diffusivity_pos.le (by norm_num)))
    hd (fun _ _ l hl hl0 _ => by omega) hm V hV hb
    (fun _ => driftCarrierBudget 0 V 0 1 (2 * ρ))
    (fun t ht _ => driftCarrierBudget_bounds 0 (streamVel φ t) V 0 1 (2 * ρ) hV
      (hb t ht) (fun l hl hl0 _ => by omega)) w u f hs
    a ⟨le_rfl, P.htime⟩ t ht ht.1
  have hinit : (fun i => (u i a).val) = (fun i => (f i).val) :=
    funext (fun i => congrArg Subtype.val (hsol.2.2.2.1 i))
  rw [hinit] at he
  exact (le_add_of_nonneg_right (mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) P.diffusivity_pos.le) (by norm_num))
    (integral_nonneg (fun r => massGradNormSq_nonneg ρ P.π P.hπ _)))).trans he

end TorusKernelOperator
end

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.Buffer

/-! The preparation error is tested in the same physical material pairing as its enhanced bound. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem weighted_material_value_pairing_le {S : Finset Comp}
    (U : ∀ v : CompIn S, TorusHk 0 (hr v.1.root)) (π w : CompIn S → ℝ)
    (hπw : ∀ v, 0 < π v / w v ^ 2) (v : CompIn S) (e : hr v.1.root)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s t : ℝ)
    (ψ : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    (hnorm : (∫ x in unitCube, ψ x ^ 2) = 1) :
    |∫ x in unitCube, inner ℝ e ((U v).toFunction.jet (valueIndex2 0) x) *
      periodicMaterialTestField hφ s ψ (t, x)| ≤
      ‖e‖ * Real.sqrt (π v / w v ^ 2) * weightedNorm 1 π w U := by
  let z := periodicMaterialHilbertTest hφ s ψ hψ hpψ e t
  have he : (∫ x in unitCube, inner ℝ e ((U v).toFunction.jet (valueIndex2 0) x) *
      periodicMaterialTestField hφ s ψ (t, x)) =
      inner ℝ (torusHkValueCLM (U v)) (torusHkValueCLM z) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [torusRawValue_ae (U v),
      periodicMaterialHilbertTest_value_ae hφ s ψ hψ hpψ e t] with x hu hz
    have hzx : (torusHkValueCLM z) x = periodicMaterialTestField hφ s ψ (t, x) • e := hz
    rw [hu, hzx, inner_smul_right, real_inner_comm]
    exact mul_comm _ _
  have hc := KernelEnergy.componentFactorialRoot_le_mass 1 (fun v => π v / w v ^ 2)
    hπw (fun v => (U v).val) v
  have hsq : factorialNormSq 1 (U v).val = ‖(U v).val‖ ^ 2 := by
    rw [factorialNormSq_zero_eq_derivative, jet_norm_sq_eq_sum]
    simp
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hc
  have hv := (PiLp.norm_apply_le (U v).val (valueIndex2 0)).trans hc
  rw [he]
  have hb := abs_real_inner_le_norm (torusHkValueCLM (U v)) (torusHkValueCLM z)
  rw [material_test_value_norm hφ s t ψ hψ hpψ hnorm e] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_right hv (norm_nonneg e)).trans_eq (by
    change (Real.sqrt (π v / w v ^ 2) * weightedNorm 1 π w U) * ‖e‖ = _
    ring))

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual incoming stage invariant supplies the literal regularized kernel operator. -/

section
open KernelEnergy
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

def nativeInvariantKernelOperator
    (law : BirthLaw) (P : ProvParams) (Mn : SuccMenu) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (k : InvConsts)
    (a b S θ : ℝ) (seed G : GenStage D hr Dm bw j₀)
    (hI : IsStageInvariant law P seedK freshK φ₀ hφ₀ M k a b S θ G)
    (hseed : ∀ v : CompIn seed.comps, v.1.births = []) (hc : IsCascadeStage D P Mn seed G)
    (hk : k.Hprod = k.G0 + Mn.H + 1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hε : 0 < D.eps (G.level - 1))
    (hab : a ≤ b) (hν : 0 < D.kap G.level)
    (hρ : 0 < rhoStar D k.c₀ G.level)
    (hρε : rhoStar D k.c₀ G.level ≤ D.eps (G.level - 1)) (hD : 2 ≤ Dm)
    (hθ : θ ≤ 1 / 8) (n : ℕ) (hn : n ≤ k.Ks)
    (w : CompIn G.comps → ℝ) (hw : (w = fun _ => 1) ∨ w = G.marker law) :
    TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root)
      a b (rhoStar D k.c₀ G.level) (D.kap G.level) n Dm := by
  rcases hI with ⟨hnat, _htags, _hgen, hshift, hpar, hcert, henv, _hledger,
    hkernel, hschur, _hquiet⟩
  have hs := (henv (fun _ => n) (fun _ => hn)).1.molecular.1
  have hwpos (v : CompIn G.comps) : 0 < w v := by
    rcases hw with hw | hw
    · rw [hw]
      exact zero_lt_one
    · rw [hw]
      exact birth_compMarker_pos hq hΛ law v.1
  refine {
    htime := hab
    radius_pos := hρ
    diffusivity_pos := hν
    order_ge_two := hD
    π := fun v => G.mass law v / w v ^ 2
    hπ := fun v => div_pos (birth_compMass_pos hq hΛ law v.1) (pow_pos (hwpos v) 2)
    B := fun v u γ d => G.physCoeff v u γ d.1
    hB_meas := ?_
    hB_smooth := ?_
    hB_per := ?_
    hB_fin := ?_
    C := fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root)
    S := G.sysS P seedK freshK φ₀ hφ₀
    c := k.cker
    r := fun v u γ => (G.kernelOf P seedK freshK v u γ).width
    hr := ?_
    hS := fun v u γ => (hkernel v u γ).2.2.2.2 _ hρ n hn
    θ := θ
    hθ := hθ
    hschur := hschur n hn w hw }
  · intro v u γ d
    exact native_physCoeff_joint_measurable hnat hcert (by omega) hi hj a b k.mEnv
      (fun _ => n + k.Jm) hs v u γ d.1
  · intro v u γ d t ht
    exact (native_physCoeff_spatial_smooth hnat hi hj a b k.mEnv hε.ne'
      (fun _ => n + k.Jm) hs v u γ d.1 t ht).of_le (by exact_mod_cast Nat.le_add_right n k.Jm)
  · intro v u γ d t _
    exact native_physCoeff_periodic hnat hshift v u γ d.1 t
  · intro v u γ d
    exact native_physCoeff_coefficientSeminorm_finite hcert hpar hnat hi hj hb hε
      a b k.mEnv (fun _ => n + k.Jm) hs v u γ
      (cascade_component_reserve_pos hseed hc k hk v).le
      ((compReserve_le_one k v.1).trans (by norm_num))
      _ hρ hρε n d.1 (Nat.le_add_right n k.Jm)
  · intro v u γ
    rw [(hkernel v u γ).2.1]
    exact (G.fam.identity v u γ).record.width_pos
end

/-! The actual operator's spatial data are independent of the represented order. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_kernel_operator_data
    (law : BirthLaw) (P : ProvParams) (Mn : SuccMenu) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (k : InvConsts)
    (a b S θ : ℝ) (seed G : GenStage D hr Dm bw j₀)
    (hI : IsStageInvariant law P seedK freshK φ₀ hφ₀ M k a b S θ G)
    (hseed : ∀ v : CompIn seed.comps, v.1.births = []) (hc : IsCascadeStage D P Mn seed G)
    (hk : k.Hprod = k.G0 + Mn.H + 1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hε : 0 < D.eps (G.level - 1))
    (hab : a ≤ b) (hν : 0 < D.kap G.level)
    (hρ : 0 < rhoStar D k.c₀ G.level)
    (hρε : rhoStar D k.c₀ G.level ≤ D.eps (G.level - 1)) (hD : 2 ≤ Dm)
    (hθ : θ ≤ 1 / 8) (n : ℕ) (hn : n ≤ k.Ks)
    (w : CompIn G.comps → ℝ) (hw : (w = fun _ => 1) ∨ w = G.marker law) :
    let R := nativeInvariantKernelOperator law P Mn seedK freshK φ₀ hφ₀ M k a b S θ seed G hI hseed hc hk hq hΛ hi hj hb hε hab hν hρ hρε hD hθ n hn w hw
    R.π = (fun v => G.mass law v / w v ^ 2) ∧
    R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1) ∧
    R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) => ContinuousLinearMap.id ℝ (hr u.1.root)) ∧
    R.S = G.sysS P seedK freshK φ₀ hφ₀ := by
  exact ⟨rfl, rfl, rfl, rfl⟩
end

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.Construction.Preservation.Buffer

/-! The common preparation error controls the physical material pairing of the actual evolution. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]

theorem common_preparation_material_error {D : OCData} {Dm j₀ : ℕ} {b : ℝ}
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm b j₀)
    {cr Q CQ C : ℝ} {p Nout Naux : ℕ} {s tf tp : ℝ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ C p Nout Naux s tf tp Preg)
    (w : CompIn G.comps → ℝ) (hw : (w = fun _ => 1) ∨ w = G.marker law)
    (hπw : ∀ v, 0 < G.mass law v / w v ^ 2)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ G.level)
      (streamVel (D.Φ G.level)) 0 s tf f (fun _ _ => 0) (fun _ _ => 0) U W Y)
    (v : CompIn G.comps) (e : hr v.1.root)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (ψ : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    (hnorm : (∫ x in unitCube, ψ x ^ 2) = 1) :
    |inner ℝ (torusHkValueCLM (Preg f v))
        (torusHkValueCLM (periodicMaterialHilbertTest hφ s ψ hψ hpψ e tp)) -
      inner ℝ (torusHkValueCLM (U v tp))
        (torusHkValueCLM (periodicMaterialHilbertTest hφ s ψ hψ hpψ e tp))| ≤
      ‖e‖ * Real.sqrt (G.mass law v / w v ^ 2) *
        (CQ * D.eps (G.level - 1) ^ Q * weightedNorm 1 (G.mass law) w f) := by
  let err := fun v : CompIn G.comps => truncateTorusHk (Nat.zero_le Nout) (Preg f v) - U v tp
  have hb := (hprep.2.2.2.2 w hw f).1 U W Y hsol
  have he := weighted_material_value_pairing_le err (G.mass law) w hπw v e
    hφ s tp ψ hψ hpψ hnorm
  rw [materialCarrier_pairing_readout] at he
  dsimp only [err] at he
  rw [map_sub, torusHkValue_truncate, inner_sub_left] at he
  exact he.trans (mul_le_mul_of_nonneg_left hb
    (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! A single invariant supplies all represented orders on the actual evolution window. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

def nativeKernelOperatorWindowFamily
    (law : BirthLaw) (P : ProvParams) (Mn : SuccMenu) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (k : InvConsts)
    (a b S θ : ℝ) (seed G : GenStage D hr Dm bw j₀)
    (hI : IsStageInvariant law P seedK freshK φ₀ hφ₀ M k a b S θ G)
    (hseed : ∀ v : CompIn seed.comps, v.1.births = []) (hc : IsCascadeStage D P Mn seed G)
    (hk : k.Hprod = k.G0 + Mn.H + 1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hε : 0 < D.eps (G.level - 1))
    (hab : a ≤ b) (hν : 0 < D.kap G.level)
    (hρ : 0 < rhoStar D k.c₀ G.level)
    (hρε : rhoStar D k.c₀ G.level ≤ D.eps (G.level - 1)) (hD : 2 ≤ Dm)
    (hθ : θ ≤ 1 / 8) (K : ℕ) (hK : K ≤ k.Ks)
    (w : CompIn G.comps → ℝ) (hw : (w = fun _ => 1) ∨ w = G.marker law)
    (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    (j : Fin (K + 1)) → KernelEnergy.TorusKernelOperator
      (h := fun v : CompIn G.comps => hr v.1.root) (Γ := G.fam.Γ)
      (G := fun _ u _ => hr u.1.root)
      c b (rhoStar D k.c₀ G.level) (D.kap G.level) j.val Dm := by
  intro j
  exact kernelOperator_time_restrict
    (nativeInvariantKernelOperator law P Mn seedK freshK φ₀ hφ₀ M k a b S θ seed G hI hseed hc hk hq hΛ hi hj hb hε hab hν hρ hρε hD hθ j.val
      ((Nat.le_of_lt_succ j.isLt).trans hK) w hw)
    (Set.Icc_subset_Icc hac le_rfl) hcb
end

/-! One spatial data family is shared by every order of the restricted actual operator. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_kernel_window_family_data
    (law : BirthLaw) (P : ProvParams) (Mn : SuccMenu) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (k : InvConsts)
    (a b S θ : ℝ) (seed G : GenStage D hr Dm bw j₀)
    (hI : IsStageInvariant law P seedK freshK φ₀ hφ₀ M k a b S θ G)
    (hseed : ∀ v : CompIn seed.comps, v.1.births = []) (hc : IsCascadeStage D P Mn seed G)
    (hk : k.Hprod = k.G0 + Mn.H + 1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hε : 0 < D.eps (G.level - 1))
    (hab : a ≤ b) (hν : 0 < D.kap G.level)
    (hρ : 0 < rhoStar D k.c₀ G.level)
    (hρε : rhoStar D k.c₀ G.level ≤ D.eps (G.level - 1)) (hD : 2 ≤ Dm)
    (hθ : θ ≤ 1 / 8) (K : ℕ) (hK : K ≤ k.Ks)
    (w : CompIn G.comps → ℝ) (hw : (w = fun _ => 1) ∨ w = G.marker law)
    (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    let R := nativeKernelOperatorWindowFamily law P Mn seedK freshK φ₀ hφ₀ M k a b S θ seed G hI hseed hc hk hq hΛ hi hj hb hε hab hν hρ hρε hD hθ K hK w hw c hac hcb
    ∀ j : Fin (K + 1),
      (R j).π = (fun v => G.mass law v / w v ^ 2) ∧
      (R j).B = (R (Fin.last K)).B ∧
      (R j).C = (R (Fin.last K)).C ∧
      (R j).S = (R (Fin.last K)).S := by
  intro R j
  have hjorder := (Nat.le_of_lt_succ j.isLt).trans hK
  have hlast := (Nat.le_of_lt_succ (Fin.last K).isLt).trans hK
  have hdj := native_kernel_operator_data law P Mn seedK freshK φ₀ hφ₀ M k a b S θ seed G hI hseed hc hk hq hΛ hi hj hb hε hab hν hρ hρε hD hθ j.val hjorder w hw
  have hdl := native_kernel_operator_data law P Mn seedK freshK φ₀ hφ₀ M k a b S θ seed G hI hseed hc hk hq hΛ hi hj hb hε hab hν hρ hρε hD hθ (Fin.last K).val hlast w hw
  exact ⟨hdj.1, hdj.2.1.trans hdl.2.1.symm,
    hdj.2.2.1.trans hdl.2.2.1.symm, hdj.2.2.2.trans hdl.2.2.2.symm⟩
end

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.Construction.Preservation.Buffer

/-! A normalized material datum removes component weights from both preparation pairing prices. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]

theorem normalized_common_preparation_pairings {D : OCData} {Dm j₀ : ℕ} {b : ℝ}
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm b j₀)
    {cr Q CQ C : ℝ} {p Nout Naux : ℕ} {s tf tp : ℝ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ C p Nout Naux s tf tp Preg)
    (hN : 1 ≤ Nout) (w : CompIn G.comps → ℝ)
    (hw : (w = fun _ => 1) ∨ w = G.marker law)
    (hπw : ∀ v, 0 < G.mass law v / w v ^ 2) (v : CompIn G.comps) (e : hr v.1.root)
    (he : ‖e‖ = 1) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (ψ η : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hpη : IsZ2Periodic η)
    (hnormψ : (∫ x in unitCube, ψ x ^ 2) = 1)
    (hnormη : (∫ x in unitCube, η x ^ 2) = 1)
    (i : Fin 2) {ell L : ℝ} (hell : 0 < ell) (hρ : 0 < rhoEnh D cr G.level)
    (hder : ∀ x, spaceGrad η x i = ell * ψ x)
    (hX : ∀ x, ‖fderiv ℝ (fun y => AVRegularity.streamFlow φ hφ tp y s) x‖ ≤ L)
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ G.level)
      (streamVel (D.Φ G.level)) 0 s tf
      (Pi.single v (materialInitialDatum hφ s ψ hψ hpψ e) :
        ∀ u : CompIn G.comps, TorusHk 0 (hr u.1.root))
      (fun _ _ => 0) (fun _ _ => 0) U W Y) :
    let f := (Pi.single v (materialInitialDatum hφ s ψ hψ hpψ e) :
      ∀ u : CompIn G.comps, TorusHk 0 (hr u.1.root))
    let z := torusHkValueCLM (periodicMaterialHilbertTest hφ s ψ hψ hpψ e tp)
    |inner ℝ (torusHkValueCLM (Preg f v)) z - inner ℝ (torusHkValueCLM (U v tp)) z| ≤
      CQ * D.eps (G.level - 1) ^ Q ∧
    |inner ℝ (torusHkValueCLM (Preg f v)) z| ≤
      Real.sqrt (2 * L ^ 2) * CQ / (rhoEnh D cr G.level * ell) := by
  dsimp only
  let f := (Pi.single v (materialInitialDatum hφ s ψ hψ hpψ e) :
    ∀ u : CompIn G.comps, TorusHk 0 (hr u.1.root))
  have hf : weightedNorm 1 (G.mass law) w f =
      Real.sqrt (G.mass law v / w v ^ 2)⁻¹ := by
    exact weighted_material_initial_norm (hr := hr) (G.mass law) w v hφ s ψ hψ hpψ hnormψ e he
  constructor
  · have hb := common_preparation_material_error law P seedK freshK φ₀ hφ₀ G Preg hprep
      w hw hπw f U W Y hsol v e hφ ψ hψ hpψ hnormψ
    apply hb.trans_eq
    rw [he, one_mul, hf, normalized_preparation_error_price (hπw v)]
  · have hb := common_preparation_material_primitive_pairing law P seedK freshK φ₀ hφ₀ G Preg hprep
      hN w hw hπw f v e hφ η ψ hη hpη hpψ i hell hρ hder hnormη hX
    rw [materialCarrier_pairing_readout (Preg f v) hφ s tp ψ hψ hpψ e,
      he, mul_one, hf, normalized_preparation_enhanced_price (hπw v)] at hb
    exact hb

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Actual order-zero kernel evolution exists for every rough datum without positive-order drift bounds. -/

section
open AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergy.Galerkin
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
variable {a b ρ ν : ℝ} {D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)

theorem stream_kernel_order_zero_exists {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (f : ∀ i, TorusHk 0 (h i)) :
    ∃ (u : ∀ i, ℝ → TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i))
      (y : ∀ i j (α : Γ i j), ℝ → TorusHk (0 + D - 1) (G i j α)),
      IsKernelWeakSolutionTorus ν a b (streamVel φ) 0 D P.B P.C P.S f
        (fun _ _ => 0) (fun _ _ => 0) u w y := by
  obtain ⟨hv, hp, hd, hb, hm⟩ := stream_kernel_drift_data hφ a b
  have hsmall : 1 * ρ / (2 * ρ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) P.radius_pos)).mpr
    ring_nf
    exact le_rfl
  exact P.kernelFourier_exists_weakSolution (streamVel φ) hv hp
    (fun _ _ => 0) (fun _ _ => 0) 0 1 (2 * ρ) le_rfl le_rfl
    (mul_pos (by norm_num) P.radius_pos) hsmall
    (by simp only [zero_mul]; exact (div_nonneg P.diffusivity_pos.le (by norm_num)))
    hd (fun _ _ l hl hl0 _ => by omega) hb hm f
    (fun i => timeMemLp_zero (E := TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i))) _ 2)
    (fun i => timeIntegrable_zero (E := TorusHk 0 (h i)) _)

end TorusKernelOperator
end

/-! The actual native weak solution has the compiled complete carrier-flux equation. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_forced (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν 0 Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) 0 a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y) :
    IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => 0)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient f
      (R.carrierFlux W) (fun _ _ => 0) U W := by
  have hs : IsKernelWeakSolutionTorus ν a b (streamVel φ) 0 Dm R.B R.C R.S f
      (fun _ _ => 0) (fun _ _ => 0) U W Y := by
    simpa only [hB, hC, hS, GenStage.IsRegSolution] using hsol
  obtain ⟨hv, _hp, _hd, ⟨V, hV⟩, _hm⟩ := stream_kernel_drift_data hφ a b
  have hf := R.kernelWeakSolution_forcedWeakSolution (streamVel φ) hv (max V 0)
    (le_max_right _ _) (fun t ht x => (hV t ht x).trans (le_max_left _ _))
    f (fun _ _ => 0) (fun _ _ => 0) U W Y hs
  simpa only [zero_add] using hf
end

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.KernelEnergy.TorusKernelOperator
namespace AVRegularity.Construction.Preservation.Buffer

/-! A literal weak evolution satisfies the material increment estimate for its complete flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem orderZero_material_increment {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) {a b : ℝ} (hab : a ≤ b)
    (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ V)
    (ν : ℝ) (f : ∀ i, TorusHk 0 (h i))
    (F : ∀ i, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)))
    (w : ∀ i, ℝ → TorusHk 1 (h i)) (u : ∀ i, ℝ → TorusHk 0 (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => 0)
      noLocalCoefficient f F (fun _ _ => 0) u w)
    (i : ι) (ψ : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hpψ : IsZ2Periodic ψ) (e : h i) (L : ℝ)
    (hflux : MemLp (fun t => torusHkValueCLM
      (ν • torusGradientTensor (w i t) + F i t)) 2 (volume.restrict (Set.Icc a b)))
    (hgrad : ∀ t ∈ Set.Icc a b, ‖torusH1GradientL2CLM (E := h i)
      (periodicMaterialHilbertTest hφ a ψ hψ hpψ e t)‖ ≤ L) :
    |inner ℝ (torusHkValueCLM (u i b))
        (torusHkValueCLM (periodicMaterialHilbertTest hφ a ψ hψ hpψ e b)) -
      inner ℝ (torusHkValueCLM (u i a))
        (torusHkValueCLM (periodicMaterialHilbertTest hφ a ψ hψ hpψ e a))| ≤
      L * ∫ t in a..b, ‖torusHkValueCLM
        (ν • torusGradientTensor (w i t) + F i t)‖ := by
  let hv := (Infra.Construction.smoothPeriodic_streamVel hφ).smooth.continuous
  have hs := windowDriftSource_time_memLp hab (streamVel φ) hv V hV hb (w i) (hsol.2.1 i)
  have hsi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (MemLp.integrable (by norm_num) hs)
  have hfi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (MemLp.integrable (by norm_num) hflux)
  exact transported_pairing_increment_bound_ae hab
    torusHkValueCLM (torusH1GradientL2CLM (E := h i))
    (fun t => torusHkValueCLM (u i t)) (windowDriftSource hab (streamVel φ) hv V hV hb (w i))
    (fun t => torusHkValueCLM (ν • torusGradientTensor (w i t) + F i t)) hsi hfi
    (fun t ht z => orderZero_physical_weak_identity hab (streamVel φ) hv V hV hb ν f F w u hsol i t ht z)
    (periodicMaterialHilbertTest hφ a ψ hψ hpψ e)
    (periodicMaterialHilbertTestDerivative hφ a ψ hψ hpψ e)
    (periodicMaterialHilbertTest_strong_time hφ a ψ hψ hpψ e hab)
    (window_material_cancellation_ae hφ hab a ψ hψ hpψ V hV hb (w i) (u i) (hsol.2.2.1 i) e)
    hgrad

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! The rough-data buffer in exactly the weighted norm of the preparation statement. -/

open KernelEnergy
variable {comps : Finset Comp} {hr : ℕ → Type}
    [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
variable {Γ : (CompIn comps) → (CompIn comps) → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν δt : ℝ} {K D : ℕ}

theorem weighted_kernel_rough_solution_buffer
    (PP : (j : Fin (K + 1)) →
      TorusKernelOperator (h := fun i : CompIn comps => hr i.1.root) (Γ := Γ) (G := G) a b ρ ν j.val D)
    (P : TorusKernelOperator (h := fun i : CompIn comps => hr i.1.root) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (hP : PP ⟨0, Nat.zero_lt_succ K⟩ = P)
    (π wgt : (CompIn comps) → ℝ) (hπ : ∀ j, (PP j).π = fun i => π i / wgt i ^ 2)
    (hBdata : ∀ j, (PP j).B = (PP (Fin.last K)).B)
    (hCdata : ∀ j, (PP j).C = (PP (Fin.last K)).C)
    (hSdata : ∀ j, (PP j).S = (PP (Fin.last K)).S)
    (hb : 0 < δt) (hbT : a + δt ≤ b) (hRad : ρ ^ 2 ≤ (5 * ν / 4) * δt)
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
    (f : ∀ i : CompIn comps, TorusHk 0 (hr i.1.root))
    (u : ∀ i : CompIn comps, ℝ → TorusHk 0 (hr i.1.root)) (w : ∀ i : CompIn comps, ℝ → TorusHk 1 (hr i.1.root))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (0 + D - 1) (G i j α))
    (hsol : IsKernelWeakSolutionTorus ν a b v 0 D P.B P.C P.S f
      (fun _ _ => 0) (fun _ _ => 0) u w y) :
    ∀ j ≤ K, ∀ t ∈ Set.Icc (a + δt) b, ∃ W : ∀ i : CompIn comps, TorusHk j (hr i.1.root),
      (∀ i, truncateTorusHk (Nat.zero_le j) (W i) = u i t) ∧
      weightedNorm ρ π wgt W ≤ Real.sqrt (bufferEnergyCost j) * weightedNorm 1 π wgt f := by
  classical
  have hbfr := kernel_rough_solution_buffer PP P hP (fun i => π i / wgt i ^ 2) hπ
    hBdata hCdata hSdata hb hbT hRad v hv hvp αv B lam hα hB hlam hsmall hstrain hd
    hjets hv_bdd hv_meas f u w y hsol
  intro j hj t ht
  obtain ⟨W, hW, hbound⟩ := hbfr j hj t ht
  exact ⟨W, hW, weighted_buffer_readout ρ j π wgt f W hbound⟩

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Weighted energy controls the material increment of a literal homogeneous kernel evolution. -/

open AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Variational
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)

theorem kernel_material_increment_of_dissipation {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ V)
    (f : ∀ i, TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i))
    (u : ∀ i, ℝ → TorusHk 0 (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => 0)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient f
      (P.carrierFlux w) (fun _ _ => 0) u w)
    (i : ι) (ψ : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hpψ : IsZ2Periodic ψ) (e : h i) (L : ℝ) (hL : 0 ≤ L)
    (hgrad : ∀ t ∈ Set.Icc a b, ‖torusH1GradientL2CLM (E := h i)
      (periodicMaterialHilbertTest hφ a ψ hψ hpψ e t)‖ ≤ L)
    {M : ℝ} (henergy : (5 * ν / 4) *
      (∫ t in Set.Icc a b, massGradNormSq ρ P.π (fun i => (w i t).val)) ≤ M) :
    |inner ℝ (CoupledEnergy.Galerkin.torusHkValueCLM (u i b))
        (CoupledEnergy.Galerkin.torusHkValueCLM (periodicMaterialHilbertTest hφ a ψ hψ hpψ e b)) -
      inner ℝ (CoupledEnergy.Galerkin.torusHkValueCLM (u i a))
        (CoupledEnergy.Galerkin.torusHkValueCLM (periodicMaterialHilbertTest hφ a ψ hψ hpψ e a))| ≤
      L * ((Real.sqrt (P.π i) * (ν * (1 + P.θ))) * Real.sqrt (b - a) *
        Real.sqrt (M / (5 * ν / 4))) := by
  exact (orderZero_material_increment hφ P.htime V hV hb ν f (P.carrierFlux w) w u hsol
    i ψ hψ hpψ e L (total_flux_value_memLp P w hsol.2.1 i) hgrad).trans
      (mul_le_mul_of_nonneg_left (total_flux_value_integral_le P w hsol.2.1 i henergy) hL)

end TorusKernelOperator

end AVRegularity.Construction.Preservation.Buffer
end
