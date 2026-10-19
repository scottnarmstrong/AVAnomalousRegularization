-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Buffer.KernelMaterialIncrement
public import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
public import AVRegularity.Construction.Preservation.Buffer.WeightedMaterialInitialNorm
import AVRegularity.Construction.StrainPhysical.Context

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Transfer the compiled rough order-zero existence theorem to the literal native system. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_kernel_order_zero_exists (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
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
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) :
    ∃ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (W : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
      (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root)),
      G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) 0 a b f
        (fun _ _ => 0) (fun _ _ => 0) U W Y := by
  obtain ⟨U, W, Y, hsol⟩ := TorusKernelOperator.stream_kernel_order_zero_exists R hφ f
  refine ⟨U, W, Y, ?_⟩
  change IsKernelWeakSolutionTorus ν a b (streamVel φ) 0 Dm
    (fun v u γ d => G.physCoeff v u γ d.1)
    (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
    (G.sysS P seedK freshK φ₀ hφ₀) f (fun _ _ => 0) (fun _ _ => 0) U W Y
  simpa only [hB, hC, hS] using hsol
end

/-! Instantiate the rough kernel buffer with the actual OC stream drift. -/

section
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

theorem actual_stream_weighted_kernel_buffer
    (PP : (j : Fin (K + 1)) →
      TorusKernelOperator (h := fun i : CompIn comps => hr i.1.root) (Γ := Γ) (G := G) a b ρ ν j.val D)
    (P : TorusKernelOperator (h := fun i : CompIn comps => hr i.1.root) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (hP : PP ⟨0, Nat.zero_lt_succ K⟩ = P)
    (π wgt : (CompIn comps) → ℝ) (hπ : ∀ j, (PP j).π = fun i => π i / wgt i ^ 2)
    (hBdata : ∀ j, (PP j).B = (PP (Fin.last K)).B)
    (hCdata : ∀ j, (PP j).C = (PP (Fin.last K)).C)
    (hSdata : ∀ j, (PP j).S = (PP (Fin.last K)).S)
    (hb : 0 < δt) (hbT : a + δt ≤ b) (hRad : ρ ^ 2 ≤ (5 * ν / 4) * δt)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 1 ≤ m)
    (hsmall : 1024 * ρ / ocEpsilon q Λ m ≤ 1 / 2)
    (hstrain : (actualDriftJetConstant * ocA α q Λ m) * 1024 * ρ ^ 2 ≤ ν / 8)
    (f : ∀ i : CompIn comps, TorusHk 0 (hr i.1.root))
    (u : ∀ i : CompIn comps, ℝ → TorusHk 0 (hr i.1.root)) (w : ∀ i : CompIn comps, ℝ → TorusHk 1 (hr i.1.root))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (0 + D - 1) (G i j α))
    (hsol : IsKernelWeakSolutionTorus ν a b (AVenhance.streamVel (Φ m)) 0 D P.B P.C P.S f
      (fun _ _ => 0) (fun _ _ => 0) u w y) :
    ∀ j ≤ K, ∀ t ∈ Set.Icc (a + δt) b, ∃ W : ∀ i : CompIn comps, TorusHk j (hr i.1.root),
      (∀ i, truncateTorusHk (Nat.zero_le j) (W i) = u i t) ∧
      weightedNorm ρ π wgt W ≤ Real.sqrt (bufferEnergyCost j) * weightedNorm 1 π wgt f := by
  have he : 0 < ocEpsilon q Λ m := (Scales.epsilon_basic hq.1 hΛ).1
  have ha : 0 < ocA α q Λ m := Real.rpow_pos_of_pos he _
  have hcur := Velocity.streamSeq_admissible hζ hΛ hΦ m
  obtain ⟨hv, hvp, hd, hbd, hmeas⟩ := stream_kernel_drift_data hcur a b
  exact weighted_kernel_rough_solution_buffer PP P hP π wgt hπ hBdata hCdata hSdata
    hb hbT hRad (streamVel (Φ m)) hv hvp (actualDriftJetConstant * ocA α q Λ m)
    1024 (ocEpsilon q Λ m) (mul_nonneg actualDriftJetConstant_nonneg ha.le)
    (by norm_num) he hsmall hstrain hd
    (fun t _ l hl _ x =>
      actual_stream_drift_arrays α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm t l hl x)
    hbd hmeas f u w y hsol
end

/-! A normalized rough material datum has a weight-independent kernel increment price. -/

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

theorem normalized_stream_material_increment {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ V)
    (i : ι) (ψ : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hpψ : IsZ2Periodic ψ) (hnorm : (∫ x in unitCube, ψ x ^ 2) = 1)
    (e : h i) (he : ‖e‖ = 1) (w : ∀ i, ℝ → TorusHk 1 (h i))
    (u : ∀ i, ℝ → TorusHk 0 (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => 0)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient
      (Pi.single i (materialInitialDatum hφ a ψ hψ hpψ e) : ∀ j, TorusHk 0 (h j))
      (P.carrierFlux w) (fun _ _ => 0) u w)
    (L : ℝ) (hL : 0 ≤ L)
    (hgrad : ∀ t ∈ Set.Icc a b, ‖torusH1GradientL2CLM (E := h i)
      (periodicMaterialHilbertTest hφ a ψ hψ hpψ e t)‖ ≤ L) :
    |inner ℝ (torusHkValueCLM (u i b))
        (torusHkValueCLM (periodicMaterialHilbertTest hφ a ψ hψ hpψ e b)) - 1| ≤
      L * ((1 + P.θ) * Real.sqrt ν * Real.sqrt (b - a)) := by
  classical
  have hd := stream_homogeneous_dissipation P hφ V hV hb _ w u hsol
  rw [materialInitialDatum_single_mass hφ a ψ hψ hpψ hnorm i e he ρ P.π] at hd
  have hi : inner ℝ (torusHkValueCLM (u i a))
      (torusHkValueCLM (periodicMaterialHilbertTest hφ a ψ hψ hpψ e a)) = 1 := by
    rw [hsol.2.2.2.1 i, Pi.single_eq_same]
    exact materialInitialDatum_pairing hφ a ψ hψ hpψ hnorm e he
  have hinc := kernel_material_increment_of_dissipation P hφ V hV hb _ w u hsol
    i ψ hψ hpψ e L hL hgrad hd
  rw [hi] at hinc
  have hθ := P.theta_nonneg_of_component i
  exact hinc.trans (mul_le_mul_of_nonneg_left
    (normalized_material_flux_price (P.hπ i) P.diffusivity_pos (by linarith only [hθ])) hL)

end TorusKernelOperator
end

/-! The literal normalized kernel evolution forces a wait whenever its prepared pairing is small. -/

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

theorem normalized_kernel_pairing_delay {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ V)
    (i : ι) (ψ : Vec 2 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hpψ : IsZ2Periodic ψ) (hnorm : (∫ x in unitCube, ψ x ^ 2) = 1)
    (e : h i) (he : ‖e‖ = 1) (w : ∀ i, ℝ → TorusHk 1 (h i))
    (u : ∀ i, ℝ → TorusHk 0 (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => 0)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient
      (Pi.single i (materialInitialDatum hφ a ψ hψ hpψ e) : ∀ j, TorusHk 0 (h j))
      (P.carrierFlux w) (fun _ _ => 0) u w)
    (L : ℝ) (hL : 0 ≤ L)
    (hgrad : ∀ t ∈ Set.Icc a b, ‖torusH1GradientL2CLM (E := h i)
      (periodicMaterialHilbertTest hφ a ψ hψ hpψ e t)‖ ≤ L)
    (prepared η A : ℝ)
    (happrox : |inner ℝ (torusHkValueCLM (u i b))
      (torusHkValueCLM (periodicMaterialHilbertTest hφ a ψ hψ hpψ e b)) - prepared| ≤ η)
    (hprepared : |prepared| ≤ A) (herrors : η + A ≤ 1 / 2)
    (hprice : L * (1 + P.θ) * ρ ≤ 1 / 4) : ρ ^ 2 / ν ≤ b - a := by
  have hθ := P.theta_nonneg_of_component i
  have hi := normalized_stream_material_increment P hφ V hV hb i ψ hψ hpψ hnorm
    e he w u hsol L hL hgrad
  have hinc : |inner ℝ (torusHkValueCLM (u i b))
      (torusHkValueCLM (periodicMaterialHilbertTest hφ a ψ hψ hpψ e b)) - 1| ≤
      (L * (1 + P.θ) * Real.sqrt ν) * Real.sqrt (b - a) :=
    hi.trans_eq (by ring)
  have hB : 0 ≤ L * (1 + P.θ) * Real.sqrt ν :=
    mul_nonneg (mul_nonneg hL (by linarith only [hθ])) (Real.sqrt_nonneg _)
  have hcost : (L * (1 + P.θ) * Real.sqrt ν) * Real.sqrt (ρ ^ 2 / ν) ≤ 1 / 4 := by
    calc
      _ = (L * (1 + P.θ)) * (Real.sqrt ν * Real.sqrt (ρ ^ 2 / ν)) := by ring
      _ = L * (1 + P.θ) * ρ := by
        rw [molecular_delay_sqrt_price P.diffusivity_pos P.radius_pos.le]
      _ ≤ _ := hprice
  exact scalar_pairing_forces_delay happrox hprepared hinc hB herrors hcost

end TorusKernelOperator
end

/-! A literal normalized Fourier evolution tests the common preparation's minimum delay. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem common_preparation_molecular_delay_test
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {cr Q CQ Cpr : ℝ} {p Nout Naux : ℕ} {s tf tp ρ : ℝ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ Cpr p Nout Naux s tf tp Preg)
    (hNout : 1 ≤ Nout) (htp : tp ≤ tf)
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) s tp ρ (D.κ G.level) 0 Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    (w : CompIn G.comps → ℝ) (hw : (w = fun _ => 1) ∨ w = G.marker law)
    (hπ : R.π = fun v => G.mass law v / w v ^ 2)
    (v : CompIn G.comps) (e : hr v.1.root) (he : ‖e‖ = 1)
    (hφ : IsAdmissibleStream (D.Φ G.level))
    (N : ℕ) (hN : 1 ≤ N) {Cfreq L : ℝ}
    (hCfreq : 0 < Cfreq) (hρEnh : 0 < rhoEnh D cr G.level)
    (hfreq : Cfreq / rhoEnh D cr G.level ≤ (N : ℝ))
    (hpreparedPrice : 8 * Real.sqrt 18 * CQ ≤ Cfreq)
    (herror : CQ * D.eps (G.level - 1) ^ Q ≤ 1 / 8)
    (hL : 0 ≤ L)
    (hDv : ∀ r x, ‖Infra.Flow.jointSpatialFDeriv (streamVel (D.Φ G.level)) r x‖ ≤ L)
    (hsmall : L * |tp - s| ≤ 1)
    (hmolecularPrice : (2 * Real.pi * (N : ℝ)) * ρ ≤ 1 / (32 * Real.sqrt 2))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ G.level)
      (streamVel (D.Φ G.level)) 0 s tf
      (Pi.single v (materialInitialDatum hφ s (axisCosine N hN)
        (axisCosine_smooth N hN) (axisCosine_periodic N hN) e) :
        ∀ u : CompIn G.comps, TorusHk 0 (hr u.1.root))
      (fun _ _ => 0) (fun _ _ => 0) U W Y) :
    ρ ^ 2 / D.κ G.level ≤ tp - s := by
  let ell := 2 * Real.pi * (N : ℝ)
  have hell : 0 < ell := mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (by exact_mod_cast hN)
  have hπw (u : CompIn G.comps) : 0 < G.mass law u / w u ^ 2 := by
    rw [← congrFun hπ u]
    exact R.hπ u
  have hX (x : Vec 2) : ‖fderiv ℝ (fun y => AVRegularity.streamFlow
      (D.Φ G.level) hφ tp y s) x‖ ≤ 3 :=
    short_time_flow_derivative_le_three (Infra.Construction.smoothPeriodic_streamVel hφ)
      (StrainPhysical.isFlow_stream hφ) hL hDv s tp hsmall x
  have hpairs := normalized_common_preparation_pairings law P seedK freshK φ₀ hφ₀ G
    Preg hprep hNout w hw hπw v e he hφ (axisCosine N hN) (axisSine N hN)
    (axisCosine_smooth N hN) (axisCosine_periodic N hN)
    (axisSine_smooth N hN) (axisSine_periodic N hN)
    (axisCosine_cell_square N hN) (axisSine_cell_square N hN) 0 hell hρEnh
    (axisSine_primitive N hN) hX U W Y hsol
  have hprepared := hpairs.2.trans (by
    simpa only [show (2 : ℝ) * 3 ^ 2 = 18 by norm_num] using
      prepared_fourier_pairing_price_le hρEnh hCfreq hfreq hpreparedPrice)
  have hs := native_reg_solution_end_restrict P seedK freshK φ₀ hφ₀ G htp
    (streamVel (D.Φ G.level)) _ U W Y hsol
  have hf := native_reg_solution_forced P seedK freshK φ₀ hφ₀ G R hB hC hS hφ _ U W Y hs
  have hgrad (t : ℝ) (ht : t ∈ Set.Icc s tp) :
      ‖CoupledEnergy.Variational.torusH1GradientL2CLM (E := hr v.1.root)
        (periodicMaterialHilbertTest hφ s (axisCosine N hN)
          (axisCosine_smooth N hN) (axisCosine_periodic N hN) e t)‖ ≤
        6 * (ell * Real.sqrt 2) := by
    have htime : L * |t - s| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      exact (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 s) hL).trans
        (by rwa [abs_of_nonneg (sub_nonneg.mpr R.htime)] at hsmall)
    have hb := short_time_material_gradient_le hφ s t (axisCosine N hN)
      (axisCosine_smooth N hN) (axisCosine_periodic N hN)
      (mul_nonneg hell.le (Real.sqrt_nonneg _)) hL (axisCosine_fderiv_norm_le N hN)
      hDv htime e
    exact hb.trans_eq (by rw [he, mul_one])
  obtain ⟨_hv, _hp, _hd, ⟨V, hV⟩, _hm⟩ := stream_kernel_drift_data hφ s tp
  apply TorusKernelOperator.normalized_kernel_pairing_delay R hφ (max V 0)
    (le_max_right _ _) (fun t ht x => (hV t ht x).trans (le_max_left _ _))
    v (axisCosine N hN) (axisCosine_smooth N hN) (axisCosine_periodic N hN)
    (axisCosine_cell_square N hN) e he W U hf (6 * (ell * Real.sqrt 2))
    (mul_nonneg (by norm_num) (mul_nonneg hell.le (Real.sqrt_nonneg _))) hgrad
    _ (CQ * D.eps (G.level - 1) ^ Q) (1 / 8)
  · exact (abs_sub_comm _ _).trans_le hpairs.1
  · exact hprepared
  · linarith only [herror]
  · exact molecular_fourier_increment_price_le hell.le R.radius_pos.le R.hθ hmolecularPrice
end

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual incoming regularized evolution has the molecular buffer after its delay. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_weighted_buffer_after_delay
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
    (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (δt : ℝ) (hδ : 0 < δt) (hδb : c + δt ≤ b)
    (hRad : (rhoStar D k.c₀ G.level) ^ 2 ≤ (5 * D.kap G.level / 4) * δt)
    (s : ℝ) (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2) (hqA : IsAdmissibleQ D.α s D.q)
    (hζ : IsFastProfile D.ζ) (hΦ : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (hsmall : 1024 * rhoStar D k.c₀ G.level / D.eps G.level ≤ 1 / 2)
    (hstrain : (actualDriftJetConstant * ocA D.α D.q D.Λ G.level) * 1024 *
      (rhoStar D k.c₀ G.level) ^ 2 ≤ D.kap G.level / 8)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.kap G.level)
      (AVenhance.streamVel (D.Φ G.level)) 0 c b f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk) :
    ∀ j ≤ K, ∀ t ∈ Set.Icc (c + δt) b,
    ∃ W : ∀ v : CompIn G.comps, TorusHk j (hr v.1.root),
      (∀ v, truncateTorusHk (Nat.zero_le j) (W v) = U v t) ∧
      weightedNorm (rhoStar D k.c₀ G.level) (G.mass law) w W ≤
        Real.sqrt (bufferEnergyCost j) * weightedNorm 1 (G.mass law) w f := by
  let PP := nativeKernelOperatorWindowFamily law P Mn seedK freshK φ₀ hφ₀ M k a b S θ seed G hI hseed hc hk hq hΛ hi hj hb hε hab hν hρ hρε hD hθ K hK w hw c hac hcb
  have hdata := native_kernel_window_family_data law P Mn seedK freshK φ₀ hφ₀ M k a b S θ seed G hI hseed hc hk hq hΛ hi hj hb hε hab hν hρ hρε hD hθ K hK w hw c hac hcb
  exact actual_stream_weighted_kernel_buffer PP (PP ⟨0, Nat.zero_lt_succ K⟩) rfl
    (G.mass law) w (fun j => (hdata j).1) (fun j => (hdata j).2.1)
    (fun j => (hdata j).2.2.1) (fun j => (hdata j).2.2.2)
    hδ hδb hRad D.α s hα₀ hα₁ hs₀ hs₁ D.q hqA D.ζ hζ D.Λ hΛ D.Φ hΦ G.level hi
    hsmall hstrain f U Uw Uk hsol

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Genuine rough-data existence makes the preparation delay test nonvacuous. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem common_preparation_molecular_delay
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {cr Q CQ Cpr : ℝ} {p Nout Naux : ℕ} {s tf tp ρ ν : ℝ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ Cpr p Nout Naux s tf tp Preg)
    (hNout : 1 ≤ Nout) (htp : tp ≤ tf)
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) s tf ρ ν 0 Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    (hν : ν = D.κ G.level)
    (w : CompIn G.comps → ℝ) (hw : (w = fun _ => 1) ∨ w = G.marker law)
    (hπ : R.π = fun v => G.mass law v / w v ^ 2)
    (v : CompIn G.comps) (e : hr v.1.root) (he : ‖e‖ = 1)
    (hφ : IsAdmissibleStream (D.Φ G.level))
    (N : ℕ) (hN : 1 ≤ N) {Cfreq L : ℝ}
    (hCfreq : 0 < Cfreq) (hρEnh : 0 < rhoEnh D cr G.level)
    (hfreq : Cfreq / rhoEnh D cr G.level ≤ (N : ℝ))
    (hpreparedPrice : 8 * Real.sqrt 18 * CQ ≤ Cfreq)
    (herror : CQ * D.eps (G.level - 1) ^ Q ≤ 1 / 8)
    (hL : 0 ≤ L)
    (hDv : ∀ r x, ‖Infra.Flow.jointSpatialFDeriv (streamVel (D.Φ G.level)) r x‖ ≤ L)
    (hflowcap : L * (ρ ^ 2 / ν) ≤ 1)
    (hmolecularPrice : (2 * Real.pi * (N : ℝ)) * ρ ≤ 1 / (32 * Real.sqrt 2))
    : ρ ^ 2 / ν ≤ tp - s := by
  subst ν
  by_contra! htime
  have hstp : s ≤ tp := hprep.2.1
  have hsub : Set.Icc s tp ⊆ Set.Icc s tf := Set.Icc_subset_Icc le_rfl htp
  let Rt := kernelOperator_time_restrict R hsub hstp
  let f := (Pi.single v (materialInitialDatum hφ s (axisCosine N hN)
    (axisCosine_smooth N hN) (axisCosine_periodic N hN) e) :
    ∀ u : CompIn G.comps, TorusHk 0 (hr u.1.root))
  obtain ⟨U, W, Y, hsol⟩ := native_kernel_order_zero_exists P seedK freshK φ₀ hφ₀ G
    R hB hC hS hφ f
  have hsmall : L * |tp - s| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hstp)]
    exact (mul_le_mul_of_nonneg_left htime.le hL).trans hflowcap
  have hdelay := common_preparation_molecular_delay_test law P seedK freshK φ₀ hφ₀ G
    Preg hprep hNout htp Rt hB hC hS w hw hπ v e he hφ N hN
    hCfreq hρEnh hfreq hpreparedPrice herror hL hDv hsmall hmolecularPrice U W Y hsol
  exact (not_lt_of_ge hdelay) htime

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! The literal invariant operator and genuine rough-data existence force the preparation delay. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_common_preparation_delay
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
    (hθ : θ ≤ 1 / 8)
    (w : CompIn G.comps → ℝ) (hw : (w = fun _ => 1) ∨ w = G.marker law)
    (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (hκ : D.kap G.level = D.κ G.level)
    {cr Q CQ Cpr : ℝ} {p Nout Naux : ℕ} {tp : ℝ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ Cpr p Nout Naux c b tp Preg)
    (hNout : 1 ≤ Nout) (htp : tp ≤ b)
    (v : CompIn G.comps) (e : hr v.1.root) (he : ‖e‖ = 1)
    (hφ : AVenhance.IsAdmissibleStream (D.Φ G.level))
    (N : ℕ) (hN : 1 ≤ N) {Cfreq L : ℝ}
    (hCfreq : 0 < Cfreq) (hρEnh : 0 < rhoEnh D cr G.level)
    (hfreq : Cfreq / rhoEnh D cr G.level ≤ (N : ℝ))
    (hpreparedPrice : 8 * Real.sqrt 18 * CQ ≤ Cfreq)
    (herror : CQ * D.eps (G.level - 1) ^ Q ≤ 1 / 8)
    (hL : 0 ≤ L)
    (hDv : ∀ r x, ‖AVenhance.Infra.Flow.jointSpatialFDeriv
      (AVenhance.streamVel (D.Φ G.level)) r x‖ ≤ L)
    (hflowcap : L * ((rhoStar D k.c₀ G.level) ^ 2 / D.kap G.level) ≤ 1)
    (hmolecularPrice : (2 * Real.pi * (N : ℝ)) * rhoStar D k.c₀ G.level ≤
      1 / (32 * Real.sqrt 2)) :
    (rhoStar D k.c₀ G.level) ^ 2 / D.kap G.level ≤ tp - c := by
  let R := nativeInvariantKernelOperator law P Mn seedK freshK φ₀ hφ₀ M k a b S θ
    seed G hI hseed hc hk hq hΛ hi hj hb hε hab hν hρ hρε hD hθ 0 (Nat.zero_le _) w hw
  let Rc := kernelOperator_time_restrict R (Set.Icc_subset_Icc hac le_rfl) hcb
  have hd := native_kernel_operator_data law P Mn seedK freshK φ₀ hφ₀ M k a b S θ
    seed G hI hseed hc hk hq hΛ hi hj hb hε hab hν hρ hρε hD hθ 0 (Nat.zero_le _) w hw
  exact common_preparation_molecular_delay law P seedK freshK φ₀ hφ₀ G
    Preg hprep hNout htp Rc hd.2.1 hd.2.2.1 hd.2.2.2 hκ w hw hd.1 v e he hφ N hN
    hCfreq hρEnh hfreq hpreparedPrice herror hL hDv hflowcap hmolecularPrice
end

/-! The literal invariant operator and genuine rough-data existence force the preparation delay. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_common_preparation_buffer
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
    (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (hκ : D.kap G.level = D.κ G.level)
    {cr Q CQ Cpr : ℝ} {p Nout Naux : ℕ} {tp : ℝ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ Cpr p Nout Naux c b tp Preg)
    (hNout : 1 ≤ Nout) (htp : tp ≤ b)
    (v : CompIn G.comps) (e : hr v.1.root) (he : ‖e‖ = 1)
    (hφ : AVenhance.IsAdmissibleStream (D.Φ G.level))
    (N : ℕ) (hN : 1 ≤ N) {Cfreq L : ℝ}
    (hCfreq : 0 < Cfreq) (hρEnh : 0 < rhoEnh D cr G.level)
    (hfreq : Cfreq / rhoEnh D cr G.level ≤ (N : ℝ))
    (hpreparedPrice : 8 * Real.sqrt 18 * CQ ≤ Cfreq)
    (herror : CQ * D.eps (G.level - 1) ^ Q ≤ 1 / 8)
    (hL : 0 ≤ L)
    (hDv : ∀ r x, ‖AVenhance.Infra.Flow.jointSpatialFDeriv
      (AVenhance.streamVel (D.Φ G.level)) r x‖ ≤ L)
    (hflowcap : L * ((rhoStar D k.c₀ G.level) ^ 2 / D.kap G.level) ≤ 1)
    (hmolecularPrice : (2 * Real.pi * (N : ℝ)) * rhoStar D k.c₀ G.level ≤
      1 / (32 * Real.sqrt 2))
    (slow : ℝ) (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3)
    (hs₀ : 0 < slow) (hs₁ : slow < (1 - D.α) / 2) (hqA : IsAdmissibleQ D.α slow D.q)
    (hζ : IsFastProfile D.ζ) (hΦ : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (hsmall : 1024 * rhoStar D k.c₀ G.level / D.eps G.level ≤ 1 / 2)
    (hstrain : (actualDriftJetConstant * ocA D.α D.q D.Λ G.level) * 1024 *
      (rhoStar D k.c₀ G.level) ^ 2 ≤ D.kap G.level / 8)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.kap G.level)
      (AVenhance.streamVel (D.Φ G.level)) 0 c b f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk) :
    ∀ j ≤ K, ∀ t ∈ Set.Icc tp b,
    ∃ W : ∀ v : CompIn G.comps, TorusHk j (hr v.1.root),
      (∀ v, truncateTorusHk (Nat.zero_le j) (W v) = U v t) ∧
      weightedNorm (rhoStar D k.c₀ G.level) (G.mass law) w W ≤
        Real.sqrt (bufferEnergyCost j) * weightedNorm 1 (G.mass law) w f := by
  have hdelay := native_common_preparation_delay law P Mn seedK freshK φ₀ hφ₀ M k
    a b S θ seed G hI hseed hc hk hq hΛ hi hj hb hε hab hν hρ hρε hD hθ
    w hw c hac hcb hκ Preg hprep hNout htp v e he hφ N hN hCfreq hρEnh hfreq
    hpreparedPrice herror hL hDv hflowcap hmolecularPrice
  let δt := (rhoStar D k.c₀ G.level) ^ 2 / D.kap G.level
  have hd := molecular_delay_energy hρ hν
  have hstart : c + δt ≤ tp := by linarith only [hdelay]
  have hδb : c + δt ≤ b := hstart.trans htp
  have hbuffer := native_weighted_buffer_after_delay law P Mn seedK freshK φ₀ hφ₀ M k
    a b S θ seed G hI hseed hc hk hq hΛ hi hj hb hε hab hν hρ hρε hD hθ K hK
    w hw c hac hcb δt hd.1 hδb hd.2 slow hα₀ hα₁ hs₀ hs₁ hqA hζ hΦ hsmall hstrain
    f U Uw Uk hsol
  intro j hj t ht
  exact hbuffer j hj t ⟨hstart.trans ht.1, ht.2⟩
end

/-! The literal invariant operator and genuine rough-data existence force the preparation delay. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_common_preparation_buffer_small_radii
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
    (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (hκ : D.kap G.level = D.κ G.level)
    {cr Q CQ Cpr : ℝ} {p Nout Naux : ℕ} {tp : ℝ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ Cpr p Nout Naux c b tp Preg)
    (hNout : 1 ≤ Nout) (htp : tp ≤ b)
    {L : ℝ} (hρEnh : 0 < rhoEnh D cr G.level)
    (hsize : rhoStar D k.c₀ G.level ≤ (1 / (32 * Real.sqrt 2)) /
      (2 * Real.pi * (8 * Real.sqrt 18 * (|CQ| + 1) + 1)))
    (hratio : rhoStar D k.c₀ G.level / rhoEnh D cr G.level ≤ (1 / (32 * Real.sqrt 2)) /
      (2 * Real.pi * (8 * Real.sqrt 18 * (|CQ| + 1) + 1)))
    (herror : CQ * D.eps (G.level - 1) ^ Q ≤ 1 / 8)
    (hL : 0 ≤ L)
    (hDv : ∀ r x, ‖AVenhance.Infra.Flow.jointSpatialFDeriv
      (AVenhance.streamVel (D.Φ G.level)) r x‖ ≤ L)
    (hflowcap : L * ((rhoStar D k.c₀ G.level) ^ 2 / D.kap G.level) ≤ 1)
    (slow : ℝ) (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3)
    (hs₀ : 0 < slow) (hs₁ : slow < (1 - D.α) / 2) (hqA : IsAdmissibleQ D.α slow D.q)
    (hζ : IsFastProfile D.ζ) (hΦ : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (hsmall : 1024 * rhoStar D k.c₀ G.level / D.eps G.level ≤ 1 / 2)
    (hstrain : (actualDriftJetConstant * ocA D.α D.q D.Λ G.level) * 1024 *
      (rhoStar D k.c₀ G.level) ^ 2 ≤ D.kap G.level / 8)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.kap G.level)
      (AVenhance.streamVel (D.Φ G.level)) 0 c b f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk) :
    ∀ j ≤ K, ∀ t ∈ Set.Icc tp b,
    ∃ W : ∀ v : CompIn G.comps, TorusHk j (hr v.1.root),
      (∀ v, truncateTorusHk (Nat.zero_le j) (W v) = U v t) ∧
      weightedNorm (rhoStar D k.c₀ G.level) (G.mass law) w W ≤
        Real.sqrt (bufferEnergyCost j) * weightedNorm 1 (G.mass law) w f := by
  rcases component_hilbert_dichotomy (hr := hr) G.comps with hzero | ⟨v, e, he⟩
  · intro j hj t ht
    obtain ⟨W, hW, hnorm⟩ := subsingleton_carrier_buffer hzero j
      (rhoStar D k.c₀ G.level) (G.mass law) w (fun u => U u t)
    refine ⟨W, hW, ?_⟩
    rw [hnorm]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · have hCfreq := prepared_fourier_choice_constant CQ
    obtain ⟨N, hN, hfreq, _hupper, hmolecularPrice⟩ :=
      exists_fourier_integer_with_radius_price hCfreq.1 hρEnh hρ.le hratio hsize
    have hφ := AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ G.level
    exact native_common_preparation_buffer law P Mn seedK freshK φ₀ hφ₀ M k
      a b S θ seed G hI hseed hc hk hq hΛ hi hj hb hε hab hν hρ hρε hD hθ K hK
      w hw c hac hcb hκ Preg hprep hNout htp v e he hφ N hN hCfreq.1 hρEnh hfreq
      hCfreq.2 herror hL hDv hflowcap hmolecularPrice
      slow hα₀ hα₁ hs₀ hs₁ hqA hζ hΦ hsmall hstrain f U Uw Uk hsol
end

/-! The literal invariant operator and genuine rough-data existence force the preparation delay. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem preparation_buffer_from_scalar_budget
    (law : BirthLaw) (P : ProvParams) (Mn : SuccMenu) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (k : InvConsts)
    (a b S θ : ℝ) (seed G : GenStage D hr Dm bw j₀)
    (hI : IsStageInvariant law P seedK freshK φ₀ hφ₀ M k a b S θ G)
    (hseed : ∀ v : CompIn seed.comps, v.1.births = []) (hc : IsCascadeStage D P Mn seed G)
    (hk : k.Hprod = k.G0 + Mn.H + 1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hab : a ≤ b) (hterminal : G.level ≤ D.term) (hD : 2 ≤ Dm)
    (K : ℕ) (hK : K ≤ k.Ks)
    (w : CompIn G.comps → ℝ) (hw : (w = fun _ => 1) ∨ w = G.marker law)
    (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    {cr Q CQ Cpr : ℝ} {p Nout Naux : ℕ} {tp : ℝ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ Cpr p Nout Naux c b tp Preg)
    (hNout : 1 ≤ Nout) (htp : tp ≤ b)
    {CI τ : ℝ}
    (hbudget : PreparationScalarBudget (D.eps (G.level - 1)) (D.eps G.level)
      (D.κ G.level) (ocA D.α D.q D.Λ G.level) (rhoStar D k.c₀ G.level)
      (rhoEnh D cr G.level) CQ CI Q τ)
    (hθeq : θ = CI * D.eps (G.level - 1) ^ τ)
    (slow : ℝ) (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3)
    (hs₀ : 0 < slow) (hs₁ : slow < (1 - D.α) / 2) (hqA : IsAdmissibleQ D.α slow D.q)
    (hζ : IsFastProfile D.ζ) (hΦ : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.kap G.level)
      (AVenhance.streamVel (D.Φ G.level)) 0 c b f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk) :
    ∀ j ≤ K, ∀ t ∈ Set.Icc tp b,
    ∃ W : ∀ v : CompIn G.comps, TorusHk j (hr v.1.root),
      (∀ v, truncateTorusHk (Nat.zero_le j) (W v) = U v t) ∧
      weightedNorm (rhoStar D k.c₀ G.level) (G.mass law) w W ≤
        Real.sqrt (bufferEnergyCost j) * weightedNorm 1 (G.mass law) w f := by
  have hκ : D.kap G.level = D.κ G.level := by
    simp only [OCData.kap, Nat.min_eq_left hterminal]
  have hν : 0 < D.kap G.level := by rw [hκ]; exact hbudget.diffusivity_pos
  have hθ : θ ≤ 1 / 8 := by rw [hθeq]; exact hbudget.kernel_small
  have he := (Scales.epsilon_basic (m := G.level) hq hΛ).1
  have ha : 0 < ocA D.α D.q D.Λ G.level := Real.rpow_pos_of_pos he _
  have hL : 0 ≤ 1048576 * ocA D.α D.q D.Λ G.level := mul_nonneg (by norm_num) ha.le
  have hDv := actual_stream_spatial_derivative_bound D.α slow hα₀ hα₁ hs₀ hs₁ D.q hqA
    D.ζ hζ D.Λ hΛ D.Φ hΦ G.level hi
  exact native_common_preparation_buffer_small_radii law P Mn seedK freshK φ₀ hφ₀ M k
    a b S θ seed G hI hseed hc hk hq hΛ hi hj hb hbudget.parent_pos hab hν
    hbudget.radius_pos hbudget.radius_le_parent hD hθ K hK
    w hw c hac hcb hκ Preg hprep hNout htp hbudget.enhanced_pos
    hbudget.radius_small hbudget.radius_ratio_small hbudget.error_small hL hDv
    (by simpa only [hκ] using hbudget.flow_small)
    slow hα₀ hα₁ hs₀ hs₁ hqA hζ hΦ hbudget.drift_small
    (by simpa only [hκ] using hbudget.strain_small) f U Uw Uk hsol
end

end AVRegularity.Construction.Preservation.Buffer
end
