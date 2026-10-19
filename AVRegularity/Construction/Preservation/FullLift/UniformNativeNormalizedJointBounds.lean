-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
import AVRegularity.KernelEnergy.TorusKernelStrongTraceExistence
import AVRegularity.KernelEnergy.TorusKernelComponentSup
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
public import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
public import AVRegularity.EntryWeak.IndependentParameterNormContinuity
public import AVRegularity.KernelEnergy.TorusKernelFiniteTraceLimit
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import Mathlib.Analysis.Complex.OperatorNorm

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Uniform fresh constants, enlarged with the seed constants, certify every actual
cascade kernel. The derivative order and time window are arbitrary. -/

/-- K4: fresh regularizers and the seed certificates give uniform inherited regularization. -/
theorem uniform_cascade_kernel_regularizers
    (φ₀ : Vec 2 → ℝ) (hc : HasCompactSupport φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφ₀ : Integrable φ₀) (nk : ℕ+)
    (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ cf : ℕ → ℝ, (∀ j, 0 ≤ cf j) ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (P : ProvParams) (Mn : SuccMenu)
      (law : BirthLaw) (seedK freshK : ℕ → KernelSpec) (kS : InvConsts)
      (cr σ₀ : ℝ), 0 < cr →
      (∀ l, 1 ≤ l → l < D.term → IsFreshKernel D cr σ₀ nk l (freshK l)) →
    ∀ (M : ℕ) (seed G : GenStage D hr Dm bw j₀) (tS tf Sbound θK : ℝ),
      seed.level < D.term →
      IsStageInvariant law P seedK freshK φ₀ hφ₀ M kS tS tf Sbound θK seed →
      IsCascadeStage D P Mn seed G → m₀ ≤ G.level →
    ∀ (C : ℕ → ℝ), (∀ j, j + 2 ≤ Dm → kS.cker j ≤ C j ∧ cf j ≤ C j) →
    ∀ a b : ℝ, Set.Icc a b ⊆ Set.Icc tS tf →
    ∀ v u (γ : G.fam.Γ v u), ∀ ρ : ℝ, 0 < ρ → ∀ k, k ≤ kS.Ks →
      IsSpatialRegularizerTorus ρ k Dm a b C (G.kernelOf P seedK freshK v u γ).width
        (G.sysS P seedK freshK φ₀ hφ₀ v u γ) := by
  obtain ⟨cf, hcf, m₀, hm₀, hf⟩ := uniform_fresh_kernel_regularizer
    φ₀ hc hd nk α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ Λ hΛ
  refine ⟨cf, hcf, m₀, hm₀, ?_⟩
  intro hr _ _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq hband Dm bw j₀ P Mn law
    seedK freshK kS cr σ₀ hcr hfresh M seed G tS tf Sbound θK hseedterm hseed hcascade
    hlevel C hC a b hwindow
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  apply cascade_kernel_regularizers_of_seed_invariant P Mn seed G hcascade law
    seedK freshK φ₀ hφ₀ M kS tS tf Sbound θK hseed a b hwindow C
    (fun j hj => (hC j hj).1) m₀ hlevel
  intro l hl hs ρ _ k _
  have hlt : l < D.term := hs.trans hseedterm
  have hspec := hfresh l (hm₀.trans hl |>.trans' (by decide : 1 ≤ 2)) hlt
  have hκ : 0 < D.κ l := CycleReference.bandChain_pos hΛD hζD hband hlt.le
  have hwidth : 0 < (freshK l).width := by
    rw [hspec.1]
    unfold freshWidth freshLength
    exact mul_pos (mul_pos hcr (Real.sqrt_pos.2
      (mul_pos hκ (Construction.Stream.ocTauPP_pos hΛD))))
      (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛD) _)
  have hreg := hf ℝ D hDα hDq hDΛ hDζ hseq hband l (by omega) (by omega)
    (freshK l) hspec.2.1 hwidth hspec.2.2 ρ a b k Dm
  exact spatial_regularizer_constants_mono hreg hwidth.le (fun j hj => (hC j hj).2)

/-! Choose compatible classical covariance gradients on a window and inherit time measurability. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem smooth_classical_gradient_window_exists {K : ℕ} (a b : ℝ)
    (W : ℝ → TorusHk K E) (f : ℝ → Vec 2 → E)
    (hW : ∀ t ∈ Set.Icc a b, IsClassicalRep (W t) (f t) K)
    (hf : ∀ t ∈ Set.Icc a b, ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (f t)) :
    ∃ Ww : ℝ → TorusHk (K + 1) E, ∀ t ∈ Set.Icc a b,
      IsClassicalRep (Ww t) (f t) (K + 1) ∧ truncateTorusHk (Nat.le_succ K) (Ww t) = W t := by
  classical
  have hex : ∀ t : Set.Icc a b, ∃ Ww : TorusHk (K + 1) E,
      IsClassicalRep Ww (f t) (K + 1) ∧ truncateTorusHk (Nat.le_succ K) Ww = W t :=
    fun t => smooth_classical_gradient_carrier_exists (W t) (f t) (hW t t.2) (hf t t.2)
  choose V hV using hex
  refine ⟨fun t => if ht : t ∈ Set.Icc a b then V ⟨t, ht⟩ else 0, ?_⟩
  intro t ht
  simpa only [ht, ↓reduceDIte] using hV ⟨t, ht⟩

theorem smooth_covImage_gradient_window_exists {K p : ℕ} (a b : ℝ)
    (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, ContinuousOn (fun t => Hc t i j) (Set.Icc a b))
    (Z : ℝ → TorusHk (K + 2 * p) E) (Zw : ℝ → TorusHk (K + 2 * p + 1) E)
    (W : ℝ → TorusHk K E) (f : ℝ → Vec 2 → E)
    (hW : ∀ t ∈ Set.Icc a b, IsClassicalRep (W t) (f t) K)
    (hf : ∀ t ∈ Set.Icc a b, ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (f t))
    (hZw : AEStronglyMeasurable Zw (volume.restrict (Set.Icc a b)))
    (hcompat : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncateTorusHk (Nat.le_succ (K + 2 * p)) (Zw t) = Z t)
    (hcov : ∀ t ∈ Set.Icc a b, IsCovImage (covPolyP (Hc t) p) (Z t) (W t)) :
    ∃ Ww : ℝ → TorusHk (K + 1) E,
      (∀ t ∈ Set.Icc a b, IsClassicalRep (Ww t) (f t) (K + 1) ∧
        truncateTorusHk (Nat.le_succ K) (Ww t) = W t) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), IsCovImage (covPolyP (Hc t) p) (Zw t) (Ww t)) ∧
      AEStronglyMeasurable Ww (volume.restrict (Set.Icc a b)) := by
  obtain ⟨Ww, hWw⟩ := smooth_classical_gradient_window_exists a b W f hW hf
  have hc : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      IsCovImage (covPolyP (Hc t) p) (Zw t) (Ww t) := by
    filter_upwards [hcompat, ae_restrict_mem measurableSet_Icc] with t ht hmem
    exact covImage_of_compatible_carriers (Nat.le_succ (K + 2 * p)) (Nat.le_succ K)
      (covPolyP (Hc t) p) (Z t) (Zw t) (W t) (Ww t) ht (hWw t hmem).2 (hcov t hmem)
  exact ⟨Ww, hWw, hc, covImage_aestronglyMeasurable_of_reserve (by omega)
    a b Hc hH Zw Ww hZw hc⟩
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
section
/-! Copy-adapt the order-zero native carrier-flux conversion at every allocated Sobolev order. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_forced_at_order (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν k Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y) :
    IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => k)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient f
      (R.carrierFlux W) (fun _ _ => 0) U W := by
  have hs : IsKernelWeakSolutionTorus ν a b (streamVel φ) k Dm R.B R.C R.S f
      (fun _ _ => 0) (fun _ _ => 0) U W Y := by
    simpa only [hB, hC, hS, GenStage.IsRegSolution] using hsol
  obtain ⟨hv, _hp, _hd, ⟨V, hV⟩, _hm⟩ := Buffer.stream_kernel_drift_data hφ a b
  have hf := R.kernelWeakSolution_forcedWeakSolution (streamVel φ) hv (max V 0)
    (le_max_right _ _) (fun t ht x => (hV t ht x).trans (le_max_left _ _))
    f (fun _ _ => 0) (fun _ _ => 0) U W Y hs
  simpa only [zero_add] using hf

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Native homogeneous kernel solution uniqueness with the literal operator identities. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_unique (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν k Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U U' : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W W' : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y Y' : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y)
    (hsol' : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
      (fun _ _ => 0) (fun _ _ => 0) U' W' Y') :
    ∀ v, ∀ t ∈ Set.Icc a b, U v t = U' v t := by
  classical
  have hforced := native_reg_solution_forced_at_order P seedK freshK φ₀ hφ₀ G R hB hC hS hφ
    f U W Y hsol
  have hforced' := native_reg_solution_forced_at_order P seedK freshK φ₀ hφ₀ G R hB hC hS hφ
    f U' W' Y' hsol'
  obtain ⟨hv, hp, hd, ⟨V, hV⟩, hm⟩ := Buffer.stream_kernel_drift_data hφ a b
  have hV0 : 0 ≤ max V 0 := le_max_right _ _
  have hbV : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ max V 0 :=
    fun t ht x => (hV t ht x).trans (le_max_left _ _)
  apply KernelEnergy.TorusKernelOperator.kernelForcedWeakSolution_unique R (streamVel φ) hv hp
    (fun _ _ => 0) (fun _ _ => 0) α B lam hα hBdrift hlam hsmall hstrain hd hjets hm
    (max V 0) hV0 hbV (fun _ => driftCarrierBudget k (max V 0) α B lam)
    (fun t ht _ => driftCarrierBudget_bounds k (streamVel φ t) (max V 0) α B lam hV0
      (hbV t ht) (hjets t ht)) W W' U U' f
    (fun _ => timeMemLp_zero _ 2) (fun _ => timeIntegrable_zero _)
  · simpa only [zero_add] using hforced
  · simpa only [zero_add] using hforced'

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Order-zero native uniqueness identifies complete higher-order Sobolev carriers. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_unique_from_zero (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν 0 Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U U' : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W W' : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y Y' : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y)
    (hsol' : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
      (fun _ _ => 0) (fun _ _ => 0) U' W' Y') :
    ∀ v, ∀ t ∈ Set.Icc a b, U v t = U' v t := by
  have h0k : 0 ≤ k := Nat.zero_le k
  have ht := native_reg_solution_truncate P seedK freshK φ₀ hφ₀ G ν a b (streamVel φ)
    0 k h0k f U W Y hsol
  have ht' := native_reg_solution_truncate P seedK freshK φ₀ hφ₀ G ν a b (streamVel φ)
    0 k h0k f U' W' Y' hsol'
  have heq := native_reg_solution_unique P seedK freshK φ₀ hφ₀ G R hB hC hS hφ
    α B lam hα hBdrift hlam hsmall hstrain (fun _ _ l hl hl0 _ => by omega)
    (fun v => truncateTorusHk h0k (f v))
    (fun v t => truncateTorusHk h0k (U v t))
    (fun v t => truncateTorusHk h0k (U' v t))
    (fun v t => truncateTorusHk (Nat.succ_le_succ h0k) (W v t))
    (fun v t => truncateTorusHk (Nat.succ_le_succ h0k) (W' v t))
    (fun v u γ t => truncateTorusHk (by omega : 0 + Dm - 1 ≤ k + Dm - 1) (Y v u γ t))
    (fun v u γ t => truncateTorusHk (by omega : 0 + Dm - 1 ≤ k + Dm - 1) (Y' v u γ t))
    ht ht'
  intro v t htime
  apply TorusHk.ext_value
  exact congrArg (fun z : TorusHk 0 (hr v.1.root) => z.val (valueIndex2 0)) (heq v t htime)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The specified native solution agrees pointwise with every higher-order solution of its full trace. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_eq_higher_truncate_from_zero (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν 0 Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y)
    {l : ℕ} (hkl : k ≤ l)
    (fhi : ∀ v : CompIn G.comps, TorusHk l (hr v.1.root))
    (Uhi : ∀ v : CompIn G.comps, ℝ → TorusHk l (hr v.1.root))
    (Whi : ∀ v : CompIn G.comps, ℝ → TorusHk (l + 1) (hr v.1.root))
    (Yhi : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (l + Dm - 1) (hr u.1.root))
    (hsolHi : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) l a b fhi
      (fun _ _ => 0) (fun _ _ => 0) Uhi Whi Yhi)
    (hinit : ∀ v, truncateTorusHk hkl (fhi v) = f v) :
    ∀ v, ∀ t ∈ Set.Icc a b, U v t = truncateTorusHk hkl (Uhi v t) := by
  have ht := native_reg_solution_truncate P seedK freshK φ₀ hφ₀ G ν a b (streamVel φ)
    k l hkl fhi Uhi Whi Yhi hsolHi
  have ht' := native_reg_solution_initial_congr P seedK freshK φ₀ hφ₀ G ν a b
    (streamVel φ) k (fun v => truncateTorusHk hkl (fhi v)) f
    (fun v t => truncateTorusHk hkl (Uhi v t))
    (fun v t => truncateTorusHk (Nat.succ_le_succ hkl) (Whi v t))
    (fun v u γ t => truncateTorusHk (by omega : k + Dm - 1 ≤ l + Dm - 1) (Yhi v u γ t))
    hinit ht
  exact native_reg_solution_unique_from_zero P seedK freshK φ₀ hφ₀ G R hB hC hS hφ
    α B lam hα hBdrift hlam hsmall hstrain f U
    (fun v t => truncateTorusHk hkl (Uhi v t)) W
    (fun v t => truncateTorusHk (Nat.succ_le_succ hkl) (Whi v t)) Y
    (fun v u γ t => truncateTorusHk (by omega : k + Dm - 1 ≤ l + Dm - 1) (Yhi v u γ t))
    hsol ht'

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! A native stage solution satisfies the literal strong-energy estimate when supplied with
its compiled kernel operator and the analytic drift prices. These are explicit
hypotheses of the statement. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_strongEnergy (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν k Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y) :
    strongEnergy ρ ν R.π a b U W ≤
      ENNReal.ofReal (Real.sqrt (2 * massNormSq ρ R.π (fun v => (f v).val))) := by
  have hforced := native_reg_solution_forced_at_order P seedK freshK φ₀ hφ₀ G R hB hC hS hφ
    f U W Y hsol
  have hforced' : IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => k)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient f
      (fun v t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) + R.carrierFlux W v t)
      (fun _ _ => 0) U W := by
    simpa only [zero_add] using hforced
  obtain ⟨hv, hp, hd, ⟨V, hV⟩, hm⟩ := Buffer.stream_kernel_drift_data hφ a b
  have hV0 : 0 ≤ max V 0 := le_max_right _ _
  have hbV : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ max V 0 :=
    fun t ht x => (hV t ht x).trans (le_max_left _ _)
  exact TorusKernelOperator.kernelForcedWeakSolution_strongEnergy R (streamVel φ) hv hp α B lam hα hBdrift hlam
    hsmall hstrain hd hjets hm (max V 0) hV0 hbV
    (fun _ => driftCarrierBudget k (max V 0) α B lam)
    (fun t ht _ => driftCarrierBudget_bounds k (streamVel φ t) (max V 0) α B lam hV0
      (hbV t ht) (hjets t ht)) W U f hforced'

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The native bounded Cauchy certificate gives independent joint slow-fast regularity at every finite order. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem contextCertified_native_flux_joint_coordinates_contDiff
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} (hG : G.IsContextCertified k)
    (hpar : G.IsSlotTransverse) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2) (n : ℕ) :
    ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
      ContDiff ℝ (n : ℕ∞) (fun X : Vec (2 + 2) =>
        G.fam.flux p (nativeStageContext G hi hj p
          (EntryWeakProofs.independentIntrinsicSlowProjection 2 X)) v u γ d I t 0
          (EntryWeakProofs.independentStoredParameterProjection 2 X) c) := by
  obtain ⟨θ, f, F, hθ, hHol, hsize, hsem, hbound⟩ :=
    contextCertified_exists_native_complex_bound hG hi hj hb hε p v u γ d I c hm hm2
  let S := (1 + compReserve k v.1 / 4) * (1 / 100) * D.eps (G.level - 1)
  let T := (1 + (2 : ℝ) / 4) * (1 / 100) * D.eps (G.level - 1)
  have hS : 0 < S := by dsimp [S]; positivity
  have hST : S ≤ T := by
    dsimp [S, T]
    apply mul_le_mul_of_nonneg_right _ hε.le
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith only [hm2]
  let A : ℕ → ℝ := fun j => ((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * bw)) ^ j) *
    ‖(ContinuousLinearMap.proj (transverseIndex p.1) : Vec 2 →L[ℝ] ℝ)‖ ^ j
  have hA (j : ℕ) : 0 ≤ A j := by dsimp [A]; positivity
  intro t ht
  apply contDiff_iff_contDiffAt.mpr
  intro W0
  let Lslow := EntryWeakProofs.independentIntrinsicSlowProjection 2
  let Lfast := EntryWeakProofs.independentStoredParameterProjection 2
  let Y := Lslow W0
  let z := Lfast W0
  let Fb : (Fin 2 → ℂ) → Vec 2 → ℂ := fun Z z => F p ⟨G.level - 1, [p.1]⟩ 0 t
    (Z, (fun a : Fin 0 => Fin.elim0 a), (fun a => (z a : ℂ)))
  have hd (z : Vec 2) : DifferentiableOn ℂ (fun Z => Fb Z z)
      {Z | (∑ a, |(Z a).im|) < T} :=
    native_holomorphic_base_slice D bw hb j₀ G.level p.1 f (F p) hHol t ht
      (fun a => (z a : ℂ)) (fun _ => Complex.ofReal_im _)
  have hfast (Z : Fin 2 → ℂ) (hZ : (∑ a, |(Z a).im|) < S) (z : Vec 2) :=
    native_complex_fast_affine_regular_and_jets G hi hj hb hε hpar p v u γ d I c f F hHol
      t ht (fun ctx X z => hsem ctx t ht X z) (compReserve k v.1) hm hm2 k.Lstar θ hθ hsize
      Z hZ z 1 n
  have hreg := base_fast_joint_regular S T hS hST n Lslow Lfast A hA Fb hd
    (fun Z hZ z => by simpa only [one_smul] using (hfast Z hZ z).1) θ hθ
    (fun Z hZ z => hbound t ht z Z hZ)
    (fun Z hZ z => by simpa only [one_smul, A] using (hfast Z hZ z).2) Y z
  let sf : Vec (2 + 2) → ℝ := fun X =>
    G.fam.flux p (nativeStageContext G hi hj p (Lslow X)) v u γ d I t 0 (Lfast X) c
  let H : Vec (2 + 2) → ℂ := fun X => Fb (fun a => ((Y + Lslow X) a : ℂ)) (z + Lfast X)
  have he : (fun X : Vec (2 + 2) => sf (W0 + X)) = Complex.reCLM ∘ H := by
    funext X
    have hh := native_flux_holomorphic_realization G hi hj p v u γ d I c f (F p) hHol t ht
      (fun ctx X z => hsem ctx t ht X z) (Y + Lslow X) (z + Lfast X)
    have hh' : H X = (sf (W0 + X) : ℂ) := by
      simpa only [sf, Fb, H, Y, z, map_add] using hh
    exact (congrArg Complex.re hh').symm
  have hreal : ContDiffAt ℝ (n : ℕ∞) (fun X : Vec (2 + 2) => sf (W0 + X)) 0 := by
    rw [he]
    exact Complex.reCLM.contDiff.contDiffAt.comp (f := H) 0 hreg
  have hreal' : ContDiffAt ℝ (n : ℕ∞) (fun X : Vec (2 + 2) => sf (W0 + X)) (W0 - W0) := by
    rw [sub_self]
    exact hreal
  have hsub : ContDiffAt ℝ (n : ℕ∞) (fun X : Vec (2 + 2) => X - W0) W0 :=
    contDiffAt_id.sub contDiffAt_const
  have hh := hreal'.comp (f := fun X : Vec (2 + 2) => X - W0) W0 hsub
  simpa only [Function.comp_def, ← add_sub_assoc, add_sub_cancel_left] using hh

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The native kernel estimate in either actual diagonal weight, bounded by its initial norm. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_strongEnergy_of_initial_norm (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀) (law : BirthLaw)
    {a b ρ ν : ℝ} {k : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν k Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y)
    (wgt : CompIn G.comps → ℝ) (hπ : R.π = fun v => G.mass law v / wgt v ^ 2)
    (A : ℝ) (hinit : weightedNorm ρ (G.mass law) wgt f ≤ A) :
    strongEnergy ρ ν (fun v => G.mass law v / wgt v ^ 2) a b U W ≤
      ENNReal.ofReal (Real.sqrt 2 * A) := by
  have hs := native_reg_solution_strongEnergy P seedK freshK φ₀ hφ₀ G R hB hC hS hφ
    α B lam hα hBdrift hlam hsmall hstrain hjets f U W Y hsol
  rw [hπ] at hs
  exact hs.trans (initial_energy_from_weighted_norm ρ (G.mass law) wgt f A hinit)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Independent joint regularity of the literal normalized incoming slot coefficients. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_actual_flux_joint_contDiff
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1))
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (n : ℕ) (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1) :
    ContDiff ℝ (n : ℕ∞) (Function.uncurry (G.fam.flux p (G.actual p) v u γ d I t)) := by
  apply contDiff_pi.mpr
  intro c
  change ContDiff ℝ (n : ℕ∞)
    (fun q : Vec 2 × Vec 2 => G.fam.flux p (G.actual p) v u γ d I t q.1 q.2 c)
  obtain ⟨_, f, _, _, _, _, he, _⟩ :=
    contextCertified_exists_native_complex_bound hG hi hj hb hε p v u γ d I c hm hm2
  let pack : Vec 2 × Vec 2 → Vec (2 + 2) := fun q =>
    EntryWeakProofs.independentIntrinsicParameterPacking 2 (D.eps (G.level - 1) • q.1) q.2
  have hpack : ContDiff ℝ (n : ℕ∞) pack := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [pack, EntryWeakProofs.independentIntrinsicParameterPacking, Fin.addCases_left]
      fun_prop
    · simp only [pack, EntryWeakProofs.independentIntrinsicParameterPacking, Fin.addCases_right]
      fun_prop
  have hc := (contextCertified_native_flux_joint_coordinates_contDiff hG hpar hi hj hb hε
    p v u γ d I c hm hm2 n t ht).comp hpack
  have heq : (fun q : Vec 2 × Vec 2 => G.fam.flux p (G.actual p) v u γ d I t q.1 q.2 c) =
      fun q => G.fam.flux p (nativeStageContext G hi hj p
        (EntryWeakProofs.independentIntrinsicSlowProjection 2 (pack q)))
        v u γ d I t 0 (EntryWeakProofs.independentStoredParameterProjection 2 (pack q)) c := by
    funext q
    simp only [pack, EntryWeakProofs.independentIntrinsicParameterPacking_slow,
      EntryWeakProofs.independentIntrinsicParameterPacking_stored]
    exact actual_native_flux_eq G hi hj p (hnat.2.2.1 p) v u γ d I c t f
      (fun ctx X z => he ctx t ht X z) q.1 q.2
  rw [heq]
  exact hc

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Native normalized joint jets retain their positive witness with constants fixed before the data. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Buffer

theorem uniform_native_normalized_joint_exists_jet_bounds (bw : ℝ) (hb : 0 < bw) (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm bw j₀)
        (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level),
        0 < D.eps (G.level - 1) → G.IsSlotTransverse →
      ∀ (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
        (I : DerivativeWord2 (d - 1)) (c : Fin 2)
        (mres : ℝ), 0 ≤ mres → mres ≤ 2 →
      ∀ (L : ℕ) (θ : ℝ), 0 ≤ θ →
      ∀ (f : GenSort.Sem .ctx)
        (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ),
        IsHolExtension D bw j₀ G.level p.1 f (F p) →
        ctxSize D bw j₀ G.level F mres L ≤ ENNReal.ofReal θ →
        (∀ (ctx : StageCtx D bw j₀ G.level p) (t : ℝ),
          t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 → ∀ X z : Vec 2,
          G.fam.flux p ctx v u γ d I t X z c =
            if IsAdmissibleChain D bw j₀ G.level p.1
              (ctx.1.recenter D (D.eps (G.level - 1) • X))
            then f t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0) →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
        ContDiff ℝ (n : ℕ∞) (fun X : Vec (2 + 2) =>
          G.fam.flux p (nativeStageContext G hi hj p
            (D.eps (G.level - 1) • EntryWeakProofs.independentIntrinsicSlowProjection 2 X))
            v u γ d I t 0 (EntryWeakProofs.independentStoredParameterProjection 2 X) c) ∧
        ∀ j ≤ n, ∀ W : Vec (2 + 2),
        ‖iteratedFDeriv ℝ j (fun X : Vec (2 + 2) =>
          G.fam.flux p (nativeStageContext G hi hj p
            (D.eps (G.level - 1) • EntryWeakProofs.independentIntrinsicSlowProjection 2 X))
            v u γ d I t 0 (EntryWeakProofs.independentStoredParameterProjection 2 X) c) W‖ ≤
          B j * θ := by
  let Lslow := EntryWeakProofs.independentIntrinsicSlowProjection 2
  let Lfast := EntryWeakProofs.independentStoredParameterProjection 2
  let A : ℕ → ℝ := fun j => ((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * bw)) ^ j) *
    ∑ a : Fin 2, ‖(ContinuousLinearMap.proj a : Vec 2 →L[ℝ] ℝ)‖ ^ j
  have hA (j : ℕ) : 0 ≤ A j := by dsimp [A]; positivity
  obtain ⟨B, hB, hC⟩ := normalized_base_fast_joint_exists_jet_bounds n Lslow Lfast A hA
  refine ⟨B, hB, ?_⟩
  intro hr _ _ D Dm j₀ G hi hj hε hpar p v u γ d I c mres hm hm2 L θ hθ f F hHol hsize he
    t ht
  let e := D.eps (G.level - 1)
  let sf : Vec (2 + 2) → ℝ := fun X => G.fam.flux p
    (nativeStageContext G hi hj p (e • Lslow X)) v u γ d I t 0 (Lfast X) c
  have hlocal (W : Vec (2 + 2)) : ContDiffAt ℝ (n : ℕ∞) sf W ∧
      ∀ j ≤ n, ‖iteratedFDeriv ℝ j sf W‖ ≤ B j * θ := by
    let Fb : (Fin 2 → ℂ) → Vec 2 → ℂ := fun Z z => F p ⟨G.level - 1, [p.1]⟩ 0 t
      (Z, (fun a : Fin 0 => Fin.elim0 a), (fun a => (z a : ℂ)))
    have hd (z : Vec 2) : DifferentiableOn ℂ (fun Z => Fb Z z)
        {Z | (∑ a, |(Z a).im|) < e * (3 / 200)} := by
      have hh := native_holomorphic_base_slice D bw hb j₀ G.level p.1 f (F p) hHol t ht
        (fun a => (z a : ℂ)) (fun _ => Complex.ofReal_im _)
      have hT : (1 + (2 : ℝ) / 4) * (1 / 100) * D.eps (G.level - 1) = e * (3 / 200) := by
        dsimp [e]; ring
      rw [hT] at hh
      exact hh
    have hstrip (Z : Fin 2 → ℂ) (hZ : (∑ a, |(Z a).im|) < ((1 + mres / 4) / 100) * e) :
        (∑ a, |(Z a).im|) < (1 + mres / 4) * (1 / 100) * D.eps (G.level - 1) := by
      convert hZ using 1
      dsimp [e]
      ring
    have hfast (Z : Fin 2 → ℂ) (hZ : (∑ a, |(Z a).im|) < ((1 + mres / 4) / 100) * e)
        (z : Vec 2) := native_complex_fast_affine_regular_and_jets G hi hj hb hε hpar
      p v u γ d I c f F hHol t ht (fun ctx X z => he ctx t ht X z)
      mres hm hm2 L θ hθ hsize Z (hstrip Z hZ) z 1 n
    have hjet : ∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < ((1 + mres / 4) / 100) * e →
        ∀ z : Vec 2, ∀ l ≤ n, ∀ X,
        ‖iteratedFDeriv ℝ l (fun X : Vec 2 => Fb Z (z + X)) X‖ ≤ A l * θ := by
      intro Z hZ z l hl X
      have hh := (hfast Z hZ z).2 l hl X
      simp only [one_smul] at hh
      apply hh.trans
      apply mul_le_mul_of_nonneg_right _ hθ
      dsimp only [A]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.single_le_sum
        (f := fun a : Fin 2 => ‖(ContinuousLinearMap.proj a : Vec 2 →L[ℝ] ℝ)‖ ^ l)
        (fun a _ => by positivity) (Finset.mem_univ (transverseIndex p.1))
    obtain ⟨hreg, hnorm⟩ := hC e mres hε hm Fb hd
      (fun Z hZ z => by simpa only [one_smul] using (hfast Z hZ z).1) θ hθ
      (fun Z hZ z => native_complex_witness_bound G hi hj hb hε p v u γ d I c
        mres hm hm2 L θ hθ f F hHol hsize he t ht z Z (hstrip Z hZ)) hjet (Lslow W) (Lfast W)
    let H : Vec (2 + 2) → ℂ := fun X => Fb
      (fun a => ((e • (Lslow W + Lslow X)) a : ℂ)) (Lfast W + Lfast X)
    have heq : (fun X => sf (W + X)) = Complex.reCLM ∘ H := by
      funext X
      have hh := native_flux_holomorphic_realization G hi hj p v u γ d I c f (F p) hHol t ht
        (fun ctx X z => he ctx t ht X z) (e • (Lslow W + Lslow X)) (Lfast W + Lfast X)
      have hh' : H X = (sf (W + X) : ℂ) := by
        simpa only [sf, H, Fb, map_add] using hh
      exact (congrArg Complex.re hh').symm
    have hreal : ContDiffAt ℝ (n : ℕ∞) (fun X : Vec (2 + 2) => sf (W + X)) 0 := by
      rw [heq]
      exact Complex.reCLM.contDiff.contDiffAt.comp (f := H) 0 hreg
    have hreal' : ContDiffAt ℝ (n : ℕ∞) (fun X : Vec (2 + 2) => sf (W + X)) (W - W) := by
      rw [sub_self]
      exact hreal
    have hsub : ContDiffAt ℝ (n : ℕ∞) (fun X : Vec (2 + 2) => X - W) W :=
      contDiffAt_id.sub contDiffAt_const
    have hcont := hreal'.comp (f := fun X : Vec (2 + 2) => X - W) W hsub
    refine ⟨?_, ?_⟩
    · simpa only [Function.comp_def, ← add_sub_assoc, add_sub_cancel_left] using hcont
    intro j hjn
    have hn := Complex.reCLM.norm_iteratedFDeriv_comp_left hreg (by exact_mod_cast hjn)
    rw [← heq, Complex.reCLM_norm, one_mul,
      iteratedFDeriv_comp_add_left (f := sf) j W 0, add_zero] at hn
    exact hn.trans (hnorm j hjn)
  refine ⟨contDiff_iff_contDiffAt.mpr (fun W => (hlocal W).1), ?_⟩
  intro j hjn W
  exact (hlocal W).2 j hjn

end AVRegularity.Construction.Preservation.FullLift
end
end
end
