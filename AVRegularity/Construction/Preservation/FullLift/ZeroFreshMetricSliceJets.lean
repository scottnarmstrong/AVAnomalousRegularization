-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.KernelEnergy.TorusKernelComponentSup
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
public import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.CycleComparison.Coarse.Bound.FcNorm
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
public import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent
public import AVRegularity.EntryWeak.IndependentFreshCenterStrip

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift

/-! Compiled Galerkin existence for the literal native homogeneous kernel system. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_exists (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
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
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root)) :
    ∃ (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
      (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
      (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)),
      G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
        (fun _ _ => 0) (fun _ _ => 0) U W Y := by
  classical
  obtain ⟨hv, hp, hd, hV, hm⟩ := Buffer.stream_kernel_drift_data hφ a b
  obtain ⟨U, W, Y, hsol⟩ := KernelEnergy.TorusKernelOperator.kernelFourier_exists_weakSolution R
    (streamVel φ) hv hp (fun _ _ => 0) (fun _ _ => 0) α B lam hα hBdrift hlam
    hsmall hstrain hd hjets hV hm f
    (fun _ => timeMemLp_zero _ 2) (fun _ => timeIntegrable_zero _)
  refine ⟨U, W, Y, ?_⟩
  simpa only [GenStage.IsRegSolution, hB, hC, hS] using hsol

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Construction.Preservation.FullLift

/-! The original positive scalar witnesses assemble into a normalized vector jet bound. -/

section
open AVRegularity.Construction.Preservation.Buffer

theorem uniform_native_normalized_vector_joint_exists_jet_bounds (bw : ℝ) (hb : 0 < bw) (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm bw j₀)
        (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level),
        0 < D.eps (G.level - 1) → G.IsSlotTransverse →
      ∀ (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
        (I : DerivativeWord2 (d - 1)) (mres : ℝ), 0 ≤ mres → mres ≤ 2 →
      ∀ (L : ℕ) (θ : Fin 2 → ℝ), (∀ c, 0 ≤ θ c) →
      ∀ (f : Fin 2 → GenSort.Sem .ctx)
        (F : Fin 2 → OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ),
        (∀ c, IsHolExtension D bw j₀ G.level p.1 (f c) (F c p)) →
        (∀ c, ctxSize D bw j₀ G.level (F c) mres L ≤ ENNReal.ofReal (θ c)) →
        (∀ c (ctx : StageCtx D bw j₀ G.level p) (t : ℝ),
          t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 → ∀ X z : Vec 2,
          G.fam.flux p ctx v u γ d I t X z c =
            if IsAdmissibleChain D bw j₀ G.level p.1
              (ctx.1.recenter D (D.eps (G.level - 1) • X))
            then f c t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0) →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
        ContDiff ℝ (n : ℕ∞) (fun X : Vec (2 + 2) =>
          G.fam.flux p (nativeStageContext G hi hj p
            (D.eps (G.level - 1) • EntryWeakProofs.independentIntrinsicSlowProjection 2 X))
            v u γ d I t 0 (EntryWeakProofs.independentStoredParameterProjection 2 X)) ∧
        ∀ j ≤ n, ∀ W : Vec (2 + 2),
        ‖iteratedFDeriv ℝ j (fun X : Vec (2 + 2) =>
          G.fam.flux p (nativeStageContext G hi hj p
            (D.eps (G.level - 1) • EntryWeakProofs.independentIntrinsicSlowProjection 2 X))
            v u γ d I t 0 (EntryWeakProofs.independentStoredParameterProjection 2 X)) W‖ ≤
          B j * ∑ c, θ c := by
  obtain ⟨B, hB, hC⟩ := uniform_native_normalized_joint_exists_jet_bounds bw hb n
  refine ⟨B, hB, ?_⟩
  intro hr _ _ D Dm j₀ G hi hj hε hpar p v u γ d I mres hm hm2 L θ hθ f F hHol hsize he t ht
  have hc (c : Fin 2) := hC hr D Dm j₀ G hi hj hε hpar p v u γ d I c mres hm hm2
    L (θ c) (hθ c) (f c) (F c) (hHol c) (hsize c) (he c) t ht
  refine ⟨contDiff_pi.mpr (fun c => (hc c).1), ?_⟩
  intro j hjn W
  apply (norm_iteratedFDeriv_vector_le_sum 2 j _
    (fun c => (hc c).1.of_le (by exact_mod_cast hjn)) W).trans
  calc
    _ ≤ ∑ c, B j * θ c := Finset.sum_le_sum (fun c _ => (hc c).2 j hjn W)
    _ = B j * ∑ c, θ c := (Finset.mul_sum _ _ _).symm
end

/-! Uniform positive native joint prices restrict to the physical two-scale diagonal. -/

section
open AVRegularity.Construction.Preservation.Buffer EntryWeakProofs

theorem uniform_native_diagonal_exists_jet_bounds (bw : ℝ) (hb : 0 < bw) (n : ℕ) :
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
      ∀ e : ℝ, 0 < e → ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
        ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 =>
          G.fam.flux p (nativeStageContext G hi hj p X) v u γ d I t 0 (e⁻¹ • X) c) ∧
        ∀ j, j ≤ n → ∀ Y : Vec 2,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun X : Vec 2 =>
          G.fam.flux p (nativeStageContext G hi hj p X) v u γ d I t 0 (e⁻¹ • X) c) Y‖ ≤
          (B j * θ) * (ρ * max (D.eps (G.level - 1))⁻¹ e⁻¹) ^ j := by
  obtain ⟨B, hB, hC⟩ := uniform_native_normalized_joint_exists_jet_bounds bw hb n
  refine ⟨B, hB, ?_⟩
  intro hr _ _ D Dm j₀ G hi hj hε hpar p v u γ d I c mres hm hm2 L θ hθ f F hHol hsize he
    e hepos ρ hρ t ht
  obtain ⟨hreg, hnorm⟩ := hC hr D Dm j₀ G hi hj hε hpar p v u γ d I c mres hm hm2
    L θ hθ f F hHol hsize he t ht
  let sf : Vec (2 + 2) → ℝ := fun X =>
    G.fam.flux p (nativeStageContext G hi hj p
      (D.eps (G.level - 1) • independentIntrinsicSlowProjection 2 X)) v u γ d I t 0
      (independentStoredParameterProjection 2 X) c
  have heq (X : Vec 2) : sf
      (independentIntrinsicParameterPacking 2 ((D.eps (G.level - 1))⁻¹ • X) (e⁻¹ • X)) =
      G.fam.flux p (nativeStageContext G hi hj p X) v u γ d I t 0 (e⁻¹ • X) c := by
    simp only [sf, independentIntrinsicParameterPacking_slow,
      independentIntrinsicParameterPacking_stored, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  constructor
  · have hh := hreg.comp (independentDiagonalMap (D.eps (G.level - 1))⁻¹ e⁻¹).contDiff
    change ContDiff ℝ (n : ℕ∞)
      (fun X => sf (independentDiagonalMap (D.eps (G.level - 1))⁻¹ e⁻¹ X)) at hh
    simpa only [independentDiagonalMap_apply, heq] using hh
  · intro j hjn Y
    have hn := independent_diagonal_scaled_jet_bound sf n hreg (fun l => B l * θ)
      (fun l => mul_nonneg (hB l) hθ) hnorm
      (D.eps (G.level - 1))⁻¹ e⁻¹ ρ (inv_nonneg.mpr hε.le) (inv_nonneg.mpr hepos.le)
      hρ j hjn Y
    simpa only [heq] using hn
end

/-! The actual dimensional coefficient retains its original positive price on the spatial diagonal. -/

section
open AVRegularity.Construction.Preservation.Buffer

theorem uniform_native_dimensional_diagonal_exists_jet_bounds (bw : ℝ) (hb : 0 < bw) (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm bw j₀)
        (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
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
      (G.actual p).1 = nativeChain G.level p.1 →
      ∀ (ν e : ℝ), 0 < e → ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
        ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 =>
          G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t X (e⁻¹ • X) c) ∧
        ∀ j, j ≤ n → ∀ Y : Vec 2,
          ρ ^ j * ‖iteratedFDeriv ℝ j (fun X : Vec 2 =>
            G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t X (e⁻¹ • X) c) Y‖ ≤
            (‖ν * e ^ (d - 2)‖ * (B j * θ)) *
              (ρ * max (D.eps (G.level - 1))⁻¹ e⁻¹) ^ j := by
  obtain ⟨B, hB, hC⟩ := uniform_native_diagonal_exists_jet_bounds bw hb n
  refine ⟨B, hB, ?_⟩
  intro hr _ _ D Dm j₀ G hi hj hε hpar p v u γ d I c mres hm hm2 L θ hθ f F hHol hsize he
    ha ν e hepos ρ hρ t ht
  obtain ⟨hreg, hnorm⟩ := hC hr D Dm j₀ G hi hj hε hpar p v u γ d I c mres hm hm2
    L θ hθ f F hHol hsize he e hepos ρ hρ t ht
  let sf : Vec 2 → ℝ := fun X => G.fam.flux p (nativeStageContext G hi hj p X)
    v u γ d I t 0 (e⁻¹ • X) c
  have heq : (fun X : Vec 2 => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p)
      v u γ d I t X (e⁻¹ • X) c) = fun X => (ν * e ^ (d - 2)) • sf X := by
    funext X
    exact actual_native_dimFlux_eq G hi hj p ha v u γ d I c t f
      (fun ctx X z => he ctx t ht X z) hε.ne' ν e X (e⁻¹ • X)
  rw [heq]
  refine ⟨hreg.const_smul _, ?_⟩
  intro j hjn Y
  rw [iteratedFDeriv_const_smul_apply' (hreg.contDiffAt.of_le (by exact_mod_cast hjn)), norm_smul]
  calc
    _ = ‖ν * e ^ (d - 2)‖ * (ρ ^ j * ‖iteratedFDeriv ℝ j sf Y‖) := by ring
    _ ≤ ‖ν * e ^ (d - 2)‖ * ((B j * θ) *
        (ρ * max (D.eps (G.level - 1))⁻¹ e⁻¹) ^ j) :=
      mul_le_mul_of_nonneg_left (hnorm j hjn Y) (norm_nonneg _)
    _ = _ := by ring
end

/-! Uniform scaled mixed bounds for the literal actual flux retain the context witnesses. -/

section
open AVRegularity.Construction.Preservation.Buffer

theorem uniform_native_actual_scaled_mixed_exists_jet_bounds (bw : ℝ) (hb : 0 < bw) (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm bw j₀)
        (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
        0 < D.eps (G.level - 1) → G.IsSlotTransverse →
      ∀ (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
        (I : DerivativeWord2 (d - 1)) (mres : ℝ), 0 ≤ mres → mres ≤ 2 →
      ∀ (L : ℕ) (θ : Fin 2 → ℝ), (∀ c, 0 ≤ θ c) →
      ∀ (f : Fin 2 → GenSort.Sem .ctx)
        (F : Fin 2 → OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ),
        (∀ c, IsHolExtension D bw j₀ G.level p.1 (f c) (F c p)) →
        (∀ c, ctxSize D bw j₀ G.level (F c) mres L ≤ ENNReal.ofReal (θ c)) →
        (∀ c (ctx : StageCtx D bw j₀ G.level p) (t : ℝ),
          t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 → ∀ X z : Vec 2,
          G.fam.flux p ctx v u γ d I t X z c =
            if IsAdmissibleChain D bw j₀ G.level p.1
              (ctx.1.recenter D (D.eps (G.level - 1) • X))
            then f c t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0) →
      (G.actual p).1 = nativeChain G.level p.1 →
      ∀ (lam : ℝ), 0 ≤ lam →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
      ∀ r q : ℕ, r + q ≤ n → ∀ X z : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
          (fun w => G.fam.flux p (G.actual p) v u γ d I t (lam • Y) w) z) X‖ ≤
          B (r + q) * lam ^ r * ∑ c, θ c := by
  obtain ⟨B, hB, hC⟩ := uniform_native_normalized_vector_joint_exists_jet_bounds bw hb n
  refine ⟨B, hB, ?_⟩
  intro hr _ _ D Dm j₀ G hi hj hε hpar p v u γ d I mres hm hm2 L θ hθ f F hHol hsize he
    ha lam hlam t ht r q hrq X z
  obtain ⟨hreg, hnorm⟩ := hC hr D Dm j₀ G hi hj hε hpar p v u γ d I mres hm hm2
    L θ hθ f F hHol hsize he t ht
  let sf : Vec (2 + 2) → Vec 2 := fun W => G.fam.flux p
    (nativeStageContext G hi hj p
      (D.eps (G.level - 1) • EntryWeakProofs.independentIntrinsicSlowProjection 2 W))
    v u γ d I t 0 (EntryWeakProofs.independentStoredParameterProjection 2 W)
  have heq (Y w : Vec 2) :
      sf (EntryWeakProofs.independentIntrinsicParameterPacking 2 (lam • Y) w) =
      G.fam.flux p (G.actual p) v u γ d I t (lam • Y) w := by
    funext c
    simp only [sf, EntryWeakProofs.independentIntrinsicParameterPacking_slow,
      EntryWeakProofs.independentIntrinsicParameterPacking_stored]
    exact (Buffer.actual_native_flux_eq G hi hj p ha v u γ d I c t (f c)
      (fun ctx X z => he c ctx t ht X z) (lam • Y) w).symm
  have hn := independent_scaled_mixed_jet_norm_le r q sf
    (hreg.of_le (by exact_mod_cast hrq)) lam (B (r + q) * ∑ c, θ c) hlam
    (mul_nonneg (hB _) (Finset.sum_nonneg (fun c _ => hθ c)))
    (fun W => hnorm (r + q) hrq W) X z
  simp only [heq] at hn
  exact hn.trans_eq (by ring)
end

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift

/-! Higher native existence from strict order-zero absorption and finite smooth coefficient prices. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_exists_higher (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν 0 Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    (hθ : R.θ < 1 / 8)
    (hfin : ∀ i j γ d, coefficientSeminorm ρ k a b (R.B i j γ d) ≠ ⊤)
    (hsmooth : ∀ i j γ d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (k : ℕ) (R.B i j γ d t))
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root)) :
    ∃ (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
      (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
      (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)),
      G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
        (fun _ _ => 0) (fun _ _ => 0) U W Y := by
  obtain ⟨r, hr, hrρ, Q, _hπ, hQB, hQC, hQS, _hc, _hr⟩ :=
    kernel_operator_order_upgrade R hθ k hfin hsmooth
  have hsmall' : B * r / lam ≤ 1 / 2 :=
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrρ (zero_le_one.trans hBdrift)) hlam.le).trans hsmall
  have hstrain' : α * B * r ^ 2 ≤ ν / 8 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrρ 2)
      (mul_nonneg hα (zero_le_one.trans hBdrift))).trans hstrain
  exact native_reg_solution_exists P seedK freshK φ₀ hφ₀ G Q
    (hQB.trans hB) (hQC.trans hC) (hQS.trans hS) hφ α B lam hα hBdrift hlam
    hsmall' hstrain' hjets f

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Constant covariance polynomials commute with gradients in the actual duality carrier relation. -/

open CycleComparison.Coarse
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem covImage_covPolyP_derivative {K p : ℕ}
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Z : TorusHk (K + 2 * p + 1) E) (W : TorusHk (K + 1) E)
    (hW : IsCovImage (covPolyP Hc p) Z W) (j : Fin 2) :
    IsCovImage (covPolyP Hc p)
      (derivativeTorusHk (K := K + 2 * p) (r := 1) (fun _ => j) Z)
      (derivativeTorusHk (K := K) (r := 1) (fun _ => j) W) := by
  intro ψ hψ hp
  have hψn (n : ℕ) : ContDiff ℝ (n : WithTop ℕ∞) ψ := hψ.of_le (by exact_mod_cast le_top)
  have hdψ : ContDiff ℝ (⊤ : ℕ∞) (partialOp j ψ) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdp : AVenhance.IsZ2Periodic (partialOp j ψ) := by
    intro k x
    exact congrArg (fun A => A (basisVec j))
      (fderiv_isZ2Periodic (hψ.differentiable (by simp)) hp k x)
  have hcomm := (ConstCoefOp.covPolyP (E := E) Hc p).comm j ψ (hψn _)
  have hPψ : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (covPolyP Hc p ψ) :=
    (ConstCoefOp.covPolyP (E := E) Hc p).reg 1 ψ (hψn _)
  have hPp : AVenhance.IsZ2Periodic (covPolyP Hc p ψ) := isZ2Periodic_covPolyP Hc p hψ hp
  change cellInner (tval (derivativeTorusHk (K := K) (r := 1) (fun _ => j) W)) ψ =
    cellInner (tval (derivativeTorusHk (K := K + 2 * p) (r := 1) (fun _ => j) Z))
      (covPolyP Hc p ψ)
  rw [tval_derivativeTorusHk_single, tval_derivativeTorusHk_single,
    cellInner_firstDerivative_eq_neg W j (hψn 1) hp,
    cellInner_firstDerivative_eq_neg Z j hPψ hPp]
  change -cellInner (tval W) (partialOp j ψ) =
    -cellInner (tval Z) (partialOp j (covPolyP Hc p ψ))
  rw [← hcomm]
  exact congrArg Neg.neg (hW (partialOp j ψ) hdψ hdp)

theorem covImage_covPolyP_gradient_factorial_le {K p : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Z : TorusHk (K + 2 * p + 1) E) (W : TorusHk (K + 1) E)
    (hW : IsCovImage (covPolyP Hc p) Z W) :
    gradFactorialNormSq ρ W.val ≤
      covPolyConst (fbCovConst ρ Hc (K + 2 * p)) p ^ 2 * gradFactorialNormSq ρ Z.val := by
  rw [← gradNormSq_eq_gradFactorialNormSq ρ W, ← gradNormSq_eq_gradFactorialNormSq ρ Z]
  unfold gradNormSq
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => covImage_covPolyP_factorial_le hρ Hc _ _
    (covImage_covPolyP_derivative Hc Z W hW j)

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Construction.Preservation.FullLift

/-! Actual native chart sampling preserves the dimensional positive context price. -/

section
open AVRegularity.Construction.Preservation.Buffer

theorem uniform_native_sampled_flux_exists_jet_bounds (bw : ℝ) (hb : 0 < bw) (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm bw j₀)
        (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
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
      (G.actual p).1 = nativeChain G.level p.1 →
      ∀ (ν e : ℝ), 0 < e → ∀ ρ : ℝ, 0 < ρ →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
      ∀ (Cchart R : ℝ), 1 ≤ Cchart → ρ ≤ R →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
        n Cchart R →
      ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 =>
        G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
          (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t)
          (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t) c) ∧
      ∀ j, j ≤ n → ∀ Y : Vec 2,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun X : Vec 2 =>
          G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
            (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t)
            (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t) c) Y‖ ≤
          (((j.factorial : ℝ) * Cchart ^ j *
            ∑ l ∈ Finset.range (j + 1), B l * (ρ * max (D.eps (G.level - 1))⁻¹ e⁻¹) ^ l) *
              ‖ν * e ^ (d - 2)‖) * θ := by
  obtain ⟨B, hB, hC⟩ := uniform_native_dimensional_diagonal_exists_jet_bounds bw hb n
  refine ⟨B, hB, ?_⟩
  intro hr _ _ D Dm j₀ G hi hj hε hpar p v u γ d I c mres hm hm2 L θ hθ f F hHol hsize he
    ha ν e hepos ρ hρ t ht Cchart R hchart hρR hjet
  obtain ⟨hreg, hnorm⟩ := hC hr D Dm j₀ G hi hj hε hpar p v u γ d I c mres hm hm2
    L θ hθ f F hHol hsize he ha ν e hepos ρ hρ.le t ht
  let raw : Vec 2 → ℝ := fun X => G.fam.dimFlux ν e (D.eps (G.level - 1))
    p (G.actual p) v u γ d I t X (e⁻¹ • X) c
  let Ψ : Vec 2 → Vec 2 := fun X => D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t
  have hΨ : ContDiff ℝ (n : ℕ∞) Ψ :=
    (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
      (D.slotAnchor G.level p.1) t).of_le (by simp)
  refine ⟨hreg.comp hΨ, ?_⟩
  intro j hjn Y
  have hh := positive_chart_composition_jet_bound raw Ψ j
    (hreg.of_le (by exact_mod_cast hjn)) (hΨ.of_le (by exact_mod_cast hjn)) Cchart R ρ (‖ν * e ^ (d - 2)‖ * θ)
    hchart hρ hρR (fun l => B l * (ρ * max (D.eps (G.level - 1))⁻¹ e⁻¹) ^ l)
    (fun l hl hlj => hjet l hl (hlj.trans hjn))
    (fun l hlj x => (hnorm l (hlj.trans hjn) x).trans_eq (by ring)) Y
  exact hh.trans_eq (by ring)
end

/-! Uniform actual sampled prices at radii below both wavelengths. -/

section
open AVRegularity.Construction.Preservation.Buffer

theorem uniform_native_sampled_flux_exists_price (bw : ℝ) (hb : 0 < bw) (n : ℕ)
    (Cchart : ℝ) (hchart : 1 ≤ Cchart) :
    ∃ Csample : ℝ, 0 ≤ Csample ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm bw j₀)
        (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
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
      (G.actual p).1 = nativeChain G.level p.1 →
      ∀ (ν e : ℝ), 0 < e → ∀ ρ : ℝ, 0 < ρ → ρ ≤ D.eps (G.level - 1) → ρ ≤ e →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
      ∀ R : ℝ, ρ ≤ R →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
        n Cchart R →
      ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 =>
        G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
          (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t)
          (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t) c) ∧
      ∀ j, j ≤ n → ∀ Y : Vec 2,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun X : Vec 2 =>
          G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
            (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t)
            (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t) c) Y‖ ≤
          (Csample * ‖ν * e ^ (d - 2)‖) * θ := by
  obtain ⟨B, hB, hC⟩ := uniform_native_sampled_flux_exists_jet_bounds bw hb n
  refine ⟨sampledJetConstant n Cchart B,
    sampledJetConstant_nonneg n Cchart (zero_le_one.trans hchart) B hB, ?_⟩
  intro hr _ _ D Dm j₀ G hi hj hε hpar p v u γ d I c mres hm hm2 L θ hθ f F hHol hsize he
    ha ν e hepos ρ hρ hρE hρe t ht R hρR hjet
  obtain ⟨hreg, hnorm⟩ := hC hr D Dm j₀ G hi hj hε hpar p v u γ d I c mres hm hm2
    L θ hθ f F hHol hsize he ha ν e hepos ρ hρ t ht Cchart R hchart hρR hjet
  refine ⟨hreg, ?_⟩
  intro j hjn Y
  apply (hnorm j hjn Y).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (sampled_jet_factor_le n j hjn Cchart (D.eps (G.level - 1)) e ρ
        (zero_le_one.trans hchart) hε hepos hρ.le hρE hρe B hB)
      (norm_nonneg _)) hθ
end

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Uniform covariance prices transfer both component suprema and gradient integrals. -/

open CycleComparison.Coarse
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem covImage_strongEnergy_le {K p : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ν a b C : ℝ) (hC : 0 ≤ C)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (u : ∀ i, ℝ → TorusHk K (h i)) (w : ∀ i, ℝ → TorusHk (K + 1) (h i))
    (z : ∀ i, ℝ → TorusHk (K + 2 * p) (h i))
    (v : ∀ i, ℝ → TorusHk (K + 2 * p + 1) (h i))
    (hv : ∀ i, MemLp (v i) 2 (volume.restrict (Set.Icc a b)))
    (hvalue : ∀ i, ∀ t ∈ Set.Icc a b, IsCovImage (covPolyP (Hc t) p) (z i t) (u i t))
    (hgrad : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      IsCovImage (covPolyP (Hc t) p) (v i t) (w i t))
    (hcost : ∀ t ∈ Set.Icc a b, covPolyConst (fbCovConst ρ (Hc t) (K + 2 * p)) p ≤ C) :
    strongEnergy ρ ν π a b u w ≤ ENNReal.ofReal C * strongEnergy ρ ν π a b z v := by
  apply strongEnergy_le_of_component_square_bounds ρ ρ ν a b C hC π hπ u w z v
  · intro i
    exact (integrable_gradFactorialNormSq_torus (hv i)).aemeasurable.ennreal_ofReal
  · intro i t ht
    exact (covImage_covPolyP_factorial_le hρ (Hc t) _ _ (hvalue i t ht)).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (covPolyConst_nonneg hρ (Hc t) p _) (hcost t ht) 2)
        (factorialNormSq_nonneg _ _))
  · intro i
    filter_upwards [hgrad i, ae_restrict_mem measurableSet_Icc] with t ht hmem
    exact (covImage_covPolyP_gradient_factorial_le hρ (Hc t) _ _ ht).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (covPolyConst_nonneg hρ (Hc t) p _) (hcost t hmem) 2)
        (gradFactorialNormSq_nonneg _ _))

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Extract actual sampled flux prices and the unchanged ledger from a context certificate. -/

theorem uniform_context_certified_sampled_flux_price (bw : ℝ) (hb : 0 < bw) (n : ℕ)
    (Cchart : ℝ) (hchart : 1 ≤ Cchart) :
    ∃ Csample : ℝ, 0 ≤ Csample ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm bw j₀) (k : InvConsts),
      G.IsContextCertified k → ∀ (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
      0 < D.eps (G.level - 1) → G.IsSlotTransverse →
      ∀ (v u : CompIn G.comps) (γ : G.fam.Γ v u),
      0 ≤ compReserve k v.1 → compReserve k v.1 ≤ 2 →
      ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
        (∀ d I c, 0 ≤ θ d I c) ∧
        (∀ d, 2 ≤ d → d ≤ (G.fam.identity v u γ).maxOrder →
          (D.eps G.level / (G.fam.identity v u γ).record.length) ^ (d - 2) *
            ∑ I, ∑ c, θ d I c ≤ (G.fam.identity v u γ).record.size) ∧
      ∀ (p : OddSlot) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2),
      (G.actual p).1 = nativeChain G.level p.1 →
      ∀ (ν e : ℝ), 0 < e → ∀ ρ : ℝ, 0 < ρ →
      ρ ≤ D.eps (G.level - 1) → ρ ≤ e →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
      ∀ R : ℝ, ρ ≤ R →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
        n Cchart R →
      ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 =>
        G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
          (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t)
          (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t) c) ∧
      ∀ j, j ≤ n → ∀ Y : Vec 2,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun X : Vec 2 =>
          G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
            (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t)
            (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) X t) c) Y‖ ≤
          (Csample * ‖ν * e ^ (d - 2)‖) * θ d I c := by
  obtain ⟨Csample, hCs, hbound⟩ := uniform_native_sampled_flux_exists_price bw hb n Cchart hchart
  refine ⟨Csample, hCs, ?_⟩
  intro hr _ _ D Dm j₀ G k hG hi hj hε hpar v u γ hm hm2
  obtain ⟨θ, hθ, hledger, hwitness⟩ := hG v u γ
  refine ⟨θ, hθ, hledger, ?_⟩
  intro p d I c ha ν e hepos ρ hρ hρE hρe t ht R hρR hjet
  obtain ⟨f, F, hF, hsize⟩ := hwitness d I c
  exact hbound hr D Dm j₀ G hi hj hε hpar p v u γ d I c
    (compReserve k v.1) hm hm2 k.Lstar (θ d I c) (hθ d I c)
    (f p) F (hF p).2.1 hsize (hF p).2.2 ha ν e hepos ρ hρ hρE hρe
    t ht R hρR hjet

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Covariance at the native radius is controlled by input energy at the enhanced radius. -/

open CycleComparison.Coarse
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem covImage_strongEnergy_enhanced_radius_le {K p : ℕ} {ρ cr : ℝ}
    (hρ : 0 < ρ) (hcr : 0 < cr) (hcr1 : cr ≤ 1)
    (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ν a b C : ℝ) (hC : 0 ≤ C)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (u : ∀ i, ℝ → TorusHk K (h i)) (w : ∀ i, ℝ → TorusHk (K + 1) (h i))
    (z : ∀ i, ℝ → TorusHk (K + 2 * p) (h i))
    (v : ∀ i, ℝ → TorusHk (K + 2 * p + 1) (h i))
    (hv : ∀ i, MemLp (v i) 2 (volume.restrict (Set.Icc a b)))
    (hvalue : ∀ i, ∀ t ∈ Set.Icc a b, IsCovImage (covPolyP (Hc t) p) (z i t) (u i t))
    (hgrad : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      IsCovImage (covPolyP (Hc t) p) (v i t) (w i t))
    (hcost : ∀ t ∈ Set.Icc a b, covPolyConst (fbCovConst ρ (Hc t) (K + 2 * p)) p ≤ C) :
    strongEnergy ρ ν π a b u w ≤
      ENNReal.ofReal (C * (cr⁻¹) ^ (K + 2 * p)) * strongEnergy (cr * ρ) ν π a b z v := by
  have hA : 1 ≤ cr⁻¹ := (one_le_inv₀ hcr).mpr hcr1
  have hr := strongEnergy_mul_radius_le hA (cr * ρ) ν a b π hπ z v
    (fun i => (integrable_gradFactorialNormSq_torus (hv i)).aemeasurable.ennreal_ofReal)
  have hid : cr⁻¹ * (cr * ρ) = ρ := by rw [← mul_assoc, inv_mul_cancel₀ hcr.ne', one_mul]
  rw [hid] at hr
  calc
    _ ≤ ENNReal.ofReal C * strongEnergy ρ ν π a b z v :=
      covImage_strongEnergy_le hρ Hc ν a b C hC π hπ u w z v hv hvalue hgrad hcost
    _ ≤ ENNReal.ofReal C *
        (ENNReal.ofReal ((cr⁻¹) ^ (K + 2 * p)) * strongEnergy (cr * ρ) ν π a b z v) :=
      mul_le_mul' le_rfl hr
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hC]

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Every requested rectangular coefficient reserve follows from the native context certificate. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_lift_fiber_boxSmooth
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hm : ∀ v : CompIn G.comps, 0 ≤ compReserve k v.1)
    (hm2 : ∀ v : CompIn G.comps, compReserve k v.1 ≤ 2)
    (p : OddSlot) (ρ : ℝ) (sX sZ : ℕ) :
    ∀ v u d, ∀ γ ∈ (familyLiftData D G.level p.1 (nativeChain G.level p.1) ρ
      (G.fam.fiber p (G.actual p))).edge v u d, ∀ α,
      ∀ t ∈ Set.Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
        ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
        IsBoxSmooth sX sZ (γ.coeff α t) := by
  apply liftEdges_boxSmooth_of_joint
  · intro t ht
    exact EntryWeakProofs.weak_lift_clock_in_pulse_window D hΛ hζ hband G.level p.1 t ht
  · intro v u d γ hγ α t ht
    obtain ⟨δ, _hd, he⟩ := fiber_coefficient_identity G.fam p (G.actual p) v u d γ hγ
    rw [he]
    exact native_actual_flux_joint_contDiff hG hpar hnat hi hj hb hε p v u δ d.1 α
      (hm v) (hm2 v) (sX + sZ) t ht

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Construction.Preservation.FullLift

/-! One original context weight array controls all lift jets and preserves its record-size inequality. -/

theorem uniform_contextCertified_lift_identity_exists_jet_bounds (bw : ℝ) (hb : 0 < bw) (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm bw j₀) (k : InvConsts) (M : ℕ),
      G.IsContextCertified k → G.IsNatural M → G.IsSlotTransverse →
      1 ≤ G.level → j₀ ≤ G.level → 0 < D.eps (G.level - 1) →
      1 ≤ D.Λ → IsFastProfile D.ζ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ (v u : CompIn G.comps) (γ : G.fam.Γ v u),
      0 ≤ compReserve k v.1 → compReserve k v.1 ≤ 2 →
      ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
        (∀ d I c, 0 ≤ θ d I c) ∧
        (∀ d, 2 ≤ d → d ≤ (G.fam.identity v u γ).maxOrder →
          (D.eps G.level / (G.fam.identity v u γ).record.length) ^ (d - 2) *
            ∑ I, ∑ c, θ d I c ≤ (G.fam.identity v u γ).record.size) ∧
        ∀ (p : OddSlot) (lam : ℝ), 0 ≤ lam → ∀ (d : ℕ) (I : DerivativeWord2 (d - 1)),
        ∀ (r q : ℕ), r + q ≤ n →
          jetSup (Set.Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
            ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
            r q (fun t X z => G.fam.flux p (G.actual p) v u γ d I
              (D.cellScaleSq G.level * t) (lam • X) z) ≤
            ENNReal.ofReal (B (r + q) * lam ^ r * ∑ c, θ d I c) := by
  obtain ⟨B, hB, hC⟩ := uniform_native_actual_scaled_mixed_exists_jet_bounds bw hb n
  refine ⟨B, hB, ?_⟩
  intro hr _ _ D Dm j₀ G k M hG hnat hpar hi hj hε hΛ hζ hband v u γ hm hm2
  obtain ⟨θ, hθ, hrecord, hforms⟩ := hG v u γ
  refine ⟨θ, hθ, hrecord, ?_⟩
  intro p lam hlam d I r q hrq
  choose f F hslots hsize using fun c : Fin 2 => hforms d I c
  apply jetSup_clock_scaled_le
    _ (ocPulseWindow D.α D.q D.Λ G.level p.1) _ lam _ r q
  · intro t ht
    exact EntryWeakProofs.weak_lift_clock_in_pulse_window D hΛ hζ hband G.level p.1 t ht
  · intro t ht X z
    exact hC hr D Dm j₀ G hi hj hε hpar p v u γ d I (compReserve k v.1) hm hm2
      k.Lstar (θ d I) (hθ d I) (fun c => f c p) F
      (fun c => (hslots c p).2.1) hsize (fun c => (hslots c p).2.2)
      (hnat.2.2.1 p) lam hlam t ht r q hrq X z

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift

/-! Common preparation bounds the retained strong energy once the literal retained kernel
operator is supplied. The operator and its analytic drift prices are hypotheses of the statement. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem common_preparation_retained_strongEnergy
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr : GenStage D hr Dm bw j₀)
    {cr Q CQ Cpr : ℝ} {p Nout Naux m : ℕ} {s tf tp : ℝ}
    (hlevel : G.level = m) (hST : G.comps ⊆ Gr.comps)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ Cpr p Nout Naux s tf tp Preg)
    (wgt : Comp → ℝ) (hwgt : ((fun v : CompIn G.comps => wgt v.1) = fun _ => 1) ∨
      (fun v : CompIn G.comps => wgt v.1) = G.marker law)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ)
    (hf : weightedNorm 1 (G.mass law) (fun v => wgt v.1) f ≤ Ain)
    (Y0 : ∀ c : CompIn Gr.comps, TorusHk Naux (hr c.1.root))
    (htrace : IsRetainedTrace G Gr m p tp (Preg f) Y0)
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn Gr.comps => hr v.1.root)
      (Γ := Gr.fam.Γ) (G := fun _ u _ => hr u.1.root)
      tp tf (rhoEnh D cr G.level) (D.κ (m - 1)) Naux Dm)
    (hB : R.B = (fun (v u : CompIn Gr.comps) (γ : Gr.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => Gr.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn Gr.comps) (_ : Gr.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = Gr.sysS P seedK freshK φ₀ hφ₀)
    (hπ : R.π = fun v => Gr.mass law v / wgt v.1 ^ 2)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * rhoEnh D cr G.level / lam ≤ 1 / 2)
    (hstrain : α * B * rhoEnh D cr G.level ^ 2 ≤ D.κ (m - 1) / 8)
    (hjets : ∀ t ∈ Set.Icc tp tf, ∀ l, 1 ≤ l → l ≤ Naux → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
    (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (Naux + Dm - 1) (hr u.1.root))
    (hsol : Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel φ) Naux tp tf Y0
      (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk) :
    strongEnergy (rhoEnh D cr G.level) (D.κ (m - 1))
      (fun v => Gr.mass law v / wgt v.1 ^ 2) tp tf Y Yw ≤
        ENNReal.ofReal (Real.sqrt 2 * (Cpr * Ain)) := by
  have hinit := common_preparation_retained_trace_norm law P seedK freshK φ₀ hφ₀ G Gr
    hlevel hST Preg hprep wgt hwgt f Ain hf Y0 htrace
  exact native_reg_solution_strongEnergy_of_initial_norm P seedK freshK φ₀ hφ₀ Gr law R
    hB hC hS hφ α B lam hα hBdrift hlam hsmall hstrain hjets Y0 Y Yw Yk hsol
    (fun v => wgt v.1) hπ (Cpr * Ain) hinit

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Native source envelopes retain the actual record matrix and its two Schur prices. -/

theorem uniform_native_lift_record_source_exists_envelope (bw : ℝ) (hb : 0 < bw) (qs qf : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
      ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm bw j₀) (k : InvConsts) (M : ℕ),
      G.IsContextCertified k → G.IsNatural M → G.IsSlotTransverse →
      1 ≤ G.level → j₀ ≤ G.level → 0 < D.eps (G.level - 1) →
      1 ≤ D.Λ → IsFastProfile D.ζ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      (∀ v : CompIn G.comps, 0 ≤ compReserve k v.1) →
      (∀ v : CompIn G.comps, compReserve k v.1 ≤ 2) →
      (∀ v u γ, 1 ≤ (G.fam.identity v u γ).record.birthExcess →
        (G.fam.identity v u γ).record.length ≤ D.eps G.level) →
      ∀ (p : OddSlot) (lam : ℝ), 0 ≤ lam → ∀ (π : CompIn G.comps → ℝ) (Θ : ℝ),
      (∀ v, ∑ u, recordMajorant π G.fam v u ≤ Θ) →
      (∀ u, ∑ v, recordMajorant π G.fam v u ≤ Θ) →
      IsScaledJetEnvelope π
        (liftEdges (D.cellScaleSq G.level) lam (G.fam.fiber p (G.actual p)))
        (Set.Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
          ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
        lam (fun r q => (Fintype.card (Finset.Icc 2 Dm) : ℝ) * B (r + q))
        qs qf (recordMajorant π G.fam) Θ := by
  obtain ⟨B, hB, hC⟩ := uniform_contextCertified_lift_identity_exists_jet_bounds bw hb (qs + qf)
  refine ⟨B, hB, ?_⟩
  intro hr _ _ D Dm j₀ G k M hG hnat hpar hi hj hε hΛ hζ hband hm hm2 hlength p lam hlam π Θ hrow hcol
  choose θ hθ hrecord hjets using fun v u (γ : G.fam.Γ v u) =>
    hC hr D Dm j₀ G k M hG hnat hpar hi hj hε hΛ hζ hband v u γ (hm v) (hm2 v)
  exact scaledEnvelope_of_original_records G.fam p (G.actual p) π _ _
    (D.cellScaleSq G.level) lam hlam (fun r q => B (r + q))
    (fun r q => hB (r + q)) qs qf θ hθ hrecord hlength Θ hrow hcol
    (fun v u γ d _hd I r hr q hq => hjets v u γ p lam hlam d I r q (Nat.add_le_add hr hq))

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual retained readout budget from common preparation and homogeneous kernel energy.
The explicit retained operator and its analytic drift prices are hypotheses of the statement. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem common_preparation_readout_budget
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr G' : GenStage D hr Dm bw j₀) (Mn : SuccMenu)
    (hactual : IsActualSuccessor D P Mn G G')
    {cr Q CQ Cpr : ℝ} {p Nout Naux m : ℕ} {s tf tp : ℝ}
    (hGr : Gr = G'.retained m Mn.H Mn.J)
    (hm : 1 ≤ m) (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, m ≤ e.scale)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (hcH : law.cH ≤ 1) (hηB : 0 ≤ law.etaB) (hη0 : 0 ≤ law.eta0) (hiota : 0 ≤ law.iota)
    {K : ℕ} (hKN : K ≤ Naux)
    (hlevel : G.level = m) (hST : G.comps ⊆ Gr.comps)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ Cpr p Nout Naux s tf tp Preg)
    (wgt : Comp → ℝ)
    (hweight : wgt = (fun _ => 1) ∨ wgt = compMarker D.q D.Λ law)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ)
    (hf : weightedNorm 1 (G.mass law) (fun v => wgt v.1) f ≤ Ain)
    (Y0 : ∀ c : CompIn Gr.comps, TorusHk Naux (hr c.1.root))
    (htrace : IsRetainedTrace G Gr m p tp (Preg f) Y0)
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn Gr.comps => hr v.1.root)
      (Γ := Gr.fam.Γ) (G := fun _ u _ => hr u.1.root)
      tp tf (rhoEnh D cr G.level) (D.κ (m - 1)) Naux Dm)
    (hB : R.B = (fun (v u : CompIn Gr.comps) (γ : Gr.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => Gr.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn Gr.comps) (_ : Gr.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = Gr.sysS P seedK freshK φ₀ hφ₀)
    (hπ : R.π = fun v => Gr.mass law v / wgt v.1 ^ 2)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * rhoEnh D cr G.level / lam ≤ 1 / 2)
    (hstrain : α * B * rhoEnh D cr G.level ^ 2 ≤ D.κ (m - 1) / 8)
    (hjets : ∀ t ∈ Set.Icc tp tf, ∀ l, 1 ≤ l → l ≤ Naux → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
    (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (Naux + Dm - 1) (hr u.1.root))
    (hsol : Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel φ) Naux tp tf Y0
      (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk)
    (hw : ∀ c, MemLp (Yw c) 2 (volume.restrict (Set.Icc tp tf))) :
    readoutEnergy law G Gr m law.eta0 (rhoEnh D cr G.level) hKN
      (fun v => wgt v.1) tp tf Y Yw ≤
        ENNReal.ofReal (Real.sqrt ((wordsUpTo Mn.A (Mn.J + 1)).card + 1) *
          (Real.sqrt 2 * (Cpr * Ain))) := by
  have hwgt : ((fun v : CompIn G.comps => wgt v.1) = fun _ => 1) ∨
      (fun v : CompIn G.comps => wgt v.1) = G.marker law := by
    rcases hweight with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have he := common_preparation_retained_strongEnergy law P seedK freshK φ₀ hφ₀ G Gr
    hlevel hST Preg hprep wgt hwgt f Ain hf Y0 htrace R hB hC hS hπ hφ α B lam
    hα hBdrift hlam hsmall hstrain hjets Y Yw Yk hsol
  subst Gr
  have hweights :
      ((fun v : CompIn G.comps => wgt v.1) = fun _ => 1) ∧
        ((fun v : CompIn (G'.retained m Mn.H Mn.J).comps => wgt v.1) = fun _ => 1) ∨
      ((fun v : CompIn G.comps => wgt v.1) = G.marker law) ∧
        ((fun v : CompIn (G'.retained m Mn.H Mn.J).comps => wgt v.1) =
          (G'.retained m Mn.H Mn.J).marker law) := by
    rcases hweight with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hread := actual_readoutEnergy_le hactual hlevel hm hold hq hΛ law hcH hηB hη0 hiota
    hKN (rhoEnh D cr G.level) tp tf (fun v => wgt v.1) (fun v => wgt v.1)
    hweights Y Yw hw
  apply hread.trans
  apply (mul_le_mul' le_rfl he).trans_eq
  exact (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
end

/-! Enlarge the proved preparation readout price to a fixed constant. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem common_preparation_readout_budget_fixed_constant
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr G' : GenStage D hr Dm bw j₀) (Mn : SuccMenu)
    (hactual : IsActualSuccessor D P Mn G G')
    {cr Q CQ Cpr : ℝ} {p Nout Naux m : ℕ} {s tf tp : ℝ}
    (hGr : Gr = G'.retained m Mn.H Mn.J)
    (hm : 1 ≤ m) (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, m ≤ e.scale)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (hcH : law.cH ≤ 1) (hηB : 0 ≤ law.etaB) (hη0 : 0 ≤ law.eta0) (hiota : 0 ≤ law.iota)
    {K : ℕ} (hKN : K ≤ Naux)
    (hlevel : G.level = m) (hST : G.comps ⊆ Gr.comps)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ Cpr p Nout Naux s tf tp Preg)
    (wgt : Comp → ℝ)
    (hweight : wgt = (fun _ => 1) ∨ wgt = compMarker D.q D.Λ law)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ)
    (hf : weightedNorm 1 (G.mass law) (fun v => wgt v.1) f ≤ Ain)
    (Y0 : ∀ c : CompIn Gr.comps, TorusHk Naux (hr c.1.root))
    (htrace : IsRetainedTrace G Gr m p tp (Preg f) Y0)
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn Gr.comps => hr v.1.root)
      (Γ := Gr.fam.Γ) (G := fun _ u _ => hr u.1.root)
      tp tf (rhoEnh D cr G.level) (D.κ (m - 1)) Naux Dm)
    (hB : R.B = (fun (v u : CompIn Gr.comps) (γ : Gr.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => Gr.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn Gr.comps) (_ : Gr.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = Gr.sysS P seedK freshK φ₀ hφ₀)
    (hπ : R.π = fun v => Gr.mass law v / wgt v.1 ^ 2)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * rhoEnh D cr G.level / lam ≤ 1 / 2)
    (hstrain : α * B * rhoEnh D cr G.level ^ 2 ≤ D.κ (m - 1) / 8)
    (hjets : ∀ t ∈ Set.Icc tp tf, ∀ l, 1 ≤ l → l ≤ Naux → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
    (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (Naux + Dm - 1) (hr u.1.root))
    (hsol : Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel φ) Naux tp tf Y0
      (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk)
    (hw : ∀ c, MemLp (Yw c) 2 (volume.restrict (Set.Icc tp tf)))
    (Ck : ℝ) (hCk : Real.sqrt ((wordsUpTo Mn.A (Mn.J + 1)).card + 1) *
      Real.sqrt 2 * Cpr ≤ Ck) :
    readoutEnergy law G Gr m law.eta0 (rhoEnh D cr G.level) hKN
      (fun v => wgt v.1) tp tf Y Yw ≤
        ENNReal.ofReal (Ck * Ain) := by
  have hAin : 0 ≤ Ain := (Real.sqrt_nonneg _).trans hf
  have hb := common_preparation_readout_budget law P seedK freshK φ₀ hφ₀ G Gr G' Mn
    hactual hGr hm hold hq hΛ hcH hηB hη0 hiota hKN hlevel hST Preg hprep wgt hweight
    f Ain hf Y0 htrace R hB hC hS hπ hφ α B lam hα hBdrift hlam hsmall hstrain hjets
    Y Yw Yk hsol hw
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCk hAin
end

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

/-! The incoming invariant supplies the native source envelope for both energy weights. -/

theorem stage_native_lift_source_exists_envelope (bw : ℝ) (hb : 0 < bw) (qs qf : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
        [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
        [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
      ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm bw j₀)
        (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
        (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (k : InvConsts) (tA tB S θK : ℝ),
      IsStageInvariant law P seedK freshK φ₀ hφ₀ M k tA tB S θK G →
      1 ≤ G.level → j₀ ≤ G.level → 0 < D.eps (G.level - 1) →
      1 < D.q → 128 ≤ D.Λ → IsFastProfile D.ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      (∀ v : CompIn G.comps, 0 ≤ compReserve k v.1) →
      (∀ v : CompIn G.comps, compReserve k v.1 ≤ 2) →
      (∀ v u γ, 1 ≤ (G.fam.identity v u γ).record.birthExcess →
        (G.fam.identity v u γ).record.length ≤ D.eps G.level) →
      ∀ (p : OddSlot) (lam : ℝ), 0 ≤ lam → ∀ w : CompIn G.comps → ℝ,
      (w = fun _ => 1) ∨ w = G.marker law →
      IsScaledJetEnvelope (fun v => G.mass law v / w v ^ 2)
        (liftEdges (D.cellScaleSq G.level) lam (G.fam.fiber p (G.actual p)))
        (Set.Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
          ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
        lam (fun r q => (Fintype.card (Finset.Icc 2 Dm) : ℝ) * B (r + q)) qs qf
        (recordMajorant (fun v => G.mass law v / w v ^ 2) G.fam) S := by
  obtain ⟨B, hB, hsource⟩ := uniform_native_lift_record_source_exists_envelope bw hb qs qf
  refine ⟨B, hB, ?_⟩
  intro hr _ _ _ _ _ _ D Dm j₀ G law P seedK freshK φ₀ hφ₀ M k tA tB S θK
    hG hi hj hε hq hΛ hζ hband hm hm2 hlength p lam hlam w hw
  have hmass (v : CompIn G.comps) : 0 < G.mass law v :=
    Buffer.birth_compMass_pos hq hΛ law v.1
  have hmarker (v : CompIn G.comps) : 0 < G.marker law v :=
    Buffer.birth_compMarker_pos hq hΛ law v.1
  have hwpos (v : CompIn G.comps) : 0 < w v := by
    rcases hw with rfl | rfl
    · exact zero_lt_one
    · exact hmarker v
  obtain ⟨_, hrow, hcol, hmrow, hmcol⟩ := stage_record_schur_bounds hG
  have hmarked : (∀ v, ∑ u, w v / w u * recordMajorant (G.mass law) G.fam v u ≤ S) ∧
      (∀ u, ∑ v, w v / w u * recordMajorant (G.mass law) G.fam v u ≤ S) := by
    rcases hw with rfl | rfl
    · simpa only [div_self (one_ne_zero : (1 : ℝ) ≠ 0), one_mul] using And.intro hrow hcol
    · exact ⟨hmrow, hmcol⟩
  obtain ⟨hrow', hcol'⟩ := recordMajorant_effective_mass_schur G.fam (G.mass law) w
    hmass hwpos S hmarked.1 hmarked.2
  obtain ⟨hnat, _, _, _, hpar, hcert, _, _⟩ := hG
  exact hsource hr D Dm j₀ G k M hcert hnat hpar hi hj hε (by omega)
    hζ hband hm hm2 hlength p lam hlam _ S hrow' hcol'

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.Construction.Preservation.FullLift

/-! A zero-child full metric jet restricts to the scaled slow slice with its exact scale power. -/

theorem zeroFresh_metric_scaled_slice_jet_le (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (e lam u C : ℝ) (hlam : 0 ≤ lam) (n : ℕ)
    (hb : ‖iteratedFDeriv ℝ n (fun Z : Vec (4 * 0) × Vec 2 =>
      ((EntryWeakProofs.independentFreshChain A (fun j : Fin 0 => Fin.elim0 j)
        (fun j : Fin 0 => Fin.elim0 j) Z.1).recenter D (e • Z.2)).famMetric D u) 0‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun X : Vec 2 =>
      (A.recenter D ((e * lam) • X)).famMetric D u) 0‖ ≤ C * lam ^ n := by
  let g : Vec (4 * 0) × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun Z =>
    (A.recenter D (e • Z.2)).famMetric D u
  have he : (fun Z : Vec (4 * 0) × Vec 2 =>
      ((EntryWeakProofs.independentFreshChain A (fun j : Fin 0 => Fin.elim0 j)
        (fun j : Fin 0 => Fin.elim0 j) Z.1).recenter D (e • Z.2)).famMetric D u) = g := by
    funext Z
    simp only [g, EntryWeakProofs.independentFreshChain, List.ofFn_zero, List.append_nil]
  rw [he] at hb
  have hg : ContDiff ℝ (n : ℕ∞) g := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact ((EntryWeakProofs.recentered_metric_entry_smooth D A hA e u i j).of_le
      (by simp)).comp contDiff_snd
  let L : Vec 2 →L[ℝ] Vec (4 * 0) × Vec 2 :=
    (0 : Vec 2 →L[ℝ] Vec (4 * 0)).prod (lam • ContinuousLinearMap.id ℝ (Vec 2))
  have hL : ‖L‖ ≤ lam := by
    apply ContinuousLinearMap.opNorm_le_bound _ hlam
    intro X
    change ‖((0 : Vec (4 * 0)), lam • X)‖ ≤ lam * ‖X‖
    rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hlam]
  have hf : (fun X : Vec 2 => (A.recenter D ((e * lam) • X)).famMetric D u) = g ∘ L := by
    funext X
    simp only [g, L, ContinuousLinearMap.prod_apply, smul_apply, ContinuousLinearMap.id_apply,
      Function.comp_def, smul_smul]
  rw [hf, L.iteratedFDeriv_comp_right hg 0 (by simp), map_zero]
  have hn := (iteratedFDeriv ℝ n g (L 0)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [map_zero, Fin.prod_const] at hn
  exact hn.trans (mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg _) hL n)
    (by positivity) ((norm_nonneg _).trans hb))

end AVRegularity.Construction.Preservation.FullLift
end
