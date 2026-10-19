-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.Flux
import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeClassicalCurves
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

section
section
/-! Ingredient `CovarianceMeanReductionStatement`: substituting the strong readout equation into
the temporal product formula and grouping the exact finite mean flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
  AVRegularity.CycleComparison.Coarse
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- A `PiLp`-valued `C^K` field has `C^K` components. -/
theorem meanReduction_component {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : ℕ}
    {f : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} (hf : ContDiff ℝ (K : WithTop ℕ∞) f) (j : Fin 2) :
    ContDiff ℝ (K : WithTop ℕ∞) (fun y => f y j) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) j).contDiff.comp hf

/-- Pointwise (in time) form of the mean reduction. -/
theorem meanReduction_pointwise (F : Frame D hr Dm bw j₀) {dZ dRep dUh : F.Field}
    (hR : Regularity F dZ dRep dUh) (t : ℝ) (ht : t ∈ Set.Icc F.tp F.tf)
    (v : CompIn F.G.comps)
    (hread : ∀ y, F.coarseRes dZ t y v = divE (fun z => WithLp.ofLp (F.readFlux v t z)) y)
    (x : Vec 2) :
    menuCovPRep F.Mn D F.m F.p (F.coarseRes dZ) t x v +
      divE (fun y => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y) x -
      divE (fun y => WithLp.ofLp (F.lastFlux v t y)) x = F.meanDiv t x v := by
  set Hc := menuCovPrimitive D F.Mn F.m t with hHc
  set g : Fin 2 → Vec 2 → hr v.1.root := fun j y =>
    menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y j with hg_def
  set u : Fin 2 → Vec 2 → hr v.1.root := fun j y => WithLp.ofLp (F.upsilon v t y) j with hu_def
  set l : Fin 2 → Vec 2 → hr v.1.root := fun j y => WithLp.ofLp (F.lastFlux v t y) j with hl_def
  have hg : ∀ j, ContDiff ℝ ((4 * F.p + 2 : ℕ) : WithTop ℕ∞) (g j) := fun j =>
    meanReduction_component ((hR.readoutFluxRegularity v).smooth t ht) j
  have hu : ∀ j, ContDiff ℝ ((2 * F.p + 2 : ℕ) : WithTop ℕ∞) (u j) := fun j =>
    meanReduction_component ((hR.upsilonRegularity v).smooth t ht) j
  have hl : ∀ j, ContDiff ℝ 1 (l j) := fun j => by
    have := meanReduction_component (K := 1)
      ((hR.fluxes F.lastFlux (by simp) v).smooth t ht) j
    simpa [hl_def] using this
  have hQg : ∀ j, ContDiff ℝ ((2 * F.p + 2 : ℕ) : WithTop ℕ∞) (covPolyQ Hc F.p (g j)) := fun j =>
    (AVRegularity.CycleComparison.Coarse.ConstCoefOp.covPolyQ (E := hr v.1.root) Hc F.p).reg
      (2 * F.p + 2) (g j) (by
        have : 2 * F.p + 2 + 2 * F.p = 4 * F.p + 2 := by omega
        rw [this]; exact hg j)
  -- the Pi-valued fields
  have hGpi : ContDiff ℝ ((2 * F.p : ℕ) : WithTop ℕ∞)
      (fun y => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y) :=
    contDiff_pi.mpr fun j => (hg j).of_le (Nat.cast_le.mpr (by omega))
  have hQcomp : ∀ y j, covPolyQ Hc F.p (fun z => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT
      F.aZ v t z) y j = covPolyQ Hc F.p (g j) y := fun y j =>
    covProj_covPolyQ Hc (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => hr v.1.root) j)
      F.p hGpi y
  have hQpi : ContDiff ℝ ((2 * F.p : ℕ) : WithTop ℕ∞)
      (covPolyQ Hc F.p (fun z => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t z)) :=
    contDiff_pi.mpr fun j => by
      have e : (fun y => covPolyQ Hc F.p (fun z => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT
          F.aZ v t z) y j) = covPolyQ Hc F.p (g j) := funext fun y => hQcomp y j
      rw [e]; exact (hQg j).of_le (Nat.cast_le.mpr (by omega))
  have hUpi : ContDiff ℝ ((2 * F.p : ℕ) : WithTop ℕ∞) (fun y => WithLp.ofLp (F.upsilon v t y)) :=
    contDiff_pi.mpr fun j => (hu j).of_le (Nat.cast_le.mpr (by omega))
  have hread' : ∀ z j, WithLp.ofLp (F.readFlux v t z) j =
      -(covPolyQ Hc F.p (g j) z + u j z) := fun z j => by
    simp [Frame.readFlux, toFluxL, ← hHc, hQcomp z j, hu_def]
  have hPQ : ∀ z j, covPolyP Hc F.p (covPolyQ Hc F.p (fun y => menuGFlux F.Mn F.G F.m F.N F.p
      F.depth F.CcT F.aZ v t y)) z j = covPolyP Hc F.p (covPolyQ Hc F.p (g j)) z := fun z j => by
    have := covProj_covPolyP Hc
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => hr v.1.root) j) F.p hQpi z
    have e : (fun y => covPolyQ Hc F.p (fun z => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT
          F.aZ v t z) y j) = covPolyQ Hc F.p (g j) := funext fun y => hQcomp y j
    simpa [e] using this
  have hPU : ∀ z j, covPolyP Hc F.p (fun y => WithLp.ofLp (F.upsilon v t y)) z j =
      covPolyP Hc F.p (u j) z := fun z j =>
    covProj_covPolyP Hc
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => hr v.1.root) j) F.p hUpi z
  have hmean : ∀ z j, WithLp.ofLp (F.mean v t z) j = g j z -
      covPolyP Hc F.p (covPolyQ Hc F.p (g j)) z - covPolyP Hc F.p (u j) z - l j z := fun z j => by
    simp only [Frame.mean, toFluxL, menuMeanFluxF, Pi.sub_apply, ← hHc, hPQ, hPU, hl_def,
      Frame.lastFlux, hg_def]
  have h1 : menuCovPRep F.Mn D F.m F.p (F.coarseRes dZ) t x v =
      covPolyP Hc F.p (fun y => ∑ j : Fin 2, partialOp j
        (fun z => -(covPolyQ Hc F.p (g j) z + u j z)) y) x := by
    unfold menuCovPRep
    congr 1
    funext y
    rw [hread y]
    simp only [divE, partialOp, hread']
  rw [h1]
  refine (meanCore_identity Hc F.p g u l hg hu hl x).trans ?_
  simp only [Frame.meanDiv, divE, partialOp, hmean]

/-- Ingredient: the temporal product formula and the strong readout equation give the strong
mean equation. -/
theorem covarianceMeanReduction : CovarianceMeanReductionStatement := by
  intro hr _ _ _ _ _ _ D Dm bw j₀ F dZ dRep dUh hR hTP hSR
  filter_upwards [hTP, hSR, ae_restrict_mem measurableSet_Icc] with t h1 h2 ht x v
  rw [h1 x v]
  exact meanReduction_pointwise F hR t ht v (fun y => h2 y v) x

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Ingredient `LiftResidualWeakStatement` (corrected form): the spatial identity with a
forcing term, the corrected statement, and its proof. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

section Spatial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The spatial identity of the weak formulation with a continuous forcing. -/
theorem liftResidual_spatial_identity (ν : ℝ) (b : Vec 2 → Vec 2) (a da g : Vec 2 → E)
    (A : Vec 2 → Fin 2 → E) (φ : Vec 2 → E)
    (ha : ContDiff ℝ 2 a) (hb : Continuous b) (hap : AVenhance.IsZ2Periodic a) (hda : Continuous da)
    (hg : Continuous g)
    (hA : ∀ k, ContDiff ℝ 1 (fun x => A x k)) (hAp : ∀ k, AVenhance.IsZ2Periodic (fun x => A x k))
    (hφ : ContDiff ℝ 1 φ) (hφp : AVenhance.IsZ2Periodic φ)
    (hstrong : ∀ x, da x + ∑ j : Fin 2, b x j • gradE a x j -
      divE (fun y => ν • gradE a y + A y) x = g x) :
    (∫ x in AVenhance.unitCube, (-(∑ k : Fin 2, b x k * inner ℝ (gradE a x k) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (gradE a x k) (gradE φ x k)
        - ∑ k : Fin 2, inner ℝ (A x k + 0) (gradE φ x k) + inner ℝ (g x) (φ x))) =
      ∫ x in AVenhance.unitCube, inner ℝ (da x) (φ x) := by
  have hz : ∀ k : Fin 2, ContDiff ℝ 1 (fun x : Vec 2 => ((0 : Vec 2 → Fin 2 → E) x) k) :=
    fun k => contDiff_const
  have hzp : ∀ k : Fin 2, AVenhance.IsZ2Periodic (fun x : Vec 2 => ((0 : Vec 2 → Fin 2 → E) x) k) :=
    fun k n x => rfl
  have h0 : ∀ x, divE (0 : Vec 2 → Fin 2 → E) x = 0 := by
    intro x; simp [divE]
  have key := macroWeak_spatial_identity ν b a (fun x => da x - g x) A 0 φ ha hap
    (hda.sub hg) hA hAp hz hzp hφ hφp (fun x => by
      rw [h0, ← hstrong x]; abel)
  have hc0 := macroWeak_spatial_continuous ν b a A 0 φ (ha.of_le (by norm_num)) hb
    (fun k => (hA k).continuous) (fun k => continuous_const) hφ
  have hi := AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable
  have I0 := hi _ hc0
  have I1 : Integrable (fun x => inner ℝ (g x) (φ x)) (volume.restrict AVenhance.unitCube) :=
    hi _ (hg.inner hφ.continuous)
  have I2 : Integrable (fun x => inner ℝ (da x) (φ x)) (volume.restrict AVenhance.unitCube) :=
    hi _ (hda.inner hφ.continuous)
  have e : (fun x => (-(∑ k : Fin 2, b x k * inner ℝ (gradE a x k) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (gradE a x k) (gradE φ x k)
        - ∑ k : Fin 2, inner ℝ (A x k + 0) (gradE φ x k) + inner ℝ (g x) (φ x))) =
      fun x => (-(∑ k : Fin 2, b x k * inner ℝ (gradE a x k) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (gradE a x k) (gradE φ x k)
        - ∑ k : Fin 2, inner ℝ (A x k + (0 : Vec 2 → Fin 2 → E) x k) (gradE φ x k) +
          inner ℝ (0 : E) (φ x)) + inner ℝ (g x) (φ x) := by
    funext x; simp
  rw [e, integral_add I0 I1, key]
  simp only [inner_sub_left]
  rw [integral_sub I2 I1]
  ring

/-- The integrand of the weak identity with forcing is continuous. -/
theorem liftResidual_spatial_continuous (ν : ℝ) (b : Vec 2 → Vec 2) (a g : Vec 2 → E)
    (A : Vec 2 → Fin 2 → E) (φ : Vec 2 → E) (ha : ContDiff ℝ 1 a) (hb : Continuous b)
    (hA : ∀ k, Continuous (fun x => A x k)) (hg : Continuous g) (hφ : ContDiff ℝ 1 φ) :
    Continuous (fun x => -(∑ k : Fin 2, b x k * inner ℝ (gradE a x k) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (gradE a x k) (gradE φ x k)
        - ∑ k : Fin 2, inner ℝ (A x k + 0) (gradE φ x k) + inner ℝ (g x) (φ x)) := by
  have h := macroWeak_spatial_continuous ν b a A 0 φ ha hb hA (fun k => continuous_const) hφ
  have h2 := h.add (hg.inner hφ.continuous)
  refine h2.congr fun x => ?_
  simp

end Spatial

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Ingredient `MacroWeakFromStrongStatement`: integrate the strong macro equation against
periodic tests, with all integrability clauses of the weak identity. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

theorem macroWeak_orderedDerivative_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Vec 2 → E) : orderedDerivative (fun i : Fin 0 => i.elim0) g = g := by
  simp [orderedDerivative]

/-- Ingredient: the strong mean equation gives the macro weak equation. -/
theorem macroWeakFromStrong : MacroWeakFromStrongStatement := by
  intro hr _ _ _ _ _ _ D Dm bw j₀ F dZ dRep dUh hR hSM
  unfold Frame.macroWeak Frame.weakEquation
  intro w t ht φ hφ hper
  have hsubI : Set.Ioc F.tp t ⊆ Set.Icc F.tp F.tf := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hK : 2 ≤ F.Naux - 2 * F.p - 2 := by have := hR.reserve; omega
  have hfa := hR.prepared.field w
  have hA2 : ∀ s ∈ Set.Icc F.tp F.tf, ContDiff ℝ 2 (fun y => F.aRep s y w) := fun s hs =>
    (hfa.smooth s hs).of_le (by exact_mod_cast hK)
  have hAper : ∀ s ∈ Set.Icc F.tp F.tf, IsZ2Periodic (fun y => F.aRep s y w) := fun s hs =>
    hfa.periodic s hs
  have hdaC : ∀ s ∈ Set.Icc F.tp F.tf, Continuous (fun y => dRep s y w) := fun s hs =>
    ((hR.prepared.derivativeBound w).smooth s hs).continuous
  have hbC : ∀ s ∈ Set.Icc F.tp F.tf, Continuous (streamVel (D.Φ (F.m - 1)) s) := fun s hs =>
    (hR.coarseDrift.smooth s hs).continuous
  have hMA := hR.fluxes F.macroFluxField (by simp) w
  have hMB := hR.fluxes F.mean (by simp) w
  have hA1 : ∀ s ∈ Set.Icc F.tp F.tf, ∀ k, ContDiff ℝ 1
      (fun y => WithLp.ofLp (F.macroFluxField w s y) k) := fun s hs k =>
    meanReduction_component (K := 1) (hMA.smooth s hs) k
  have hB1 : ∀ s ∈ Set.Icc F.tp F.tf, ∀ k, ContDiff ℝ 1
      (fun y => WithLp.ofLp (F.mean w s y) k) := fun s hs k =>
    meanReduction_component (K := 1) (hMB.smooth s hs) k
  have hAp : ∀ s ∈ Set.Icc F.tp F.tf, ∀ k, IsZ2Periodic
      (fun y => WithLp.ofLp (F.macroFluxField w s y) k) := fun s hs k n x =>
    congrArg (fun z : PiLp 2 (fun _ : Fin 2 => hr w.1.root) => WithLp.ofLp z k) (hMA.periodic s hs n x)
  have hBp : ∀ s ∈ Set.Icc F.tp F.tf, ∀ k, IsZ2Periodic
      (fun y => WithLp.ofLp (F.mean w s y) k) := fun s hs k n x =>
    congrArg (fun z : PiLp 2 (fun _ : Fin 2 => hr w.1.root) => WithLp.ofLp z k) (hMB.periodic s hs n x)
  have hcont : ∀ s ∈ Set.Icc F.tp F.tf, Continuous (fun x =>
      -(∑ k : Fin 2, streamVel (D.Φ (F.m - 1)) s x k *
          inner ℝ (gradE (fun y => F.aRep s y w) x k) (φ x))
        - D.κ (F.m - 1) * ∑ k : Fin 2, inner ℝ (gradE (fun y => F.aRep s y w) x k)
          (gradE φ x k)
        - ∑ k : Fin 2, inner ℝ (WithLp.ofLp (F.macroFluxField w s x) k +
          WithLp.ofLp (F.mean w s x) k) (gradE φ x k) + inner ℝ (0 : hr w.1.root) (φ x)) :=
    fun s hs => macroWeak_spatial_continuous _ _ _ _ _ _ ((hA2 s hs).of_le (by norm_num))
      (hbC s hs) (fun k => (hA1 s hs k).continuous) (fun k => (hB1 s hs k).continuous) hφ1
  have hspatial : ∀ᵐ s ∂(volume.restrict (Set.Ioc F.tp t)),
      (∫ x in AVenhance.unitCube,
        (-(∑ k : Fin 2, streamVel (D.Φ (F.m - 1)) s x k *
          inner ℝ (gradE (fun y => F.aRep s y w) x k) (φ x))
        - D.κ (F.m - 1) * ∑ k : Fin 2, inner ℝ (gradE (fun y => F.aRep s y w) x k)
          (gradE φ x k)
        - ∑ k : Fin 2, inner ℝ (WithLp.ofLp (F.macroFluxField w s x) k +
          WithLp.ofLp (F.mean w s x) k) (gradE φ x k) + inner ℝ (0 : hr w.1.root) (φ x))) =
      ∫ x in AVenhance.unitCube, inner ℝ (dRep s x w) (φ x) := by
    have h1 : ∀ᵐ s ∂(volume.restrict (Set.Ioc F.tp t)),
        ∀ x v, F.macroResidual dRep s x v = F.meanDiv s x v :=
      ae_restrict_of_ae_restrict_of_subset hsubI hSM
    filter_upwards [h1, ae_restrict_mem measurableSet_Ioc] with s hs hsI
    have hsI' := hsubI hsI
    exact macroWeak_spatial_identity (D.κ (F.m - 1)) (streamVel (D.Φ (F.m - 1)) s)
      (fun x => F.aRep s x w) (fun x => dRep s x w)
      (fun x => WithLp.ofLp (F.macroFluxField w s x)) (fun x => WithLp.ofLp (F.mean w s x)) φ
      (hA2 s hsI') (hAper s hsI') (hdaC s hsI') (hA1 s hsI') (hAp s hsI') (hB1 s hsI')
      (hBp s hsI') hφ1 hper (fun x => hs x w)
  have hB : ∃ B : ℝ → ℝ, IntegrableOn B (Set.Icc F.tp F.tf) ∧
      ∀ s ∈ Set.Icc F.tp F.tf, ∀ x ∈ AVenhance.unitCube, ‖dRep s x w‖ ≤ B s := by
    obtain ⟨B, hBi, hBb⟩ := (hR.prepared.derivativeBound w).bound 0 (Nat.zero_le _)
      (fun i : Fin 0 => i.elim0)
    refine ⟨B, hBi, fun s hs x hx => ?_⟩
    have := hBb s hs x hx
    rwa [macroWeak_orderedDerivative_zero] at this
  have hat : Integrable (fun x => inner ℝ (F.aRep t x w) (φ x))
      (volume.restrict AVenhance.unitCube) :=
    AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable _
      ((hA2 t ht).continuous.inner hφ.continuous)
  have hatp : Integrable (fun x => inner ℝ (F.aRep F.tp x w) (φ x))
      (volume.restrict AVenhance.unitCube) :=
    AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable _
      ((hA2 F.tp ⟨le_rfl, ht.1.trans ht.2⟩).continuous.inner hφ.continuous)
  obtain ⟨hP, hEq, hInt⟩ := macroWeakTime F.tp F.tf t ht (fun s x => F.aRep s x w)
    (fun s x => dRep s x w) φ hφ.continuous
    (fun x s hs => hR.prepared.valuePrimitive w s hs x)
    (hR.prepared.derivativeBound w).measurable hB hat hatp
  unfold AVRegularity.CoupledWeakIdentity
  dsimp only
  refine ⟨hat, hatp, fun s hs => ?_, ?_, ?_⟩
  · exact AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable _ (hcont s (hsubI hs))
  · exact hInt.congr (hspatial.mono fun s h => h.symm)
  · rw [hEq]
    exact integral_congr_ae (hspatial.mono fun s h => h.symm)

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Frame step of `ReadoutStrongEquationStatement`: the classical data of `Regularity` for one
component of the readout field give the hypotheses `RoStrData` of the abstract core, and the
core's conclusion is the strong readout equation for that component. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

theorem roStr_orderedDerivative_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : DerivativeWord2 0) (g : Vec 2 → E) : orderedDerivative w g = g := by
  simp [orderedDerivative]

theorem roStr_divE_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G H : Vec 2 → Fin 2 → E) (x : Vec 2) (hG : ∀ k, DifferentiableAt ℝ (fun y => G y k) x)
    (hH : ∀ k, DifferentiableAt ℝ (fun y => H y k) x) :
    divE (fun y => G y + H y) x = divE G x + divE H x := by
  unfold divE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (fun y => (G y + H y) k) = fun y => G y k + H y k := rfl
  rw [this, fderiv_fun_add (hG k) (hH k)]
  rfl

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The hypotheses of the abstract core, for one component of the readout field. -/
theorem roStr_frame_data (F : Frame D hr Dm bw j₀) (dZ dRep dUh : F.Field)
    (hReg : Regularity F dZ dRep dUh) (v : CompIn F.G.comps) :
    RoStrData F.tp F.tf (D.κ (F.m - 1)) (streamVel (D.Φ (F.m - 1)))
      (fun t x => F.aZ t x v) (fun t x => dZ t x v) (F.readFlux v) := by
  have hres := hReg.reserve
  have hfld := hReg.readout.field v
  have hder := hReg.readout.derivativeBound v
  have hfl : ∀ s ∈ Set.Icc F.tp F.tf, ContDiff ℝ 1 (F.readFlux v s) := fun s hs => by
    have := (hReg.fluxes F.readFlux (by simp) v).smooth s hs
    exact_mod_cast this
  refine ⟨fun s hs => ?_, fun s hs => hfld.periodic s hs, fun s hs => (hder.smooth s hs).continuous,
    fun s hs => hder.periodic s hs, fun s hs => (hReg.coarseDrift.smooth s hs).continuous,
    fun s hs => hReg.coarseDrift.periodic s hs, fun s hs k => ?_, fun s hs k => ?_,
    fun x s hs => hReg.readout.valuePrimitive v s hs x, hder.measurable, ?_⟩
  · exact (hfld.smooth s hs).of_le (by exact_mod_cast (show 2 ≤ F.Naux - 2 by omega))
  · exact (contDiff_piLp 2).1 (hfl s hs) k
  · intro n x
    exact congrArg (fun z => z k) ((hReg.fluxes F.readFlux (by simp) v).periodic s hs n x)
  · obtain ⟨B, hB, hb⟩ := hder.bound 0 (Nat.zero_le _) (fun i => i.elim0)
    exact ⟨B, hB, fun s hs x hx => by
      have := hb s hs x hx
      rwa [roStr_orderedDerivative_zero] at this⟩

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end

section
section
/-! Ingredient `LiftResidualWeakStatement` (corrected form with the nondegenerate time scale):
statement and proof. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

/-- `LiftResidualWeakStatement` with the extra hypothesis that the cell time scale of level `m`
is nonzero (needed for time locality of the complete lift). -/
def LiftResidualWeakStatementNondeg : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (F : Frame D hr Dm bw j₀)
    (dZ dRep dUh : F.Field), D.cellScaleSq F.m ≠ 0 → Regularity F dZ dRep dUh →
      F.StrongMean dRep → F.plainWeak dRep dUh

theorem liftResidualWeak_nondeg : LiftResidualWeakStatementNondeg := by
  intro hr _ _ _ _ _ _ D Dm bw j₀ F dZ dRep dUh hc hR hSM
  unfold Frame.plainWeak Frame.weakEquation
  intro w t ht φ hφ hper
  have hsubI : Set.Ioc F.tp t ⊆ Set.Icc F.tp F.tf := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hK : 2 ≤ Dm + 4 - 2 := by omega
  have hfa := hR.lifted.field w
  have hA2 : ∀ s ∈ Set.Icc F.tp F.tf, ContDiff ℝ 2 (fun y => F.uh s y w) := fun s hs =>
    (hfa.smooth s hs).of_le (by exact_mod_cast hK)
  have hAper : ∀ s ∈ Set.Icc F.tp F.tf, IsZ2Periodic (fun y => F.uh s y w) := fun s hs =>
    hfa.periodic s hs
  have hdaC : ∀ s ∈ Set.Icc F.tp F.tf, Continuous (fun y => dUh s y w) := fun s hs =>
    ((hR.lifted.derivativeBound w).smooth s hs).continuous
  have hbC : ∀ s ∈ Set.Icc F.tp F.tf, Continuous (streamVel (D.Φ F.m) s) := fun s hs =>
    (hR.fineDrift.smooth s hs).continuous
  have hMA := hR.fluxes F.plain (by simp) w
  have hgS := hR.sources (F.physSource dRep dUh) (by simp) w
  have hgC : ∀ s ∈ Set.Icc F.tp F.tf, Continuous (fun y => F.physSource dRep dUh s y w) :=
    fun s hs => (hgS.smooth s hs).continuous
  have hA1 : ∀ s ∈ Set.Icc F.tp F.tf, ∀ k, ContDiff ℝ 1
      (fun y => WithLp.ofLp (F.plain w s y) k) := fun s hs k =>
    meanReduction_component (K := 1) (hMA.smooth s hs) k
  have hAp : ∀ s ∈ Set.Icc F.tp F.tf, ∀ k, IsZ2Periodic
      (fun y => WithLp.ofLp (F.plain w s y) k) := fun s hs k n x =>
    congrArg (fun z : PiLp 2 (fun _ : Fin 2 => hr w.1.root) => WithLp.ofLp z k) (hMA.periodic s hs n x)
  have hspatial : ∀ᵐ s ∂(volume.restrict (Set.Ioc F.tp t)),
      (∫ x in AVenhance.unitCube,
        (-(∑ k : Fin 2, streamVel (D.Φ F.m) s x k *
          inner ℝ (gradE (fun y => F.uh s y w) x k) (φ x))
        - D.κ F.m * ∑ k : Fin 2, inner ℝ (gradE (fun y => F.uh s y w) x k)
          (gradE φ x k)
        - ∑ k : Fin 2, inner ℝ (WithLp.ofLp (F.plain w s x) k + 0) (gradE φ x k)
        + inner ℝ (F.physSource dRep dUh s x w) (φ x))) =
      ∫ x in AVenhance.unitCube, inner ℝ (dUh s x w) (φ x) := by
    have h1 : ∀ᵐ s ∂(volume.restrict (Set.Ioc F.tp t)),
        ∀ x v, F.macroResidual dRep s x v = F.meanDiv s x v :=
      ae_restrict_of_ae_restrict_of_subset hsubI hSM
    filter_upwards [h1, ae_restrict_mem measurableSet_Ioc] with s hs hsI
    have hsI' := hsubI hsI
    exact liftResidual_spatial_identity (D.κ F.m) (streamVel (D.Φ F.m) s)
      (fun x => F.uh s x w) (fun x => dUh s x w) (fun x => F.physSource dRep dUh s x w)
      (fun x => WithLp.ofLp (F.plain w s x)) φ
      (hA2 s hsI') (hbC s hsI') (hAper s hsI') (hdaC s hsI') (hgC s hsI') (hA1 s hsI')
      (hAp s hsI') hφ1 hper (fun x => liftResidual_pointwise F hc dRep dUh s hs x w)
  have hB : ∃ B : ℝ → ℝ, IntegrableOn B (Set.Icc F.tp F.tf) ∧
      ∀ s ∈ Set.Icc F.tp F.tf, ∀ x ∈ AVenhance.unitCube, ‖dUh s x w‖ ≤ B s := by
    obtain ⟨B, hBi, hBb⟩ := (hR.lifted.derivativeBound w).bound 0 (Nat.zero_le _)
      (fun i : Fin 0 => i.elim0)
    refine ⟨B, hBi, fun s hs x hx => ?_⟩
    have := hBb s hs x hx
    rwa [macroWeak_orderedDerivative_zero] at this
  have hat : Integrable (fun x => inner ℝ (F.uh t x w) (φ x))
      (volume.restrict AVenhance.unitCube) :=
    AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable _
      ((hA2 t ht).continuous.inner hφ.continuous)
  have hatp : Integrable (fun x => inner ℝ (F.uh F.tp x w) (φ x))
      (volume.restrict AVenhance.unitCube) :=
    AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable _
      ((hA2 F.tp ⟨le_rfl, ht.1.trans ht.2⟩).continuous.inner hφ.continuous)
  obtain ⟨hP, hEq, hInt⟩ := macroWeakTime F.tp F.tf t ht (fun s x => F.uh s x w)
    (fun s x => dUh s x w) φ hφ.continuous
    (fun x s hs => hR.lifted.valuePrimitive w s hs x)
    (hR.lifted.derivativeBound w).measurable hB hat hatp
  unfold AVRegularity.CoupledWeakIdentity
  dsimp only
  refine ⟨hat, hatp, fun s hs => ?_, ?_, ?_⟩
  · exact AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable _
      (liftResidual_spatial_continuous (D.κ F.m) (streamVel (D.Φ F.m) s)
        (fun x => F.uh s x w) (fun x => F.physSource dRep dUh s x w)
        (fun x => WithLp.ofLp (F.plain w s x)) φ ((hA2 s (hsubI hs)).of_le (by norm_num))
        (hbC s (hsubI hs)) (fun k => (hA1 s (hsubI hs) k).continuous) (hgC s (hsubI hs)) hφ1)
  · exact hInt.congr (hspatial.mono fun s h => h.symm)
  · rw [hEq]
    exact integral_congr_ae (hspatial.mono fun s h => h.symm)

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! The ingredient `ReadoutStrongEquationStatement` of covariance transport: the tested readout
equation gives the classical common-time equation. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- One component: the strong readout equation at almost every time. -/
theorem roStr_component (F : Frame D hr Dm bw j₀) (dZ dRep dUh : F.Field)
    (hReg : Regularity F dZ dRep dUh) (hW : F.readoutWeak) (hle : F.tp ≤ F.tf)
    (v : CompIn F.G.comps) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc F.tp F.tf)), ∀ x,
      F.coarseRes dZ t x v = divE (fun y => WithLp.ofLp (F.readFlux v t y)) x := by
  have hData := roStr_frame_data F dZ dRep dUh hReg v
  have hweak : ∀ t ∈ Set.Icc F.tp F.tf, ∀ φ : Vec 2 → hr v.1.root, ContDiff ℝ (⊤ : ℕ∞) φ →
      AVenhance.IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ (F.m - 1)) F.tp t
        (streamVel (D.Φ (F.m - 1))) (fun x => F.aZ t x v) (fun x => F.aZ F.tp x v) φ
        (fun k x => gradE φ x k) (fun s k x => gradE (fun y => F.aZ s y v) x k)
        0 (F.readFlux v) 0 := fun t ht φ hφ hφp => hW v t ht φ hφ hφp
  filter_upwards [roStr_defect_ae_zero hle hData hweak,
    ae_restrict_mem measurableSet_Icc] with t ht htI x
  have h0 := ht x
  unfold roStrDefect roStrR at h0
  beta_reduce at h0
  have ha2 : ContDiff ℝ 2 (fun y => F.aZ t y v) := ((hReg.readout.field v).smooth t htI).of_le
    (by exact_mod_cast (show 2 ≤ F.Naux - 2 by have := hReg.reserve; omega))
  have hga : ∀ k, DifferentiableAt ℝ (fun y => (D.κ (F.m - 1) • gradE (fun y' => F.aZ t y' v) y) k) x :=
    fun k => (((roStr_grad_contDiff ha2 k).const_smul _).differentiable one_ne_zero) x
  have hfl : ∀ k, DifferentiableAt ℝ (fun y => roStrFlux (F.readFlux v) t y k) x := fun k => by
    have h1 : ContDiff ℝ 1 (F.readFlux v t) := by
      have := (hReg.fluxes F.readFlux (by simp) v).smooth t htI
      exact_mod_cast this
    exact (((contDiff_piLp 2).1 h1 k).differentiable one_ne_zero) x
  have hdiv := roStr_divE_add (fun y => D.κ (F.m - 1) • gradE (fun y' => F.aZ t y' v) y)
    (roStrFlux (F.readFlux v) t) x hga hfl
  have h1 := sub_eq_zero.1 h0
  unfold Frame.coarseRes
  have hD2 : divE (roStrFlux (F.readFlux v) t) x =
      divE (fun y => WithLp.ofLp (F.readFlux v t y)) x := rfl
  rw [hdiv, hD2] at h1
  rw [h1]
  abel

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

/-- The tested readout equation gives the common-time classical readout equation. -/
theorem readoutStrongEquation : ReadoutStrongEquationStatement := by
  intro hr _ _ _ _ _ _ D Dm bw j₀ F dZ dRep dUh hReg _ hW
  unfold Frame.StrongReadout
  by_cases hle : F.tp ≤ F.tf
  · have hv := fun v => roStr_component F dZ dRep dUh hReg hW hle v
    filter_upwards [ae_all_iff.2 hv] with t ht x v using ht v x
  · rw [Set.Icc_eq_empty hle]
    simp

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end

section
/-! The prepared time derivative representative is `P_p dZ + 𝒜 (P_{p-1} aZ)` almost everywhere. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.CycleComparison.Coarse
  Set Filter
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The covariance rate matrix `J - κ_{m-1} I` of the frame. -/
def S130rate (F : Frame D hr Dm bw j₀) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t - D.κ (F.m - 1) • 1

/-- Almost every time the readout jets have good time derivatives up to order `2p`. -/
theorem readout_good (F : Frame D hr Dm bw j₀) {dZ dRep dUh : F.Field}
    (Q : Regularity F dZ dRep dUh) (hab : F.tp ≤ F.tf) (v : CompIn F.G.comps) :
    ∀ᵐ t ∂(volume.restrict (Icc F.tp F.tf)),
      HasWordTimeDerivAt (F.p * 2) (fun s y => F.aZ s y v) (fun s y => dZ s y v) t := by
  have hres := Q.reserve
  have hae : ∀ (n : ℕ) (w : DerivativeWord2 n), ∀ᵐ t ∂(volume.restrict (Icc F.tp F.tf)),
      n ≤ F.p * 2 → ∀ x, HasDerivAt (fun s => orderedDerivative w (fun y => F.aZ s y v) x)
        (orderedDerivative w (fun y => dZ t y v) x) t := fun n w => by
    by_cases hn : n ≤ F.p * 2
    · filter_upwards [native_classical_curve_moving_word F Q.readout hab w (by omega) v] with
        t ht _ x
      have := ht (fun _ => x) 0 (hasDerivAt_const t x)
      simpa using this
    · exact Filter.Eventually.of_forall fun t h => absurd h hn
  have hall := ae_all_iff.2 fun n => ae_all_iff.2 fun w => hae n w
  filter_upwards [hall, ae_restrict_mem measurableSet_Icc] with t ht hmem
  refine ⟨?_, fun n w hn x => ht n w hn x⟩
  exact ((Q.readout.derivativeBound v).smooth t hmem).of_le (by exact_mod_cast (by omega))

theorem dRep_eq (F : Frame D hr Dm bw j₀) {dZ dRep dUh : F.Field}
    (Q : Regularity F dZ dRep dUh)
    (hid : ∀ t ∈ Icc F.tp F.tf, ∀ x v, F.aRep t x v = menuCovPRep F.Mn D F.m F.p F.aZ t x v) :
    ∀ᵐ t ∂(volume.restrict (Icc F.tp F.tf)), ∀ x v, dRep t x v =
      AVRegularity.covPolyP (menuCovPrimitive D F.Mn F.m t) F.p (fun y => dZ t y v) x +
        AVRegularity.covOperator (S130rate F t)
          (PolyLow (menuCovPrimitive D F.Mn F.m t) F.p (fun y => F.aZ t y v)) x := by
  by_cases hab : F.tp ≤ F.tf
  swap
  · rw [Set.Icc_eq_empty hab, Measure.restrict_empty]
    simp
  have hres := Q.reserve
  have hgood := ae_all_iff.2 fun v => readout_good F Q hab v
  have hends : ∀ᵐ t ∂(volume.restrict (Icc F.tp F.tf)), t ∉ ({F.tp, F.tf} : Set ℝ) := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    have e : {a : ℝ | ¬ a ∉ ({F.tp, F.tf} : Set ℝ)} = {F.tp, F.tf} := by ext; simp; tauto
    rw [e]
    exact (Set.toFinite ({F.tp, F.tf} : Set ℝ)).measure_zero volume
  filter_upwards [hgood, hends, Q.prepared.derivative, Q.covarianceDerivative,
    ae_restrict_mem measurableSet_Icc] with t hg he hd hcov hmem
  have hIoo : t ∈ Ioo F.tp F.tf := by
    refine ⟨lt_of_le_of_ne hmem.1 ?_, lt_of_le_of_ne hmem.2 ?_⟩
    · exact fun h => he (by simp [h])
    · exact fun h => he (by simp [h])
  intro x v
  have hf : ∀ s ∈ Icc F.tp F.tf, ContDiff ℝ ((F.p * 2 : ℕ) : WithTop ℕ∞) (fun y => F.aZ s y v) :=
    fun s hs => ((Q.readout.field v).smooth s hs).of_le (by exact_mod_cast (by omega))
  have hD := hasDerivAt_covPolyP hIoo (menuCovPrimitive D F.Mn F.m) (S130rate F)
    (fun i j => hcov i j) (f := fun s y => F.aZ s y v) (df := fun s y => dZ s y v) F.p hf (hg v) x
  have hev : (fun s => AVRegularity.covPolyP (menuCovPrimitive D F.Mn F.m s) F.p
      (fun y => F.aZ s y v) x) =ᶠ[nhds t] fun s => F.aRep s x v := by
    filter_upwards [Icc_mem_nhds hIoo.1 hIoo.2] with s hs
    rw [hid s hs x v]; rfl
  have hRep : HasDerivAt (fun s => F.aRep s x v) (dRep t x v) t :=
    hasDerivAt_pi.1 (hd x) v
  have hu := (hD.congr_of_eventuallyEq hev.symm).unique hRep
  rw [← hu]
  have hc1 : ContDiff ℝ ((F.p * 2 + 2 : ℕ) : WithTop ℕ∞) (fun y => F.aZ t y v) :=
    ((Q.readout.field v).smooth t hmem).of_le (by exact_mod_cast (by omega))
  have hc2 : ContDiff ℝ ((F.p * 2 : ℕ) : WithTop ℕ∞) (fun y => dZ t y v) :=
    ((Q.readout.derivativeBound v).smooth t hmem).of_le (by exact_mod_cast (by omega))
  exact dPoly_eq _ _ F.p hc1 hc2 x

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
section
/-! Native budgets: algebra of window bounds (finite sums, sums of two, negatives, differences). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- Finite sums of window bounds are window bounds of the same order. -/
theorem ClassicalWindowBound.sum_fintype
    {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {K : ℕ} {f : ι → ℝ → Vec 2 → V}
    (Q : ∀ i, ClassicalWindowBound a b K (f i)) :
    ClassicalWindowBound a b K (fun t x => ∑ i, f i t x) := by
  classical
  have hpi := ClassicalWindowBound.pi (V := fun _ : ι => V) Q
  have hs := hpi.map (∑ i : ι, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => V) i)
  simpa only [sum_apply, ContinuousLinearMap.proj_apply] using hs

/-- Sums of two window bounds. -/
theorem ClassicalWindowBound.add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {K : ℕ} {f g : ℝ → Vec 2 → V}
    (hf : ClassicalWindowBound a b K f) (hg : ClassicalWindowBound a b K g) :
    ClassicalWindowBound a b K (fun t x => f t x + g t x) := by
  have h := ClassicalWindowBound.sum_fintype (ι := Fin 2) (f := ![f, g])
    (fun i => by fin_cases i <;> simpa)
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- Negatives of window bounds. -/
theorem ClassicalWindowBound.neg
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → V} (hf : ClassicalWindowBound a b K f) :
    ClassicalWindowBound a b K (fun t x => -f t x) := by
  have h := hf.map (-ContinuousLinearMap.id ℝ V)
  simpa using h

/-- Differences of window bounds. -/
theorem ClassicalWindowBound.sub
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {K : ℕ} {f g : ℝ → Vec 2 → V}
    (hf : ClassicalWindowBound a b K f) (hg : ClassicalWindowBound a b K g) :
    ClassicalWindowBound a b K (fun t x => f t x - g t x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- A window bound only needs its order lowered. -/
theorem ClassicalWindowBound.mono
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {a b : ℝ} {K L : ℕ} {f : ℝ → Vec 2 → V} (hf : ClassicalWindowBound a b K f) (h : L ≤ K) :
    ClassicalWindowBound a b L f :=
  ⟨fun t ht => (hf.smooth t ht).of_le (Nat.cast_le.mpr h), hf.periodic, hf.measurable,
    fun n hn w => hf.bound n (hn.trans h) w⟩

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native budgets, brick 1: a product (Leibniz) lemma for `ClassicalWindowBound`. A coefficient
with values in continuous linear maps and uniform spatial jet bounds, applied to a field with a
window bound, again has a window bound at the same order. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- Spatial jets of a window-bounded field have integrable cell budgets, valid at every
point, in the operator norm of the iterated derivative. -/
theorem nativeBudget_jet_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → V}
    (Q : ClassicalWindowBound a b K f) (n : ℕ) (hn : n ≤ K) :
    ∃ B : ℝ → ℝ, IntegrableOn B (Icc a b) ∧
      ∀ t ∈ Icc a b, ∀ x, ‖iteratedFDeriv ℝ n (f t) x‖ ≤ B t := by
  classical
  choose B hB hb using fun w : DerivativeWord2 n => Q.global_bound n hn w
  refine ⟨fun t => ∑ w : DerivativeWord2 n, |B (fun i => w (Fin.rev i)) t|, ?_,
    fun t ht x => ?_⟩
  · exact integrable_finsetSum _ (fun w _ => (hB _).abs)
  · have hfn : ContDiff ℝ (n : ℕ∞) (f t) := (Q.smooth t ht).of_le (Nat.cast_le.mpr hn)
    refine (ChartTransport.norm_le_sum_basisVec _).trans (Finset.sum_le_sum fun w _ => ?_)
    have he := congrFun (AVRegularity.orderedDerivative_eq_iteratedFDeriv
      (fun i => w (Fin.rev i)) hfn) x
    simp only [Fin.rev_rev] at he
    rw [← he]
    exact (hb _ t ht x).trans (le_abs_self _)

/-- Uniform window data for a coefficient with values in continuous linear maps: smoothness,
periodicity, joint measurability and constant spatial jet bounds. -/
structure NativeUniformCoeff {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace V] [MeasurableSpace W]
    (a b : ℝ) (K : ℕ) (A : ℝ → Vec 2 → V →L[ℝ] W) : Prop where
  smooth : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (A t)
  periodic : ∀ t ∈ Icc a b, IsZ2Periodic (A t)
  measurable : Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Icc a b} => A z.1.1 z.1.2)
  bound : ∀ n ≤ K, ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x, ‖iteratedFDeriv ℝ n (A t) x‖ ≤ C

/-- An ordered derivative word is bounded by the norm of the iterated derivative. -/
theorem nativeBudget_word_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (g : Vec 2 → E) (hg : ContDiff ℝ (n : ℕ∞) g) (w : DerivativeWord2 n) (x : Vec 2) :
    ‖orderedDerivative w g x‖ ≤ ‖iteratedFDeriv ℝ n g x‖ := by
  rw [congrFun (AVRegularity.orderedDerivative_eq_iteratedFDeriv w hg) x]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have : ∏ i, ‖basisVec (w (Fin.rev i))‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      fun i _ => AVRegularity.CycleComparison.Coarse.norm_basisVec_le_one _
  calc _ ≤ ‖iteratedFDeriv ℝ n g x‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

/-- The product (Leibniz) lemma: a coefficient with uniform window data applied to a field with
a window bound has the window bound of the same order. -/
theorem ClassicalWindowBound.clm_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    {a b : ℝ} {K : ℕ} {A : ℝ → Vec 2 → V →L[ℝ] W} {f : ℝ → Vec 2 → V}
    (hA : NativeUniformCoeff a b K A) (hf : ClassicalWindowBound a b K f) :
    ClassicalWindowBound a b K (fun t x => A t x (f t x)) := by
  classical
  refine ⟨fun t ht => (hA.smooth t ht).clm_apply (hf.smooth t ht),
    fun t ht n x => by simp only [hA.periodic t ht n x, hf.periodic t ht n x], ?_, ?_⟩
  · have hc : Continuous (fun p : (V →L[ℝ] W) × V => p.1 p.2) :=
      isBoundedBilinearMap_apply.continuous
    exact hc.measurable.comp (hA.measurable.prodMk hf.measurable)
  · intro n hn w
    have hC : ∀ i : Fin (n + 1), ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x,
        ‖iteratedFDeriv ℝ i (A t) x‖ ≤ C := fun i => hA.bound i (by omega)
    have hB : ∀ i : Fin (n + 1), ∃ B : ℝ → ℝ, IntegrableOn B (Icc a b) ∧
        ∀ t ∈ Icc a b, ∀ x, ‖iteratedFDeriv ℝ (n - i) (f t) x‖ ≤ B t :=
      fun i => nativeBudget_jet_norm_le hf (n - i) (by omega)
    choose C hC using hC
    choose B hB hBb using hB
    refine ⟨fun t => ∑ i : Fin (n + 1), (n.choose i : ℝ) * |C i| * |B i t|, ?_, ?_⟩
    · exact integrable_finsetSum _ fun i _ => ((hB i).abs).const_mul _
    · intro t ht x _
      have hKn : (n : ℕ∞ω) ≤ (K : ℕ∞ω) := Nat.cast_le.mpr hn
      have hgd : ContDiff ℝ (n : ℕ∞) (fun y => A t y (f t y)) :=
        ((hA.smooth t ht).clm_apply (hf.smooth t ht)).of_le (Nat.cast_le.mpr hn)
      refine (nativeBudget_word_norm_le _ hgd w x).trans ?_
      refine (norm_iteratedFDeriv_clm_apply (hA.smooth t ht) (hf.smooth t ht) x hKn).trans ?_
      rw [Finset.sum_range]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 := hC i t ht x
      have h2 := hBb i t ht x
      have h3 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
      calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (A t) x‖ * ‖iteratedFDeriv ℝ (n - i) (f t) x‖
          ≤ (n.choose i : ℝ) * |C i| * |B i t| := by
            gcongr
            · exact h1.trans (le_abs_self _)
            · exact h2.trans (le_abs_self _)
        _ = _ := rfl

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end

section
section
/-! The temporal product formula of the finite covariance polynomial, from the analytic
regularity package and the identification of the prepared field. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance Set
  AVRegularity.CycleComparison.Coarse
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Product rule for the finite temporal covariance polynomial, with its last flux retained,
under the nonvanishing of the cell scale. -/
theorem temporal_product (F : Frame D hr Dm bw j₀) {dZ dRep dUh : F.Field}
    (Q : Regularity F dZ dRep dUh) (hc : D.cellScaleSq F.m ≠ 0)
    (hid : ∀ t ∈ Icc F.tp F.tf, ∀ x v, F.aRep t x v = menuCovPRep F.Mn D F.m F.p F.aZ t x v) :
    F.TemporalProduct dZ dRep := by
  have hres := Q.reserve
  filter_upwards [dRep_eq F Q hid, ae_restrict_mem measurableSet_Icc] with t hdR hmem
  intro x v
  obtain ⟨hb, hdiv⟩ := stream_smooth_div (D.hΦ (F.m - 1)) t
  have hH := Q.covarianceSymmetric t
  have hφ : ContDiff ℝ ((F.p * 2 + 2 : ℕ) : WithTop ℕ∞) (fun y => F.aZ t y v) :=
    ((Q.readout.field v).smooth t hmem).of_le (by exact_mod_cast (by omega))
  have hψ : ContDiff ℝ ((F.p * 2 : ℕ) : WithTop ℕ∞) (fun y => dZ t y v) :=
    ((Q.readout.derivativeBound v).smooth t hmem).of_le (by exact_mod_cast (by omega))
  have hG : ∀ j, ContDiff ℝ 1 (fun y => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y j) := by
    intro j
    have h := ((Q.readoutFluxRegularity v).smooth t hmem).of_le
      (show (1 : WithTop ℕ∞) ≤ ((4 * F.p + 2 : ℕ) : WithTop ℕ∞) by exact_mod_cast (by omega))
    exact (contDiff_piLp 2).1 h j
  have hg : (fun y => F.aRep t y v) =
      AVRegularity.covPolyP (menuCovPrimitive D F.Mn F.m t) F.p (fun y => F.aZ t y v) :=
    funext fun y => hid t hmem y v
  have core := core (menuCovPrimitive D F.Mn F.m t) hH (streamVel (D.Φ (F.m - 1)) t) hb hdiv
    (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t) (D.κ (F.m - 1)) F.p hφ hψ x (dRep t x v)
    (fun y => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y)
    (fun y => D.κ (F.m - 1) • gradE (fun y' => F.aRep t y' v) y +
      menuMacroFlux F.Mn F.G F.m F.N F.depth F.CcT F.aRep v t y)
    (fun y => WithLp.ofLp (F.lastFlux v t y)) hG (hdR x v)
    (fun y => flux_identity' F hc t (hid t hmem) v y) (fun y => rfl)
  have hmid : ∑ j : Fin 2, streamVel (D.Φ (F.m - 1)) t x j • gradE (fun y => F.aRep t y v) x j =
      driftDeriv (streamVel (D.Φ (F.m - 1)) t)
        (AVRegularity.covPolyP (menuCovPrimitive D F.Mn F.m t) F.p (fun y => F.aZ t y v)) x := by
    rw [hg]; rfl
  have e : F.macroResidual dRep t x v = dRep t x v + driftDeriv (streamVel (D.Φ (F.m - 1)) t)
      (AVRegularity.covPolyP (menuCovPrimitive D F.Mn F.m t) F.p (fun y => F.aZ t y v)) x -
      divE (fun y => D.κ (F.m - 1) • gradE (fun y' => F.aRep t y' v) y +
        menuMacroFlux F.Mn F.G F.m F.N F.depth F.CcT F.aRep v t y) x := by
    unfold Frame.macroResidual menuMacroRes
    rw [hmid]
  rw [e]
  exact core

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! # Two covariance-transport ingredients 

`liftResidualWeak : LiftResidualWeakStatement` and
`covarianceTemporalProduct : CovarianceTemporalProductStatement`. Both were proved under the
extra hypothesis that the cell time scale of the level is nonzero (`liftResidualWeak_nondeg`; `temporal_product`), because the complete lift is time
local only then. The frame regularity now carries that clock (`Regularity.clock_nonzero`), so
the statements follow. -/

@[expose] public section

namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- **`LiftResidualWeakStatement`**, from the nondegenerate form and the clock of the frame
regularity. -/
theorem liftResidualWeak : LiftResidualWeakStatement :=
  fun F dZ dRep dUh hR hSM => liftResidualWeak_nondeg F dZ dRep dUh hR.clock_nonzero hR hSM

/-- **`CovarianceTemporalProductStatement`**, from the product rule and the clock of the frame
regularity. -/
theorem covarianceTemporalProduct : CovarianceTemporalProductStatement :=
  fun F _ _ _ hR hid => temporal_product F hR hR.clock_nonzero hid

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end
