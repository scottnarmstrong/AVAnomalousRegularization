-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FrontierFlux.Jets
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.CycleComparison.Error.WeakSolution
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CycleComparison.Reconstruction.ClassicalBridge
import Mathlib.CategoryTheory.Countable

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.FrontierFlux

/-! The internal steps of the frontier flux.
The letter step reads only finite requested orders;
the flux estimate is separated into the pointwise/integral estimate and temporal integrability.
Its case contains exactly the data and hypotheses in the final assembly.
The degenerate cases are included: empty family and zero datum give zero; `R_w = 0` has no letter
coefficient; `J_w = 1` is the root passage. All scalar constants precede the instance and `Dm`. -/

open WeakEntryProofs WeakEntryProofs.Assembly Reduction Residual CoarseDefect

/-- The source premises of one application of the frontier flux statement.
No regularity, energy estimate or flux bound is added as a field. -/
structure Case (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) where
  Dc : ℕ
  m : ℕ
  k : ℕ
  cap : 1 + A.Jw * A.Nw ≤ Dc
  offset : m ≤ weakEntryMmax R
  reserve : k + 1 + Dc ≤ R.Kw + m
  energyOrder : k + Dc - 1 ≤ kOf R
  regularityOrder : kOf R + 3 ≤ R.Kw + m
  menuN : A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1)
  menuR : A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 <
    2 * weakAStar B.α B.q * (A.Rw + 1)
  c : WeakPassageInstance plan R
  r : WeakPassageRun c
  Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j
  Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j
  passages : ∀ j, c.M < j → j ≤ c.M + A.Jw →
    WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi j
  i : ℕ
  lower : c.M < i
  upper : i ≤ c.M + A.Jw
  input : WeakComparisonInput r i
  v₀ : CompIn (c.stage i).comps
  Fc : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
  truncation : ∀ v : CompIn (c.stage (i - 1)).comps, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
    truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) = r.Ur (i - 1) v t
  realizes : CdFcRealizes c r Dc m k
    (fun w => reserve.trans (weakReductionReserve_kw R m w)) i Uhi (cdAD c Dc i v₀) Fc

variable {plan : WeakPassagePlan}
  {kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ}
  {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

/-- The exact real mass integrand of hY in the weak reconstruction window. -/
def Case.fluxMass (x : Case plan kOf R) (t : ℝ) : ℝ :=
  massNormSq (E := fun v : CompIn (x.c.stage x.i).comps => PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
    (K := fun _ => x.k) (plan.radius R * x.c.D.eps (x.i - 1))
    (fun v : CompIn (x.c.stage x.i).comps => weakMass x.c.D A.Nw A.Jw A.η₀ v.1)
    (fun v => (x.Fc v t).val)

/-- The letter step at the largest finite requested reserve, with the plan's existing conditions. -/
def FrontierLetterStep (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) : Prop :=
  WeakPassageCommonOK plan → WeakCoarseReadoutPlanOK plan kOf →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc k : ℕ), 1 + A.Jw * A.Nw ≤ Dc → k ≤ weakEntryKmax R →
    ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ v₀ : CompIn (c.stage i).comps,
    FrontierLetterReg c r Dc k i v₀ (plan.radius R * c.D.eps (i - 1)) ∧
    frontierLetterTotal c r Dc k i v₀ (plan.radius R * c.D.eps (i - 1)) ≤
      c.D.κ c.M * (weakFluxLetterConst (plan.radius R) R *
        c.D.eps c.M ^ (2 * weakAStar B.α B.q))

/-- The factorial flux estimate, separately from square integrability of its trajectory.
The second clause is the integral of the first with the exact component masses. -/
def FrontierFluxPointwiseStep (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) : Prop :=
  WeakPassageCommonOK plan → WeakCoarseReadoutPlanOK plan kOf →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (x : Case plan kOf R),
    FrontierLetterReg x.c x.r x.Dc x.k x.i x.v₀ (plan.radius R * x.c.D.eps (x.i - 1)) →
    (∀ t ∈ Set.Icc (x.r.tq x.i) (x.r.a + A.T₀), ∀ v : CompIn (x.c.stage x.i).comps,
      ENNReal.ofReal (factorialNormSq (plan.radius R * x.c.D.eps (x.i - 1)) (x.Fc v t).val) ≤
        ENNReal.ofReal (frontierLetterTotal x.c x.r x.Dc x.k x.i x.v₀
          (plan.radius R * x.c.D.eps (x.i - 1)) ^ 2) *
        classicalGradFactorialSq (plan.radius R * x.c.D.eps (x.i - 1)) (kOf R)
          (fun y => weakFrontierField x.i A.Rw A.η₀ (x.c.stage x.i)
            (x.c.stage (x.i - 1)) (x.input.aU t) v y)) ∧
    (∫⁻ t in Set.Icc (x.r.tq x.i) (x.r.a + A.T₀), ENNReal.ofReal (x.fluxMass t)) ≤
      ENNReal.ofReal (frontierLetterTotal x.c x.r x.Dc x.k x.i x.v₀
        (plan.radius R * x.c.D.eps (x.i - 1)) ^ 2) *
      frontierDissipation x.c x.r x.i (kOf R) x.input (plan.radius R * x.c.D.eps (x.i - 1))

/-- Temporal control comes from the solved family and named frontier energy.
The pointwise bound is a separate already proved ingredient, not an integrability premise. -/
def FrontierFluxMemLpStep (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) : Prop :=
  WeakPassageCommonOK plan → WeakCoarseReadoutPlanOK plan kOf →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (x : Case plan kOf R),
    FrontierLetterReg x.c x.r x.Dc x.k x.i x.v₀ (plan.radius R * x.c.D.eps (x.i - 1)) →
    (∀ t ∈ Set.Icc (x.r.tq x.i) (x.r.a + A.T₀), ∀ v : CompIn (x.c.stage x.i).comps,
      ENNReal.ofReal (factorialNormSq (plan.radius R * x.c.D.eps (x.i - 1)) (x.Fc v t).val) ≤
        ENNReal.ofReal (frontierLetterTotal x.c x.r x.Dc x.k x.i x.v₀
          (plan.radius R * x.c.D.eps (x.i - 1)) ^ 2) *
        classicalGradFactorialSq (plan.radius R * x.c.D.eps (x.i - 1)) (kOf R)
          (fun y => weakFrontierField x.i A.Rw A.η₀ (x.c.stage x.i)
            (x.c.stage (x.i - 1)) (x.input.aU t) v y)) →
    (∀ v, MemLp (x.Fc v) 2 (volume.restrict (Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)))) ∧
    IntegrableOn x.fluxMass (Set.Icc (x.r.tq x.i) (x.r.a + A.T₀))

/-- The radius statement `WeakFrontierFluxStatement`, from the internal steps. -/

theorem weakFrontierFlux_of_steps (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseReadoutPlanOK plan kOf) (hS2 : FrontierLetterStep plan kOf)
    (hS3a : FrontierFluxPointwiseStep plan kOf) (hS3b : FrontierFluxMemLpStep plan kOf) :
    WeakFrontierFluxStatement plan kOf := by
  intro B A R Dc m k hDc hm hk hkOf hkOf3 menu1 menu2 c r Uhi Whi hpass i hi hit h v₀ Fc htrunc hreal
  have hK : k ≤ weakEntryKmax R := by
    unfold weakEntryKmax
    omega
  let x : Case plan kOf R :=
    ⟨Dc, m, k, hDc, hm, hk, hkOf, hkOf3, menu1, menu2, c, r, Uhi, Whi, hpass, i, hi, hit,
      h, v₀, Fc, htrunc, hreal⟩
  obtain ⟨hreg, hLt⟩ := hS2 hcommon hok R Dc k hDc hK c r i hi hit v₀
  obtain ⟨hpoint, hlin⟩ := hS3a hcommon hok x hreg
  obtain ⟨hmem, hint⟩ := hS3b hcommon hok x hreg hpoint
  have hI := hlin
  have hmass : ∀ t, (0 : ℝ) ≤ x.fluxMass t := by
    intro t
    change 0 ≤ massNormSq (E := fun v : CompIn (c.stage i).comps =>
      PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)) (K := fun _ => k) _ _ _
    exact massNormSq_nonneg' _ _
      (fun v : CompIn (c.stage i).comps => (weakPassageRawSetting c).mass_pos v.1) _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hmass)] at hI
  have hEn := weakCoarseFrontierEnergyAt_named hcommon hok menu1 menu2 c r i hi hit h
  have hκ : 0 < c.D.κ c.M := (weakPassageRawSetting c).kappa_pos
  have hε : 0 < c.D.eps c.M := frontier_eps_pos c c.M
  have hwin := weak_quiet_window c r i hi hit
  have hΦ0 : 0 ≤ h.Φ :=
    (by unfold weightedNorm; positivity : (0 : ℝ) ≤ _).trans
      (h.mass_bound (r.tq (i + 1)) ⟨le_rfl, hwin.2.2.1.le.trans hwin.2.1⟩)
  have hρ : 0 < plan.radius R * c.D.eps (i - 1) :=
    mul_pos (plan.radius_pos R) (frontier_eps_pos c (i - 1))
  have hΛ0 : 0 ≤ frontierLetterTotal c r Dc k i v₀ (plan.radius R * c.D.eps (i - 1)) := by
    unfold frontierLetterTotal derivativeReserveFactor
    exact Finset.sum_nonneg fun d _ => mul_nonneg ENNReal.toReal_nonneg (by positivity)
  have hCen : 0 ≤ weakCoarseReadoutConst (plan.radius R) R := weakCoarseReadoutConst_nonneg _ _
  set Y0 := weakCoarseReadoutConst (plan.radius R) R *
    c.D.eps c.M ^ (2 * weakAStar B.α B.q * A.Rw) * h.Φ with hY0def
  have hY0 : 0 ≤ Y0 := by positivity
  set Λ := frontierLetterTotal c r Dc k i v₀ (plan.radius R * c.D.eps (i - 1))
  have h1 : ENNReal.ofReal (c.D.κ c.M) * ENNReal.ofReal (∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
        massNormSq (E := fun v : CompIn (c.stage i).comps => PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
          (K := fun _ => k) (plan.radius R * c.D.eps (i - 1))
          (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (Fc v s).val)) ≤ ENNReal.ofReal (Λ ^ 2) * ENNReal.ofReal (Y0 ^ 2) := by
    calc _ ≤ ENNReal.ofReal (c.D.κ c.M) * (ENNReal.ofReal (Λ ^ 2) *
          frontierDissipation c r i (kOf R) h (plan.radius R * c.D.eps (i - 1))) :=
          mul_le_mul' le_rfl hI
      _ = ENNReal.ofReal (Λ ^ 2) * (ENNReal.ofReal (c.D.κ c.M) *
          frontierDissipation c r i (kOf R) h (plan.radius R * c.D.eps (i - 1))) := by
          rw [mul_left_comm]
      _ ≤ _ := by
          refine mul_le_mul' le_rfl ?_
          refine (frontierDissipation_le_energy c r i (kOf R) h _).trans ?_
          rw [ENNReal.ofReal_pow hY0]
          exact pow_le_pow_left' hEn 2
  rw [← ENNReal.ofReal_mul hκ.le, ← ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (sq_nonneg _))] at h1
  refine ⟨hmem, frontierFlux_real_step hκ hΛ0 hY0 h1 hLt ?_⟩
  rw [hY0def, weakFrontierFluxConst, mul_add, mul_one, Real.rpow_add hε]
  ring

/-- The lift-length statement `WeakFrontierFluxFinalStatement`, from the internal steps. -/
theorem weakFrontierFluxFinal_of_steps (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseReadoutPlanOK plan kOf) (hS2 : FrontierLetterStep plan kOf)
    (hS3a : FrontierFluxPointwiseStep plan kOf) (hS3b : FrontierFluxMemLpStep plan kOf) :
    WeakFrontierFluxFinalStatement plan kOf := by
  intro B A R Dc m k hDc hm hk hkOf hkOf3 menu1 menu2 c r Uhi Whi hpass i hi hit h v₀ Fc htrunc hreal
  have hbase := weakFrontierFlux_of_steps hcommon hok hS2 hS3a hS3b R Dc m k hDc hm hk hkOf
    hkOf3 menu1 menu2 c r Uhi Whi hpass i hi hit h v₀ Fc htrunc hreal
  have hK : k ≤ weakEntryKmax R := by unfold weakEntryKmax; omega
  let x : Case plan kOf R :=
    ⟨Dc, m, k, hDc, hm, hk, hkOf, hkOf3, menu1, menu2, c, r, Uhi, Whi, hpass, i, hi, hit,
      h, v₀, Fc, htrunc, hreal⟩
  obtain ⟨hreg, _⟩ := hS2 hcommon hok R Dc k hDc hK c r i hi hit v₀
  obtain ⟨hpoint, _⟩ := hS3a hcommon hok x hreg
  obtain ⟨_, hint⟩ := hS3b hcommon hok x hreg hpoint
  exact frontierFlux_radius_change c r i k Fc _ hint hbase

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.FrontierFlux
end

section
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.FrontierFlux

/-! The fresh one-letter edge has at most one constituent. An inherited source preserves
its word, so cannot have the endpoints of a fresh eddy letter. These facts use only the
passage classification and the birth scales, independently of the analytic coefficients. -/

open Homogenization WeakEntryProofs Construction.Preservation.FullLift

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Fresh-letter endpoints determine the weak source, including its degree. -/
theorem weakFrontierLetterSource_eq (G : GenStage D hr Dm b j₀)
    (hm : 1 ≤ G.level) (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (N R Din n : ℕ) (v₀ : CompIn G.comps) (s : WeakSource G)
    (hs : s.Valid N R Din) (hsrc : s.srcComp G.level = v₀.1)
    (htgt : s.tgtComp G.level = succComp G.level v₀.1 [.eddy n]) :
    s = .eddy v₀ [] n := by
  have hzero := InitialValue.compParent_eq_self hm (hold v₀.1 v₀.2)
  have hone := parent_word_succComp hm v₀.1 (hold v₀.1 v₀.2) [.eddy n]
  cases s with
  | inherited w h π n' =>
    have hw₀ := congrArg (compWord G.level) hsrc
    have hw₁ := congrArg (compWord G.level) htgt
    rw [WeakSource.srcComp,
      (parent_word_succComp hm π.src (hold _ (Providers.CascadeInvariants.stagePath_src_mem π hs.2.1)) w).2,
      hzero.2] at hw₀
    rw [WeakSource.tgtComp,
      (parent_word_succComp hm π.tgt (hold _ (Providers.CascadeInvariants.stagePath_tgt_mem π hs.2.1)) w).2,
      hone.2, hw₀] at hw₁
    cases hw₁
  | eddy v w n' =>
    have hv := congrArg (compParent G.level) hsrc
    have hw := congrArg (compWord G.level) hsrc
    have hn := congrArg (compWord G.level) htgt
    rw [WeakSource.srcComp, (parent_word_succComp hm v.1 (hold v.1 v.2) w).1,
      hzero.1] at hv
    rw [WeakSource.srcComp, (parent_word_succComp hm v.1 (hold v.1 v.2) w).2,
      hzero.2] at hw
    rw [WeakSource.tgtComp,
      (parent_word_succComp hm v.1 (hold v.1 v.2) (w ++ [WordLetter.eddy n'])).2,
      hone.2, hw, List.nil_append] at hn
    have hv' : v = v₀ := Subtype.ext hv
    have hn' : n' = n := by simpa only [List.singleton_inj, WordLetter.eddy.injEq] using hn
    subst v
    subst w
    subst n'
    rfl

/-- The sum of record sizes on a one-letter edge costs one eddy tag, with no
multiplicity from the inherited sources or the number of roots. -/
theorem weakFrontierLetterRecordSum_le (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din n : ℕ)
    (G G' : GenStage D hr Dm b j₀) (m : ℕ) (hlevel : G.level = m) (hp : IsWeakPassage D P Mn rW Din G G')
    (htags : G'.HasTags P) (hm : 1 ≤ G.level)
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (heps : 0 < D.eps (m - 1)) (v₀ : CompIn G.comps)
    (hv : succComp m v₀.1 [.eddy n] ∈ G'.comps) (hu : v₀.1 ∈ G'.comps) :
    (∑ γ : G'.fam.Γ ⟨succComp m v₀.1 [.eddy n], hv⟩ ⟨v₀.1, hu⟩,
      (G'.fam.identity _ _ γ).record.size) ≤
      D.eps (m - 1) ^ (-Mn.η0) * D.weakPe m ^ 2 := by
  classical
  obtain ⟨_, _, _, _, _, e, idx, Cc, Cc0, _, _, _, hd⟩ := hp
  let v : CompIn G'.comps := ⟨succComp m v₀.1 [.eddy n], hv⟩
  let u : CompIn G'.comps := ⟨v₀.1, hu⟩
  have hsource (γ : G'.fam.Γ v u) : (e v u γ).1 = .eddy v₀ [] n :=
    weakFrontierLetterSource_eq G hm hold Mn.N Mn.R Din n v₀ _
      (e v u γ).2.1 (by simpa only [hlevel] using (e v u γ).2.2.1)
      (by simpa only [hlevel] using (e v u γ).2.2.2)
  have hsize (γ : G'.fam.Γ v u) : (G'.fam.identity v u γ).record.size =
      D.eps (m - 1) ^ (-Mn.η0) * D.weakPe m ^ 2 := by
    have ht := htags v u γ
    rw [(hd v u γ).1] at ht
    rw [ht.1.1, hsource]
    simp only [WeakSource.weakTag, hlevel, Prov.tags]
  have hcard : (Finset.univ : Finset (G'.fam.Γ v u)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun γ _ γ' _ => (e v u).injective ?_
    apply Subtype.ext
    rw [hsource, hsource]
  have htag : 0 ≤ D.eps (m - 1) ^ (-Mn.η0) * D.weakPe m ^ 2 :=
    mul_nonneg (Real.rpow_nonneg heps.le _) (sq_nonneg _)
  change (∑ γ : G'.fam.Γ v u, (G'.fam.identity v u γ).record.size) ≤ _
  simp_rw [hsize]
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_of_le_one_left htag (by exact_mod_cast hcard)

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.FrontierFlux
end

section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.FrontierFlux

/-! The classical frontier is the representative of a continuous higher Sobolev curve.
The curve is available at kOf + 1 from the solved high family, not from a temporal
regularity assumption on the arbitrary realization Fc. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Reduction Residual CoarseDefect
open Construction.Preservation.FullLift CoupledEnergy.Variational

variable {plan : WeakPassagePlan}
  {kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ}
  {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

/-- The frontier at the order used by its named classical energy. -/
def Case.higherFrontier (x : Case plan kOf R) (v : CompIn (x.c.stage x.i).comps) (t : ℝ) :
    TorusHk (kOf R + 1) ℝ :=
  cdFrontier x.c x.m (kOf R + 1)
    (fun w => (show kOf R + 1 ≤ R.Kw + x.m by have := x.regularityOrder; omega).trans
      (weakReductionReserve_kw R x.m w)) x.i x.Uhi v t

/-- The higher frontier has precisely the representative that the energy statement estimates. -/
theorem Case.higherFrontier_rep (x : Case plan kOf R)
    (v : CompIn (x.c.stage x.i).comps) (t : ℝ)
    (ht : t ∈ Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)) :
    IsClassicalRep (x.higherFrontier v t)
      (weakFrontierField x.i A.Rw A.η₀ (x.c.stage x.i) (x.c.stage (x.i - 1)) (x.input.aU t) v)
      (kOf R + 1) := by
  classical
  have hrep := weakCoarseFamilyRep plan kOf R x.m x.offset x.regularityOrder x.c x.r
    x.Uhi x.i x.lower x.upper x.input x.truncation
  unfold Case.higherFrontier cdFrontier cdReadout weakFrontierField
  apply classicalRep_sum le_rfl
  intro v'
  by_cases hh : compParent x.i v'.1 = v.1 ∧ (compWord x.i v'.1).length = A.Rw
  · simp only [hh, cdWeight]
    exact classicalRep_smul _ _
      (classicalRep_truncate _ le_rfl _ _ (hrep v' t ht)) _
  · simp only [hh, ↓reduceIte]
    exact classicalRep_zero le_rfl

/-- The continuity inherited from the solved high family controls the frontier trajectory. -/
theorem Case.higherFrontier_continuousOn (x : Case plan kOf R)
    (v : CompIn (x.c.stage x.i).comps) :
    ContinuousOn (x.higherFrontier v) (Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)) := by
  classical
  have hU := (x.passages x.i x.lower x.upper).1
  have hK (w : Comp) : kOf R + 1 ≤ weakReductionReserve R x.m w :=
    (show kOf R + 1 ≤ R.Kw + x.m by have := x.regularityOrder; omega).trans
      (weakReductionReserve_kw R x.m w)
  have htr (v' : CompIn (x.c.stage (x.i - 1)).comps) :
      ContinuousOn (fun t => truncateTorusHk (E := ℝ) (hK v'.1) (x.Uhi (x.i - 1) v' t))
        (Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)) :=
    (truncateTorusHk (E := ℝ) (hK v'.1)).continuous.comp_continuousOn (hU v')
  unfold Case.higherFrontier cdFrontier cdReadout
  refine continuousOn_finsetSum _ fun v' _ => ?_
  split_ifs with hh
  · exact (htr v').const_smul (cdWeight x.c x.i v'.1)
  · exact continuousOn_const
end

/-! The literal Fc realization is the negative finite sum of Sobolev coupling fluxes.
The reserve of the input is the named frontier-energy order kOf, independent of Dc. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Reduction Residual CoarseDefect
open CoupledEnergy.Variational CoupledEnergy.Galerkin Construction.Preservation.FullLift

variable {plan : WeakPassagePlan}
  {kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ}
  {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

/-- The two component reserves for the diagonal multiplier estimate. -/
def Case.fluxReserves (x : Case plan kOf R) : Bool → ℕ := fun b => if b then kOf R else x.k

/-- Every declared AD order is admissible from the energy reserve into the output reserve. -/
def Case.fluxOrder (x : Case plan kOf R) (d : Finset.Icc 2 x.Dc) :
    admissibleOrders x.fluxReserves x.Dc false true :=
  ⟨d.1, Finset.mem_filter.mpr ⟨d.2, by
    have hd := Finset.mem_Icc.mp d.2
    have hk := x.energyOrder
    change x.k + d.1 ≤ kOf R + 2
    omega⟩⟩

/-- One Sobolev flux term against the higher frontier curve. -/
def Case.fluxTerm (x : Case plan kOf R)
    (hreg : FrontierLetterReg x.c x.r x.Dc x.k x.i x.v₀ (plan.radius R * x.c.D.eps (x.i - 1)))
    (v : CompIn (x.c.stage x.i).comps) (d : Finset.Icc 2 x.Dc)
    (t : Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)) :
    TorusHk x.k (PiLp 2 (fun _ : Fin 2 => ℝ)) :=
  torusCoupledFluxTerm (h := fun _ : Bool => ℝ) (plan.radius R * x.c.D.eps (x.i - 1))
    (mul_pos (plan.radius_pos R) (frontier_eps_pos x.c _)) x.fluxReserves x.Dc
    (x.r.tq x.i) (x.r.a + A.T₀) false true (x.fluxOrder d) (cdAD x.c x.Dc x.i x.v₀ d)
    (hreg d).1 t t.property ((hreg d).2 t t.property).1 ((hreg d).2 t t.property).2
    (x.higherFrontier v t)

/-- The raw realization of Fc equals the classical frontier flux, a.e. in space at each time. -/
theorem Case.Fc_classical_ae (x : Case plan kOf R)
    (v : CompIn (x.c.stage x.i).comps) (t : ℝ)
    (ht : t ∈ Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)) :
    (x.Fc v t).toFunction.jet (valueIndex2 x.k) =ᵐ[volume.restrict unitCube]
      fun y => -(WithLp.toLp 2 fun j : Fin 2 =>
        ∑ d : Finset.Icc 2 x.Dc, ∑ α : DerivativeWord2 (d.1 - 1),
          (cdAD x.c x.Dc x.i x.v₀ d t y (WithLp.toLp 2 (Pi.single α (1 : ℝ))) j) *
            orderedDerivative α
              (weakFrontierField x.i A.Rw A.η₀ (x.c.stage x.i) (x.c.stage (x.i - 1))
                (x.input.aU t) v) y) := by
  have hf := frontierJetsStep plan kOf R x.Dc x.m x.k x.offset x.reserve x.energyOrder
    x.regularityOrder x.c x.r x.Uhi x.i x.lower x.upper x.input x.truncation v t ht
  have hwords (d : Finset.Icc 2 x.Dc) (α : DerivativeWord2 (d.1 - 1)) :=
    hf (d.1 - 1) (by have := (Finset.mem_Icc.mp d.2).2; omega) α
  filter_upwards [x.realizes v t ht, ae_all_iff.mpr (fun d => ae_all_iff.mpr (hwords d))]
    with y hy hjets
  rw [hy]
  congr 1
  apply PiLp.ext
  intro j
  dsimp only
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun α _ => ?_
  rw [hjets d α]
  rfl

private theorem frontierOperator_expand {J : Type*} [Fintype J] [DecidableEq J]
    (L : PiLp 2 (fun _ : J => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)) (g : J → ℝ) :
    L (WithLp.toLp 2 g) = WithLp.toLp 2 (fun j => ∑ α : J,
      L (WithLp.toLp 2 (Pi.single α (1 : ℝ))) j * g α) := by
  have he : (WithLp.toLp 2 g : PiLp 2 (fun _ : J => ℝ)) =
      ∑ α : J, g α • (WithLp.toLp 2 (Pi.single α (1 : ℝ))) := by
    apply PiLp.ext
    intro β
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [he, map_sum]
  apply PiLp.ext
  intro j
  simp only [WithLp.ofLp_sum, Finset.sum_apply, map_smul, PiLp.smul_apply, smul_eq_mul, mul_comm]

/-- A coupling term has the corresponding classical coefficient-times-derivative value. -/
theorem Case.fluxTerm_classical_ae (x : Case plan kOf R)
    (hreg : FrontierLetterReg x.c x.r x.Dc x.k x.i x.v₀ (plan.radius R * x.c.D.eps (x.i - 1)))
    (v : CompIn (x.c.stage x.i).comps) (d : Finset.Icc 2 x.Dc)
    (t : Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)) :
    (x.fluxTerm hreg v d t).toFunction.jet (valueIndex2 x.k) =ᵐ[volume.restrict unitCube]
      fun y => WithLp.toLp 2 fun j : Fin 2 =>
        ∑ α : DerivativeWord2 (d.1 - 1),
          (cdAD x.c x.Dc x.i x.v₀ d t y (WithLp.toLp 2 (Pi.single α (1 : ℝ))) j) *
            orderedDerivative α
              (weakFrontierField x.i A.Rw A.η₀ (x.c.stage x.i) (x.c.stage (x.i - 1))
                (x.input.aU t) v) y := by
  have hterm := torusCoupledFluxTerm_value_ae (h := fun _ : Bool => ℝ)
    (plan.radius R * x.c.D.eps (x.i - 1))
    (mul_pos (plan.radius_pos R) (frontier_eps_pos x.c _)) x.fluxReserves x.Dc
    (x.r.tq x.i) (x.r.a + A.T₀) false true (x.fluxOrder d) (cdAD x.c x.Dc x.i x.v₀ d)
    (hreg d).1 t t.property ((hreg d).2 t t.property).1 ((hreg d).2 t t.property).2
    (x.higherFrontier v t)
  change (x.fluxTerm hreg v d t).val (valueIndex2 x.k) =ᵐ[volume.restrict unitCube] _ at hterm
  have hd : d.1 - 1 ≤ kOf R + 1 := by
    have := (Finset.mem_Icc.mp d.2).2
    have := x.energyOrder
    omega
  have hjets (α : DerivativeWord2 (d.1 - 1)) :
      (x.higherFrontier v t).val ⟨⟨d.1 - 1, Nat.lt_succ_of_le hd⟩, α⟩ =ᵐ[volume.restrict unitCube]
        orderedDerivative α
          (weakFrontierField x.i A.Rw A.η₀ (x.c.stage x.i) (x.c.stage (x.i - 1))
            (x.input.aU t) v) := by
    have hr := (x.higherFrontier_rep v t t.property).2.2.2 (d.1 - 1) hd α
    have hv := KernelEnergy.torusHk_toFunction_jet_ae (x.higherFrontier v t)
      ⟨⟨d.1 - 1, Nat.lt_succ_of_le hd⟩, α⟩
    unfold torusJetOrder at hr
    simp only [hd, ↓reduceDIte] at hr
    exact hv.symm.trans hr
  filter_upwards [KernelEnergy.torusHk_toFunction_jet_ae (x.fluxTerm hreg v d t) (valueIndex2 x.k),
    hterm, ae_all_iff.mpr hjets] with y hy hvalue hword
  rw [hy, hvalue]
  change (cdAD x.c x.Dc x.i x.v₀ d t y)
    (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) =>
      (x.higherFrontier v t).val ⟨⟨d.1 - 1, Nat.lt_succ_of_le hd⟩, α⟩ y) = _
  have he : (fun α : DerivativeWord2 (d.1 - 1) =>
      (x.higherFrontier v t).val ⟨⟨d.1 - 1, Nat.lt_succ_of_le hd⟩, α⟩ y) =
      fun α => orderedDerivative α
        (weakFrontierField x.i A.Rw A.η₀ (x.c.stage x.i) (x.c.stage (x.i - 1))
          (x.input.aU t) v) y := funext hword
  rw [he]
  exact frontierOperator_expand _ _

/-- Spatial realization uniquely identifies Fc with the finite Sobolev flux sum. -/
theorem Case.Fc_eq_fluxSum (x : Case plan kOf R)
    (hreg : FrontierLetterReg x.c x.r x.Dc x.k x.i x.v₀ (plan.radius R * x.c.D.eps (x.i - 1)))
    (v : CompIn (x.c.stage x.i).comps) (t : Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)) :
    x.Fc v t = -(∑ d : Finset.Icc 2 x.Dc, x.fluxTerm hreg v d t) := by
  classical
  apply KernelEnergy.torusCarrier_eq_of_value_ae
  have hsum := KernelEnergy.torusJet_sum_ae_of_eq (fun d => x.fluxTerm hreg v d t)
    (valueIndex2 x.k) _ (fun d => x.fluxTerm_classical_ae hreg v d t)
  have hn := KernelEnergy.torusJet_smul_ae (-1 : ℝ)
    (∑ d : Finset.Icc 2 x.Dc, x.fluxTerm hreg v d t) (valueIndex2 x.k)
  simp only [neg_one_smul] at hn
  filter_upwards [x.Fc_classical_ae v t t.property, hsum, hn] with y hy hs hneg
  rw [hy, hneg, hs]
  congr 1
  apply PiLp.ext
  intro j
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
end

/-! The finite-order seminorm price of a fresh eddy coefficient. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Reduction Residual CycleJointProofs

private theorem letterSeminorm_const_smul {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ℝ) (k : ℕ) (a b z : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F) :
    coefficientSeminorm ρ k a b (fun t x => z • A t x) =
      ENNReal.ofReal |z| * coefficientSeminorm ρ k a b A := by
  have hnorm (j : ℕ) (t : ℝ) (x : Vec 2) :
      (‖coefficientDerivativeArray (fun y => z • A t y) j x‖₊ : ℝ≥0∞) =
        ENNReal.ofReal |z| * (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞) := by
    rw [coefficientDerivativeArray_const_smul, nnnorm_smul, ENNReal.coe_mul]
    congr 1
    exact ENNReal.ofReal_coe_nnreal.symm
  unfold coefficientSeminorm
  simp_rw [hnorm, ← ENNReal.mul_iSup, ← mul_assoc, mul_comm _ (ENNReal.ofReal |z|), mul_assoc]
  exact (Finset.mul_sum _ _ _).symm

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- A fixed fresh-letter edge has the eddy record price after multiplying by its readout weight. -/
theorem weakFrontierFreshCoeff_price (hcommon : WeakPassageCommonOK plan)
    (c : WeakPassageInstance plan R)
    (hfloor : weakEntryPassageCoeffFloor R ≤ c.M) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps) (n d k : ℕ)
    (hd : 2 ≤ d) (hk : k ≤ weakEntryKmax R) (a b rad : ℝ)
    (hrad : 0 < rad) (hrad1 : rad ≤ 1)
    (hv : succComp i v₀.1 [.eddy n] ∈ (c.stage (i - 1)).comps)
    (hu : v₀.1 ∈ (c.stage (i - 1)).comps) :
    coefficientSeminorm (rad * c.D.eps (i - 1)) k a b
      (fun t x => ∑ γ : (c.stage (i - 1)).fam.Γ ⟨succComp i v₀.1 [.eddy n], hv⟩ ⟨v₀.1, hu⟩,
        (c.D.eps (i - 1) ^ A.η₀) • (c.stage (i - 1)).physCoeff _ _ γ d t x) ≤
      ENNReal.ofReal (weakRawCK R * c.D.κ c.M * c.D.weakPe i ^ 2 * c.D.eps (i - 1) ^ (d - 2)) := by
  classical
  let S := weakPassageRawSetting c
  let v : CompIn (c.stage (i - 1)).comps := ⟨succComp i v₀.1 [.eddy n], hv⟩
  let u : CompIn (c.stage (i - 1)).comps := ⟨v₀.1, hu⟩
  have hε : 0 < c.D.eps (i - 1) := S.eps_pos _
  have hκ : 0 ≤ c.D.κ c.M := S.kappa_pos.le
  have hη : 0 < c.D.eps (i - 1) ^ A.η₀ := Real.rpow_pos_of_pos hε _
  have hreg := weakPassage_coeffRegular hcommon c (i - 1) (show c.M ≤ i - 1 by omega) (show i - 1 < c.M + A.Jw by omega)
  have hlev : (c.stage i).level = i := by
    have hh := (partB_stage_invariant c (c.M + A.Jw - i) (by omega)).1
    rwa [show c.M + A.Jw - (c.M + A.Jw - i) = i by omega] at hh
  have hold : ∀ v ∈ (c.stage i).comps, ∀ e ∈ v.births, i ≤ e.scale := by
    have hh := (partB_stage_invariant c (c.M + A.Jw - i) (by omega)).2.1
    rwa [show c.M + A.Jw - (c.M + A.Jw - i) = i by omega] at hh
  have hsize := weakFrontierLetterRecordSum_le c.P _ _ _ n (c.stage i) (c.stage (i - 1)) i hlev
    (c.construction.2.2 i hi hit).1 (c.construction.2.2 i hi hit).2
    (by rw [hlev]; omega) (by rw [hlev]; exact hold)
    hε v₀ hv hu
  have hsum : coefficientSeminorm (rad * c.D.eps (i - 1)) k a b
      (fun t x => ∑ γ : (c.stage (i - 1)).fam.Γ v u,
        c.D.eps (i - 1) ^ A.η₀ • (c.stage (i - 1)).physCoeff v u γ d t x) ≤
      ∑ γ : (c.stage (i - 1)).fam.Γ v u,
        ENNReal.ofReal (c.D.eps (i - 1) ^ A.η₀ * (weakRawCK R *
          ((c.stage (i - 1)).fam.identity v u γ).record.size * c.D.κ c.M *
            c.D.eps (i - 1) ^ (d - 2))) := by
    refine (CycleComparison.Error.coefficientSeminorm_finset_sum_le Finset.univ _
      (mul_pos hrad hε).le k a b _ (fun γ _ t _ => (hreg v u γ k d a b).2.1 t |>.const_smul _)).trans ?_
    refine Finset.sum_le_sum fun γ _ => ?_
    rw [letterSeminorm_const_smul, abs_of_pos hη, ENNReal.ofReal_mul hη.le]
    refine mul_le_mul' le_rfl ?_
    exact (coefficientSeminorm_radius_mono _ (c.D.eps (i - 1)) (mul_pos hrad hε).le
      (mul_le_of_le_one_left hε.le hrad1) k a b _).trans
      (weakRaw_physCoeff_seminorm_le S hfloor (i - 1) (show c.M ≤ i - 1 by omega) (show i - 1 < c.M + A.Jw by omega) a b v u γ d hd k hk)
  refine hsum.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => mul_nonneg hη.le
    (mul_nonneg (mul_nonneg (mul_nonneg (weakRawCK_nonneg R)
      ((c.stage (i - 1)).fam.identity v u γ).record.size_nonneg) hκ) (pow_nonneg hε.le _)))]
  apply ENNReal.ofReal_le_ofReal
  have hfactor : ∑ γ : (c.stage (i - 1)).fam.Γ v u,
      c.D.eps (i - 1) ^ A.η₀ * (weakRawCK R *
        ((c.stage (i - 1)).fam.identity v u γ).record.size * c.D.κ c.M *
          c.D.eps (i - 1) ^ (d - 2)) =
      (weakRawCK R * c.D.κ c.M * c.D.eps (i - 1) ^ (d - 2)) *
        (c.D.eps (i - 1) ^ A.η₀ * ∑ γ : (c.stage (i - 1)).fam.Γ v u,
          ((c.stage (i - 1)).fam.identity v u γ).record.size) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    ring
  rw [hfactor]
  have hcanc : c.D.eps (i - 1) ^ A.η₀ * c.D.eps (i - 1) ^ (-A.η₀) = 1 := by
    rw [← Real.rpow_add hε, add_neg_cancel, Real.rpow_zero]
  calc _ ≤ (weakRawCK R * c.D.κ c.M * c.D.eps (i - 1) ^ (d - 2)) *
        (c.D.eps (i - 1) ^ A.η₀ * (c.D.eps (i - 1) ^ (-A.η₀) * c.D.weakPe i ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsize hη.le)
        (mul_nonneg (mul_nonneg (weakRawCK_nonneg R) hκ) (pow_nonneg hε.le _))
    _ = _ := by
      rw [← mul_assoc _ _ (c.D.weakPe i ^ 2), hcanc, one_mul]
      ring
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.FrontierFlux
end
end
end

section
@[expose] public noncomputable section
section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.FrontierFlux

/-! The pointwise factorial estimate and its mass-weighted time integral. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Reduction Residual CoarseDefect
open CoupledEnergy.Variational CoupledEnergy.Galerkin CycleComparison.Coarse

variable {plan : WeakPassagePlan}
  {kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ}
  {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

/-- The classical gradient density is the full gradient norm of the higher frontier. -/
theorem Case.frontierGradient_eq (x : Case plan kOf R)
    (v : CompIn (x.c.stage x.i).comps) (t : ℝ)
    (ht : t ∈ Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)) (ρ : ℝ) :
    classicalGradFactorialSq ρ (kOf R)
      (weakFrontierField x.i A.Rw A.η₀ (x.c.stage x.i) (x.c.stage (x.i - 1)) (x.input.aU t) v) =
      ENNReal.ofReal (gradFactorialNormSq ρ (x.higherFrontier v t).val) := by
  rw [CycleComparison.Reconstruction.classicalGradFactorialSq_eq_of_rep
    (x.higherFrontier_rep v t ht) ρ le_rfl]
  congr 1
  unfold gradFactorialNormSqUpTo gradFactorialNormSq
  rw [Fin.sum_univ_succ]
  have hzero : (if 1 ≤ (0 : Fin (kOf R + 1 + 1)).val ∧
      (0 : Fin (kOf R + 1 + 1)).val ≤ kOf R + 1 then
      factorialWeight ρ ((0 : Fin (kOf R + 1 + 1)).val - 1) *
        derivativeNormSq (x.higherFrontier v t).val 0 else 0) = 0 := by simp
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  have hle : j.val + 1 ≤ kOf R + 1 := Nat.succ_le_of_lt j.isLt
  have hpos : 1 ≤ j.val + 1 := Nat.le_add_left 1 j.val
  simp only [Fin.val_succ, hpos, hle, and_self, ↓reduceIte, Nat.add_sub_cancel]
  rfl

/-- Exact finite triangle and reserve inequalities for the identified flux. -/
theorem Case.Fc_factorial_sqrt_le (x : Case plan kOf R)
    (hreg : FrontierLetterReg x.c x.r x.Dc x.k x.i x.v₀ (plan.radius R * x.c.D.eps (x.i - 1)))
    (v : CompIn (x.c.stage x.i).comps) (t : Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)) :
    Real.sqrt (factorialNormSq (plan.radius R * x.c.D.eps (x.i - 1)) (x.Fc v t).val) ≤
      frontierLetterTotal x.c x.r x.Dc x.k x.i x.v₀ (plan.radius R * x.c.D.eps (x.i - 1)) *
        Real.sqrt (gradFactorialNormSq (plan.radius R * x.c.D.eps (x.i - 1)) (x.higherFrontier v t).val) := by
  classical
  set ρ := plan.radius R * x.c.D.eps (x.i - 1)
  have hρ : 0 < ρ := mul_pos (plan.radius_pos R) (frontier_eps_pos x.c _)
  have hterm (d : Finset.Icc 2 x.Dc) := torusCoupledFluxTerm_factorialNorm_le
    (h := fun _ : Bool => ℝ) ρ hρ x.fluxReserves x.Dc (x.r.tq x.i) (x.r.a + A.T₀)
    false true (x.fluxOrder d) (cdAD x.c x.Dc x.i x.v₀ d) (hreg d).1 t t.property
    ((hreg d).2 t t.property).1 ((hreg d).2 t t.property).2 (x.higherFrontier v t)
  have hval : (∑ d : Finset.Icc 2 x.Dc, x.fluxTerm hreg v d t).val =
      ∑ d : Finset.Icc 2 x.Dc, (x.fluxTerm hreg v d t).val := by
    change (torusHkGraph (E := PiLp 2 (fun _ : Fin 2 => ℝ)) x.k).toSubmodule.subtypeL
      (∑ d, x.fluxTerm hreg v d t) = _
    exact map_sum _ _ _
  rw [x.Fc_eq_fluxSum hreg v t]
  change Real.sqrt (factorialNormSq ρ (-(∑ d : Finset.Icc 2 x.Dc, x.fluxTerm hreg v d t).val)) ≤ _
  rw [← factorialWeightedJet_norm, factorialWeightedJet_neg, norm_neg, factorialWeightedJet_norm, hval]
  refine (factorialNorm_sum_le ρ Finset.univ (fun d => (x.fluxTerm hreg v d t).val)).trans ?_
  calc _ ≤ ∑ d : Finset.Icc 2 x.Dc,
        ((coefficientSeminorm ρ x.k (x.r.tq x.i) (x.r.a + A.T₀)
          (cdAD x.c x.Dc x.i x.v₀ d)).toReal * derivativeReserveFactor ρ x.k (d.1 - 2)) *
            Real.sqrt (gradFactorialNormSq ρ (x.higherFrontier v t).val) :=
      Finset.sum_le_sum fun d _ => hterm d
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- The pointwise flux estimate; temporal measurability is a separate theorem. -/
theorem Case.Fc_factorial_le (x : Case plan kOf R)
    (hreg : FrontierLetterReg x.c x.r x.Dc x.k x.i x.v₀ (plan.radius R * x.c.D.eps (x.i - 1)))
    (t : ℝ) (ht : t ∈ Set.Icc (x.r.tq x.i) (x.r.a + A.T₀))
    (v : CompIn (x.c.stage x.i).comps) :
    ENNReal.ofReal (factorialNormSq (plan.radius R * x.c.D.eps (x.i - 1)) (x.Fc v t).val) ≤
      ENNReal.ofReal (frontierLetterTotal x.c x.r x.Dc x.k x.i x.v₀
        (plan.radius R * x.c.D.eps (x.i - 1)) ^ 2) *
      classicalGradFactorialSq (plan.radius R * x.c.D.eps (x.i - 1)) (kOf R)
        (weakFrontierField x.i A.Rw A.η₀ (x.c.stage x.i) (x.c.stage (x.i - 1)) (x.input.aU t) v) := by
  have h := x.Fc_factorial_sqrt_le hreg v ⟨t, ht⟩
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (factorialNormSq_nonneg _ _), mul_pow,
    Real.sq_sqrt (gradFactorialNormSq_nonneg _ _)] at hs
  rw [x.frontierGradient_eq v t ht, ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hs

/-- The gradient density is measurable on the window, from the continuous higher curve. -/
theorem Case.frontierGradient_aemeasurable (x : Case plan kOf R)
    (v : CompIn (x.c.stage x.i).comps) (ρ : ℝ) :
    AEMeasurable (fun t => classicalGradFactorialSq ρ (kOf R)
      (weakFrontierField x.i A.Rw A.η₀ (x.c.stage x.i) (x.c.stage (x.i - 1)) (x.input.aU t) v))
      (volume.restrict (Set.Icc (x.r.tq x.i) (x.r.a + A.T₀))) := by
  have hc := (continuous_gradFactorialNormSq ρ (kOf R)).comp_continuousOn
    (continuous_subtype_val.comp_continuousOn (x.higherFrontier_continuousOn v))
  have hm := (hc.aestronglyMeasurable_of_isCompact (μ := volume) isCompact_Icc measurableSet_Icc).aemeasurable.ennreal_ofReal
  apply hm.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (x.frontierGradient_eq v t ht ρ).symm

/-- The factorial flux estimate, including the exact finite mass sum and time integral. -/
theorem frontierFluxPointwiseStep (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ) :
    FrontierFluxPointwiseStep plan kOf := by
  intro _hcommon _hok B A R x hreg
  refine ⟨x.Fc_factorial_le hreg, ?_⟩
  let ρ := plan.radius R * x.c.D.eps (x.i - 1)
  let Λ := frontierLetterTotal x.c x.r x.Dc x.k x.i x.v₀ ρ
  let π := fun v : CompIn (x.c.stage x.i).comps => weakMass x.c.D A.Nw A.Jw A.η₀ v.1
  let G := fun (v : CompIn (x.c.stage x.i).comps) (t : ℝ) => classicalGradFactorialSq ρ (kOf R)
    (weakFrontierField x.i A.Rw A.η₀ (x.c.stage x.i) (x.c.stage (x.i - 1)) (x.input.aU t) v)
  have hπ (v) : 0 < π v := (weakPassageRawSetting x.c).mass_pos v.1
  have hm (t : ℝ) (ht : t ∈ Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)) :
      ENNReal.ofReal (x.fluxMass t) ≤ ENNReal.ofReal (Λ ^ 2) * ∑ v, ENNReal.ofReal ((π v)⁻¹) * G v t := by
    unfold Case.fluxMass massNormSq
    rw [ENNReal.ofReal_sum_of_nonneg (fun v _ =>
      mul_nonneg (inv_nonneg.mpr (hπ v).le) (factorialNormSq_nonneg _ _))]
    simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr (hπ _).le)]
    calc _ ≤ ∑ v, ENNReal.ofReal ((π v)⁻¹) * (ENNReal.ofReal (Λ ^ 2) * G v t) :=
        Finset.sum_le_sum fun v _ => mul_le_mul' le_rfl (x.Fc_factorial_le hreg t ht v)
      _ = ENNReal.ofReal (Λ ^ 2) * ∑ v, ENNReal.ofReal ((π v)⁻¹) * G v t := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ac_rfl
  calc _ ≤ ∫⁻ t in Set.Icc (x.r.tq x.i) (x.r.a + A.T₀),
        ENNReal.ofReal (Λ ^ 2) * ∑ v, ENNReal.ofReal ((π v)⁻¹) * G v t :=
      setLIntegral_mono' measurableSet_Icc hm
    _ = ENNReal.ofReal (Λ ^ 2) *
        ∑ v, ENNReal.ofReal ((π v)⁻¹) * ∫⁻ t in Set.Icc (x.r.tq x.i) (x.r.a + A.T₀), G v t := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum' Finset.univ
          (f := fun v t => ENNReal.ofReal ((π v)⁻¹) * G v t)
          (fun v _ => aemeasurable_const.mul (x.frontierGradient_aemeasurable v ρ))]
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := rfl
end

/-! The uniform bounded-order letter estimate, with the weak cap independent of Dc. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Reduction Residual CycleJointProofs Comparison

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- Joint measurability, smoothness and periodicity of the finite letter sum. -/
theorem weakFrontierAD_regular (hcommon : WeakPassageCommonOK plan)
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (Dc k : ℕ) (v₀ : CompIn (c.stage i).comps) (d : Finset.Icc 2 Dc) (a b : ℝ) :
    Measurable (fun z : Set.Icc a b × Vec 2 => cdAD c Dc i v₀ d z.1 z.2) ∧
    (∀ t, ContDiff ℝ (k : ℕ) (cdAD c Dc i v₀ d t)) ∧
    ∀ t, IsZ2Periodic (cdAD c Dc i v₀ d t) := by
  classical
  have hreg := weakPassage_coeffRegular hcommon c (i - 1)
    (show c.M ≤ i - 1 by omega) (show i - 1 < c.M + A.Jw by omega)
  refine ⟨?_, ?_, ?_⟩
  · unfold cdAD
    refine Finset.measurable_sum _ fun n _ => ?_
    split_ifs with h
    · exact Finset.measurable_sum _ fun γ _ => (hreg _ _ γ k d.1 a b).1.const_smul (c.D.eps (i - 1) ^ A.η₀)
    · exact measurable_const
  · intro t
    unfold cdAD
    refine ContDiff.sum fun n _ => ?_
    split_ifs with h
    · exact ContDiff.sum fun γ _ => ((hreg _ _ γ k d.1 a b).2.1 t).const_smul _
    · exact contDiff_const
  · intro t z y
    unfold cdAD
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with h
    · exact Finset.sum_congr rfl fun γ _ =>
        congrArg (fun p => (c.D.eps (i - 1) ^ A.η₀) • p) ((hreg _ _ γ k d.1 a b).2.2.1 t z y)
    · rfl

/-- The physical order support of AD is the fixed weak cap, rather than Dc. -/
theorem weakFrontierAD_zero_above (c : WeakPassageInstance plan R)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (Dc : ℕ) (v₀ : CompIn (c.stage i).comps) (d : Finset.Icc 2 Dc)
    (hd : 1 + A.Jw * A.Nw < d.1) : cdAD c Dc i v₀ d = fun _ _ => 0 := by
  classical
  funext t x
  unfold cdAD
  refine Finset.sum_eq_zero fun n _ => ?_
  split_ifs with h
  · refine Finset.sum_eq_zero fun γ _ => ?_
    have ho := EntryWeakProofs.weakConstruction_output_maxOrder_bound c.P _ c.M A.Jw _ 0 c.stage
      c.construction (i - 1) (by omega) (by omega) _ _ γ
    have hz : (c.stage (i - 1)).physCoeff _ _ γ d.1 t x = 0 :=
      constituentPhysical_zero_above_max (c.stage (i - 1)).fam _ _ _
        (c.stage (i - 1)).actual _ _ γ d.1 (ho.trans_lt hd) t x
    rw [hz]
    exact smul_zero (A := PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ)) (c.D.eps (i - 1) ^ A.η₀)
  · rfl

/-- Each order costs Nw fresh eddy records, whose readout weights cancel their tag weights. -/
theorem weakFrontierAD_seminorm_le (hcommon : WeakPassageCommonOK plan)
    (c : WeakPassageInstance plan R) (hfloor : weakEntryPassageCoeffFloor R ≤ c.M)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (Dc k : ℕ)
    (hk : k ≤ weakEntryKmax R) (v₀ : CompIn (c.stage i).comps) (d : Finset.Icc 2 Dc)
    (a b rad : ℝ) (hrad : 0 < rad) (hrad1 : rad ≤ 1) :
    coefficientSeminorm (rad * c.D.eps (i - 1)) k a b (cdAD c Dc i v₀ d) ≤
      ENNReal.ofReal (A.Nw * (weakRawCK R * c.D.κ c.M * c.D.weakPe i ^ 2 *
        c.D.eps (i - 1) ^ (d.1 - 2))) := by
  classical
  have hreg := weakPassage_coeffRegular hcommon c (i - 1)
    (show c.M ≤ i - 1 by omega) (show i - 1 < c.M + A.Jw by omega)
  let X (n : ℕ) (t : ℝ) (x : Vec 2) :
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => ℝ) :=
    if h : v₀.1 ∈ (c.stage (i - 1)).comps ∧
      succComp i v₀.1 [.eddy n] ∈ (c.stage (i - 1)).comps then
      ∑ γ : (c.stage (i - 1)).fam.Γ ⟨succComp i v₀.1 [.eddy n], h.2⟩ ⟨v₀.1, h.1⟩,
        (c.D.eps (i - 1) ^ A.η₀) • (c.stage (i - 1)).physCoeff _ _ γ d.1 t x
    else 0
  have hX (n : ℕ) (t : ℝ) : ContDiff ℝ (k : ℕ) (X n t) := by
    dsimp only [X]
    split_ifs with h
    · exact ContDiff.sum fun γ _ => ((hreg _ _ γ k d.1 a b).2.1 t).const_smul _
    · exact contDiff_const
  have hc : 0 ≤ weakRawCK R * c.D.κ c.M * c.D.weakPe i ^ 2 * c.D.eps (i - 1) ^ (d.1 - 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (weakRawCK_nonneg R)
      (weakPassageRawSetting c).kappa_pos.le) (sq_nonneg _))
      (pow_nonneg (frontier_eps_pos c _).le _)
  have hXsem (n : ℕ) : coefficientSeminorm (rad * c.D.eps (i - 1)) k a b (X n) ≤
      ENNReal.ofReal (weakRawCK R * c.D.κ c.M * c.D.weakPe i ^ 2 * c.D.eps (i - 1) ^ (d.1 - 2)) := by
    dsimp only [X]
    split_ifs with h
    · exact weakFrontierFreshCoeff_price hcommon c hfloor i hi hit v₀ n d.1 k
        (Finset.mem_Icc.mp d.2).1 hk a b rad hrad hrad1 h.2 h.1
    · rw [coefficientSeminorm_zero_function]
      exact bot_le
  have hcard : (Finset.Icc 2 (A.Nw + 1)).card = A.Nw := by
    rw [Nat.card_Icc]
    have := A.Nw_pos
    omega
  calc coefficientSeminorm (rad * c.D.eps (i - 1)) k a b (cdAD c Dc i v₀ d)
      ≤ ∑ n ∈ Finset.Icc 2 (A.Nw + 1), coefficientSeminorm (rad * c.D.eps (i - 1)) k a b (X n) :=
        CycleComparison.Error.coefficientSeminorm_finset_sum_le _ _
          (mul_pos hrad (frontier_eps_pos c _)).le k a b X (fun n _ t _ => hX n t)
    _ ≤ _ := by
      apply (Finset.sum_le_sum fun n _ => hXsem n).trans_eq
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hc), Finset.sum_const, hcard, nsmul_eq_mul]

/-- The normalized letter total before the Péclet scale estimate. -/
theorem weakFrontierLetterTotal_le (hcommon : WeakPassageCommonOK plan)
    (c : WeakPassageInstance plan R) (hfloor : weakEntryPassageCoeffFloor R ≤ c.M)
    (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (Dc k : ℕ) (hk : k ≤ weakEntryKmax R) (v₀ : CompIn (c.stage i).comps)
    (rad : ℝ) (hrad : 0 < rad) (hrad1 : rad ≤ 1) :
    frontierLetterTotal c r Dc k i v₀ (rad * c.D.eps (i - 1)) ≤
      (A.Nw * c.D.κ c.M * c.D.weakPe i ^ 2) * weakRawEdgeConst rad R := by
  classical
  set C := A.Nw * weakRawCK R * c.D.κ c.M * c.D.weakPe i ^ 2
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (weakRawCK_nonneg R)) (weakPassageRawSetting c).kappa_pos.le) (sq_nonneg _)
  let S : Finset (Finset.Icc 2 Dc) := Finset.univ.filter (fun d => d.1 ≤ 1 + A.Jw * A.Nw)
  have hterm (d : Finset.Icc 2 Dc) :
      (coefficientSeminorm (rad * c.D.eps (i - 1)) k (r.tq i) (r.a + A.T₀)
        (cdAD c Dc i v₀ d)).toReal * derivativeReserveFactor (rad * c.D.eps (i - 1)) k (d.1 - 2) ≤
      C * (rad⁻¹ ^ (d.1 - 2) * ((weakEntryKmax R + (d.1 - 2)).factorial : ℝ)) := by
    have hs := weakFrontierAD_seminorm_le hcommon c hfloor i hi hit Dc k hk v₀ d
      (r.tq i) (r.a + A.T₀) rad hrad hrad1
    have hs' : coefficientSeminorm (rad * c.D.eps (i - 1)) k (r.tq i) (r.a + A.T₀)
        (cdAD c Dc i v₀ d) ≤ ENNReal.ofReal (C * c.D.eps (i - 1) ^ (d.1 - 2)) := by
      convert hs using 1
      dsimp only [C]
      congr 1
      ring
    have hr := ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg hC (pow_nonneg (frontier_eps_pos c _).le _)) hs'
    have hρ : 0 < rad * c.D.eps (i - 1) := mul_pos hrad (frontier_eps_pos c _)
    have hreserve : 0 ≤ derivativeReserveFactor (rad * c.D.eps (i - 1)) k (d.1 - 2) := by
      unfold derivativeReserveFactor
      positivity
    exact (mul_le_mul_of_nonneg_right hr hreserve).trans
      (edge_order_term_le _ _ _ hC (frontier_eps_pos c _) hrad (d.1 - 2) _ _ hk)
  have hcut : frontierLetterTotal c r Dc k i v₀ (rad * c.D.eps (i - 1)) =
      ∑ d ∈ S, (coefficientSeminorm (rad * c.D.eps (i - 1)) k (r.tq i) (r.a + A.T₀)
        (cdAD c Dc i v₀ d)).toReal * derivativeReserveFactor (rad * c.D.eps (i - 1)) k (d.1 - 2) := by
    unfold frontierLetterTotal
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d _ hd
    have hd' : 1 + A.Jw * A.Nw < d.1 := by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hd
    rw [weakFrontierAD_zero_above c i hi hit Dc v₀ d hd', coefficientSeminorm_zero_function,
      ENNReal.toReal_zero, zero_mul]
  have hsum : ∑ d ∈ S, rad⁻¹ ^ (d.1 - 2) * ((weakEntryKmax R + (d.1 - 2)).factorial : ℝ) ≤
      ∑ n ∈ Finset.range (A.Jw * A.Nw), rad⁻¹ ^ n * ((weakEntryKmax R + n).factorial : ℝ) := by
    have himg := Finset.sum_image (s := S)
      (f := fun n : ℕ => rad⁻¹ ^ n * ((weakEntryKmax R + n).factorial : ℝ))
      (g := fun d : Finset.Icc 2 Dc => d.1 - 2) (fun d _ d' _ hdd => by
        have h1 := (Finset.mem_Icc.mp d.2).1
        have h2 := (Finset.mem_Icc.mp d'.2).1
        change d.1 - 2 = d'.1 - 2 at hdd
        exact Subtype.ext (by omega))
    rw [← himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ =>
      mul_nonneg (pow_nonneg (inv_nonneg.mpr hrad.le) _) (Nat.cast_nonneg _)
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    have h1 := (Finset.mem_Icc.mp d.2).1
    have h2 := (Finset.mem_filter.mp hd).2
    exact Finset.mem_range.mpr (by omega)
  rw [hcut]
  calc _ ≤ ∑ d ∈ S, C * (rad⁻¹ ^ (d.1 - 2) * ((weakEntryKmax R + (d.1 - 2)).factorial : ℝ)) :=
      Finset.sum_le_sum fun d _ => hterm d
    _ ≤ C * ∑ n ∈ Finset.range (A.Jw * A.Nw), rad⁻¹ ^ n * ((weakEntryKmax R + n).factorial : ℝ) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by unfold weakRawEdgeConst; dsimp only [C]; ring
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.FrontierFlux
end
end
end

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.FrontierFlux

/-! The letter step of the frontier flux at all requested orders, with the original named letter constant. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Reduction Residual CycleJointProofs

/-- The Péclet square has the extra two powers of the weak scale gain. -/
theorem weakFrontierPeclet_sq_le {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) :
    c.D.weakPe i ^ 2 ≤ weakFluxScaleConst B ^ 2 * c.D.eps c.M ^ (2 * weakAStar B.α B.q) := by
  have h128 : 128 ≤ A.Λ := (plan.base_ge B).trans c.base_ge
  have hPe : c.D.weakPe i ≤ weakFluxScaleConst B * c.D.eps (i - 1) ^ weakAStar B.α B.q := by
    have hh := (EntryScales.weak_scales_core B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq).choose_spec.2
      A.Λ h128 c.M (c.D.κ c.M) c.band.1 i hi
    simpa only [OCData.weakPe, OCData.kap, c.terminal, min_eq_right hi.le, OCData.eps, c.alpha,
      c.q_eq, c.base_eq, weakAStar, weakFluxScaleConst] using hh.1
  have hPe0 : 0 ≤ c.D.weakPe i := by
    have hν : 0 < c.D.κ c.M := (weakPassageRawSetting c).kappa_pos
    unfold OCData.weakPe OCData.kap
    rw [c.terminal, min_eq_right hi.le]
    exact div_nonneg (Real.rpow_nonneg (frontier_eps_pos c i).le _) hν.le
  have hEx : c.D.eps (i - 1) ≤ c.D.eps c.M := by
    simpa only [OCData.eps, c.q_eq, c.base_eq] using
      EntryScales.epsilon_antitone B.hq.1 h128 (by omega : c.M ≤ i - 1)
  have hastar : 0 ≤ weakAStar B.α B.q := by
    unfold weakAStar
    exact mul_nonneg (by linarith only [B.hq.1])
      (Scales.admissible_exponent_facts B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq).1.le
  have hh := pow_le_pow_left₀ hPe0 hPe 2
  rw [mul_pow, ← Real.rpow_natCast (c.D.eps (i - 1) ^ weakAStar B.α B.q) 2,
    ← Real.rpow_mul (frontier_eps_pos c (i - 1)).le] at hh
  have hpow : c.D.eps (i - 1) ^ (weakAStar B.α B.q * (2 : ℕ)) ≤
      c.D.eps c.M ^ (2 * weakAStar B.α B.q) := by
    rw [Nat.cast_ofNat, mul_comm]
    exact Real.rpow_le_rpow (frontier_eps_pos c (i - 1)).le hEx (mul_nonneg (by norm_num) hastar)
  exact hh.trans (mul_le_mul_of_nonneg_left hpow (sq_nonneg _))

/-- The bounded-order letter step, unconditionally from the existing common and readout plans. -/
theorem frontierLetterStep (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ) :
    FrontierLetterStep plan kOf := by
  intro hcommon hok B A R Dc k _hDc hk c r i hi hit v₀
  have hfl := hok.1.1
  have hfloor : weakEntryPassageCoeffFloor R ≤ c.M := ((hfl.2 R c.j₀).1).trans c.level_ge
  have hrad1 : plan.radius R ≤ 1 := (hfl.1 R).trans (by norm_num)
  refine ⟨?_, ?_⟩
  · intro d
    refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (weakFrontierAD_seminorm_le hcommon c hfloor i hi hit Dc k hk v₀ d
        (r.tq i) (r.a + A.T₀) _ (plan.radius_pos R) hrad1), ?_⟩
    have hr := weakFrontierAD_regular hcommon c i hi hit Dc k v₀ d (r.tq i) (r.a + A.T₀)
    exact fun t _ => ⟨hr.2.1 t, hr.2.2 t⟩
  · refine (weakFrontierLetterTotal_le hcommon c hfloor r i hi hit Dc k hk v₀
      _ (plan.radius_pos R) hrad1).trans ?_
    have hh := mul_le_mul_of_nonneg_left (weakFrontierPeclet_sq_le c i hi)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg A.Nw) (weakPassageRawSetting c).kappa_pos.le)
        (weakRawEdgeConst_nonneg (plan.radius_pos R).le R))
    convert hh using 1
    · ring
    · unfold weakFluxLetterConst
      ring
end

/-! Temporal measurability and square integrability of the realized frontier flux.
The solved high family supplies continuity; the coefficients need only joint measurability. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Reduction Residual CoarseDefect
open CoupledEnergy.Variational CoupledEnergy.Galerkin KernelEnergy CycleComparison.Coarse

private theorem frontierPositiveTensor_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    {K L : ℕ} (m : ℕ) (hm : 1 ≤ m) (hKL : K + (m - 1) ≤ L)
    (W : T → TorusHk (L + 1) ℝ) (hW : StronglyMeasurable W) :
    StronglyMeasurable (fun t => torusPositiveDerivativeTensor m hm hKL (W t)) := by
  cases m with
  | zero => omega
  | succ s =>
    change StronglyMeasurable (fun t => CoupledEnergy.Variational.torusDerivativeTensor
      (truncateTorusHk (E := ℝ) (by omega : K + (s + 1) ≤ L + 1) (W t)))
    have htr := (truncateTorusHk (E := ℝ) (by omega : K + (s + 1) ≤ L + 1)).continuous.comp_stronglyMeasurable hW
    unfold CoupledEnergy.Variational.torusDerivativeTensor CoupledEnergy.Variational.torusFamilyTensor
    refine Finset.stronglyMeasurable_fun_sum Finset.univ fun α _ => ?_
    have hd := (derivativeTorusHk α).continuous.comp_stronglyMeasurable htr
    have ht := (CoupledEnergy.Variational.mapTorusHkCLM K (CoupledEnergy.Galerkin.tensorEntryCLM α)).continuous.comp_stronglyMeasurable hd
    simpa only [CoupledEnergy.Variational.mapTorusHkCLM_apply] using ht

variable {plan : WeakPassagePlan}
  {kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ}
  {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

/-- Each finite multiplier term is strongly measurable on the closed passage window. -/
theorem Case.fluxTerm_stronglyMeasurable (hcommon : WeakPassageCommonOK plan)
    (x : Case plan kOf R)
    (hreg : FrontierLetterReg x.c x.r x.Dc x.k x.i x.v₀ (plan.radius R * x.c.D.eps (x.i - 1)))
    (v : CompIn (x.c.stage x.i).comps) (d : Finset.Icc 2 x.Dc) :
    StronglyMeasurable (x.fluxTerm hreg v d) := by
  let ρ := plan.radius R * x.c.D.eps (x.i - 1)
  have hρ : 0 < ρ := mul_pos (plan.radius_pos R) (frontier_eps_pos x.c _)
  let frontierFluxTimeEither : SecondCountableTopologyEither
      (Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)) (TorusHk (kOf R + 1) ℝ) :=
    ⟨Or.inl inferInstance⟩
  have hW : StronglyMeasurable (fun t : Set.Icc (x.r.tq x.i) (x.r.a + A.T₀) =>
      x.higherFrontier v t) :=
    (continuousOn_iff_continuous_domRestrict.mp (x.higherFrontier_continuousOn v)).stronglyMeasurable
  have hr := admissibleOrders_reserve x.fluxReserves x.Dc false true (x.fluxOrder d)
  have htensor := frontierPositiveTensor_stronglyMeasurable (d.1 - 1) hr.1 hr.2 _ hW
  have hm := (weakFrontierAD_regular hcommon x.c x.i x.lower x.upper x.Dc x.k x.v₀ d
    (x.r.tq x.i) (x.r.a + A.T₀)).1
  have hmultiply := torusMultiplier_time_stronglyMeasurable ρ hρ
    (fun t : Set.Icc (x.r.tq x.i) (x.r.a + A.T₀) => cdAD x.c x.Dc x.i x.v₀ d t) hm
    (fun t => ((hreg d).2 t t.property).1) (fun t => ((hreg d).2 t t.property).2)
    (fun l : Fin (x.k + 1) => (coefficientOrderSup (x.r.tq x.i) (x.r.a + A.T₀)
      (cdAD x.c x.Dc x.i x.v₀ d) l.val).toReal)
    (fun t l y => coefficientOrderSup_derivative_bound ρ hρ x.k (x.r.tq x.i) (x.r.a + A.T₀)
      (cdAD x.c x.Dc x.i x.v₀ d) (hreg d).1 l.val (Nat.le_of_lt_succ l.isLt)
        t t.property y) _ htensor
  exact hmultiply

/-- The arbitrary realization Fc inherits measurability by uniqueness of its spatial class. -/
theorem Case.Fc_aestronglyMeasurable (hcommon : WeakPassageCommonOK plan)
    (x : Case plan kOf R)
    (hreg : FrontierLetterReg x.c x.r x.Dc x.k x.i x.v₀ (plan.radius R * x.c.D.eps (x.i - 1)))
    (v : CompIn (x.c.stage x.i).comps) :
    AEStronglyMeasurable (x.Fc v) (volume.restrict (Set.Icc (x.r.tq x.i) (x.r.a + A.T₀))) := by
  have hsum := (Finset.stronglyMeasurable_fun_sum Finset.univ
    (fun d _ => x.fluxTerm_stronglyMeasurable hcommon hreg v d)).neg
  have he : (fun t : Set.Icc (x.r.tq x.i) (x.r.a + A.T₀) => x.Fc v t) =
      fun t => -(∑ d : Finset.Icc 2 x.Dc, x.fluxTerm hreg v d t) :=
    funext (x.Fc_eq_fluxSum hreg v)
  change StronglyMeasurable (fun t => -(∑ d : Finset.Icc 2 x.Dc, x.fluxTerm hreg v d t)) at hsum
  rw [← he] at hsum
  let F : ℝ → TorusHk x.k (PiLp 2 (fun _ : Fin 2 => ℝ)) :=
    Function.extend Subtype.val (fun t : Set.Icc (x.r.tq x.i) (x.r.a + A.T₀) => x.Fc v t) (fun _ => 0)
  have hF : StronglyMeasurable F :=
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).stronglyMeasurable_extend hsum stronglyMeasurable_const
  apply hF.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact Subtype.coe_injective.extend_apply _ _ ⟨t, ht⟩

/-- The pointwise estimate supplies finite cost, independently of measurability. -/
theorem frontierFluxMemLpStep (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ) :
    FrontierFluxMemLpStep plan kOf := by
  intro hcommon _hok B A R x hreg hpoint
  let ρ := plan.radius R * x.c.D.eps (x.i - 1)
  let Λ := frontierLetterTotal x.c x.r x.Dc x.k x.i x.v₀ ρ
  have hmem (v : CompIn (x.c.stage x.i).comps) :
      MemLp (x.Fc v) 2 (volume.restrict (Set.Icc (x.r.tq x.i) (x.r.a + A.T₀))) := by
    have hc := (continuous_gradFactorialNormSq ρ (kOf R)).comp_continuousOn
      (continuous_subtype_val.comp_continuousOn (x.higherFrontier_continuousOn v))
    have hint := hc.integrableOn_Icc (μ := volume)
    have hfin : (∫⁻ t in Set.Icc (x.r.tq x.i) (x.r.a + A.T₀),
        ENNReal.ofReal (gradFactorialNormSq ρ (x.higherFrontier v t).val)) ≠ ⊤ :=
      ne_top_of_le_ne_top hint.2.ne (lintegral_ofReal_le_lintegral_enorm _)
    apply Comparison.torusHk_memLp_of_factorial (ρ := ρ)
      (mul_pos (plan.radius_pos R) (frontier_eps_pos x.c _))
      (x.Fc_aestronglyMeasurable hcommon hreg v)
    have hbound : (∫⁻ t in Set.Icc (x.r.tq x.i) (x.r.a + A.T₀),
        ENNReal.ofReal (factorialNormSq ρ (x.Fc v t).val)) ≤ ENNReal.ofReal (Λ ^ 2) *
        ∫⁻ t in Set.Icc (x.r.tq x.i) (x.r.a + A.T₀),
          ENNReal.ofReal (gradFactorialNormSq ρ (x.higherFrontier v t).val) := by
      calc
        _ ≤ (∫⁻ t in Set.Icc (x.r.tq x.i) (x.r.a + A.T₀), ENNReal.ofReal (Λ ^ 2) *
            ENNReal.ofReal (gradFactorialNormSq ρ (x.higherFrontier v t).val)) := by
          apply setLIntegral_mono' measurableSet_Icc
          intro t ht
          exact (hpoint t ht v).trans_eq (by rw [x.frontierGradient_eq v t ht])
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hbound
  refine ⟨hmem, ?_⟩
  change Integrable (fun t => ∑ v : CompIn (x.c.stage x.i).comps,
    (weakMass x.c.D A.Nw A.Jw A.η₀ v.1)⁻¹ * factorialNormSq ρ (x.Fc v t).val)
      (volume.restrict (Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)))
  exact integrable_finsetSum _ fun v _ => (integrable_factorialNormSq_torus (hmem v)).const_mul _
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.FrontierFlux
end

section
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! The response-frontier flux at the energy radius and the window lift length, with all internal
steps proved. -/

open WeakEntryProofs.Assembly Residual

variable {plan : WeakPassagePlan}
  {kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ}

/-- The frontier flux estimate at the lift length `ε_{i-1}`. -/
theorem weakFrontierFluxFinal (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseReadoutPlanOK plan kOf) : WeakFrontierFluxFinalStatement plan kOf :=
  FrontierFlux.weakFrontierFluxFinal_of_steps hcommon hok (FrontierFlux.frontierLetterStep plan kOf)
    (FrontierFlux.frontierFluxPointwiseStep plan kOf) (FrontierFlux.frontierFluxMemLpStep plan kOf)

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end
