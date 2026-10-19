-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FluxJets
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup.Periodic
import AVRegularity.CycleJoint.PlaneWeakCurveCongruenceOn
import AVRegularity.Proofs.WeakGen.Reduction.CoeffAllOrder
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.CategoryTheory.Countable

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The block sum.** `IsCoarseDefect` from the parts `CdFluxIdentity` and
`CdIntegrable` by `coupledWeakIdentity_weighted_rows`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- A weighted finite sum of a.e. zero functions is a.e. zero. -/
theorem cd_weighted_zero_ae {J E : Type*} [Finite J] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Finset J) (lam : J → ℝ) (g : J → ℝ → Vec 2 → E) (μ : Measure (Vec 2)) (s : ℝ)
    (h : ∀ j, g j s =ᵐ[μ] 0) : (∑ j ∈ S, lam j • g j) s =ᵐ[μ] 0 := by
  have h2 := ae_all_iff.2 h
  filter_upwards [h2] with x hx
  simp [Finset.sum_apply, hx]

theorem cd_sum_smul_apply {J : Type*} (S : Finset J) (lam : J → ℝ)
    (f : J → ℝ → Fin 2 → Vec 2 → ℝ) (s : ℝ) (k : Fin 2) (x : Vec 2) :
    (∑ j ∈ S, lam j • f j) s k x = ∑ j ∈ S, lam j • f j s k x := by
  simp [Finset.sum_apply]

/-- **The block sum**: `IsCoarseDefect` at every parent, from the two open parts. -/
theorem cdIsCoarseDefect_of_parts (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (Dc m k N : ℕ) (hDc : 1 + A.Jw * A.Nw ≤ Dc) (hk : k + 1 + Dc ≤ R.Kw + m)
    (hN : N ≤ R.Kw + m)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw)
    (hp : WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi i)
    (v₀ : CompIn (c.stage i).comps)
    (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (hOc : ∀ v, CdFluxIdentity c r Dc m k (fun w => hk.trans (weakReductionReserve_kw R m w)) i
      hi hit v₀ Uhi Whi Fc v)
    (hI : ∀ v, CdIntegrable c r Dc m k (fun w => hk.trans (weakReductionReserve_kw R m w)) i
      hi hit v₀ Uhi Fc v) :
    IsCoarseDefect (r.tq i) (r.a + A.T₀) (c.D.κ c.M) (streamVel (c.D.Φ (i - 1))) Dc
      (A.Jw * A.Rw) k N (cdAD c Dc i v₀) (cdCE c Dc i hi hit)
      (fun _ => (c.D.κ c.M) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (cdF c r m N (fun w => hN.trans (weakReductionReserve_kw R m w)) i Uhi)
      (fun v t => cdW c m (k + 1 + Dc) (fun w => hk.trans (weakReductionReserve_kw R m w))
        i Uhi v t) Fc := by
  intro v t ht φ
  obtain ⟨-, -, hw, -, hrow⟩ := cdPassage_rewrite c r m Uhi Whi i hi hit hp
  have hK := fun w => hk.trans (weakReductionReserve_kw R m w)
  have hK1 : 1 ≤ k + 1 + Dc := by omega
  refine coupledWeakIdentity_weighted_rows Finset.univ (cdLam c i v) _ _ _ _ _
    (fun j => (Uhi (i - 1) j t).toFunction.jet (valueIndex2 (weakReductionReserve R m j.1)))
    (fun j => (weakStageTrace (weakPassageRawSetting c) m i (Uhi i) (r.tq i) j).toFunction.jet
      (valueIndex2 (weakReductionReserve R m j.1)))
    _ _
    (fun j s k' => (Whi (i - 1) j s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos _)⟩, fun _ => k'⟩)
    (fun j s x => cdRowFlux c m Whi i j s x)
    (fun j s => (0 : TorusHk (weakReductionReserve R m j.1)
      (PiLp 2 (fun _ : Fin 2 => ScalarH j.1.root))).toFunction.jet
        (valueIndex2 (weakReductionReserve R m j.1)))
    (fun j s => (0 : TorusHk (weakReductionReserve R m j.1) (ScalarH j.1.root)).toFunction.jet
        (valueIndex2 (weakReductionReserve R m j.1)))
    (fun j _ => hrow j t ht φ) _ _ _ _ _
    ((cdW_value_ae c m _ hK i Uhi v t)) ((cdF_value_ae c r m N _ i Uhi v))
    (fun s => cd_weighted_zero_ae _ _ _ _ _ fun j => torusHk_zero_jet_ae _ _)
    (fun s => cd_weighted_zero_ae _ _ _ _ _ fun j => torusHk_zero_jet_ae _ _)
    ?_ ?_ ?_
  · have hsub : Set.Ioc (r.tq i) t ⊆ Set.Icc (r.tq i) (r.a + A.T₀) :=
      fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
    filter_upwards [cdW_grad_ae c m _ hK hK1 i Uhi Whi _
      (fun j => ae_restrict_of_ae_restrict_of_subset hsub (hw j)) v] with s hs k'
    exact Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => by
      exact cd_sum_smul_apply _ _ _ s k' x) (hs k')
  · have hsub : Set.Ioc (r.tq i) t ⊆ Set.Icc (r.tq i) (r.a + A.T₀) :=
      fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hOc v)] with s hs
    simpa [Finset.sum_apply, cdTargetFlux] using hs
  · intro s hs
    exact hI v t ht φ s hs
end

/-! **`WeakCoarseDefectStatement` from the two parts.**

* `CdFluxIdentityAll plan`: the flux identity, for all data satisfying the hypotheses of
  `WeakCoarseDefectStatement`;
* `CdIntegrableAll plan`: integrability of the right side.

`weakCoarseDefect_of_parts : CdFluxIdentityAll plan → CdIntegrableAll plan →
WeakCoarseDefectStatement plan`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- **(Oc) for all data**: the flux identity under the hypotheses of the statement. -/
def CdFluxIdentityAll (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc m k : ℕ) (_hDc : 1 + A.Jw * A.Nw ≤ Dc) (hk : k + 1 + Dc ≤ R.Kw + m)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j),
    (∀ j, c.M < j → j ≤ c.M + A.Jw →
      WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi j) →
    ∀ (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps)
      (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))),
    CdFcRealizes c r Dc m k (fun w => hk.trans (weakReductionReserve_kw R m w)) i Uhi
      (cdAD c Dc i v₀) Fc →
    ∀ v, CdFluxIdentity c r Dc m k (fun w => hk.trans (weakReductionReserve_kw R m w)) i hi hit
      v₀ Uhi Whi Fc v

/-- **(I) for all data**: integrability of the right side. -/
def CdIntegrableAll (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc m k : ℕ) (_hDc : 1 + A.Jw * A.Nw ≤ Dc) (hk : k + 1 + Dc ≤ R.Kw + m)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j),
    (∀ j, c.M < j → j ≤ c.M + A.Jw →
      WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi j) →
    ∀ (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps)
      (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))),
    CdFcRealizes c r Dc m k (fun w => hk.trans (weakReductionReserve_kw R m w)) i Uhi
      (cdAD c Dc i v₀) Fc →
    ∀ v, CdIntegrable c r Dc m k (fun w => hk.trans (weakReductionReserve_kw R m w)) i hi hit
      v₀ Uhi Fc v

/-- **`WeakCoarseDefectStatement` from the two parts.** -/
theorem weakCoarseDefect_of_parts (plan : WeakPassagePlan) (hOc : CdFluxIdentityAll plan)
    (hI : CdIntegrableAll plan) : WeakCoarseDefectStatement plan := by
  intro B A R Dc m k N hDc hk hN c r Uhi Whi hpass i hi hit v₀ Fc hFc
  exact cdIsCoarseDefect_of_parts c r Dc m k N hDc hk hN Uhi Whi i hi hit (hpass i hi hit) v₀ Fc
    (hOc R Dc m k hDc hk c r Uhi Whi hpass i hi hit v₀ Fc hFc)
    (hI R Dc m k hDc hk c r Uhi Whi hpass i hi hit v₀ Fc hFc)
end

/-! **The statements of the flux identity**.

The weighted sum of the row fluxes (flux identity `CdFluxIdentity`) is reduced, by the algebra of
the coefficients and of the jets, to three named structural statements about the edges of the
stage `i - 1` of a weak passage:

* `CdParentMem`: the parent of a component of the stage `i - 1` is a component of the stage `i`;
* `CdInhClass`: the inherited edges, summed over the children of `v` with the readout weights, are
  `λ_{u'}` times the sum of the grade coefficients `cdCE r` at the parent of `u'` (the coefficient of
  an inherited edge `(u,w) → (v,w)` does not depend on `w`);
* `CdEddClass`: the eddy edges give `λ_{u'}` times `cdAD` (the coefficient of an eddy edge
  `(v,w) → (v,w n)` depends on `n` only, and `λ_{wn} ε^{-η₀} = λ_w`).
-/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- A weak source is an inherited path mean. -/
def cdIsInh {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {G : GenStage D ScalarH Dm b j₀} :
    WeakSource G → Prop
  | .inherited .. => True
  | .eddy .. => False

open scoped Classical in
/-- The part of the physical coefficient of the pair `(v', u')` of the stage `i - 1` carried by the
inherited edges. -/
def cdInh (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (v' u' : CompIn (c.stage (i - 1)).comps) (d : ℕ) (s : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ) :=
  ∑ γ : (c.stage (i - 1)).fam.Γ v' u',
    if cdIsInh (cdEdgeSource c i hi hit v' u' γ).1 then
      (c.stage (i - 1)).physCoeff v' u' γ d s x
    else 0

open scoped Classical in
/-- The part carried by the eddy edges. -/
def cdEddy (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (v' u' : CompIn (c.stage (i - 1)).comps) (d : ℕ) (s : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ) :=
  ∑ γ : (c.stage (i - 1)).fam.Γ v' u',
    if cdIsInh (cdEdgeSource c i hi hit v' u' γ).1 then 0
    else (c.stage (i - 1)).physCoeff v' u' γ d s x

/-- **(P) parents**: the parent of a component of the stage `i - 1` is a component of the stage `i`
(the extended components are the words over the components of the stage `i`). -/
def CdParentMem (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (c : WeakPassageInstance plan R) (i : ℕ) (_hi : c.M < i) (_hit : i ≤ c.M + A.Jw)
    (u' : CompIn (c.stage (i - 1)).comps), compParent i u'.1 ∈ (c.stage i).comps

/-- **(Inh) the inherited edges**: summed over the children `v'` of `v` with the readout weights,
the inherited part of the coefficient of `(v', u')` is `λ_{u'}` times the sum of the coefficients
`cdCE r` (the grade `r ∈ [1, J_wR_w]`) of the parents. Route: an inherited edge has the source
`(inherited w h π n)`; `v' = (π.tgt, w)`, `u' = (π.src, w)`; the coefficient does not depend on `w`
(`fluxOp` reads neither `w` nor the component; the lift coefficients `Cc s` agree by
`native_family_lift_coefficients_unique`; `maxOrder = degree` by `HasTags`); the words of `v'` and
`u'` agree, so the unique `v'` is `succComp i v (word u')`; grades `h ≤ J_wR_w` by
`weakConstruction_path_length_bound`. -/
def CdInhClass (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc : ℕ) (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (v : CompIn (c.stage i).comps) (u' : CompIn (c.stage (i - 1)).comps)
    (hu : compParent i u'.1 ∈ (c.stage i).comps) (d : Finset.Icc 2 Dc) (s : ℝ) (x : Vec 2),
    ∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' • cdInh c i hi hit v' u' d.1 s x =
      cdWeight c i u'.1 • ∑ r ∈ Finset.Icc 1 (A.Jw * A.Rw),
        cdCE c Dc i hi hit r v ⟨compParent i u'.1, hu⟩ d s x

/-- **(Edd) the eddy edges**: summed over the children `v'` of `v` with the readout weights, the
eddy part of the coefficient of `(v', u')` is `λ_{u'} · cdAD` when `u'` is a child of `v` of word
length `≠ R_w`, and `0` otherwise. Route: an eddy edge `(v₁, w, n)` runs `(v₁, w) → (v₁, w n)`;
its coefficient is `ε^{-η₀}` times the `(w, v₁)`-free coefficient (`fluxOp` of `weakEddyFlux`
reads `Cc0` only; `identity.map = rootPathMap _ [] _` is the identity); `λ_{wn} ε^{-η₀} = λ_w`;
the edges `(v₀, []) → (v₀, [n])` of `cdAD` are the eddy edges (an inherited edge keeps the word). -/
def CdEddClass (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc : ℕ) (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (v₀ v : CompIn (c.stage i).comps) (u' : CompIn (c.stage (i - 1)).comps)
    (d : Finset.Icc 2 Dc) (s : ℝ) (x : Vec 2),
    ∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' • cdEddy c i hi hit v' u' d.1 s x =
      if compParent i u'.1 = v.1 ∧ (compWord i u'.1).length ≠ A.Rw then
        cdWeight c i u'.1 • cdAD c Dc i v₀ d s x
      else 0
end

/-! **Continuity, periodicity and bounds of the coefficients `cdAD`, `cdCE`**,
and of the velocity `streamVel (Φ_{i-1})`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- A finite sum of continuous periodic fields is continuous and periodic. -/
theorem cdCP_sum {ι E : Type*} [NormedAddCommGroup E] (S : Finset ι) (f : ι → Vec 2 → E)
    (h : ∀ j ∈ S, Continuous (f j) ∧ IsZ2Periodic (f j)) :
    Continuous (fun x => ∑ j ∈ S, f j x) ∧ IsZ2Periodic (fun x => ∑ j ∈ S, f j x) :=
  ⟨continuous_finsetSum _ fun j hj => (h j hj).1, fun n x =>
    Finset.sum_congr rfl fun j hj => (h j hj).2 n x⟩

/-- The physical coefficient of an edge of the stage `i - 1` is continuous and periodic in space. -/
theorem cd_physCoeff_cp (hcommon : WeakPassageCommonOK plan) (c : WeakPassageInstance plan R)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v u : CompIn (c.stage (i - 1)).comps)
    (γ : (c.stage (i - 1)).fam.Γ v u) (d : ℕ) (s : ℝ) :
    Continuous ((c.stage (i - 1)).physCoeff v u γ d s) ∧
      IsZ2Periodic ((c.stage (i - 1)).physCoeff v u γ d s) := by
  obtain ⟨-, hcd, hper, -⟩ := weakPassage_coeffRegular hcommon c (i - 1)
    (by show c.M ≤ i - 1; omega) (by show i - 1 < c.M + A.Jw; omega) v u γ 0 d 0 0
  exact ⟨(hcd s).continuous, hper s⟩

/-- A dependent `if` of continuous periodic fields. -/
theorem cdCP_dite {E : Type*} [NormedAddCommGroup E] (P : Prop) [Decidable P]
    (f : P → Vec 2 → E) (h : ∀ hp, Continuous (f hp) ∧ IsZ2Periodic (f hp)) :
    Continuous (fun x => if hp : P then f hp x else 0) ∧
      IsZ2Periodic (fun x => if hp : P then f hp x else 0) := by
  by_cases hP : P
  · simp only [hP, dite_true]; exact h hP
  · simp only [hP, dite_false]; exact ⟨continuous_const, fun _ _ => rfl⟩

/-- `cdAD` is continuous and periodic in space. -/
theorem cdAD_cp (hcommon : WeakPassageCommonOK plan) (c : WeakPassageInstance plan R)
    (Dc i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps)
    (d : Finset.Icc 2 Dc) (s : ℝ) :
    Continuous (cdAD c Dc i v₀ d s) ∧ IsZ2Periodic (cdAD c Dc i v₀ d s) := by
  classical
  unfold cdAD
  refine cdCP_sum _ _ fun n _ => cdCP_dite _ _ fun hh => cdCP_sum _ _ fun γ _ => ?_
  exact ⟨(cd_physCoeff_cp hcommon c i hi hit _ _ γ d.1 s).1.const_smul
    (c.D.eps (i - 1) ^ A.η₀), fun n x => by
    simp only [(cd_physCoeff_cp hcommon c i hi hit _ _ γ d.1 s).2 n x]⟩

/-- `cdCE` is continuous and periodic in space. -/
theorem cdCE_cp (hcommon : WeakPassageCommonOK plan) (c : WeakPassageInstance plan R)
    (Dc i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (r : ℕ) (v u : CompIn (c.stage i).comps)
    (d : Finset.Icc 2 Dc) (s : ℝ) :
    Continuous (cdCE c Dc i hi hit r v u d s) ∧ IsZ2Periodic (cdCE c Dc i hi hit r v u d s) := by
  classical
  unfold cdCE
  refine cdCP_dite _ _ fun hh => cdCP_sum _ _ fun γ _ => ?_
  by_cases hg : cdIsGrade r (cdEdgeSource c i hi hit ⟨v.1, hh.1⟩ ⟨u.1, hh.2⟩ γ).1
  · simp only [hg, ite_true]; exact cd_physCoeff_cp hcommon c i hi hit _ _ γ d.1 s
  · simp only [hg, ite_false]; exact ⟨continuous_const, fun _ _ => rfl⟩

/-- `cdAD` is bounded in space, uniformly in the order. -/
theorem cdAD_bdd (hcommon : WeakPassageCommonOK plan) (c : WeakPassageInstance plan R)
    (Dc i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps) (s : ℝ) :
    ∃ CA : ℝ, ∀ (d : Finset.Icc 2 Dc) x, ‖cdAD c Dc i v₀ d s x‖ ≤ CA := by
  have h := fun d : Finset.Icc 2 Dc => Providers.KernelSup.bdd_of_periodic
    (cdAD_cp hcommon c Dc i hi hit v₀ d s).1 (cdAD_cp hcommon c Dc i hi hit v₀ d s).2
  choose Bd hBd using h
  refine ⟨∑ d, |Bd d|, fun d x => (hBd d x).trans ?_⟩
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun d => |Bd d|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ d))

/-- `cdCE` is bounded in space. -/
theorem cdCE_bdd (hcommon : WeakPassageCommonOK plan) (c : WeakPassageInstance plan R)
    (Dc i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (H : ℕ) (v : CompIn (c.stage i).comps)
    (s : ℝ) :
    ∃ CC : ℝ, ∀ r ∈ Finset.Icc 1 H, ∀ (u : CompIn (c.stage i).comps) (d : Finset.Icc 2 Dc) x,
      ‖cdCE c Dc i hi hit r v u d s x‖ ≤ CC := by
  have h := fun r (u : CompIn (c.stage i).comps) (d : Finset.Icc 2 Dc) =>
    Providers.KernelSup.bdd_of_periodic (cdCE_cp hcommon c Dc i hi hit r v u d s).1
      (cdCE_cp hcommon c Dc i hi hit r v u d s).2
  choose Bd hBd using h
  refine ⟨∑ r ∈ Finset.Icc 1 H, ∑ u, ∑ d, |Bd r u d|, fun r hr u d x => (hBd r u d x).trans ?_⟩
  refine (le_abs_self _).trans ?_
  refine (Finset.single_le_sum (f := fun d => |Bd r u d|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ d)).trans ?_
  refine (Finset.single_le_sum (f := fun u => ∑ d, |Bd r u d|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ u)).trans ?_
  exact Finset.single_le_sum (f := fun r => ∑ u, ∑ d, |Bd r u d|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hr

/-- The velocity `streamVel (Φ_{i-1})` is continuous in space and bounded at a fixed time. -/
theorem cd_streamVel_cont_bdd (c : WeakPassageInstance plan R) (i : ℕ) (s : ℝ) :
    Continuous (streamVel (c.D.Φ (i - 1)) s) ∧ ∃ Cb : ℝ, ∀ x, ‖streamVel (c.D.Φ (i - 1)) s x‖ ≤ Cb := by
  obtain ⟨hadm, -⟩ := c.streams.2 (i - 1 + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hadm
  refine ⟨?_, ?_⟩
  · exact (Infra.Construction.smoothPeriodic_streamVel hadm).smooth.continuous.comp
      (Continuous.prodMk continuous_const continuous_id)
  · obtain ⟨C, -, hC⟩ := CycleJointProofs.streamVel_bounded_on_compact_time hadm {s}
      isCompact_singleton
    exact ⟨C, fun x => hC s rfl x⟩
end

/-! **The coefficient identity**. Pure algebra: from `CdParentMem`, `CdInhClass`
and `CdEddClass` the weighted sum of the row coefficients applied to an arbitrary jet field `Z`
equals the `AD` part (minus the frontier) plus the `CE` part. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The physical coefficient of an edge of the stage `i - 1` vanishes at the orders `d ≥ 2` that are
not admissible. -/
theorem cd_physCoeff_zero_not_adm (c : WeakPassageInstance plan R) (m i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v u : CompIn (c.stage (i - 1)).comps)
    (γ : (c.stage (i - 1)).fam.Γ v u) (d : ℕ) (hd : 2 ≤ d)
    (hna : d ∉ admissibleOrders
      (fun w : CompIn (c.stage (i - 1)).comps => weakReductionReserve R m w.1)
      (1 + A.Jw * A.Nw) v u) (s : ℝ) (y : Vec 2) :
    (c.stage (i - 1)).physCoeff v u γ d s y = 0 := by
  have ho := EntryWeakProofs.weakConstruction_output_maxOrder_bound c.P _ c.M A.Jw _ 0 c.stage
    c.construction (i - 1) (by omega) (by omega) v u γ
  by_cases hle : d ≤ ((c.stage (i - 1)).fam.identity v u γ).maxOrder
  · exact absurd (weakStage_edge_admissible (weakPassageRawSetting c) m (i - 1) (by
      show c.M ≤ i - 1; omega) (by show i - 1 ≤ c.M + A.Jw; omega) v u γ d hd (hle.trans ho)) hna
  · exact CycleJointProofs.constituentPhysical_zero_above_max
      (c.stage (i - 1)).fam _ _ _ (c.stage (i - 1)).actual v u γ d (not_le.mp hle) s y

/-- The sum over the admissible orders is the sum over `[2, D_c]`. -/
theorem cd_adm_sum_eq (c : WeakPassageInstance plan R) (m Dc : ℕ) (hDc : 1 + A.Jw * A.Nw ≤ Dc)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v' u' : CompIn (c.stage (i - 1)).comps)
    (s : ℝ) (x : Vec 2) (Z : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) :
    ∑ d : admissibleOrders
        (fun w : CompIn (c.stage (i - 1)).comps => weakReductionReserve R m w.1)
        (1 + A.Jw * A.Nw) v' u',
      weakStageCoeff (weakPassageRawSetting c) m (i - 1) v' u' d s x
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z d.1 α) =
    ∑ d : Finset.Icc 2 Dc, (∑ γ : (c.stage (i - 1)).fam.Γ v' u',
        (c.stage (i - 1)).physCoeff v' u' γ d.1 s x)
      (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z d.1 α) := by
  change ∑ d : admissibleOrders
        (fun w : CompIn (c.stage (i - 1)).comps => weakReductionReserve R m w.1)
        (1 + A.Jw * A.Nw) v' u', (∑ γ : (c.stage (i - 1)).fam.Γ v' u',
        (c.stage (i - 1)).physCoeff v' u' γ d.1 s x)
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z d.1 α) = _
  rw [Finset.sum_coe_sort (admissibleOrders
        (fun w : CompIn (c.stage (i - 1)).comps => weakReductionReserve R m w.1)
        (1 + A.Jw * A.Nw) v' u')
      (fun d => (∑ γ : (c.stage (i - 1)).fam.Γ v' u',
        (c.stage (i - 1)).physCoeff v' u' γ d s x)
        (WithLp.toLp 2 fun α : DerivativeWord2 (d - 1) => Z d α)),
    Finset.sum_coe_sort (Finset.Icc 2 Dc)
      (fun d => (∑ γ : (c.stage (i - 1)).fam.Γ v' u',
        (c.stage (i - 1)).physCoeff v' u' γ d s x)
        (WithLp.toLp 2 fun α : DerivativeWord2 (d - 1) => Z d α))]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    have h := (Finset.mem_filter.1 hd).1
    have h2 := Finset.mem_Icc.1 h
    exact Finset.mem_Icc.2 ⟨h2.1, h2.2.trans hDc⟩
  · intro d hd hna
    have h2 := Finset.mem_Icc.1 hd
    have : (∑ γ : (c.stage (i - 1)).fam.Γ v' u', (c.stage (i - 1)).physCoeff v' u' γ d s x) = 0 :=
      Finset.sum_eq_zero fun γ _ => cd_physCoeff_zero_not_adm c m i hi hit v' u' γ d h2.1 hna s x
    rw [this]; rfl

open scoped Classical in
/-- The coefficient of the pair is the sum of the inherited and the eddy parts. -/
theorem cd_coeff_split (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v' u' : CompIn (c.stage (i - 1)).comps) (d : ℕ) (s : ℝ) (x : Vec 2) :
    (∑ γ : (c.stage (i - 1)).fam.Γ v' u', (c.stage (i - 1)).physCoeff v' u' γ d s x) =
      cdInh c i hi hit v' u' d s x + cdEddy c i hi hit v' u' d s x := by
  unfold cdInh cdEddy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  split_ifs <;> simp

/-- A vector of reals indexed by words is the sum of its coordinates. -/
theorem cd_toLp_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι → ℝ) :
    (WithLp.toLp 2 z : PiLp 2 (fun _ : ι => ℝ)) =
      ∑ α, z α • (WithLp.toLp 2 (Pi.single α (1 : ℝ)) : PiLp 2 (fun _ : ι => ℝ)) := by
  ext β
  simp [Pi.single_apply]
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! **The physical coefficient reads an edge only through its map, maximal order and
flux**. -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Two edges of a stage with the same map, maximal order and flux have the same physical
coefficient. -/
theorem cd_physCoeff_congr (G : GenStage D ScalarH Dm b j₀) {v₁ u₁ v₂ u₂ : CompIn G.comps}
    (γ₁ : G.fam.Γ v₁ u₁) (γ₂ : G.fam.Γ v₂ u₂)
    (hmax : (G.fam.identity v₁ u₁ γ₁).maxOrder = (G.fam.identity v₂ u₂ γ₂).maxOrder)
    (hmap : (G.fam.identity v₁ u₁ γ₁).map = (G.fam.identity v₂ u₂ γ₂).map)
    (hflux : ∀ p c d I, G.fam.flux p c v₁ u₁ γ₁ d I = G.fam.flux p c v₂ u₂ γ₂ d I) (d : ℕ) :
    G.physCoeff v₁ u₁ γ₁ d = G.physCoeff v₂ u₂ γ₂ d := by
  unfold GenStage.physCoeff constituentPhysical ChartedFamily.dimFlux ChartedFamily.slowFlux
  simp only [hmax, hmap, hflux]

end AVRegularity
end
end
end

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The coefficient identity from the classification**. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The coefficient identity**: for every jet field `Z`, the weighted sum of the row
coefficients applied to `Z` is the `AD` part (the readout minus the frontier) plus the `CE` part
(the readouts of the parents). -/
def CdCoefIdentity (c : WeakPassageInstance plan R) (m Dc : ℕ) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v₀ v : CompIn (c.stage i).comps) : Prop :=
  ∀ (s : ℝ) (x : Vec 2)
    (Z : ∀ _ : CompIn (c.stage (i - 1)).comps, ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ),
    ∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' • ∑ u' : CompIn (c.stage (i - 1)).comps,
      ∑ d : admissibleOrders
          (fun w : CompIn (c.stage (i - 1)).comps => weakReductionReserve R m w.1)
          (1 + A.Jw * A.Nw) v' u',
        weakStageCoeff (weakPassageRawSetting c) m (i - 1) v' u' d s x
          (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) =
    (∑ d : Finset.Icc 2 Dc, ∑ α : DerivativeWord2 (d.1 - 1),
      (∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' *
        (if (compWord i v'.1).length = A.Rw then 0 else Z v' d.1 α)) •
        cdAD c Dc i v₀ d s x (WithLp.toLp 2 (Pi.single α (1 : ℝ)))) +
    ∑ r ∈ Finset.Icc 1 (A.Jw * A.Rw), ∑ u : CompIn (c.stage i).comps, ∑ d : Finset.Icc 2 Dc,
      cdCE c Dc i hi hit r v u d s x
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) =>
          ∑ u' : CompIn (c.stage (i - 1)).comps, cdLam c i u u' * Z u' d.1 α)

/-- **Step 1**: the left side as the sum over the sources `u'` and the orders of the weighted
inherited and eddy parts. -/
theorem cdCoef_lhs (Dc : ℕ) (hDc : 1 + A.Jw * A.Nw ≤ Dc) (c : WeakPassageInstance plan R) (m : ℕ)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v : CompIn (c.stage i).comps) (s : ℝ)
    (x : Vec 2) (Z : ∀ _ : CompIn (c.stage (i - 1)).comps, ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) :
    ∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' • ∑ u' : CompIn (c.stage (i - 1)).comps,
      ∑ d : admissibleOrders
          (fun w : CompIn (c.stage (i - 1)).comps => weakReductionReserve R m w.1)
          (1 + A.Jw * A.Nw) v' u',
        weakStageCoeff (weakPassageRawSetting c) m (i - 1) v' u' d s x
          (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) =
    ∑ u' : CompIn (c.stage (i - 1)).comps, ∑ d : Finset.Icc 2 Dc,
      ((∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' • cdInh c i hi hit v' u' d.1 s x) +
        (∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' • cdEddy c i hi hit v' u' d.1 s x))
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) := by
  have h1 : ∀ v' u' : CompIn (c.stage (i - 1)).comps,
      ∑ d : admissibleOrders
          (fun w : CompIn (c.stage (i - 1)).comps => weakReductionReserve R m w.1)
          (1 + A.Jw * A.Nw) v' u',
        weakStageCoeff (weakPassageRawSetting c) m (i - 1) v' u' d s x
          (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) =
      ∑ d : Finset.Icc 2 Dc, (cdInh c i hi hit v' u' d.1 s x + cdEddy c i hi hit v' u' d.1 s x)
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) := by
    intro v' u'
    rw [cd_adm_sum_eq c m Dc hDc i hi hit v' u' s x (Z u')]
    exact Finset.sum_congr rfl fun d _ => by rw [cd_coeff_split]
  simp only [h1]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [add_apply, sum_apply, smul_apply, smul_add, Finset.sum_add_distrib]

/-- A coordinate sum with scalar weights is the weighted sum of the vectors. -/
theorem cd_toLp_sum_mul {ι J : Type*} [Fintype ι] (S : Finset J) (f : J → ℝ) (z : J → ι → ℝ) :
    (WithLp.toLp 2 fun α : ι => ∑ j ∈ S, f j * z j α : PiLp 2 (fun _ : ι => ℝ)) =
      ∑ j ∈ S, f j • (WithLp.toLp 2 (z j) : PiLp 2 (fun _ : ι => ℝ)) := by
  ext α
  simp

/-- **Step 2**: the `CE` part. -/
theorem cdCoef_ce (hP : CdParentMem plan) (Dc : ℕ) (c : WeakPassageInstance plan R)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v : CompIn (c.stage i).comps) (s : ℝ)
    (x : Vec 2) (Z : ∀ _ : CompIn (c.stage (i - 1)).comps, ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) :
    ∑ u' : CompIn (c.stage (i - 1)).comps, ∑ d : Finset.Icc 2 Dc,
      (cdWeight c i u'.1 • ∑ r ∈ Finset.Icc 1 (A.Jw * A.Rw),
        cdCE c Dc i hi hit r v ⟨compParent i u'.1, hP R c i hi hit u'⟩ d s x)
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) =
    ∑ r ∈ Finset.Icc 1 (A.Jw * A.Rw), ∑ u : CompIn (c.stage i).comps, ∑ d : Finset.Icc 2 Dc,
      cdCE c Dc i hi hit r v u d s x
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) =>
          ∑ u' : CompIn (c.stage (i - 1)).comps, cdLam c i u u' * Z u' d.1 α) := by
  classical
  have e1 : ∀ r u (d : Finset.Icc 2 Dc),
      cdCE c Dc i hi hit r v u d s x
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) =>
          ∑ u' : CompIn (c.stage (i - 1)).comps, cdLam c i u u' * Z u' d.1 α) =
      ∑ u' : CompIn (c.stage (i - 1)).comps, cdLam c i u u' •
        cdCE c Dc i hi hit r v u d s x
          (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) := by
    intro r u d
    rw [cd_toLp_sum_mul Finset.univ (fun u' => cdLam c i u u') (fun u' α => Z u' d.1 α), map_sum]
    exact Finset.sum_congr rfl fun u' _ => map_smul _ _ _
  simp only [e1]
  have e2 : ∀ r (u' : CompIn (c.stage (i - 1)).comps) (d : Finset.Icc 2 Dc),
      ∑ u : CompIn (c.stage i).comps, cdLam c i u u' •
        cdCE c Dc i hi hit r v u d s x
          (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) =
      cdWeight c i u'.1 • cdCE c Dc i hi hit r v ⟨compParent i u'.1, hP R c i hi hit u'⟩ d s x
          (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) := by
    intro r u' d
    rw [Finset.sum_eq_single (⟨compParent i u'.1, hP R c i hi hit u'⟩ : CompIn (c.stage i).comps)]
    · simp [cdLam]
    · intro u _ hne
      have : compParent i u'.1 ≠ u.1 := fun h => hne (Subtype.ext h.symm)
      simp [cdLam, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  calc _ = ∑ u' : CompIn (c.stage (i - 1)).comps, ∑ d : Finset.Icc 2 Dc,
        ∑ r ∈ Finset.Icc 1 (A.Jw * A.Rw), ∑ u : CompIn (c.stage i).comps,
        cdLam c i u u' • cdCE c Dc i hi hit r v u d s x
          (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) := by
        refine Finset.sum_congr rfl fun u' _ => Finset.sum_congr rfl fun d _ => ?_
        simp only [e2, smul_apply, sum_apply, Finset.smul_sum]
    _ = _ := by
        symm
        calc _ = ∑ r ∈ Finset.Icc 1 (A.Jw * A.Rw), ∑ d : Finset.Icc 2 Dc,
              ∑ u : CompIn (c.stage i).comps, ∑ u' : CompIn (c.stage (i - 1)).comps,
              cdLam c i u u' • cdCE c Dc i hi hit r v u d s x
                (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) :=
              Finset.sum_congr rfl fun r _ => Finset.sum_comm
          _ = ∑ d : Finset.Icc 2 Dc, ∑ r ∈ Finset.Icc 1 (A.Jw * A.Rw),
              ∑ u : CompIn (c.stage i).comps, ∑ u' : CompIn (c.stage (i - 1)).comps,
              cdLam c i u u' • cdCE c Dc i hi hit r v u d s x
                (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) :=
              Finset.sum_comm
          _ = ∑ d : Finset.Icc 2 Dc, ∑ r ∈ Finset.Icc 1 (A.Jw * A.Rw),
              ∑ u' : CompIn (c.stage (i - 1)).comps, ∑ u : CompIn (c.stage i).comps,
              cdLam c i u u' • cdCE c Dc i hi hit r v u d s x
                (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) :=
              Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun r _ => Finset.sum_comm
          _ = ∑ d : Finset.Icc 2 Dc, ∑ u' : CompIn (c.stage (i - 1)).comps,
              ∑ r ∈ Finset.Icc 1 (A.Jw * A.Rw), ∑ u : CompIn (c.stage i).comps,
              cdLam c i u u' • cdCE c Dc i hi hit r v u d s x
                (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) :=
              Finset.sum_congr rfl fun d _ => Finset.sum_comm
          _ = _ := Finset.sum_comm


/-- **Step 3**: the `AD` part. -/
theorem cdCoef_ad (Dc : ℕ) (c : WeakPassageInstance plan R) (i : ℕ)
    (v₀ v : CompIn (c.stage i).comps) (s : ℝ) (x : Vec 2)
    (Z : ∀ _ : CompIn (c.stage (i - 1)).comps, ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) :
    ∑ u' : CompIn (c.stage (i - 1)).comps, ∑ d : Finset.Icc 2 Dc,
      (if compParent i u'.1 = v.1 ∧ (compWord i u'.1).length ≠ A.Rw then
        cdWeight c i u'.1 • cdAD c Dc i v₀ d s x else 0)
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) =
    ∑ d : Finset.Icc 2 Dc, ∑ α : DerivativeWord2 (d.1 - 1),
      (∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' *
        (if (compWord i v'.1).length = A.Rw then 0 else Z v' d.1 α)) •
        cdAD c Dc i v₀ d s x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) := by
  classical
  have hterm : ∀ (v' : CompIn (c.stage (i - 1)).comps) (d : Finset.Icc 2 Dc),
      ∑ α : DerivativeWord2 (d.1 - 1), (cdLam c i v v' *
        (if (compWord i v'.1).length = A.Rw then 0 else Z v' d.1 α)) •
          cdAD c Dc i v₀ d s x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) =
      (if compParent i v'.1 = v.1 ∧ (compWord i v'.1).length ≠ A.Rw then
        cdWeight c i v'.1 • cdAD c Dc i v₀ d s x else 0)
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z v' d.1 α) := by
    intro v' d
    by_cases hc : compParent i v'.1 = v.1 ∧ (compWord i v'.1).length ≠ A.Rw
    · have h1 : cdLam c i v v' = cdWeight c i v'.1 := by simp [cdLam, hc.1]
      simp only [hc.1, hc.2, h1, true_and, ne_eq, not_false_eq_true, ↓reduceIte]
      rw [cd_toLp_eq_sum (fun α : DerivativeWord2 (d.1 - 1) => Z v' d.1 α)]
      simp only [smul_apply, map_sum, map_smul, mul_smul]
      exact Finset.sum_congr rfl fun α _ => smul_comm _ _ _
    · have h0 : ∀ α : DerivativeWord2 (d.1 - 1), (cdLam c i v v' *
          (if (compWord i v'.1).length = A.Rw then 0 else Z v' d.1 α)) = 0 := by
        intro α
        by_cases h2 : compParent i v'.1 = v.1
        · have h3 : (compWord i v'.1).length = A.Rw := by
            by_contra h4; exact hc ⟨h2, h4⟩
          simp [h3]
        · simp [cdLam, h2]
      simp [hc, h0]
  calc _ = ∑ d : Finset.Icc 2 Dc, ∑ u' : CompIn (c.stage (i - 1)).comps,
        (if compParent i u'.1 = v.1 ∧ (compWord i u'.1).length ≠ A.Rw then
          cdWeight c i u'.1 • cdAD c Dc i v₀ d s x else 0)
          (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [← hterm, Finset.sum_smul]
      rw [Finset.sum_comm]

/-- **The coefficient identity from the classification.** -/
theorem cdCoefIdentity_of_classes (hP : CdParentMem plan) (hI : CdInhClass plan)
    (hE : CdEddClass plan) (Dc : ℕ) (hDc : 1 + A.Jw * A.Nw ≤ Dc) (c : WeakPassageInstance plan R)
    (m : ℕ) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v₀ v : CompIn (c.stage i).comps) :
    CdCoefIdentity c m Dc i hi hit v₀ v := by
  classical
  intro s x Z
  rw [cdCoef_lhs Dc hDc c m i hi hit v s x Z]
  have key : ∀ (u' : CompIn (c.stage (i - 1)).comps) (d : Finset.Icc 2 Dc),
      ((∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' • cdInh c i hi hit v' u' d.1 s x) +
        (∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' • cdEddy c i hi hit v' u' d.1 s x))
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) =
      (cdWeight c i u'.1 • ∑ r ∈ Finset.Icc 1 (A.Jw * A.Rw),
        cdCE c Dc i hi hit r v ⟨compParent i u'.1, hP R c i hi hit u'⟩ d s x)
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) +
      (if compParent i u'.1 = v.1 ∧ (compWord i u'.1).length ≠ A.Rw then
        cdWeight c i u'.1 • cdAD c Dc i v₀ d s x else 0)
        (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) => Z u' d.1 α) := by
    intro u' d
    rw [hI R Dc c i hi hit v u' (hP R c i hi hit u') d s x, hE R Dc c i hi hit v₀ v u' d s x,
      add_apply]
  simp only [key, Finset.sum_add_distrib]
  rw [cdCoef_ce hP Dc c i hi hit v s x Z, cdCoef_ad Dc c i v₀ v s x Z, add_comm]
end

/-! **The coefficient of an eddy edge depends on the degree only**. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The maximal order of the seed tag of a weak source is its degree. -/
theorem cd_weakTag_maxOrder {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {G : GenStage D ScalarH Dm b j₀} (P : ProvParams) (m : ℕ) (rW η₀ : ℝ) (s : WeakSource G) :
    (s.weakTag P m rW η₀).maxOrder = s.degree := by
  cases s <;> rfl

/-- The maximal order of the identity of an edge is the degree of its source. -/
theorem cd_maxOrder_eq_degree (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v u : CompIn (c.stage (i - 1)).comps)
    (γ : (c.stage (i - 1)).fam.Γ v u) :
    ((c.stage (i - 1)).fam.identity v u γ).maxOrder = (cdEdgeSource c i hi hit v u γ).1.degree := by
  have hex := (c.construction.2.2 i hi hit).1.2.2.2.2.2
  obtain ⟨idx, Cc, Cc0, -, -, -, hall⟩ := Classical.choose_spec hex
  have h1 := ((c.construction.2.2 i hi hit).2 v u γ).2
  rw [(hall v u γ).1] at h1
  rw [h1]
  show (Prov.tags _ (Prov.seed _ _)).order = _
  simp only [Prov.tags]
  exact cd_weakTag_maxOrder _ _ _ _ _

theorem cd_succComp_root (m : ℕ) (v : Comp) (t : List WordLetter) :
    (succComp m v t).root = v.root := by
  unfold succComp
  split_ifs <;> rfl

theorem cd_rootPathMap_nil (r₀ r : ℕ) :
    rootPathMap ScalarH r₀ [] r = if r₀ = r then ContinuousLinearMap.id ℝ ℝ else 0 := by
  unfold rootPathMap
  by_cases h : r₀ = r
  · subst h; simp
  · simp [h]

/-- The map of the identity of an edge is the root path map. -/
theorem cd_edge_map (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v u : CompIn (c.stage (i - 1)).comps)
    (γ : (c.stage (i - 1)).fam.Γ v u) :
    ((c.stage (i - 1)).fam.identity v u γ).map = rootPathMap ScalarH u.1.root [] v.1.root := by
  have hex := (c.construction.2.2 i hi hit).1.2.2.2.2.2
  obtain ⟨idx, Cc, Cc0, -, -, -, hall⟩ := Classical.choose_spec hex
  exact (hall v u γ).2.1

/-- **The coefficient of an eddy edge depends on the degree only**: two eddy edges of the same
degree have the same physical coefficient (whatever their component and word). -/
theorem cd_eddy_coeff_indep (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) {v₁ u₁ v₂ u₂ : CompIn (c.stage (i - 1)).comps}
    (γ₁ : (c.stage (i - 1)).fam.Γ v₁ u₁) (γ₂ : (c.stage (i - 1)).fam.Γ v₂ u₂)
    (a b : CompIn (c.stage i).comps) (w₁ w₂ : List WordLetter) (n : ℕ)
    (h₁ : (cdEdgeSource c i hi hit v₁ u₁ γ₁).1 = WeakSource.eddy a w₁ n)
    (h₂ : (cdEdgeSource c i hi hit v₂ u₂ γ₂).1 = WeakSource.eddy b w₂ n) (d : ℕ) :
    (c.stage (i - 1)).physCoeff v₁ u₁ γ₁ d = (c.stage (i - 1)).physCoeff v₂ u₂ γ₂ d := by
  have hex := (c.construction.2.2 i hi hit).1.2.2.2.2.2
  obtain ⟨idx, Cc, Cc0, -, -, -, hall⟩ := Classical.choose_spec hex
  have hm₁ := cd_maxOrder_eq_degree c i hi hit v₁ u₁ γ₁
  have hm₂ := cd_maxOrder_eq_degree c i hi hit v₂ u₂ γ₂
  rw [h₁] at hm₁
  rw [h₂] at hm₂
  have h₁' : (Classical.choose hex v₁ u₁ γ₁).1 = WeakSource.eddy a w₁ n := h₁
  have h₂' : (Classical.choose hex v₂ u₂ γ₂).1 = WeakSource.eddy b w₂ n := h₂
  refine cd_physCoeff_congr (c.stage (i - 1)) γ₁ γ₂ (hm₁.trans hm₂.symm) ?_ ?_ d
  · rw [cd_edge_map c i hi hit, cd_edge_map c i hi hit]
    have p₁ := (Classical.choose hex v₁ u₁ γ₁).2
    have p₂ := (Classical.choose hex v₂ u₂ γ₂).2
    rw [h₁'] at p₁
    rw [h₂'] at p₂
    have ru₁ : u₁.1.root = a.1.root := by
      rw [← p₁.2.1]; exact cd_succComp_root _ _ _
    have rv₁ : v₁.1.root = a.1.root := by
      rw [← p₁.2.2]; exact cd_succComp_root _ _ _
    have ru₂ : u₂.1.root = b.1.root := by
      rw [← p₂.2.1]; exact cd_succComp_root _ _ _
    have rv₂ : v₂.1.root = b.1.root := by
      rw [← p₂.2.2]; exact cd_succComp_root _ _ _
    rw [cd_rootPathMap_nil, cd_rootPathMap_nil, ru₁, rv₁, ru₂, rv₂]
    simp
  · intro p ctx d' I
    by_cases hd : 2 ≤ d' ∧ d' ≤ n
    · funext t X z
      have e₁ := (hall v₁ u₁ γ₁).2.2 p ctx d' I t X z hd.1
      have e₂ := (hall v₂ u₂ γ₂).2.2 p ctx d' I t X z hd.1
      rw [h₁'] at e₁
      rw [h₂'] at e₂
      rw [e₁, e₂]
      rfl
    · have z₁ := (c.stage (i - 1)).fam.flux_zero p ctx v₁ u₁ γ₁ d' I (by rw [hm₁]; exact hd)
      have z₂ := (c.stage (i - 1)).fam.flux_zero p ctx v₂ u₂ γ₂ d' I (by rw [hm₂]; exact hd)
      rw [z₁, z₂]
end

/-! **The flux identity from the coefficient identity**. The jets of `cdW` and
`cdFrontier` are the `cdLam`-weighted sums of the jets of `Uhi`; the row fluxes read the jets of
`Uhi`; `Fc` is minus the `AD`-flux of the frontier. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The jets of `cdW` at the orders `≤ K'` are the `cdLam`-weighted sums of the jets of `Uhi`. -/
theorem cdW_jet_lam_ae (c : WeakPassageInstance plan R) (m K' : ℕ)
    (hK : ∀ w, K' ≤ weakReductionReserve R m w) (i : ℕ)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (v : CompIn (c.stage i).comps) (t : ℝ) {m' : ℕ} (hm' : m' ≤ K') (w : DerivativeWord2 m') :
    torusJetOrder (cdW c m K' hK i Uhi v t) m' w =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ v' : CompIn (c.stage (i - 1)).comps,
        cdLam c i v v' * torusJetOrder (Uhi (i - 1) v' t) m' w x := by
  classical
  filter_upwards [cdReadout_jet_ae c m K' hK i (fun _ => True) (fun v' => Uhi (i - 1) v' t) v
    hm' w] with x hx
  refine hx.trans (Finset.sum_congr rfl fun v' _ => ?_)
  by_cases h : compParent i v'.1 = v.1 <;> simp [cdLam, h]

/-- The jets of `cdFrontier` are the weighted sums over the children of word length `R_w`. -/
theorem cdFrontier_jet_lam_ae (c : WeakPassageInstance plan R) (m K' : ℕ)
    (hK : ∀ w, K' ≤ weakReductionReserve R m w) (i : ℕ)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (v : CompIn (c.stage i).comps) (t : ℝ) {m' : ℕ} (hm' : m' ≤ K') (w : DerivativeWord2 m') :
    torusJetOrder (cdFrontier c m K' hK i Uhi v t) m' w =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ v' : CompIn (c.stage (i - 1)).comps,
        cdLam c i v v' * (if (compWord i v'.1).length = A.Rw then
          torusJetOrder (Uhi (i - 1) v' t) m' w x else 0) := by
  classical
  filter_upwards [cdReadout_jet_ae c m K' hK i (fun w => (compWord i w).length = A.Rw)
    (fun v' => Uhi (i - 1) v' t) v hm' w] with x hx
  refine hx.trans (Finset.sum_congr rfl fun v' _ => ?_)
  by_cases h : compParent i v'.1 = v.1 <;> by_cases h2 : (compWord i v'.1).length = A.Rw <;>
    simp [cdLam, h, h2]
end

/-! **The flux identity from the coefficient identity**, the jet side. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The flux identity from the coefficient identity.** -/
theorem cdFluxIdentity_of_coef (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (Dc m k : ℕ) (hK : ∀ w, k + 1 + Dc ≤ weakReductionReserve R m w) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j)
    (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (v : CompIn (c.stage i).comps)
    (hw : ∀ j : CompIn (c.stage (i - 1)).comps,
      ∀ᵐ s ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
        truncateTorusHk (Nat.le_succ _) (Whi (i - 1) j s) = Uhi (i - 1) j s)
    (hFc : CdFcRealizes c r Dc m k hK i Uhi (cdAD c Dc i v₀) Fc)
    (hcoef : CdCoefIdentity c m Dc i hi hit v₀ v) :
    CdFluxIdentity c r Dc m k hK i hi hit v₀ Uhi Whi Fc v := by
  classical
  have hK1 : ∀ w, 1 ≤ weakReductionReserve R m w := fun w => by have := hK w; omega
  unfold CdFluxIdentity
  filter_upwards [cdRowFlux_ae c m hK1 Uhi Whi _ i hw,
    ae_restrict_mem (μ := volume) (measurableSet_Icc (a := r.tq i) (b := r.a + A.T₀))]
    with s hrow hs
  have hd : ∀ d : Finset.Icc 2 Dc, d.1 - 1 ≤ k + 1 + Dc := fun d => by
    have := (Finset.mem_Icc.1 d.2).2; omega
  have hW : ∀ᵐ x ∂(volume.restrict unitCube), ∀ (u : CompIn (c.stage i).comps)
      (d : Finset.Icc 2 Dc) (α : DerivativeWord2 (d.1 - 1)),
      torusJetOrder (cdW c m (k + 1 + Dc) hK i Uhi u s) (d.1 - 1) α x =
        ∑ u' : CompIn (c.stage (i - 1)).comps,
          cdLam c i u u' * torusJetOrder (Uhi (i - 1) u' s) (d.1 - 1) α x :=
    ae_all_iff.2 fun u => ae_all_iff.2 fun d => ae_all_iff.2 fun α =>
      cdW_jet_lam_ae c m _ hK i Uhi u s (hd d) α
  have hH : ∀ᵐ x ∂(volume.restrict unitCube), ∀ (d : Finset.Icc 2 Dc)
      (α : DerivativeWord2 (d.1 - 1)),
      torusJetOrder (cdFrontier c m (k + 1 + Dc) hK i Uhi v s) (d.1 - 1) α x =
        ∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' *
          (if (compWord i v'.1).length = A.Rw then
            torusJetOrder (Uhi (i - 1) v' s) (d.1 - 1) α x else 0) :=
    ae_all_iff.2 fun d => ae_all_iff.2 fun α =>
      cdFrontier_jet_lam_ae c m _ hK i Uhi v s (hd d) α
  have hF := hFc v s hs
  have hR := ae_all_iff.2 hrow
  filter_upwards [hW, hH, hF, hR] with x hxW hxH hxF hxR
  have hL : ∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' • cdRowFlux c m Whi i v' s x =
      ∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' • cdRowFluxU c m Uhi i v' s x :=
    Finset.sum_congr rfl fun v' _ => by rw [hxR v']
  rw [hL]
  have hc := hcoef s x (fun u' d α => torusJetOrder (Uhi (i - 1) u' s) (d - 1) α x)
  refine hc.trans ?_
  ext k'
  simp only [cdTargetFlux, coarseDefectFlux, hxW, PiLp.add_apply]
  rw [hxF]
  have key : ∀ (d : Finset.Icc 2 Dc) (α : DerivativeWord2 (d.1 - 1)),
      (∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' *
        (if (compWord i v'.1).length = A.Rw then 0 else
          torusJetOrder (Uhi (i - 1) v' s) (d.1 - 1) α x)) =
      (∑ u' : CompIn (c.stage (i - 1)).comps,
        cdLam c i v u' * torusJetOrder (Uhi (i - 1) u' s) (d.1 - 1) α x) -
      ∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' *
        (if (compWord i v'.1).length = A.Rw then
          torusJetOrder (Uhi (i - 1) v' s) (d.1 - 1) α x else 0) := by
    intro d α
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v' _ => ?_
    split_ifs <;> ring
  have hJ : ∀ l : Fin 2, ((c.D.κ c.M • (1 : Matrix (Fin 2) (Fin 2) ℝ)) k' l -
      c.D.κ c.M * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) = 0 := by
    intro l; simp [Matrix.smul_apply]
  simp only [hxH, key, hJ, zero_mul, Finset.sum_const_zero, zero_add, WithLp.ofLp_sum,
    WithLp.ofLp_smul, WithLp.ofLp_neg, Finset.sum_apply, Pi.smul_apply,
    Pi.neg_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
  simp only [mul_comm]
  ring
end

/-! **`CdIntegrableAll` is proved**, from `WeakPassageCommonOK plan`.

The integrand is the abstract integrand `weakIntegrand` (drift, diffusion and flux pairings with
`L²` factors); the flux is `L²` by `coarseDefectFlux_memLp_bound` (bounded continuous periodic
coefficients `cdAD`, `cdCE`, the finitely many families `cdW`), `Fc` and the jets of the test are
`L²` as jets of `TorusHk` classes. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.CycleComparison.Coarse

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **(I) integrability** at every time, for every `H¹` test. -/
theorem cdIntegrable_of_common (hcommon : WeakPassageCommonOK plan)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (Dc m k : ℕ)
    (hK : ∀ w, k + 1 + Dc ≤ weakReductionReserve R m w) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (v : CompIn (c.stage i).comps) :
    CdIntegrable c r Dc m k hK i hi hit v₀ Uhi Fc v := by
  classical
  intro t ht φ s hs
  have hK1 : 1 ≤ k + 1 + Dc := by omega
  obtain ⟨CA, hCA⟩ := cdAD_bdd hcommon c Dc i hi hit v₀ s
  obtain ⟨CC, hCC⟩ := cdCE_bdd hcommon c Dc i hi hit (A.Jw * A.Rw) v s
  obtain ⟨hbc, Cb, hCb⟩ := cd_streamVel_cont_bdd c i s
  have hflux := coarseDefectFlux_memLp_bound
    (h := fun u : CompIn (c.stage i).comps => ScalarH u.1.root)
    (fun u t => cdW c m (k + 1 + Dc) hK i Uhi u t) (D := Dc) (H := A.Jw * A.Rw) (by omega) hK1
    (c.D.κ c.M) (cdAD c Dc i v₀) (cdCE c Dc i hi hit)
    (fun _ => (c.D.κ c.M) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) v s (CA := CA) (CC := CC) (CJ := 0)
    (MW := ∑ u, ‖cdW c m (k + 1 + Dc) hK i Uhi u s‖) hCA hCC (by intro k l; simp [Matrix.smul_apply])
    (fun u => Finset.single_le_sum (f := fun u => ‖cdW c m (k + 1 + Dc) hK i Uhi u s‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ u))
    (fun d => (cdAD_cp hcommon c Dc i hi hit v₀ d s).1)
    (fun r _ u d => (cdCE_cp hcommon c Dc i hi hit r v u d s).1)
  have hF : ∀ k0 : Fin 2, MemLp (fun x => (cdTargetFlux c Dc m k hK i hi hit v₀ Uhi v s x +
      (Fc v s).toFunction.jet (valueIndex2 k) x) k0) 2 (volume.restrict AVenhance.unitCube) := by
    intro k0
    have h1 : MemLp (fun x => cdTargetFlux c Dc m k hK i hi hit v₀ Uhi v s x +
        (Fc v s).toFunction.jet (valueIndex2 k) x) 2 (volume.restrict AVenhance.unitCube) :=
      MemLp.add hflux.1 (memLp_jet (Fc v s) (valueIndex2 k))
    exact MemLp.of_le h1 ((PiLp.proj (𝕜 := ℝ) (p := 2)
      (β := fun _ : Fin 2 => ScalarH v.1.root) k0).continuous.comp_aestronglyMeasurable
        h1.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => PiLp.norm_apply_le _ k0)
  have hint := weakIntegrand_integrable_and_bound (E := ScalarH v.1.root)
    (μ := volume.restrict AVenhance.unitCube)
    (bk := fun k0 x => streamVel (c.D.Φ (i - 1)) s x k0) (Cb := Cb)
    (fun k0 => ((continuous_apply k0).comp hbc).aestronglyMeasurable)
    (fun k0 x => by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (streamVel (c.D.Φ (i - 1)) s x) k0).trans (hCb x))
    (c.D.κ c.M)
    (J := fun k0 x => torusJetOrder (cdW c m (k + 1 + Dc) hK i Uhi v s) 1 (fun _ => k0) x)
    (Z := fun k0 x => (cdTargetFlux c Dc m k hK i hi hit v₀ Uhi v s x +
      (Fc v s).toFunction.jet (valueIndex2 k) x) k0)
    (MJ := ‖cdW c m (k + 1 + Dc) hK i Uhi v s‖)
    (MZ := ∑ k0 : Fin 2, (eLpNorm (fun x => (cdTargetFlux c Dc m k hK i hi hit v₀ Uhi v s x +
      (Fc v s).toFunction.jet (valueIndex2 k) x) k0) 2
      (volume.restrict AVenhance.unitCube)).toReal)
    (fun k0 => memLp_torusJetOrder (cdW c m (k + 1 + Dc) hK i Uhi v s) hK1 (fun _ => k0))
    (fun k0 => eLpNorm_torusJetOrder_le (cdW c m (k + 1 + Dc) hK i Uhi v s) hK1 _)
    hF
    (fun k0 => Finset.single_le_sum
      (f := fun k0 => (eLpNorm (fun x => (cdTargetFlux c Dc m k hK i hi hit v₀ Uhi v s x +
        (Fc v s).toFunction.jet (valueIndex2 k) x) k0) 2
        (volume.restrict AVenhance.unitCube)).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ k0))
    (φ0 := φ.toFunction.jet (valueIndex2 1))
    (φ1 := fun k0 => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k0⟩)
    (Mφ := ‖φ‖) (memLp_jet φ _) (eLpNorm_jet_le φ _) (fun k0 => memLp_jet φ _)
    (fun k0 => eLpNorm_jet_le φ _)
  refine hint.1.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [weakIntegrand]

/-- **(I) for all data**, from the common plan hypothesis. -/
theorem cdIntegrableAll_of_common (plan : WeakPassagePlan) (hcommon : WeakPassageCommonOK plan) :
    CdIntegrableAll plan := by
  intro B A R Dc m k hDc hk c r Uhi Whi hpass i hi hit v₀ Fc hFc v
  exact cdIntegrable_of_common hcommon c r Dc m k _ i hi hit v₀ Uhi Fc v
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end
