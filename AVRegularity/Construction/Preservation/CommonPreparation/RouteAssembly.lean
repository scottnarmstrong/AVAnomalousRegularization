-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.CtxModel
import AVRegularity.Families.TorusCompatible.WeakStage

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Instantiate local coefficient data on the same post-buffer neutral family. -/

/-- The exact estimate supplied after the constant in local producer. -/
abbrev CopyCoeffEstimate (D Kmax Jm : ℕ) (Cm Cchart : ℕ → ℝ) (Cprep : ℝ) : Prop :=
  ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (a b Cpad Cage : ℝ) (Npad : ℕ) (ν e ρ : ℝ),
    0 < ocTauPP α q Λ m → 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)]
    {Part : Type*} {Ctx : Part → Type*} (F : ChartedFamily ι h D Part Ctx)
    (π : ι → ℝ), (∀ i, 0 < π i) →
  ∀ (K : ι → ℕ), (∀ i, K i ≤ Kmax) → ∀ (actual : ∀ pc, Ctx pc) (B : ι → ι → ℝ),
    (∀ v u, 0 ≤ B v u) →
    (∃ n : ℕ, e⁻¹ = (n : ℝ)) →
    F.IsTimeMeasurable → (∀ p, Measurable (F.weight p)) →
    IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)) →
    (∀ (c d : ℝ), a ≤ c → c ≤ d → d ≤ b → d - c ≤ 2 * ocTauPP α q Λ m →
      ∃ (l₀ : ℤ) (P : ℕ), IsPreparationChartCertificate α q Λ m φ hφ c d
        Cpad Cage Npad Jm Cchart l₀ P F) →
    IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
    (∀ v u d, coefficientSeminorm ρ (K v) a b
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K v u d) ≠ ⊤) ∧
    (∀ v u d, Measurable (fun z : Set.Icc a b × Vec 2 =>
      edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K v u d z.1 z.2)) ∧
    (∀ v u d t, t ∈ Set.Icc a b → ContDiff ℝ (K v : ℕ)
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K v u d t)) ∧
    (∀ v u d t, t ∈ Set.Icc a b → IsZ2Periodic
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K v u d t)) ∧
    ∀ v u, schurMatrix (h := h) ν ρ π K D a b
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K) v u ≤ Cprep * B v u


variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ Hpr : ℕ} {Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
    j₀ Hpr Q T₀ hr)


private theorem context_copyCoeff_eq
    (K : CompIn c.G.comps × Fin (Hpr + 1) → ℕ) :
    CopyCoeff c.request K = edgeCoefficient (preparationNeutralChain c.G.actualFamily Hpr)
      (c.D.κ c.G.level) (c.D.eps c.G.level) (c.D.eps (c.G.level - 1)) (fun _ => ()) K := rfl

/-- Whole-window copied coefficient clauses from the supplied scalar scales,
original copied envelopes and local short-chart coefficient estimate. -/
theorem copyCoeffAt_of_context
    (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hc₀ : 0 < kI.c₀) (hc₁ : kI.c₀ ≤ 1)
    (g cOld Crat : ℝ) (sc : PreparationContextScales c g cOld Crat)
    (Kmax Jm : ℕ) (Cpad Cage : ℝ) (Npad : ℕ) (Cchart : ℕ → ℝ)
    (Cprep : ℝ) (hCprep : 0 ≤ Cprep)
    (hlocal : CopyCoeffEstimate.{0, 0, 0, 0} (succSchedD D₀ N p (H + 1)) Kmax Jm kI.Cm Cchart Cprep)
    (hcharts : ∀ (a b : ℝ), c.request.bufferEnd ≤ a → a ≤ b → b ≤ c.tf →
      b - a ≤ 2 * ocTauPP α q Λ c.m → ∃ (l₀ : ℤ) (P : ℕ),
        IsPreparationChartCertificate α q Λ c.m (c.D.Φ (c.m - 1)) (c.D.hΦ (c.m - 1))
          a b Cpad Cage Npad Jm Cchart l₀ P (preparationNeutralChain c.G.actualFamily Hpr))
    (K : CompIn c.G.comps × Fin (Hpr + 1) → ℕ) (hK : ∀ v, K v ≤ Kmax)
    (kenv : InvConsts) (hCm : kenv.Cm = kI.Cm) (hJm : kenv.Jm = Jm)
    (hcopy : NativeCopyEnvelopesStatement c.G kenv (Set.Icc c.s₀ c.tf)
      (rhoStar c.D kI.c₀ c.G.level) Hpr K)
    (hm : 1 ≤ c.m) :
    CopyCoeffAt c.request K (Cprep * (CI * ocEpsilon q Λ c.m ^ min (ocDelta α q / 4) τe)) := by
  classical
  have hΛ1 : 1 ≤ Λ := (by norm_num : 1 ≤ 128).trans hΛ
  have hτ := Construction.Stream.ocTauPP_pos (m := c.m) (α := α) (q := q) hΛ1
  have hsub : Set.Icc c.request.bufferEnd c.tf ⊆ Set.Icc c.tA c.tf := fun _ ht =>
    ⟨(c.tA_le_s₀ hΛ1).trans (sc.buffer_after.trans ht.1), ht.2⟩
  have hpost : Set.Icc c.request.bufferEnd c.tf ⊆ Set.Icc c.s₀ c.tf :=
    fun _ ht => ⟨sc.buffer_after.trans ht.1, ht.2⟩
  have he : c.D.eps c.G.level = ocEpsilon q Λ c.m := by
    simp only [OCData.eps, c.hlevel, c.hq, c.hΛ]
  have hparent : c.D.eps (c.G.level - 1) = ocEpsilon q Λ (c.m - 1) := by
    simp only [OCData.eps, c.hlevel, c.hq, c.hΛ]
  have hepos : 0 < c.D.eps c.G.level := he.symm ▸ (Scales.epsilon_basic hq hΛ).1
  have hρe : rhoStar c.D kI.c₀ c.G.level ≤ c.D.eps c.G.level := by
    unfold rhoStar
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hc₀.le).trans
      (mul_le_mul_of_nonneg_right hc₁ hepos.le |>.trans_eq (one_mul _))
  have heE : c.D.eps c.G.level ≤ ocEpsilon q Λ (c.m - 1) := by
    rw [he]
    have hratio := Scales.epsilon_ratio_lower hq hΛ hm
    have hΛr : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ1
    have hr := (le_div_iff₀ (Scales.epsilon_basic (m := c.m) hq hΛ).1).mp
      (hΛr.trans hratio)
    simpa only [one_mul] using hr
  have hcopyPost := native_copy_envelopes_subwindow c.G kenv hpost
    (rhoStar c.D kI.c₀ c.G.level) Hpr K
    (by rw [hparent]; exact (Scales.epsilon_basic hq hΛ).1.le) hcopy
  obtain ⟨FD⟩ := model_family_data c.law _ c.seedK c.freshK _ _ c.Mnat kI kenv
    c.tA c.tf _ _ c.G c.hinv (c.q_gt hq) (c.lambda_ge hΛ)
    c.request.bufferEnd c.tf hsub (rhoStar c.D kI.c₀ c.G.level) Hpr K hcopyPost
  let C := preparationNeutralChain c.G.actualFamily Hpr
  have hctime : C.IsTimeMeasurable := FD.measurable
  have hcweight : ∀ pc, Measurable (C.weight pc) := FD.weight_measurable
  have hctorus : IsTorusCompatible C (fun _ => ()) (ocEpsilon q Λ (c.m - 1)) := by
    rw [← hparent]
    exact FD.torus
  have weighted (w : CompIn c.G.comps → ℝ)
      (hw : (w = fun _ => 1) ∨ w = c.G.marker c.law) := FD.envelopes w hw
  have pointwise (w : CompIn c.G.comps → ℝ)
      (hw : (w = fun _ => 1) ∨ w = c.G.marker c.law) := (weighted w hw).2.2
  have hν : c.D.kap c.G.level = c.D.κ c.G.level := by
    rw [c.kap_eq, c.hlevel]
  have hκ : c.D.κ c.G.level = c.D.κ c.m := congrArg c.D.κ c.hlevel
  have raw (w : CompIn c.G.comps → ℝ)
      (hw : (w = fun _ => 1) ∨ w = c.G.marker c.law) :=
    hlocal (ι := CompIn c.G.comps × Fin (Hpr + 1))
      (h := fun v => hr v.1.1.root) α q Λ c.m (c.D.Φ (c.m - 1)) (c.D.hΦ (c.m - 1))
      c.request.bufferEnd c.tf Cpad Cage Npad (c.D.κ c.G.level)
      (c.D.eps c.G.level) (rhoStar c.D kI.c₀ c.G.level) hτ
      (hκ.symm ▸ sc.diffusivity_pos) sc.radius_pos hρe heE C
      (fun v => c.G.mass c.law v.1 / w v.1 ^ 2) (weighted w hw).1 K hK
      (fun _ => ()) _ (weighted w hw).2.1.nonneg
      (by rw [he]; exact TorusCompatible.ocEpsilon_inv_natCast q Λ c.m)
      hctime hcweight hctorus hcharts
      (by simpa only [hCm, hJm, hparent, hν] using pointwise w hw)
  have hraw0 := raw (fun _ => 1) (Or.inl rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [context_copyCoeff_eq, PrepCtx.request, C, ← hparent] using hraw0.1
  · have hmeas := hraw0.2.1
    rw [← hparent] at hmeas
    convert hmeas using 1; rfl
  · simpa only [context_copyCoeff_eq, PrepCtx.request, C, ← hparent] using hraw0.2.2.1
  · simpa only [context_copyCoeff_eq, PrepCtx.request, C, ← hparent] using hraw0.2.2.2.1
  · intro w hw
    have hb := weighted w hw
    have hs := schur_of_entrywise_price _ _ Cprep _ hCprep
      (raw w hw).2.2.2.2 hb.2.1.row_sum hb.2.1.col_sum
    have hbudget : CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe =
        CI * ocEpsilon q Λ c.m ^ min (ocDelta α q / 4) τe := by
      rw [OCData.eps, c.hq, c.hΛ]
    rw [hbudget] at hs
    rw [← hparent] at hs
    convert hs using 1 <;> rfl

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The native route objects in the native instance context** (the route part of the
actual preparation context).

The statements of the native route core (`native_frame_copies` and its companions) are
elaborated with the local instances of the copied-energy files (in particular the neutral
energy-path group instance). The request-level route lemmas (such as `buffered_insertion_route`)
use only the native family instances. This module restates in that context:

* the native objects (`NativeFacts3`, `NativeExists3`, `native_exists3`) and the chosen
  objects (`NatHac3`, `NatM3`, `NatB3`, `NatL3`, `NatE3`, `NatFacts3`);
* the core rows (`native_of_realizes3`, `native_rows3`, `route_defect3`,
  `copy_solve3`);
* the weighted path energy as a seminorm on the path space with the structure of the route
  (`RouteP2`), with the rows in it (`native_rows2`, `route_defect2`), and the constant
  trace at the copy-zero slot order (`const_slot`).

The degenerate cases are as in the native route core. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul preparationWeightedLowSMul
  preparationWeightedLowSpace
attribute [local instance] preparationNeutralSlotsMonoid preparationNeutralSlotsModule

variable {ι : Type} [Fintype ι] [DecidableEq ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Part : Type*} {Ctx : Part → Type*}

/-- The facts of the native objects: the realized buffered maps `M` with their fixed point, the
buffered datum `B` with its trace, buffer bound and constant trace, the raw copied solution `L` and
the post-buffer plain maps `E` with the buffered join. -/
def NativeFacts3 (family : ChartedFamily ι h D Part Ctx) (H Kbase : ℕ) {a b c ρ ν : ℝ}
    (e Esc : ℝ) (actual : ∀ p, Ctx p)
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (π : ι → ℝ) (weights : Set (ι → ℝ)) (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i)))
    (L : (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1)))
    (E : PreparationPostPlainMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) H c b) : Prop :=
  BufferedKernelMapsRealizes P φ hac hcb M ∧ M.IsFixedPoint hac hcb ∧
  (∀ f i, truncateTorusHk (Nat.zero_le _) (B f i) = (M.full f).1 ⟨c, hac, hcb⟩ i) ∧
  (∀ r : ℝ, 0 ≤ r → r ≤ ρ → ∀ w ∈ weights, ∀ f,
    Real.sqrt (massNormSq r (fun i => π i / w i ^ 2) (fun i => (B f i).val)) ≤
      Real.sqrt (Buffer.bufferEnergyCost (Kbase + H * (D - 2))) *
        Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2) (fun i => (f i).val))) ∧
  BufferedConstantTraceStatement (fun _ => Kbase + H * (D - 2)) B ∧
  RawCopyRealizes family H (preparationNeutralSlots H D Kbase) ν c b e Esc
    (streamVel φ) actual (SlotCast B) (fun f => L (SlotCast B f)) E ∧
  BufferedPlainLayerJoinStatement hac hcb M E

/-- The native objects exist with their facts. -/
def NativeExists3 (family : ChartedFamily ι h D Part Ctx) (H Kbase : ℕ) {a b c ρ ν : ℝ}
    (e Esc : ℝ) (actual : ∀ p, Ctx p)
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (π : ι → ℝ) (weights : Set (ι → ℝ)) (hcb : c ≤ b) : Prop :=
  ∃ (hac : a ≤ c)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i)))
    (L : (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1)))
    (E : PreparationPostPlainMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) H c b),
    NativeFacts3 family H Kbase e Esc actual P φ π weights hac hcb M B L E

omit [DecidableEq ι] in
/-- The native objects in the native instance context. -/
theorem native_exists3 {family : ChartedFamily ι h D Part Ctx} {H Kbase : ℕ} {a b c ρ ν : ℝ}
    {e Esc : ℝ} {actual : ∀ p, Ctx p}
    {P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D}
    {φ : ℝ → Vec 2 → ℝ} {π : ι → ℝ} {weights : Set (ι → ℝ)} {hcb : c ≤ b}
    (hx : NativeExists family H Kbase e Esc actual P φ π weights hcb) :
    NativeExists3 family H Kbase e Esc actual P φ π weights hcb :=
  hx

omit [DecidableEq ι] in
/-- `native_of_realizes` in the native instance context. -/
theorem native_of_realizes3 {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j γ, NormedAddCommGroup (G i j γ)]
    [∀ i j γ, InnerProductSpace ℝ (G i j γ)] [∀ i j γ, FiniteDimensional ℝ (G i j γ)]
    [∀ i j γ, MeasurableSpace (G i j γ)] [∀ i j γ, BorelSpace (G i j γ)]
    [∀ i j γ, CompleteSpace (G i j γ)] {a b c ρ ν : ℝ}
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M) :
    ∀ f, ∃ (w : ∀ i, ℝ → TorusHk 1 (h i))
      (y : ∀ i j (γ : Γ i j), ℝ → TorusHk (0 + D - 1) (G i j γ)),
      IsKernelWeakSolutionTorus ν a b (streamVel φ) 0 D P.B P.C P.S f (fun _ _ => 0)
        (fun _ _ => 0) (fun i t => (M.full f).1 (Set.projIcc a b (hac.trans hcb) t) i) w y :=
  native_of_realizes P φ hac hcb M hM

/-- `native_rows` in the native instance context. -/
theorem native_rows3 (family : ChartedFamily ι h D Part Ctx) (Kbuf : ℕ)
    {a b c ρ ν : ℝ}
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (π : ι → ℝ) (weights : Set (ι → ℝ))
    (operators : ∀ w ∈ weights, KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
      (G := fun _ j _ => h j) a b ρ ν 0 D)
    (hagree : ∀ w hw, PreparationKernelDataAgreement P (operators w hw))
    (hmass : ∀ w hw, (operators w hw).π = fun i => π i / w i ^ 2)
    (hφ : IsAdmissibleStream φ) (hac : a ≤ c) (hcb : c ≤ b)
    (hd : TorusDriftData ν ρ c b (streamVel φ) Kbuf) (Θ : ℝ)
    (htheta : ∀ w hw, (operators w hw).θ = Θ)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M) (w : ι → ℝ) (hw : w ∈ weights) :
    (∀ f, preparationWeightedPathEnergy (h := h) ρ (fun i => π i / w i ^ 2) ν a b c
      (M.full f) ≤ 2 * Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2)
        (fun i => (f i).val))) ∧
    (∀ x, preparationWeightedPathEnergy (h := h) ρ (fun i => π i / w i ^ 2) ν a b c
      (preparationBufferedKernelMap hcb M.source x) ≤
        7 * |Θ| * preparationWeightedPathEnergy (h := h) ρ (fun i => π i / w i ^ 2) ν a b c x) ∧
    ∀ (x : PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b c) (t : Set.Icc a b),
      Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2) (fun i => (x.1 t i).val)) ≤
        preparationWeightedPathEnergy (h := h) ρ (fun i => π i / w i ^ 2) ν a b c x :=
  native_rows family Kbuf P φ π weights operators hagree hmass hφ hac hcb hd Θ htheta M hM w hw

omit [DecidableEq ι] in
/-- `route_defect` in the native instance context. -/
theorem route_defect3 (family : ChartedFamily ι h D Part Ctx) (H Kbase : ℕ) (hD : 2 ≤ D)
    (ν ρ a c b e Esc : ℝ) (φ : ℝ → Vec 2 → ℝ) (actual : ∀ p, Ctx p) (hac : a ≤ c) (hcb : c ≤ b)
    (hd : TorusDriftData ν ρ c b (streamVel φ) (Kbase + H * (D - 2)))
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i)))
    (hB : ∀ f i, truncateTorusHk (Nat.zero_le _) (B f i) = (M.full f).1 ⟨c, hac, hcb⟩ i)
    (hcl : CopyClauses family H Kbase ν ρ c b e Esc actual)
    (L : (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1)))
    (E : PreparationPostPlainMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) H c b)
    (hreal : RawCopyRealizes family H (preparationNeutralSlots H D Kbase) ν c b e Esc
      (streamVel φ) actual (SlotCast B) (fun f => L (SlotCast B f)) E)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (Cbuf : ℝ)
    (hbound : ∀ f, Real.sqrt (massNormSq ρ π (fun i => (B f i).val)) ≤
      Cbuf * Real.sqrt (massNormSq 1 π (fun i => (f i).val)))
    (Sr : ℝ) (hSr : 0 ≤ Sr)
    (hschur : SchurBound Sr (schurMatrix ν ρ (fun x : ι × Fin (H + 1) => π x.1)
      (preparationNeutralSlots H D Kbase) D c b
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase))))
    (PF : PreparationPlainKernelFrame
      (Buffer.kernelOperator_time_restrict P (Set.Icc_subset_Icc hac le_rfl) hcb))
    (hcoeff : ∀ i j γ d, (Buffer.kernelOperator_time_restrict P
      (Set.Icc_subset_Icc hac le_rfl) hcb).B i j γ d =
        constituentPhysical family ν e Esc actual i j γ d.val)
    (hincl : ∀ i j γ, (Buffer.kernelOperator_time_restrict P
      (Set.Icc_subset_Icc hac le_rfl) hcb).C i j γ = ContinuousLinearMap.id ℝ (h j))
    (hreserve : ∀ (l : Fin H) j, PF.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (qw : ℝ) (hqw : 0 ≤ qw) (hw : ∀ i j γ, (PF.spec i j γ).width ≤ qw * ρ)
    (Ks : ι → ℕ) (Cs : ℝ) (hCs : 0 ≤ Cs) (Bm : ι → ι → ℝ) (hBm : ∀ i j, 0 ≤ Bm i j)
    (hsampled : IsSampledEnvelope family π Ks actual c b ν e Esc ρ Cs Bm)
    (Sinc : ℝ) (hSinc0 : 0 ≤ Sinc) (hSinc : SchurBound Sinc Bm)
    (Fm : PreparationMomentBudgetParameters) (m : ℕ) (hm : 1 ≤ m) (hFL : PF.L = Fm.L)
    (hFH : H = Fm.H) (hFbuf : Cbuf = Fm.Cbuf)
    (hFsample : preparationPlainSampledConstant PF.φ PF.matrix_bound D PF.L * Cs ≤ Fm.Csample)
    (hwidth : qw ≤ Fm.Cwid * ocEpsilon Fm.q Fm.Λ m ^ Fm.σ)
    (hinc : Sinc ≤ Fm.CI * ocEpsilon Fm.q Fm.Λ m ^ Fm.θ) (hraw : Sr ≤ Fm.Cplain * Sinc) :
    ∀ (f : ∀ i, TorusHk 0 (h i)) (l : ℕ), l < H →
      preparationWeightedPathEnergy (h := h) ρ π ν a b c
        (preparationBufferedPlainLayer hac hcb M E (l + 1) f -
          preparationBufferedKernelMap hcb M.source
            (preparationBufferedPlainLayer hac hcb M E l f)) ≤
        preparationMomentDefectConstant Fm * ocEpsilon Fm.q Fm.Λ (m - 1) ^ (Fm.q * Fm.σ * Fm.L) *
          Real.sqrt (massNormSq 1 π (fun i => (f i).val)) :=
  route_defect family H Kbase hD ν ρ a c b e Esc φ actual hac hcb hd P M hM B hB hcl L E hreal
    π hπ Cbuf hbound Sr hSr hschur PF hcoeff hincl hreserve qw hqw hw Ks Cs hCs Bm
    hBm hsampled Sinc hSinc0 hSinc Fm m hm hFL hFH hFbuf hFsample hwidth hinc hraw

omit [DecidableEq ι] in
/-- `copy_solve` in the native instance context. -/
theorem copy_solve3 (family : ChartedFamily ι h D Part Ctx) (H Kbase : ℕ) {ν c b e Esc : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {actual : ∀ p, Ctx p}
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)))
    (L : (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1)))
    (E : PreparationPostPlainMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) H c b)
    (hreal : RawCopyRealizes family H (preparationNeutralSlots H D Kbase) ν c b e Esc v
      actual B (fun f => L (B f)) E) (f : ∀ i, TorusHk 0 (h i)) :
    ∃ (u : ∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1))
      (w : ∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x + 1) (h x.1)),
      IsCoupledWeakSolutionTorus ν c b v D (preparationNeutralSlots H D Kbase)
        (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
          (preparationNeutralSlots H D Kbase))
        (preparationNeutralInitial H (preparationNeutralSlots H D Kbase) (B f))
        (fun _ _ => 0) (fun _ _ => 0) u w ∧
      ∀ (t : ℝ) (ht : t ∈ Set.Icc c b),
        (∑ l : Fin (H + 1), (E l f).1 ⟨t, ht⟩) =
          CopyJoint.plainReadout (preparationNeutralSlots H D Kbase) u t :=
  copy_solve family H Kbase B L E hreal f

/-- The weighted path energy as a seminorm on the path space with the structure of the route. -/
noncomputable def RouteP2 (ρ : ℝ) (π : ι → ℝ) (ν a b c : ℝ) :=
  SeminormOn (H := ∀ i, TorusHk 0 (h i)) (V := CoupledHighHilbert (h := h) (fun _ => 0))
    (a := a) (b := b) (c := c) (fun x => preparationWeightedPathEnergy (h := h) ρ π ν a b c x)
    (fun x y => (preparationWeightedPathEnergy (h := h) ρ π ν a b c).add_le' x y)
    (fun r x => (preparationWeightedPathEnergy (h := h) ρ π ν a b c).smul' r x)

/-- The energy rows in the route seminorm. -/
theorem native_rows2 (family : ChartedFamily ι h D Part Ctx) (Kbuf : ℕ)
    {a b c ρ ν : ℝ}
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (π : ι → ℝ) (weights : Set (ι → ℝ))
    (operators : ∀ w ∈ weights, KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
      (G := fun _ j _ => h j) a b ρ ν 0 D)
    (hagree : ∀ w hw, PreparationKernelDataAgreement P (operators w hw))
    (hmass : ∀ w hw, (operators w hw).π = fun i => π i / w i ^ 2)
    (hφ : IsAdmissibleStream φ) (hac : a ≤ c) (hcb : c ≤ b)
    (hd : TorusDriftData ν ρ c b (streamVel φ) Kbuf) (Θ : ℝ)
    (htheta : ∀ w hw, (operators w hw).θ = Θ)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M) (w : ι → ℝ) (hw : w ∈ weights) :
    (∀ f, RouteP2 (h := h) ρ (fun i => π i / w i ^ 2) ν a b c
      (M.full f) ≤ 2 * Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2)
        (fun i => (f i).val))) ∧
    (∀ x, RouteP2 (h := h) ρ (fun i => π i / w i ^ 2) ν a b c
      (preparationBufferedKernelMap hcb M.source x) ≤
        7 * |Θ| * RouteP2 (h := h) ρ (fun i => π i / w i ^ 2) ν a b c x) ∧
    ∀ (x : PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b c) (t : Set.Icc a b),
      Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2) (fun i => (x.1 t i).val)) ≤
        RouteP2 (h := h) ρ (fun i => π i / w i ^ 2) ν a b c x :=
  native_rows3 family Kbuf P φ π weights operators hagree hmass hφ hac hcb hd Θ htheta M hM w hw

omit [DecidableEq ι] in
/-- The priced defect row in the route seminorm and the route difference. -/
theorem route_defect2 (family : ChartedFamily ι h D Part Ctx) (H Kbase : ℕ) (hD : 2 ≤ D)
    (ν ρ a c b e Esc : ℝ) (φ : ℝ → Vec 2 → ℝ) (actual : ∀ p, Ctx p) (hac : a ≤ c) (hcb : c ≤ b)
    (hd : TorusDriftData ν ρ c b (streamVel φ) (Kbase + H * (D - 2)))
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i)))
    (hB : ∀ f i, truncateTorusHk (Nat.zero_le _) (B f i) = (M.full f).1 ⟨c, hac, hcb⟩ i)
    (hcl : CopyClauses family H Kbase ν ρ c b e Esc actual)
    (L : (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1)))
    (E : PreparationPostPlainMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) H c b)
    (hreal : RawCopyRealizes family H (preparationNeutralSlots H D Kbase) ν c b e Esc
      (streamVel φ) actual (SlotCast B) (fun f => L (SlotCast B f)) E)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (Cbuf : ℝ)
    (hbound : ∀ f, Real.sqrt (massNormSq ρ π (fun i => (B f i).val)) ≤
      Cbuf * Real.sqrt (massNormSq 1 π (fun i => (f i).val)))
    (Sr : ℝ) (hSr : 0 ≤ Sr)
    (hschur : SchurBound Sr (schurMatrix ν ρ (fun x : ι × Fin (H + 1) => π x.1)
      (preparationNeutralSlots H D Kbase) D c b
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase))))
    (PF : PreparationPlainKernelFrame
      (Buffer.kernelOperator_time_restrict P (Set.Icc_subset_Icc hac le_rfl) hcb))
    (hcoeff : ∀ i j γ d, (Buffer.kernelOperator_time_restrict P
      (Set.Icc_subset_Icc hac le_rfl) hcb).B i j γ d =
        constituentPhysical family ν e Esc actual i j γ d.val)
    (hincl : ∀ i j γ, (Buffer.kernelOperator_time_restrict P
      (Set.Icc_subset_Icc hac le_rfl) hcb).C i j γ = ContinuousLinearMap.id ℝ (h j))
    (hreserve : ∀ (l : Fin H) j, PF.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (qw : ℝ) (hqw : 0 ≤ qw) (hw : ∀ i j γ, (PF.spec i j γ).width ≤ qw * ρ)
    (Ks : ι → ℕ) (Cs : ℝ) (hCs : 0 ≤ Cs) (Bm : ι → ι → ℝ) (hBm : ∀ i j, 0 ≤ Bm i j)
    (hsampled : IsSampledEnvelope family π Ks actual c b ν e Esc ρ Cs Bm)
    (Sinc : ℝ) (hSinc0 : 0 ≤ Sinc) (hSinc : SchurBound Sinc Bm)
    (Fm : PreparationMomentBudgetParameters) (m : ℕ) (hm : 1 ≤ m) (hFL : PF.L = Fm.L)
    (hFH : H = Fm.H) (hFbuf : Cbuf = Fm.Cbuf)
    (hFsample : preparationPlainSampledConstant PF.φ PF.matrix_bound D PF.L * Cs ≤ Fm.Csample)
    (hwidth : qw ≤ Fm.Cwid * ocEpsilon Fm.q Fm.Λ m ^ Fm.σ)
    (hinc : Sinc ≤ Fm.CI * ocEpsilon Fm.q Fm.Λ m ^ Fm.θ) (hraw : Sr ≤ Fm.Cplain * Sinc) :
    ∀ (f : ∀ i, TorusHk 0 (h i)) (l : ℕ), l < H →
      RouteP2 (h := h) ρ π ν a b c
        (pathSub (preparationBufferedPlainLayer hac hcb M E (l + 1) f)
          (preparationBufferedKernelMap hcb M.source
            (preparationBufferedPlainLayer hac hcb M E l f))) ≤
        preparationMomentDefectConstant Fm * ocEpsilon Fm.q Fm.Λ (m - 1) ^ (Fm.q * Fm.σ * Fm.L) *
          Real.sqrt (massNormSq 1 π (fun i => (f i).val)) := by
  intro f l hl
  refine le_trans (le_of_eq ?_) ((route_defect3 family H Kbase hD ν ρ a c b e Esc φ actual
    hac hcb hd P M hM B hB hcl L E hreal π hπ Cbuf hbound Sr hSr hschur PF hcoeff hincl hreserve
    qw hqw hw Ks Cs hCs Bm hBm hsampled Sinc hSinc0 hSinc Fm m hm hFL hFH hFbuf hFsample hwidth
    hinc hraw f l hl).trans (le_of_eq ?_))
  · rfl
  · rfl

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The constant trace of the buffered datum at the copy-zero slot order. -/
theorem const_slot {H Kbase : ℕ}
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i)))
    (hB : BufferedConstantTraceStatement (fun _ => Kbase + H * (D - 2)) B) :
    ∀ (cv : ∀ i, h i) (f : ∀ i, TorusHk 0 (h i)),
      (∀ i, (f i).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun _ => cv i) →
      ∀ i, (truncateTorusHk (Nat.zero_le _) (SlotCast B f i)).toFunction.jet (valueIndex2 0)
        =ᵐ[volume.restrict unitCube] fun _ => cv i :=
  hB

section Choice3

variable {family : ChartedFamily ι h D Part Ctx} {H Kbase : ℕ} {a b c ρ ν : ℝ} {e Esc : ℝ}
  {actual : ∀ p, Ctx p}
  {P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
    a b ρ ν 0 D}
  {φ : ℝ → Vec 2 → ℝ} {π : ι → ℝ} {weights : Set (ι → ℝ)} {hcb : c ≤ b}

omit [DecidableEq ι] in
/-- The buffer order of the chosen native objects. -/
theorem NatHac3 (hx : NativeExists3 family H Kbase e Esc actual P φ π weights hcb) :
    a ≤ c :=
  Classical.choose hx

/-- The chosen buffered maps. -/
noncomputable def NatM3 (hx : NativeExists3 family H Kbase e Esc actual P φ π weights hcb) :=
  Classical.choose (Classical.choose_spec hx)

/-- The chosen buffered datum. -/
noncomputable def NatB3 (hx : NativeExists3 family H Kbase e Esc actual P φ π weights hcb) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec hx))

/-- The chosen raw copied solution. -/
noncomputable def NatL3 (hx : NativeExists3 family H Kbase e Esc actual P φ π weights hcb) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hx)))

/-- The chosen post-buffer plain maps. -/
noncomputable def NatE3 (hx : NativeExists3 family H Kbase e Esc actual P φ π weights hcb) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec hx))))

omit [DecidableEq ι] in
/-- The facts of the chosen native objects. -/
theorem NatFacts3 (hx : NativeExists3 family H Kbase e Esc actual P φ π weights hcb) :
    NativeFacts3 family H Kbase e Esc actual P φ π weights (NatHac3 hx) hcb (NatM3 hx)
      (NatB3 hx) (NatL3 hx) (NatE3 hx) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec hx))))

end Choice3
end

/-! **The rows of the native route in the form of the request** (the route part of the
actual preparation context).

Over an abstract family (ι, h), in the native instance context, with the data identity
`e₀ = PiEquiv`, the seminorm `p_w = RouteP2 ρ (π / w²) ν a b c` and the native objects
`M, B, L, E` with their facts (`NativeFacts3`), each row is stated literally as the matching
hypothesis of the request-level packaging (`routePkg_rows`), with the input norm unfolded:

* `row_native`, `row_trace`, `row_kernel`, `row_full`, `row_buffer`,
  `row_solve` and the priced defect row `row_defect`.
* `OpsG` (the weighted operators of a tower), `CopyG` (the copied-coefficient clauses)
  and `SourceG` (the plain frame and sampled source) restate the request-level inputs over the
  abstract family.

For `H = 0` there is no defect row; an empty index type `ι` and the zero datum are
allowed. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul preparationWeightedLowSMul
  preparationWeightedLowSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Part : Type*} {Ctx : Part → Type*}

/-- The weighted operators of a tower: one operator per weight with the data of `P`, the mass
`π / w²` and the price `Θ`. -/
def OpsG (family : ChartedFamily ι h D Part Ctx) {a b ρ ν : ℝ}
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (π : ι → ℝ) (weights : Set (ι → ℝ)) (Θ : ℝ) : Prop :=
  ∃ operators : ∀ w ∈ weights, KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
      (G := fun _ j _ => h j) a b ρ ν 0 D,
    (∀ w hw, PreparationKernelDataAgreement P (operators w hw)) ∧
    (∀ w hw, (operators w hw).π = fun i => π i / w i ^ 2) ∧
    ∀ w hw, (operators w hw).θ = Θ

/-- The copied-coefficient clauses over an abstract family. -/
def CopyG (family : ChartedFamily ι h D Part Ctx) (H : ℕ) (K : ι × Fin (H + 1) → ℕ)
    (ν ρ c b e Esc : ℝ) (actual : ∀ p, Ctx p) (π : ι → ℝ) (weights : Set (ι → ℝ))
    (Sr : ℝ) : Prop :=
  (∀ x y d, coefficientSeminorm ρ (K x) c b
    (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual K x y d) ≠ ⊤) ∧
  (∀ x y d, Measurable (fun p : Set.Icc c b × Vec 2 =>
    edgeCoefficient (preparationNeutralChain family H) ν e Esc actual K x y d p.1 p.2)) ∧
  (∀ x y d t, t ∈ Set.Icc c b → ContDiff ℝ (K x : ℕ)
    (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual K x y d t)) ∧
  (∀ x y d t, t ∈ Set.Icc c b → IsZ2Periodic
    (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual K x y d t)) ∧
  ∀ w : ι → ℝ, w ∈ weights →
    SchurBound Sr (schurMatrix ν ρ (fun x : ι × Fin (H + 1) => π x.1 / w x.1 ^ 2) K D c b
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual K))

/-- The plain frame and sampled source over an abstract family. -/
def SourceG (family : ChartedFamily ι h D Part Ctx) (H : ℕ) (K : ι × Fin (H + 1) → ℕ)
    {a b c ρ ν : ℝ}
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (hac : a ≤ c) (hcb : c ≤ b) (φ₀ : Vec 2 → ℝ) (Γk : ℝ) (Lpr : ℕ) (qw Cs Sinc e Esc : ℝ)
    (actual : ∀ p, Ctx p) (π : ι → ℝ) (weights : Set (ι → ℝ)) : Prop :=
  ∃ PF : PreparationPlainKernelFrame (Buffer.kernelOperator_time_restrict P
      (Set.Icc_subset_Icc hac le_rfl) hcb),
    PF.φ = φ₀ ∧ PF.matrix_bound = Γk ∧ PF.L = Lpr ∧
    (∀ (l : Fin H) j, PF.K j ≤ K (j, l.castSucc)) ∧
    (∀ i j γ, (PF.spec i j γ).width ≤ qw * ρ) ∧
    (∀ i j γ d, (Buffer.kernelOperator_time_restrict P
      (Set.Icc_subset_Icc hac le_rfl) hcb).B i j γ d =
        constituentPhysical family ν e Esc actual i j γ d.val) ∧
    ∀ w : ι → ℝ, w ∈ weights →
      ∃ (Ks : ι → ℕ) (Bm : ι → ι → ℝ),
        (∀ i j, 0 ≤ Bm i j) ∧
        IsSampledEnvelope family (fun i => π i / w i ^ 2) Ks actual c b ν e Esc ρ Cs Bm ∧
        SchurBound Sinc Bm

section Rows

variable (family : ChartedFamily ι h D Part Ctx) {a b c ρ ν : ℝ}
  (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
    a b ρ ν 0 D)
  (φ : ℝ → Vec 2 → ℝ) (hac : a ≤ c) (hcb : c ≤ b)
  (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
    (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)

/-- The native row of the realized buffered maps. -/
theorem row_native (hM : BufferedKernelMapsRealizes P φ hac hcb M) :
    ∀ f : ∀ i, TorusHk 0 (h i),
      ∃ (W : ∀ v, ℝ → TorusHk 1 (h v))
        (Y : ∀ v u (_γ : family.Γ v u), ℝ → TorusHk (0 + D - 1) (h u)),
        IsKernelWeakSolutionTorus ν a b (streamVel φ) 0 D P.B P.C P.S f (fun _ _ => 0)
          (fun _ _ => 0) (fun v t => (PiEquiv (h := h)).symm
            ((M.full (PiEquiv (h := h) f)).1 (Set.projIcc a b (hac.trans hcb) t)) v) W Y :=
  fun f => native_of_realizes3 P φ hac hcb M hM f

/-- The trace row in the route seminorm. -/
theorem row_trace (Kbuf : ℕ) (π : ι → ℝ) (weights : Set (ι → ℝ)) (Θ : ℝ)
    (hops : OpsG family P π weights Θ) (hφ : IsAdmissibleStream φ)
    (hd : TorusDriftData ν ρ c b (streamVel φ) Kbuf)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M) :
    ∀ w : ι → ℝ, w ∈ weights →
      ∀ (x : PreparationEnergyPath (∀ i, TorusHk 0 (h i))
          (CoupledHighHilbert (h := h) (fun _ => 0)) a b c) (t : Set.Icc a b),
        Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2)
          (fun i => ((PiEquiv (h := h)).symm (x.1 t) i).val)) ≤
          RouteP2 (h := h) ρ (fun i => π i / w i ^ 2) ν a b c x := by
  obtain ⟨operators, hagree, hmass, htheta⟩ := hops
  intro w hw x t
  exact (native_rows2 family Kbuf P φ π weights operators hagree hmass hφ hac hcb hd Θ
    htheta M hM w hw).2.2 x t

/-- The kernel row in the route seminorm. -/
theorem row_kernel (Kbuf : ℕ) (π : ι → ℝ) (weights : Set (ι → ℝ)) (Θ : ℝ)
    (hops : OpsG family P π weights Θ) (hφ : IsAdmissibleStream φ)
    (hd : TorusDriftData ν ρ c b (streamVel φ) Kbuf)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M) :
    ∀ w : ι → ℝ, w ∈ weights → ∀ x,
      RouteP2 (h := h) ρ (fun i => π i / w i ^ 2) ν a b c
        (preparationBufferedKernelMap hcb M.source x) ≤
        7 * |Θ| * RouteP2 (h := h) ρ (fun i => π i / w i ^ 2) ν a b c x := by
  obtain ⟨operators, hagree, hmass, htheta⟩ := hops
  intro w hw x
  exact (native_rows2 family Kbuf P φ π weights operators hagree hmass hφ hac hcb hd Θ
    htheta M hM w hw).2.1 x

/-- The full row in the route seminorm. -/
theorem row_full (Kbuf : ℕ) (π : ι → ℝ) (weights : Set (ι → ℝ)) (Θ : ℝ)
    (hops : OpsG family P π weights Θ) (hφ : IsAdmissibleStream φ)
    (hd : TorusDriftData ν ρ c b (streamVel φ) Kbuf)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M) :
    ∀ w : ι → ℝ, w ∈ weights → ∀ f : ∀ i, TorusHk 0 (h i),
      RouteP2 (h := h) ρ (fun i => π i / w i ^ 2) ν a b c
        (M.full (PiEquiv (h := h) f)) ≤
        2 * Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2) (fun i => (f i).val)) := by
  obtain ⟨operators, hagree, hmass, htheta⟩ := hops
  intro w hw f
  exact (native_rows2 family Kbuf P φ π weights operators hagree hmass hφ hac hcb hd Θ
    htheta M hM w hw).1 f

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The buffer row at an old radius. -/
theorem row_buffer {H Kbase : ℕ} (π : ι → ℝ) (weights : Set (ι → ℝ))
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i)))
    (hbound : ∀ r : ℝ, 0 ≤ r → r ≤ ρ → ∀ w ∈ weights, ∀ f,
      Real.sqrt (massNormSq r (fun i => π i / w i ^ 2) (fun i => (B f i).val)) ≤
        Real.sqrt (Buffer.bufferEnergyCost (Kbase + H * (D - 2))) *
          Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2) (fun i => (f i).val)))
    (ρold : ℝ) (h0 : 0 ≤ ρold) (h1 : ρold ≤ ρ) :
    ∀ w : ι → ℝ, w ∈ weights → ∀ f : ∀ i, TorusHk 0 (h i),
      Real.sqrt (∑ i, (π i / w i ^ 2)⁻¹ *
        torusHkNorm ρold (le_refl (preparationNeutralSlots H D Kbase (i, 0)))
          (SlotCast B f i) ^ 2) ≤
        Real.sqrt (Buffer.bufferEnergyCost (Kbase + H * (D - 2))) *
          Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2) (fun i => (f i).val)) :=
  fun w hw f => gate_buffer (fun i => π i / w i ^ 2) ρold _ B
    (fun f => hbound ρold h0 h1 w hw f) f

/-- The copied solution row. -/
theorem row_solve {H Kbase : ℕ} {e Esc : ℝ} {actual : ∀ p, Ctx p}
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i)))
    (L : (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1)))
    (E : PreparationPostPlainMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) H c b)
    (hreal : RawCopyRealizes family H (preparationNeutralSlots H D Kbase) ν c b e Esc
      (streamVel φ) actual (SlotCast B) (fun f => L (SlotCast B f)) E) :
    ∀ f : ∀ i, TorusHk 0 (h i),
      ∃ (u : ∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1))
        (w : ∀ x : ι × Fin (H + 1), ℝ →
          TorusHk (preparationNeutralSlots H D Kbase x + 1) (h x.1)),
        IsCoupledWeakSolutionTorus ν c b (streamVel φ) D (preparationNeutralSlots H D Kbase)
          (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
            (preparationNeutralSlots H D Kbase))
          (preparationNeutralInitial H (preparationNeutralSlots H D Kbase) (SlotCast B f))
          (fun _ _ => 0) (fun _ _ => 0) u w ∧
        ∀ (t : ℝ) (ht : t ∈ Set.Icc c b),
          (PiEquiv (h := h)).symm
            (∑ l : Fin (H + 1), (E l (PiEquiv (h := h) f)).1 ⟨t, ht⟩) =
            CopyJoint.plainReadout (preparationNeutralSlots H D Kbase) u t :=
  fun f => copy_solve3 family H Kbase (SlotCast B) L E hreal f

/-- The priced defect row in the route seminorm. -/
theorem row_defect (H Kbase : ℕ) (hD : 2 ≤ D) (e Esc : ℝ) (actual : ∀ p, Ctx p)
    (hd : TorusDriftData ν ρ c b (streamVel φ) (Kbase + H * (D - 2)))
    (π : ι → ℝ) (weights : Set (ι → ℝ)) (Θ : ℝ) (hops : OpsG family P π weights Θ)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i)))
    (L : (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1)))
    (E : PreparationPostPlainMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) H c b)
    (hfacts : NativeFacts3 family H Kbase e Esc actual P φ π weights hac hcb M B L E)
    (Sr : ℝ) (hSr : 0 ≤ Sr)
    (hcopy : CopyG family H (preparationNeutralSlots H D Kbase) ν ρ c b e Esc actual π
      weights Sr)
    (φ₀ : Vec 2 → ℝ) (Γk : ℝ) (Lpr : ℕ) (qw Cs Sinc : ℝ) (hqw : 0 ≤ qw) (hCs : 0 ≤ Cs)
    (hSinc0 : 0 ≤ Sinc)
    (hsrc : SourceG family H (preparationNeutralSlots H D Kbase) P hac hcb φ₀ Γk Lpr qw Cs
      Sinc e Esc actual π weights)
    (hC : ∀ i j γ, P.C i j γ = ContinuousLinearMap.id ℝ (h j))
    (Fm : PreparationMomentBudgetParameters) (m : ℕ) (hm : 1 ≤ m) (hFL : Lpr = Fm.L)
    (hFH : H = Fm.H)
    (hFbuf : Real.sqrt (Buffer.bufferEnergyCost (Kbase + H * (D - 2))) = Fm.Cbuf)
    (hFsample : preparationPlainSampledConstant φ₀ Γk D Lpr * Cs ≤ Fm.Csample)
    (hwidth : qw ≤ Fm.Cwid * ocEpsilon Fm.q Fm.Λ m ^ Fm.σ)
    (hinc : Sinc ≤ Fm.CI * ocEpsilon Fm.q Fm.Λ m ^ Fm.θ) (hraw : Sr ≤ Fm.Cplain * Sinc) :
    ∀ w : ι → ℝ, w ∈ weights → ∀ (f : ∀ i, TorusHk 0 (h i)) (l : ℕ), l < H →
      RouteP2 (h := h) ρ (fun i => π i / w i ^ 2) ν a b c
        (pathSub (preparationBufferedPlainLayer hac hcb M E (l + 1) (PiEquiv (h := h) f))
          (preparationBufferedKernelMap hcb M.source
            (preparationBufferedPlainLayer hac hcb M E l (PiEquiv (h := h) f)))) ≤
        preparationMomentDefectConstant Fm * ocEpsilon Fm.q Fm.Λ (m - 1) ^ (Fm.q * Fm.σ * Fm.L) *
          Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2) (fun i => (f i).val)) := by
  obtain ⟨operators, -, hmass, -⟩ := hops
  obtain ⟨hM, -, hB, hbound, -, hreal, -⟩ := hfacts
  obtain ⟨hfin, hmeas, hsmooth, hper, hschur⟩ := hcopy
  obtain ⟨PF, hφ, hΓ, hL, hreserve, hwid, hcoeff, hsamp⟩ := hsrc
  intro w hw f l hl
  obtain ⟨Ks, Bm, hBm, hsampled, hSinc⟩ := hsamp w hw
  have hπ : ∀ i, 0 < π i / w i ^ 2 := fun i => by
    have := (operators w hw).hπ i
    rw [hmass w hw] at this
    exact this
  have hρ : 0 ≤ ρ := P.radius_pos.le
  have hsample' : preparationPlainSampledConstant PF.φ PF.matrix_bound D PF.L * Cs ≤
      Fm.Csample := by
    rw [hφ, hΓ, hL]
    exact hFsample
  exact route_defect2 family H Kbase hD ν ρ a c b e Esc φ actual hac hcb hd P M hM B hB
    ⟨hfin, hmeas, hsmooth, hper⟩ L E hreal (fun i => π i / w i ^ 2) hπ _
    (hbound ρ hρ le_rfl w hw) Sr hSr (hschur w hw) PF hcoeff hC hreserve qw hqw hwid Ks Cs
    hCs Bm hBm hsampled Sinc hSinc0 hSinc Fm m hm (hL.trans hFL) hFH hFbuf hsample' hwidth
    hinc hraw (PiEquiv (h := h) f) l hl

end Rows
end

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
section
public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The copied coefficient callback with its constants chosen before root spaces. -/

/-- Both weights of the same copied family satisfy the exact coefficient clauses,
with one sampled constant and one level floor at the fixed choices. -/
theorem copyCoeffPiece (α s : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    CopyCoeffPieceStatement α s q ζ := by
  intro Λg g₀ orders Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr
    Acl Naux Nout Kres npad σ₀ a σ sX sZ Ce kS kI CI Cw j₀ hf x hx
  let R : PreparationEarlyOrderRequest :=
    { Λ := Λ, Q := Q, τe := τe, D₀ := D₀, H := H, N := N, p := p, Lpr := Lpr, Nout := Nout }
  let Hpr := R.depth α q
  let Kbuf := R.buffer α q
  let Ks := max Kbuf (orders R).Ks
  let Jm := max (Kbuf + R.dimension + 2) (orders R).Jm
  obtain ⟨Cpad, Cage, Npad, Cchart, mch, _, _, hmch, hcharts⟩ :=
    nativeShortChartCertificate hα₀ hα₁ hs₀ hs₁ hq hζ Λ hf.hΛ
  obtain ⟨Cprep, hprep, hlocal⟩ :=
    localPreparationCoefficientData.{0, 0, 0, 0} R.dimension Kbuf Jm Jm
      (le_max_left _ _) (le_max_left _ _) kI.Cm Cchart
  let mStar := max mch (max x.1.2.1 x.1.2.2.2.2)
  refine ⟨(Cprep, mStar), ?_, ?_⟩
  · exact zero_le_one.trans hprep
  · intro hr _ _ _ _ _ _ _ c hm
    have hmchart : mch ≤ c.m := (le_max_left _ _).trans hm
    have hmenv : x.1.2.1 ≤ c.m :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hm
    have hmscalar : x.1.2.2.2.2 ≤ c.m :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hm
    have hn := preparation_context_numeric_orders hα₀ hα₁ hs₀ hs₁ hq hf
    have sc := preparation_context_scalar_inputs c hf.hΛ hζ hn.1 (g₀ Λ)
      x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2 hx.1.2.2.2.2.2.1 hmscalar
    let K : CompIn c.G.comps × Fin (Hpr + 1) → ℕ :=
      Slots Hpr R.dimension Nout Lpr
    have hK : ∀ v, K v ≤ Kbuf := fun v =>
      (preparation_descending_copy_orders R.dimension Nout Lpr Hpr v).1
    let kenv := preparationEnvelopeOrders kI Ks (orders R).Ks (orders R).Ls Jm
    have hcopy : NativeCopyEnvelopesStatement c.G kenv (Set.Icc c.s₀ c.tf)
        (rhoStar c.D kI.c₀ c.G.level) Hpr K :=
      hx.1.2.1 c hmenv K (fun v => (hK v).trans (le_max_left _ _))
    apply copyCoeffAt_of_context c hq.1 hf.hΛ hn.1 hx.1.2.2.2.2.2.2.2
      (g₀ Λ) x.1.2.2.1 x.1.2.2.2.1 sc Kbuf Jm Cpad Cage Npad Cchart Cprep
      (zero_le_one.trans hprep) hlocal ?_ K hK kenv rfl rfl hcopy
      ((by norm_num : 1 ≤ 2).trans (hmch.trans hmchart))
    intro aa bb _ hab _ hlen
    obtain ⟨l₀, P, hcert⟩ :=
      hcharts c.D c.hα c.hq c.hΛ c.hseq c.Mnat c.m hmchart
        (c.m_le_M.trans c.hMnat) c.G.actualFamily
        (fun pc => by simpa only [GenStage.actualFamily, c.hlevel] using c.hinv.1.1 pc) aa bb Jm hab hlen
    exact ⟨l₀, P, preparation_neutral_preparation c.G.actualFamily Hpr α q Λ c.m
      (c.D.Φ (c.m - 1)) (c.D.hΦ (c.m - 1)) aa bb Cpad Cage Npad Jm Cchart l₀ P hcert⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The route package of a request** (the route part of the actual preparation context).

At a request `F` with a native tower `T` at the buffer order `K_base + H_pr (D − 2)` (the
copy-zero slot):

* `request_native`: the native objects (`RouteHx3`) from the native buffer input
  (`preparation_native_buffer_input`), the native frame and the copies (`native_frame_copies`).
* `req_native`, `req_trace`, `req_kernel`, `req_full`, `req_const`,
  `req_buf`, `req_solve`, `req_defect`: the named request rows of the chosen native
  objects, instances of the rows `row_native`, …, `row_defect` (the chosen objects are elaborated as
  `(NatM3 hx : _)`, without propagating the expected type).
* `request_routePkg_of_native`, `request_routePkg`: the route package `RoutePkg` with
  `β = 7|Θ|`, `C_full = 2`, `C_def = preparationMomentDefectConstant F_m` and `L = q σ L`, from the
  scalar window/drift facts, the copied-coefficient clauses (`CopyCoeffAt`), the plain-frame and
  sampled-source clauses (`SourceAt`) and the moment-budget parameters `F_m`.

For `H_pr = 0` there is no defect; an empty component family and the zero datum are
allowed. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul preparationWeightedLowSMul
  preparationWeightedLowSpace

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The native objects of a request exist (at its tower and window), in the route context. -/
abbrev RouteHx3 (F : Request hr D Dm bw j₀) (Kbase : ℕ) {CK : ℕ → ℝ} {Θ : ℝ}
    (T : PreparationNativeTower F (Kbase + F.Hpr * (Dm - 2)) CK Θ)
    (hcb : F.bufferEnd ≤ F.tf) : Prop :=
  NativeExists3 (ι := CompIn F.G.comps) (h := fun i : CompIn F.G.comps => hr i.1.root)
    F.G.actualFamily F.Hpr Kbase (D.eps F.G.level) (D.eps (F.G.level - 1)) (fun _ => ())
    (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩) (D.Φ F.G.level)
    (F.G.mass F.law) {w | (w = fun _ => 1) ∨ w = F.G.marker F.law} hcb

/-- **The native objects of a request.** -/
theorem request_native (F : Request hr D Dm bw j₀) (hD : 2 ≤ Dm) {Kbase : ℕ}
    {CK : ℕ → ℝ} {Θ : ℝ} (T : PreparationNativeTower F (Kbase + F.Hpr * (Dm - 2)) CK Θ)
    (slow : ℝ) (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < slow)
    (hs₁ : slow < (1 - D.α) / 2) (hq : IsAdmissibleQ D.α slow D.q) (hζ : IsFastProfile D.ζ)
    (hΛ : 128 ≤ D.Λ) (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ) (hi : 1 ≤ F.G.level)
    (hc₀ : 0 < F.c₀) (hcap : F.c₀ ≤ Buffer.exists_molecular_uniform_constants.choose)
    (hcb : F.bufferEnd ≤ F.tf) (hκ : 0 < D.κ F.G.level) (hρ : 0 < rhoStar D F.c₀ F.G.level)
    (hdrift : Providers.WeakGen.Comparison.TorusDriftData (D.κ F.G.level)
      (rhoStar D F.c₀ F.G.level) F.bufferEnd F.tf (streamVel (D.Φ F.G.level))
      (Kbase + F.Hpr * (Dm - 2)))
    {Sr : ℝ} (hcopy : CopyCoeffAt F (preparationNeutralSlots F.Hpr Dm Kbase) Sr) :
    RouteHx3 F Kbase T hcb := by
  have hI := preparation_native_buffer_input F T slow hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hseq hi hc₀
    hcap hcb
  obtain ⟨I⟩ := hI
  have hcl : CopyClauses F.G.actualFamily F.Hpr Kbase (D.κ F.G.level)
      (rhoStar D F.c₀ F.G.level) F.bufferEnd F.tf (D.eps F.G.level) (D.eps (F.G.level - 1))
      (fun _ => ()) := ⟨hcopy.1, hcopy.2.1, hcopy.2.2.1, hcopy.2.2.2.1⟩
  exact native_exists3 (native_frame_copies (ι := CompIn F.G.comps)
    (h := fun i : CompIn F.G.comps => hr i.1.root) F.G.actualFamily F.Hpr Kbase hD
    (c := F.bufferEnd) rfl hκ hρ (D.eps F.G.level) (D.eps (F.G.level - 1)) (fun _ => ())
    (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩) D F.G.level (F.G.mass F.law)
    {w | (w = fun _ => 1) ∨ w = F.G.marker F.law} I hcb hdrift hcl)


/-- The route seminorm of a request. -/
def ReqP (F : Request hr D Dm bw j₀) (w : CompIn F.G.comps → ℝ) :=
  RouteP2 (h := fun i : CompIn F.G.comps => hr i.1.root) (rhoStar D F.c₀ F.G.level)
    (fun i => F.G.mass F.law i / w i ^ 2) (D.κ F.G.level) F.s F.tf F.bufferEnd

/-- The weighted operators of a native tower. -/
theorem req_ops (F : Request hr D Dm bw j₀) {Kt : ℕ} {CK : ℕ → ℝ} {Θ : ℝ}
    (T : PreparationNativeTower F Kt CK Θ) :
    OpsG (ι := CompIn F.G.comps) (h := fun i : CompIn F.G.comps => hr i.1.root)
      F.G.actualFamily (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩)
      (F.G.mass F.law) {w | (w = fun _ => 1) ∨ w = F.G.marker F.law} Θ :=
  ⟨fun w hw => T.operators w hw ⟨0, Nat.succ_pos _⟩,
    fun w hw => ⟨(T.coefficient _ (Or.inl rfl) _).trans (T.coefficient w hw _).symm,
      (T.inclusion _ (Or.inl rfl) _).trans (T.inclusion w hw _).symm,
      (T.kernel _ (Or.inl rfl) _).trans (T.kernel w hw _).symm⟩,
    fun w hw => T.mass w hw _, fun w hw => T.price w hw _⟩

/-- The data identity of a request. -/
abbrev ReqE (F : Request hr D Dm bw j₀) :=
  PiEquiv (ι := CompIn F.G.comps) (h := fun i : CompIn F.G.comps => hr i.1.root)

/-- The native row of the chosen objects. -/
theorem req_native (F : Request hr D Dm bw j₀) {Kbase : ℕ} {CK : ℕ → ℝ} {Θ : ℝ}
    (T : PreparationNativeTower F (Kbase + F.Hpr * (Dm - 2)) CK Θ)
    (hcb : F.bufferEnd ≤ F.tf) (hx : RouteHx3 F Kbase T hcb) :
    NativeRow F T (NatHac3 hx) hcb (NatM3 hx : _) (ReqE F : _) :=
  row_native F.G.actualFamily (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩)
    (D.Φ F.G.level) (NatHac3 hx) hcb (NatM3 hx : _) ((NatFacts3 hx : _).1)

/-- The trace row of the chosen objects. -/
theorem req_trace (F : Request hr D Dm bw j₀) {Kbase : ℕ} {CK : ℕ → ℝ} {Θ : ℝ}
    (T : PreparationNativeTower F (Kbase + F.Hpr * (Dm - 2)) CK Θ)
    (hcb : F.bufferEnd ≤ F.tf) (hx : RouteHx3 F Kbase T hcb)
    (hdrift : Providers.WeakGen.Comparison.TorusDriftData (D.κ F.G.level)
      (rhoStar D F.c₀ F.G.level) F.bufferEnd F.tf (streamVel (D.Φ F.G.level))
      (Kbase + F.Hpr * (Dm - 2))) :
    TraceRow F (ReqE F : _) (ReqP F : _) :=
  row_trace F.G.actualFamily (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩)
    (D.Φ F.G.level) (NatHac3 hx) hcb (NatM3 hx : _) _ (F.G.mass F.law)
    {w | (w = fun _ => 1) ∨ w = F.G.marker F.law} Θ (req_ops F T) (D.hΦ F.G.level) hdrift
    ((NatFacts3 hx : _).1)


/-- The kernel row of the chosen objects. -/
theorem req_kernel (F : Request hr D Dm bw j₀) {Kbase : ℕ} {CK : ℕ → ℝ} {Θ : ℝ}
    (T : PreparationNativeTower F (Kbase + F.Hpr * (Dm - 2)) CK Θ)
    (hcb : F.bufferEnd ≤ F.tf) (hx : RouteHx3 F Kbase T hcb)
    (hdrift : Providers.WeakGen.Comparison.TorusDriftData (D.κ F.G.level)
      (rhoStar D F.c₀ F.G.level) F.bufferEnd F.tf (streamVel (D.Φ F.G.level))
      (Kbase + F.Hpr * (Dm - 2))) :
    KernelRow F hcb (NatM3 hx : _) (ReqP F : _) (7 * |Θ|) :=
  row_kernel F.G.actualFamily (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩)
    (D.Φ F.G.level) (NatHac3 hx) hcb (NatM3 hx : _) _ (F.G.mass F.law)
    {w | (w = fun _ => 1) ∨ w = F.G.marker F.law} Θ (req_ops F T) (D.hΦ F.G.level) hdrift
    ((NatFacts3 hx : _).1)

/-- The full row of the chosen objects. -/
theorem req_full (F : Request hr D Dm bw j₀) {Kbase : ℕ} {CK : ℕ → ℝ} {Θ : ℝ}
    (T : PreparationNativeTower F (Kbase + F.Hpr * (Dm - 2)) CK Θ)
    (hcb : F.bufferEnd ≤ F.tf) (hx : RouteHx3 F Kbase T hcb)
    (hdrift : Providers.WeakGen.Comparison.TorusDriftData (D.κ F.G.level)
      (rhoStar D F.c₀ F.G.level) F.bufferEnd F.tf (streamVel (D.Φ F.G.level))
      (Kbase + F.Hpr * (Dm - 2))) :
    FullRow F (NatM3 hx : _) (ReqE F : _) (ReqP F : _) 2 :=
  row_full F.G.actualFamily (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩)
    (D.Φ F.G.level) (NatHac3 hx) hcb (NatM3 hx : _) _ (F.G.mass F.law)
    {w | (w = fun _ => 1) ∨ w = F.G.marker F.law} Θ (req_ops F T) (D.hΦ F.G.level) hdrift
    ((NatFacts3 hx : _).1)

/-- The constant-trace row of the chosen buffered datum. -/
theorem req_const (F : Request hr D Dm bw j₀) {Kbase : ℕ} {CK : ℕ → ℝ} {Θ : ℝ}
    (T : PreparationNativeTower F (Kbase + F.Hpr * (Dm - 2)) CK Θ)
    (hcb : F.bufferEnd ≤ F.tf) (hx : RouteHx3 F Kbase T hcb) :
    ConstRow F (K := preparationNeutralSlots F.Hpr Dm Kbase)
      (SlotCast (NatB3 hx : _) : _) :=
  const_slot (NatB3 hx : _) ((NatFacts3 hx : _).2.2.2.2.1)

/-- The buffer row of the chosen buffered datum at an old radius. -/
theorem req_buf (F : Request hr D Dm bw j₀) {Kbase : ℕ} {CK : ℕ → ℝ} {Θ : ℝ}
    (T : PreparationNativeTower F (Kbase + F.Hpr * (Dm - 2)) CK Θ)
    (hcb : F.bufferEnd ≤ F.tf) (hx : RouteHx3 F Kbase T hcb) {ρold : ℝ}
    (h0 : 0 ≤ ρold) (h1 : ρold ≤ rhoStar D F.c₀ F.G.level) :
    BufRow F (K := preparationNeutralSlots F.Hpr Dm Kbase)
      (SlotCast (NatB3 hx : _) : _) ρold
      (Real.sqrt (Buffer.bufferEnergyCost (Kbase + F.Hpr * (Dm - 2)))) :=
  row_buffer (F.G.mass F.law) {w | (w = fun _ => 1) ∨ w = F.G.marker F.law}
    (NatB3 hx : _) ((NatFacts3 hx : _).2.2.2.1) ρold h0 h1

/-- The copied-solution row of the chosen objects. -/
theorem req_solve (F : Request hr D Dm bw j₀) {Kbase : ℕ} {CK : ℕ → ℝ} {Θ : ℝ}
    (T : PreparationNativeTower F (Kbase + F.Hpr * (Dm - 2)) CK Θ)
    (hcb : F.bufferEnd ≤ F.tf) (hx : RouteHx3 F Kbase T hcb) :
    SolveRow F (K := preparationNeutralSlots F.Hpr Dm Kbase) (NatE3 hx : _)
      (ReqE F : _) (SlotCast (NatB3 hx : _) : _) :=
  row_solve F.G.actualFamily (D.Φ F.G.level) (NatB3 hx : _) (NatL3 hx : _)
    (NatE3 hx : _) ((NatFacts3 hx : _).2.2.2.2.2.1)

/-- The priced defect row of the chosen objects. -/
theorem req_defect (F : Request hr D Dm bw j₀) (hD : 2 ≤ Dm) {Kbase : ℕ} {CK : ℕ → ℝ}
    {Θ : ℝ} (T : PreparationNativeTower F (Kbase + F.Hpr * (Dm - 2)) CK Θ)
    (hcb : F.bufferEnd ≤ F.tf) (hx : RouteHx3 F Kbase T hcb)
    (hdrift : Providers.WeakGen.Comparison.TorusDriftData (D.κ F.G.level)
      (rhoStar D F.c₀ F.G.level) F.bufferEnd F.tf (streamVel (D.Φ F.G.level))
      (Kbase + F.Hpr * (Dm - 2)))
    {Sr : ℝ} (hSr : 0 ≤ Sr) (hcopy : CopyCoeffAt F (preparationNeutralSlots F.Hpr Dm Kbase) Sr)
    {Γk : ℝ} {Lpr : ℕ} {qw Cs Sinc : ℝ} (hqw : 0 ≤ qw) (hCs : 0 ≤ Cs) (hSinc0 : 0 ≤ Sinc)
    (hsrc : SourceAt F (preparationNeutralSlots F.Hpr Dm Kbase) T (NatHac3 hx) hcb Γk Lpr
      qw Cs Sinc)
    (Fm : PreparationMomentBudgetParameters) (hm : 1 ≤ F.G.level) (hFL : Lpr = Fm.L)
    (hFH : F.Hpr = Fm.H)
    (hFbuf : Real.sqrt (Buffer.bufferEnergyCost (Kbase + F.Hpr * (Dm - 2))) = Fm.Cbuf)
    (hFsample : preparationPlainSampledConstant F.φ₀ Γk Dm Lpr * Cs ≤ Fm.Csample)
    (hwidth : qw ≤ Fm.Cwid * ocEpsilon Fm.q Fm.Λ F.G.level ^ Fm.σ)
    (hinc : Sinc ≤ Fm.CI * ocEpsilon Fm.q Fm.Λ F.G.level ^ Fm.θ)
    (hraw : Sr ≤ Fm.Cplain * Sinc) :
    DefectRow F (NatHac3 hx) hcb (NatM3 hx : _) (NatE3 hx : _) (ReqE F : _)
      (ReqP F : _) (preparationMomentDefectConstant Fm)
      (ocEpsilon Fm.q Fm.Λ (F.G.level - 1)) (Fm.q * Fm.σ * Fm.L) :=
  row_defect F.G.actualFamily (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩)
    (D.Φ F.G.level) (NatHac3 hx) hcb (NatM3 hx : _) F.Hpr Kbase hD (D.eps F.G.level)
    (D.eps (F.G.level - 1)) (fun _ => ()) hdrift (F.G.mass F.law)
    {w | (w = fun _ => 1) ∨ w = F.G.marker F.law} Θ (req_ops F T) (NatB3 hx : _)
    (NatL3 hx : _) (NatE3 hx : _) (NatFacts3 hx : _) Sr hSr hcopy F.φ₀ Γk Lpr qw Cs
    Sinc hqw hCs hSinc0 hsrc
    (fun i j γ => congrFun (congrFun (congrFun (T.inclusion _ (Or.inl rfl) _) i) j) γ) Fm
    F.G.level hm hFL hFH hFbuf hFsample hwidth hinc hraw

/-- The parent scale of a request in the letters of moment-budget parameters. -/
theorem eps_parent (F : Request hr D Dm bw j₀) (Fm : PreparationMomentBudgetParameters)
    (hFq : Fm.q = D.q) (hFΛ : Fm.Λ = D.Λ) :
    D.eps (F.G.level - 1) = ocEpsilon Fm.q Fm.Λ (F.G.level - 1) := by
  unfold OCData.eps
  rw [hFq, hFΛ]

/-- **The route package of a request from its native objects** (the rows above). -/
theorem request_routePkg_of_native (F : Request hr D Dm bw j₀) (hD : 2 ≤ Dm) {Kbase : ℕ}
    {CK : ℕ → ℝ} {Θ : ℝ} (T : PreparationNativeTower F (Kbase + F.Hpr * (Dm - 2)) CK Θ)
    (hcb : F.bufferEnd ≤ F.tf) (hx : RouteHx3 F Kbase T hcb)
    (hdrift : Providers.WeakGen.Comparison.TorusDriftData (D.κ F.G.level)
      (rhoStar D F.c₀ F.G.level) F.bufferEnd F.tf (streamVel (D.Φ F.G.level))
      (Kbase + F.Hpr * (Dm - 2)))
    {ρold : ℝ} (h0 : 0 ≤ ρold) (h1 : ρold ≤ rhoStar D F.c₀ F.G.level)
    {Sr : ℝ} (hSr : 0 ≤ Sr) (hcopy : CopyCoeffAt F (preparationNeutralSlots F.Hpr Dm Kbase) Sr)
    {Γk : ℝ} {Lpr : ℕ} {qw Cs Sinc : ℝ} (hqw : 0 ≤ qw) (hCs : 0 ≤ Cs) (hSinc0 : 0 ≤ Sinc)
    (hsrc : SourceAt F (preparationNeutralSlots F.Hpr Dm Kbase) T (NatHac3 hx) hcb Γk Lpr
      qw Cs Sinc)
    (Fm : PreparationMomentBudgetParameters) (hm : 1 ≤ F.G.level) (hFq : Fm.q = D.q)
    (hFΛ : Fm.Λ = D.Λ) (hFL : Lpr = Fm.L) (hFH : F.Hpr = Fm.H)
    (hFbuf : Real.sqrt (Buffer.bufferEnergyCost (Kbase + F.Hpr * (Dm - 2))) = Fm.Cbuf)
    (hFsample : preparationPlainSampledConstant F.φ₀ Γk Dm Lpr * Cs ≤ Fm.Csample)
    (hwidth : qw ≤ Fm.Cwid * ocEpsilon Fm.q Fm.Λ F.G.level ^ Fm.σ)
    (hinc : Sinc ≤ Fm.CI * ocEpsilon Fm.q Fm.Λ F.G.level ^ Fm.θ)
    (hraw : Sr ≤ Fm.Cplain * Sinc) :
    Nonempty (RoutePkg F (preparationNeutralSlots F.Hpr Dm Kbase) (7 * |Θ|) 2
      (preparationMomentDefectConstant Fm) (Fm.q * Fm.σ * Fm.L) ρold
      (Real.sqrt (Buffer.bufferEnergyCost (Kbase + F.Hpr * (Dm - 2))))) :=
  routePkg_rows F T (NatHac3 hx) hcb (NatM3 hx : _) (NatE3 hx : _)
    (ReqE F : _) (req_native F T hcb hx) ((NatFacts3 hx : _).2.1)
    ((NatFacts3 hx : _).2.2.2.2.2.2) (ReqP F : _) (req_trace F T hcb hx hdrift)
    (req_kernel F T hcb hx hdrift) (req_full F T hcb hx hdrift)
    (req_defect F hD T hcb hx hdrift hSr hcopy hqw hCs hSinc0 hsrc Fm hm hFL hFH hFbuf
      hFsample hwidth hinc hraw)
    (eps_parent F Fm hFq hFΛ) (SlotCast (NatB3 hx : _) : _) (req_const F T hcb hx)
    (req_buf F T hcb hx h0 h1) (req_solve F T hcb hx)

/-- **The route package of a request** at a native tower of the buffer order, from the scalar
window/drift facts, the copied-coefficient clauses, the plain-frame and sampled-source clauses
and the moment-budget parameters. -/
theorem request_routePkg (F : Request hr D Dm bw j₀) (hD : 2 ≤ Dm) {Kbase : ℕ}
    {CK : ℕ → ℝ} {Θ : ℝ} (T : PreparationNativeTower F (Kbase + F.Hpr * (Dm - 2)) CK Θ)
    (slow : ℝ) (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < slow)
    (hs₁ : slow < (1 - D.α) / 2) (hq : IsAdmissibleQ D.α slow D.q) (hζ : IsFastProfile D.ζ)
    (hΛ : 128 ≤ D.Λ) (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ) (hi : 1 ≤ F.G.level)
    (hc₀ : 0 < F.c₀) (hcap : F.c₀ ≤ Buffer.exists_molecular_uniform_constants.choose)
    (hcb : F.bufferEnd ≤ F.tf) (hκ : 0 < D.κ F.G.level) (hρ : 0 < rhoStar D F.c₀ F.G.level)
    (hdrift : Providers.WeakGen.Comparison.TorusDriftData (D.κ F.G.level)
      (rhoStar D F.c₀ F.G.level) F.bufferEnd F.tf (streamVel (D.Φ F.G.level))
      (Kbase + F.Hpr * (Dm - 2)))
    {ρold : ℝ} (h0 : 0 ≤ ρold) (h1 : ρold ≤ rhoStar D F.c₀ F.G.level)
    {Sr : ℝ} (hSr : 0 ≤ Sr) (hcopy : CopyCoeffAt F (preparationNeutralSlots F.Hpr Dm Kbase) Sr)
    {Γk : ℝ} {Lpr : ℕ} {qw Cs Sinc : ℝ} (hqw : 0 ≤ qw) (hCs : 0 ≤ Cs) (hSinc0 : 0 ≤ Sinc)
    (hsrc : ∀ hac : F.s ≤ F.bufferEnd,
      SourceAt F (preparationNeutralSlots F.Hpr Dm Kbase) T hac hcb Γk Lpr qw Cs Sinc)
    (Fm : PreparationMomentBudgetParameters) (hFq : Fm.q = D.q)
    (hFΛ : Fm.Λ = D.Λ) (hFL : Lpr = Fm.L) (hFH : F.Hpr = Fm.H)
    (hFbuf : Real.sqrt (Buffer.bufferEnergyCost (Kbase + F.Hpr * (Dm - 2))) = Fm.Cbuf)
    (hFsample : preparationPlainSampledConstant F.φ₀ Γk Dm Lpr * Cs ≤ Fm.Csample)
    (hwidth : qw ≤ Fm.Cwid * ocEpsilon Fm.q Fm.Λ F.G.level ^ Fm.σ)
    (hinc : Sinc ≤ Fm.CI * ocEpsilon Fm.q Fm.Λ F.G.level ^ Fm.θ)
    (hraw : Sr ≤ Fm.Cplain * Sinc) :
    Nonempty (RoutePkg F (preparationNeutralSlots F.Hpr Dm Kbase) (7 * |Θ|) 2
      (preparationMomentDefectConstant Fm) (Fm.q * Fm.σ * Fm.L) ρold
      (Real.sqrt (Buffer.bufferEnergyCost (Kbase + F.Hpr * (Dm - 2))))) :=
  request_routePkg_of_native F hD T hcb
    (request_native F hD T slow hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hseq hi hc₀ hcap hcb hκ hρ hdrift
      hcopy)
    hdrift h0 h1 hSr hcopy hqw hCs hSinc0 (hsrc _) Fm hi hFq hFΛ hFL hFH hFbuf hFsample hwidth
    hinc hraw

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
