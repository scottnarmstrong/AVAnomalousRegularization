-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Cascade.CovGAssembly
import AVRegularity.Construction.Residual.Presentation.Cascade.GluedConclusion
import AVRegularity.Construction.Preservation.Assembly.PreparationJointOfInputs
import AVRegularity.EntryTerminal.Ingredients.PrepChart.Chart
import AVRegularity.Construction.Residual.Presentation.Cascade.Part1
import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.SourcesA
import AVRegularity.Construction.Residual.Presentation.Cascade.Budget
import AVRegularity.Construction.Residual.Presentation.Cascade.PointwiseEnvelope
import AVRegularity.CycleComparison.Reconstruction.LiftSource

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The inputs of the bill residual from other parts, at every context** (cascade side of the
bill residual).

The forms in which the final assembly takes the pieces proved in other trees, each at every
context of level `≥ m_*`, at the frame of every lifted field with classical representatives
(under the quiet margin of the preparation endpoint, which the assembly has):

* `CovGCtxAt` (the covariance G form): `CovGForm` at the order `succKc`, the radius `rhoEnh D k_I.c_r m`,
  the bound `C·A_in` (the text of part 0 of the `CovGPartStatement`);
* `FilterDefectCtxAt` (the filter defect): `FilterDefectForm` with the bound `C·succFilterPrice·A_in`;
* `ReconCoarseCtxAt`: `FrameReconCoarseAt` on a nondegenerate window, given `F.macroWeak`,
  at every flux constant and every constant of the lift setting;
* `ReconLettersCtxAt`, `ReconDefectConvCtxAt` and
  `succPrefix_reconCoarse_of_parts`: the coarse reconstruction from its two parts (`frameReconCoarse_of_parts`; the
  order `N_c + 2p ≤ N_aux` is paid by the order floor, `windowOrders_of_succReconFloor`).

For `A_in = 0` the bounds are `0`; `p = 0` and a stage without identities are allowed. -/

/-- **The covariance G form at every context of level `≥ m_*`** (the part 0). -/
def CovGCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl : ℕ) (C : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      CovGForm (c.frame CcT PZ aRep û hlift aZ aY hZ hY).Mn c.G c.m N p (succSchedR r₀ J H)
        (succKc r₀ D₀ H J N p Acl) CcT aZ
        (c.G.mass c.law) c.tp c.tf (rhoEnh c.D kI.cr c.m) (C * c.Ain)

/-- **The filter defect at every context of level `≥ m_*`.** -/
def FilterDefectCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl Lc : ℕ) (C : ℝ) (mStar : ℕ) :
    Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      FilterDefectForm (c.frame CcT PZ aRep û hlift aZ aY hZ hY).P c.seedK c.freshK φ₀
        c.G c.G' c.m p (succKc r₀ D₀ H J N p Acl) (c.D.eps (c.m - 1)) (succEta0 α q s) aZ
        (c.G.mass c.law) c.tp c.tf (rhoEnh c.D kI.cr c.m)
        (C * succFilterPrice c.D c.G c.m kI.cr σ₀ Lc * c.Ain)

/-- **The coarse reconstruction at every context of level `≥ m_*` with `t_p < t_f`**, given the coarse equation of
`P_pZ`, at every flux constant and every constant of the lift setting. -/
def ReconCoarseCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl Lc : ℕ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m → c.tp < c.tf →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      (c.frame CcT PZ aRep û hlift aZ aY hZ hY).macroWeak →
      ∀ (hW : (succKc r₀ D₀ H J N p Acl) + 1 + (N + succSchedD D₀ N p (H + 1)) ≤ Naux - 2 * p)
        (Cfl : ℝ) (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ),
        FrameReconCoarseAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law Acl
          (succKc r₀ D₀ H J N p Acl) 0 hW kI.cr σ₀ Lc
          (succTheta1 α q s σ₀ (succDstar D₀ N p H))
        (succTheta2 α q s σ₀ (succDstar D₀ N p H)) c.Ain Cfl CGl Cwl Ca Sb Cgr

/-- **The reconstruction letters at every context of level `≥ m_*` with `t_p < t_f`.** -/
def ReconLettersCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl : ℕ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m → c.tp < c.tf →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      FrameReconLettersAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law (succKc r₀ D₀ H J N p Acl)

/-- **The reconstruction defect at every context of level `≥ m_*` with `t_p < t_f`**, at every flux constant and
every constant of the lift setting. -/
def ReconDefectConvCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl Lc : ℕ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m → c.tp < c.tf →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      ∀ (hW : (succKc r₀ D₀ H J N p Acl) + 1 + (N + succSchedD D₀ N p (H + 1)) ≤ Naux - 2 * p)
        (hf : succKc r₀ D₀ H J N p Acl +
          (0 + succSchedR r₀ J H + 3) * ((N + succSchedD D₀ N p (H + 1)) + 8 * 1 + 4) ≤
            Naux - 2 * p)
        (Cfl : ℝ) (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ),
        FrameReconDefectConvAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law Acl
          (succKc r₀ D₀ H J N p Acl) 0 hW hf kI.cr σ₀ Lc
          (succTheta1 α q s σ₀ (succDstar D₀ N p H))
        (succTheta2 α q s σ₀ (succDstar D₀ N p H)) c.Ain Cfl CGl Cwl Ca Sb Cgr

/-- **The coarse reconstruction at every context from its two parts**; the constant is the level `m_*`. -/
theorem succPrefix_reconCoarse_of_parts {α s q : ℝ} {ζ : ℝ → ℝ}
    (hL : SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX sZ
          σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconLettersCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Acl x))
    (hD : SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX sZ
          σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconDefectConvCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
          σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Acl Lc x)) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX sZ
          σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconCoarseCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Acl Lc x) := by
  refine (hL.and hD).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  have hf : succKc r₀ D₀ H J N p Acl +
      (0 + succSchedR r₀ J H + 3) * ((N + succSchedD D₀ N p (H + 1)) + 8 * 1 + 4) ≤
        Naux - 2 * p := by
    have h := (windowOrders_of_succReconFloor hfacts.recon).2
    have e : (0 + succSchedR r₀ J H + 3) * ((N + succSchedD D₀ N p (H + 1)) + 8 * 1 + 4) =
        (succSchedR r₀ J H + 3) * (N + succSchedD D₀ N p (H + 1) + 12) := by ring
    rw [e]
    exact h
  refine ⟨max x.1 x.2, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm htt hquietMargin CcT PZ aRep û hlift aZ aY hZ hY hmacro hW Cfl CGl Cwl
    Ca Sb Cgr
  exact frameReconCoarse_of_parts (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law hf hmacro
    (hx.1 c (le_trans (le_max_left _ _) hm) htt hquietMargin CcT PZ aRep û hlift aZ aY hZ hY)
    (hx.2 c (le_trans (le_max_right _ _) hm) htt hquietMargin CcT PZ aRep û hlift aZ aY hZ hY hW hf Cfl
      CGl Cwl Ca Sb Cgr)

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The scale facts of the error energy at every context** (cascade side of the bill
residual).

`succPrefix_stageScale`: in the common prefix form, a level `m_*` such that every context of
level `≥ m_*` has `StageScale c`, the hypothesis of the `errorEnergy`
(`ErrorEnergyStatement' c`): the reserves, the positivity of the scales, `ρ_⋆ ≤ ε_{m−1}`, and
the smallness of the kernel price bound `C_I·ε_{m−1}^{q·min(δ/4, τ_e)} ≤ 1/8`
(`succPrefix_levelFloor`). So the error energy holds at every context of level `≥ m_*`.

A stage without identities is allowed; `C_I ≤ 0` is excluded by the ledger (`C_I ≥ C_e ≥ 1`). -/

/-- **The scale facts of the error energy at every context of level `≥ m_*`.** -/
def StageScaleCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m → StageScale c

/-- **The scale facts of the error energy in the common prefix form**; the constant is the level `m_*`. -/
theorem succPrefix_stageScale (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        StageScaleCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ x) := by
  have h1 := succPrefix_retainedProductionBundle α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
  have h2 := succPrefix_levelFloor α s hα₀ q hq
  refine (h1.and h2).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨⟨-, hpk⟩, hfloor⟩ := hx
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  have hk15 := hfacts.sched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk0 : 0 + N + 2 * p ≤ Naux := by
    have := (le_max_right _ _).trans hk15
    omega
  refine ⟨max (max x.1.2 x.2) 2, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm
  have hm1 : x.1.2 ≤ c.m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : x.2 ≤ c.m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm3 : 2 ≤ c.m := le_trans (le_max_right _ _) hm
  obtain ⟨hgeom, -, -⟩ := hpk hk0 c hm1
  obtain ⟨-, -, -, hj, -, hres, -, -, hρ0, hρε⟩ := hgeom
  have hqD : 1 < c.D.q := c.q_gt hq.1
  have hΛD : 128 ≤ c.D.Λ := c.lambda_ge hfacts.hΛ
  have hΛD1 : 1 ≤ c.D.Λ := le_trans (by norm_num) hΛD
  have hθ : CI * c.D.eps (c.m - 1) ^ (q * min (ocDelta α q / 4) τe) ≤ 1 / 8 := by
    show CI * ocEpsilon c.D.q c.D.Λ (c.m - 1) ^ _ ≤ 1 / 8
    rw [c.hq, c.hΛ]
    exact (hfloor c.m hm2).1
  exact
    { hres0 := hres
      hq := hqD
      hΛ := hΛD
      hi := by rw [c.hlevel]; omega
      hj := hj
      hb := hfacts.hbw
      hε := Construction.Stream.ocEpsilon_pos hΛD1
      hν := by rw [c.kap_eq]; exact c.kappa_pos hΛ1 hζ
      hR := hρ0
      hRε := le_trans hρε (Providers.CascadeInvariants.eps_le_of_le hqD hΛD (Nat.sub_le _ _))
      hD := Construction.Preservation.Buffer.preparation_schedule_order_ge_two D₀ N p H
      hθ := hθ }

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients AVRegularity.EntryTerminal.Route
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The drift and edge coefficients of the window at every context** (cascade side of
the bill residual, the discharge of `frameReconCoeffAt_of_envelope`).

`succPrefix_reconCoeff`: in the common prefix form, a level `m_*` such that at every context of
level `≥ m_*`, at the frame of every lifted field with classical representatives,
`FrameReconCoeffAt F 0`: the hypothesis `hR6b` of `frameReconAt_of_steps`.

Inputs:

* the pointwise molecular envelope of the incoming stage (`seedPointwise`),
  from the supplied pointwise envelope of the seed, the field `hpw` of the context;
* the preparation chart certificate of the actual family on every block
  (`preservation_preparation_chart_certificate`, constants before the stage; the block of a start
  `t_S` is `prepBlock τ'' t_S` with three renewal windows);
* the orders `D_m·r_H + D_m + 2 ≤ N_aux ≤ K_res` from the order floor;
* the radius `ρ_⋆ = rhoStar D k_I.c₀ m` with `0 < ρ_⋆ ≤ ε_m` from the incoming lift geometry.

At the first passage `G` is the seed and the pointwise envelope returns the seed's own
constants; a stage without identities and `t_p = t_f` are allowed. -/

/-- **The coefficient step at every context of level `≥ m_*`.** -/
def CoeffCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      FrameReconCoeffAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) 0

/-- The block of a start `t_S` with three renewal windows contains `[t_S, t_S + 2h]`. -/
theorem billCtx_prepBlock_three {h tS : ℝ} (hh : 0 < h) :
    ((prepBlock h tS : ℝ) - 1 / 2) * h ≤ tS ∧ tS < ((prepBlock h tS : ℝ) + 1 / 2) * h ∧
      tS + 2 * h ≤ ((prepBlock h tS : ℝ) + ((3 : ℕ) : ℝ) - 1 / 2) * h := by
  obtain ⟨h1, h2⟩ := prepBlock_spec (aM := tS) hh
  refine ⟨h1, h2, ?_⟩
  push_cast
  nlinarith

/-- **The coefficient step in the common prefix form**; the constant is the level `m_*`. -/
theorem succPrefix_reconCoeff (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        CoeffCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI
          Cw j₀ CQ Cpr Q T₀ x) := by
  have h1 := seedPointwise α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h2 := succPrefix_retainedProductionBundle α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
  refine (SuccPrefix.and h1 h2).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨hpwAt, -, hpk⟩ := hx
  obtain ⟨Cpad, Cage, Npad, Cchart, -, -, mc, -, hchartAll⟩ :=
    preservation_preparation_chart_certificate α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ Λ hfacts.hΛ
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  have hk15 := hfacts.sched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk0 : 0 + N + 2 * p ≤ Naux := by
    have := (le_max_right _ _).trans hk15
    omega
  have hord : succSchedD D₀ N p (H + 1) * succSchedR r₀ J H + succSchedD D₀ N p (H + 1) + 2 ≤
      Kres := by
    have e : 2 * succSchedD D₀ N p (H + 1) * succSchedR r₀ J H =
        2 * (succSchedD D₀ N p (H + 1) * succSchedR r₀ J H) := Nat.mul_assoc _ _ _
    have h2 := hfacts.recon
    simp only [succReconFloor] at h2
    have h3 := hfacts.hNaux
    omega
  refine ⟨max (max x.1 x.2.2) (max mc 2), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY
  have hm1 : x.1 ≤ c.m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : x.2.2 ≤ c.m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm3 : mc ≤ c.m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hm4 : 2 ≤ c.m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  obtain ⟨hgeom, -, -⟩ := hpk hk0 c hm2
  obtain ⟨-, -, -, hj, -, -, -, -, hρ0, hρε⟩ := hgeom
  obtain ⟨kW, hkW, hKs, hJm, a', ha', hpw⟩ := hpwAt c hm1 c.hpw
  have hqD : 1 < c.D.q := c.q_gt hq.1
  have hΛD : 128 ≤ c.D.Λ := c.lambda_ge hfacts.hΛ
  have hτ'' : 0 < ocTauPP c.D.α c.D.q c.D.Λ c.m :=
    Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛD)
  have hi : 1 ≤ c.G.level := by rw [c.hlevel]; omega
  have hρ0' : 0 < rhoStar c.D kW.c₀ c.m := by rw [hkW]; exact c.hlevel ▸ hρ0
  have hρε' : rhoStar c.D kW.c₀ c.m ≤ ocEpsilon c.D.q c.D.Λ c.m := by
    rw [hkW]
    exact (c.hlevel ▸ hρε : rhoStar c.D kI.c₀ c.m ≤ c.D.eps c.m)
  have hnat : ∀ pc : OddSlot, IsNaturalPiece c.D c.Mnat c.m pc.val (c.G.actualFamily.piece pc) :=
    fun pc => c.hlevel ▸ c.hinv.1.1 pc
  have hchart : ∀ tS : ℝ, IsPreparationChartCertificate c.D.α c.D.q c.D.Λ c.m
      (c.D.Φ (c.m - 1)) (c.D.hΦ (c.m - 1)) tS (tS + 2 * ocTauPP c.D.α c.D.q c.D.Λ c.m) Cpad Cage
      Npad (0 + succSchedD D₀ N p (H + 1) * succSchedR r₀ J H + succSchedD D₀ N p (H + 1) + 2)
      Cchart (prepBlock (ocTauPP c.D.α c.D.q c.D.Λ c.m) tS) 3 c.G.actualFamily := by
    intro tS
    obtain ⟨hb1, hb2, hb3⟩ := billCtx_prepBlock_three (tS := tS) hτ''
    rw [c.hα, c.hq, c.hΛ] at hb1 hb2 hb3 ⊢
    exact hchartAll c.D c.hα c.hq c.hΛ c.Mnat c.m hm4 hm3 (le_trans c.m_le_M c.hMnat) tS _ 3
      (by norm_num) hb1 hb2 hb3 c.G.actualFamily hnat c.hseq _
  have hwait : a' + 2 * ocTauPP c.D.α c.D.q c.D.Λ c.m ≤ c.tf := by
    have e1 := c.hs₀
    have e2 := c.htf
    have hτ : 0 < ocTau α q Λ c.m := Construction.Stream.ocTau_pos hΛ1
    have hτ2 : 0 < ocTauPP α q Λ c.m := Construction.Stream.ocTauPP_pos hΛ1
    rw [c.hα, c.hq, c.hΛ]
    linarith
  have hord1 : 0 + succSchedD D₀ N p (H + 1) * succSchedR r₀ J H ≤ Kres := by omega
  have hord2 : 0 + succSchedD D₀ N p (H + 1) * succSchedR r₀ J H + succSchedD D₀ N p (H + 1) + 2 ≤
      Kres := by omega
  exact frameReconCoeffAt_of_envelope (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law (s := s) 0
    kW a' c.tf (by rw [c.hα]; exact hα₀) (by rw [c.hα]; exact hα₁) hs₀
    (by rw [c.hα]; exact hs₁) (by rw [c.hα, c.hq]; exact hq) (by rw [c.hζ]; exact hζ) hΛD
    (by rw [c.hα, c.hq, c.hΛ, c.hζ]; exact c.hseq) c.hlevel c.m_le_term (c.kappa_pos hΛ1 hζ)
    (c.mass_pos hq.1 hfacts.hΛ) hρ0' hρε'
    (Providers.CascadeInvariants.eps_le_of_le hqD hΛD (Nat.sub_le _ _)) c.hinv.1.2.2.1 hi hj hpw
    (fun v => le_trans (fK_le (c.frame CcT PZ aRep û hlift aZ aY hZ hY) 0 v)
      (le_trans hord1 hKs))
    (le_trans hord2 hJm) Cpad Cage Npad Cchart hchart
    (le_trans ha' (c.tA_le_tp hΛ1)) le_rfl hwait

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.CovComm AVRegularity.CycleComparison.Coarse
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! The commutator calculation at a bill frame, conditional on the full-lift,
covariance-size and coarse-drift ingredients. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The full-lift energy and drift bounds give the exact physical commutator term. -/
theorem commAt_of_energy (F : Frame D hr Dm b j₀) (law : BirthLaw) (kc k : ℕ)
    (hk : k + F.N + 2 * F.p ≤ F.Naux) (hkc : kc + 4 * F.p + 1 ≤ k + F.N)
    {c₀ cr Ck Ain ω a B₀ lam : ℝ}
    {Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)}
    (cl : FullLiftClauses law F.G F.Gr F.m F.p F.Naux F.N F.depth F.sX F.sZ k hk F.η₀ c₀ cr
      F.tp F.tf Ck Ain F.Y Yw)
    (hp : RetainedPair F Yw) (hν : 0 < D.κ (F.m - 1))
    (hρ : 0 < rhoEnh D cr F.m) (hπ : ∀ v, 0 < F.G.mass law v)
    (hCk : 0 ≤ Ck) (hAin : 0 ≤ Ain)
    (hS : CovSizeForm F.Mn D F.m F.tp F.tf (rhoEnh D cr F.m) ω)
    (ha : 0 ≤ a) (hB₀ : 1 ≤ B₀) (hlam : 0 < lam)
    (hu : B₀ * rhoEnh D cr F.m / lam ≤ 1 / 2)
    (hst : a * B₀ * rhoEnh D cr F.m ^ 2 ≤ D.κ (F.m - 1) / 8)
    (hjets : ∀ l : ℕ, 1 ≤ l → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ (F.m - 1)) t)) l x‖ ≤
        a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hsmooth : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (streamVel (D.Φ (F.m - 1)) t))
    (hper : ∀ t, IsZ2Periodic (streamVel (D.Φ (F.m - 1)) t)) :
    CovGTermAt 0 F law cr kc (commPriceConst (kc + 4 * F.p + 2 * F.p) F.p 1 * Ck * Ain) := by
  have hF := gradZ_hasFluxBound F law hk hkc cl hp hν (mul_nonneg hCk hAin) hπ
  have hhyp : CommHyp (streamVel (D.Φ (F.m - 1)))
      (fun t => menuCovPrimitive D F.Mn F.m t) (Set.Icc F.tp F.tf) (kc + 4 * F.p) F.p
      (ω * rhoEnh D cr F.m ^ 2) (driftB a B₀ lam) :=
    { smooth := fun t _ => commCtx_contDiff_nat (hsmooth t) _
      periodic := fun t _ => hper t
      cov := hS.1
      drift := fun t _ l _ x => commDrift_iter_le (hsmooth t) ha (zero_le_one.trans hB₀) hlam
        (fun l hl x => hjets l hl t x) l x }
  have hbc := timeCont_of_arrays streamArrayCont
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (D.hΦ (F.m - 1))).smooth hper
    (Set.Icc F.tp F.tf) (kc + 4 * F.p + 2 * F.p)
  have hreg : ∀ v : CompIn F.G.comps, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((kc + 4 * F.p + 2 * F.p + 1 : ℕ) : WithTop ℕ∞)
        (fun z => F.aZ t z v) ∧ IsZ2Periodic (fun z => F.aZ t z v) := by
    intro v t ht
    have h1 := F.readout v t ht
    exact ⟨h1.2.1.of_le (by exact_mod_cast
      (by omega : kc + 4 * F.p + 2 * F.p + 1 ≤ F.Naux)), h1.2.2.1⟩
  have hflux := covComm_flux commAdjCont commPrice commDual (ι := CompIn F.G.comps)
    (h := fun v => hr v.1.root) (kc + 4 * F.p) F.p measurableSet_Icc
    (D.κ (F.m - 1)) (rhoEnh D cr F.m) (F.G.mass law) hν hρ hπ
    (streamVel (D.Φ (F.m - 1))) (fun t => menuCovPrimitive D F.Mn F.m t)
    ω a B₀ lam (D.κ (F.m - 1)) hS.2.2.2 hbc hhyp hS.2.1 ha hB₀ hlam hu hst hν.le
    (fun v t z => F.aZ t z v) _ hreg hF
  have hprice := commPriceConst_mono (kc + 4 * F.p + 2 * F.p) F.p hS.2.1 hS.2.2.1
  have he : (D.κ (F.m - 1) * commPriceConst (kc + 4 * F.p + 2 * F.p) F.p ω) *
      (Ck * Ain / D.κ (F.m - 1)) =
      commPriceConst (kc + 4 * F.p + 2 * F.p) F.p ω * Ck * Ain := by
    field_simp
  have hb := hasFluxBound_mono_Y hflux (he.le.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprice hCk) hAin))
  exact hb
end

/-! The commutator part of the covariance-G form at every bill context. -/

/-- The order floor pays the full-lift order used for the commutator. -/
theorem commOrders {r₀ D₀ H J N p Acl Lc Naux : ℕ}
    (h : succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux) :
    succKc r₀ D₀ H J N p Acl + 4 * p + 1 + N + 2 * p ≤ Naux := by
  have hk := wKcFloor_le (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl
  have hm := le_max_left (succSchedD D₀ N p (H + 1) + Lc + N + 6 * p + 4)
    ((succSchedR r₀ J H + 3) * (N + succSchedD D₀ N p (H + 1) + 12) + 2 * p)
  change wKcFloor (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0 +
    4 * p + 1 + N + 2 * p ≤ Naux
  simp only [succReconFloor] at h
  omega

/-- Part 2 in the exact prefix consumed by the four-part assembly. -/
theorem covGPart2 (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : CovGPartStatement α s q ζ 2 := by
  obtain ⟨ΛD, B₀, _C₁, hΛD, hB₀, _hC₁, hdr⟩ :=
    CycleComparison.Assembly.coarse_drift_small α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h1 := succPrefix_fullLift α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun r₀ D₀ H J N p _ _ _ _ Acl _ _ _ _ _ _ => succKc r₀ D₀ H J N p Acl + 4 * p + 1)
  have h2 := succPrefix_covSize α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ kI => kI.cr) (fun _ _ hc he => he ▸ hc)
  have h3 : SuccPrefix α s q (X := Unit)
      (fun Λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ΛD ≤ Λ) := by
    refine SuccPrefix.of_scale ⟨ΛD, hΛD, fun _ h => h⟩ ?_
    intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
      σ₀ a σ kI CI Cw j₀ _hfacts h CQ Cpr
    exact ⟨(), h⟩
  refine ((h1.and h2).and h3).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨⟨hfl, hsize⟩, hΛdr⟩ := hx
  have hk := commOrders hfacts.recon
  refine ⟨(commPriceConst (succKc r₀ D₀ H J N p Acl + 4 * p + 2 * p) p 1 * max x.1.1.1 0,
    max (max x.1.1.2 x.1.2) 2), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm _hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  have hmfl : x.1.1.2 ≤ c.m := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hmsize : x.1.2 ≤ c.m := (le_max_right _ _).trans ((le_max_left _ _).trans hm)
  have hm2 : 2 ≤ c.m := (le_max_right _ _).trans hm
  have hAin : 0 ≤ c.Ain := (Real.sqrt_nonneg _).trans c.hf
  have hν := c.kappa_pred_pos (le_trans (by norm_num) hfacts.hΛ) hζ
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hcrEq := (Construction.Preservation.Buffer.invariantAdmissible_molecular_parameters hkI).2.1
  have hcr : 0 < kI.cr := hcrEq ▸ hfacts.hcr
  have hcr1 : kI.cr ≤ 1 := hcrEq ▸ hfacts.hcr_le
  have hτ : 0 < ocTauPP c.D.α c.D.q c.D.Λ c.m :=
    Construction.Stream.ocTauPP_pos (le_trans (by norm_num) (c.lambda_ge hfacts.hΛ))
  have hρ : 0 < rhoEnh c.D kI.cr c.m := mul_pos hcr (Real.sqrt_pos.2 (mul_pos hν hτ))
  obtain ⟨aD, lam, haD, hlam, hsm, hst, -, hjets, hsmooth, -, hper, -⟩ :=
    hdr Λ hΛdr c.D.Φ c.hseq c.M c.D.κ c.hband c.m hm2 c.m_le_M
      (c.D.κ c.m) (c.D.κ (c.m - 1)) rfl rfl
  have hH : ocTauPP c.D.α c.D.q c.D.Λ c.m = ocTauPP α q Λ c.m := by
    rw [c.hα, c.hq, c.hΛ]
  have hsqrt : rhoEnh c.D kI.cr c.m ≤
      Real.sqrt (c.D.κ (c.m - 1) * ocTauPP c.D.α c.D.q c.D.Λ c.m) :=
    mul_le_of_le_one_left (Real.sqrt_nonneg _) hcr1
  have hu : B₀ * rhoEnh c.D kI.cr c.m / lam ≤ 1 / 2 := by
    refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt
      (zero_le_one.trans hB₀)) hlam.le).trans ?_
    rw [hH]
    exact hsm
  have hstrain : aD * B₀ * rhoEnh c.D kI.cr c.m ^ 2 ≤ c.D.κ (c.m - 1) / 8 := by
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le hsqrt 2)
      (mul_nonneg haD (zero_le_one.trans hB₀))).trans ?_
    rw [hH]
    exact hst
  let F := c.frame CcT PZ aRep û hlift aZ aY hZ hY
  have cl := billCtx_fullLiftClauses_mono (le_max_left x.1.1.1 0) hAin (hfl hk c hmfl)
  have hS := hsize c hmsize CcT PZ aRep û hlift aZ aY hZ hY
  have hb := commAt_of_energy F c.law (succKc r₀ D₀ H J N p Acl)
    (succKc r₀ D₀ H J N p Acl + 4 * p + 1) hk (Nat.le_add_right _ _) cl
    (retainedPair_of_isRegSolution F c.hsol) hν hρ (c.mass_pos hq.1 hfacts.hΛ)
    (le_max_right _ _) hAin hS haD hB₀ hlam hu hstrain hjets hsmooth hper
  exact hb

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The comparison clauses at every context from the bounds of the residual** (cascade side
of the bill residual).

`succPrefix_comparison`: in the common prefix form, a level `m_*` such that at every context of
level `≥ m_*`, under the quiet margin of the preparation endpoint, for every lifted field `û` of the
context with classical representatives, `C^{D_m − 1}` and periodic at every time of the window:
if the bounds of the residual hold at its frame with the constant `C`
(`FrameResidualBoundAt … A_in C`), then for every regularized solution `U` of the incoming system
from `s₀` the second clause of `ComparisonClauses` holds at `û` with the bounds

    C'·A_in·𝔅   (residual),      C'·A_in·(𝔅 + ε_{m−1}^Q)   (error),

`C' = CmpConst p C_Q C = 2(3 + 8W₀)·(|C_Q|·(1 + C_fil) + |C|)`, `C_fil = cqp((4p)²) p`.

Steps: the residual half at the frame (`comparisonResidual_at_frame`); the initial error
`(C_Q·ε^Q + C_fil·ω^{p+1}·C_Q)·‖f‖` (`succPrefix_initialError`, the initial error); the error energy
(`errorEnergy` with `succPrefix_stageScale`, the error energy); then the conversion of the constants:
the unmarked norm of `f` is at most the marked one, hence at most `A_in`
(`ordinary_input_from_marked`), and `ω^{p+1} ≤ 𝔅` because the bill contains
`ε^{−qγ}·ω^{p+1}` with `ε^{−qγ} ≥ 1` (`omega_pow_le_succBill`).

The regularity hypothesis is the third clause of the lift step of the fine tail
(`FrameFineLiftAt` at an order `K ≥ D_m − 2`).

For `A_in = 0` one has `f = 0` in the weights and both bounds are `0`. The constants use `|C|`
and `|C_Q|`, so negative values are allowed, and for `C ≤ 0` the residual vanishes. -/

/-! ### The constants -/

/-- `x ≤ k·(a + x + b + c + d) + e + f + g` for `k ≥ 1` and nonnegative letters. -/
theorem term_le_bill {k a x b c d e f g : ℝ} (hk : 1 ≤ k) (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 ≤ g) :
    x ≤ k * (a + x + b + c + d) + e + f + g := by
  have h1 : x ≤ k * x := le_mul_of_one_le_left hx hk
  have h2 : k * x ≤ k * (a + x + b + c + d) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- The constant of the comparison clauses: `2(3 + 8W₀)·(|C_Q|·(1 + C_fil) + |C|)`. -/
def CmpConst (p : ℕ) (CQ C : ℝ) : ℝ :=
  ErrConst * (|CQ| * (1 + cqp (((4 * p : ℕ) : ℝ) ^ 2) p) + |C|)

theorem ErrConst_one_le : 1 ≤ ErrConst := by
  have h := AVRegularity.EntryTerminal.ForcedEnergy.wordCount_nonneg 0
  unfold ErrConst
  linarith

/-- The residual bound in the form of the comparison clauses. -/
theorem resBound_le {K CQ Cfil C B Ain : ℝ} (hK : 1 ≤ K) (hCfil : 0 ≤ Cfil) (hB : 0 ≤ B)
    (hA : 0 ≤ Ain) : C * B * Ain ≤ K * (|CQ| * (1 + Cfil) + |C|) * Ain * B := by
  have hq : 0 ≤ |CQ| * (1 + Cfil) := mul_nonneg (abs_nonneg _) (by linarith)
  have h1 : |C| ≤ K * (|CQ| * (1 + Cfil) + |C|) :=
    le_trans (by linarith) (le_mul_of_one_le_left (add_nonneg hq (abs_nonneg _)) hK)
  calc C * B * Ain ≤ |C| * B * Ain :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hB) hA
    _ ≤ K * (|CQ| * (1 + Cfil) + |C|) * B * Ain :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hB) hA
    _ = K * (|CQ| * (1 + Cfil) + |C|) * Ain * B := by ring

/-- The error bound in the form of the comparison clauses (`w` is `ω^{p+1}`, `e` is `ε^Q`, `nf` the unmarked
norm of the datum). -/
theorem errBound_le {K CQ Cfil C e w B nf Ain : ℝ} (hK : 0 ≤ K) (hCfil : 0 ≤ Cfil)
    (he : 0 ≤ e) (hw : 0 ≤ w) (hwB : w ≤ B) (hnf0 : 0 ≤ nf) (hnf : nf ≤ Ain) :
    K * ((CQ * e + Cfil * w * CQ) * nf + max 0 (C * B * Ain)) ≤
      K * (|CQ| * (1 + Cfil) + |C|) * Ain * (B + e) := by
  have hB : 0 ≤ B := hw.trans hwB
  have hA : 0 ≤ Ain := hnf0.trans hnf
  have hq : 0 ≤ |CQ| := abs_nonneg _
  have hpos : 0 ≤ |CQ| * (1 + Cfil) * (B + e) :=
    mul_nonneg (mul_nonneg hq (by linarith)) (by linarith)
  have h1 : CQ * e + Cfil * w * CQ ≤ |CQ| * (1 + Cfil) * (B + e) := by
    have ha : CQ * e ≤ |CQ| * e := mul_le_mul_of_nonneg_right (le_abs_self _) he
    have hb : Cfil * w * CQ ≤ Cfil * w * |CQ| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg hCfil hw)
    have hc : Cfil * w * |CQ| ≤ Cfil * B * |CQ| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwB hCfil) hq
    have hd : 0 ≤ |CQ| * B := mul_nonneg hq hB
    have he' : 0 ≤ |CQ| * Cfil * e := mul_nonneg (mul_nonneg hq hCfil) he
    calc CQ * e + Cfil * w * CQ ≤ |CQ| * e + Cfil * B * |CQ| := by linarith
      _ ≤ |CQ| * (1 + Cfil) * (B + e) := by linarith
  have h2 : (CQ * e + Cfil * w * CQ) * nf ≤ |CQ| * (1 + Cfil) * (B + e) * Ain :=
    (mul_le_mul_of_nonneg_right h1 hnf0).trans (mul_le_mul_of_nonneg_left hnf hpos)
  have h3 : max 0 (C * B * Ain) ≤ |C| * (B + e) * Ain := by
    have hC : 0 ≤ |C| := abs_nonneg _
    refine max_le (mul_nonneg (mul_nonneg hC (by linarith)) hA) ?_
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right (le_abs_self _) hB).trans
        (mul_le_mul_of_nonneg_left (by linarith) hC)) hA
  calc K * ((CQ * e + Cfil * w * CQ) * nf + max 0 (C * B * Ain))
      ≤ K * (|CQ| * (1 + Cfil) * (B + e) * Ain + |C| * (B + e) * Ain) :=
        mul_le_mul_of_nonneg_left (add_le_add h2 h3) hK
    _ = K * (|CQ| * (1 + Cfil) + |C|) * Ain * (B + e) := by ring

section Bill

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The filter price is below the bill**: `ω^{p+1} ≤ 𝔅`, because the bill contains
`ε^{−qγ}·ω^{p+1}` with `ε^{−qγ} ≥ 1` and its other terms are nonnegative. -/
theorem omega_pow_le_succBill (G : GenStage D hr Dm b j₀) (m : ℕ)
    (c₀ cr c σ₀ η : ℝ) (p N Lc Lf Acl J H : ℕ) (tp tf θ₁ θ₂ : ℝ)
    (hE : 0 < D.eps (m - 1)) (hE1 : D.eps (m - 1) ≤ 1) (he : 0 ≤ D.eps m) (hc₀ : 0 ≤ c₀)
    (hcr : 0 ≤ cr) (hγ : 0 ≤ D.q * ocGamma D.α D.q) :
    ((⨆ t : Set.Icc tp tf, ∑ a : Fin 2, ∑ a' : Fin 2, |covPrimitive D m t a a'|) /
        rhoEnh D cr m ^ 2) ^ (p + 1) ≤
      succBill D G m c₀ cr c σ₀ η p N Lc Lf Acl J H tp tf θ₁ θ₂ := by
  have hρ : 0 ≤ rhoEnh D cr m := mul_nonneg hcr (Real.sqrt_nonneg _)
  have hρs : 0 ≤ rhoStar D c₀ m := mul_nonneg hc₀ (le_min he (Real.sqrt_nonneg _))
  have hω : 0 ≤ (⨆ t : Set.Icc tp tf, ∑ a : Fin 2, ∑ a' : Fin 2,
      |covPrimitive D m t a a'|) / rhoEnh D cr m ^ 2 :=
    div_nonneg (Real.iSup_nonneg fun _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _) (sq_nonneg _)
  have hεc : 0 ≤ ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / rhoEnh D cr m :=
    div_nonneg (mul_nonneg he (Real.sqrt_nonneg _)) hρ
  have hεo : 0 ≤ max (D.eps (m - 1) ^ σ₀)
      (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
        (G.fam.identity v u γ).record.width / rhoEnh D cr m) :=
    (Real.rpow_nonneg hE.le _).trans (le_max_left _ _)
  have hεf : 0 ≤ (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
      (G.fam.identity v u γ).record.width / rhoStar D c₀ m) :=
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
      div_nonneg (ConstituentRecord.width_pos _).le hρs
  have hZcl : 0 ≤ Real.sqrt (tf - tp) / Real.sqrt (D.cellScaleSq m) *
      (D.eps m / rhoEnh D cr m) ^ Acl :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (pow_nonneg (div_nonneg he hρ) _)
  unfold succBill
  dsimp only
  exact term_le_bill
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hE hE1 (neg_nonpos.mpr hγ))
    (pow_nonneg hω _) (pow_nonneg hω _) (pow_nonneg hεo _) (Real.rpow_nonneg hE.le _)
    (Real.rpow_nonneg hE.le _) (mul_nonneg (pow_nonneg hεc _) (by linarith))
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.exp_pos _).le)
    (pow_nonneg hεf _)

end Bill

/-! ### The comparison clauses at every context -/

/-- **The comparison clauses at every context of level `≥ m_*`**, under the quiet margin of the preparation endpoint: the
second clause of `ComparisonClauses` at every lifted field with classical representatives which
is `C^{D_m − 1}` and periodic on the window, from the bounds of the residual at its frame. -/
def ComparisonCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Lc Lf Acl : ℕ) (mStar : ℕ) :
    Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      (∀ v, ∀ t ∈ Set.Icc c.tp c.tf,
        ContDiff ℝ ((succSchedD D₀ N p (H + 1) - 1 : ℕ) : ℕ∞)
            (fun x => (c.frame CcT PZ aRep û hlift aZ aY hZ hY).uh t x v) ∧
          IsZ2Periodic (fun x => (c.frame CcT PZ aRep û hlift aZ aY hZ hY).uh t x v)) →
    ∀ cg C : ℝ,
      FrameResidualBoundAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law kI.c₀ kI.cr cg σ₀ Lc
        Lf Acl (succTheta1 α q s σ₀ (succDstar D₀ N p H))
        (succTheta2 α q s σ₀ (succDstar D₀ N p H)) c.Ain C →
    ∀ (U : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (Uw : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root))
      (Uk : ∀ v u (_ : c.G.fam.Γ v u), ℝ →
        TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        φ₀ hφ₀ (c.D.κ c.m) (streamVel (c.D.Φ c.m)) 0 c.s₀ c.tf c.f (fun _ _ => 0) (fun _ _ => 0)
        U Uw Uk →
      ∃ (ŵ : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root))
        (ŷ : ∀ v u (_ : c.G.fam.Γ v u), ℝ →
          TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root))
        (Rres : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
        (qres : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)),
        c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
            φ₀ hφ₀ (c.D.κ c.m) (streamVel (c.D.Φ c.m)) 0 c.tp c.tf (fun v => û v c.tp) Rres qres
            û ŵ ŷ ∧
          residualNorm (c.D.κ c.m) (c.G.mass c.law) (Set.Icc c.tp c.tf)
              (fun t x k v => ((Rres v t).toFunction.jet (valueIndex2 0) x) k)
              (fun t x v => (qres v t).toFunction.jet (valueIndex2 0) x) ≤
            ENNReal.ofReal (CmpConst p CQ C * c.Ain *
              succBill c.D c.G c.m kI.c₀ kI.cr cg σ₀ (succEta0 α q s) p N Lc Lf Acl J H c.tp c.tf
                (succTheta1 α q s σ₀ (succDstar D₀ N p H))
                (succTheta2 α q s σ₀ (succDstar D₀ N p H))) ∧
          obsErrorNorm (c.D.κ c.m) (c.G.mass c.law) (fun _ => 0) c.tp c.tf
              (fun v t => U v t - û v t) (fun v t => Uw v t - ŵ v t) ≤
            ENNReal.ofReal (CmpConst p CQ C * c.Ain *
              (succBill c.D c.G c.m kI.c₀ kI.cr cg σ₀ (succEta0 α q s) p N Lc Lf Acl J H c.tp
                  c.tf (succTheta1 α q s σ₀ (succDstar D₀ N p H))
                  (succTheta2 α q s σ₀ (succDstar D₀ N p H)) + c.D.eps (c.m - 1) ^ Q))

/-- **The comparison clauses in the common prefix form**; the constant is the level `m_*`. -/
theorem succPrefix_comparison (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ComparisonCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ Lc Lf Acl x) := by
  have h1 := succPrefix_stageScale α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h2 := succPrefix_initialError α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine (h1.and h2).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨hss, hie⟩ := hx
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  have hc₀ : 0 ≤ kI.c₀ := by rw [hkI.1]; exact hfacts.hc₀.le
  have hcr : 0 ≤ kI.cr := by rw [hkI.2.1]; exact hfacts.hcr.le
  have hγ : 0 ≤ q * ocGamma α q :=
    mul_nonneg (le_trans zero_le_one hq.1.le) (ocGamma_pos_of_admissible hα₀ hq).le
  have hη : 0 < succEta0 α q s := succEta0_pos_of_admissible hα₀ hs₀ hq
  have hCfil : 0 ≤ cqp (((4 * p : ℕ) : ℝ) ^ 2) p := cqp_nonneg' (sq_nonneg _) p
  refine ⟨max x.1 x.2, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hquietMargin CcT PZ aRep û hlift aZ aY hZ hY hreg cg C hres U Uw Uk hU
  have hm1 : x.1 ≤ c.m := le_trans (le_max_left _ _) hm
  have hm2 : x.2 ≤ c.m := le_trans (le_max_right _ _) hm
  have hqD : 1 < c.D.q := c.q_gt hq.1
  have hΛD : 128 ≤ c.D.Λ := c.lambda_ge hfacts.hΛ
  -- the residual half at the frame
  obtain ⟨ŵ, ŷ, Rres, qres, hsol, hRm, hqm, hrb⟩ :=
    comparisonResidual_at_frame (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law
      (Construction.Preservation.Buffer.preparation_schedule_order_ge_two D₀ N p H) hφ₀
      hfacts.smooth hfacts.support c.Mnat kI c.tA c.tf _ _ c.hinv c.hlevel c.kap_eq
      (c.tA_le_tp hΛ1) le_rfl c.tp_le_tf hreg hres
  -- the initial error and the error energy
  have hE₀ := hie c hm2 hquietMargin U Uw Uk hU CcT PZ aRep û hlift
  have herr := errorEnergy c (hss c hm1) U Uw Uk hU û ŵ ŷ Rres qres hsol hRm hqm _ _ hrb hE₀
  -- the scales of the bill
  have heps := Scales.epsilon_basic (m := c.m - 1) hqD hΛD
  have hE : 0 < c.D.eps (c.m - 1) := heps.1
  have hE1 : c.D.eps (c.m - 1) ≤ 1 := heps.2.1
  have he : 0 ≤ c.D.eps c.m := (Scales.epsilon_basic (m := c.m) hqD hΛD).1.le
  have hγD : 0 ≤ c.D.q * ocGamma c.D.α c.D.q := by rw [c.hα, c.hq]; exact hγ
  have hωB := omega_pow_le_succBill c.G c.m kI.c₀ kI.cr cg σ₀ (succEta0 α q s) p N Lc Lf Acl
    J H c.tp c.tf (succTheta1 α q s σ₀ (succDstar D₀ N p H))
    (succTheta2 α q s σ₀ (succDstar D₀ N p H)) hE hE1 he hc₀ hcr hγD
  have hω0 : 0 ≤ ((⨆ t : Set.Icc c.tp c.tf, ∑ a : Fin 2, ∑ a' : Fin 2,
      |covPrimitive c.D c.m t a a'|) / rhoEnh c.D kI.cr c.m ^ 2) ^ (p + 1) :=
    pow_nonneg (div_nonneg (Real.iSup_nonneg fun t => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _) (sq_nonneg _)) _
  -- the datum
  have hι : 0 ≤ c.law.iota := by rw [c.hlaw.2.2.1]; linarith
  have hnf : weightedNorm 1 (c.G.mass c.law) (fun _ => 1) c.f ≤ c.Ain :=
    Construction.Preservation.FullLift.ordinary_input_from_marked c.G hqD hΛD c.law hι 1 c.f c.hf
  have hnf0 : 0 ≤ weightedNorm 1 (c.G.mass c.law) (fun _ => 1) c.f := Real.sqrt_nonneg _
  have hA : 0 ≤ c.Ain := hnf0.trans hnf
  refine ⟨ŵ, ŷ, Rres, qres, hsol, hrb.trans (ENNReal.ofReal_le_ofReal ?_),
    herr.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · exact resBound_le ErrConst_one_le hCfil (hω0.trans hωB) hA
  · exact errBound_le (le_trans zero_le_one ErrConst_one_le) hCfil
      (Real.rpow_nonneg hE.le _) hω0 hωB hnf0 hnf

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Frontier
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The frontier inner flux at every context: the order facts and the smoothness of the readout** (cascade side of
the bill residual).

* `orders`: above the order order floor, `k_c + 2p + D_{H+1} ≤ N_aux` for the coarse order
  `k_c = succKc` (so the order of the readout, its regularizer lift and the order of the classical
  representative of the retained solution, all `≤ N_aux`), and `D_{H+1} ≤ k_c`.
* `Kres_le_Ks`: an admissible invariant has `K_res ≤ k_I.K_s`.
* `BillCtx.smooth'`: the readout of the omitted flux at the frame of a lifted field is
  `C^{k_c+2p}` and periodic at every time of the window (`frontierSmooth`), from the native
  inputs of the frame (the outgoing certificate and reserves, naturality, shift invariance), slot
  transversality of `G'` and the classical representative of the retained solution.

The statements are arithmetic and hold in particular for `p = 0`. -/

/-- **The orders of the readout fit under the order floor.** -/
theorem orders {r₀ D₀ H J N p Acl Lc Naux : ℕ}
    (h : succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux) :
    succKc r₀ D₀ H J N p Acl + 2 * p + succSchedD D₀ N p (H + 1) ≤ Naux ∧
      succSchedD D₀ N p (H + 1) ≤ succKc r₀ D₀ H J N p Acl := by
  have h1 := wKcFloor_le (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl
  have h2 := le_max_left (succSchedD D₀ N p (H + 1) + Lc + N + 6 * p + 4)
    ((succSchedR r₀ J H + 3) * (N + succSchedD D₀ N p (H + 1) + 12) + 2 * p)
  have h3 := le_wKcFloor (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0
  simp only [succReconFloor] at h
  refine ⟨?_, h3⟩
  show wKcFloor (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0 + 2 * p +
    succSchedD D₀ N p (H + 1) ≤ Naux
  omega

/-- **An admissible invariant has `K_res ≤ k_I.K_s`.** -/
theorem Kres_le_Ks {kS thr kI : InvConsts} {H J N p nk Kres Lpr Lc Lf : ℕ}
    {σ₀ δ q c : ℝ}
    (h : IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ δ q c) : Kres ≤ kI.Ks := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h
  exact h

namespace BillCtx

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀
    CQ Cpr Q T₀ hr)

/-- **The frontier inner flux.3 at a context**: the readout of the omitted flux at the frame of a lifted field is
`C^{k_c + 2p}` and `ℤ²`-periodic at every time of the window. -/
theorem smooth' {Acl : ℕ}
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
    (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
      (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
    (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
      (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
      (fun x => aZ t x v) Naux)
    (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux)
    (hi : NativeInput (c.frame CcT PZ aRep û hlift aZ aY hZ hY))
    (hST : c.G'.IsSlotTransverse) (hΛ : 1 ≤ Λ) (hbw : 0 < bw) (hjm : j₀ + 2 ≤ c.m)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (hord : succKc r₀ D₀ H J N p Acl + 2 * p + succSchedD D₀ N p (H + 1) ≤ Naux) :
    ∀ v, ∀ t ∈ Set.Icc c.tp c.tf,
      ContDiff ℝ ((succKc r₀ D₀ H J N p Acl + 2 * p : ℕ) : ℕ∞)
          (fun y => frontierReadout (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
            c.seedK c.freshK φ₀ c.G c.G' (c.G'.retained c.m H J) c.m H J (c.D.eps (c.m - 1))
            (succEta0 α q s) aY v t y) ∧
        IsZ2Periodic
          (fun y => frontierReadout (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
            c.seedK c.freshK φ₀ c.G c.G' (c.G'.retained c.m H J) c.m H J (c.D.eps (c.m - 1))
            (succEta0 α q s) aY v t y) := by
  obtain ⟨k0, hcert, hres⟩ := hi.outgoing_context
  have hl' : c.G'.level = c.m - 1 := by
    have := c.hactual.2.1
    rw [c.hlevel] at this
    exact this
  have h1 : 1 ≤ c.G'.level := by omega
  have h2 : j₀ ≤ c.G'.level := by omega
  have hε : 0 < c.D.eps (c.G'.level - 1) := by
    unfold OCData.eps
    exact Construction.Stream.ocEpsilon_pos (by rw [c.hΛ]; exact hΛ)
  have hkY : ∀ t ∈ Set.Icc c.tp c.tf, ∀ u : CompIn (c.G'.retained c.m H J).comps,
      ContDiff ℝ ((succKc r₀ D₀ H J N p Acl + 2 * p + succSchedD D₀ N p (H + 1) : ℕ) : ℕ∞)
        (fun y => aY t y u) ∧ IsZ2Periodic (fun y => aY t y u) := by
    intro t ht u
    have h := hY u t ht
    exact ⟨h.2.1.of_le (by exact_mod_cast hord), h.2.2.1⟩
  exact frontierSmooth (c.frame CcT PZ aRep û hlift aZ aY hZ hY)
    (succKc r₀ D₀ H J N p Acl) hcert hST hi.actual.2.2.2.1 (nativeUpsilon_shift hi)
    h1 h2 hbw hε hres hφs hsupp hkY

/-- **The frontier inner flux at a context**: `FrontierInnerForm` at the frame of a lifted field at the coarse order
`k_c = succKc`, with the bound `C³ |C_pr| (E^{ιΣ_H} + E^{θ₁+Jθ₂}) A_in`, from the frontier
production at both grades (constant `C`), the regularizer clause of the kernels of `G'` at the
order `k_c + 2p`, the native inputs of the frame, slot transversality and the orders of the
schedule. -/
theorem form {Acl Kres : ℕ} [∀ r, Nontrivial (hr r)] {Creg : ℕ → ℝ} {C : ℝ} {mStar : ℕ}
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
    (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
      (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
    (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
      (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
      (fun x => aZ t x v) Naux)
    (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux)
    (hi : NativeInput (c.frame CcT PZ aRep û hlift aZ aY hZ hY))
    (hST : c.G'.IsSlotTransverse)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hq1 : 1 < q) (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ)
    (hbw : 0 < bw) (hjm : j₀ + 2 ≤ c.m)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφc : HasCompactSupport φ₀)
    (hsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (hord : succKc r₀ D₀ H J N p Acl + 2 * p + succSchedD D₀ N p (H + 1) ≤ Naux)
    (hDk : succSchedD D₀ N p (H + 1) ≤ succKc r₀ D₀ H J N p Acl)
    (hD2 : 2 ≤ succSchedD D₀ N p (H + 1)) (hNK : Naux ≤ Kres)
    (hS : RegClause c.G' (c.G'.retained c.m H J)
      (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀ hφ₀
      (succKc r₀ D₀ H J N p Acl + 2 * p) c.tp c.tf Creg)
    (hC : 0 ≤ C) (hm : mStar ≤ c.m)
    (hT : FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
      Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar true)
    (hF : FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
      Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar false) :
    FrontierInnerForm (c.frame CcT PZ aRep û hlift aZ aY hZ hY).P c.seedK c.freshK φ₀ c.G c.G'
      (c.G'.retained c.m H J) c.m p H J (succKc r₀ D₀ H J N p Acl) (c.D.eps (c.m - 1))
      (succEta0 α q s) aY (c.G.mass c.law) c.tp c.tf (rhoEnh c.D kI.cr c.m)
      (C ^ 3 * |Cpr| * succFrontPrice c.D c.m (succEta0 α q s) J H
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)) *
        c.Ain) := by
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hΛ
  have hk1 : succKc r₀ D₀ H J N p Acl + 2 * p + 1 ≤ Naux := by omega
  have hk : succKc r₀ D₀ H J N p Acl + 2 * p ≤ Kres := by omega
  obtain ⟨Y0k, Yk, Ywk, Ykk, yom, hsol', htr', hnorm, hcl, hv⟩ := retainedData
    (G := c.G) (G' := c.G') (R := c.G'.retained c.m H J) c.law
    (c.retained_mass_pos hq1 hΛ) (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
    c.seedK c.freshK φ₀ hφ₀ (c.D.κ (c.m - 1)) (streamVel (c.D.Φ (c.m - 1))) c.m p c.tp c.tf
    (c.Preg c.f) Naux (succKc r₀ D₀ H J N p Acl + 2 * p) hk1 c.Y0 c.Y c.Yw c.Yk c.hsol c.htrace
    aY hY
    (fun t _ => (streamVel_facts α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ c.D.Φ c.hseq
      (c.m - 1) t).1)
    (fun t _ => (streamVel_facts α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ c.D.Φ c.hseq
      (c.m - 1) t).2) hD2 Creg hS (rhoEnh c.D kI.cr c.m) (Cpr * c.Ain) c.trace_norm
  have hyom : ∀ v u (γ : c.G'.fam.Γ v u) (hu : IsRetained c.m H J u.1),
      ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp c.tf)),
        (yom v u γ t).val (valueIndex2 (succKc r₀ D₀ H J N p Acl + 2 * p +
            succSchedD D₀ N p (H + 1) - 1)) =
          c.G'.sysS (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀
            hφ₀ v u γ t ((Ywk ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t).val
              (valueIndex2 (succKc r₀ D₀ H J N p Acl + 2 * p + 1))) := by
    intro v u γ hu
    exact ae_restrict_of_forall_mem measurableSet_Icc fun t ht =>
      hv t ht v u γ (Finset.mem_filter.2 ⟨u.2, hu⟩)
  have hgrade := c.frontierAt hT hm _ hk Y0k Yk Ywk Ykk htr' hsol' yom hyom
  have hlength := c.frontierAt hF hm _ hk Y0k Yk Ywk Ykk htr' hsol' yom hyom
  have hAin : 0 ≤ c.Ain := le_trans (by unfold weightedNorm; exact Real.sqrt_nonneg _) c.hf
  have hbd := frontierInner_bound (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law rfl
    (succKc r₀ D₀ H J N p Acl) kI.cr (succTheta1 α q s σ₀ (succDstar D₀ N p H))
    (succTheta2 α q s σ₀ (succDstar D₀ N p H)) C Cpr c.Ain hC
    (c.kappa_pred_pos hΛ1 hζ)
    (by unfold OCData.eps; exact Construction.Stream.ocEpsilon_pos (by rw [c.hΛ]; exact hΛ1))
    (c.mass_pos hq1 hΛ) c.rows' Y0k Ywk yom hgrade hlength hnorm hφ₀ hφs hφc (by omega) hcl
    (fun t ht v u γ hu => hv t ht v u γ hu)
  refine frontierInnerForm_of (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law
    (succKc r₀ D₀ H J N p Acl) kI.cr _
    (c.smooth' CcT PZ aRep û hlift aZ aY hZ hY hi hST hΛ1 hbw hjm hφs hsupp hord)
    (hasFluxBound_mono_Y hbd ?_)
  have hn : 0 ≤ C ^ 3 * succFrontPrice c.D c.m (succEta0 α q s) J H
      (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)) *
      c.Ain := by
    have hε : 0 < c.D.eps (c.m - 1) := by
      unfold OCData.eps; exact Construction.Stream.ocEpsilon_pos (by rw [c.hΛ]; exact hΛ1)
    have hP : 0 ≤ succFrontPrice c.D c.m (succEta0 α q s) J H
        (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)) :=
      add_nonneg (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg hε.le _)
    exact mul_nonneg (mul_nonneg (pow_nonneg hC 3) hP) hAin
  calc C ^ 3 * Cpr * succFrontPrice c.D c.m (succEta0 α q s) J H
        (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)) *
        c.Ain = (C ^ 3 * succFrontPrice c.D c.m (succEta0 α q s) J H
        (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)) *
        c.Ain) * Cpr := by ring
    _ ≤ (C ^ 3 * succFrontPrice c.D c.m (succEta0 α q s) J H
        (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)) *
        c.Ain) * |Cpr| := mul_le_mul_of_nonneg_left (le_abs_self _) hn
    _ = _ := by ring

end BillCtx

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
