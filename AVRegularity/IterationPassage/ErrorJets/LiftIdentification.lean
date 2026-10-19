-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.IterationPassage.Assembly.IterationCascadeAssemblyProbe
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
public import AVRegularity.IterationPassage.PassageJetClausesOfBounds
import AVRegularity.EntryTerminal.Ingredients.PrepInterp.PrepInterp
import AVRegularity.Construction.Preservation.FullLift.NativeGluedDissipationEnergyPrice
import AVRegularity.Construction.Preservation.Assembly.FullLiftFromInputs
import AVRegularity.Construction.Preservation.Assembly.PreparationJointOfInputs
import AVRegularity.Construction.Preservation.FullLift.NativeLiftedFieldCovarianceEnergy
public import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.IterationPassage.ErrorJets

/-! Lift identification, covariance part: the covariance polynomial `covPolyP` of a `C^{2p}` field
commutes with a continuous linear map (here: the evaluation at one component of a family-valued
field). Only `NormedSpace ℝ` is assumed, since the family-valued fields carry the sup norm. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem liftId_fderiv_clm (Φ : E →L[ℝ] F) {g : Vec 2 → E} (hg : Differentiable ℝ g) (x : Vec 2) :
    fderiv ℝ (fun y => Φ (g y)) x = Φ.comp (fderiv ℝ g x) :=
  (Φ.hasFDerivAt.comp x (hg x).hasFDerivAt).fderiv

theorem liftId_cov_clm (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Φ : E →L[ℝ] F) {f : Vec 2 → E}
    (hf : ContDiff ℝ 2 f) (x : Vec 2) :
    Φ (covOperator Hc f x) = covOperator Hc (fun y => Φ (f y)) x := by
  have hd (j : Fin 2) : Differentiable ℝ (fun y => fderiv ℝ f y (basisVec j)) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero
  have hj (j : Fin 2) : (fun y => fderiv ℝ (fun z => Φ (f z)) y (basisVec j)) =
      fun y => Φ (fderiv ℝ f y (basisVec j)) := by
    funext y
    rw [liftId_fderiv_clm Φ (hf.differentiable (by norm_num)) y]
    rfl
  unfold covOperator
  simp only [map_sum, map_smul, hj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [liftId_fderiv_clm Φ (hd j) x]
  rfl

/-- The `l`-fold covariance operator commutes with a continuous linear map on `C^{2l}` fields. -/
theorem liftId_covIter_clm (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Φ : E →L[ℝ] F) :
    ∀ (l : ℕ) (u : Vec 2 → E), ContDiff ℝ ((2 * l : ℕ) : ℕ∞) u → ∀ x,
      Φ ((covOperator Hc)^[l] u x) = (covOperator Hc)^[l] (fun y => Φ (u y)) x
  | 0, u, _, x => by simp only [Function.iterate_zero_apply]
  | l + 1, u, hu, x => by
    have hlow : ContDiff ℝ ((2 * l : ℕ) : ℕ∞) u :=
      hu.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * (l + 1)))
    have h2 : ContDiff ℝ 2 ((covOperator Hc)^[l] u) := by
      apply AVRegularity.Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc l 2 u
      simpa only [Nat.mul_succ, Nat.add_comm] using hu
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [liftId_cov_clm Hc Φ h2 x]
    congr 1
    funext y
    exact liftId_covIter_clm Hc Φ l u hlow y

/-- `covPolyP` of a `C^{2p}` field commutes with a continuous linear map. -/
theorem liftId_covPolyP_clm (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Φ : E →L[ℝ] F) (p : ℕ)
    (u : Vec 2 → E) (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u) (x : Vec 2) :
    Φ (covPolyP Hc p u x) = covPolyP Hc p (fun y => Φ (u y)) x := by
  unfold covPolyP
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  rw [liftId_covIter_clm Hc Φ l u (hu.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * p))) x]

end AVRegularity.IterationPassage.ErrorJets
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.ErrorJets

/-! **Ingredients of `passage_error_jets`**.

The physical error of one passage in jets is interpolated (`passage_jet_clauses_of_actual_bounds`)
between three bounds on two carriers of order `2J_r = 2(K + 2)` at every time of the window
`W = [t_p, t_f]`: the incoming solution `U` (the molecular buffer, `preparation_buffer`), the lifted
field `TP_p𝖱Y` (the full lift, `successor_full_lift_bound`), and their order-zero difference (the
bill, `successor_bill`). Those producers speak about the **regenerated** retained solution of order
`N_aux` and about **some** lifted field, while `PassageErrorOutput` gives an order-zero retained
solution `Y`, classical representatives `aU`, `aY` and lift coefficients `CcT`. Two facts
bridge the gap:

* `PassageRegenerationStatement` (`PassageRegenerationProp` for a generic family type): an
  order-zero retained solution is the truncation of the order-`N_aux` solution from the same trace
  (trace uniqueness and uniqueness at order zero). Proved in `ErrorJets/Regeneration.lean`.
* `PassageLiftIdentificationStatement` (prefix form, as for the producers): every lifted field of the
  regenerated solution has the value `passageLift CcT (fieldCov (fieldReadout aY))` on the window,
  for every actual lift `CcT` and every classical representative `aY` (uniqueness of the lift
  sequence on the active pulses, `native_liftedField_value_eq_constructed`; the classical
  representative of the covariance image is the classical covariance polynomial of `aY`).

The degenerate cases are included. Empty component families: every family and norm is zero,
both statements are vacuous or trivial. `p = 0`: `covPolyP · 0` is the identity polynomial and
`Naux - 2p = Naux`. `N_aux = 0` is excluded by the schedule but harmless here (the regeneration
is the identity).
A time outside the window: nothing is asserted there. -/

section
section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The homogeneous regularized system of a stage (`GenStage.IsRegSolution` with zero forcing),
stated for a generic family type `hr` as for the producers. The statements here use
`HomRegSol (hr := ScalarH)`: a system elaborated directly at `ScalarH` is definitionally the same
proposition, but its zero forcing is a structurally different term, and unifying the two forms
is expensive. -/
def HomRegSol (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm b j₀) (ν : ℝ) (bv : ℝ → Vec 2 → Vec 2)
    (k : ℕ) (t₀ t₁ : ℝ) (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)) : Prop :=
  G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ f (fun _ _ => 0) (fun _ _ => 0) U W Y

/-- **Regeneration**, for a generic family type. If the order-zero and the order-`N_aux`
retained systems from the trace `Q_p(t_p)h` are well posed (`RetainedSolutionClauses`), then every
order-zero retained solution from that trace is, on the window, the truncation of an
order-`N_aux` solution from the same trace.

The degenerate cases are included: an empty family (all fields are zero); `N_aux = 0` (take the
solution itself). -/
def PassageRegenerationProp (law : BirthLaw) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (G Gr : GenStage D hr Dm b j₀) (m p Naux : ℕ) (cr C Q Ain tp tf : ℝ) {Nh : ℕ}
    (h : ∀ v : CompIn G.comps, TorusHk Nh (hr v.1.root)) : Prop :=
  ∀ (Y00 : ∀ v' : CompIn Gr.comps, TorusHk 0 (hr v'.1.root))
    (YN0 : ∀ v' : CompIn Gr.comps, TorusHk Naux (hr v'.1.root)),
    IsRetainedTrace G Gr m p tp h Y00 →
    RetainedSolutionClauses law P seedK freshK φ₀ hφ₀ Gr m 0 cr C Q Ain tp tf Y00 →
    IsRetainedTrace G Gr m p tp h YN0 →
    RetainedSolutionClauses law P seedK freshK φ₀ hφ₀ Gr m Naux cr C Q Ain tp tf YN0 →
    ∀ (Y0 : ∀ v' : CompIn Gr.comps, TorusHk 0 (hr v'.1.root))
      (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (hr v.1.root))
      (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk 1 (hr v.1.root))
      (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root)),
      IsRetainedTrace G Gr m p tp h Y0 →
      HomRegSol P seedK freshK φ₀ hφ₀ Gr (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) 0 tp tf
        Y0 Y Yw Yk →
    ∃ (YN : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
      (YNw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
      (YNk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (Naux + Dm - 1) (hr u.1.root)),
      HomRegSol P seedK freshK φ₀ hφ₀ Gr (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf
        YN0 YN YNw YNk ∧
      ∀ v, ∀ t ∈ Set.Icc tp tf, truncateTorusHk (Nat.zero_le Naux) (YN v t) = Y v t

end Generic

/-- **Regeneration** at scalar families, for every stage pair and trace. -/
def PassageRegenerationStatement : Prop :=
  ∀ {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (law : BirthLaw) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (G Gr : GenStage D ScalarH Dm b j₀) (m p Naux : ℕ) (cr C Q Ain tp tf : ℝ) {Nh : ℕ}
    (h : ∀ v : CompIn G.comps, TorusHk Nh (ScalarH v.1.root)),
    PassageRegenerationProp law P seedK freshK φ₀ hφ₀ G Gr m p Naux cr C Q Ain tp tf h

/-- Data part of `PassageLiftIdentificationStatement`: for the regenerated retained solution
`Y` (order `N_aux`) of a common preparation, every classical representative `aY` of `Y` on the
window (order `K_r ≥ 2p`), every actual lift `CcT` and every lifted field `û` of `Y` (any order
`k`, any coefficients): the value of `û` is `passageLift CcT (fieldCov (fieldReadout aY))`. -/
def PassageLiftIdentificationDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (ScalarH v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (ScalarH v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (ScalarH v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ →
        TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (ScalarH u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      HomRegSol (hr := ScalarH) (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (G'.retained m H J) (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux
        tp tf Y0 Y Yw Yk →
    ∀ (Kr : ℕ), 2 * p ≤ Kr →
    ∀ (aY : ℝ → Vec 2 → ∀ v : CompIn (G'.retained m H J).comps, ScalarH v.1.root),
      (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) Kr) →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m N (succSchedR r₀ J H) sX sZ CcT →
    ∀ (CcT' : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root) {k : ℕ}
      (û : ∀ v : CompIn G.comps, ℝ → TorusHk k (ScalarH v.1.root)),
      IsLiftedField G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s)
        tp tf Y CcT' PZ aRep û →
    ∀ v, ∀ t ∈ Set.Icc tp tf,
      (û v t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => passageLift D m N (succSchedR r₀ J H) CcT
          (fieldCov D m p (fieldReadout m (D.eps (m - 1)) (succEta0 α q s) aY)) t x v

/-- **Lift identification**, with the quantifier prefix of `successor_full_lift_bound` and
`successor_bill` (lift floors `s_X, s_Z` as premises). The proof: the incoming lift geometry
and the native stage slot lifts (`RetainedProductionBundleStatement`,
`uniform_native_weighted_slot_lifts`), `native_liftedField_value_eq_constructed` for `û`,
`nativeStageLiftFamily_coefficients_unique` for `CcT`, and the identification of the classical
representative of `IsCovImage (covPolyP …) (succReadout … Y)` with `covPolyP` of `fieldReadout aY`
(duality against smooth periodic tests, continuity of both sides). -/
def PassageLiftIdentificationStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ mStar : ℕ,
    PassageLiftIdentificationDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout
      npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar
end

/-! **`passage_error_jets` with its data part named**.

`PassageErrorJetsData` is the data part of `PassageErrorJetsStatement` after its constants
`C, m_*`, and `PassageErrorJetsSplit` is `PassageErrorJetsStatement` with that part named;
`passageErrorJets_of_split` is the identity (definitional unfolding). The assembly proves the split
form, whose intermediate goals are small. -/

/-- The data part of `passage_error_jets`. -/
def PassageErrorJetsData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw : ℝ)
    (K : ℕ) (Q T₀ : ℝ) (r₀ D₀ : ℕ) (τe : ℝ) (H J N p nk Naux Nout npad : ℕ) (σ₀ : ℝ)
    (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr C : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
      s₀ + rhoStar D kI.c₀ m ^ 2 / D.κ m ≤ tp →
      Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆ ocQuietTimes α q Λ ζ m →
      PassageErrorOutput law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G (G'.retained m H J) m p N (succSchedR r₀ J H) sX sZ K (succEta0 α q s) Q C kI.c₀ s₀ tp
        tf Preg

/-- `PassageErrorJetsStatement` with its data part named. -/
def PassageErrorJetsSplit : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc : ℝ), 3 ≤ K → 0 < Pacc →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ → Pacc + q * iterZ α q s K + 4 < Q / 2 →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
    ∀ L : ℕ, IsPassageOrders α q s K Pacc σ₀ L N p nk Naux →
      IsCascadeWidths α q lamE a σ (succDstar D₀ N p H) →
    ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ (C : ℝ) (mStar : ℕ),
    PassageErrorJetsData α s q ζ Λ φ₀ hφ₀ bw K Q T₀ r₀ D₀ τe H J N p nk Naux Nout npad σ₀ sX sZ Ce kS kI
      CI Cw j₀ CQ Cpr C mStar

theorem passageErrorJets_of_split (h : PassageErrorJetsSplit) :
    IterationPassage.Assembly.PassageErrorJetsStatement := h

theorem passageErrorJetsSplit_of_statement
    (h : IterationPassage.Assembly.PassageErrorJetsStatement) : PassageErrorJetsSplit := h

end AVRegularity.IterationPassage.ErrorJets
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.IterationPassage.ErrorJets

/-! **Regeneration of the retained solution** (`PassageRegenerationStatement`).

The order-`N_aux` retained solution exists (`RetainedSolutionClauses`); its truncation to order
zero solves the order-zero system (`native_reg_solution_truncate`) from the truncated trace, which
is the given order-zero trace (`covImage_truncate`, `covImage_unique`; both vanish off the
incoming components); uniqueness at order zero identifies it with the given solution on the
window.

The degenerate cases are included: an empty family (all identities are between empty
functions); `N_aux = 0`. -/

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Two retained traces of the same field at the same order coincide. -/
theorem retainedTrace_unique (G Gr : GenStage D hr Dm b j₀) (m p : ℕ) (tp : ℝ) {Nh k : ℕ}
    (h : ∀ v : CompIn G.comps, TorusHk Nh (hr v.1.root))
    (Y0 Y0' : ∀ v' : CompIn Gr.comps, TorusHk k (hr v'.1.root))
    (h0 : IsRetainedTrace G Gr m p tp h Y0) (h0' : IsRetainedTrace G Gr m p tp h Y0') :
    Y0 = Y0' := by
  funext v'
  by_cases hv : v'.1 ∈ G.comps
  · exact covImage_unique _ _ _ _ (h0.1 v' hv) (h0'.1 v' hv)
  · rw [h0.2 v' hv, h0'.2 v' hv]

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The truncation of a retained trace is a retained trace. -/
theorem retainedTrace_truncate (G Gr : GenStage D hr Dm b j₀) (m p : ℕ) (tp : ℝ) {Nh k l : ℕ}
    (hkl : k ≤ l) (h : ∀ v : CompIn G.comps, TorusHk Nh (hr v.1.root))
    (Y0 : ∀ v' : CompIn Gr.comps, TorusHk l (hr v'.1.root))
    (h0 : IsRetainedTrace G Gr m p tp h Y0) :
    IsRetainedTrace G Gr m p tp h (fun v' => truncateTorusHk hkl (Y0 v')) := by
  refine ⟨fun v' hv => covImage_truncate hkl _ _ _ (h0.1 v' hv), fun v' hv => ?_⟩
  change truncateTorusHk hkl (Y0 v') = 0
  rw [h0.2 v' hv, map_zero]

/-- **Regeneration** for a generic family type. -/
theorem passageRegenerationProp (law : BirthLaw) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (G Gr : GenStage D hr Dm b j₀) (m p Naux : ℕ) (cr C Q Ain tp tf : ℝ) {Nh : ℕ}
    (h : ∀ v : CompIn G.comps, TorusHk Nh (hr v.1.root)) :
    PassageRegenerationProp law P seedK freshK φ₀ hφ₀ G Gr m p Naux cr C Q Ain tp tf h := by
  intro Y00 YN0 htr00 hR0 htrN hRN Y0 Y Yw Yk hY0 hY
  obtain rfl : Y0 = Y00 := retainedTrace_unique G Gr m p tp h _ _ hY0 htr00
  have h0 : (fun v' => truncateTorusHk (Nat.zero_le Naux) (YN0 v')) = Y0 :=
    retainedTrace_unique G Gr m p tp h _ _
      (retainedTrace_truncate G Gr m p tp (Nat.zero_le Naux) h YN0 htrN) htr00
  subst h0
  obtain ⟨YN, YNw, YNk, hYN⟩ := hRN.1
  refine ⟨YN, YNw, YNk, hYN, ?_⟩
  have htrunc := native_reg_solution_truncate P seedK freshK φ₀ hφ₀ Gr (D.κ (m - 1)) tp tf
    (streamVel (D.Φ (m - 1))) 0 Naux (Nat.zero_le _) YN0 YN YNw YNk hYN
  exact fun v t ht => (hR0.2 _ Y _ Yw _ Yk htrunc hY).1 v t ht

end Generic

/-- **Regeneration.** -/
theorem passageRegeneration : PassageRegenerationStatement :=
  fun law P seedK freshK φ₀ hφ₀ G Gr m p Naux cr C Q Ain tp tf _ h =>
    passageRegenerationProp law P seedK freshK φ₀ hφ₀ G Gr m p Naux cr C Q Ain tp tf h

end AVRegularity.IterationPassage.ErrorJets
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.IterationPassage.ErrorJets

/-! Lift identification, representative part: the classical representative `aRep` of the
covariance image `P_p 𝖱 Y` of `IsLiftedField` is `fieldCov (fieldReadout aY)` at every time of the
window, for every classical representative `aY` of `Y`. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A smooth periodic function a.e. equal to the stored value is a classical representative. -/
theorem liftId_isClassicalRep_of_smooth {K r : ℕ} (hKr : r + 2 ≤ K) (W : TorusHk K E)
    (a : Vec 2 → E) (hc : ContDiff ℝ r a) (hp : AVenhance.IsZ2Periodic a)
    (hw : W.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] a) :
    IsClassicalRep W a r := by
  obtain ⟨a', ha'⟩ := hilbert_classicalRep_exists K r hKr W
  have hae : a' =ᵐ[volume.restrict AVenhance.unitCube] a :=
    (classicalRep_value_ae W a' ha').symm.trans hw
  have hEq : a' = a := CycleComparison.Lift.periodicContinuous_eq_of_cell_ae a' a
    ha'.2.1.continuous hc.continuous ha'.2.2.1 hp hae
  exact hEq ▸ ha'

/-- Every component of `fieldReadout aY t` is the classical representative (of order `2p`) of the
corresponding component of `𝖱 Y(t)`. -/
theorem liftId_readout_rep {S S' : Finset Comp} (m p Naux : ℕ) (E₀ η : ℝ) (hN : 2 * p + 2 ≤ Naux)
    (Yt : ∀ c : CompIn S', TorusHk Naux (ScalarH c.1.root)) (Kr : ℕ) (hKr : 2 * p ≤ Kr)
    (a : Vec 2 → ∀ c : CompIn S', ScalarH c.1.root)
    (hs : IsSmoothRep Yt a Kr) (v : CompIn S) :
    IsClassicalRep (succReadout m E₀ η Naux Yt v)
      (fun x => fieldReadout m E₀ η (fun _ => a) 0 x v) (2 * p) := by
  have hrep : ∀ c, IsClassicalRep (Yt c) (fun x => a x c) (2 * p) := fun c =>
    liftId_isClassicalRep_of_smooth (by omega) (Yt c) _
      ((contDiff_pi.mp hs.1 c).of_le (by exact_mod_cast hKr))
      (fun n x => congrFun (hs.2.1 n x) c) (hs.2.2 c)
  have h := readout_classicalRep (hr := ScalarH) (by omega : 2 * p ≤ Naux) m E₀ η Yt
    (fun c x => a x c) hrep v
  have hfun : (fun x => fieldReadout m E₀ η (fun _ => a) 0 x v) = fun x => ∑ c : CompIn S',
      if h : compParent m c.1 = v.1 then
        E₀ ^ (η * (compWord m c.1).length) •
          cast (congrArg ScalarH ((compParent_root m c.1).symm.trans (congrArg Comp.root h)))
            (a x c)
        else 0 := by
    funext x
    simp only [fieldReadout, smul_eq_mul]
    rfl
  rw [hfun]
  exact h


/-- **The classical representative of the lifted covariance image.** -/
theorem liftId_aRep_eq {S S' : Finset Comp} (D : OCData) (m p Naux : ℕ) (η tp tf : ℝ)
    (hN : 2 * p + 2 ≤ Naux) (Y : ∀ v : CompIn S', ℝ → TorusHk Naux (ScalarH v.1.root))
    (Kr : ℕ) (hKr : 2 * p ≤ Kr)
    (aY : ℝ → Vec 2 → ∀ v : CompIn S', ScalarH v.1.root)
    (haY : ∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) Kr)
    (PZ : ∀ v : CompIn S, ℝ → TorusHk (Naux - 2 * p) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root)
    (hsym : ∀ t i j, covPrimitive D m t i j = covPrimitive D m t j i)
    (hPZ : ∀ v, ∀ t ∈ Set.Icc tp tf,
      IsCovImage (covPolyP (covPrimitive D m t) p)
        (succReadout m (D.eps (m - 1)) η Naux (fun v' => Y v' t) v) (PZ v t) ∧
      IsClassicalRep (PZ v t) (fun x => aRep t x v) (Naux - 2 * p)) :
    ∀ t ∈ Set.Icc tp tf, aRep t = fieldCov D m p (fieldReadout m (D.eps (m - 1)) η aY) t := by
  intro t ht
  have hread : ∀ v : CompIn S, IsClassicalRep
      (succReadout m (D.eps (m - 1)) η Naux (fun v' => Y v' t) v)
      (fun x => fieldReadout m (D.eps (m - 1)) η aY t x v) (2 * p) := fun v =>
    liftId_readout_rep m p Naux (D.eps (m - 1)) η hN
      (fun v' => Y v' t) Kr hKr (aY t) (haY t ht) v
  have hkey : ∀ v : CompIn S, covPolyP (covPrimitive D m t) p
      (fun x => fieldReadout m (D.eps (m - 1)) η aY t x v) = fun x => aRep t x v := by
    intro v
    obtain ⟨W, hI, hW⟩ := covPolyP_carrier_exists (covPrimitive D m t) (hsym t) p 0
      (succReadout m (D.eps (m - 1)) η Naux (fun v' => Y v' t) v)
      (fun x => fieldReadout m (D.eps (m - 1)) η aY t x v) (by rw [zero_add]; exact hread v)
    have hI' := covImage_truncate (Nat.zero_le (Naux - 2 * p)) _ _ _ (hPZ v t ht).1
    have hrep' := classicalRep_truncate (Nat.zero_le (Naux - 2 * p)) (le_refl 0) _ _
      (classicalRep_order_mono _ _ (hPZ v t ht).2 (Nat.zero_le _))
    exact classical_covImage_rep_unique _ _ W _ hI hI' _ _ hW hrep'
  have hcd : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (fieldReadout (S := S) m (D.eps (m - 1)) η aY t) := by
    refine contDiff_pi.mpr fun v => ?_
    exact_mod_cast (hread v).2.1
  funext x v
  have h1 := liftId_covPolyP_clm (covPrimitive D m t) (ContinuousLinearMap.proj v) p
    (fieldReadout m (D.eps (m - 1)) η aY t) hcd x
  change aRep t x v = covPolyP (covPrimitive D m t) p
    (fieldReadout m (D.eps (m - 1)) η aY t) x v
  have h2 : covPolyP (covPrimitive D m t) p (fieldReadout m (D.eps (m - 1)) η aY t) x v =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun v : CompIn S => ScalarH v.1.root) v)
        (covPolyP (covPrimitive D m t) p (fieldReadout m (D.eps (m - 1)) η aY t) x) := rfl
  rw [h2, h1]
  exact (congrFun (hkey v) x).symm

end AVRegularity.IterationPassage.ErrorJets
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.ErrorJets

/-! **The datum part of `passage_error_jets` from the producer outputs**.

At a fixed common preparation, the outputs of the buffer (`preparation_buffer`, weight `1`), of the
retained energy (`RetainedSolutionClauses` at the orders `0` and `N_aux`), of the full lift
(`FullLiftClauses` at the order `2(K + 2)`) and of the bill (`ComparisonClauses` with the error
bound `C_bill E^Q A`), with the regeneration and the lift identification, give
`PassageErrorOutput` with the constant `C₁ + paidErrorJetConstant (K + 2) |C_bill| C₁`,
`C₁ = |C_b| + C_k²`. The carriers of `passage_jet_clauses_of_actual_bounds` are the buffer carrier
of `U(t)` and the full lifted field at `t`; their order-zero difference is `U(t) - û(t)` for the
bill's lifted field `û`, by the lift identification applied to both lifted fields.

The degenerate cases are included: an empty family (all norms zero); `A = 0` (then `f = 0` in the
marked norm and every
bound is `0`); negative producer constants (absolute values are taken). -/

/-- Two `TorusHk` states with a.e. equal value representatives are equal. -/
theorem torusHk_eq_of_jet_ae {K : ℕ} {f g : TorusHk K ℝ}
    (h : f.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      g.toFunction.jet (valueIndex2 K)) : f = g := by
  apply TorusHk.ext_value
  apply Lp.ext
  exact (periodicJetRepresentative_ae f.val (valueIndex2 K)).symm.trans
    (h.trans (periodicJetRepresentative_ae g.val (valueIndex2 K)))

/-- A time slice of the observable error norm. -/
theorem obsErrorNorm_slice_le {S : Finset Comp} (ν : ℝ) (π : CompIn S → ℝ) {t₀ t₁ t : ℝ}
    (ht : t ∈ Set.Icc t₀ t₁)
    (e : ∀ v : CompIn S, ℝ → TorusHk 0 (ScalarH v.1.root))
    (ew : ∀ v : CompIn S, ℝ → TorusHk 1 (ScalarH v.1.root)) :
    ENNReal.ofReal (Real.sqrt (massNormSq (E := fun v : CompIn S => ScalarH v.1.root)
        (K := fun _ => 0) 1 π (fun v => (truncateTorusHk (Nat.zero_le _) (e v t)).val))) ≤
      obsErrorNorm ν π (fun _ => 0) t₀ t₁ e ew := by
  unfold obsErrorNorm
  refine le_trans ?_ le_self_add
  exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc t₀ t₁) => ENNReal.ofReal (Real.sqrt
    (massNormSq (E := fun v : CompIn S => ScalarH v.1.root) (K := fun _ => 0) 1 π
      (fun v => (truncateTorusHk (Nat.zero_le _) (e v t)).val)))) t ht

/-- A real bound from an `ENNReal.ofReal` bound, with the absolute value of the constant. -/
theorem le_abs_mul_of_ofReal_le {x C Y : ℝ} (hY : 0 ≤ Y)
    (h : ENNReal.ofReal x ≤ ENNReal.ofReal (C * Y)) : x ≤ |C| * Y := by
  rcases (ENNReal.ofReal_le_ofReal_iff').1 h with h | h
  · exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hY)
  · exact h.trans (mul_nonneg (abs_nonneg C) hY)

/-- The full-lift chain `𝓔 ≤ C_k 𝓔^B ≤ C_k (C_k A)` gives `𝓔 ≤ C_k² A`. -/
theorem ofReal_chain_le {x : ENNReal} {R : ENNReal} {Ck A : ℝ}
    (h1 : x ≤ ENNReal.ofReal Ck * R) (h2 : R ≤ ENNReal.ofReal (Ck * A)) :
    x ≤ ENNReal.ofReal (Ck ^ 2 * A) := by
  refine h1.trans ?_
  rcases le_or_gt 0 Ck with hC | hC
  · calc ENNReal.ofReal Ck * R ≤ ENNReal.ofReal Ck * ENNReal.ofReal (Ck * A) :=
          mul_le_mul_right h2 _
      _ = ENNReal.ofReal (Ck ^ 2 * A) := by
          rw [← ENNReal.ofReal_mul hC]
          ring_nf
  · rw [ENNReal.ofReal_of_nonpos hC.le, zero_mul]
    exact zero_le

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **One passage at one common preparation**: the objects of `PassageErrorOutput` (stage pair,
orders, constants of the window and the preparation `𝐏_reg`), bundled so that every named
predicate below is elaborated once. -/
structure PassagePair (D : OCData) (Dm : ℕ) (b : ℝ) (j₀ : ℕ) where
  law : BirthLaw
  P : ProvParams
  seedK : ℕ → KernelSpec
  freshK : ℕ → KernelSpec
  φ₀ : Vec 2 → ℝ
  hφ₀ : Integrable φ₀
  G : GenStage D ScalarH Dm b j₀
  Gr : GenStage D ScalarH Dm b j₀
  m : ℕ
  p : ℕ
  N : ℕ
  depth : ℕ
  sX : ℕ
  sZ : ℕ
  K : ℕ
  Naux : ℕ
  Kres : ℕ
  Nout : ℕ
  η₀ : ℝ
  Q : ℝ
  c₀ : ℝ
  cr : ℝ
  s₀ : ℝ
  tp : ℝ
  tf : ℝ
  Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
    (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))

namespace PassagePair

variable (X : PassagePair D Dm b j₀)

/-- The incoming order-zero solution from `f` at `s₀`. -/
def IncSol (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn X.G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn X.G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : X.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)) : Prop :=
  HomRegSol (hr := ScalarH) X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.G (D.κ X.m) (streamVel (D.Φ X.m)) 0
    X.s₀ X.tf f U Uw Uk

/-- The retained solution of order `k` from `Y0` at `t_p`. -/
def RetSol (k : ℕ) (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk k (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk k (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk (k + 1) (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (ScalarH u.1.root)) : Prop :=
  HomRegSol (hr := ScalarH) X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.Gr (D.κ (X.m - 1))
    (streamVel (D.Φ (X.m - 1))) k X.tp X.tf Y0 Y Yw Yk

/-- An incoming solution in the form of the statements (elaborated at `ScalarH`). -/
theorem incSol_of_direct (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn X.G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn X.G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : X.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root))
    (h : X.G.IsRegSolution X.P X.seedK X.freshK X.φ₀ X.hφ₀ (D.κ X.m) (streamVel (D.Φ X.m)) 0 X.s₀
      X.tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk) : X.IncSol f U Uw Uk := h

/-- A retained solution in the form of the statements (elaborated at `ScalarH`). -/
theorem retSol_of_direct (k : ℕ) (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk k (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk k (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk (k + 1) (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (ScalarH u.1.root))
    (h : X.Gr.IsRegSolution X.P X.seedK X.freshK X.φ₀ X.hφ₀ (D.κ (X.m - 1))
      (streamVel (D.Φ (X.m - 1))) k X.tp X.tf Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk) :
    X.RetSol k Y0 Y Yw Yk := h

/-- The marked amplitude bound of the datum. -/
def Marked (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ) : Prop :=
  weightedNorm 1 (X.G.mass X.law) (X.G.marker X.law) f ≤ A

/-- The retained trace `Q_p(t_p)𝐏_reg f`. -/
def Trace {k : ℕ} (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root))
    (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk k (ScalarH v'.1.root)) : Prop :=
  IsRetainedTrace X.G X.Gr X.m X.p X.tp (X.Preg f) Y0

/-- A classical representative of the retained solution on the window. -/
def SmoothY {k : ℕ} (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk k (ScalarH v.1.root))
    (aY : ℝ → Vec 2 → ∀ v : CompIn X.Gr.comps, ScalarH v.1.root) (Kr : ℕ) : Prop :=
  ∀ t ∈ Set.Icc X.tp X.tf, IsSmoothRep (fun v => Y v t) (aY t) Kr

/-- The value of a lifted field is the passage lift of `fieldCov (fieldReadout aY)`. -/
def LiftValue (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn X.G.comps) (fun v => ScalarH v.1.root))
    (aY : ℝ → Vec 2 → ∀ v : CompIn X.Gr.comps, ScalarH v.1.root) {k : ℕ}
    (û : ∀ v : CompIn X.G.comps, ℝ → TorusHk k (ScalarH v.1.root)) : Prop :=
  ∀ v, ∀ t ∈ Set.Icc X.tp X.tf,
    (û v t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => passageLift D X.m X.N X.depth CcT
        (fieldCov D X.m X.p (fieldReadout X.m (D.eps (X.m - 1)) X.η₀ aY)) t x v

/-- The buffer at weight `1` and order `2(K + 2)` (`preparation_buffer`). -/
def BufferOut (Cb : ℝ) : Prop :=
  ∀ (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn X.G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn X.G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : X.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
    X.IncSol f U Uw Uk →
    ∀ t ∈ Set.Icc X.tp X.tf,
      ∃ Un : ∀ v : CompIn X.G.comps, TorusHk (2 * (X.K + 2)) (ScalarH v.1.root),
        (∀ v, truncateTorusHk (Nat.zero_le _) (Un v) = U v t) ∧
        weightedNorm (rhoStar D X.c₀ X.m) (X.G.mass X.law) (fun _ => 1) Un ≤
          Cb * weightedNorm 1 (X.G.mass X.law) (fun _ => 1) f

/-- The retained energy at every order `k ≤ K_res` (`prepared_retained_energy_production`). -/
def EnergyOut (Cret : ℝ) : Prop :=
  ∀ (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (Ain : ℝ), X.Marked f Ain →
    ∀ k ≤ X.Kres, ∃ Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk k (ScalarH v'.1.root),
      X.Trace f Y0 ∧
      RetainedSolutionClauses X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.Gr X.m k X.cr Cret X.Q Ain
        X.tp X.tf Y0

/-- The full lift (`successor_full_lift_bound` at `k = 2(K + 2)`, weight `1`): a lifted field of
the regenerated solution with the energy bound `C_k² A`. -/
def LiftOut (Ck : ℝ) : Prop :=
  ∀ (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (Ain : ℝ), X.Marked f Ain →
  ∀ (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk X.Naux (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk X.Naux (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk (X.Naux + 1) (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (X.Naux + Dm - 1) (ScalarH u.1.root)),
    X.Trace f Y0 → X.RetSol X.Naux Y0 Y Yw Yk →
    ∃ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn X.G.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn X.G.comps, ℝ → TorusHk (X.Naux - 2 * X.p) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn X.G.comps, ScalarH v.1.root)
      (û : ∀ v : CompIn X.G.comps, ℝ → TorusHk (2 * (X.K + 2)) (ScalarH v.1.root))
      (ŵ : ∀ v : CompIn X.G.comps, ℝ → TorusHk (2 * (X.K + 2) + 1) (ScalarH v.1.root)),
      IsLiftedField X.G X.Gr X.m X.p X.Naux X.N X.depth X.sX X.sZ X.η₀ X.tp X.tf Y CcT PZ aRep û ∧
      strongEnergy (rhoStar D X.c₀ X.m) (D.κ X.m) (X.G.mass X.law) X.tp X.tf û ŵ ≤
        ENNReal.ofReal (Ck ^ 2 * Ain)

/-- The bill (`successor_bill`): a lifted field of order zero with the observable error bound
`C_bill E^Q A` for every incoming solution. -/
def BillOut (Cbill : ℝ) : Prop :=
  ∀ (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (Ain : ℝ), X.Marked f Ain →
  ∀ (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk X.Naux (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk X.Naux (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk (X.Naux + 1) (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (X.Naux + Dm - 1) (ScalarH u.1.root)),
    X.Trace f Y0 → X.RetSol X.Naux Y0 Y Yw Yk →
  ∀ (U : ∀ v : CompIn X.G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn X.G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : X.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
    X.IncSol f U Uw Uk →
    ∃ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn X.G.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn X.G.comps, ℝ → TorusHk (X.Naux - 2 * X.p) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn X.G.comps, ScalarH v.1.root)
      (û : ∀ v : CompIn X.G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (ŵ : ∀ v : CompIn X.G.comps, ℝ → TorusHk 1 (ScalarH v.1.root)),
      IsLiftedField X.G X.Gr X.m X.p X.Naux X.N X.depth X.sX X.sZ X.η₀ X.tp X.tf Y CcT PZ aRep û ∧
      obsErrorNorm (D.κ X.m) (X.G.mass X.law) (fun _ => 0) X.tp X.tf (fun v t => U v t - û v t)
        (fun v t => Uw v t - ŵ v t) ≤ ENNReal.ofReal (Cbill * D.eps (X.m - 1) ^ X.Q * Ain)

/-- The lift identification (`PassageLiftIdentificationStatement`) at the pair. -/
def LidOut : Prop :=
  ∀ (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (Ain : ℝ), X.Marked f Ain →
  ∀ (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk X.Naux (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk X.Naux (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk (X.Naux + 1) (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (X.Naux + Dm - 1) (ScalarH u.1.root)),
    X.Trace f Y0 → X.RetSol X.Naux Y0 Y Yw Yk →
  ∀ (Kr : ℕ), 2 * X.p ≤ Kr → ∀ (aY : ℝ → Vec 2 → ∀ v : CompIn X.Gr.comps, ScalarH v.1.root),
    X.SmoothY Y aY Kr →
  ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn X.G.comps) (fun v => ScalarH v.1.root)),
    IsPassageLift X.G X.m X.N X.depth X.sX X.sZ CcT →
  ∀ (CcT' : ℤ → ℕ → ℕ → LiftCoeff (CompIn X.G.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn X.G.comps, ℝ → TorusHk (X.Naux - 2 * X.p) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn X.G.comps, ScalarH v.1.root) {k : ℕ}
    (û : ∀ v : CompIn X.G.comps, ℝ → TorusHk k (ScalarH v.1.root)),
    IsLiftedField X.G X.Gr X.m X.p X.Naux X.N X.depth X.sX X.sZ X.η₀ X.tp X.tf Y CcT' PZ aRep û →
    X.LiftValue CcT aY û

/-- The regenerated solution of order `N_aux` with the classical representative of `Y`. -/
theorem regenerated (Cret : ℝ) (hNK : X.Naux ≤ X.Kres) (henergy : X.EnergyOut Cret)
    (hregen : PassageRegenerationStatement)
    (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ) (hfA : X.Marked f A)
    (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk 0 (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root))
    (hY0 : X.Trace f Y0) (hY : X.RetSol 0 Y0 Y Yw Yk)
    (aY : ℝ → Vec 2 → ∀ v : CompIn X.Gr.comps, ScalarH v.1.root) (Kr : ℕ)
    (haY : X.SmoothY Y aY Kr) :
    ∃ (YN0 : ∀ v' : CompIn X.Gr.comps, TorusHk X.Naux (ScalarH v'.1.root))
      (YN : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk X.Naux (ScalarH v.1.root))
      (YNw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk (X.Naux + 1) (ScalarH v.1.root))
      (YNk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (X.Naux + Dm - 1) (ScalarH u.1.root)),
      X.Trace f YN0 ∧ X.RetSol X.Naux YN0 YN YNw YNk ∧ X.SmoothY YN aY Kr := by
  obtain ⟨Y00, htr0, hR0⟩ := henergy f A hfA 0 (Nat.zero_le _)
  obtain ⟨YN0, htrN, hRN⟩ := henergy f A hfA X.Naux hNK
  have hrg := hregen X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.G X.Gr X.m
    X.p X.Naux X.cr Cret X.Q A X.tp X.tf (X.Preg f) Y00 YN0 htr0 hR0 htrN hRN Y0 Y Yw Yk hY0 hY
  obtain ⟨YN, YNw, YNk, hYN, hYNY⟩ := hrg
  refine ⟨YN0, YN, YNw, YNk, htrN, hYN, fun t ht => ?_⟩
  obtain ⟨hc, hper, hae⟩ := haY t ht
  refine ⟨hc, hper, fun v => ?_⟩
  have htr := torus_truncate_value_ae (Nat.zero_le X.Naux) (YN v t)
  rw [hYNY v t ht] at htr
  exact htr.symm.trans (hae v)

/-- The jet clauses from the two carriers at one time. -/
theorem jetClauses (Cb Ck Cbill : ℝ) (hπ : ∀ v, 0 < X.G.mass X.law v)
    (hρ : 0 ≤ rhoStar D X.c₀ X.m) (hE : 0 ≤ D.eps (X.m - 1))
    (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ) (hA : 0 ≤ A)
    (hford : weightedNorm 1 (X.G.mass X.law) (fun _ => 1) f ≤ A)
    (U : ∀ v : CompIn X.G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn X.G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn X.G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn X.G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn X.Gr.comps, ScalarH v.1.root)
    (haU : ∀ t ∈ Set.Icc X.tp X.tf,
      IsSmoothRep (fun v => U v t) (aU t) (X.K + X.N + 2 * X.p + 2))
    (XU : ℝ → ∀ v : CompIn X.G.comps, TorusHk (2 * (X.K + 2)) (ScalarH v.1.root))
    (hXU : ∀ t ∈ Set.Icc X.tp X.tf, (∀ v, truncateTorusHk (Nat.zero_le _) (XU t v) = U v t) ∧
      weightedNorm (rhoStar D X.c₀ X.m) (X.G.mass X.law) (fun _ => 1) (XU t) ≤
        Cb * weightedNorm 1 (X.G.mass X.law) (fun _ => 1) f)
    (û1 : ∀ v : CompIn X.G.comps, ℝ → TorusHk (2 * (X.K + 2)) (ScalarH v.1.root))
    (ŵ1 : ∀ v : CompIn X.G.comps, ℝ → TorusHk (2 * (X.K + 2) + 1) (ScalarH v.1.root))
    (hSE : strongEnergy (rhoStar D X.c₀ X.m) (D.κ X.m) (X.G.mass X.law) X.tp X.tf û1 ŵ1 ≤
      ENNReal.ofReal (Ck ^ 2 * A))
    (hv1 : X.LiftValue CcT aY û1)
    (û2 : ∀ v : CompIn X.G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (ŵ2 : ∀ v : CompIn X.G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (herr : obsErrorNorm (D.κ X.m) (X.G.mass X.law) (fun _ => 0) X.tp X.tf
      (fun v t => U v t - û2 v t) (fun v t => Uw v t - ŵ2 v t) ≤
        ENNReal.ofReal (Cbill * D.eps (X.m - 1) ^ X.Q * A))
    (hv2 : X.LiftValue CcT aY û2) :
    PassageJetClauses X.law X.G X.Gr X.m X.p X.N X.depth X.K X.η₀ X.Q
      ((|Cb| + Ck ^ 2) + paidErrorJetConstant (X.K + 2) |Cbill| (|Cb| + Ck ^ 2)) X.c₀ A X.tp X.tf
      CcT aU aY := by
  apply IterationPassage.passage_jet_clauses_of_actual_bounds X.law X.G X.Gr X.m X.p X.N X.depth
    X.K X.η₀ X.Q X.c₀ A X.tp X.tf |Cbill| (|Cb| + Ck ^ 2) hρ hE hA (abs_nonneg _) (by positivity) hπ
    CcT aU aY XU (fun t v => û1 v t)
  · intro t ht v
    have htr := torus_truncate_value_ae (Nat.zero_le _) (XU t v)
    rw [(hXU t ht).1 v] at htr
    exact htr.symm.trans ((haU t ht).2.2 v)
  · intro t ht v
    exact hv1 v t ht
  · intro t ht
    have hUa : weightedNorm (rhoStar D X.c₀ X.m) (X.G.mass X.law) (fun _ => 1) (XU t) ≤
        |Cb| * A := by
      refine (hXU t ht).2.trans ?_
      calc Cb * weightedNorm 1 (X.G.mass X.law) (fun _ => 1) f
          ≤ |Cb| * weightedNorm 1 (X.G.mass X.law) (fun _ => 1) f :=
            mul_le_mul_of_nonneg_right (le_abs_self Cb) (Real.sqrt_nonneg _)
        _ ≤ |Cb| * A := mul_le_mul_of_nonneg_left hford (abs_nonneg Cb)
    have hHa := EntryTerminal.Ingredients.weightedNorm_le_of_strongEnergy hπ ht
      (mul_nonneg (sq_nonneg Ck) hA) û1 ŵ1 hSE
    calc weightedNorm (rhoStar D X.c₀ X.m) (X.G.mass X.law) (fun _ => 1) (XU t) +
          weightedNorm (rhoStar D X.c₀ X.m) (X.G.mass X.law) (fun _ => 1) (fun v => û1 v t)
        ≤ |Cb| * A + Ck ^ 2 * A := add_le_add hUa hHa
      _ = (|Cb| + Ck ^ 2) * A := by ring
  · intro t ht
    have hdiff : (fun v => truncateTorusHk (Nat.zero_le _) (XU t v - û1 v t)) =
        fun v => truncateTorusHk (Nat.zero_le _) (U v t - û2 v t) := by
      funext v
      apply torusHk_eq_of_jet_ae
      have hXa : (XU t v).toFunction.jet (valueIndex2 (2 * (X.K + 2))) =ᵐ[volume.restrict
          AVenhance.unitCube] fun x => aU t x v := by
        have htr := torus_truncate_value_ae (Nat.zero_le _) (XU t v)
        rw [(hXU t ht).1 v] at htr
        exact htr.symm.trans ((haU t ht).2.2 v)
      have h1 := IterationPassage.actual_error_carrier_value (Nat.zero_le _) (XU t v) (û1 v t)
        _ _ hXa (hv1 v t ht)
      have h2 := torus_truncate_value_ae (Nat.zero_le 0) (U v t - û2 v t)
      have h3 := torus_sub_value_ae (U v t) (û2 v t)
      filter_upwards [h1, h2, h3, (haU t ht).2.2 v, hv2 v t ht] with x h1x h2x h3x hux h2vx
      rw [h1x, h2x, h3x, hux, h2vx]
    have hs := obsErrorNorm_slice_le (D.κ X.m) (X.G.mass X.law) ht (fun v t => U v t - û2 v t)
      (fun v t => Uw v t - ŵ2 v t)
    have hb := le_abs_mul_of_ofReal_le (mul_nonneg (Real.rpow_nonneg hE _) hA)
      (hs.trans (herr.trans_eq (by rw [mul_assoc])))
    rw [hdiff]
    unfold weightedNorm
    simp only [one_pow, div_one]
    calc Real.sqrt (massNormSq (E := fun v : CompIn X.G.comps => ScalarH v.1.root)
          (K := fun _ => 0) 1 (X.G.mass X.law)
          (fun v => (truncateTorusHk (Nat.zero_le _) (U v t - û2 v t)).val))
        ≤ |Cbill| * (D.eps (X.m - 1) ^ X.Q * A) := hb
      _ = |Cbill| * D.eps (X.m - 1) ^ X.Q * A := by ring

/-- **`PassageErrorOutput` from the producer outputs at one common preparation.** -/
theorem errorOutput (Cb Ck Cbill Cret : ℝ) (hNK : X.Naux ≤ X.Kres) (hπ : ∀ v, 0 < X.G.mass X.law v)
    (hρ : 0 ≤ rhoStar D X.c₀ X.m) (hE : 0 ≤ D.eps (X.m - 1))
    (hord : ∀ (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ),
      X.Marked f A → weightedNorm 1 (X.G.mass X.law) (fun _ => 1) f ≤ A)
    (hbuf : X.BufferOut Cb) (henergy : X.EnergyOut Cret) (hlift : X.LiftOut Ck)
    (hbill : X.BillOut Cbill) (hlid : X.LidOut) (hregen : PassageRegenerationStatement) :
    PassageErrorOutput X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.G X.Gr X.m X.p X.N X.depth X.sX
      X.sZ X.K X.η₀ X.Q ((|Cb| + Ck ^ 2) + paidErrorJetConstant (X.K + 2) |Cbill| (|Cb| + Ck ^ 2))
      X.c₀ X.s₀ X.tp X.tf X.Preg := by
  classical
  intro f A hfA U Uw Uk hU Y0 Y Yw Yk hY0 hY CcT hCcT aU aY haU haY
  have hfA' : X.Marked f A := hfA
  have hU' : X.IncSol f U Uw Uk := X.incSol_of_direct f U Uw Uk hU
  have hY' : X.RetSol 0 Y0 Y Yw Yk := X.retSol_of_direct 0 Y0 Y Yw Yk hY
  have hA : 0 ≤ A := (Real.sqrt_nonneg _).trans hfA
  obtain ⟨YN0, YN, YNw, YNk, htrN, hYN, haYN⟩ := X.regenerated Cret hNK henergy hregen f A hfA'
    Y0 Y Yw Yk hY0 hY' aY (X.K + X.N + 2 * X.p + 2) haY
  obtain ⟨CcT1, PZ1, aRep1, û1, ŵ1, hW1, hSE⟩ := hlift f A hfA' YN0 YN YNw YNk htrN hYN
  obtain ⟨CcT2, PZ2, aRep2, û2, ŵ2, hL2, herr⟩ := hbill f A hfA' YN0 YN YNw YNk htrN hYN
    U Uw Uk hU'
  have hv1 := hlid f A hfA' YN0 YN YNw YNk htrN hYN (X.K + X.N + 2 * X.p + 2) (by omega) aY haYN
    CcT hCcT CcT1 PZ1 aRep1 û1 hW1
  have hv2 := hlid f A hfA' YN0 YN YNw YNk htrN hYN (X.K + X.N + 2 * X.p + 2) (by omega) aY haYN
    CcT hCcT CcT2 PZ2 aRep2 û2 hL2
  have hex : ∀ t : ℝ, ∃ Un : ∀ v : CompIn X.G.comps, TorusHk (2 * (X.K + 2)) (ScalarH v.1.root),
      t ∈ Set.Icc X.tp X.tf → (∀ v, truncateTorusHk (Nat.zero_le _) (Un v) = U v t) ∧
        weightedNorm (rhoStar D X.c₀ X.m) (X.G.mass X.law) (fun _ => 1) Un ≤
          Cb * weightedNorm 1 (X.G.mass X.law) (fun _ => 1) f := by
    intro t
    by_cases ht : t ∈ Set.Icc X.tp X.tf
    · obtain ⟨Un, hUn⟩ := hbuf f U Uw Uk hU' t ht
      exact ⟨Un, fun _ => hUn⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose XU hXU using hex
  exact X.jetClauses Cb Ck Cbill hπ hρ hE f A hA (hord f A hfA') U Uw CcT aU aY haU XU
    (fun t ht => hXU t ht) û1 ŵ1 hSE hv1 û2 ŵ2 herr hv2

end PassagePair

end AVRegularity.IterationPassage.ErrorJets
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.IterationPassage.ErrorJets

/-! Lift identification, value part. With the native slot lifts, the value of every lifted field
`û` of `Y` (any order, any actual lift coefficients) is `passageLift CcT (fieldCov (fieldReadout aY))`
for any classical representative `aY` of `Y`.

All statements are at `ScalarH`; the producers' generic-family forms are not involved. -/

/-- `gluedLift` reads its field only at the time `t`, through `c * (c⁻¹ * t) = t`. -/
theorem liftId_gluedLift_congr_time {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ e εc : ℝ) (N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (a b : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2)
    (hc : c ≠ 0) (hab : a t = b t) :
    gluedLift kset ϖ c ρ e εc N H Cc chart label a t x =
      gluedLift kset ϖ c ρ e εc N H Cc chart label b t x := by
  have hct : c * (c⁻¹ * t) = t := mul_inv_cancel_left₀ hc t
  have hl : ∀ k hh n, liftApply n (Cc k hh n)
      (fun s' X' => a (c * s') (chart k (c * s') (ρ • X'))) (c⁻¹ * t) =
      liftApply n (Cc k hh n) (fun s' X' => b (c * s') (chart k (c * s') (ρ • X'))) (c⁻¹ * t) := by
    intro k hh n
    unfold liftApply
    funext X z v
    simp only [hct, hab]
  simp only [gluedLift, pulsePhysicalLift, diagSample, hl]

/-- The value of a lifted field of `Y`, in terms of any classical representative `aY` of `Y`. -/
theorem liftId_value_of_slotLifts {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    {G Gr : GenStage D ScalarH Dm bw j₀} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (m p Naux sX sZ : ℕ) (hlevel : G.level = m)
    (η tp tf : ℝ) (hN : 2 * p + 2 ≤ Naux)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (ScalarH v.1.root))
    (Kr : ℕ) (hKr : 2 * p ≤ Kr)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root)
    (haY : ∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) Kr)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hCcT : IsPassageLift G m N H sX sZ CcT)
    (CcT' : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root) {r : ℕ}
    (û : ∀ v : CompIn G.comps, ℝ → TorusHk r (ScalarH v.1.root))
    (hfield : IsLiftedField G Gr m p Naux N H sX sZ η tp tf Y CcT' PZ aRep û) :
    ∀ v, ∀ t ∈ Set.Icc tp tf,
      (û v t).toFunction.jet (valueIndex2 r) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => passageLift D m N H CcT
          (fieldCov D m p (fieldReadout m (D.eps (m - 1)) η aY)) t x v := by
  classical
  subst hlevel
  intro v t ht
  have hc : 0 < D.cellScaleSq G.level :=
    EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hband G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  have hrep := liftId_aRep_eq D G.level p Naux η tp tf hN Y Kr hKr aY haY PZ aRep
    (fun t i j => native_covPrimitive_entry_symm D hΛ hζ G.level t i j) hfield.2.1 t ht
  apply (native_liftedField_value_eq_constructed slotLifts hΛ hζ hband p Naux sX sZ η tp tf Y
    CcT' PZ aRep û hfield v t ht).trans
  apply Filter.Eventually.of_forall
  intro x
  have hstep : gluedLift (ocObsPulses D.α D.q D.Λ G.level t t)
      (fun j => ocCutoff D.α D.q D.Λ G.level j)
      (D.cellScaleSq G.level) (liftLength D G.level) (D.eps G.level)
      (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) / liftLength D G.level)
      N H (nativeStageLiftFamily slotLifts)
      (fun j s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level j))
      (fun j s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s') aRep t x =
      passageLift D G.level N H CcT aRep t x := by
    apply gluedLift_coeff_congr
    intro j hj hcut hh hhh n _hn m' α X z v' u
    have hjodd : Odd j := (Finset.mem_filter.mp hj).2.1
    have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
    have htcell : (D.cellScaleSq G.level)⁻¹ * t ∈
        Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
          ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) := by
      rw [inv_mul_eq_div]
      exact ⟨div_le_div_of_nonneg_right htw.1 hc.le,
        div_le_div_of_nonneg_right htw.2 hc.le⟩
    exact (nativeStageLiftFamily_coefficients_unique slotLifts sX sZ CcT hCcT
      j hjodd hh hhh n m' α _ htcell X z v' u).symm
  beta_reduce
  rw [congrFun hstep v]
  exact congrFun (liftId_gluedLift_congr_time _ _ _ _ _ _ _ _ CcT _ _ aRep _ t x hc.ne' hrep) v

end AVRegularity.IterationPassage.ErrorJets
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.IterationPassage.ErrorJets

/-! **The passage lift identification**.

The prefix is the one of `successor_full_lift_bound`: the incoming lift geometry comes from the
retained production bundle (`retained_production_bundle_of_certificates`), the native stage slot
lifts from `uniform_native_weighted_slot_lifts`, and the identification of the value of
a lifted field from `liftId_value_of_slotLifts`. The statements here use `HomRegSol` at `ScalarH`;
the conversion to the generic-family form of the producers is the separate lemma
`liftId_regSolution_of_hom`.

The degenerate cases are included: an empty family (the conclusion quantifies over `CompIn ∅`);
`p` with `Kr = 2p`
(only the order-`0` carrier of `P_p` is used); a time outside the window (nothing is asserted). -/

/-- Conversion of the `HomRegSol` form at `ScalarH` to the explicit zero-forcing form. -/
theorem liftId_regSolution_of_hom {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (G : GenStage D ScalarH Dm b j₀) (ν : ℝ) (bv : ℝ → Vec 2 → Vec 2) (k : ℕ) (t₀ t₁ : ℝ)
    (f : ∀ v : CompIn G.comps, TorusHk k (ScalarH v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (ScalarH v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (ScalarH v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (ScalarH u.1.root))
    (h : HomRegSol (hr := ScalarH) P seedK freshK φ₀ hφ₀ G ν bv k t₀ t₁ f U W Y) :
    G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ f (fun _ _ => 0) (fun _ _ => 0) U W Y :=
  h


/-- **Lift identification**: the lifted field of the producers is `passageLift` of
`fieldCov (fieldReadout aY)`. -/
theorem passageLiftIdentification (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : PassageLiftIdentificationStatement α s q ζ := by
  classical
  obtain ⟨Λa, hΛa, hlift⟩ := uniform_native_weighted_slot_lifts hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λ₀, hΛ₀, hbase, hprod⟩ := retained_production_bundle_of_certificates hα₀ hα₁ hs₀ hs₁
    hq hζ (retained_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ) Λa hΛa
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨c₀max, hc₀max, hp⟩ := hprod Λ hΛ
  refine ⟨c₀max, hc₀max, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hp⟩ := hp φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper
    hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hp⟩ := hp kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  have hDm : 2 ≤ succSchedD D₀ N p (H + 1) := by
    change 2 ≤ succSchedD D₀ N p H + 2 * N + 4 * p + 4
    omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hNauxle, _, _, hN2, _, _⟩ := hsched
  have hNa : 2 * p + 2 ≤ Naux := by
    have := (le_max_left _ _).trans hNauxle
    omega
  have hk0 : 0 + N + 2 * p ≤ Naux := by omega
  obtain ⟨CG, Cw', Cj, m₀, hm₀, hpk⟩ := hlift Λ (hbase.trans hΛ) bw hbw
    (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N sX sZ 0 hDm (by omega)
  obtain ⟨Cread, mStar, hCread, hp⟩ := hp CI Cw j₀ hledger hstart 0 hk0 CQ Cpr m₀ m₀ hm₀ hm₀
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
    hseed m hm hn hnM tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual tp Preg hprep
    f Ain hf Y0 Y Yw Yk htrace hsol Kr hKr aY haY CcT hCcT CcT' PZ aRep k û hfield
  have hpD := hp D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    (hr := ScalarH) seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA s₀ htA hdelay hwindow hT
    G G' hcascade hlevel hG hactual tp Preg hprep f Ain hf Y0 Y Yw Yk htrace
    (liftId_regSolution_of_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsol)
  obtain ⟨hgeom, _, _⟩ := hpD
  obtain ⟨hge, _, htermG, hj, hdepth, hreserve, hreserve2, hlength, _, _⟩ := hgeom
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hΛD : 1 ≤ D.Λ := by
    rw [hDΛ]
    omega
  have hζD : IsFastProfile D.ζ := hDζ ▸ hζ
  have hpk' := hpk ScalarH D hDα hDq hDΛ hDζ hseq hbandD j₀ G law _ seedK freshK φ₀ hφ₀
    Mnat kI tA tf _ _ hG hge htermG hj hdepth hreserve hreserve2 hlength (fun _ => 1) (Or.inl rfl)
  have hslotLifts := fun slot => Classical.choice (hpk' slot)
  exact liftId_value_of_slotLifts hslotLifts hΛD hζD hbandD m p Naux sX sZ hlevel (succEta0 α q s)
    tp tf hNa Y Kr hKr aY haY CcT hCcT CcT' PZ aRep û hfield

end AVRegularity.IterationPassage.ErrorJets
end
end
end
