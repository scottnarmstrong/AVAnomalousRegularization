-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.InitialValue.Cascade
public import AVRegularity.Definitions.Construction.ResidualOps
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVRegularity.Construction.StrainPhysical.Context
import AVRegularity.Proofs.Results.Construction.SuccWindowData.Jacobian
import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.Smooth
import AVRegularity.Construction.Uniqueness.SuccessorFluxWindow
import AVRegularity.Proofs.GenSem.LiftOn.Omega
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.CycleReference.SingleModeFlux

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers

/-! Proof of `AVRegularity.lift_sequence_unique`: uniqueness of the lift sequence under the
premises `IsLiftSetting`. The premises give the window data of the cell equation (the metric lies
between `3/4` and `5/4`; the drift is bounded on the window by the `0`-jet of `√η v`), and the
window uniqueness `AVRegularity.Uniqueness.lift_sequence_unique_window` applies. -/

/-- **Uniqueness of the lift sequence** (Proposition 9.6(a) of the paper). -/
theorem lift_sequence_unique {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    {Dm : ℕ} (Q : LiftOperatorData ι h Dm) (π : ι → ℝ) (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ)
    (par : Fin 2) (V : ℝ → ℝ → ℝ) (H N K k L qs qf : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) (bb : ι → ι → ℝ) (Θ : ℝ)
    (hS : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bb Θ)
    (sX sZ : ℕ) (hsX : sX ≤ qs) (hsZ : sZ ≤ qf)
    (Cc Cc' : ℕ → ℕ → LiftCoeff ι h) (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    (hC' : IsLiftSequence Q sX sZ t₀ t₁ N H Cc') :
    ∀ hh ≤ H, ∀ n m (α : DerivativeWord2 m), ∀ t ∈ Set.Icc t₀ t₁, ∀ X z v u,
      Cc hh n m α t X z v u = Cc' hh n m α t X z v u := by
  have _ := hsX
  have _ := hsZ
  have hη : 0 < Q.η := by rw [hS.η_eq]; exact div_pos hS.ν_pos hS.B_pos
  have hsq : 0 < Real.sqrt Q.η := Real.sqrt_pos.mpr hη
  have hbd : ∀ t ∈ Set.Icc t₀ t₁, ∀ z, ‖Q.v t z‖ ≤ max (Cw 0) 0 / Real.sqrt Q.η := by
    intro t ht z
    have h0 := hS.w_jets 0 (Nat.zero_le _)
    have h1 : ‖iteratedFDeriv ℝ 0 (fun z' => Real.sqrt Q.η • Q.v t z') z‖ₑ ≤
        ENNReal.ofReal (Cw 0) :=
      le_trans (le_trans (le_iSup (fun z => ‖iteratedFDeriv ℝ 0
          (fun z' => Real.sqrt Q.η • Q.v t z') z‖ₑ) z)
        (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc t₀ t₁) => ⨆ z : Vec 2,
          ‖iteratedFDeriv ℝ 0 (fun z' => Real.sqrt Q.η • Q.v t z') z‖ₑ) t ht)) h0
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [toReal_enorm, norm_iteratedFDeriv_zero, ENNReal.toReal_ofReal'] at h2
    rw [norm_smul, Real.norm_of_nonneg hsq.le] at h2
    rw [le_div_iff₀ hsq]
    linarith
  refine AVRegularity.Uniqueness.lift_sequence_unique_window Q t₀ t₁ hS.window ?_ sX sZ N H Cc Cc' hC hC'
  intro X
  exact ⟨3 / 4, 5 / 4, max (Cw 0) 0 / Real.sqrt Q.η,
    AVRegularity.Uniqueness.windowData_of_elliptic (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁
      (3 / 4) (5 / 4) _ (fun t => hS.G_symm t X 0 1) (by norm_num)
      (fun t ht ξ => hS.G_ellip t ht X ξ) hbd⟩

end AVRegularity.Providers
end
end

section
/-! Proof of `successor_initial_value`: with the readout `Q_h` of the retained
trace, the dual image identities are the trace relation and the lifted-field relation at `t_p`; the
stage's own components are their own parents with the empty word (cascade invariant), so the
readout of the retained trace is the trace of the component itself. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity

namespace InitialValue

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The readout of a field supported on the own components of a stage. -/
theorem readout_self (G Gr : GenStage D hr Dm b j₀) (m : ℕ) (E η : ℝ) (k : ℕ)
    (X : ∀ v' : CompIn Gr.comps, TorusHk k (hr v'.1.root))
    (hpar : ∀ c ∈ G.comps, compParent m c = c ∧ compWord m c = [])
    (hmem : ∀ c ∈ G.comps, c ∈ Gr.comps) (hzero : ∀ v' : CompIn Gr.comps, v'.1 ∉ G.comps → X v' = 0)
    (v : CompIn G.comps) :
    succReadout (S := G.comps) m E η k X v = X ⟨v.1, hmem v.1 v.2⟩ := by
  unfold succReadout
  rw [Finset.sum_eq_single (⟨v.1, hmem v.1 v.2⟩ : CompIn Gr.comps)]
  · rw [dite_eq_left_of_eq_true (eq_true (hpar v.1 v.2).1)]
    have hw : (compWord m v.1).length = 0 := by rw [(hpar v.1 v.2).2]; rfl
    simp only [hw, Nat.cast_zero, mul_zero, Real.rpow_zero, one_smul, cast_eq]
  · intro v' _ hne
    by_cases hv : v'.1 ∈ G.comps
    · have hneq : ¬ compParent m v'.1 = v.1 := by
        intro h
        apply hne
        apply Subtype.ext
        rw [← h, (hpar v'.1 hv).1]
      rw [dite_eq_right_of_eq_false (eq_false hneq)]
    · have hc : ∀ {a a' : ℕ} (e : a = a'),
          cast (congrArg (fun r => TorusHk k (hr r)) e) (0 : TorusHk k (hr a)) = 0 := by
        rintro a _ rfl; rfl
      rw [hzero v' hv]
      split_ifs with h
      · rw [hc ((compParent_root m v'.1).symm.trans (congrArg Comp.root h)), smul_zero]
      · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The three-step telescoping of a difference. -/
theorem sub_eq_telescope {E : Type*} [AddCommGroup E] (a b c d : E) :
    a - b = (a - c) - (d - c) - (b - d) := by abel

end InitialValue

end AVRegularity

namespace AVRegularity.Providers



/-- **The initial value of the successor** (Proposition 12.11 of the paper). -/
theorem successor_initial_value (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) :
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
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ mStar : ℕ,
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    ∀ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
      (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      G.IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        (D.κ m) (streamVel (D.Φ m)) 0 s₀ tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (û : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root)),
      IsLiftedField G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) tp tf Y CcT PZ aRep û →
    ∃ Qh : ∀ v : CompIn G.comps, TorusHk Naux (hr v.1.root),
      (∀ v, IsCovImage (covPolyQ (covPrimitive D m tp) p) (Preg f v) (Qh v)) ∧
      (∀ v, IsCovImage (covPolyP (covPrimitive D m tp) p) (Qh v) (PZ v tp)) ∧
      ∀ v, U v tp - û v tp =
        (U v tp - truncateTorusHk (Nat.zero_le Nout) (Preg f v)) -
          (truncateTorusHk (Nat.zero_le (Naux - 2 * p)) (PZ v tp) -
            truncateTorusHk (Nat.zero_le Nout) (Preg f v)) -
          (û v tp - truncateTorusHk (Nat.zero_le (Naux - 2 * p)) (PZ v tp)) := by
  refine ⟨128, le_rfl, fun Λ _ => ⟨1, one_pos, ?_⟩⟩
  intro φ₀ hφ₀ _ _ _ _ bw _ _ Q T₀ _ _ Ce τe kS r₀ D₀ _ _ _ _ _ _ _ _ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ _ _ _ _
  refine ⟨kS, 1, 1, le_rfl, one_pos, fun kI _ => ⟨0, 0, fun CI Cw j₀ _ _ CQ Cpr => ⟨0, ?_⟩⟩⟩
  intro D hDα hDq hDΛ _ _ M _ _ Mnat _ law _ hr _ _ _ _ _ _ seedK freshK _ seed n tS tf hgen m _ _ _
    tA s₀ _ _ hs₀tf _ G G' hcasc hlev _ hsucc tp Preg hprep f Ain _ Y0 Y Yw Yk htrace hYsol U Uw Uk _
    CcT PZ aRep û hlift
  have hinv := InitialValue.cascade_invariant hgen.2.1 hcasc
  have hm1 : 1 ≤ m := hlev ▸ hsucc.1
  have hpar : ∀ c ∈ G.comps, compParent m c = c ∧ compWord m c = [] := fun c hc =>
    InitialValue.compParent_eq_self hm1 (fun e he => hlev ▸ (hinv c hc).1 e he)
  have hmem : ∀ c ∈ G.comps, c ∈ (G'.retained m H J).comps := by
    intro c hc
    show c ∈ G'.comps.filter (IsRetained m H J)
    rw [Finset.mem_filter, hsucc.2.2.1]
    refine ⟨Finset.mem_union_left _ hc, (hinv c hc).2, ?_⟩
    rw [(hpar c hc).2]
    exact Nat.zero_le _
  have hY0 : (fun v' => Y v' tp) = Y0 := funext hYsol.2.2.2.1
  have htp : tp ∈ Set.Icc tp tf := by
    refine ⟨le_rfl, ?_⟩
    have h1 := hprep.2.2.1
    rw [hlev, hDα, hDq, hDΛ] at h1
    linarith
  subst hY0
  refine ⟨fun v => succReadout m (D.eps (m - 1)) (succEta0 α q s) Naux (fun v' => Y v' tp) v,
    fun v => ?_, fun v => (hlift.2.1 v tp htp).1, fun v => InitialValue.sub_eq_telescope _ _ _ _⟩
  have h1 := htrace.1 ⟨v.1, hmem v.1 v.2⟩ v.2
  have h2 := InitialValue.readout_self G (G'.retained m H J) m (D.eps (m - 1)) (succEta0 α q s)
    Naux (fun v' => Y v' tp) hpar hmem htrace.2 v
  exact (congrArg (IsCovImage _ (Preg f v)) h2).mpr h1

end AVRegularity.Providers
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance AVRegularity
namespace AVRegularity.Providers

/-! Proof of `context_strain_physical`. -/

/-- **The context strain at a physical context is `D𝐛_i`**. -/
theorem context_strain_physical (α q : ℝ) (hα₀ : 0 < α) (hq₁ : 1 < q) (Λ : ℕ) (ζ : ℝ → ℝ)
    (hζf : IsFastProfile ζ) (D : OCData) (hα : D.α = α)
    (hq : D.q = q) (hΛ : D.Λ = Λ) (hζ : D.ζ = ζ) (hS : IsOCStreamSeq α q Λ ζ D.Φ)
    (i : ℕ) (hi : 1 ≤ i) (pc : ℤ) (hpc : Odd pc) (t : ℝ) (ht : t ∈ ocPulseWindow α q Λ i pc)
    (Y : Vec 2) :
    contextStrain D i pc t ((nativeChain i pc).recenter D Y) ((D.eps i)⁻¹ • Y) =
      jacMatrix (streamVel (D.Φ i) t)
        ((((nativeChain i pc).recenter D Y).geom D).1 t Y
          (((nativeChain i pc).recenter D Y).geom D).2.2) :=
  StrainPhysical.context_strain_physical_aux α q hα₀ hq₁ Λ ζ hζf D hα hq hΛ hζ hS i hi pc hpc t ht Y

end AVRegularity.Providers
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.Providers

/-! Proof of `succ_window_data`.

The molecular metric of a family's lift operator is `𝒢_t = F⁻¹F⁻ᵀ` at the chart time `u = ℓ²t`
of the recentered chain, with `F_u` the Jacobian of its offset flow. The offset flow is jointly
`C¹` (`geomC1_geom`) and has the inverse law (`invLaw_geomAux`), so `F_u` is continuous and
invertible (`jac_continuous`, `jac_isUnit_det`); on the compact cell-time window its entries and
those of its inverse are bounded, which gives ellipticity and entry bounds (`metric_elliptic`,
`metric_entry_le`). The pulse drift is bounded since `0 ≤ p_k ≤ 1` and the shear velocity of an
odd pulse is an explicit cosine. -/

open SuccWindow

/-- The shear velocity of an odd pulse is bounded. -/
theorem ocShearVel_bound (α q : ℝ) (Λ m : ℕ) {k : ℤ} (hk : Odd k) (y : Vec 2) (j : Fin 2) :
    |ocShearVel α q Λ m k y j| ≤
      |2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹| := by
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by
    obtain ⟨r, rfl⟩ := hk
    omega
  set K := 2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹ with hK
  rcases hk4 with h1 | h3
  · rw [AVRegularity.CycleReference.ocShearVel_horizontal h1 y]
    fin_cases j
    · show |(0 : ℝ)| ≤ |K|
      rw [abs_zero]; exact abs_nonneg _
    · show |K * Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0)| ≤ |K|
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · rw [AVRegularity.CycleReference.ocShearVel_vertical h3 y]
    fin_cases j
    · show |-K * Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1)| ≤ |K|
      rw [abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · show |(0 : ℝ)| ≤ |K|
      rw [abs_zero]; exact abs_nonneg _

/-- The pulse drift of an odd pulse is bounded. -/
theorem ocPulseCellDrift_bound {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (m : ℕ)
    (ν : ℝ) {k : ℤ} (hk : Odd k) : ∃ Mv : ℝ, ∀ t z j, |ocPulseCellDrift α q Λ ζ m ν k t z j| ≤ Mv := by
  refine ⟨|ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m| *
    |2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹|, fun t z j => ?_⟩
  have hp := AVRegularity.CycleReference.ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k (ocEll q Λ m ν ^ 2 * t)
  have hu := ocShearVel_bound α q Λ m hk (ocEpsilon q Λ m • z) j
  have hp' : |ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t)| ≤ 1 := by
    rw [abs_of_nonneg hp.1]; exact hp.2
  show |ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m *
      (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) *
        ocShearVel α q Λ m k (ocEpsilon q Λ m • z) j)| ≤ _
  rw [abs_mul, abs_mul]
  gcongr
  calc |ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t)| *
        |ocShearVel α q Λ m k (ocEpsilon q Λ m • z) j|
      ≤ 1 * |2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹| :=
        mul_le_mul hp' hu (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The sum of the absolute entries of a `2 × 2` matrix bounds each entry. -/
private theorem entry_le_sum (F : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    |F i j| ≤ |F 0 0| + |F 0 1| + |F 1 0| + |F 1 1| := by
  have h00 := abs_nonneg (F 0 0)
  have h01 := abs_nonneg (F 0 1)
  have h10 := abs_nonneg (F 1 0)
  have h11 := abs_nonneg (F 1 1)
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- A continuous matrix family has bounded entries on a compact interval. -/
private theorem exists_entry_bound {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hF : Continuous F)
    (a b : ℝ) : ∃ M : ℝ, ∀ t ∈ Set.Icc a b, ∀ i j, |F t i j| ≤ M := by
  have hc : Continuous (fun t => |F t 0 0| + |F t 0 1| + |F t 1 0| + |F t 1 1|) := by
    have he : ∀ i j : Fin 2, Continuous (fun t => F t i j) := fun i j =>
      (continuous_apply j).comp ((continuous_apply i).comp hF)
    fun_prop
  obtain ⟨M, -, hM⟩ := exists_bound_Icc hc a b
  refine ⟨M, fun t ht i j => (entry_le_sum (F t) i j).trans ?_⟩
  have := hM t ht
  rwa [abs_of_nonneg (by positivity)] at this

/-- **Window data of the lift operators of a stage**. -/
theorem succ_window_data {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, NormedSpace ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hζ : IsFastProfile D.ζ) (_hκ : ∀ i, 0 < D.κ i) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) :
    SuccWindowData D b j₀ Mn G := by
  intro h π k A hA X
  set ch := A.recenter D ((Mn.lenFactor * liftLength D G.level) • X) with hch
  set g := ch.geom D with hg
  have hC : ∀ r : ℝ, ContDiff ℝ 1 (fun p : ℝ × Vec 2 => g.1 p.1 p.2 r) :=
    geomC1_geom D hζ ch
  have hinv : AVRegularity.ChainGeometry.InvLaw g :=
    AVRegularity.ChainGeometry.invLaw_geomAux D _ _ _ (AVRegularity.ChainGeometry.invLaw_base D _ _ _)
  set c := D.cellScaleSq G.level with hc
  let F : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => ch.famJac D (c * t)
  have hFc : Continuous F :=
    (jac_continuous (f := fun u y => g.1 u y g.2.2) (hC g.2.2) g.2.1).comp
      (continuous_const.mul continuous_id)
  have hFdet : ∀ t, IsUnit (F t).det := fun t => jac_isUnit_det hinv hC (c * t) g.2.2 g.2.1
  have hAc : Continuous (fun t => (F t)⁻¹) := continuous_inv_of_det hFc hFdet
  set a₀ := D.slotStart G.level k / c
  set b₀ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / c
  obtain ⟨M, hM⟩ := exists_entry_bound hFc a₀ b₀
  obtain ⟨N, hN⟩ := exists_entry_bound hAc a₀ b₀
  obtain ⟨Mv, hMv⟩ := ocPulseCellDrift_bound (α := D.α) (q := D.q) (Λ := D.Λ) hζ G.level
    (D.kap G.level) hA.2
  refine ⟨(4 * M ^ 2 + 1)⁻¹, 2 * N ^ 2, Mv, by positivity, fun t ht ξ => ?_,
    fun t ht i j => ?_, fun t _ z j => hMv t z j⟩
  · exact metric_elliptic (Matrix.nonsing_inv_mul _ (hFdet t)) (hM t ht) ξ
  · exact metric_entry_le (hN t ht) i j

end AVRegularity.Providers
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers

/-! Statement of the **path decomposition** identifying the comparison lift with the producer's
lifts, at **every grade** `1 ≤ h' ≤ h` of the comparison lift.

The comparison lift of `IsLiftedField` is the lift `CcT` of the full Hilbert fiber `G.fam.fiber` on
the native chart of the pulse `k` (`hnat`, supplied by `GenStage.IsNatural`) through the grade
`h = depth`; the producer's lifts inside `IsActualSuccessor` (`SuccSource.IsLiftFamily`) are the
lifts `Ccπ h' π` of the scalar path families `pathEdges G π` of the paths `π` of `h'` edges (each
through its own grade `h'`), on the same slot, original start and chart. Under the lift setting of
the full fiber **at the top grade `h`** (whose depth clause is `HasDepthAtMost (fiber) h`, satisfied
at `h = depth`, the grade used by `IsLiftedField`; a setting at a lower grade would require the
fiber to have no longer paths and is not assumed), the grade-`h'` degree-`n` cell mean of the full
lift applied to `f e` (a scalar `f` times a vector `e` of the source component `u`), read at the
target `v`, is the sum over the paths `π : u → v` of `h'` edges of the path mean (read at the entry
`h' ← 0`) times the ordered product of the maps of `π` applied to `e` (`rootPathMap`). The full
lift is triangular in the grade (`IsLiftSequence.restrict`, proved), so its grade-`h'` part is
determined by the grades `≤ h'`, and the statement is non-vacuous at every grade it is used: the
single setting premise is the one satisfiable at the top grade. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]

open scoped Classical in
/-- **Path decomposition of the full lift**. -/
theorem lift_path_decomposition {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (G : GenStage D hr Dm b j₀) (m : ℕ) (hm : G.level = m) (k : ℤ) (hk : Odd k)
    (hnat : (G.actual ⟨k, hk⟩).1 = nativeChain m k) (sX sZ N : ℕ)
    (h : ℕ)
    (π : CompIn G.comps → ℝ) (e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ)
    (K kk L qs qf : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (bb : CompIn G.comps → CompIn G.comps → ℝ)
    (Θ : ℝ)
    (hS : IsLiftSetting (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) π (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)
        e ν B ρ E ℓ dstar εc lam par V h N K kk L qs qf CG Cw Cj bb Θ)
    (hsX : sX ≤ qs) (hsZ : sZ ≤ qf) (hsX₂ : Dm + 2 ≤ sX) (hsZ₂ : Dm + 2 ≤ sZ)
    (CcT : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hT : IsLiftSequence (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      sX sZ (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N h CcT)
    (Ccπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ))
    (hπ : ∀ h' ≤ h, ∀ σ : StagePath G h', IsLiftSequence
      (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (pathEdges G σ ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      sX sZ (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N h' (Ccπ h' σ))
    (u v : CompIn G.comps) (f : Vec 2 → ℝ) (ev : hr u.1.root) (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m))
    (X : Vec 2) (j : Fin 2)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsXN : N + Dm + 1 ≤ sX) (hsZN : N + Dm + 1 ≤ sZ) :
    ∀ h' : ℕ, 1 ≤ h' → h' ≤ h →
    fieldCellMean (fun z => liftFluxX (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) CcT
        (fun _ Y => Pi.single u (f (liftLength D m • Y) • ev)) h' n t X z j v) =
      ∑ st : Fin h' → (Σ (v' u' : CompIn G.comps), G.fam.Γ v' u'),
        if hj : ∀ (i : ℕ) (hi : i + 1 < h'), (st ⟨i + 1, hi⟩).2.1 = (st ⟨i, by omega⟩).1 then
          if (StagePath.src ⟨st, hj⟩ = u.1 ∧ StagePath.tgt ⟨st, hj⟩ = v.1) then
            fieldCellMean (fun z => liftFluxX (familyLiftData D m k (nativeChain m k)
                (liftLength D m) (pathEdges G ⟨st, hj⟩ ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
                (Ccπ h' ⟨st, hj⟩)
                (fun _ Y => Pi.single (0 : Fin (h' + 1)) (f (liftLength D m • Y))) h' n t X z j
                (Fin.last h')) •
              rootPathMap hr u.1.root (StagePath.mapList ⟨st, hj⟩) v.1.root ev
          else 0
        else 0 :=
  by exact lift_path_decomposition_of_smooth G m hm k hk hnat sX sZ N h π e ν B ρ E ℓ dstar εc lam par V K kk L qs qf CG Cw Cj bb Θ hS hsX hsZ hsX₂ hsZ₂ CcT hT Ccπ hπ u v f ev n t ht X j hf hsXN hsZN

end AVRegularity.Providers
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers

/-! Successor coefficient uniqueness from the proved cell-window and chart
geometry inputs. The first diagonal source is excluded exactly as in the statement. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]

/-- **Uniqueness of the transferred coefficients of the next family**. -/
theorem successor_flux_unique {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (P : ProvParams)
    (hζ : IsFastProfile D.ζ) (hκ : ∀ i, 0 < D.κ i)
    (Mn : SuccMenu) (M : ℕ) (G G₁ G₂ : GenStage D hr Dm b j₀) (hnat : G.IsNatural M)
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (h₁ : IsActualSuccessor D P Mn G G₁)
    (h₂ : IsActualSuccessor D P Mn G G₂) (v₁ u₁ : CompIn G₁.comps) (γ₁ : G₁.fam.Γ v₁ u₁)
    (v₂ u₂ : CompIn G₂.comps) (γ₂ : G₂.fam.Γ v₂ u₂) (hv : v₁.1 = v₂.1) (hu : u₁.1 = u₂.1)
    (hγ : G₁.prov v₁ u₁ γ₁ = G₂.prov v₂ u₂ γ₂)
    (hnd : ∀ m', G₁.prov v₁ u₁ γ₁ ≠ Prov.letter m' .diag []) (p : OddSlot)
    (c₁ : StageCtx D b j₀ G₁.level p) (c₂ : StageCtx D b j₀ G₂.level p) (hc : c₁.1 = c₂.1)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2) (hd : 2 ≤ d) :
    G₁.fam.flux p c₁ v₁ u₁ γ₁ d I t X z = G₂.fam.flux p c₂ v₂ u₂ γ₂ d I t X z :=
by
  exact Uniqueness.successor_flux_unique_of_succ_window_data P hζ hκ Mn M G G₁ G₂ hnat
    hold h₁ h₂ v₁ u₁ γ₁ v₂ u₂ γ₂ hv hu hγ hnd p c₁ c₂ hc d I t X z hd
    (succ_window_data hζ hκ Mn G)
    (fun _ _ hA => ⟨GenSem.isOpen_ladderOmega _ _ _ _ _ _ _,
      GenSem.zero_mem_ladderOmega hζ hA _⟩)
    (fun A t => ⟨(GenSem.contDiff_famMapInv A t).continuous.continuousAt,
      GenSem.famMapInv_zero hζ A t⟩)

end AVRegularity.Providers
end
end
