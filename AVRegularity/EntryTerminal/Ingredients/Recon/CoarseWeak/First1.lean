-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Recon.CoarseWeak.FirstInput
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofSourceMeanDirect
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseMain
import AVRegularity.Construction.StrainPhysical.Context
import AVRegularity.EntryWeak.NormalizedPulseTransverse
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofSourceMeanEdges
import AVenhance.Infra.Construction.StreamAdmissible

/-! Terminal first-source proof: the generic proof with the degree cutoff omitted only from its
input. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
/-- **The glued mean flux is `C^s` in space.** -/
theorem s47_menuGluedMeanFlux_contDiff (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hin : FirstSourceInput P Mn G G' depth CcT) (s : ℕ) (hsX : s + Dm ≤ Mn.sX) (hsZ : s + Dm ≤ Mn.sZ)
    (rs ns : Finset ℕ) (hrs : ∀ r ∈ rs, r ≤ depth)
    (hE : (∃ r ∈ rs, r ≠ 0) → ActualFluxJointSmooth G)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ)
    (ha : ContDiff ℝ ((s + Dm + Mn.N : ℕ) : ℕ∞) (a t)) (v : CompIn G.comps) :
    ContDiff ℝ (s : ℕ∞) (fun x => menuGluedMeanFlux Mn G G.level rs ns CcT a t x v) := by
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hin.stage.base hin.stage.profile
    hin.stage.band G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hin.stage.base
  unfold menuGluedMeanFlux
  refine ContDiff.sum fun k _ => ContDiff.sum fun r hr => ContDiff.sum fun n _ => ?_
  by_cases hodd : Odd k
  · simp only [hodd, dite_true]
    by_cases hcut : ocCutoff D.α D.q D.Λ G.level k t = 0
    · simp only [hcut, zero_smul]
      exact contDiff_const
    · refine ContDiff.const_smul _ ?_
      have ht' := clock_mem_window D G.level k t hτ hcc hcut
      have hwin := AVRegularity.Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
      obtain ⟨_, _, hz3, _, _, hbox, _⟩ := hin.lift k hodd
      refine pulseMeanFluxEuler_contDiff _ _ _ n r _ _ _ _ _ t v s Mn.N depth hcc.ne'
        hin.stage.order (hrs r hr) hz3 ?_ ?_ ?_ ?_ ha ?_ ?_
      · exact fun hh' hH n' m α v u => (hbox hh' hH n' m α v u _ ht').1.mono hsX hsZ
      · intro k' j
        exact (EntryWeakProofs.familyLiftData_metric_entry_smooth D G.level k _
          (by simp [nativeChain]) _ _ _ k' j).of_le (by exact_mod_cast le_top)
      · intro k'
        exact (ocPulseCellDrift_contDiff D.α D.q D.Λ D.ζ G.level (D.kap G.level) hodd _ k').of_le
          (by exact_mod_cast le_top)
      · intro hr0
        exact fiber_edge_boxSmooth G (hE ⟨r, hr, hr0⟩) k hodd _ _ t hcc.ne' hwin s
      · exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
          (D.slotAnchor G.level k)).of_le (by exact_mod_cast le_top)
      · exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
          (D.slotAnchor G.level k) t).of_le (by exact_mod_cast le_top)
  · simp only [hodd, dite_false]
    exact contDiff_const

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

open CovarianceTransport

section Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Operators

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The floors of `FirstSourceInput.range` give the orders needed at `s = 2p`. -/
theorem s47_floors' (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hin : FirstSourceInput P Mn G G' depth CcT) :
    2 * Mn.p + Dm ≤ Mn.sX ∧ 2 * Mn.p + Dm ≤ Mn.sZ := by
  obtain ⟨Dord, nMax, hMax, npad, _, _, _, _, h1, h2⟩ := hin.range
  have := le_max_right (Mn.N + Dord) (2 * Mn.p)
  omega

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
/-- **Clause 1: the temporal flux is `C^{2p}`.** -/
theorem s47_menuTemporalFlux_contDiff (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hin : FirstSourceInput P Mn G G' depth CcT) (K : ℕ) (hK : Mn.N + Dm + 4 * Mn.p ≤ K)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ)
    (hg : ∀ v, ContDiff ℝ (K : ℕ∞) (fun x => g t x v)) (v : CompIn G.comps) :
    ContDiff ℝ ((2 * Mn.p : ℕ) : ℕ∞) (fun y => menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y) := by
  obtain ⟨hX, hZ⟩ := s47_floors' P Mn G G' depth CcT hin
  have hord : 1 ≤ Dm := hin.stage.order
  have hbv : ContDiff ℝ (⊤ : ℕ∞) (streamVel (D.Φ (G.level - 1)) t) :=
    ((AVenhance.Infra.Construction.smoothPeriodic_streamVel (D.hΦ (G.level - 1))).smooth).comp
      (contDiff_const.prodMk contDiff_id)
  have ha : ContDiff ℝ ((2 * Mn.p + Dm + Mn.N : ℕ) : ℕ∞) (menuCovPRep Mn D G.level Mn.p g t) := by
    refine contDiff_pi.mpr fun w => ?_
    exact covPolyP_contDiff _ Mn.p _ ((hg w).of_le (by exact_mod_cast (by omega :
      2 * Mn.p + Dm + Mn.N + 2 * Mn.p ≤ K)))
  have hga : ContDiff ℝ ((2 * Mn.p + 1 : ℕ) : ℕ∞) (fun y => menuCovPRep Mn D G.level Mn.p g t y v) :=
    covPolyP_contDiff _ Mn.p _ ((hg v).of_le (by exact_mod_cast (by omega :
      2 * Mn.p + 1 + 2 * Mn.p ≤ K)))
  unfold menuTemporalFlux menuDiagFluxPhys
  refine ContDiff.sub ?_ (ContDiff.sub ?_ ?_)
  · exact temporal_comm_contDiff _ hbv _ Mn.p K (by omega) (hg v)
  · exact s47_menuGluedMeanFlux_contDiff P Mn G G' depth CcT hin (2 * Mn.p) hX hZ {0}
      (Finset.Icc 2 (Mn.N + 1)) (fun r hr => by simp at hr; omega)
      (fun ⟨r, hr, hr0⟩ => absurd (Finset.mem_singleton.mp hr) hr0)
      (menuCovPRep Mn D G.level Mn.p g) t ha v
  · refine contDiff_pi.mpr fun j => ContDiff.sum fun l _ => ContDiff.smul contDiff_const ?_
    exact gradE_contDiff (2 * Mn.p) hga l

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The label array of the first source of the piece `p` of `G'` at the time `t` and the point `x`:
`fluxCoeff (firstSourceFlux …) d I 0` at the recentred actual context of `p` (recentred at
`Y = Φ_p(t,·)⁻¹ x`) and the fast variable `ε_{m-1}⁻¹ Y`; zero when that context is not admissible
(the formula of the flux of the first-source identity, `IsActualSuccessor`). -/
def fsPieceArray' (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (p : OddSlot) (t : ℝ)
    (x : Vec 2) : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 :=
  fun d I =>
    if IsAdmissibleChain D b j₀ G'.level p.1
        ((G'.actual p).1.recenter D (((G'.fam.piece p).material t).symm x))
    then fluxCoeff (firstSourceFlux D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level)
        Mn.N Mn.p Mn.anchor Cc0 t ((G'.actual p).1.recenter D (((G'.fam.piece p).material t).symm x))
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) d I 0
    else 0

/-- The physical flux of the first source through the piece `p`: the Piola transport
(`transportedCoeff`, order `N + 1 + 4p`) of `fsPieceArray'`, contracted with the ordered derivatives
of `g` at `x` (the shape of `constituentPhysical` for the identity map). -/
def fsPiecePhys' (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (p : OddSlot)
    (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => hr v.1.root)).symm
    (fun k : Fin 2 => ∑ d ∈ Finset.Icc 2 Dm, ∑ A : DerivativeWord2 (d - 1),
      transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
        (Mn.N + 1 + 4 * Mn.p) (fsPieceArray' Mn G G' Cc0 p t x) (d - 1) A x k •
        orderedDerivative A (fun y => g t y v) x)

/-- The hypotheses on the field of the first-source flux identity: class `C^K`, `K ≥ N + Dm + 4p`, periodic, on the
window. -/
def FSField' (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (K : ℕ) (ta tb : ℝ)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) : Prop :=
  Mn.N + Dm + 4 * Mn.p ≤ K ∧ ∀ v, ∀ t ∈ Set.Icc ta tb,
    ContDiff ℝ (K : ℕ) (fun x => g t x v) ∧ IsZ2Periodic (fun x => g t x v)

/-- **Step 1.** The diagonal readout is the glue over the pieces of
`G'` of the physical flux of the first source: the only first-source identity out of the root `v`
into a child of `v` is `letterDiag [] v` (provenance `letter m diag []`, unit total weight
`E^{η₀·1}·lam = 1`), its flux is the formula of `IsActualSuccessor` (the factor
`lam (κ ε^{d-2})⁻¹` cancels the readout weight and `ν e^{d-2}` of `dimFlux`), and orders above its
`maxOrder = N + 1 + 4p ≤ Dm` carry the zero array. -/
def FirstSourceReadoutStatement' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (v : CompIn G.comps) (t : ℝ) (x : Vec 2),
    diagReadout G G' G.level (D.eps (G.level - 1)) Mn.η0 g v t x =
      ∑ᶠ p : OddSlot, G'.fam.weight p t • fsPiecePhys' Mn G G' W.Cc0 g v p t x

/-- **Step 2 (one piece is `-Q_p 𝒟`).** For a piece of nonzero weight at a time of the window
(so `t` is in its output window and every active finer slot is scheduled in it), the Piola
transport of the first-source arrays of the piece is `-Q_p 𝒟 g`: `piecePiolaFiniteOrder`
and `arrOp_eq_sum_fluxCoeff`/`firstSourceFlux_applyArr` turn it into the Eulerian operator
`K · firstSourceFlux`; the context strain at the actual context is `D𝐛_{m-1}`
(`context_strain_physical`, `m - 1 ≥ 1`); `diagFluxCtx = diagFluxPhys` at the actual context
(`hilbertLiftGradeZero` on each component, the appended children as for the other pieces); the `C^K` field is
handled in the same way. -/
def FirstSourcePieceStatement' : Prop :=
  RootSourceBookkeepingStatement → PiecePiolaFiniteOrderStatement →
    HilbertLiftGradeZeroStatement →
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (K : ℕ) (ta tb : ℝ)
      (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root), FSField' Mn G K ta tb g →
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc ta tb, ∀ x : Vec 2, ∀ p : OddSlot,
      G'.fam.weight p t ≠ 0 →
      fsPiecePhys' Mn G G' W.Cc0 g v p t x =
        -covTemporalAt Mn G G.level Mn.N Mn.p CcT g v t x

/-- **The first-source flux identity, assembled from the two named steps.** -/
theorem firstSourceIdentity_of_steps' (S1 : FirstSourceReadoutStatement')
    (S2 : FirstSourcePieceStatement') :
    RootSourceBookkeepingStatement → PiecePiolaFiniteOrderStatement →
      HilbertLiftGradeZeroStatement → FirstSourceIdentityStatement' := by
  intro h1 h2 h5 hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin K hK ta tb g hg v t ht x
  obtain ⟨W⟩ := splitWitness_nonempty hin.successor
  rw [S1 P Mn G G' depth CcT hin W g v t x]
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  have key : ∀ p : OddSlot, G'.fam.weight p t • fsPiecePhys' Mn G G' W.Cc0 g v p t x =
      G'.fam.weight p t • (-covTemporalAt Mn G G.level Mn.N Mn.p CcT g v t x) := by
    intro p
    by_cases hp : G'.fam.weight p t = 0
    · simp [hp]
    · rw [S2 h1 h2 h5 P Mn G G' depth CcT hin W K ta tb g ⟨hK, hg⟩ v t ht x p hp]
  rw [finsum_congr key, ← finsum_smul, fs_weight_finsum hnat, one_smul]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The inner sum of `rootDiagFlux` at one identity. -/
def fsDiagInner' (G G' : GenStage D hr Dm b j₀)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v1 u1 : CompIn G'.comps)
    (γ0 : G'.fam.Γ v1 u1) (hu : u1.1 ∈ G.comps) (t : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => hr v1.1.root) :=
  ∑ d : Finset.Icc 2 Dm,
    G'.physCoeff v1 u1 γ0 d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      orderedDerivative word (fun y => g t y ⟨u1.1, hu⟩) x)

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem fs_rootDiag_collapse' {G G' : GenStage D hr Dm b j₀}
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v1 u1 : CompIn G'.comps) (γ0 : G'.fam.Γ v1 u1) (hu : u1.1 ∈ G.comps)
    (hprov0 : G'.prov v1 u1 γ0 = Prov.letter G.level WordLetter.diag [])
    (huniq : ∀ (u' : CompIn G'.comps) (γ' : G'.fam.Γ v1 u'), u'.1 ∈ G.comps →
        G'.prov v1 u' γ' = Prov.letter G.level WordLetter.diag [] →
        ∃ h : u' = u1, h ▸ γ' = γ0)
    (t : ℝ) (x : Vec 2) :
    rootDiagFlux G G' g v1 t x = fsDiagInner' G G' g v1 u1 γ0 hu t x := by
  classical
  unfold rootDiagFlux
  rw [Finset.sum_eq_single u1]
  · simp only [hu, ↓reduceDIte]
    rw [Finset.sum_eq_single γ0]
    · simp only [hprov0, ↓reduceIte]; rfl
    · intro γ _ hne
      simp only [ite_eq_right_iff]
      intro hp
      obtain ⟨_, h⟩ := huniq u1 γ hu hp
      exact absurd h hne
    · simp
  · intro u' _ hne
    by_cases hu' : u'.1 ∈ G.comps
    · simp only [hu', ↓reduceDIte]
      apply Finset.sum_eq_zero
      intro γ _
      simp only [ite_eq_right_iff]
      intro hp
      obtain ⟨h, _⟩ := huniq u' γ hu' hp
      exact absurd h hne
    · simp only [hu', ↓reduceDIte]
  · simp

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The dimensional flux of the first-source identity at a piece. -/
theorem fs_dimFlux_eq' {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    {depth : ℕ} {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : FirstSourceInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G')
    (v1 u1 : CompIn G'.comps) (γ0 : G'.fam.Γ v1 u1) (hdiag : (W.e v1 u1 γ0).1.IsDiag)
    (p : OddSlot) (t : ℝ) (x : Vec 2) {d : ℕ} (hd : 2 ≤ d) (I : DerivativeWord2 (d - 1)) :
    G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1)) p (G'.actual p)
        v1 u1 γ0 d I t (((G'.fam.piece p).material t).symm x)
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) =
      (W.e v1 u1 γ0).1.lam G.level Mn.η0 • fsPieceArray' Mn G G' W.Cc0 p t x d I := by
  have hsucc := hin.successor
  have hΛ := hin.stage.base
  have hε : D.eps G'.level ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hεc : D.eps (G'.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hκ : D.kap G'.level ≠ 0 :=
    (EntryWeakProofs.weakData_kap_pos D hΛ hin.stage.profile hin.stage.band G'.level).ne'
  have hkk : D.kap G'.level = D.κ G'.level := by
    have h1 := hsucc.1
    have h2 := hsucc.2.1
    have h3 := hin.stage.top
    unfold OCData.kap
    rw [min_eq_left (by omega)]
  simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux]
  rw [(W.spec v1 u1 γ0).2.2.2 hdiag p (G'.actual p) d I t _ _ hd, smul_inv_smul₀ hεc]
  unfold fsPieceArray'
  by_cases hadm : IsAdmissibleChain D b j₀ G'.level p.1
      ((G'.actual p).1.recenter D (((G'.fam.piece p).material t).symm x))
  · simp only [hadm, ↓reduceIte, smul_smul, hkk]
    rw [← hkk]
    congr 1
    field_simp
  · simp [hadm]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The first-source identity out of `v`: existence, weight, and uniqueness. -/
theorem fs_diag_data' {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀} {depth : ℕ}
    {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : FirstSourceInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G') (v : CompIn G.comps) :
    ∃ (v1 u1 : CompIn G'.comps) (γ0 : G'.fam.Γ v1 u1), u1.1 = v.1 ∧
      compParent G.level v1.1 = v.1 ∧
      G'.prov v1 u1 γ0 = Prov.letter G.level WordLetter.diag [] ∧
      D.eps (G.level - 1) ^ (Mn.η0 * ((compWord G.level v1.1).length : ℝ)) *
        (W.e v1 u1 γ0).1.lam G.level Mn.η0 = 1 ∧
      ∀ (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'), u'.1 ∈ G.comps →
        compParent G.level v'.1 = v.1 →
        G'.prov v' u' γ' = Prov.letter G.level WordLetter.diag [] →
        v' = v1 ∧ u' = u1 ∧ (W.e v' u' γ').1 = (W.e v1 u1 γ0).1 := by
  have bk := rootSourceBookkeeping P Mn G G' hin.stage hin.successor W
  have hdiagA : WordLetter.diag ∈ Mn.A := by
    obtain ⟨Dord, nMax, hMax, npad, hA, -⟩ := hin.range
    rw [hA]; simp [succAlphabet]
  have hval : (SuccSource.letterDiag ([] : List WordLetter) v).Valid Mn.A Mn.J := by
    refine ⟨by simp [SuccSource.word], ?_, trivial⟩
    intro l hl
    simp only [SuccSource.letter?, Option.some.injEq] at hl
    subst hl
    exact ⟨by simp [SuccSource.word], hdiagA⟩
  obtain ⟨v1, u1, γ0, he0, hu1⟩ := bk.2.2 _ hval rfl
  obtain ⟨hw0, hos0, hot0, hpar0, hcw0, hwt0, hdiag0⟩ := bk.2.1 v1 u1 γ0 hu1
  have hsrc0 : (W.e v1 u1 γ0).1.oldSrc = v.1 := by rw [he0]; rfl
  have hprov0 : G'.prov v1 u1 γ0 = Prov.letter G.level WordLetter.diag [] :=
    hdiag0.1 (by rw [he0]; trivial)
  refine ⟨v1, u1, γ0, ?_, ?_, hprov0, hwt0, ?_⟩
  · rw [← hos0, hsrc0]
  · rw [hpar0, he0]; rfl
  · intro v' u' γ' hu' hpar hprov
    obtain ⟨hw, hos, hot, hpar', hcw, hwt, hdiag⟩ := bk.2.1 v' u' γ' hu'
    have hD : (W.e v' u' γ').1.IsDiag := hdiag.2 hprov
    have hprovS := (rsb_isDiag_iff G.level _).1 hD
    obtain ⟨t, w, hs⟩ := fs_isDiag_cases G.level _ hprovS
    have hold : (W.e v' u' γ').1.oldTgt = v.1 := by rw [← hpar', hpar]
    have hwv : w = v := by
      apply Subtype.ext
      have : (W.e v' u' γ').1.oldTgt = w.1 := by rw [hs]; rfl
      rw [← this, hold]
    have ht : t = [] := by rw [← hw, hs]; rfl
    have hs' : (W.e v' u' γ').1 = (W.e v1 u1 γ0).1 := by rw [hs, he0, ht, hwv]
    refine ⟨?_, ?_, hs'⟩
    · apply Subtype.ext
      rw [← (W.e v' u' γ').2.2.2, ← (W.e v1 u1 γ0).2.2.2, hs']
    · apply Subtype.ext
      rw [← (W.e v' u' γ').2.2.1, ← (W.e v1 u1 γ0).2.2.1, hs']

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The readout collapses to the single first-source identity. -/
theorem fs_readout_collapse' {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (W : SplitWitness P Mn G G')
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (v1 u1 : CompIn G'.comps) (γ0 : G'.fam.Γ v1 u1) (hu : u1.1 ∈ G.comps)
    (hpar : compParent G.level v1.1 = v.1)
    (hprov0 : G'.prov v1 u1 γ0 = Prov.letter G.level WordLetter.diag [])
    (huniq : ∀ (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'), u'.1 ∈ G.comps →
        compParent G.level v'.1 = v.1 →
        G'.prov v' u' γ' = Prov.letter G.level WordLetter.diag [] →
        v' = v1 ∧ u' = u1 ∧ (W.e v' u' γ').1 = (W.e v1 u1 γ0).1)
    (t : ℝ) (x : Vec 2) :
    diagReadout G G' G.level (D.eps (G.level - 1)) Mn.η0 g v t x =
      (D.eps (G.level - 1)) ^ (Mn.η0 * ((compWord G.level v1.1).length : ℝ)) •
        cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r))
          ((compParent_root G.level v1.1).symm.trans (congrArg Comp.root hpar)))
          (fsDiagInner' G G' g v1 u1 γ0 hu t x) := by
  classical
  unfold diagReadout readoutFlux
  rw [Finset.sum_eq_single v1]
  · simp only [hpar, and_self, ↓reduceDIte]
    congr 2
    refine fs_rootDiag_collapse' g v1 u1 γ0 hu hprov0 ?_ t x
    intro u' γ' hu' hp
    obtain ⟨-, rfl, hs⟩ := huniq v1 u' γ' hu' hpar hp
    exact ⟨rfl, (W.e v1 u').injective (Subtype.ext hs)⟩
  · intro v' _ hne
    by_cases hc : compParent G.level v'.1 = v.1
    · simp only [hc, and_self, ↓reduceDIte]
      rw [fs_rootDiag_zero g v' ?_ t x]
      · simp only [smul_eq_zero]
        exact Or.inr (fs_cast_zero ((compParent_root G.level v'.1).symm.trans
          (congrArg Comp.root hc)) _)
      · intro u' γ' hu' hp
        exact hne (huniq v' u' γ' hu' hc hp).1
    · simp [hc]
  · simp

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The component of the single-identity term as the sum over the pieces. -/
theorem fs_inner_apply' {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    {depth : ℕ} {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : FirstSourceInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G')
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v1 u1 : CompIn G'.comps) (γ0 : G'.fam.Γ v1 u1) (hu : u1.1 ∈ G.comps)
    (hprov0 : G'.prov v1 u1 γ0 = Prov.letter G.level WordLetter.diag [])
    (hdiag : (W.e v1 u1 γ0).1.IsDiag)
    (h0 : u1.1.root = v1.1.root) (hmaps : (W.e v1 u1 γ0).1.maps = [])
    (t : ℝ) (x : Vec 2) (κ : Fin 2) :
    fsDiagInner' G G' g v1 u1 γ0 hu t x κ =
      h0 ▸ ∑ d ∈ Finset.Icc 2 Dm, ∑ p ∈ (G'.fam.locally_finite t t).toFinset,
        G'.fam.weight p t • ∑ A : DerivativeWord2 (d - 1),
          ((W.e v1 u1 γ0).1.lam G.level Mn.η0 *
            transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
              (Mn.N + 1 + 4 * Mn.p) (fsPieceArray' Mn G G' W.Cc0 p t x) (d - 1) A x κ) •
            orderedDerivative A (fun y => g t y ⟨u1.1, hu⟩) x := by
  have htags : G'.HasTags P := hin.successor.2.2.2.2.1
  have hmax : (G'.fam.identity v1 u1 γ0).maxOrder = Mn.N + 1 + 4 * Mn.p := by
    rw [(htags v1 u1 γ0).2, hprov0]
    simp only [Prov.tags, letterOrder]
    rw [hin.stage.cutoff_eq, hin.stage.covariance_eq]
  have hmap : (G'.fam.identity v1 u1 γ0).map = rootPathMap hr u1.1.root [] v1.1.root := by
    rw [(W.spec v1 u1 γ0).2.1, hmaps]
  unfold fsDiagInner'
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [tc_physCoeff_apply]
  rw [Finset.sum_coe_sort (Finset.Icc 2 Dm) fun d : ℕ =>
    ∑ p ∈ (G'.fam.locally_finite t t).toFinset, G'.fam.weight p t •
      ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
          (G'.fam.identity v1 u1 γ0).maxOrder
          (fun d' I => G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1)) p
            (G'.actual p) v1 u1 γ0 d' I t (((G'.fam.piece p).material t).symm x)
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x))
          (d - 1) A x κ • (G'.fam.identity v1 u1 γ0).map
            (orderedDerivative A (fun y => g t y ⟨u1.1, hu⟩) x)]
  obtain ⟨φ, hφ⟩ := fs_eqrec_linear (hr := hr) h0
  have happly : ∀ y : hr u1.1.root, (G'.fam.identity v1 u1 γ0).map y = φ y := by
    intro y
    rw [hmap, fs_rootPathMap_nil_apply h0, hφ]
  simp only [happly, ← hφ, map_sum, map_smul]
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun p _ => ?_
  have hd2 := (Finset.mem_Icc.mp hd).1
  congr 1
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [hmax]
  congr 1
  rw [Providers.QuietAtlas.transportedCoeff_congr _ _ (B' := fun d' I => (W.e v1 u1 γ0).1.lam G.level Mn.η0 •
      fsPieceArray' Mn G G' W.Cc0 p t x d' I) (fun d' hd' _ I =>
    fs_dimFlux_eq' hin W v1 u1 γ0 hdiag p t x (by omega) I) A x,
    fs_transportedCoeff_smul]

/-- **Step 1 of the first-source flux identity**: the diagonal readout is the glue over the pieces of the physical
flux of the first source. -/
theorem firstSourceReadout' : FirstSourceReadoutStatement' := by
  classical
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W g v t x
  obtain ⟨v1, u1, γ0, hu1v, hpar, hprov0, hwt, huniq⟩ := fs_diag_data' hin W v
  have hu : u1.1 ∈ G.comps := hu1v ▸ v.2
  have hprovS := ((W.spec v1 u1 γ0).1).symm.trans hprov0
  have hdiag : (W.e v1 u1 γ0).1.IsDiag := (rsb_isDiag_iff _ _).2 hprovS
  obtain ⟨t', w', hs⟩ := fs_isDiag_cases G.level _ hprovS
  have hmaps : (W.e v1 u1 γ0).1.maps = [] := by rw [hs]; rfl
  have h0 : u1.1.root = v1.1.root := by rw [hu1v, ← hpar, compParent_root]
  rw [fs_readout_collapse' W g v v1 u1 γ0 hu hpar hprov0 huniq t x]
  have hinner := fs_inner_apply' hin W g v1 u1 γ0 hu hprov0 hdiag h0 hmaps t x
  rcases v with ⟨c, hc⟩
  rcases u1 with ⟨c', hc'⟩
  simp only at hu1v hu h0 hinner
  subst hu1v
  have hsupp : (Function.support fun p : OddSlot =>
      G'.fam.weight p t • fsPiecePhys' Mn G G' W.Cc0 g ⟨c', hc⟩ p t x) ⊆
      ↑(G'.fam.locally_finite t t).toFinset := by
    intro p hp
    simp only [Function.mem_support] at hp
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    refine ⟨t, ?_, Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩⟩
    by_contra hnot
    exact hp (by rw [G'.fam.weight_zero p t hnot, zero_smul])
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [fs_cast_of_eqrec h0 ((compParent_root G.level v1.1).symm.trans (congrArg Comp.root hpar)) _ (fun κ => ∑ d ∈ Finset.Icc 2 Dm,
      ∑ p ∈ (G'.fam.locally_finite t t).toFinset, G'.fam.weight p t • ∑ A : DerivativeWord2 (d - 1),
        ((W.e v1 ⟨c', hc'⟩ γ0).1.lam G.level Mn.η0 *
          transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
            (Mn.N + 1 + 4 * Mn.p) (fsPieceArray' Mn G G' W.Cc0 p t x) (d - 1) A x κ) •
          orderedDerivative A (fun y => g t y ⟨c', hc⟩) x) hinner]
  ext κ
  simp only [fsPiecePhys', WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    PiLp.smul_apply, PiLp.continuousLinearEquiv_symm_apply]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun A _ => ?_
  rw [smul_comm, smul_smul, smul_smul]
  rw [smul_smul]
  congr 1
  linear_combination (G'.fam.weight p t * transportedCoeff
    (chartInvJacobian ⇑((G'.fam.piece p).material t).symm) (Mn.N + 1 + 4 * Mn.p)
    (fsPieceArray' Mn G G' W.Cc0 p t x) (d - 1) A x κ) * hwt

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The recentred actual context of the piece `p` at the physical point `x`. -/
def fsCtx' (G' : GenStage D hr Dm b j₀) (p : OddSlot) (t : ℝ) (x : Vec 2) : RealChain :=
  (G'.actual p).1.recenter D (((G'.fam.piece p).material t).symm x)

/-- The label operator of the first source at the piece `p` and the point `x`. -/
def fsLabelOp' (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (p : OddSlot) (t : ℝ)
    (x : Vec 2) : (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  firstSourceFlux D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N Mn.p Mn.anchor Cc0 t
    (fsCtx' G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)

open scoped Classical in
/-- The Eulerian reading of the label operator on a scalar field `f`: the Piola factor
`K(x) = chartInvJacobian` times the label operator at the centre on `f∘Φ_p(t, Y + ·)`;
zero off the carrier. -/
def fsEulerRead' (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (p : OddSlot) (t : ℝ)
    (x : Vec 2) (f : Vec 2 → ℝ) : Vec 2 :=
  if IsAdmissibleChain D b j₀ G'.level p.1 (fsCtx' G' p t x) then
    (chartInvJacobian ⇑((G'.fam.piece p).material t).symm x).mulVec
      (fsLabelOp' Mn G G' Cc0 p t x
        (fun y => f ((G'.fam.piece p).material t (((G'.fam.piece p).material t).symm x + y))) 0)
  else 0

/-- **Sub-step Piola.** -/
def FSStepPiola' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (K : ℕ) (ta tb : ℝ)
      (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root), FSField' Mn G K ta tb g →
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc ta tb, ∀ x : Vec 2, ∀ p : OddSlot,
      G'.fam.weight p t ≠ 0 → ∀ (ℓ : hr v.1.root →L[ℝ] ℝ) (κ : Fin 2),
      ℓ (fsPiecePhys' Mn G G' W.Cc0 g v p t x κ) =
        fsEulerRead' Mn G G' W.Cc0 p t x (fun y => ℓ (g t y v)) κ

/-- **Sub-step Strain.** ROUTINE. At a time of nonzero weight the context strain at the actual
context recentred at any `Y` is `D𝐛_{m-1}` (the statement of `context_strain_physical`). -/
def FSStepStrain' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 → ∀ Y : Vec 2,
      contextStrain D (G.level - 1) p.1 t ((G'.actual p).1.recenter D Y)
          ((D.eps (G.level - 1))⁻¹ • Y) =
        jacMatrix (streamVel (D.Φ (G.level - 1)) t)
          (((((G'.actual p).1.recenter D Y).geom D).1 t Y
            (((G'.actual p).1.recenter D Y).geom D).2.2))

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

section Pure
variable (D : OCData)

end Pure

section Unfold

/-- The commutator flux `𝒥_H` of `firstSourceFlux`, with the context strain read at the recentred
context of each point. -/
def fsAlgJH' (D : OCData) (m : ℕ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (ch : RealChain)
    (ζ : Vec 2) : (Vec 2 → ℝ) → Vec 2 → Vec 2 := fun g x =>
  -((contextStrain D (m - 1) ch.slot t (ch.recenter D (ch.famMapInv D t x))
          (ζ + (D.eps (m - 1))⁻¹ • ch.famMapInv D t x) * Hc +
        Hc * Matrix.transpose (contextStrain D (m - 1) ch.slot t
          (ch.recenter D (ch.famMapInv D t x)) (ζ + (D.eps (m - 1))⁻¹ • ch.famMapInv D t x))).mulVec
        (gradField g x))

/-- The commutator sum `∑_l (1/l!) ∑_{a<l} 𝒞^a 𝒥 𝒞^{l-1-a}` for a commutator flux `J`. -/
def fsAlgSum' (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (J : (Vec 2 → ℝ) → Vec 2 → Vec 2)
    (g : Vec 2 → ℝ) : Vec 2 → Vec 2 := fun z =>
  ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
    (covOperator Hc)^[a] (J ((covOperator Hc)^[l - 1 - a] g)) z

/-- `firstSourceFlux` unfolded. -/
theorem fsAlg_firstSourceFlux_eq' (D : OCData) (b : ℝ) (j₀ : ℕ) (Dm m : ℕ) (ρ : ℝ) (N p : ℕ)
    (s₀ : ℝ) (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (u : Vec 2 → ℝ) (y : Vec 2) :
    firstSourceFlux D b j₀ Dm m ρ N p s₀ Cc0 t ch ζ u y =
      ((jacMatrix (ch.famMap D t) y)⁻¹).mulVec
        (covPolyQ (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) p (fun x' =>
          -(fsAlgSum' (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) p
              (fsAlgJH' D m (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) t ch ζ)
              (u ∘ ch.famMapInv D t) x') +
            diagFluxCtx D b j₀ Dm m ρ N Cc0 t ch ζ
              (covPolyP (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) p
                (u ∘ ch.famMapInv D t)) x') (ch.famMap D t y)) := rfl

end Unfold

section Generic
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀} {depth : ℕ}
  {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The recentred actual context of a piece is the native context at the label `Φ_p(t,·)⁻¹ x`. -/
theorem fsAlg_ctx_native' (hin : FirstSourceInput P Mn G G' depth CcT) (p : OddSlot) (t : ℝ) (x : Vec 2) :
    fsCtx' G' p t x = ⟨G'.level - 1, [p.1],
      D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) x t, []⟩ := by
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  unfold fsCtx'
  rw [hnat.2.2.1 p, nativeChain_recenter, tc_material_symm hnat]

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
theorem fsAlg_level_pos' (hin : FirstSourceInput P Mn G G' depth CcT) :
    1 ≤ G'.level ∧ j₀ ≤ G'.level ∧ G'.level = G.level - 1 := by
  have hL : G'.level = G.level - 1 := hin.successor.2.1
  have := hin.stage.level
  omega

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The recentred actual context is admissible. -/
theorem fsAlg_ctx_adm' (hin : FirstSourceInput P Mn G G' depth CcT) (p : OddSlot) (t : ℝ) (x : Vec 2) :
    IsAdmissibleChain D b j₀ G'.level p.1 (fsCtx' G' p t x) := by
  obtain ⟨h1, h2, -⟩ := fsAlg_level_pos' hin
  rw [fsAlg_ctx_native' hin]
  exact nativeChain_isCarrier D b j₀ G'.level p.1 2 h1 h2 p.2 _

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The hypothesis of the strain step, read at the native context. -/
theorem fsAlg_strain_native' (hin : FirstSourceInput P Mn G G' depth CcT) (p : OddSlot) (t : ℝ)
    (hSS : ∀ Y : Vec 2, contextStrain D (G.level - 1) p.1 t ((G'.actual p).1.recenter D Y)
          ((D.eps (G.level - 1))⁻¹ • Y) =
        jacMatrix (streamVel (D.Φ (G.level - 1)) t)
          (((((G'.actual p).1.recenter D Y).geom D).1 t Y
            (((G'.actual p).1.recenter D Y).geom D).2.2))) (Y : Vec 2) :
    contextStrain D G'.level p.1 t ⟨G'.level - 1, [p.1], Y, []⟩ ((D.eps G'.level)⁻¹ • Y) =
      jacMatrix (streamVel (D.Φ G'.level) t)
        (D.flowOf (G'.level - 1) t Y (D.slotAnchor G'.level p.1)) := by
  obtain ⟨h1, -, hL⟩ := fsAlg_level_pos' hin
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  have := hSS Y
  rw [← hL, hnat.2.2.1 p, nativeChain_recenter, StrainPhysical.geom_native D _ h1] at this
  exact this

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- **The commutator flux of `firstSourceFlux` at the recentred actual context is that of the
physical velocity, translated to the centre `x`.** -/
theorem fsAlg_JH_rel' (hin : FirstSourceInput P Mn G G' depth CcT) (p : OddSlot) (t : ℝ) (x : Vec 2)
    (hSS : ∀ Y : Vec 2, contextStrain D (G.level - 1) p.1 t ((G'.actual p).1.recenter D Y)
          ((D.eps (G.level - 1))⁻¹ • Y) =
        jacMatrix (streamVel (D.Φ (G.level - 1)) t)
          (((((G'.actual p).1.recenter D Y).geom D).1 t Y
            (((G'.actual p).1.recenter D Y).geom D).2.2)))
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) :
    fsAlgJH' D G.level Hc t (fsCtx' G' p t x)
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) =
      commutatorFluxJH (fun y => streamVel (D.Φ (G.level - 1)) t (x + y)) Hc := by
  obtain ⟨h1, -, hL⟩ := fsAlg_level_pos' hin
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  have hS := fsAlg_strain_native' hin p t hSS
  funext g z
  unfold fsAlgJH' commutatorFluxJH
  have key : contextStrain D (G.level - 1) (fsCtx' G' p t x).slot t
      ((fsCtx' G' p t x).recenter D ((fsCtx' G' p t x).famMapInv D t z))
      ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x +
        (D.eps (G.level - 1))⁻¹ • (fsCtx' G' p t x).famMapInv D t z) =
      jacMatrix (fun y => streamVel (D.Φ (G.level - 1)) t (x + y)) z := by
    rw [← hL, tc_material_symm hnat, fsAlg_ctx_native' hin, StrainPhysical.recenter_native,
      ← smul_add]
    beta_reduce
    change contextStrain D G'.level p.1 t _ _ = _
    rw [hS, fsAlg_physPoint D h1 p.1 t x z]
    unfold jacMatrix
    ext a c
    simp only [Matrix.of_apply, fderiv_comp_add_left (f := streamVel (D.Φ G'.level) t)]
  rw [key]

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The three chart facts used by the unfolding: the centre is fixed, the pull-back of a
relabelled field is the translated field, the Piola factor cancels the Jacobian. -/
theorem fsAlg_chart_facts' (hin : FirstSourceInput P Mn G G' depth CcT) (p : OddSlot) (t : ℝ) (x : Vec 2)
    (f : Vec 2 → ℝ) :
    (fsCtx' G' p t x).famMap D t 0 = 0 ∧
    ((fun y => f (((G'.fam.piece p).material t) (((G'.fam.piece p).material t).symm x + y))) ∘
        (fsCtx' G' p t x).famMapInv D t) = (fun w => f (x + w)) ∧
    chartInvJacobian ⇑((G'.fam.piece p).material t).symm x *
      (jacMatrix ((fsCtx' G' p t x).famMap D t) 0)⁻¹ = 1 := by
  obtain ⟨h1, -, -⟩ := fsAlg_level_pos' hin
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  have hmat : ⇑((G'.fam.piece p).material t) =
      fun y => D.flowOf (G'.level - 1) t y (D.slotAnchor G'.level p.1) := by
    exact (hnat.1 p).2.2.2.2 t
  refine ⟨?_, ?_, ?_⟩
  · rw [fsAlg_ctx_native' hin, fsAlg_famMap_native D h1]
    simp
  · funext w
    simp only [Function.comp_apply]
    rw [tc_material_symm hnat, hmat, fsAlg_ctx_native' hin]
    beta_reduce
    rw [fsAlg_physPoint D h1 p.1 t x w]
  · rw [tc_material_symm hnat, fsAlg_ctx_native' hin]
    exact fsAlg_piola_cancel D h1 p.1 t x

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- **The Eulerian reading, unfolded.** Given the strain step, `fsEulerRead'` is `𝖰_p` of the
translated commutator sum plus the diagonal flux of `𝖯_p` of the translated field, at the centre. -/
theorem fsAlg_unfold' (hin : FirstSourceInput P Mn G G' depth CcT) (p : OddSlot) (t : ℝ) (x : Vec 2)
    (hSS : ∀ Y : Vec 2, contextStrain D (G.level - 1) p.1 t ((G'.actual p).1.recenter D Y)
          ((D.eps (G.level - 1))⁻¹ • Y) =
        jacMatrix (streamVel (D.Φ (G.level - 1)) t)
          (((((G'.actual p).1.recenter D Y).geom D).1 t Y
            (((G'.actual p).1.recenter D Y).geom D).2.2)))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (f : Vec 2 → ℝ) :
    fsEulerRead' Mn G G' Cc0 p t x f =
      covPolyQ (menuCovPrimitive D Mn G.level t) Mn.p (fun x' =>
        -(fsAlgSum' (menuCovPrimitive D Mn G.level t) Mn.p
            (commutatorFluxJH (fun y => streamVel (D.Φ (G.level - 1)) t (x + y))
              (menuCovPrimitive D Mn G.level t))
            (fun y => f (x + y)) x') +
          diagFluxCtx D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N Cc0 t
            (fsCtx' G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)
            (covPolyP (menuCovPrimitive D Mn G.level t) Mn.p (fun y => f (x + y))) x') 0 := by
  obtain ⟨h0, hU, hK⟩ := fsAlg_chart_facts' hin p t x f
  unfold fsEulerRead'
  simp only [fsAlg_ctx_adm' hin p t x, ↓reduceIte]
  unfold fsLabelOp'
  rw [fsAlg_firstSourceFlux_eq', fsAlg_JH_rel' hin p t x hSS, h0, hU, Matrix.mulVec_mulVec]
  rw [hK, Matrix.one_mulVec]
  rfl

end Generic

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
