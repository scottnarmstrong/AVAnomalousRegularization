-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetPoly
import AVRegularity.Construction.Preservation.Residual.KernelReadout.ClassicalComponent
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofFluxContinuityProduction
import AVRegularity.Proofs.GenSem.LiftOn.Omega
import AVRegularity.Proofs.GenSem.Jet.Chart
public import AVRegularity.Construction.Preservation.Ledger.ActualSourceSums
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Construction.Uniqueness.SuccessorFluxWindow
import AVRegularity.EntryWeak.MolecularHilbertToRawSolution
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup
import Mathlib.Algebra.Order.Star.Real

section
section
/-! The provenance reindexing of the retained readout flux `R = K - RO` (`RetainedReadoutReindexStatement`). `reindex_pointwise` is the identity at one time and place from
the data of a frame (the classical representatives of the retained solution and of its readout),
and `retainedReadoutReindex` is the statement under the quantifier prefix. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {P : ProvParams} {Mn : SuccMenu}
  {G G' : GenStage D hr Dm b j₀}

/-- **`R + RO = K` at one time and place**, from the classical representatives of the retained
solution and of its readout. -/
theorem reindex_pointwise (R : ReindexInput P Mn G G') (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    {H J Naux : ℕ} (hJ : J ≤ Mn.J) (hDm : Dm ≤ Naux) (E η : ℝ) (hE : 0 < E) (t : ℝ)
    (Y : ∀ c : CompIn (G'.retained G.level H J).comps, ℝ → TorusHk Naux (hr c.1.root))
    (aY : ℝ → Vec 2 → ∀ c : CompIn (G'.retained G.level H J).comps, hr c.1.root)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hY : ∀ c, IsClassicalRep (Y c t) (fun x => aY t x c) Naux)
    (hZ : ∀ v : CompIn G.comps, IsClassicalRep
      (succReadout G.level E η Naux (fun c => Y c t) v) (fun x => aZ t x v) Naux)
    (v : CompIn G.comps) (x : Vec 2) :
    readoutFlux G.level E η (fun _ => True)
        (fun v' s y => coeffFluxOn P seedK freshK φ₀ (G'.retained G.level H J) .kernel aY v' s y)
        v t x =
      rootReadout P seedK freshK φ₀ G G' .kernel G.level E η aZ v t x -
        readoutFlux G.level E η (fun c => ¬ IsRetained G.level H J c)
          (fun v' s y => omittedFluxClassical P seedK freshK φ₀ G' (G'.retained G.level H J) aY v' s y)
          v t x := by
  classical
  have hcs : HasCompactSupport φ₀ := Providers.hasCompactSupport_of_unitBall hφsupp
  have hsplit := reindex_readout_split (hr := hr) (S := G.comps) (S' := G'.comps) G.level E η
    (IsRetained G.level H J) (omittedFluxClassical P seedK freshK φ₀ G' (G'.retained G.level H J) aY)
    (fun v' s y => coeffFluxOn P seedK freshK φ₀ (G'.retained G.level H J) .kernel aY v' s y)
    (fun v' s y => reindex_coeffFlux_eq_omitted P seedK freshK φ₀ G' G.level H J aY v' s y) v t x
  have hmain := reindex_readout_eq R seedK freshK φ₀ hφs hφsupp (H := H) hJ E η hE t aY
    (fun c => (hY c).2.1.continuous) (fun c => (hY c).2.2.1)
    (fun c S => ((kernel_readout_kernel_classical_rep hφ₀ hφs hcs S t (Y c t)
      (fun x' => aY t x' c) (hY c)).2.1).of_le (by exact_mod_cast hDm))
    aZ (fun u => readout_representative_eq G.level E η (fun c => Y c t) (fun c x => aY t x c)
      (fun u x => aZ t x u) hY hZ u) v x
  rw [← hmain, ← hsplit]
  abel

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual
open AVRegularity.Construction.Preservation.Assembly FluxCancellation CovarianceTransport

/-- (a)+(d) The provenance reindexing of the retained readout flux with the omitted-row
correction, `R = K - RO` pointwise, under the quantifier prefix. -/
theorem retainedReadoutReindex (α s q : ℝ) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    RetainedReadoutReindexStatement α s q ζ := by
  classical
  refine ⟨128, le_rfl, fun Λ hΛ => ⟨1, one_pos, ?_⟩⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨kS, 1, 1, le_rfl, one_pos, fun kI _ => ⟨0, 0, fun CI Cw j₀ _ _ CQ Cpr => ⟨0, ?_⟩⟩⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  subst hlevel
  have haux := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hDm : succSchedD D₀ N p (H + 1) ≤ Naux := by omega
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hold := (InitialValue.cascade_invariant hseed.2.1 hcascade)
  have hnat := hG.1
  have hκ : 0 < D.κ (min G.level D.term) :=
    CycleReference.bandChain_pos (by omega) hζ hband (by rw [hterm]; exact min_le_right _ _)
  have hcs : 0 ≤ D.cellScaleSq G.level := by
    unfold OCData.cellScaleSq OCData.kap
    exact div_nonneg (sq_nonneg _) hκ.le
  let R : ReindexInput (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' :=
    { act := hactual
      W := Classical.choice (splitWitness_nonempty hactual)
      hold := fun c hc e he => ((hold c hc).1 e he)
      hE := Construction.Stream.ocEpsilon_pos hΛD
      hcs := hcs
      hτ := Construction.Stream.ocTau_pos hΛD
      hWin := Uniqueness.succWindowData_of_target (reindex_succ_window_data hζD _ G)
      hΩ := fun _ _ hA => ⟨Providers.GenSem.isOpen_ladderOmega _ _ _ _ _ _ _,
        Providers.GenSem.zero_mem_ladderOmega hζD hA _⟩
      hΦ := fun A t => ⟨(Providers.GenSem.contDiff_famMapInv A t).continuous.continuousAt,
        Providers.GenSem.famMapInv_zero hζD A t⟩ }
  intro v t htt x
  have hcs' : HasCompactSupport φ₀ := Providers.hasCompactSupport_of_unitBall hφsupport
  have key := reindex_pointwise R seedK freshK φ₀ hφ₀ hφsmooth hφsupport (H := H) (J := J)
    (Naux := Naux) (le_refl J) hDm (D.eps (G.level - 1)) (succEta0 α q s)
    (Construction.Stream.ocEpsilon_pos hΛD) t Y aY aZ (fun c => hY c t htt) (fun u => hZ u t htt) v x
  exact key

end AVRegularity.Construction.Preservation.Residual
end
end

section
/-! The continuity statement `RetainedReadoutFluxContinuityStatement`: `R`, `RO`,
`RD`, `Pl` are proved from the stage certificates (`ProofFluxContinuityProduction`); `N = Q_p G` is
the last clause of the regularity piece `CovarianceFluxRegularityStatement` at `g = aZ`, whose
hypotheses (`SplitInputOn`) come from the cascade input statement and whose smoothness is the
classical-representative clause of the frame. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual
open AVRegularity.Construction.Preservation.Assembly FluxCancellation CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **Continuity of `N`** from the regularity piece, on a frame with the split input. -/
theorem fluxContN_of_regularity (hreg : CovarianceFluxRegularityStatement)
    (F : Frame D hr Dm b j₀) (hin : SplitInputOn F) :
    ∀ v : CompIn F.G.comps, ∀ t ∈ Set.Icc F.tp F.tf, Continuous (fluxN F v t) := by
  obtain ⟨hlev, hN, hp, hη, hK, hI⟩ := hin
  intro v t ht
  have h := hreg F.P F.seedK F.freshK F.φ₀ F.Mn F.G F.G' F.depth F.CcT hI
    F.Naux (by rw [hN, hp]; exact hK) F.tp F.tf F.aZ
    (fun w s hs => ⟨(F.readout w s hs).2.1, (F.readout w s hs).2.2.1⟩) v t ht
  have h5 := h.2.2.2
  rw [hlev, hN, hp] at h5
  exact h5

/-- The frame statement from its parts. -/
theorem fluxContinuityOn_of_parts (hreg : CovarianceFluxRegularityStatement)
    (F : Frame D hr Dm b j₀) (hR : ContROn F) (hE : ContEOn F) (hin : SplitInputOn F) :
    FluxContinuityOn F := fun v t ht =>
  ⟨hR v t ht, (hE v t ht).1, (hE v t ht).2.1, (hE v t ht).2.2, fluxContN_of_regularity hreg F hin v t ht⟩

/-- **Spatial continuity of the five fluxes** under the quantifier prefix, from the regularity
piece and the cascade input. -/
theorem retainedReadoutFluxContinuity_of_pieces {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (hreg : CovarianceFluxRegularityStatement)
    (hinput : CascadeSplitInputStatement α s q ζ) :
    RetainedReadoutFluxContinuityStatement α s q ζ :=
  FluxCancellation.frame_production_map
    (FluxCancellation.frame_production_join
      (FluxCancellation.frame_production_join (fluxContR_production hα₀ hα₁ hs₀ hs₁ hq hζ)
        (fluxContE_production hα₀ hα₁ hs₀ hs₁ hq hζ)) hinput)
    (fun F h => fluxContinuityOn_of_parts hreg F h.1.1 h.1.2 h.2)

/-- **Spatial continuity of the five fluxes**, conditional only on the cascade split input (the flux-regularity step
is `covarianceFluxRegularity`). -/
theorem retainedReadoutFluxContinuity_of_input {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (hinput : CascadeSplitInputStatement α s q ζ) :
    RetainedReadoutFluxContinuityStatement α s q ζ :=
  retainedReadoutFluxContinuity_of_pieces hα₀ hα₁ hs₀ hs₁ hq hζ
    FluxCancellation.covarianceFluxRegularity hinput

end AVRegularity.Construction.Preservation.Residual
end
end
end

section
section
/-! **Source mean: the path means on the native families**: independence of the lift family and
vanishing in high degree.

At a time of the pulse window of an odd pulse `k`:

* `nativePathMean_lift_indep`: two lift families of the scalar path family of `π` give the same
  path mean on the native family of `k`, for every field and at every label: the lift sequence on
  the ladder is unique on the cell-time window (`lift_sequence_unique_window_on`, window data from
  `pcc_succ_window_data`), and the ladder of the native chain is all of `ℝ²`
  (`isAdmissibleChain_nativeChain_recenter`). So the lifts `W.Cc s` of the different sources `s` on
  one path (`copyQuad`, `letterMean`, `letterCov`) may be exchanged.
* `nativePathMean_high`: the path mean of degree `n > N + max 2 E` vanishes on smooth fields at
  every label, when the edges of the path vanish above `max 2 E` (`pathMeanFlux_high_eq_zero`).
* `dressedPathTerm_lift_indep`, `dressedPathTerm_high`: the same for the dressed terms (the
  covariance iterates of a smooth field are smooth; the covariance iterates of `0` are `0`).

For an even pulse, or a pulse whose native chain is not admissible, both path means are `0`;
for `a = a' = 0` the dressed term is the push of the path mean. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport Providers.QuietAtlas Providers.GenSem

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Every label is an admissible offset of the native chain. -/
theorem nativeLadder_mem {m : ℕ} (hm : 1 ≤ m) (hj : j₀ ≤ m) {k : ℤ} (hk : Odd k) (ρ : ℝ)
    (X : Vec 2) : X ∈ ladderOmega D b j₀ m k (nativeChain m k) ρ :=
  isAdmissibleChain_nativeChain_recenter hm hj ⟨k, hk⟩ (ρ • X)

/-- **The path mean on a native family does not depend on the lift family**, at a time of the
pulse window. -/
theorem nativePathMean_lift_indep (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (hm : 1 ≤ G.level) (hj : j₀ ≤ G.level) {h : ℕ} (π : StagePath G h)
    (Cc Cc' : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hC : (SuccSource.copyQuad [] h π).IsLiftFamily Mn Cc)
    (hC' : (SuccSource.copyQuad [] h π).IsLiftFamily Mn Cc') (n : ℕ) (k : ℤ) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) :
    nativePathMean Mn G π Cc n k t = nativePathMean Mn G π Cc' n k t := by
  by_cases hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k
  · rw [nativePathMean_pos Mn G π Cc n t hA, nativePathMean_pos Mn G π Cc' n t hA]
    have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
    have hΩ := isOpen_ladderOmega D b j₀ G.level k (nativeChain G.level k)
      (Mn.lenFactor * liftLength D G.level)
    have hag := Uniqueness.liftAgreeOn_of_window Mn hc.le (Construction.Stream.ocTau_pos hΛ)
      (Uniqueness.succWindowData_of_target (pcc_succ_window_data hζ Mn G))
      (SuccSource.copyQuad [] h π) Cc Cc' hC hC' k (nativeChain G.level k) hA hΩ
      ((D.cellScaleSq G.level)⁻¹ * t) (ccov_inv_mul_mem_window hc ht)
    funext f y
    exact Uniqueness.pathMeanFlux_eq_of_agreeOn D G.level _ _ _ _ n t hΩ hag f y
      (nativeLadder_mem hm hj hA.2 _ _)
  · rw [nativePathMean_neg Mn G π Cc n t hA, nativePathMean_neg Mn G π Cc' n t hA]

/-- **The path mean of degree `n > N + max 2 E` on a native family vanishes** on smooth fields, at
every label, at a time of the pulse window. -/
theorem nativePathMean_high (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (hm : 1 ≤ G.level) (hj : j₀ ≤ G.level) {h : ℕ} (π : StagePath G h)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hC : (SuccSource.copyQuad [] h π).IsLiftFamily Mn Cc) {E : ℕ}
    (hev : ∀ j, OrderBound.EdgeVanish G E (π.step j).2.2) (hsX : Dm ≤ Mn.sX) (hsZ : Dm ≤ Mn.sZ)
    {n : ℕ} (hn : Mn.N + max 2 E < n) (k : ℤ) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : Vec 2) :
    nativePathMean Mn G π Cc n k t f y = 0 := by
  by_cases hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k
  · rw [nativePathMean_pos Mn G π Cc n t hA]
    exact OrderBound.pathMeanFlux_high_eq_zero hΛ hζ hκ π hev k hA.2 hA.1 _ hsX hsZ
      (Cc k (nativeChain G.level k)) (hC k (nativeChain G.level k) hA) ht hn hf
      (nativeLadder_mem hm hj hA.2 _ _)
  · rw [nativePathMean_neg Mn G π Cc n t hA]

/-- The dressed term does not depend on the lift family, at a time of the pulse window. -/
theorem dressedPathTerm_lift_indep (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (hm : 1 ≤ G.level) (hj : j₀ ≤ G.level) {h : ℕ} (π : StagePath G h)
    (Cc Cc' : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hC : (SuccSource.copyQuad [] h π).IsLiftFamily Mn Cc)
    (hC' : (SuccSource.copyQuad [] h π).IsLiftFamily Mn Cc') (n a a' : ℕ) (k : ℤ) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) (φ : Vec 2 → ℝ) (x : Vec 2) :
    dressedPathTerm Mn G π Cc n a a' k t φ x = dressedPathTerm Mn G π Cc' n a a' k t φ x := by
  unfold dressedPathTerm
  rw [nativePathMean_lift_indep hΛ hζ hκ Mn G hm hj π Cc Cc' hC hC' n k ht]

/-- The dressed term of degree `n > N + max 2 E` vanishes on smooth fields, at a time of the pulse
window. -/
theorem dressedPathTerm_high (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (hm : 1 ≤ G.level) (hj : j₀ ≤ G.level) {h : ℕ} (π : StagePath G h)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hC : (SuccSource.copyQuad [] h π).IsLiftFamily Mn Cc) {E : ℕ}
    (hev : ∀ j, OrderBound.EdgeVanish G E (π.step j).2.2) (hsX : Dm ≤ Mn.sX) (hsZ : Dm ≤ Mn.sZ)
    {n : ℕ} (hn : Mn.N + max 2 E < n) (a a' : ℕ) (k : ℤ) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) {φ : Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec 2) :
    dressedPathTerm Mn G π Cc n a a' k t φ x = 0 := by
  have htop : ∀ r : ℕ, ((r : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun r => by
    exact_mod_cast le_top
  have hg : ContDiff ℝ (⊤ : ℕ∞) ((SuccSource.covAt D G.level Mn.anchor t)^[a'] φ) := by
    rw [contDiff_infty]
    intro r
    exact contDiff_covOperator_iterate _ a' (hφ.of_le (htop _))
  have e : pushFlux (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level k))
      (fun x' => D.flowOf (G.level - 1) (D.slotAnchor G.level k) x' t)
      (nativePathMean Mn G π Cc n k t) ((SuccSource.covAt D G.level Mn.anchor t)^[a'] φ) =
      fun _ => 0 := by
    funext x'
    unfold pushFlux
    rw [nativePathMean_high hΛ hζ hκ Mn G hm hj π Cc hC hev hsX hsZ hn k ht
      (hg.comp (flowOf_contDiff D (G.level - 1) t (D.slotAnchor G.level k))) _]
    exact Matrix.mulVec_zero _
  unfold dressedPathTerm SuccSource.covAtFlux
  rw [e, ccfo_covOperator_iterate_zero, smul_zero]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, step 1, part B: the dimensional flux of the first-source identity at a piece is
`lam • fsPieceArray`, and the algebra of `transportedCoeff` and the root casts. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- `transportedCoeff` is homogeneous in the array. -/
theorem fs_transportedCoeff_smul (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (c : ℝ) (r : ℕ) (A : DerivativeWord2 r)
    (y : Vec 2) (κ : Fin 2) :
    transportedCoeff K Dγ (fun d I => c • B d I) r A y κ = c * transportedCoeff K Dγ B r A y κ := by
  unfold transportedCoeff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The dimensional flux of the first-source identity at a piece. -/
theorem fs_dimFlux_eq {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    {depth : ℕ} {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : SplitInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G')
    (v1 u1 : CompIn G'.comps) (γ0 : G'.fam.Γ v1 u1) (hdiag : (W.e v1 u1 γ0).1.IsDiag)
    (p : OddSlot) (t : ℝ) (x : Vec 2) {d : ℕ} (hd : 2 ≤ d) (I : DerivativeWord2 (d - 1)) :
    G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1)) p (G'.actual p)
        v1 u1 γ0 d I t (((G'.fam.piece p).material t).symm x)
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) =
      (W.e v1 u1 γ0).1.lam G.level Mn.η0 • fsPieceArray Mn G G' W.Cc0 p t x d I := by
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
  unfold fsPieceArray
  by_cases hadm : IsAdmissibleChain D b j₀ G'.level p.1
      ((G'.actual p).1.recenter D (((G'.fam.piece p).material t).symm x))
  · simp only [hadm, ↓reduceIte, smul_smul, hkk]
    rw [← hkk]
    congr 1
    field_simp
  · simp [hadm]

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The identity root map applied to a vector. -/
theorem fs_rootPathMap_nil_apply {a b : ℕ} (h : a = b) (w : hr a) :
    rootPathMap hr a [] b w = h ▸ w := by
  subst h; simp [rootPathMap]

omit [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- A cast of a `PiLp` whose components are transports is the untransported `PiLp`. -/
theorem fs_cast_of_eqrec {a b : ℕ} (h : a = b) (e : b = a)
    (y : PiLp 2 (fun _ : Fin 2 => hr b)) (z : Fin 2 → hr a) (hyz : ∀ κ, y κ = h ▸ z κ) :
    cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) y = WithLp.toLp 2 z := by
  subst h
  simp only [cast_eq]
  ext κ
  exact hyz κ

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The source-mean step, the sum over the sources by kind**.

`finsum_succSource_split`: a function on the sources of a stage which vanishes off the empty word,
on the first source, and off finite ranges of the grades, degrees and covariance orders, has the
`finsum` of its values on the four kinds of sources with a path or an identity: the direct
transports (identities of the stage), the quadratic conversions (grades and paths), the letters
`𝖬_{n,h}` (degrees, grades, paths) and the letters `𝖵_{n,h,a,a'}`.

For a stage without identities every sum is empty, and for `hTop = 0` only the direct
transports remain. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport Construction.Preservation.Ledger

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- **The sum over the sources with the empty word, by kind.** -/
theorem finsum_succSource_split {M : Type*} [AddCommMonoid M] (G : GenStage D hr Dm b j₀)
    (F : SuccSource G → M) (nMax hTop p : ℕ)
    (hw : ∀ s : SuccSource G, s.word ≠ [] → F s = 0)
    (hdiag : ∀ u, F (SuccSource.letterDiag [] u) = 0)
    (hquad : ∀ h (π : StagePath G h), h ∉ Finset.Icc 1 hTop → F (SuccSource.copyQuad [] h π) = 0)
    (hmean : ∀ n h (π : StagePath G h), ¬ (n ∈ Finset.Icc 3 nMax ∧ h ∈ Finset.Icc 1 hTop) →
      F (SuccSource.letterMean [] n h π) = 0)
    (hcov : ∀ n h a a' (π : StagePath G h),
      ¬ (n ∈ Finset.Icc 2 nMax ∧ a ∈ Finset.range (p + 1) ∧ a' ∈ Finset.range (p + 1) ∧
        h ∈ Finset.Icc 1 hTop) → F (SuccSource.letterCov [] n h a a' π) = 0) :
    ∑ᶠ s, F s =
      (∑ x : (Σ v u : CompIn G.comps, G.fam.Γ v u), F (SuccSource.copyDir [] x.1 x.2.1 x.2.2)) +
      (∑ h ∈ Finset.Icc 1 hTop, ∑ π : StagePath G h, F (SuccSource.copyQuad [] h π)) +
      (∑ n ∈ Finset.Icc 3 nMax, ∑ h ∈ Finset.Icc 1 hTop, ∑ π : StagePath G h,
        F (SuccSource.letterMean [] n h π)) +
      (∑ n ∈ Finset.Icc 2 nMax, ∑ a ∈ Finset.range (p + 1), ∑ a' ∈ Finset.range (p + 1),
        ∑ h ∈ Finset.Icc 1 hTop, ∑ π : StagePath G h, F (SuccSource.letterCov [] n h a a' π)) := by
  set P : Finset (Σ h : ℕ, StagePath G h) :=
    (Finset.Icc 1 hTop).sigma (fun h => (Finset.univ : Finset (StagePath G h))) with hP
  set f1 : (Σ v u : CompIn G.comps, G.fam.Γ v u) → SuccSource G :=
    fun x => SuccSource.copyDir [] x.1 x.2.1 x.2.2 with hf1
  set f2 : (Σ h : ℕ, StagePath G h) → SuccSource G := fun x => SuccSource.copyQuad [] x.1 x.2
    with hf2
  set f3 : ℕ × (Σ h : ℕ, StagePath G h) → SuccSource G :=
    fun x => SuccSource.letterMean [] x.1 x.2.1 x.2.2 with hf3
  set f4 : ℕ × ℕ × ℕ × (Σ h : ℕ, StagePath G h) → SuccSource G :=
    fun x => SuccSource.letterCov [] x.1 x.2.2.2.1 x.2.1 x.2.2.1 x.2.2.2.2 with hf4
  have i1 : Function.Injective f1 := by
    rintro ⟨v, u, γ⟩ ⟨v', u', γ'⟩ h
    simp only [hf1, SuccSource.copyDir.injEq, true_and] at h
    obtain ⟨rfl, rfl, h⟩ := h
    rw [eq_of_heq h]
  have i2 : Function.Injective f2 := by
    rintro ⟨h, π⟩ ⟨h', π'⟩ e
    simp only [hf2, SuccSource.copyQuad.injEq, true_and] at e
    obtain ⟨rfl, e⟩ := e
    rw [eq_of_heq e]
  have i3 : Function.Injective f3 := by
    rintro ⟨n, h, π⟩ ⟨n', h', π'⟩ e
    simp only [hf3, SuccSource.letterMean.injEq, true_and] at e
    obtain ⟨rfl, rfl, e⟩ := e
    rw [eq_of_heq e]
  have i4 : Function.Injective f4 := by
    rintro ⟨n, a, a', h, π⟩ ⟨n', b, b', h', π'⟩ e
    simp only [hf4, SuccSource.letterCov.injEq, true_and] at e
    obtain ⟨rfl, rfl, rfl, rfl, e⟩ := e
    rw [eq_of_heq e]
  set T1 : Finset (SuccSource G) := Finset.univ.image f1 with hT1
  set T2 : Finset (SuccSource G) := P.image f2 with hT2
  set T3 : Finset (SuccSource G) := (Finset.Icc 3 nMax ×ˢ P).image f3 with hT3
  set T4 : Finset (SuccSource G) :=
    (Finset.Icc 2 nMax ×ˢ Finset.range (p + 1) ×ˢ Finset.range (p + 1) ×ˢ P).image f4 with hT4
  have hsupp : Function.support F ⊆ ↑(T1 ∪ T2 ∪ T3 ∪ T4) := by
    intro s hs
    have hs' : F s ≠ 0 := hs
    have hword : s.word = [] := by
      by_contra h
      exact hs' (hw s h)
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    cases s with
    | copyDir t v u γ =>
      have ht : t = [] := hword
      subst ht
      exact Or.inl (Or.inl (Or.inl (Finset.mem_image.2 ⟨⟨v, u, γ⟩, Finset.mem_univ _, rfl⟩)))
    | copyQuad t h π =>
      have ht : t = [] := hword
      subst ht
      have hh : h ∈ Finset.Icc 1 hTop := by
        by_contra hn
        exact hs' (hquad h π hn)
      exact Or.inl (Or.inl (Or.inr (Finset.mem_image.2
        ⟨⟨h, π⟩, Finset.mem_sigma.2 ⟨hh, Finset.mem_univ _⟩, rfl⟩)))
    | letterDiag t u =>
      have ht : t = [] := hword
      subst ht
      exact absurd (hdiag u) hs'
    | letterMean t n h π =>
      have ht : t = [] := hword
      subst ht
      have hh : n ∈ Finset.Icc 3 nMax ∧ h ∈ Finset.Icc 1 hTop := by
        by_contra hn
        exact hs' (hmean n h π hn)
      exact Or.inl (Or.inr (Finset.mem_image.2 ⟨⟨n, h, π⟩,
        Finset.mem_product.2 ⟨hh.1, Finset.mem_sigma.2 ⟨hh.2, Finset.mem_univ _⟩⟩, rfl⟩))
    | letterCov t n h a a' π =>
      have ht : t = [] := hword
      subst ht
      have hh : n ∈ Finset.Icc 2 nMax ∧ a ∈ Finset.range (p + 1) ∧
          a' ∈ Finset.range (p + 1) ∧ h ∈ Finset.Icc 1 hTop := by
        by_contra hn
        exact hs' (hcov n h a a' π hn)
      exact Or.inr (Finset.mem_image.2 ⟨⟨n, a, a', h, π⟩,
        Finset.mem_product.2 ⟨hh.1, Finset.mem_product.2 ⟨hh.2.1, Finset.mem_product.2
          ⟨hh.2.2.1, Finset.mem_sigma.2 ⟨hh.2.2.2, Finset.mem_univ _⟩⟩⟩⟩, rfl⟩)
  have d12 : Disjoint T1 T2 := by
    rw [Finset.disjoint_left]
    intro s h1 h2
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨y, -, e⟩ := Finset.mem_image.1 h2
    simp [hf1, hf2] at e
  have d123 : Disjoint (T1 ∪ T2) T3 := by
    rw [Finset.disjoint_left]
    intro s h1 h2
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 h2
    rcases Finset.mem_union.1 h1 with h1 | h1
    · obtain ⟨x, -, e⟩ := Finset.mem_image.1 h1
      simp [hf1, hf3] at e
    · obtain ⟨x, -, e⟩ := Finset.mem_image.1 h1
      simp [hf2, hf3] at e
  have d1234 : Disjoint (T1 ∪ T2 ∪ T3) T4 := by
    rw [Finset.disjoint_left]
    intro s h1 h2
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 h2
    rcases Finset.mem_union.1 h1 with h1 | h1
    · rcases Finset.mem_union.1 h1 with h1 | h1
      · obtain ⟨x, -, e⟩ := Finset.mem_image.1 h1
        simp [hf1, hf4] at e
      · obtain ⟨x, -, e⟩ := Finset.mem_image.1 h1
        simp [hf2, hf4] at e
    · obtain ⟨x, -, e⟩ := Finset.mem_image.1 h1
      simp [hf3, hf4] at e
  rw [finsum_eq_sum_of_support_subset F hsupp, Finset.sum_union d1234, Finset.sum_union d123,
    Finset.sum_union d12, hT1, hT2, hT3, hT4, Finset.sum_image (fun x _ y _ h => i1 h),
    Finset.sum_image (fun x _ y _ h => i2 h), Finset.sum_image (fun x _ y _ h => i3 h),
    Finset.sum_image (fun x _ y _ h => i4 h), Finset.sum_product, hP]
  simp only [Finset.sum_product, Finset.sum_sigma]
  rfl

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The source-mean step, the alphabet and the direct parts**.

* `mean_mem_succAlphabet`, `covariance_mem_succAlphabet`: the letters `𝖬_{n,h}` and `𝖵_{n,h,a,a'}`
  of the padded alphabet (`3 ≤ n ≤ nMax`, resp. `2 ≤ n ≤ nMax`, `a, a' ≤ p`, `1 ≤ a + a'`;
  `1 ≤ h ≤ hMax`).
* `nativeDirect_sum`: the direct part of the orders `ords` is the sum of its orders;
  `nativeDirect_Icc_eq`: for an identity whose arrays vanish above `Dord ≤ nMax`, the direct parts
  of the orders `3..nMax` (subtracted in the letters `𝖬_{n,1}`) add up to the direct part of the
  orders `3..Dm` (the direct transport), provided `nMax ≤ Dm` or `nMax < 3`;
  `nativeDirect_eq_zero_of_maxOrder`: an identity of maximal order below `3` has no direct part of
  the orders `≥ 3`.
* `gluedFluxOp_sum`: the Eulerian glue is additive in the label operators.

For `nMax < 3` there is no letter `𝖬` and the direct transport vanishes, its arrays being zero
above `Dord ≤ nMax < 3`; for `Dm < 3` both sides are empty sums. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-! ### The letters of the padded alphabet -/

theorem mean_mem_succAlphabet {nMax hMax p npad n h : ℕ} :
    WordLetter.mean n h ∈ succAlphabet nMax hMax p npad ↔
      n ∈ Finset.Icc 3 nMax ∧ h ∈ Finset.Icc 1 hMax := by
  simp only [succAlphabet, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_product, Finset.mem_filter, Finset.mem_range, reduceCtorEq, false_or, or_false,
    WordLetter.mean.injEq, Prod.exists, and_false, exists_false]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl, rfl⟩
    exact ⟨ha, hb⟩
  · rintro ⟨h1, h2⟩
    exact ⟨n, h, ⟨h1, h2⟩, rfl, rfl⟩

theorem covariance_mem_succAlphabet {nMax hMax p npad n h a a' : ℕ} :
    WordLetter.covariance n h a a' ∈ succAlphabet nMax hMax p npad ↔
      (n ∈ Finset.Icc 2 nMax ∧ h ∈ Finset.Icc 1 hMax) ∧ (a < p + 1 ∧ a' < p + 1) ∧
        1 ≤ a + a' := by
  simp only [succAlphabet, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_product, Finset.mem_filter, Finset.mem_range, reduceCtorEq, false_or, or_false,
    WordLetter.covariance.injEq, Prod.exists, and_false, exists_false]
  constructor
  · rintro ⟨n', h', b, b', ⟨⟨⟨hn, hh⟩, hb, hb'⟩, hs⟩, rfl, rfl, rfl, rfl⟩
    exact ⟨⟨hn, hh⟩, ⟨hb, hb'⟩, hs⟩
  · rintro ⟨⟨hn, hh⟩, ⟨ha, ha'⟩, hs⟩
    exact ⟨n, h, a, a', ⟨⟨⟨hn, hh⟩, ha, ha'⟩, hs⟩, rfl, rfl, rfl, rfl⟩

/-! ### The glue is additive -/

theorem gluedFluxOp_sum (D : OCData) (m : ℕ) {κ : Type*} (S : Finset κ)
    (L : κ → ℤ → (Vec 2 → ℝ) → Vec 2 → Vec 2) (t : ℝ) (f : Vec 2 → ℝ) (x : Vec 2) :
    gluedFluxOp D m (fun k g y => ∑ i ∈ S, L i k g y) t f x =
      ∑ i ∈ S, gluedFluxOp D m (L i) t f x := by
  unfold gluedFluxOp pushFlux
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_sum, Finset.smul_sum]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-! ### The direct parts -/

/-- The direct part of the orders `ords` is the sum of the direct parts of its orders. -/
theorem nativeDirect_sum (G : GenStage D hr Dm b j₀) {v u : CompIn G.comps} (γ : G.fam.Γ v u)
    (ords : Finset ℕ) (k : ℤ) (t : ℝ) (f : Vec 2 → ℝ) (y : Vec 2) :
    nativeDirect G γ ords k t f y = ∑ d ∈ ords, nativeDirect G γ {d} k t f y := by
  by_cases hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k
  · rw [nativeDirect_pos G γ ords t hA]
    simp only [nativeDirect_pos G γ _ t hA]
    unfold directFlux
    simp only [Finset.sum_singleton]
  · rw [nativeDirect_neg G γ ords t hA]
    simp only [nativeDirect_neg G γ _ t hA, Finset.sum_const_zero]

/-- The direct part of an order whose arrays vanish is zero. -/
theorem nativeDirect_singleton_eq_zero (G : GenStage D hr Dm b j₀) {v u : CompIn G.comps}
    (γ : G.fam.Γ v u) (d : ℕ)
    (hz : ∀ (p : OddSlot) (c : StageCtx D b j₀ G.level p) (α : DerivativeWord2 (d - 1)),
      G.fam.flux p c v u γ d α = fun _ _ _ => 0) (k : ℤ) (t : ℝ) (f : Vec 2 → ℝ) (y : Vec 2) :
    nativeDirect G γ {d} k t f y = 0 := by
  by_cases hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k
  · rw [nativeDirect_pos G γ _ t hA]
    exact OrderBound.directFlux_singleton_eq_zero G _ _ γ d (fun α => hz _ _ α) t f y
  · rw [nativeDirect_neg G γ _ t hA]

/-- **The direct parts of the orders `3..nMax` add up to the direct part of the orders `3..Dm`**,
for an identity whose arrays vanish above `Dord ≤ nMax`. -/
theorem nativeDirect_Icc_eq (G : GenStage D hr Dm b j₀) {v u : CompIn G.comps} (γ : G.fam.Γ v u)
    {Dord nMax : ℕ}
    (hvan : ∀ (p : OddSlot) (c : StageCtx D b j₀ G.level p) (d : ℕ)
      (I : DerivativeWord2 (d - 1)), Dord < d → G.fam.flux p c v u γ d I = fun _ _ _ => 0)
    (hD : Dord ≤ nMax) (hsub : ∀ d ∈ Finset.Icc 3 nMax, d ≤ Dm) (k : ℤ) (t : ℝ)
    (f : Vec 2 → ℝ) (y : Vec 2) :
    ∑ n ∈ Finset.Icc 3 nMax, nativeDirect G γ {n} k t f y =
      nativeDirect G γ (Finset.Icc 3 Dm) k t f y := by
  rw [nativeDirect_sum G γ (Finset.Icc 3 Dm)]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    have h1 := Finset.mem_Icc.1 hd
    exact Finset.mem_Icc.2 ⟨h1.1, hsub d hd⟩
  · intro d hd hnd
    have h1 := Finset.mem_Icc.1 hd
    have h2 : nMax < d := by
      by_contra hc
      exact hnd (Finset.mem_Icc.2 ⟨h1.1, by omega⟩)
    exact nativeDirect_singleton_eq_zero G γ d (fun p c α => hvan p c d α (by omega)) k t f y

/-- An identity of maximal order below `3` has no direct part of the orders `≥ 3`. -/
theorem nativeDirect_eq_zero_of_maxOrder (G : GenStage D hr Dm b j₀) {v u : CompIn G.comps}
    (γ : G.fam.Γ v u) (hγ : (G.fam.identity v u γ).maxOrder < 3) (ords : Finset ℕ)
    (hords : ∀ d ∈ ords, 3 ≤ d) (k : ℤ) (t : ℝ) (f : Vec 2 → ℝ) (y : Vec 2) :
    nativeDirect G γ ords k t f y = 0 := by
  rw [nativeDirect_sum G γ ords]
  refine Finset.sum_eq_zero fun d hd => ?_
  have h3 := hords d hd
  exact nativeDirect_singleton_eq_zero G γ d
    (fun p c α => G.fam.flux_zero p c v u γ d α (fun h => by omega)) k t f y

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end
