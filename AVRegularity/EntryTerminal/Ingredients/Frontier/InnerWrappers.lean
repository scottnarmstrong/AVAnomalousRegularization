-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerStatements
import AVRegularity.Construction.Preservation.Frontier.MarkerReadout.Producer
public import AVRegularity.EntryTerminal.Ingredients.CoarseFamily.CoarseFamily
import AVRegularity.EntryTerminal.Ingredients.PrepInterp.PrepInterp
public import AVRegularity.Construction.Residual.Presentation.FluxAe
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.KernelDefect.UniformDefect
import AVRegularity.CycleComparison.Reconstruction.PartitionBound
import AVRegularity.Construction.Preservation.Frontier.LengthPrice.Producer
public import AVRegularity.Construction.Preservation.Frontier.LengthRows.Producer
import AVRegularity.EntryTerminal.Ingredients.SeedCert.SeedCertPart
import AVRegularity.EntryTerminal.Ingredients.SeedQuiet.Proof
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
public import AVRegularity.EntryTerminal.Ingredients.SeedCert.MenuFieldsStmt

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Frontier
namespace AVRegularity.Construction.Residual.Presentation

/-! **The marker readout at the terminal frame.**

`termInnerMarkerAt_of_ctx`: the cascade's `marker_readout_of_profile` at the terminal `Frame`
(length rows: the marker of every row is `1` since `ι = 0`; the old components have no births;
`Gt'.comps = succExtComps M A R_T Gw.comps`). The constant is
`#(wordsUpTo A (R_T + 1)) + 1`. It needs `lawT.cH ≤ 1` and `1 ≤ M` as hypotheses: `cH ≤ 1` is
`cHP ≤ 1`, which no premise of `TermResPrefix` gives.

For `R_T = 0` only the one-letter words occur, and for an empty weak family there are no rows. -/

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The marker readout estimate for length rows is monotone in the constant. -/
theorem markerReadout_mono (F : Frame D hr Dm bw j₀) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    {C C' : ℝ} (h0 : 0 ≤ C) (h : C ≤ C') (hM : MarkerReadoutStatement F false C) :
    MarkerReadoutStatement F false C' := by
  intro OF hOF hOFlp
  obtain ⟨RF, hRF, hlp, hpt⟩ := hM OF hOF hOFlp
  refine ⟨RF, hRF, hlp, fun t ht => (hpt t ht).trans ?_⟩
  have hg : (0 : ℝ) ≤ F.markerGain false := by
    simp only [Frame.markerGain, Bool.false_eq_true, ite_false]; exact zero_le_one
  have hσ : ∀ c : CompIn F.G'.comps, 0 < F.G'.mass F.law c / F.G'.marker F.law c ^ 2 := fun c =>
    div_pos (Construction.Preservation.Buffer.birth_compMass_pos hq hΛ F.law c.1)
      (pow_pos (Construction.Preservation.Buffer.birth_compMarker_pos hq hΛ F.law c.1) 2)
  refine mul_le_mul_of_nonneg_right ?_ (CoupledEnergy.Variational.massNormSq_nonneg _ _ hσ _)
  exact pow_le_pow_left₀ (mul_nonneg h0 hg) (mul_le_mul_of_nonneg_right h hg) 2

end Generic

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- `0 < η₀` from the validity of the arguments. -/
theorem termValid_eta0_pos (hV : A.Valid) : 0 < A.η₀ := by
  obtain ⟨-, -, -, ⟨-, -, -, -, -, -, -, hη, -⟩, -⟩ := hV
  exact hη

/-- **The marker readout at the terminal frame**, from the cascade's profile lemma. -/
theorem termInnerMarkerAt_of_ctx (hΛ128 : 128 ≤ A.Λ) (hV : A.Valid) (hM1 : 1 ≤ M)
    (hcH : c.lawT.cH ≤ 1) (kc : ℕ) {C : ℝ}
    (hC : ((wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) (A.RT + 1)).card : ℝ) + 1 ≤ C) :
    TermInnerMarkerAt c kc C := by
  intro yom _
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := c.data
  have hΛD : 128 ≤ c.D.Λ := hDΛ ▸ hΛ128
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hη := termValid_eta0_pos hV
  have hroots : ∀ x ∈ c.Gw.comps, x.births = [] := fun x hx => c.weak.2.2.2.2.1 ⟨x, hx⟩
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have hsub : c.Gt'.comps ⊆ succExtComps M (termAlphabet A.NT A.pT A.DW A.dW) A.RT c.Gw.comps := by
    have h1 := c.succ.2.2.1
    rw [hlev] at h1
    exact h1.subset
  have hmark : ∀ v : CompIn c.Gt'.comps, (compMarker c.D.q c.D.Λ c.lawT v.1)⁻¹ ≤ 1 := by
    intro v
    simp only [compMarker, c.law.2.2.2.1, neg_zero, Real.rpow_zero, Finset.prod_const_one, inv_one,
      le_refl]
  have hbase : MarkerReadoutStatement (termFrame c kc yom) false
      (((wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) (A.RT + 1)).card : ℝ) + 1) :=
    marker_readout_of_profile (termFrame c kc yom) hq1 hΛD hM1 hcH
      (show 0 ≤ c.lawT.etaB by rw [c.law.2.2.2.2.2.1]; linarith) hη.le (termAlphabet A.NT A.pT A.DW A.dW)
      (fun v hv e he => by rw [hroots v hv] at he; simp at he) hsub false
      (fun v _ => by
        simp only [Frame.markerGain, Bool.false_eq_true, ite_false]
        exact hmark v)
  exact markerReadout_mono (termFrame c kc yom) hq1 hΛD (by positivity) hC hbase

end Terminal

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route AVRegularity.EntryTerminal.Ingredients
open AVRegularity.Construction.Preservation.Frontier
namespace AVRegularity.Construction.Residual.Presentation

/-! **The energy of the coarse family**: `TermInnerInitialStatement`.

The initial value of the retained system at the order `k_c + 2p_T` is the truncation of the trace
`Z₀` of the paired solution `V(a_M)` after `P_term`; its weighted norm in `ρ`, with the masses of
the weak roots (the retained masses on old components agree by `IsTerminalLaw`, the markers are `1`
since `ι = 0`), is bounded by the first clause of `c.prepB`.

For an empty weak family `Y₀ = 0`, and likewise for `f = 0`. -/

theorem truncTo_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] {K : ℕ} (k : ℕ) : truncTo k (0 : TorusHk K E) = 0 := by
  unfold truncTo
  split_ifs
  · exact map_zero _
  · rfl

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The initial value of the retained system is the truncated trace. -/
theorem termY0_eq_trace (kc : ℕ) :
    termY0 c kc = terminalTrace c.Gw (c.Gt'.retained M 1 A.RT)
      (fun v => truncTo (kc + 2 * A.pT) (c.Pterm (fun v => c.V v c.aM) v)) := by
  funext v'
  unfold termY0 terminalTrace
  by_cases hv : v'.1 ∈ c.Gw.comps
  · simp only [hv, dite_true, c.trace.1 v' hv]
  · simp only [hv, dite_false, c.trace.2 v' hv, truncTo_zero]

/-- The retained masses of the old components are the weak masses. -/
theorem termRetained_mass (v' : CompIn (c.Gt'.retained M 1 A.RT).comps) (hv : v'.1 ∈ c.Gw.comps) :
    (c.Gt'.retained M 1 A.RT).mass c.lawT v' = c.Gw.mass c.lawW ⟨v'.1, hv⟩ := by
  have hb : v'.1.births = [] := c.weak.2.2.2.2.1 ⟨v'.1, hv⟩
  simp only [GenStage.mass, compMass, hb, List.map_nil, List.prod_nil, mul_one]
  rw [c.law.1]

/-- The markers of the terminal law are `1`. -/
theorem termRetained_marker : (c.Gt'.retained M 1 A.RT).marker c.lawT = fun _ => 1 := by
  funext v
  simp only [GenStage.marker, compMarker, c.law.2.2.2.1, neg_zero, Real.rpow_zero,
    Finset.prod_const_one]

/-- **The energy of the coarse family at a context**, from the first clause of `c.prepB`. -/
theorem termInnerInitialAt_of_ctx (hΛ128 : 128 ≤ A.Λ) (kc : ℕ)
    (hk : kc + 2 * A.pT ≤ A.Khat Kout) {C : ℝ} (hC : CP ≤ C) : TermInnerInitialAt c kc C := by
  intro yom
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := c.data
  have hΛD : 128 ≤ c.D.Λ := hDΛ ▸ hΛ128
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hpos : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD c.lawW v.1
  have h1 : (termFrame c kc yom).initialNorm =
      weightedNorm (rhoEnh c.D cr M) ((c.Gt'.retained M 1 A.RT).mass c.lawT) (fun _ => 1)
        (terminalTrace c.Gw (c.Gt'.retained M 1 A.RT)
          (fun v => truncTo (kc + 2 * A.pT) (c.Pterm (fun v => c.V v c.aM) v))) := by
    show weightedNorm _ _ ((c.Gt'.retained M 1 A.RT).marker c.lawT) (termY0 c kc) = _
    rw [termRetained_marker, termY0_eq_trace]
    rfl
  have h2 := terminalTrace_weightedNorm_le c.Gw (c.Gt'.retained M 1 A.RT) c.lawW c.lawT
    (rhoEnh c.D cr M)
    (fun v => truncTo (kc + 2 * A.pT) (c.Pterm (fun v => c.V v c.aM) v))
    (fun v' hv => termRetained_mass c v' hv) (fun v => (hpos v).le)
  have h3 : weightedNorm (rhoEnh c.D cr M) (c.Gw.mass c.lawW) (fun _ => 1)
      (fun v => truncTo (kc + 2 * A.pT) (c.Pterm (fun v => c.V v c.aM) v)) ≤
      weightedNorm (rhoEnh c.D cr M) (c.Gw.mass c.lawW) (fun _ => 1)
        (c.Pterm (fun v => c.V v c.aM)) := by
    have := weightedNorm_truncate_le hk (rhoEnh c.D cr M) (c.Gw.mass c.lawW) hpos
      (c.Pterm (fun v => c.V v c.aM))
    simpa only [truncTo_of_le hk] using this
  have h4 := c.prepB.1
  have h5 : 0 ≤ c.normF := Real.sqrt_nonneg _
  calc (termFrame c kc yom).initialNorm ≤ _ := h1.le.trans (h2.trans h3)
    _ ≤ CP * c.normF := h4
    _ ≤ C * c.normF := mul_le_mul_of_nonneg_right hC h5

/-- **`TermInnerInitialStatement`.** -/
theorem termInnerInitial : TermInnerInitialStatement := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ _ => ?_⟩
  refine ⟨0, fun kc _ => ?_⟩
  refine ⟨0, 0, kc + 2 * A.pT, fun sXT sZT _ _ Kout hK => ?_⟩
  refine ⟨0, ?_⟩
  intro Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm
    cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP Cfl
  refine ⟨max CP 0, 1, 0, one_pos, 1, 1, le_rfl, one_pos, ?_⟩
  intro C hC j₀ hj₀
  refine ⟨0, fun M _ c x => ?_⟩
  exact termInnerInitialAt_of_ctx c hΛ kc (hK.trans (le_max_left _ _)) ((le_max_left _ _).trans hC)

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
namespace AVRegularity.Construction.Residual.Presentation

/-! **`TermInnerIdentStatement`, proved**: the generic identification
`omittedFlux_ae_eq_classical` instantiated at the terminal context, with the kernel-lifted
edge inputs built from the truncations of `Z` (not of `Z_w`, which is tied to `Z` only for almost
every time). For an empty retained family there is nothing to identify. -/

section Trunc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- Truncation does not change the value. -/
theorem truncTo_val {K j : ℕ} (h : j ≤ K) (f : TorusHk K E) :
    (truncTo j f).val (valueIndex2 j) = f.val (valueIndex2 K) := by
  rw [truncTo_of_le h]
  rfl

end Trunc

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The kernel-lifted edge inputs of the terminal context: the paired smoothing of the truncations
of `Z` to the order `k_c + 2p_T + D_t - 1`. -/
def terminalEdgeInputs (kc : ℕ) : ∀ v u (_ : c.Gt'.fam.Γ v u), ℝ →
    TorusHk (kc + 2 * A.pT + A.Dt - 1) (ScalarH u.1.root) :=
  kernelLiftYom (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.hφ₀ c.Gt'
    (c.Gt'.retained M 1 A.RT) (kc + 2 * A.pT)
    (fun u t => truncTo (kc + 2 * A.pT + A.Dt - 1) (c.Z u t))

/-- The retained components of the stage are the components of the retained stage. -/
theorem mem_retained (u : CompIn c.Gt'.comps) :
    IsRetained M 1 A.RT u.1 ↔ u.1 ∈ (c.Gt'.retained M 1 A.RT).comps := by
  unfold GenStage.retained GenStage.restrict
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩

/-- **The identification at the terminal context**, from the order floor. -/
theorem termInnerIdentAt_of_orders (x : TermResAux c) (kc : ℕ) (hV : A.Valid)
    (hkc : A.Dt ≤ kc) (hK : kc + 2 * A.pT + A.Dt + 3 ≤ A.Khat Kout) :
    TermInnerIdentAt x kc := by
  have hφ := hV.2.1
  have hφc : HasCompactSupport A.φ₀ := Construction.KernelDefect.kd_hasCompactSupport hφ.2.2.2
  refine ⟨terminalEdgeInputs c kc, ?_, ?_⟩
  · intro v u γ hu
    have hu' : u.1 ∈ (c.Gt'.retained M 1 A.RT).comps := (mem_retained c u).1 hu
    have hmem : (⟨u.1, hu'⟩ : CompIn (c.Gt'.retained M 1 A.RT).comps) = ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ := rfl
    filter_upwards [c.sol.2.2.1 ⟨u.1, hu'⟩] with s hs
    have hv := kernelLiftYom_val (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.hφ₀ c.Gt'
      (c.Gt'.retained M 1 A.RT) (kc + 2 * A.pT)
      (fun u t => truncTo (kc + 2 * A.pT + A.Dt - 1) (c.Z u t)) v u γ hu' s
    have e1 : (truncTo (kc + 2 * A.pT + A.Dt - 1) (c.Z ⟨u.1, hu'⟩ s)).val
        (valueIndex2 (kc + 2 * A.pT + A.Dt - 1)) = (c.Z ⟨u.1, hu'⟩ s).val (valueIndex2 (A.Khat Kout)) :=
      truncTo_val (by omega) _
    have e2 : (termYw c kc ⟨u.1, hu'⟩ s).val (valueIndex2 (kc + 2 * A.pT + 1)) =
        (c.Z ⟨u.1, hu'⟩ s).val (valueIndex2 (A.Khat Kout)) := by
      unfold termYw
      rw [truncTo_val (by omega)]
      exact congrArg (fun Z => Z.val (valueIndex2 (A.Khat Kout))) hs
    change (kernelLiftYom _ _ _ A.hφ₀ _ _ _ _ v u γ s).val _ = _
    rw [hv, e1]
    change _ = (c.Gt'.kernelOf (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) v u γ).op A.φ₀ A.hφ₀ s _
    rw [e2]
  · intro v t ht
    refine omittedFlux_ae_eq_classical (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr)
      A.hφ₀ hφ.1 hφc c.Gt' (c.Gt'.retained M 1 A.RT) (IsRetained M 1 A.RT)
      (mem_retained c) (k := kc + 2 * A.pT) (kY := kc + 2 * A.pT + 1) (by omega)
      (fun u t => truncTo (kc + 2 * A.pT + 1) (c.Z u t)) x.aY (terminalEdgeInputs c kc) t ?_ ?_ v
    · intro u
      have h1 := AVRegularity.CycleComparison.Reconstruction.isClassicalRep_of_le (x.repY u t ht)
        (r' := kc + 2 * A.pT + 1) (by omega)
      rw [truncTo_of_le (by omega)]
      exact Construction.Preservation.FullLift.classicalRep_truncate (by omega) le_rfl _ _ h1
    · intro v u γ hu
      have hv := kernelLiftYom_val (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.hφ₀ c.Gt'
        (c.Gt'.retained M 1 A.RT) (kc + 2 * A.pT)
        (fun u t => truncTo (kc + 2 * A.pT + A.Dt - 1) (c.Z u t)) v u γ hu t
      have e1 : (truncTo (kc + 2 * A.pT + A.Dt - 1) (c.Z ⟨u.1, hu⟩ t)).val
          (valueIndex2 (kc + 2 * A.pT + A.Dt - 1)) = (c.Z ⟨u.1, hu⟩ t).val (valueIndex2 (A.Khat Kout)) :=
        truncTo_val (by omega) _
      have e2 : (truncTo (kc + 2 * A.pT + 1) (c.Z ⟨u.1, hu⟩ t)).val (valueIndex2 (kc + 2 * A.pT + 1)) =
          (c.Z ⟨u.1, hu⟩ t).val (valueIndex2 (A.Khat Kout)) := truncTo_val (by omega) _
      change (kernelLiftYom _ _ _ A.hφ₀ _ _ _ _ v u γ t).val _ = _
      rw [hv, e1, e2]

end Terminal

/-- **`TermInnerIdentStatement`, proved.** -/
theorem termInnerIdent_prefix : TermInnerIdentStatement := by
  intro X
  refine ⟨128, le_rfl, fun A _ hV => ?_⟩
  refine ⟨A.Dt, fun kc hkc => ?_⟩
  refine ⟨0, 0, kc + 2 * A.pT + A.Dt + 3, fun sXT sZT _ _ Kout hKout => ?_⟩
  refine ⟨0, fun Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _ cP CP cHP Cw Ce cker _ Cfl => ⟨0, 1, 1, one_pos, 1, 1, le_rfl, one_pos, fun C _ j₀ _ => ⟨0, fun M _ c x => ?_⟩⟩⟩
  exact termInnerIdentAt_of_orders c x kc hV hkc (le_trans hKout (le_max_left _ _))

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier.LengthPrice

/-! **The fresh-prefix price from the per-identity kernel price, generically.**
`fresh_prefix_price_of_actual` for arbitrary provenance parameters
(`genProvParams`, width exponent `σ`, decay order `d`) with the birth-diagonal bound `hbirth` as a
hypothesis. The per-identity kernel price `hprice` and the regularizer relation `hy` stay
hypotheses, as in the cascade. -/

open Ledger FullLift KernelEnergy AVRegularity.Construction.Preservation.Assembly RetainedEnergy
open scoped Classical
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The finite fresh-prefix constant, generic birth ratio `Rl`. -/
def freshPrefixConstantGen (Cw A Rl : ℝ) (Mn : SuccMenu) : ℝ :=
  A * (2 * ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (Mn.A.card : ℝ) * Cw * Rl)

theorem fresh_kernel_entry_le_gen (F : Frame D hr Dm bw j₀) (l : ℕ) (A : ℝ)
    (P : F.KernelOp)
    (hC : P.C = fun (v u : CompIn F.G'.comps) (_ : F.G'.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root))
    (hc : ∀ d, d + 2 ≤ Dm → 0 ≤ P.c d)
    (hprice : ∀ v u (γ : F.G'.fam.Γ v u),
      (∑ d : ↥(Finset.Icc 2 Dm),
        ((coefficientSeminorm (rhoEnh D F.cr F.m) F.k F.tp F.tf
          (F.G'.physCoeff v u γ d.1)).toReal * P.c (d.1 - 2)) /
          (D.κ (F.m - 1) * P.r v u γ ^ (d.1 - 2))) ≤
        A * (‖(F.G'.fam.identity v u γ).map‖ * (F.G'.fam.identity v u γ).record.size *
          constituentPrice (F.G'.fam.identity v u γ).record))
    (v u : CompIn F.G'.comps) :
    kernelSchurMatrix (D.κ (F.m - 1)) (rhoEnh D F.cr F.m) P.π F.k Dm F.tp F.tf
      P.c P.r P.C (F.freshCoeff l) v u ≤
      A * (if F.IsFreshEdge l v u then
        pricedRecordMajorant P.π (fun _ => 1) F.G'.fam v u else 0) := by
  classical
  by_cases he : F.IsFreshEdge l v u
  · simp only [he, ite_true]
    unfold kernelSchurMatrix pricedRecordMajorant
    simp only [Frame.freshCoeff, he, ite_true, hC, div_self (by norm_num : (1 : ℝ) ≠ 0),
      one_mul]
    rw [mul_left_comm A]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ _
    have hn : 0 ≤ ∑ d : ↥(Finset.Icc 2 Dm),
        ((coefficientSeminorm (rhoEnh D F.cr F.m) F.k F.tp F.tf
          (F.G'.physCoeff v u γ d.1)).toReal * P.c (d.1 - 2)) /
          (D.κ (F.m - 1) * P.r v u γ ^ (d.1 - 2)) := by
      apply Finset.sum_nonneg
      intro d _
      exact div_nonneg (mul_nonneg ENNReal.toReal_nonneg (hc _ (by
        have hd := Finset.mem_Icc.mp d.property
        omega))) (mul_nonneg P.diffusivity_pos.le (pow_nonneg (P.hr v u γ).le _))
    exact (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_id_le (𝕜 := ℝ)) hn).trans
      (by simpa only [one_mul] using hprice v u γ)
  · simp only [he, ite_false, Frame.freshCoeff, kernelSchurMatrix,
      CycleComparison.Coarse.coefficientSeminorm_zero_coefficient, ENNReal.toReal_zero,
      zero_mul, zero_div, Finset.sum_const_zero, mul_zero]
    exact le_rfl

theorem fresh_prefix_price_of_actual_gen (F : Frame D hr Dm bw j₀)
    {Cw σ η A Rl θ₁ θ₂ : ℝ} {N p d : ℕ} {Rb rb : ℕ → ℝ} {Mn : SuccMenu}
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hCw : 0 ≤ Cw) (hσ : 0 ≤ σ) (hA : 0 ≤ A)
    (hrb : rb (F.G.level - 1) = Rb (F.G.level - 1) * D.eps (F.G.level - 1) ^ σ)
    (hletters : ∀ l ∈ Mn.A, letterOrder N p l - 2 ≤ d)
    (hG : F.G.HasTags (genProvParams D Cw η N p Rb rb))
    (hold : ∀ v ∈ F.G.comps, ∀ e ∈ v.births, F.G.level ≤ e.scale)
    (hactual : IsActualSuccessor D (genProvParams D Cw η N p Rb rb) Mn F.G F.G')
    (hm : F.G.level = F.m) (hθ₁ : F.θ₁ = θ₁) (hθ₂ : F.θ₂ = θ₂)
    (hRl : 1 ≤ Rl) (hθ₂def : θ₂ = ocDelta D.α D.q - η - σ * (d : ℝ))
    (hbirth : birthDiagonalFactor D.q D.Λ F.G.level F.law true * D.eps (F.G.level - 1) ^ θ₂ ≤
      Rl * D.eps (F.G.level - 1) ^ θ₁)
    {S : ℝ} (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2)
    (hledger : markedLedger (F.G.mass F.law) (F.G.marker F.law) F.G.fam ≤ S)
    (l : ℕ) (hl : 1 ≤ l) (P : F.KernelOp)
    (hB : P.B = fun (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => F.G'.physCoeff v u γ d.1)
    (hC : P.C = fun (v u : CompIn F.G'.comps) (_ : F.G'.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root))
    (hπ : P.π = fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
    (hc : ∀ d, d + 2 ≤ Dm → 0 ≤ P.c d) (hθ : 0 ≤ P.θ)
    (hprice : ∀ v u (γ : F.G'.fam.Γ v u),
      (∑ d : ↥(Finset.Icc 2 Dm),
        ((coefficientSeminorm (rhoEnh D F.cr F.m) F.k F.tp F.tf
          (F.G'.physCoeff v u γ d.1)).toReal * P.c (d.1 - 2)) /
          (D.κ (F.m - 1) * P.r v u γ ^ (d.1 - 2))) ≤
        A * (‖(F.G'.fam.identity v u γ).map‖ * (F.G'.fam.identity v u γ).record.size *
          constituentPrice (F.G'.fam.identity v u γ).record))
    (hy : ∀ v u (γ : F.G'.fam.Γ v u) (hu : IsRetained F.m F.H F.J u.1),
      ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
        (F.yom v u γ t).val (valueIndex2 (F.k + Dm - 1)) =
          P.S v u γ t ((F.Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t).val
            (valueIndex2 (F.k + 1)))) :
    FreshPrefixPriceStatement F l (freshPrefixConstantGen Cw A Rl Mn) := by
  classical
  let Cp := 2 * ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (Mn.A.card : ℝ) * Cw *
    Rl
  have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
  have heps : 0 < D.eps (F.m - 1) := (Scales.epsilon_basic
    (m := F.m - 1) hq hΛ).1
  let Q : LedgerEdge F.G' → Prop := fun e => F.IsFreshEdge l e.1 e.2.1
  have hrecords := fresh_record_schur_gen hq hΛ hCw hσ hrb hletters F.law
    hG hold hactual hRl hθ₂def hbirth hS hhalf hledger l hl Q (fun e he => by
      exact ⟨hm.symm ▸ he.1.2, hm.symm ▸ he.2.2⟩)
  have hexp : (if l = 1 then θ₁ else θ₂) =
      F.lengthExponent l := by rw [Frame.lengthExponent, hθ₁, hθ₂]
  rw [hm, hexp] at hrecords
  have hπpos (v : CompIn F.G'.comps) : 0 < F.G'.mass F.law v :=
    Buffer.birth_compMass_pos hq hΛ F.law v.1
  have hmarkpos (v : CompIn F.G'.comps) : 0 < F.G'.marker F.law v :=
    Buffer.birth_compMarker_pos hq hΛ F.law v.1
  have hsum (v u : CompIn F.G'.comps) :
      (∑ γ, if Q ⟨v, u, γ⟩ then identityPrice F.G'
        (ledgerDiagonal D.q D.Λ F.law true) ⟨v, u, γ⟩ else 0) =
      if F.IsFreshEdge l v u then
        pricedRecordMajorant P.π (fun _ => 1) F.G'.fam v u else 0 := by
    by_cases he : F.IsFreshEdge l v u
    · simp only [Q, he, ite_true]
      rw [sum_identityPrice_eq hq hΛ F.law true, hπ,
        pricedRecordMajorant_effective_mass F.G'.fam _ _ hπpos hmarkpos]
      rfl
    · simp only [Q, he, ite_false, Finset.sum_const_zero]
  have hentry (v u : CompIn F.G'.comps) :
      kernelSchurMatrix (D.κ (F.m - 1)) (rhoEnh D F.cr F.m) P.π F.k Dm F.tp F.tf
        P.c P.r P.C (F.freshCoeff l) v u ≤
      A * (∑ γ, if Q ⟨v, u, γ⟩ then identityPrice F.G'
        (ledgerDiagonal D.q D.Λ F.law true) ⟨v, u, γ⟩ else 0) := by
    rw [hsum]
    exact fresh_kernel_entry_le_gen F l A P hC hc hprice v u
  have hsharp : SchurBound (freshPrefixConstantGen Cw A Rl Mn *
      D.eps (F.m - 1) ^ F.lengthExponent l)
      (kernelSchurMatrix (D.κ (F.m - 1)) (rhoEnh D F.cr F.m) P.π F.k Dm F.tp F.tf
        P.c P.r P.C (F.freshCoeff l)) := by
    constructor
    · intro v
      calc
        _ ≤ ∑ u, A * (∑ γ, if Q ⟨v, u, γ⟩ then identityPrice F.G'
            (ledgerDiagonal D.q D.Λ F.law true) ⟨v, u, γ⟩ else 0) :=
          Finset.sum_le_sum (fun u _ => hentry v u)
        _ = A * ∑ u, ∑ γ, if Q ⟨v, u, γ⟩ then identityPrice F.G'
            (ledgerDiagonal D.q D.Λ F.law true) ⟨v, u, γ⟩ else 0 := (Finset.mul_sum _ _ _).symm
        _ ≤ A * (Cp * D.eps (F.m - 1) ^ F.lengthExponent l) :=
          mul_le_mul_of_nonneg_left (hrecords.1 v) hA
        _ = _ := by unfold freshPrefixConstantGen; dsimp only [Cp]; ring
    · intro u
      calc
        _ ≤ ∑ v, A * (∑ γ, if Q ⟨v, u, γ⟩ then identityPrice F.G'
            (ledgerDiagonal D.q D.Λ F.law true) ⟨v, u, γ⟩ else 0) :=
          Finset.sum_le_sum (fun v _ => hentry v u)
        _ = A * ∑ v, ∑ γ, if Q ⟨v, u, γ⟩ then identityPrice F.G'
            (ledgerDiagonal D.q D.Λ F.law true) ⟨v, u, γ⟩ else 0 := (Finset.mul_sum _ _ _).symm
        _ ≤ A * (Cp * D.eps (F.m - 1) ^ F.lengthExponent l) :=
          mul_le_mul_of_nonneg_left (hrecords.2 u) hA
        _ = _ := by unfold freshPrefixConstantGen; dsimp only [Cp]; ring
  exact ⟨fresh_edge_provenance_of_actual F hactual hold hm l,
    fresh_prefix_price_of_schur F l _ P hB hC hπ hc hθ
      (mul_nonneg (mul_nonneg hA hCp) (Real.rpow_nonneg heps.le _)) hsharp hy⟩

end AVRegularity.Construction.Preservation.Frontier.LengthPrice
end
end
end

section
section
section
/-! **The row statement from the terminal fresh-prefix price.**

Generic pieces (shared with the fresh-record Schur bound):
* `birth_bound_any`: the first-prefix birth factor of a law with `ι ≥ 0`;
* `freshPrice_of_larger_exponent`: a price with larger exponents gives the price with smaller ones;
* `termFresh_exponent_facts`: the arithmetic `θ_T = δ - η₀ - t_T s_T`, `θ_T - η₀/4 ≥ δ/2`
  from `IsTerminalSchedule`.

Terminal: `termInnerRowsAt_of_price` reduces `TermInnerRowsAt` to `FreshPrefixPriceStatement` at
the lengths `1..R_T+1` and the time integrability of `Y_w`.

For `R_T = 0` there is a single prefix, and for `x.aY = 0` the flux vanishes. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Frontier

namespace AVRegularity.Construction.Residual.Presentation

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- A price with larger exponents gives the price with smaller ones. -/
theorem freshPrice_of_larger_exponent (F : Frame D hr Dm bw j₀) (θ₁' θ₂' : ℝ)
    (h1 : F.θ₁ ≤ θ₁') (h2 : F.θ₂ ≤ θ₂') (hE : 0 < D.eps (F.m - 1)) (hE1 : D.eps (F.m - 1) ≤ 1)
    (l : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : FreshPrefixPriceStatement { F with θ₁ := θ₁', θ₂ := θ₂' } l C) :
    FreshPrefixPriceStatement F l C := by
  obtain ⟨hprov, P, hB, hC', hπ, hθ0, hθ, hy⟩ := h
  refine ⟨hprov, P, hB, hC', hπ, hθ0, hθ.trans ?_, hy⟩
  apply mul_le_mul_of_nonneg_left _ hC
  unfold Frame.lengthExponent
  by_cases hl : l = 1
  · simp only [hl, ite_true]
    exact Real.rpow_le_rpow_of_exponent_ge hE hE1 h1
  · simp only [hl, ite_false]
    exact Real.rpow_le_rpow_of_exponent_ge hE hE1 h2

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The tags of a stage whose provenance is all `seed` do not depend on the parameters. -/
theorem hasTags_of_seed_prov {G : GenStage D hr Dm bw j₀} {P P' : ProvParams}
    (hseed : ∀ v u (γ : G.fam.Γ v u), ∃ k tag, G.prov v u γ = .seed k tag)
    (h : G.HasTags P) : G.HasTags P' := by
  intro v u γ
  obtain ⟨k, tag, hk⟩ := hseed v u γ
  have := h v u γ
  rw [hk] at this ⊢
  exact this

end Generic

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The exponent arithmetic of the terminal price**: with
`θ_T = δ - η₀ - t_T s_T`, both `θ_T` and `θ_T - η₀/4` are at least `δ/2`. -/
theorem termFresh_exponent_facts (hV : A.Valid) :
    ocDelta X.α X.q / 2 ≤
      ocDelta X.α X.q - A.η₀ - A.tT * (termExcess A.NT A.pT A.alph : ℝ) - A.η₀ / 4 := by
  obtain ⟨-, -, -, -, -, hsch, -⟩ := hV
  obtain ⟨-, -, -, -, -, -, hη, hη8, htT, htT8, -⟩ := hsch
  set sT : ℝ := (termExcess A.NT A.pT A.alph : ℝ) with hsT
  have hsT0 : (0 : ℝ) ≤ sT := Nat.cast_nonneg _
  have hden : 0 < 8 * (sT + 1) := by positivity
  have h1 : A.tT * (8 * (sT + 1)) < ocDelta X.α X.q := (lt_div_iff₀ hden).1 htT8
  nlinarith

/-- Every fresh letter of the terminal alphabet has present order at most `2 + s_T`. -/
theorem termFresh_letters (l : WordLetter) (hl : l ∈ A.alph) :
    letterOrder A.NT A.pT l - 2 ≤ termExcess A.NT A.pT A.alph :=
  Nat.sub_le_sub_right (Finset.le_sup (f := letterOrder A.NT A.pT) hl) 2

/-- **Row Cauchy at the terminal frame, from the fresh-prefix price** at the lengths `1..R_T+1`
and the time integrability of `Y_w`. -/
theorem termInnerRowsAt_of_price
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (kc : ℕ) (C : ℝ)
    (hprice : ∀ yom, TermYomSpec c kc yom → ∀ l : ℕ, 1 ≤ l → l ≤ A.RT + 1 →
      FreshPrefixPriceStatement (termFrame c kc yom) l C)
    (hmem : ∀ u, MemLp (termYw c kc u) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))) :
    TermInnerRowsAt c kc C := fun yom hy =>
  outside_length_rows_of_prefix_rows (termFrame c kc yom) C fun l hl1 hlJ =>
    word_length_row_of_price (termFrame c kc yom) l C hl1 hlJ (hprice yom hy l hl1 hlJ) hmem

end Terminal

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **Smoothness of the coefficients of the terminal successor.**

The coefficients `Gt'.physCoeff` of ALL rows of the terminal successor (retained or omitted) are
`C^n` for every `n` and `ℤ²`-periodic, from the context certificate
(`native_physCoeff_all_order_smooth`) and the shift invariance. The slot transversality of `Gt'` is
derived from the weak stage and the successor (`terminalSuccessor_generation`); the certificate
`Gt'.IsContextCertified kW` is a named hypothesis (it needs `Cw ≥ Cw₀`). If `Gt'` has no edges, the transversality statement is vacuous. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route

namespace AVRegularity.Construction.Residual.Presentation

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The slot transversality of the terminal successor at the context. -/
theorem termCtx_slotTransverse (x : TermResAux c) (hA : A.Valid) (hΛ : 128 ≤ A.Λ)
    {CH Υ : ℝ} (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT) : c.Gt'.IsSlotTransverse := by
  have hN : 2 ≤ A.NT := AVRegularity.EntryTerminal.Ingredients.two_le_NT_of_valid A hA
  have hDW : 1 ≤ A.DW := hA.2.2.2.2.2.2.2.2
  have hb : 0 < A.bw := hA.2.2.1.1
  have hcr : cr ≠ 0 := by rw [x.one]; exact one_ne_zero
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := by rw [hΛD]; omega
  have hζ : IsFastProfile c.D.ζ := by rw [hζD]; exact X.hζ
  have hκ : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [hα, hq, hΛD, hζD, hterm]; exact hband
  have hcar' : IsCarrierStart c.D.α c.D.q c.D.Λ A.bw CH Υ j₀ := by rw [hα, hq, hΛD]; exact hcar
  exact (Providers.GenSem.terminalSuccessor_generation hΛ1 hζ hκ hb hCH hΥ hcar' hterm c.weak
    hN hDW hcr hX hZ c.succ).2

/-- The shift invariance of the terminal successor at the context. -/
theorem termCtx_shiftInvariant (hΛ : 128 ≤ A.Λ) : c.Gt'.IsShiftInvariant := by
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := by rw [hΛD]; omega
  have hζ : IsFastProfile c.D.ζ := by rw [hζD]; exact X.hζ
  have hκ : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [hα, hq, hΛD, hζD, hterm]; exact hband
  have hcs : 0 ≤ c.D.cellScaleSq c.Gw.level :=
    (EntryWeakProofs.weakData_cellScaleSq_pos c.D hΛ1 hζ hκ _).le
  obtain ⟨-, -, -, -, -, -, -, -, -, hinv⟩ := c.weak
  obtain ⟨hnat, -, -, hsh, -⟩ := hinv
  exact Construction.Preservation.FullLift.successor_shift_invariant_of_cellScaleSq_nonneg hζ hcs
    hnat hsh c.succ

end AVRegularity.Construction.Residual.Presentation
end
end
end

section
section
/-! **The smoothness of the classical readout of the omitted flux.**

`termCtx_physCoeff`: all coefficients of the terminal successor are `C^n` and periodic, from the
certificate. `omittedFluxClassical_smooth` (generic): the classical omitted flux is `C^n` and
periodic when the coefficients are and the classical field is `C^{n+D_m-1}` and periodic.
`termInnerSmoothAt_of_certificate`: the readout.

For `aY = 0` everything is zero. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.FullLift

namespace AVRegularity.Construction.Residual.Presentation

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- `compReserve k c ≤ 1`. -/
theorem compReserve_le_one' (k : InvConsts) (c : Comp) : compReserve k c ≤ 1 := by
  unfold compReserve
  have : (0 : ℝ) ≤ ((k.G0 + compGrade c : ℕ) : ℝ) / ((k.Hprod : ℝ) + 1) := by positivity
  linarith

/-- **All coefficients of the terminal successor are smooth and periodic** (from the certificate,
the slot transversality and the shift invariance). -/
theorem termCtx_physCoeff (x : TermResAux c) (hcert : c.Gt'.IsContextCertified kW)
    (hST : c.Gt'.IsSlotTransverse) (hSH : c.Gt'.IsShiftInvariant) (hA : A.Valid) (hΛ : 128 ≤ A.Λ)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (n : ℕ) (v u : CompIn c.Gt'.comps) (γ : c.Gt'.fam.Γ v u) (d : ℕ) (t : ℝ) :
    ContDiff ℝ (n : ℕ) (c.Gt'.physCoeff v u γ d t) ∧ IsZ2Periodic (c.Gt'.physCoeff v u γ d t) := by
  have hb : 0 < A.bw := hA.2.2.1.1
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := by rw [hΛD]; omega
  have hlevW : c.Gw.level = M := c.weak.2.2.1
  have hbirth : ∀ w : CompIn c.Gw.comps, w.1.births = [] := c.weak.2.2.2.2.1
  have hlev : c.Gt'.level = M - 1 := by rw [c.succ.2.1, hlevW]
  have hres : ∀ w : CompIn c.Gt'.comps, 0 ≤ compReserve kW w.1 := fun w =>
    termReserve_nonneg x.reserve1
      (termGrade_le_one (fun u => by simp [compGrade, hbirth u]) c.succ w)
  have hnat := c.succ.2.2.2.1
  refine ⟨native_physCoeff_all_order_smooth hcert hST hnat (by rw [hlev]; omega) (by rw [hlev]; omega) hb
    (Construction.Stream.ocEpsilon_pos hΛ1) t t v u γ (hres v)
    ((compReserve_le_one' kW v.1).trans (by norm_num)) n d t ⟨le_rfl, le_rfl⟩, ?_⟩
  exact Construction.Preservation.Buffer.native_physCoeff_periodic hnat hSH v u γ d t

/-- **The readout of the omitted flux is smooth and periodic, from the certificate** (the first
clause of `FrontierInnerAt`; `TermInnerSmoothAt`). Premises: the certificate of `Gt'`, the
carrier start with `C_H = Υ = 1`, the lift floors, the level `M ≥ j₀ + 2` and the order floor
`k_c + 2p_T + D_t + 2 ≤ K̂`. -/
theorem termInnerSmoothAt_of_certificate (x : TermResAux c) (kc : ℕ)
    (hcert : c.Gt'.IsContextCertified kW) (hA : A.Valid) (hΛ : 128 ≤ A.Λ)
    {CH Υ : ℝ} (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (hK : kc + 2 * A.pT + A.Dt + 2 ≤ A.Khat Kout) :
    TermInnerSmoothAt x kc := by
  intro v t ht
  have hST := termCtx_slotTransverse c x hA hΛ hCH hΥ hcar hX hZ
  have hSH := termCtx_shiftInvariant c hΛ
  have hφ := hA.2.1
  have hflux := omittedFluxClassical_smooth (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr)
    A.φ₀ hφ.1 hφ.2.2.2 c.Gt' (c.Gt'.retained M 1 A.RT) x.aY t (kc + 2 * A.pT)
    (fun v u γ d => termCtx_physCoeff c x hcert hST hSH hA hΛ hj hM2 _ v u γ d t)
    (fun u => by
      obtain ⟨-, h1, h2, -⟩ := x.repY u t ht
      exact ⟨h1.of_le (WithTop.coe_le_coe.2 (Nat.cast_le.2 (by omega))), h2⟩)
  have hro := readoutFlux_smooth (hr := ScalarH) M (c.D.eps (M - 1)) A.η₀
    (S := c.Gw.comps) (S' := c.Gt'.comps) (fun c' => ¬ IsRetained M 1 A.RT c')
    (fun v' s y' => omittedFluxClassical (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr)
      A.φ₀ c.Gt' (c.Gt'.retained M 1 A.RT) x.aY v' s y') t (kc + 2 * A.pT)
    (fun v' => hflux v') v
  exact ⟨PiLp.contDiff_ofLp.comp hro.1, fun k y => congrArg WithLp.ofLp (hro.2 k y)⟩

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **The weight floor of the plan**, used by the smoothness part from the certificate
(`termInnerSmoothAt_of_certificate`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route

namespace AVRegularity.Construction.Residual.Presentation

/-- The weight floor of `x.lstar` gives that of the plan. -/
theorem termPlan_lstar {X : TermConstruction} {A : TermArgs X} {kW : InvConsts} (hV : A.Valid)
    (hLs : A.NT + A.DW + A.dW * (A.Dt + 1) ≤ kW.Lstar) :
    Providers.GenSem.UEnv.liftWt A.Dt A.dW (termNMax A) ≤ kW.Lstar := by
  have hDW : 1 ≤ A.DW := hV.2.2.2.2.2.2.2.2
  unfold termNMax Providers.GenSem.UEnv.liftWt
  by_cases h0 : A.dW = 0
  · simp only [h0, ite_true, zero_mul, add_zero] at hLs ⊢
    omega
  · simpa [h0] using hLs

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **The prefix forms of the marker and smoothness parts.** Both are proved at a
context:
- the marker by `termInnerMarkerAt_of_ctx`, with `lawT.c_H = c_{H,P} ≤ 1` from `x.cHle` and
  `IsTerminalLaw`;
- the smoothness by `termInnerSmoothAt_of_certificate`, with the certificate `x.cert`.
This section supplies the floors of the prefix: `C₀ = #words + 1` for the marker; `s_X, s_Z`,
`K_out` and `M ≥ j₀ + 2` for the smoothness.

For `R_T = 0` there is one word length, and `C₀ = #words + 1` is still positive; for `j₀ = 0` the
floor reads `M ≥ 2`. -/

@[expose] public noncomputable section

open AVRegularity.EntryTerminal.Route

namespace AVRegularity.Construction.Residual.Presentation

/-- **Marker readout with the prefix.** -/
theorem termInnerMarker : TermInnerMarkerStatement := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hV => ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨0, ?_⟩⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker _ Cfl
  refine ⟨((wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) (A.RT + 1)).card : ℝ) + 1, 1, 1, one_pos,
    1, 1, le_rfl, one_pos, fun C hC j₀ _ => ⟨1, fun M hM c x => ?_⟩⟩
  have hcH : c.lawT.cH ≤ 1 := by rw [c.law.2.2.1]; exact x.cHle
  exact termInnerMarkerAt_of_ctx c hΛ hV hM hcH kc hC

/-- **Smoothness of the classical readout with the prefix.** -/
theorem termInnerSmooth : TermInnerSmoothStatement := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hV => ⟨0, fun kc _ => ?_⟩⟩
  set S := max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 with hS
  refine ⟨S, S, kc + 2 * A.pT + A.Dt + 2, fun sXT sZT hX hZ Kout hKout => ⟨0, ?_⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker _ Cfl
  refine ⟨0, 1, 1, one_pos, 1, 1, le_rfl, one_pos, fun C _ j₀ hcar => ⟨j₀ + 2, fun M hM c x => ?_⟩⟩
  exact termInnerSmoothAt_of_certificate c x kc x.cert hV hΛ le_rfl le_rfl hcar hX hZ (by omega)
    (by omega) (le_trans hKout (le_max_left _ _))

end AVRegularity.Construction.Residual.Presentation
end
end
end
end
