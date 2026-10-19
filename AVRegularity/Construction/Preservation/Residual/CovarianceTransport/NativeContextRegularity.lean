-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.StageSuccessor.StageOfFields
import AVRegularity.EntryWeakAssembly.QuietScalarEvolution
public import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.Smooth
import AVRegularity.Proofs.QuietAtlas.PiolaGeom
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.Proofs.Results.Construction.ContextCertified.Assemble
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.Flux
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeDifferentialOperators
import AVRegularity.Construction.FreshAxes.RefFluxContinuous
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import AVRegularity.EntryWeakAssembly.NativeFullLiftRankCentering
import AVRegularity.EntryWeakAssembly.NativeWeakLiftFamilies
import AVRegularity.Proofs.GenSem.LiftOn.Omega

/-! Qualitative native coefficient regularity from the actual holomorphic context
certificate. No nonnegative inner-reserve or quantitative smallness premise is added. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology
open AVRegularity.Sobolev AVRegularity.Providers.GenSem AVRegularity.Providers.WeakGen
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- Phase periodicity of the outer extension includes arbitrary parallel real shifts. -/
theorem native_holomorphic_parallel_shift {D : OCData} (hΛ : 1 ≤ D.Λ)
    {bw : ℝ} (hb : 0 < bw) {j₀ m : ℕ} {p : ℤ} {f : GenSort.Sem .ctx}
    {F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ}
    (hF : IsHolExtension D bw j₀ m p f F) (A : RealChain)
    (hA : IsAdmissibleChain D bw j₀ m p A) (t : ℝ)
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ m p) (z : Vec 2) (s : ℝ) :
    f t A (z + s • basisVec (slotParallel p)) = f t A z := by
  have hslot : A.data.slots.getLastD 0 = p := hA.2.2.2.1
  have hzero : (s • basisVec (slotParallel p)) (transverseIndex (A.data.slots.getLastD 0)) =
      (0 : ℤ) := by
    rw [hslot]
    simp only [Pi.smul_apply, smul_eq_mul, basisVec_apply]
    unfold slotParallel transverseIndex
    split_ifs <;> norm_num at *
  have hper := (hF.2.1.2.1 A.data A.children.length t ht (A.paramsC z)
    (paramsC_mem_carrierC hΛ hb hA z)).1 (s • basisVec (slotParallel p)) ⟨0, hzero⟩
  have he : (A.paramsC z).shiftFinal (s • basisVec (slotParallel p)) =
      A.paramsC (z + s • basisVec (slotParallel p)) := by
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext c
    simp only [ChainParamsC.shiftFinal, RealChain.paramsC, Pi.add_apply, Complex.ofReal_add]
  rw [he, hF.2.2 A t ht _ hA, hF.2.2 A t ht z hA] at hper
  exact Complex.ofReal_injective hper

/-- The menu anchor remains fixed in the covariance time derivative. -/
theorem native_menu_covariance_derivative (D : OCData) (Mn : SuccMenu) (m : ℕ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hν : 0 < D.κ m) (t : ℝ) (i j : Fin 2) :
    HasDerivAt (fun r => menuCovPrimitive D Mn m r i j)
      ((ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t - D.κ (m - 1) • 1) i j) t := by
  have hc := (FreshAxes.refFlux_entry_continuous
    (α := D.α) (q := D.q) (m := m) hΛ hζ hν i j).sub
      (continuous_const (y := D.κ (m - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable Mn.anchor t) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- Symmetry of the reference flux gives symmetry at every menu anchor. -/
theorem native_menu_covariance_symmetric (D : OCData) (Mn : SuccMenu) (m : ℕ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (t : ℝ) (i j : Fin 2) :
    menuCovPrimitive D Mn m t i j = menuCovPrimitive D Mn m t j i := by
  apply intervalIntegral.integral_congr
  intro r _
  change ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) r i j -
      D.κ (m - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j =
    ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) r j i -
      D.κ (m - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) j i
  rw [Construction.Preservation.FullLift.refFlux_entry_symm hΛ hζ]
  simp only [Matrix.one_apply, eq_comm]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The context certificate already supplies the transverse law on its output windows. -/
theorem native_context_slot_transverse (hΛ : 1 ≤ D.Λ) (hb : 0 < bw)
    {G : GenStage D hr Dm bw j₀} {kI : InvConsts} (hG : G.IsContextCertified kI) :
    G.IsSlotTransverse := by
  intro p ctx v u γ d I t ht X z s
  funext c
  obtain ⟨θ, _, _, hθ⟩ := hG v u γ
  obtain ⟨f, F, hF, _⟩ := hθ d I c
  have hval := (hF p).2.2
  rw [hval ctx t ht X _, hval ctx t ht X z]
  split_ifs with hA
  · exact native_holomorphic_parallel_shift hΛ hb (hF p).2.1 _ hA t ht z s
  · rfl

/-- Actual scalar fields inherit the local smoothness and compact jet budgets of
outer holomorphic extensions, at the menu's own slow length and physical clock. -/
theorem native_context_flux_local_data (hΛ : 1 ≤ D.Λ) (hb : 0 < bw)
    {G : GenStage D hr Dm bw j₀} {kI : InvConsts} (hG : G.IsContextCertified kI)
    (p : OddSlot) (A : RealChain) (hA : IsAdmissibleChain D bw j₀ G.level p.1 A)
    (ρ : ℝ) (T : Set ℝ) (clock : ℝ → ℝ) (hc : Continuous clock)
    (hclock : MapsTo clock T (ocPulseWindow D.α D.q D.Λ G.level p.1))
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
    let Ω := ladderOmega D bw j₀ G.level p.1 A ρ
    let g := fun t (z Y : Vec 2) => G.fam.flux p ⟨A, hA⟩ v u γ d I (clock t)
      ((ρ / D.eps (G.level - 1)) • Y) z c
    (∀ t ∈ T, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun X : Vec 2 × Vec 2 => g t X.1 X.2) {X | X.2 ∈ Ω}) ∧
    (∀ Y ∈ Ω, Measurable (fun Z : T × Vec 2 => g Z.1 Z.2 Y)) ∧
    (∀ K : Set (Vec 2 × Vec 2), IsCompact K → K ⊆ {X | X.2 ∈ Ω} → ∀ n,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ T, ∀ X ∈ K,
        ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × Vec 2 => g t Z.1 Z.2) X‖ ≤ B) := by
  obtain ⟨θ, _, _, hθ⟩ := hG v u γ
  obtain ⟨f, F, hF, _⟩ := hθ d I c
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  obtain ⟨hs, hm, hj⟩ := holomorphic_recenter_data hΛ hb (hF p).2.1 A ρ T clock hc hclock
  let Ω := ladderOmega D bw j₀ G.level p.1 A ρ
  have he (t : ℝ) (ht : t ∈ T) (X : Vec 2 × Vec 2) (hX : X.2 ∈ Ω) :
      G.fam.flux p ⟨A, hA⟩ v u γ d I (clock t) ((ρ / D.eps (G.level - 1)) • X.2) X.1 c =
        f p (clock t) (A.recenter D (ρ • X.2)) X.1 := by
    rw [(hF p).2.2 ⟨A, hA⟩ (clock t) (hclock ht), smul_smul, mul_div_cancel₀ _ hε]
    exact ite_eq_left hX
  refine ⟨fun t ht => (hs t ht).congr (fun X hX => he t ht X hX), ?_, ?_⟩
  · intro Y hY
    convert hm Y hY using 1
    funext Z
    exact he Z.1 Z.1.2 (Z.2, Y) hY
  · intro K hK hKO n
    obtain ⟨B, hB, hbound⟩ := hj K hK hKO n
    refine ⟨B, hB, fun t ht X hX => ?_⟩
    have heq : (fun Z : Vec 2 × Vec 2 => G.fam.flux p ⟨A, hA⟩ v u γ d I (clock t)
        ((ρ / D.eps (G.level - 1)) • Z.2) Z.1 c) =ᶠ[𝓝 X]
        (fun Z => f p (clock t) (A.recenter D (ρ • Z.2)) Z.1) := by
      filter_upwards [((isOpen_ladderOmega D bw j₀ G.level p.1 A ρ).preimage
        continuous_snd).mem_nhds (hKO hX)] with Z hZ
      exact he t ht Z hZ
    rw [(heq.iteratedFDeriv ℝ n).self_of_nhds]
    exact hbound t ht X hX

/-- Reuse the physical multiplier API at every finite order on the actual window.
The incoming certificate is an existing context/ledger output, not a PDE assumption. -/
theorem native_context_physical_fields
    [∀ r, FiniteDimensional ℝ (hr r)]
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hΛ : 1 ≤ D.Λ) (hb : 0 < bw) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hG : G.IsContextCertified k) (hn : G.IsNatural M) (hsh : G.IsShiftInvariant)
    (hres : ∀ v : CompIn G.comps, 0 ≤ compReserve k v.1)
    (a b : ℝ) (n d : ℕ) (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    (∀ t ∈ Icc a b, ContDiff ℝ (n : ℕ) (G.physCoeff v u γ d t) ∧
      AVenhance.IsZ2Periodic (G.physCoeff v u γ d t)) ∧
    Measurable (fun z : Icc a b × Vec 2 => G.physCoeff v u γ d z.1 z.2) ∧
    coefficientSeminorm (D.eps (G.level - 1)) n a b (G.physCoeff v u γ d) ≠ ⊤ := by
  have hp := native_context_slot_transverse hΛ hb hG
  have hε : 0 < D.eps (G.level - 1) := Construction.Stream.ocEpsilon_pos hΛ
  have htwo : ∀ w : CompIn G.comps, compReserve k w.1 ≤ 2 :=
    fun w => GenStage.compReserve_le_two k w.1
  refine ⟨fun t ht => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact Construction.Preservation.FullLift.native_physCoeff_all_order_smooth
      hG hp hn hi hj hb hε a b v u γ (hres v) (htwo v) n d t ht
  · exact Construction.Preservation.Buffer.native_physCoeff_periodic hn hsh v u γ d t
  · exact Construction.Preservation.FullLift.native_physCoeff_joint_measurable_of_context
      hG hp hn hΛ hi hj hb hε a b hres htwo v u γ d
  · exact Construction.Preservation.FullLift.native_physCoeff_all_order_seminorm_finite
      hG hp hn hi hj hb hε a b v u γ (hres v) (htwo v)
      (D.eps (G.level - 1)) hε le_rfl n d

/-- Retention preserves the already produced context and torus certificates.
Only the cell scale at the current level is used; the unused tail is unconstrained. -/
theorem native_input_retained_certificates
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {F : Frame D hr Dm bw j₀} (hi : NativeInput F) :
    F.Gr.IsNatural F.Mn.M ∧ F.Gr.IsShiftInvariant ∧
      ∃ k : InvConsts, F.Gr.IsContextCertified k ∧
        ∀ v : CompIn F.Gr.comps, 0 ≤ compReserve k v.1 := by
  obtain ⟨k, hc, hr⟩ := hi.outgoing_context
  have hcs : 0 ≤ D.cellScaleSq F.G.level :=
    (EntryWeakProofs.weakData_cellScaleSq_pos D hi.stage.base hi.stage.profile hi.stage.band F.G.level).le
  have hsh := Construction.Preservation.FullLift.successor_shift_invariant_of_cellScaleSq_nonneg
    hi.stage.profile hcs hi.stage.natural hi.shift hi.actual
  rw [hi.retained]
  have hn := hi.actual.2.2.2.1
  refine ⟨⟨hn.1, hn.2.1, hn.2.2.1, fun v u => hn.2.2.2 _ _⟩,
    hsh.restrict _ _, k, (hc.retained F.m F.H F.J).2, ?_⟩
  intro v
  exact hr ⟨v.1, (Finset.filter_subset (IsRetained F.m F.H F.J) F.G'.comps) v.2⟩

/-- Every canonical scalar path coefficient has a genuinely bounded local model at
any finite reserve. The path, stage, window and slow length are the ones already
used by the generic successor construction. -/
theorem native_path_coefficient_local_reserve {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (A : RealChain)
    (hA : IsAdmissibleChain D bw j₀ G.level k A ∧ Odd k)
    (R hh n m : ℕ) (hhh : hh ≤ h) (hn : 1 ≤ n) (hnN : n ≤ Mn.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : Fin (h + 1)) (Y₀ : Vec 2)
    (hY : Y₀ ∈ ladderOmega D bw j₀ G.level k A (Mn.lenFactor * liftLength D G.level)) :
    let a := D.slotStart G.level k / D.cellScaleSq G.level
    let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    ∃ (U : Set (Vec 2)) (c : Vec 2 → ℝ → Vec 2 → ℝ),
      IsOpen U ∧ Y₀ ∈ U ∧
      U ⊆ ladderOmega D bw j₀ G.level k A (Mn.lenFactor * liftLength D G.level) ∧
      Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R
        (fun t z Y => c Y t z)) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
        c Y t z = StageSuccessor.pathLiftFamily hi.base hi.profile hi.band
          (Mn.lenFactor * liftLength D G.level) Mn.N π k A hh n m α t Y z v u 1 := by
  classical
  dsimp only
  obtain ⟨kI, hcontext⟩ := hi.context
  let ρ := Mn.lenFactor * liftLength D G.level
  let edge := pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩
  let a := D.slotStart G.level k / D.cellScaleSq G.level
  let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let Ω := ladderOmega D bw j₀ G.level k A ρ
  let base := R + 2 * Dm + 5
  have hbase : 2 * Dm + 1 + 4 ≤ base := by dsimp only [base]; omega
  have hp := WeakEntryProofs.native_full_lift_rank_induction D hi.profile hi.base G.level
    (EntryWeakProofs.weakData_kap_pos D hi.base hi.profile hi.band G.level)
    k hA.2 A hA.1.2.2.1 ρ edge a b
    (EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level k)
    1 le_rfl base Mn.N h hi.order hbase Ω
    (isOpen_ladderOmega D bw j₀ G.level k A ρ)
    (StageSuccessor.context_path_local_reserves hi.base hi.profile hi.band hi.bandwidth
      G hcontext π k hA.2 ρ A hA.1) hh n hhh hn hnN m hm α v u
  obtain ⟨U, c, hU, hYU, hUΩ, ⟨Qc⟩, hc⟩ := hp.local_reserve Y₀ hY
  have hroom : R ≤ WeakEntryProofs.weakLiftRankReserve Dm base Mn.N h hh n := by
    have hb := WeakEntryProofs.weakLiftRankReserve_base Dm base Mn.N h hh n
    exact (show R ≤ base + 1 by dsimp only [base]; omega).trans hb
  let cw := fun Y t z => EntryWeakProofs.independentTimeWindowSource (Ioc a b)
    (fun t z Y => c Y t z) t z Y
  refine ⟨U, cw, hU, hYU, hUΩ, ⟨Qc.restrictOrder R hroom⟩, ?_⟩
  have he (t : ℝ) (ht : t ∈ Icc a b) (Y : Vec 2) (hYU : Y ∈ U) (z : Vec 2) :
      c Y t z = StageSuccessor.pathLiftFamily hi.base hi.profile hi.band
        (Mn.lenFactor * liftLength D G.level) Mn.N π k A hh n m α t Y z v u 1 := by
    rw [hc t ht Y hYU z]
    have hmem : Y ∈ ladderOmega D bw j₀ G.level k A
        (Mn.lenFactor * liftLength D G.level) := hUΩ hYU
    simp only [StageSuccessor.pathLiftFamily, dite_eq_left hA,
      WeakEntryProofs.weakLiftCarrierRestriction, ite_eq_left (Or.inr hmem)]
    rfl
  intro t ht Y hYU z
  by_cases ha : t = a
  · subst t
    rw [← he a ⟨le_rfl, (EntryWeakProofs.weakData_lift_window_strict
      D hi.base hi.profile hi.band G.level k).le⟩ Y hYU z,
      hc a ⟨le_rfl, (EntryWeakProofs.weakData_lift_window_strict
        D hi.base hi.profile hi.band G.level k).le⟩ Y hYU z]
    simp only [cw, EntryWeakProofs.independentTimeWindowSource,
      Set.mem_Ioc, lt_self_iff_false, false_and, ite_false]
    exact (hp.initial_zero Y (hUΩ hYU) z).symm
  · have ht' : t ∈ Ioc a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm ha), ht.2⟩
    simpa only [cw, EntryWeakProofs.independentTimeWindowSource, ite_eq_left ht']
      using he t ht Y hYU z

/-- The literal forcing of every positive canonical path rank has a centered
local model with any prescribed finite reserve. The existing rank induction
supplies all predecessor bounds; no time smoothness of the contexts is presumed. -/
theorem native_path_coefficient_forcing_reserve {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (A : RealChain)
    (hA : IsAdmissibleChain D bw j₀ G.level k A ∧ Odd k)
    (R hh n m : ℕ) (hhh : hh ≤ h) (hn : 1 ≤ n) (hnN : n ≤ Mn.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : Fin (h + 1)) (Y₀ : Vec 2)
    (hY : Y₀ ∈ ladderOmega D bw j₀ G.level k A (Mn.lenFactor * liftLength D G.level)) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let edge := pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩
    let a := D.slotStart G.level k / D.cellScaleSq G.level
    let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let Q := familyLiftData D G.level k A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ :=
      fun Y => WeakEntryProofs.nativeWindowResponseLinear D hi.profile G.level
      k hA.2 A ρ edge 1 le_rfl a b
      (EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level k).le Y
    let Cc := WeakEntryProofs.weakLiftInverseCoefficients Q inv Mn.N
    ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → ℝ),
      IsOpen U ∧ Y₀ ∈ U ∧ U ⊆ ladderOmega D bw j₀ G.level k A ρ ∧
      Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
      (∀ t Y, ∫ z in AVenhance.unitCube, g t z Y = 0) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
        g t z Y = WeakEntryProofs.weakLiftCoefficientForcing Q Cc hh n m α v u t z Y := by
  classical
  dsimp only
  obtain ⟨kI, hcontext⟩ := hi.context
  let ρ := Mn.lenFactor * liftLength D G.level
  let edge := pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩
  let a := D.slotStart G.level k / D.cellScaleSq G.level
  let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let Ω := ladderOmega D bw j₀ G.level k A ρ
  let Q := familyLiftData D G.level k A ρ edge
  have hab := EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level k
  let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ :=
    fun Y => WeakEntryProofs.nativeWindowResponseLinear D hi.profile G.level
    k hA.2 A ρ edge 1 le_rfl a b hab.le Y
  let Cc := WeakEntryProofs.weakLiftInverseCoefficients Q inv Mn.N
  let S := R + 2 * Dm + 4
  let base := S + Mn.N + Dm + 10
  have hbase : 2 * Dm + 1 + 4 ≤ base := by dsimp only [base, S]; omega
  have hν := EntryWeakProofs.weakData_kap_pos D hi.base hi.profile hi.band G.level
  have hedge := StageSuccessor.context_path_local_reserves hi.base hi.profile hi.band hi.bandwidth
    G hcontext π k hA.2 ρ A hA.1
  have hp := WeakEntryProofs.native_full_lift_rank_induction D hi.profile hi.base G.level
    hν k hA.2 A hA.1.2.2.1 ρ edge a b hab 1 le_rfl base Mn.N h hi.order hbase Ω
    (isOpen_ladderOmega D bw j₀ G.level k A ρ) hedge
  have hzero (p : ℕ) (hp : p ≠ 0) : Cc p 0 = 0 := by
    funext l β t X z v u
    exact WeakEntryProofs.weakLiftInverseCoefficients_positive_grade_zero Q inv Mn.N p
      (by omega) l β t X z v u
  have hroom (p q : ℕ) : S + n + Dm + 2 ≤
      WeakEntryProofs.weakLiftRankReserve Dm base Mn.N h p q := by
    have hb := WeakEntryProofs.weakLiftRankReserve_base Dm base Mn.N h p q
    exact (show S + n + Dm + 2 ≤ base + 1 by dsimp only [base]; omega).trans hb
  have Pd := WeakEntryProofs.localFullLiftPredecessors_of_rank_properties
    (S + n + Dm + 2) a b Ω Y₀ hY Cc Mn.N hh n
    (WeakEntryProofs.weakLiftRankReserve Dm base Mn.N h)
    (fun p q _ _ _ => hroom p q)
    (fun p q hpq hq hqN l hl β v u => hp p q
      (by rcases hpq with hpq | ⟨rfl, _⟩ <;> omega) hq hqN l hl β v u)
    hzero (WeakEntryProofs.weakLiftInverseCoefficients_cutoff Q inv Mn.N)
  obtain ⟨V, edge', hV, hYV, he, ⟨Qe⟩⟩ := hedge (S + n + 1) Y₀ hY
  obtain ⟨U, g, hU, hYU, hUΩ, ⟨Qg⟩, hgm, heq⟩ :=
    WeakEntryProofs.native_full_cell_source_local_reserve D hi.profile hi.base G.level hν
      k hA.2 A hA.1.2.2.1 ρ edge S (by dsimp only [S]; omega) hi.order a b hab.le Ω
      (isOpen_ladderOmega D bw j₀ G.level k A ρ) Y₀ hY inv Mn.N hh n hn hnN
      (by dsimp only [S]; omega) V hV hYV edge' he Qe
      Pd.initial_zero Pd.local_reserve Pd.mean_zero m hm α v u
  exact ⟨U, g, hU, hYU, hUΩ, ⟨Qg.restrictOrder R (by dsimp only [S]; omega)⟩, hgm, heq⟩

/-- The same canonical path coefficient solves its cell equation at every finite
fast order. Increasing the requested reserve does not replace the array. -/
theorem native_path_coefficient_cell_inverse {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (A : RealChain)
    (hA : IsAdmissibleChain D bw j₀ G.level k A ∧ Odd k)
    (R hh n m : ℕ) (hR : 1 ≤ R) (hhh : hh ≤ h)
    (hn : 1 ≤ n) (hnN : n ≤ Mn.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : Fin (h + 1)) (Y : Vec 2)
    (hY : Y ∈ ladderOmega D bw j₀ G.level k A (Mn.lenFactor * liftLength D G.level)) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let edge := pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩
    let a := D.slotStart G.level k / D.cellScaleSq G.level
    let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let Q := familyLiftData D G.level k A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ :=
      fun Y => WeakEntryProofs.nativeWindowResponseLinear D hi.profile G.level
        k hA.2 A ρ edge 1 le_rfl a b
        (EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level k).le Y
    let Cc := WeakEntryProofs.weakLiftInverseCoefficients Q inv Mn.N
    IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v R a b 0
      (fun t z => WeakEntryProofs.weakLiftCoefficientForcing Q Cc hh n m α v u t z Y)
      (fun t z => Cc hh n m α t Y z v u 1) := by
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let edge := pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩
  let a := D.slotStart G.level k / D.cellScaleSq G.level
  let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let Ω := ladderOmega D bw j₀ G.level k A ρ
  have hab := EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level k
  have hsource Y₀ (hY₀ : Y₀ ∈ Ω) :=
    native_path_coefficient_forcing_reserve hi π k A hA (3 * R + 5) hh n m
      hhh hn hnN hm α v u Y₀ hY₀
  have hs : let Q := familyLiftData D G.level k A ρ edge
      let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ :=
        fun Y => WeakEntryProofs.nativeWindowResponseLinear D hi.profile G.level
          k hA.2 A ρ edge 1 le_rfl a b hab.le Y
      let Cc := WeakEntryProofs.weakLiftInverseCoefficients Q inv Mn.N
      ∀ Y₀ ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → ℝ),
        IsOpen U ∧ Y₀ ∈ U ∧
        Nonempty (EntryWeakProofs.IndependentParameterSourceReserve (3 * R + 5) g) ∧
        (∀ t Y, ∫ z in AVenhance.unitCube, g t z Y = 0) ∧
        ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
          g t z Y = WeakEntryProofs.weakLiftCoefficientForcing Q Cc hh n m α v u t z Y := by
    dsimp only
    intro Y₀ hY₀
    obtain ⟨U, g, hU, hYU, _hUΩ, hg, hgm, heq⟩ := hsource Y₀ hY₀
    exact ⟨U, g, hU, hYU, hg, hgm, heq⟩
  exact (WeakEntryProofs.native_full_lift_rank_response D hi.profile hi.base G.level
    (EntryWeakProofs.weakData_kap_pos D hi.base hi.profile hi.band G.level)
    k hA.2 A hA.1.2.2.1 ρ edge a b hab 1 le_rfl R (R + 4) hR
    (by omega) (by omega) le_rfl Mn.N hh n m hn hnN hm α v u Ω
    (isOpen_ladderOmega D bw j₀ G.level k A ρ) hs).1 Y hY

/-- The literal time right-hand side of a canonical path coefficient has a
bounded local model at every joint spatial order, including the initial time. -/
theorem native_path_coefficient_rhs_reserve {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (A : RealChain)
    (hA : IsAdmissibleChain D bw j₀ G.level k A ∧ Odd k)
    (R hh n m : ℕ) (hhh : hh ≤ h) (hn : 1 ≤ n) (hnN : n ≤ Mn.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : Fin (h + 1)) (Y₀ : Vec 2)
    (hY : Y₀ ∈ ladderOmega D bw j₀ G.level k A (Mn.lenFactor * liftLength D G.level)) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let edge := pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩
    let a := D.slotStart G.level k / D.cellScaleSq G.level
    let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let Q := familyLiftData D G.level k A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ :=
      fun Y => WeakEntryProofs.nativeWindowResponseLinear D hi.profile G.level
        k hA.2 A ρ edge 1 le_rfl a b
        (EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level k).le Y
    let Cc := WeakEntryProofs.weakLiftInverseCoefficients Q inv Mn.N
    ∃ (U : Set (Vec 2)) (df : ℝ → Vec 2 → Vec 2 → ℝ),
      IsOpen U ∧ Y₀ ∈ U ∧ U ⊆ ladderOmega D bw j₀ G.level k A ρ ∧
      Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R df) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
        df t z Y = -cellOperator (Q.G t Y) (Q.v t)
          (fun w => Cc hh n m α t Y w v u 1) z +
          WeakEntryProofs.weakLiftCoefficientForcing Q Cc hh n m α v u t z Y := by
  classical
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let edge := pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩
  let a := D.slotStart G.level k / D.cellScaleSq G.level
  let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let Q := familyLiftData D G.level k A ρ edge
  have hab := EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level k
  let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ :=
    fun Y => WeakEntryProofs.nativeWindowResponseLinear D hi.profile G.level
      k hA.2 A ρ edge 1 le_rfl a b hab.le Y
  let Cc := WeakEntryProofs.weakLiftInverseCoefficients Q inv Mn.N
  obtain ⟨Uc, c, hUc, hYc, hUcΩ, ⟨Qc⟩, hec⟩ :=
    native_path_coefficient_local_reserve hi π k A hA (R + 2) hh n m
      hhh hn hnN hm α v u Y₀ hY
  obtain ⟨Ug, g, hUg, hYg, _hUgΩ, ⟨Qg⟩, _hgm, heg⟩ :=
    native_path_coefficient_forcing_reserve hi π k A hA R hh n m
      hhh hn hnN hm α v u Y₀ hY
  obtain ⟨Gm, Um, hUm, hYm, ⟨QG⟩, heG⟩ :=
    WeakEntryProofs.native_local_metric_joint_reserve D hi.profile G.level k A hA.1.2.2.1
      ρ edge a b hab.le R Y₀
  have Qpulse : EntryWeakProofs.JointSourceReserve R (fun t z (_ : Vec 2) => Q.v t z) :=
    EntryWeakProofs.pulseJointSourceReserve R hi.base
      (EntryWeakProofs.weakData_kap_pos D hi.base hi.profile hi.band G.level) hi.profile hA.2
  let df := fun t z Y => -cellOperator (Gm t Y) (Q.v t) (fun w => c Y t w) z + g t z Y
  have Qdf : EntryWeakProofs.IndependentParameterSourceReserve R df :=
    native_cell_rhs_source_reserve R Gm Q.v g (fun t z Y => c Y t z)
      (fun i j => WeakEntryProofs.independentReserveOfJoint (QG i j))
      (fun i => (WeakEntryProofs.independentReserveOfJoint Qpulse).map
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i)) Qg Qc
  refine ⟨Uc ∩ Ug ∩ Um, df, (hUc.inter hUg).inter hUm, ⟨⟨hYc, hYg⟩, hYm⟩,
    (fun Y hY => hUcΩ hY.1.1), ⟨Qdf⟩, ?_⟩
  intro t ht Y hYU z
  have hec' : (fun w => c Y t w) = (fun w => Cc hh n m α t Y w v u 1) := by
    funext w
    rw [hec t ht Y hYU.1.1 w]
    have hmem := hUcΩ hYU.1.1
    simp only [StageSuccessor.pathLiftFamily, dite_eq_left hA,
      WeakEntryProofs.weakLiftCarrierRestriction, ite_eq_left (Or.inr hmem)]
    rfl
  dsimp only [df]
  rw [hec', heG t ht Y hYU.2, heg t ht Y hYU.1.2 z]

/-- Every slow offset of an actual native history is admissible. -/
theorem native_actual_ladderOmega_eq_univ {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    (p : OddSlot) (ρ : ℝ) : ladderOmega D bw j₀ G.level p.1 (G.actual p).1 ρ = univ := by
  apply Set.eq_univ_of_forall
  intro X
  change IsAdmissibleChain D bw j₀ G.level p.1 ((G.actual p).1.recenter D (ρ • X))
  rw [hi.natural.2.2.1 p]
  exact Providers.QuietAtlas.isAdmissibleChain_nativeChain_recenter
    (D := D) (b := bw) (by have := hi.level; omega) (by have := hi.level; omega) p (ρ • X)

/-- The actual native context has every qualitative stage-data reserve on its
cell window, without the normalized bounds of `IsLiftSetting`. -/
theorem native_stage_goodDat {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    (p : OddSlot) (R : ℕ) (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    ∀ t ∈ Icc a b, Providers.PathDecomp.GoodDat R t
      (Providers.PathDecomp.stageDat G (D.cellScaleSq G.level)
        (ρ / D.eps (G.level - 1)) p (G.actual p) v u γ) := by
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  have hΩ := native_actual_ladderOmega_eq_univ hi p ρ
  obtain ⟨kI, hcontext⟩ := hi.context
  intro t ht d α κ
  by_cases hd : d ≤ Dm
  · obtain ⟨hs, _, _⟩ := native_context_flux_local_data hi.base hi.bandwidth hcontext
      p (G.actual p).1 (G.actual p).2 ρ (Icc a b)
      (fun r => D.cellScaleSq G.level * r) (continuous_const.mul continuous_id)
      (fun r hr => EntryWeakProofs.weak_lift_clock_in_pulse_window D hi.base hi.profile hi.band
        G.level p.1 r hr) v u γ d α κ
    have hs' : ContDiff ℝ (⊤ : ℕ∞) (fun X : Vec 2 × Vec 2 =>
        G.fam.flux p (G.actual p) v u γ d α (D.cellScaleSq G.level * t)
          ((ρ / D.eps (G.level - 1)) • X.2) X.1 κ) := by
      simpa only [hΩ, Set.mem_univ, Set.ofPred_true, contDiffOn_univ] using hs t ht
    refine ⟨?_, ?_⟩
    · change ContDiff ℝ (R : ℕ∞) (fun X : Vec 2 × Vec 2 =>
        (if d ≤ Dm then G.fam.flux p (G.actual p) v u γ d α
          (D.cellScaleSq G.level * t) ((ρ / D.eps (G.level - 1)) • X.1) X.2 else 0) κ)
      simp only [ite_eq_left hd]
      exact (hs'.comp (contDiff_snd.prodMk contDiff_fst)).of_le
        (by exact_mod_cast (show (R : ℕ∞) ≤ ⊤ from le_top))
    · intro X n z
      simpa only [Providers.PathDecomp.stageDat, ite_eq_left hd] using
        congrFun (G.fam.flux_periodic p (G.actual p) v u γ d α
          (D.cellScaleSq G.level * t) ((ρ / D.eps (G.level - 1)) • X) n z) κ
  · exact GoodField.zero.congr (fun X z => by
      simp only [Providers.PathDecomp.stageDat, ite_eq_right hd, Pi.zero_apply])

private theorem native_sourceCoeff_empty {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {K : ℕ}
    (edge : ConstituentEdges K h) (he : ∀ v u d, edge v u d = [])
    (η : ℝ) (j : ℕ) (t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) :
    sourceCoeff edge η j t Φ = 0 := by
  have hflux (ε : ℝ) (k : Fin 2) : sourceFlux edge η ε t Φ k = 0 := by
    funext X z v
    simp only [sourceFlux, he, List.map_nil, List.sum_nil, Finset.sum_const_zero,
      Pi.zero_apply]
  have hop (ε : ℝ) : sourceOp edge η ε t Φ = 0 := by
    funext X z
    simp only [sourceOp, hflux, dEps, fastPartial, slowPartial, Pi.zero_apply,
      fderiv_fun_const, zero_apply, smul_zero, add_zero,
      Finset.sum_const_zero]
  funext X z
  simp only [sourceCoeff, hop, Pi.zero_apply, iteratedDeriv_const, ite_self, smul_zero]

private theorem native_empty_source_degree_congr {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {K K' : ℕ}
    (Q : LiftOperatorData ι h K) (Q' : LiftOperatorData ι h K')
    (he : ∀ v u d, Q.edge v u d = []) (he' : ∀ v u d, Q'.edge v u d = [])
    (hη : Q.η = Q'.η) (hG : Q.G = Q'.G) (hv : Q.v = Q'.v)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i) (g n : ℕ) :
    liftCellSource Q Cc f g n = liftCellSource Q' Cc f g n := by
  have hA (g n : ℕ) : liftA Q Cc f g n = liftA Q' Cc f g n := by
    funext t X z
    simp only [liftA, native_sourceCoeff_empty Q.edge he,
      native_sourceCoeff_empty Q'.edge he', Pi.zero_apply, Finset.sum_const_zero,
      ite_self, sub_zero, hη, hG, hv]
  have hm (g n : ℕ) : liftMean Q Cc f g n = liftMean Q' Cc f g n := by
    funext t X
    simp only [liftMean, hA]
  funext t X z
  simp only [liftCellSource, hA, hm]

private theorem native_empty_sequence_degree_congr {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] {K K' : ℕ}
    (Q : LiftOperatorData ι h K) (Q' : LiftOperatorData ι h K')
    (he : ∀ v u d, Q.edge v u d = []) (he' : ∀ v u d, Q'.edge v u d = [])
    (hη : Q.η = Q'.η) (hG : Q.G = Q'.G) (hv : Q.v = Q'.v)
    {sX sZ N H : ℕ} {a b : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hc : IsLiftSequence Q sX sZ a b N H Cc) :
    IsLiftSequence Q' sX sZ a b N H Cc := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, ?_⟩
  intro g hg n hn hnN f hf X
  have hi := hc.2.2.2.2.2.2 g hg n hn hnN f hf X
  rw [hG, hv] at hi
  apply CycleComparison.Lift.cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hi
  intro t _
  exact congrFun (congrFun (native_empty_source_degree_congr Q Q' he he' hη hG hv Cc
    (fun _ => f) g n) t) X

/-- Qualitative path decomposition at the actual menu length, for orders at
least two. It uses arbitrary elliptic window bounds and the existing cell uniqueness. -/
theorem native_stage_path_step_hypotheses
    [∀ r, FiniteDimensional ℝ (hr r)] {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G) (hD : 2 ≤ Dm)
    (p : OddSlot) (H sX sZ : ℕ) (hX : Mn.N + 1 + Dm ≤ sX) (hZ : Mn.N + 1 + Dm ≤ sZ) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let A := (G.actual p).1
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let F := Providers.PathDecomp.stageFam G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p)
    let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
      hi.base hi.profile hi.band ρ Mn.N π p.1 A
    let Lift := Providers.PathDecomp.stLift G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp
    let Arise := Providers.PathDecomp.stArise G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p) H
    let Q := familyLiftData D G.level p.1 A ρ (G.fam.fiber p (G.actual p))
    let Qc := Providers.PathDecomp.stQc G G.level p.1 A ρ p (G.actual p) H
    Providers.PathDecomp.StepHyp F Q Lift Qc Arise sX sZ a b Mn.N Mn.N H ∧
      ∀ L cd, Arise L cd → L ≤ H →
        Providers.PathDecomp.StepHyp (Providers.PathDecomp.chainFam cd) (Qc L cd)
          Lift Qc Arise sX sZ a b Mn.N Mn.N L := by
  classical
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let A := (G.actual p).1
  let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let lam := ρ / D.eps (G.level - 1)
  let F := Providers.PathDecomp.stageFam G (D.cellScaleSq G.level) lam p (G.actual p)
  let Q := familyLiftData D G.level p.1 A ρ (G.fam.fiber p (G.actual p))
  let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
    hi.base hi.profile hi.band ρ Mn.N π p.1 A
  let Lift := Providers.PathDecomp.stLift G (D.cellScaleSq G.level) lam p (G.actual p) H Cp
  let Qc := Providers.PathDecomp.stQc G G.level p.1 A ρ p (G.actual p) H
  let Arise := Providers.PathDecomp.stArise G (D.cellScaleSq G.level) lam p (G.actual p) H
  have hab : a ≤ b :=
    (EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level p.1).le
  have hW : ∀ X, ∃ lo up Mv : ℝ,
      Uniqueness.WindowData (fun t => Matrix.of (Q.G t X)) Q.v a b lo up Mv := by
    intro X
    obtain ⟨lo, up, hlo, hq⟩ := Providers.GenSem.familyLiftData_pos_window D hi.profile
      G.level p.1 A ρ (G.fam.fiber p (G.actual p)) a b X
    obtain ⟨Mv, hv⟩ := Providers.GenSem.familyLiftData_v_bounded D hi.profile G.level p.2
      A ρ (G.fam.fiber p (G.actual p))
    exact ⟨lo, up, Mv, Uniqueness.windowData_of_elliptic _ _ a b lo up Mv
      (fun t => Providers.GenSem.familyLiftData_symm D G.level p.1 A ρ
        (G.fam.fiber p (G.actual p)) t X 0 1)
      hlo hq (fun t _ z => hv t z)⟩
  have hLs (g : ℕ) (cd : Fin g → Providers.PathDecomp.StepDat) (hA : Arise g cd) :
      IsLiftSequence (Qc g cd) sX sZ a b Mn.N g (Lift g cd) := by
    have hA' : Providers.PathDecomp.stArise G (D.cellScaleSq G.level)
        (ρ / D.eps (G.level - 1)) p
        (G.actual p) H g cd := hA
    have heQ : Qc g cd = familyLiftData D G.level p.1 A ρ
        (pathEdges G (Classical.choose hA.2) p (G.actual p)) := by
      simp only [Qc, Providers.PathDecomp.stQc, dite_eq_left hA']
    have heL : Lift g cd = Cp g (Classical.choose hA.2) := by
      simp only [Lift, lam, Providers.PathDecomp.stLift, dite_eq_left hA']
    rw [heQ, heL]
    have hseq := StageSuccessor.path_lift_family hi (Classical.choose hA.2) sX sZ
      p.1 A ⟨(G.actual p).2, p.2⟩
    rw [native_actual_ladderOmega_eq_univ hi p ρ] at hseq
    exact WeakEntryProofs.liftSequence_of_on_univ _ sX sZ a b Mn.N g _ hseq
  have hdat (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
      ∀ t ∈ Icc a b, Providers.PathDecomp.GoodDat (Mn.N + 1 + Dm) t (F.dat v u γ) :=
    native_stage_goodDat hi p (Mn.N + 1 + Dm) v u γ
  have hcd (g : ℕ) (cd : Fin g → Providers.PathDecomp.StepDat) (hA : Arise g cd) :
      ∀ i, ∀ t ∈ Icc a b, Providers.PathDecomp.GoodDat (Mn.N + 1 + Dm) t (cd i) := by
    obtain ⟨_, π, rfl⟩ := hA
    intro i
    exact hdat (π.step i).1 (π.step i).2.1 (π.step i).2.2
  have hGr : ∀ t ∈ Icc a b, ∀ i j,
      ContDiff ℝ ((Mn.N + 2 : ℕ) : ℕ∞) (fun X => Q.G t X i j) := by
    intro t _ i j
    exact ((WeakEntryProofs.familyLiftData_metric_spacetime_smooth D hi.profile G.level p.1 A
      (G.actual p).2.2.2.1 ρ (G.fam.fiber p (G.actual p)) i j).comp
      (contDiff_const.prodMk contDiff_id)).of_le
        (by exact_mod_cast (show ((Mn.N + 2 : ℕ) : ℕ∞) ≤ ⊤ from le_top))
  have hvr : ∀ t ∈ Icc a b, ∀ κ,
      GoodField (Mn.N + 2) (fun (_ z : Vec 2) => Q.v t z κ) := by
    intro t _ κ
    have hν := EntryWeakProofs.weakData_kap_pos D hi.base hi.profile hi.band G.level
    refine ⟨?_, fun _ n z => ?_⟩
    · have hv := EntryWeakProofs.normalizedPulseDrift_contDiff
        (α := D.α) (q := D.q) (m := G.level) (ζ := D.ζ) hi.base hν p.2 t
      exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) κ).contDiff.comp
        (hv.comp contDiff_snd)).of_le
          (by exact_mod_cast (show ((Mn.N + 2 : ℕ) : ℕ∞) ≤ ⊤ from le_top))
    · exact congrFun (EntryWeakProofs.normalizedPulseDrift_periodic hi.base hν p.2 t n z) κ
  have hs : Providers.PathDecomp.StepHyp F Q Lift Qc Arise sX sZ a b Mn.N Mn.N H := {
    hQ := Providers.PathDecomp.hasFamFlux_fiber G G.level p.1 A ρ p (G.actual p)
    hab := hab
    hW := hW
    hQc := fun _ _ hA => Providers.PathDecomp.StageSetting.qc_flux hA
    hη := fun _ _ => rfl
    hG := fun _ _ => rfl
    hv := fun _ _ => rfl
    hLs := hLs
    hcd := hcd
    hdat := hdat
    hGr := hGr
    hvr := hvr
    hD2 := hD
    hsX := hX
    hsZ := hZ
    hNr := le_rfl
    hArise := fun _ _ _ q hg => ⟨hg, Providers.PathDecomp.stage_walk_path q⟩ }
  have hsc : ∀ L cd, Arise L cd → L ≤ H →
      Providers.PathDecomp.StepHyp (Providers.PathDecomp.chainFam cd) (Qc L cd)
        Lift Qc Arise sX sZ a b Mn.N Mn.N L := by
    intro L cd hA _
    refine {
      hQ := Providers.PathDecomp.StageSetting.qc_flux hA
      hab := hab
      hW := hW
      hQc := fun _ _ hB => Providers.PathDecomp.StageSetting.qc_flux hB
      hη := fun _ _ => rfl
      hG := fun _ _ => rfl
      hv := fun _ _ => rfl
      hLs := hLs
      hcd := hcd
      hdat := ?_
      hGr := hGr
      hvr := hvr
      hD2 := hD
      hsX := hX
      hsZ := hZ
      hNr := le_rfl
      hArise := fun _ _ _ τ hg => Providers.PathDecomp.StageSetting.arise_chain hA τ hg }
    intro v i γ
    exact hcd L cd hA ⟨i.val, by have := γ.down; have := v.isLt; omega⟩
  exact ⟨hs, hsc⟩

/-- Full native coefficient decomposition, from the shared path certificates. -/
theorem native_stage_path_decomposition_of_two_le
    [∀ r, FiniteDimensional ℝ (hr r)] {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G) (hD : 2 ≤ Dm)
    (p : OddSlot) (H sX sZ : ℕ) (hX : Mn.N + 1 + Dm ≤ sX) (hZ : Mn.N + 1 + Dm ≤ sZ) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let A := (G.actual p).1
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let F := Providers.PathDecomp.stageFam G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p)
    let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
      hi.base hi.profile hi.band ρ Mn.N π p.1 A
    let Lift := Providers.PathDecomp.stLift G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp
    let Arise := Providers.PathDecomp.stArise G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p) H
    ∀ Cc : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root),
      IsLiftSequence (familyLiftData D G.level p.1 A ρ (G.fam.fiber p (G.actual p)))
        sX sZ a b Mn.N H Cc →
      ∀ g ≤ H, ∀ n, Uniqueness.CoeffEq Cc
        (Providers.PathDecomp.cand F (Providers.PathDecomp.topOf Lift Arise)) a b g n := by
  classical
  obtain ⟨hs, hsc⟩ := native_stage_path_step_hypotheses hi hD p H sX sZ hX hZ
  dsimp only
  intro Cc hCc
  exact Providers.PathDecomp.decomp hs hsc hCc

/-- An order-one native stage has no edges. Padding the empty source degree
permits the qualitative decomposition without discarding its grade-zero correctors. -/
theorem native_stage_path_decomposition_order_one
    [∀ r, FiniteDimensional ℝ (hr r)] {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr 1 bw j₀} (hi : StageSuccessor.Input P Mn G)
    (p : OddSlot) (H sX sZ : ℕ) (hX : Mn.N + 3 ≤ sX) (hZ : Mn.N + 3 ≤ sZ) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let A := (G.actual p).1
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let F := Providers.PathDecomp.stageFam G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p)
    let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
      hi.base hi.profile hi.band ρ Mn.N π p.1 A
    let Lift := Providers.PathDecomp.stLift G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp
    let Arise := Providers.PathDecomp.stArise G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p) H
    ∀ Cc : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root),
      IsLiftSequence (familyLiftData D G.level p.1 A ρ (G.fam.fiber p (G.actual p)))
        sX sZ a b Mn.N H Cc →
      ∀ g ≤ H, ∀ n, Uniqueness.CoeffEq Cc
        (Providers.PathDecomp.cand F (Providers.PathDecomp.topOf Lift Arise)) a b g n := by
  classical
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let A := (G.actual p).1
  let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let lam := ρ / D.eps (G.level - 1)
  let F := Providers.PathDecomp.stageFam G (D.cellScaleSq G.level) lam p (G.actual p)
  let Q : LiftOperatorData (CompIn G.comps) (fun v => hr v.1.root) 2 :=
    familyLiftData D G.level p.1 A ρ (fun _ _ _ => [])
  let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
    hi.base hi.profile hi.band ρ Mn.N π p.1 A
  let Lift := Providers.PathDecomp.stLift G (D.cellScaleSq G.level) lam p (G.actual p) H Cp
  let Qc := fun (g : ℕ) (_ : Fin g → Providers.PathDecomp.StepDat) =>
    familyLiftData (Dm := 2) (hv := fun _ : Fin (g + 1) => ℝ)
      D G.level p.1 A ρ (fun _ _ _ => [])
  let Arise := Providers.PathDecomp.stArise G (D.cellScaleSq G.level) lam p (G.actual p) H
  have hab : a ≤ b :=
    (EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level p.1).le
  have hW : ∀ X, ∃ lo up Mv : ℝ,
      Uniqueness.WindowData (fun t => Matrix.of (Q.G t X)) Q.v a b lo up Mv := by
    intro X
    obtain ⟨lo, up, hlo, hq⟩ := Providers.GenSem.familyLiftData_pos_window D hi.profile
      G.level p.1 A ρ (G.fam.fiber p (G.actual p)) a b X
    obtain ⟨Mv, hv⟩ := Providers.GenSem.familyLiftData_v_bounded D hi.profile G.level p.2
      A ρ (G.fam.fiber p (G.actual p))
    exact ⟨lo, up, Mv, Uniqueness.windowData_of_elliptic _ _ a b lo up Mv
      (fun t => Providers.GenSem.familyLiftData_symm D G.level p.1 A ρ
        (G.fam.fiber p (G.actual p)) t X 0 1)
      hlo hq (fun t _ z => hv t z)⟩
  have hempty (v u : CompIn G.comps) (γ : G.fam.Γ v u) : False := by
    have h₂ := (G.fam.identity v u γ).two_le
    have h₁ := (G.fam.identity v u γ).le_D
    omega
  have hzero (g : ℕ) (cd : Fin g → Providers.PathDecomp.StepDat) (hA : Arise g cd) :
      g = 0 := by
    by_contra hg
    let π := Classical.choose hA.2
    exact hempty (π.step ⟨0, Nat.pos_of_ne_zero hg⟩).1
      (π.step ⟨0, Nat.pos_of_ne_zero hg⟩).2.1 (π.step ⟨0, Nat.pos_of_ne_zero hg⟩).2.2
  have hLs (g : ℕ) (cd : Fin g → Providers.PathDecomp.StepDat) (hA : Arise g cd) :
      IsLiftSequence (Qc g cd) sX sZ a b Mn.N g (Lift g cd) := by
    have hA' : Providers.PathDecomp.stArise G (D.cellScaleSq G.level)
        (ρ / D.eps (G.level - 1)) p (G.actual p) H g cd := hA
    have heL : Lift g cd = Cp g (Classical.choose hA.2) := by
      simp only [Lift, lam, Providers.PathDecomp.stLift, dite_eq_left hA']
    rw [heL]
    have hseq := StageSuccessor.path_lift_family hi (Classical.choose hA.2) sX sZ
      p.1 A ⟨(G.actual p).2, p.2⟩
    rw [native_actual_ladderOmega_eq_univ hi p ρ] at hseq
    let Qo := familyLiftData D G.level p.1 A ρ
      (pathEdges G (Classical.choose hA.2) p (G.actual p))
    have hc : IsLiftSequence Qo sX sZ a b Mn.N g (Cp g (Classical.choose hA.2)) :=
      WeakEntryProofs.liftSequence_of_on_univ _ sX sZ a b Mn.N g _ hseq
    have heo : ∀ v u d, Qo.edge v u d = [] := by
      intro v u d
      have := (Finset.mem_Icc.mp d.2)
      omega
    have hep : ∀ v u d, (Qc g cd).edge v u d = [] := by
      intro v u d
      simp only [Qc, familyLiftData, liftEdges, List.map_nil]
    exact native_empty_sequence_degree_congr Qo (Qc g cd) heo hep rfl rfl rfl hc
  have hQc (g : ℕ) (cd : Fin g → Providers.PathDecomp.StepDat) (hA : Arise g cd) :
      Providers.PathDecomp.HasFamFlux (Qc g cd) (Providers.PathDecomp.chainFam cd) := by
    have hg := hzero g cd hA
    subst g
    intro η ε t Φ κ X z v
    have hi (u : Fin 1) : IsEmpty ((Providers.PathDecomp.chainFam cd).Γ v u) :=
      ⟨fun γ => by have := γ.down; have := v.isLt; have := u.isLt; omega⟩
    simp only [Qc, familyLiftData, liftEdges, List.map_nil, sourceFlux, List.sum_nil,
      Finset.sum_const_zero]
    exact (Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun _ _ =>
      @Fintype.sum_empty _ _ _ _ (hi u) _).symm
  have hdat (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
      ∀ t ∈ Icc a b, Providers.PathDecomp.GoodDat (Mn.N + 3) t (F.dat v u γ) :=
    (hempty v u γ).elim
  have hcd (g : ℕ) (cd : Fin g → Providers.PathDecomp.StepDat) (hA : Arise g cd) :
      ∀ i, ∀ t ∈ Icc a b, Providers.PathDecomp.GoodDat (Mn.N + 3) t (cd i) := by
    have hg := hzero g cd hA
    subst g
    exact fun i => Fin.elim0 i
  have hGr : ∀ t ∈ Icc a b, ∀ i j,
      ContDiff ℝ ((Mn.N + 2 : ℕ) : ℕ∞) (fun X => Q.G t X i j) := by
    intro t _ i j
    exact ((WeakEntryProofs.familyLiftData_metric_spacetime_smooth D hi.profile G.level p.1 A
      (G.actual p).2.2.2.1 ρ (G.fam.fiber p (G.actual p)) i j).comp
      (contDiff_const.prodMk contDiff_id)).of_le
        (by exact_mod_cast (show ((Mn.N + 2 : ℕ) : ℕ∞) ≤ ⊤ from le_top))
  have hvr : ∀ t ∈ Icc a b, ∀ κ,
      GoodField (Mn.N + 2) (fun (_ z : Vec 2) => Q.v t z κ) := by
    intro t _ κ
    have hν := EntryWeakProofs.weakData_kap_pos D hi.base hi.profile hi.band G.level
    refine ⟨?_, fun _ n z => ?_⟩
    · have hv := EntryWeakProofs.normalizedPulseDrift_contDiff
        (α := D.α) (q := D.q) (m := G.level) (ζ := D.ζ) hi.base hν p.2 t
      exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) κ).contDiff.comp
        (hv.comp contDiff_snd)).of_le
          (by exact_mod_cast (show ((Mn.N + 2 : ℕ) : ℕ∞) ≤ ⊤ from le_top))
    · exact congrFun (EntryWeakProofs.normalizedPulseDrift_periodic hi.base hν p.2 t n z) κ
  have hs : Providers.PathDecomp.StepHyp F Q Lift Qc Arise sX sZ a b Mn.N Mn.N H := {
    hQ := by
      intro η ε t Φ κ X z v
      have hi (u : CompIn G.comps) : IsEmpty (F.Γ v u) := ⟨hempty v u⟩
      simp only [Q, familyLiftData, liftEdges, List.map_nil, sourceFlux, List.sum_nil,
        Finset.sum_const_zero]
      exact (Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun _ _ =>
        @Fintype.sum_empty _ _ _ _ (hi u) _).symm
    hab := hab
    hW := hW
    hQc := fun _ _ hA => hQc _ _ hA
    hη := fun _ _ => rfl
    hG := fun _ _ => rfl
    hv := fun _ _ => rfl
    hLs := hLs
    hcd := hcd
    hdat := hdat
    hGr := hGr
    hvr := hvr
    hD2 := le_rfl
    hsX := hX
    hsZ := hZ
    hNr := le_rfl
    hArise := fun _ _ _ q hg => ⟨hg, Providers.PathDecomp.stage_walk_path q⟩ }
  have hsc : ∀ L cd, Arise L cd → L ≤ H →
      Providers.PathDecomp.StepHyp (Providers.PathDecomp.chainFam cd) (Qc L cd)
        Lift Qc Arise sX sZ a b Mn.N Mn.N L := by
    intro L cd hA _
    refine {
      hQ := hQc _ _ hA
      hab := hab
      hW := hW
      hQc := fun _ _ hB => hQc _ _ hB
      hη := fun _ _ => rfl
      hG := fun _ _ => rfl
      hv := fun _ _ => rfl
      hLs := hLs
      hcd := hcd
      hdat := ?_
      hGr := hGr
      hvr := hvr
      hD2 := le_rfl
      hsX := hX
      hsZ := hZ
      hNr := le_rfl
      hArise := fun _ _ _ τ hg => Providers.PathDecomp.StageSetting.arise_chain hA τ hg }
    intro v i γ
    exact hcd L cd hA ⟨i.val, by have := γ.down; have := v.isLt; omega⟩
  intro Cc hCc
  apply Providers.PathDecomp.decomp hs hsc
  let Qo := familyLiftData D G.level p.1 A ρ (G.fam.fiber p (G.actual p))
  have heo : ∀ v u d, Qo.edge v u d = [] := by
    intro v u d
    have := (Finset.mem_Icc.mp d.2)
    omega
  have hep : ∀ v u d, Q.edge v u d = [] := by
    intro v u d
    simp only [Q, familyLiftData, liftEdges, List.map_nil]
  exact native_empty_sequence_degree_congr Qo Q heo hep rfl rfl rfl hCc

/-- The actual-menu path sum built from the canonical scalar path arrays. -/
def nativeStagePathCandidate {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    (H : ℕ) (p : OddSlot) : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root) := by
  classical
  let ρ := Mn.lenFactor * liftLength D G.level
  let A := (G.actual p).1
  let F := Providers.PathDecomp.stageFam G (D.cellScaleSq G.level)
    (ρ / D.eps (G.level - 1)) p (G.actual p)
  let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
    hi.base hi.profile hi.band ρ Mn.N π p.1 A
  let Lift := Providers.PathDecomp.stLift G (D.cellScaleSq G.level)
    (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp
  let Arise := Providers.PathDecomp.stArise G (D.cellScaleSq G.level)
    (ρ / D.eps (G.level - 1)) p (G.actual p) H
  exact Providers.PathDecomp.cand F (Providers.PathDecomp.topOf Lift Arise)

/-- Full native path identification at every permitted order, including order one. -/
theorem native_stage_path_decomposition
    [∀ r, FiniteDimensional ℝ (hr r)] {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    (p : OddSlot) (H sX sZ : ℕ) (hX : Mn.N + 2 + Dm ≤ sX) (hZ : Mn.N + 2 + Dm ≤ sZ) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let A := (G.actual p).1
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let F := Providers.PathDecomp.stageFam G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p)
    let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
      hi.base hi.profile hi.band ρ Mn.N π p.1 A
    let Lift := Providers.PathDecomp.stLift G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp
    let Arise := Providers.PathDecomp.stArise G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p) H
    ∀ Cc : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root),
      IsLiftSequence (familyLiftData D G.level p.1 A ρ (G.fam.fiber p (G.actual p)))
        sX sZ a b Mn.N H Cc →
      ∀ g ≤ H, ∀ n, Uniqueness.CoeffEq Cc
        (Providers.PathDecomp.cand F (Providers.PathDecomp.topOf Lift Arise)) a b g n := by
  by_cases hD : 2 ≤ Dm
  · exact native_stage_path_decomposition_of_two_le hi hD p H sX sZ
      (by omega) (by omega)
  · have hD1 : Dm = 1 := by have := hi.order; omega
    subst Dm
    exact native_stage_path_decomposition_order_one hi p H sX sZ hX hZ

/-- The same canonical path candidate has every finite joint spatial reserve.
The scalar path producer supplies arbitrary orders before the finite path sum. -/
theorem native_stage_path_candidate_joint_contDiff {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    (H : ℕ) (p : OddSlot) (R : ℕ) (g : ℕ) (hg : g ≤ H) (n m : ℕ)
    (α : DerivativeWord2 m) (v u : CompIn G.comps) (t : ℝ)
    (ht : t ∈ Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)) :
    ContDiff ℝ (R : ℕ∞) (fun Z : Vec 2 × Vec 2 =>
      nativeStagePathCandidate hi H p g n m α t Z.1 Z.2 v u) := by
  classical
  let ρ := Mn.lenFactor * liftLength D G.level
  let lam := ρ / D.eps (G.level - 1)
  let F := Providers.PathDecomp.stageFam G (D.cellScaleSq G.level) lam p (G.actual p)
  let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
    hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
  let Arise := Providers.PathDecomp.stArise G (D.cellScaleSq G.level) lam p (G.actual p) H
  change ContDiff ℝ (R : ℕ∞) (fun Z : Vec 2 × Vec 2 =>
    ∑ q : F.Walk g u v, Providers.PathDecomp.topOf
      (Providers.PathDecomp.stLift G (D.cellScaleSq G.level) lam p (G.actual p) H Cp)
      Arise g (F.walkDat q) n m α t Z.1 Z.2 • F.compMap q)
  apply ContDiff.sum
  intro q _
  have hA : Arise g (F.walkDat q) := ⟨hg, Providers.PathDecomp.stage_walk_path q⟩
  simp only [Providers.PathDecomp.topOf, ite_eq_left hA, Providers.PathDecomp.topArr]
  have hA' : Providers.PathDecomp.stArise G (D.cellScaleSq G.level)
      (ρ / D.eps (G.level - 1)) p (G.actual p) H g (F.walkDat q) := hA
  have heL : Providers.PathDecomp.stLift G (D.cellScaleSq G.level) lam p (G.actual p)
      H Cp g (F.walkDat q) = Cp g (Classical.choose hA.2) := by
    simp only [lam, Providers.PathDecomp.stLift, dite_eq_left hA']
  rw [heL]
  have hseq := StageSuccessor.path_lift_family hi (Classical.choose hA.2) R R
    p.1 (G.actual p).1 ⟨(G.actual p).2, p.2⟩
  rw [native_actual_ladderOmega_eq_univ hi p ρ] at hseq
  have hc := WeakEntryProofs.liftSequence_of_on_univ _ R R _ _ Mn.N g _ hseq
  have hb := (hc.2.2.2.2.2.1 g le_rfl n m α (Fin.last g) 0 t ht).1
  exact ((hb.contDiff_uncurry le_rfl le_rfl).clm_apply contDiff_const).smul contDiff_const

open AVRegularity.Sobolev AVenhance

variable [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

section FiniteCoefficientCarrier
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift

end FiniteCoefficientCarrier

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- Every actual canonical path coefficient has its literal finite-past time
primitive, with an arbitrary native-history metric and the menu's slow length. -/
theorem native_path_coefficient_time_primitive {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (A : RealChain)
    (hA : IsAdmissibleChain D bw j₀ G.level k A ∧ Odd k)
    (hh n m : ℕ) (hhh : hh ≤ h) (hn : 1 ≤ n) (hnN : n ≤ Mn.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : Fin (h + 1)) (Y : Vec 2)
    (hY : Y ∈ ladderOmega D bw j₀ G.level k A (Mn.lenFactor * liftLength D G.level)) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let edge := pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩
    let a := D.slotStart G.level k / D.cellScaleSq G.level
    let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let Q := familyLiftData D G.level k A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ :=
      fun Y => WeakEntryProofs.nativeWindowResponseLinear D hi.profile G.level
        k hA.2 A ρ edge 1 le_rfl a b
        (EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level k).le Y
    let Cc := WeakEntryProofs.weakLiftInverseCoefficients Q inv Mn.N
    let c := fun t z => Cc hh n m α t Y z v u 1
    let g := fun t z => WeakEntryProofs.weakLiftCoefficientForcing Q Cc hh n m α v u t z Y
    ∀ t ∈ Icc a b, ∀ z,
      c t z - c a z = ∫ r in Ioc a t, -cellOperator (Q.G r Y) (Q.v r) (c r) z + g r z := by
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let edge := pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩
  let a := D.slotStart G.level k / D.cellScaleSq G.level
  let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let Q := familyLiftData D G.level k A ρ edge
  have hab := EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level k
  let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ :=
    fun Y => WeakEntryProofs.nativeWindowResponseLinear D hi.profile G.level
      k hA.2 A ρ edge 1 le_rfl a b hab.le Y
  let Cc := WeakEntryProofs.weakLiftInverseCoefficients Q inv Mn.N
  let c := fun t z => Cc hh n m α t Y z v u 1
  let g := fun t z => WeakEntryProofs.weakLiftCoefficientForcing Q Cc hh n m α v u t z Y
  have hc : IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v 2 a b 0 g c :=
    native_path_coefficient_cell_inverse hi π k A hA 2 hh n m (by omega)
      hhh hn hnN hm α v u Y hY
  obtain ⟨Ug, g', _hUg, hYg, _hUgΩ, ⟨Qg⟩, _hgm, heg⟩ :=
    native_path_coefficient_forcing_reserve hi π k A hA 0 hh n m
      hhh hn hnN hm α v u Y hY
  have hg (t : ℝ) (ht : t ∈ Icc a b) : Continuous (g t) :=
    ((Qg.regular t).comp (contDiff_id.prodMk (contDiff_const (c := Y)))).continuous.congr
      (fun z => heg t ht Y hYg z)
  obtain ⟨U, df, _hU, hYU, _hUΩ, ⟨Qdf⟩, heq⟩ :=
    native_path_coefficient_rhs_reserve hi π k A hA 0 hh n m
      hhh hn hnN hm α v u Y hY
  have hp := native_cell_inverse_primitive_of_reserved_rhs
    (fun t => Matrix.of (Q.G t Y)) Q.v le_rfl hab.le g c hc
    (fun t _ i j => Providers.GenSem.familyLiftData_symm D G.level k A ρ edge t Y i j)
    (fun t _ => (EntryWeakProofs.normalizedPulseDrift_contDiff hi.base
      (EntryWeakProofs.weakData_kap_pos D hi.base hi.profile hi.band G.level) hA.2 t).continuous)
    hg df Qdf Y (fun t ht z => heq t ht Y hYU z)
  intro t ht z
  exact (hp t ht z).trans (setIntegral_congr_fun (μ := volume) measurableSet_Ioc
    (fun r hr => heq r ⟨hr.1.le, hr.2.trans ht.2⟩ Y hYU z))

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- Canonical path coefficients supply the all-order local time data without
normalizing the metric or the menu length. -/
theorem native_path_coefficient_time_data {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (A : RealChain)
    (hA : IsAdmissibleChain D bw j₀ G.level k A ∧ Odd k)
    (hh n m : ℕ) (hhh : hh ≤ h) (hn : 1 ≤ n) (hnN : n ≤ Mn.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : Fin (h + 1)) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let edge := pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩
    let a := D.slotStart G.level k / D.cellScaleSq G.level
    let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let Q := familyLiftData D G.level k A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ :=
      fun Y => WeakEntryProofs.nativeWindowResponseLinear D hi.profile G.level
        k hA.2 A ρ edge 1 le_rfl a b
        (EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level k).le Y
    let Cc := WeakEntryProofs.weakLiftInverseCoefficients Q inv Mn.N
    let c := fun t z Y => Cc hh n m α t Y z v u 1
    let df := fun t z Y => -cellOperator (Q.G t Y) (Q.v t) (fun w => c t w Y) z +
      WeakEntryProofs.weakLiftCoefficientForcing Q Cc hh n m α v u t z Y
    NativeLocalTimeData a b (ladderOmega D bw j₀ G.level k A ρ) c df := by
  classical
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let edge := pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩
  let a := D.slotStart G.level k / D.cellScaleSq G.level
  let b := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let Ω := ladderOmega D bw j₀ G.level k A ρ
  let Q := familyLiftData D G.level k A ρ edge
  have hab := EntryWeakProofs.weakData_lift_window_strict D hi.base hi.profile hi.band G.level k
  let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ :=
    fun Y => WeakEntryProofs.nativeWindowResponseLinear D hi.profile G.level
      k hA.2 A ρ edge 1 le_rfl a b hab.le Y
  let Cc := WeakEntryProofs.weakLiftInverseCoefficients Q inv Mn.N
  let c := fun t z Y => Cc hh n m α t Y z v u 1
  let df := fun t z Y => -cellOperator (Q.G t Y) (Q.v t) (fun w => c t w Y) z +
    WeakEntryProofs.weakLiftCoefficientForcing Q Cc hh n m α v u t z Y
  have hcmodel (R : ℕ) : ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → ℝ),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = c t z Z := by
    intro Y hY
    obtain ⟨U, c', hU, hYU, hUΩ, hQc, heq⟩ :=
      native_path_coefficient_local_reserve hi π k A hA R hh n m hhh hn hnN hm α v u Y hY
    refine ⟨U, fun t z Z => c' Z t z, hU, hYU, hQc, ?_⟩
    intro t ht Z hZ z
    exact (heq t ht Z hZ z).trans (by
      simp only [StageSuccessor.pathLiftFamily, dite_eq_left hA,
        WeakEntryProofs.weakLiftCarrierRestriction, ite_eq_left (Or.inr (hUΩ hZ))]
      rfl)
  have hdfmodel (R : ℕ) : ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → ℝ),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = df t z Z := by
    intro Y hY
    obtain ⟨U, g, hU, hYU, _hUΩ, hQg, heq⟩ :=
      native_path_coefficient_rhs_reserve hi π k A hA R hh n m hhh hn hnN hm α v u Y hY
    exact ⟨U, g, hU, hYU, hQg, heq⟩
  exact ⟨hcmodel, hdfmodel, fun t ht Y hY z =>
    native_path_coefficient_time_primitive hi π k A hA hh n m
      hhh hn hnN hm α v u Y hY t ht z⟩

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
