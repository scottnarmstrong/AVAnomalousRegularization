-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.WalkMeanIntegral
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.Construction.FreshAxes.RefFluxContinuous
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVenhance.Infra.Classical.Drift

section
section
/-! Cell means when the native family has no identities. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev Set
open AVRegularity.CycleComparison.Lift AVRegularity.Providers.PathDecomp
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm bw j₀}

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- A diagonal lift has no positive-grade flux when the source orders are empty. -/
theorem small_diagonal_flux_zero (hD : Dm < 2)
    (Q : LiftOperatorData (CompIn G.comps) (fun v => hr v.1.root) Dm)
    (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (g n : ℕ) (t : ℝ) :
    liftFluxX Q (HLZero.hlDiagCoeff (fun v : CompIn G.comps => hr v.1.root) c)
      a (g + 1) n t = 0 := by
  have : IsEmpty (Finset.Icc 2 Dm) := ⟨fun d => by
    have hd := Finset.mem_Icc.mp d.2
    omega⟩
  have hsource (ε : ℝ) (Φ : Vec 2 → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
      sourceFlux Q.edge Q.η ε t Φ = 0 := by
    funext k X z v
    simp only [sourceFlux, Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, Pi.zero_apply]
  have ha (n' : ℕ) : liftApply n'
      (HLZero.hlDiagCoeff (fun v : CompIn G.comps => hr v.1.root) c (g + 1) n') a = 0 :=
    liftApply_of_coeff_zero n' _ (fun _ _ _ _ _ _ _ => by
      simp only [HLZero.hlDiagCoeff, Nat.succ_ne_zero, ite_false]) a
  have hfast (j : Fin 2) : fastPartial j
      (0 : Vec 2 → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) = 0 := fastPartial_zero j
  have hslow (j : Fin 2) : slowPartial j
      (0 : Vec 2 → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) = 0 := slowPartial_zero j
  funext X z k
  simp only [liftFluxX, ha, hsource, hfast, hslow, Pi.zero_apply,
    smul_zero, Finset.sum_const_zero, sub_zero, add_zero, neg_zero, ite_self,
    iteratedDeriv_const]

/-- The exact walk-mean expansion at the empty source orders, including zero. -/
theorem small_walk_mean (hi : StageSuccessor.Input P Mn G)
    (hD : Dm < 2) (H : ℕ) (p : OddSlot) (g n : ℕ)
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ)
    (ht : t ∈ Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (X : Vec 2) (k : Fin 2) (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
    let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
    ℓ (fieldCellMean (fun z => liftFluxX Q (nativeStagePathCandidate hi H p)
      (fun _ => f) g n t X z k v)) =
      ∑ u : CompIn G.comps, ∑ q : F.Walk g u v,
        let π := Classical.choose (stage_walk_path q)
        let Qp := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
        let C := StageSuccessor.pathLiftFamily hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
        fieldCellMean (fun z => liftFluxX Qp C
          (fun _ Y => Pi.single (0 : Fin (g + 1)) (ℓ (F.compMap q (f Y u))))
          g n t X z k) (Fin.last g) := by
  classical
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
  let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
  let π₀ : StagePath G 0 := ⟨Fin.elim0, fun j hj => by omega⟩
  let c := StageSuccessor.pathLiftFamily hi.base hi.profile hi.band ρ Mn.N π₀ p.1 (G.actual p).1
  let Q0 := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π₀ p (G.actual p))
  rw [small_candidate_diagonal hi hD H p π₀]
  cases g with
  | succ g =>
    rw [small_diagonal_flux_zero hD Q c (fun _ => f) g n t]
    simp only [Pi.zero_apply, fieldCellMean_zero, map_zero]
    symm
    apply Finset.sum_eq_zero
    intro u hu
    have : IsEmpty (F.Walk (g + 1) u v) := ⟨fun q => by
      have h₂ := (G.fam.identity v q.1 q.2.2).two_le
      have h₁ := (G.fam.identity v q.1 q.2.2).le_D
      omega⟩
    exact Finset.sum_eq_zero (fun q _ => isEmptyElim q)
  | zero =>
    have hseq := StageSuccessor.path_lift_family hi π₀ (n + Dm + 3) (n + Dm + 3)
      p.1 (G.actual p).1 ⟨(G.actual p).2, p.2⟩
    rw [native_actual_ladderOmega_eq_univ hi p ρ] at hseq
    have hs : IsLiftSequence Q0 (n + Dm + 3) (n + Dm + 3)
        (D.slotStart G.level p.1 / D.cellScaleSq G.level)
        ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        Mn.N 0 c := WeakEntryProofs.liftSequence_of_on_univ _ _ _ _ _ _ _ _ hseq
    have hcS (n' m : ℕ) (α : DerivativeWord2 m) (v' u : Fin 1) :
        IsBoxSmooth 2 1 (fun X z => c 0 n' m α t X z v' u) :=
      (hs.2.2.2.2.2.1 0 le_rfl n' m α v' u t ht).1.mono (by omega) (by omega)
    have hcH (n' m : ℕ) (α : DerivativeWord2 m) (v' u : CompIn G.comps) :
        IsBoxSmooth 2 1 (fun X z => HLZero.hlDiagCoeff
          (fun v : CompIn G.comps => hr v.1.root) c 0 n' m α t X z v' u) :=
      (HLZero.hlDiag_boxSmooth_periodic c 2 1 n' m α t v' u (hcS n' m α 0 0)
        (hs.2.2.2.2.2.1 0 le_rfl n' m α 0 0 t ht).2).1
    have hG (i j : Fin 2) : ContDiff ℝ (0 : ℕ∞) (fun X => Q.G t X i j) :=
      (((WeakEntryProofs.familyLiftData_metric_spacetime_smooth D hi.profile G.level p.1
        (G.actual p).1 (G.actual p).2.2.2.1 ρ (G.fam.fiber p (G.actual p)) i j).comp
        (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast le_top))
    have hv (k' : Fin 2) : ContDiff ℝ (0 : ℕ∞) (fun z => Q.v t z k') := by
      have hν := EntryWeakProofs.weakData_kap_pos D hi.base hi.profile hi.band G.level
      exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k').contDiff.comp
        (EntryWeakProofs.normalizedPulseDrift_contDiff hi.base hν p.2 t)).of_le
        (by exact_mod_cast le_top)
    have hc := HLZero.liftFluxX_continuous_zero Q
      (HLZero.hlDiagCoeff (fun v : CompIn G.comps => hr v.1.root) c)
      (fun _ => f) n t k hG hv (hf.of_le (by exact_mod_cast le_top)) hcH X
    have heval := fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun v : CompIn G.comps => hr v.1.root) v) hc
    simp only [ContinuousLinearMap.proj_apply] at heval
    rw [heval]
    rw [HLZero.hl_fluxMean_transfer c Q Q0 rfl rfl rfl ℓ (fun _ => f) n t X k
      hG hv (hf.of_le (by exact_mod_cast le_top)) hcH hcS]
    rw [Finset.sum_eq_single v]
    · let : Unique (F.Walk 0 v v) := ⟨⟨⟨rfl⟩⟩, fun q => by cases q; rfl⟩
      rw [Fintype.sum_unique, empty_stage_path_eq (Classical.choose (stage_walk_path
        (default : F.Walk 0 v v))) π₀]
      have hin : HLZero.hlScal (hs := fun v : CompIn G.comps => hr v.1.root) (v := v) ℓ (fun _ => f) =
          fun _ Y => Pi.single (0 : Fin 1) (ℓ (F.compMap (default : F.Walk 0 v v) (f Y v))) := by
        funext τ Y j
        have hj : j = 0 := Fin.eq_zero j
        subst j
        rfl
      rw [hin]
      rfl
    · intro u hu huv
      have : IsEmpty (F.Walk 0 u v) := ⟨fun q => huv q.down⟩
      exact Finset.sum_eq_zero (fun q _ => isEmptyElim q)
    · intro hnot
      exact (hnot (Finset.mem_univ v)).elim

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! The native stage-path mean action, with both scalar and walk ingredients discharged. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- The literal native mean expands into actual scalar walk means at every source order. -/
theorem walkMeanExpansion : WalkMeanExpansionStatement := by
  classical
  intro hr _ _ _ D Dm bw j₀ P Mn G hi H p g n hg _ _
  dsimp only
  intro f hf t ht X k v ℓ
  by_cases hD : 2 ≤ Dm
  · exact walk_mean_of_two_le hi hD H p g n hg f hf t ht X k v ℓ
  · exact small_walk_mean hi (by omega) H p g n f hf t ht X k v ℓ

/-- The literal cell mean of the native stage-path flux is its actual mean-coefficient action. -/
theorem nativeStagePathMeanAction : NativeStagePathMeanActionStatement :=
  native_mean_action_of_ingredients scalarPathMean walkMeanExpansion

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native budgets: the analytic fields of `Regularity` beyond the time curves, stated one by
one, with the assembled budgets theorem. The drift fields and the kernel fields are proved;
the flux, readout flux, upsilon and source budgets are named statements. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The three time curves from which the budgets are derived. -/
structure NativeBudgetCurves (F : Frame D hr Dm bw j₀) (dZ dRep dUh : F.Field) : Prop where
  readout : ClassicalTimeCurve F F.Naux F.aZ dZ
  prepared : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep
  lifted : ClassicalTimeCurve F (Dm + 4) F.uh dUh

/-- The seven literal flux budgets of order one. -/
def NativeFluxBudgets (F : Frame D hr Dm bw j₀) (dZ dRep dUh : F.Field) :
    Prop :=
  NativeInput F → NativeBudgetCurves F dZ dRep dUh →
  ∀ A ∈ ([F.readFlux, F.macroFluxField, F.mean, F.plain, F.kernel, F.fine, F.lastFlux] :
      List F.Flux), ∀ v, ClassicalWindowBound F.tp F.tf 1 (A v)

/-- The readout flux budget of order `4p+2`. -/
def NativeReadoutFluxBudget (F : Frame D hr Dm bw j₀)
    (dZ dRep dUh : F.Field) : Prop :=
  NativeInput F → NativeBudgetCurves F dZ dRep dUh → ∀ v,
    ClassicalWindowBound F.tp F.tf (4 * F.p + 2)
      (fun t x => toFluxL (menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t x))

/-- The upsilon budget of order `2p+2`. -/
def NativeUpsilonBudget (F : Frame D hr Dm bw j₀)
    (dZ dRep dUh : F.Field) : Prop :=
  NativeInput F → NativeBudgetCurves F dZ dRep dUh → ∀ v,
    ClassicalWindowBound F.tp F.tf (2 * F.p + 2) (F.upsilon v)

/-- The two source budgets of order zero. -/
def NativeSourceBudgets (F : Frame D hr Dm bw j₀)
    (dZ dRep dUh : F.Field) : Prop :=
  NativeInput F → NativeBudgetCurves F dZ dRep dUh →
  ∀ f ∈ ([F.liftedMean, F.physSource dRep dUh] : List F.Field),
    ∀ v, ClassicalWindowBound F.tp F.tf 0 (fun t x => f t x v)

/-- The `kernelFields` clause of `Regularity`, from the native lifted-field regularity. -/
theorem nativeBudget_kernelFields (F : Frame D hr Dm bw j₀) (hi : NativeInput F) :
    ∀ v u (γ : F.G.fam.Γ v u), ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((Dm + 1 : ℕ) : ℕ∞)
        ((F.G.kernelOf F.P F.seedK F.freshK v u γ).applyClassical F.φ₀ t
          (fun y => F.uh t y u)) := fun v u γ t ht =>
  native_input_lifted_kernel_contDiff hi (Dm + 1) (by have := hi.auxiliary; omega) v u γ t ht

/-- All analytic `Regularity` fields that are not time-curve packages. -/
structure NativeBudgetFields (F : Frame D hr Dm bw j₀) (dZ dRep dUh : F.Field) : Prop where
  kernelFields : ∀ v u (γ : F.G.fam.Γ v u), ∀ t ∈ Set.Icc F.tp F.tf,
    ContDiff ℝ ((Dm + 1 : ℕ) : ℕ∞)
      ((F.G.kernelOf F.P F.seedK F.freshK v u γ).applyClassical F.φ₀ t (fun y => F.uh t y u))
  coarseDrift : ClassicalWindowBound F.tp F.tf 1 (streamVel (D.Φ (F.m - 1)))
  fineDrift : ClassicalWindowBound F.tp F.tf 1 (streamVel (D.Φ F.m))
  fluxes : ∀ A ∈ ([F.readFlux, F.macroFluxField, F.mean, F.plain, F.kernel, F.fine,
      F.lastFlux] : List F.Flux), ∀ v, ClassicalWindowBound F.tp F.tf 1 (A v)
  readoutFluxRegularity : ∀ v,
    ClassicalWindowBound F.tp F.tf (4 * F.p + 2)
      (fun t x => toFluxL (menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t x))
  upsilonRegularity : ∀ v, ClassicalWindowBound F.tp F.tf (2 * F.p + 2) (F.upsilon v)
  sources : ∀ f ∈ ([F.liftedMean, F.physSource dRep dUh] : List F.Field),
    ∀ v, ClassicalWindowBound F.tp F.tf 0 (fun t x => f t x v)

/-- The budgets theorem, from four statements taken as hypotheses. -/
theorem nativeBudget_fields (F : Frame D hr Dm bw j₀) (hi : NativeInput F)
    (dZ dRep dUh : F.Field) (hc : NativeBudgetCurves F dZ dRep dUh)
    (hflux : NativeFluxBudgets F dZ dRep dUh)
    (hro : NativeReadoutFluxBudget F dZ dRep dUh)
    (hups : NativeUpsilonBudget F dZ dRep dUh)
    (hsrc : NativeSourceBudgets F dZ dRep dUh) :
    NativeBudgetFields F dZ dRep dUh where
  kernelFields := nativeBudget_kernelFields F hi
  coarseDrift := nativeBudget_coarseDrift F
  fineDrift := nativeBudget_fineDrift F
  fluxes := hflux hi hc
  readoutFluxRegularity := hro hi hc
  upsilonRegularity := hups hi hc
  sources := hsrc hi hc

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Window calculus for the source budgets: the divergence of a flux, the stream velocity as a
scalar coefficient at every order, and the stream transport term `∑ⱼ vⱼ ∂ⱼ g`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- The divergence of a flux whose components have window bounds of order `K + 1`. -/
theorem div_window {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {a b : ℝ} {K : ℕ}
    {f : ℝ → Vec 2 → Fin 2 → E}
    (hf : ∀ j, ClassicalWindowBound a b (K + 1) (fun t x => f t x j)) :
    ClassicalWindowBound a b K (fun t x => divE (f t) x) := by
  have e : (fun t x => divE (f t) x) = fun t x => ∑ j : Fin 2,
      orderedDerivative (fun _ : Fin 1 => j) (fun y => f t y j) x := by
    funext t x
    unfold divE
    exact Finset.sum_congr rfl fun j _ => (nativeBudget_gradE_eq (fun y => f t y j) x j).symm
  rw [e]
  exact ClassicalWindowBound.sum_fintype fun j => (hf j).word (fun _ => j) (by omega)

/-- A component of the gradient, from a window bound one order higher. -/
theorem gradComp_window {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {a b : ℝ} {K : ℕ}
    {f : ℝ → Vec 2 → E} (hf : ClassicalWindowBound a b (K + 1) f) (j : Fin 2) :
    ClassicalWindowBound a b K (fun t x => gradE (f t) x j) := by
  have e : (fun t x => gradE (f t) x j) = fun t x =>
      orderedDerivative (fun _ : Fin 1 => j) (f t) x := by
    funext t x; exact nativeBudget_gradE_eq (f t) x j
  rw [e]
  exact hf.word (fun _ => j) (by omega)

/-- The components of the velocity of an admissible stream are scalar windows of every order. -/
theorem streamVel_scalar (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (a b : ℝ)
    (K : ℕ) (j : Fin 2) : NativeScalarWindow a b K (fun t x => streamVel φ t x j) := by
  have hv := Infra.Classical.streamVel_smoothPeriodic φ hφ
  have hc (t : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (streamVel φ t) :=
    hv.smooth.comp (contDiff_const.prodMk contDiff_id)
  let L : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j
  have hs : ∀ t, (fun x => streamVel φ t x j) = L ∘ streamVel φ t := fun t => rfl
  refine ⟨fun t _ => ?_, fun t _ k x => ?_, ?_, fun n hn => ?_⟩
  · rw [hs t]; exact L.contDiff.comp ((hc t).of_le (by simp))
  · have hp : IsZ2Periodic (streamVel φ t) := fun k x => by
      simpa only [Int.cast_zero, add_zero] using hv.periodic 0 k t x
    show streamVel φ t (x + latticeShift k) j = streamVel φ t x j
    rw [hp k x]
  · have hcont : Continuous (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2 j) :=
      (continuous_apply j).comp hv.smooth.continuous
    exact hcont.measurable.comp measurable_subtype_coe
  · obtain ⟨C, hC0, hC⟩ := CycleJointProofs.admissible_stream_spatial_jet_bound φ hφ n
    refine ⟨‖L‖ * C, fun t _ x => ?_⟩
    rw [hs t]
    have h1 := L.norm_iteratedFDeriv_comp_left (f := streamVel φ t) (x := x)
      (N := (n : ℕ∞ω)) ((hc t).of_le (by simp)).contDiffAt le_rfl
    exact h1.trans (mul_le_mul_of_nonneg_left (hC t x) (norm_nonneg _))

/-- The transport term `∑ⱼ vⱼ ∂ⱼ g` of an admissible stream has the window bound `K` when `g` has
the window bound `K + 1`. -/
theorem streamGrad_window {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {a b : ℝ} {K : ℕ}
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) {f : ℝ → Vec 2 → E}
    (hf : ClassicalWindowBound a b (K + 1) f) :
    ClassicalWindowBound a b K (fun t x => ∑ j : Fin 2, streamVel φ t x j • gradE (f t) x j) :=
  ClassicalWindowBound.sum_fintype fun j =>
    ClassicalWindowBound.smul_scalar (streamVel_scalar φ hφ a b K j)
      (gradComp_window hf j)

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native budgets: the seven flux budgets of order one, from the glued pulse budget
(`NativeGluedMeanBudget`) and the upsilon budget of order `2p+2`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The upsilon budget as a hypothesis of the flux reductions. -/
def NativeUpsilonWindow (F : Frame D hr Dm bw j₀) : Prop :=
  ∀ v, ClassicalWindowBound F.tp F.tf (2 * F.p + 2) (F.upsilon v)

/-- The read flux has the window bound of order one. -/
theorem nativeBudget_readFlux {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudget F)
    (hu : NativeUpsilonWindow F) (hi : NativeInput F) {dZ : F.Field}
    (hc : ClassicalTimeCurve F F.Naux F.aZ dZ) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf 1 (F.readFlux v) := by
  have hH := fun i j => nativeBudget_covPrimitive_continuous hi i j
  have hG := nativeBudget_gFlux_pi hg hi hc v
  have hQ := ClassicalWindowBound.covQ (H := menuCovPrimitive D F.Mn F.m) hH F.p
    (K := 1) (hG.mono (by omega))
  have hQ' := hQ.map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => hr v.1.root)).symm.toContinuousLinearMap
  exact (hQ'.add ((hu v).mono (by omega))).neg

/-- The mean flux has the window bound of order one. -/
theorem nativeBudget_meanFlux {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudget F)
    (hu : NativeUpsilonWindow F) (hi : NativeInput F) {dZ : F.Field}
    (hc : ClassicalTimeCurve F F.Naux F.aZ dZ) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf 1 (F.mean v) := by
  have hres := hi.auxiliary
  have hH := fun i j => nativeBudget_covPrimitive_continuous hi i j
  have hG := nativeBudget_gFlux_pi hg hi hc v
  have hQ := ClassicalWindowBound.covQ (H := menuCovPrimitive D F.Mn F.m) hH F.p
    (K := 2 * F.p + 1) (hG.mono (by omega))
  have hPQ := ClassicalWindowBound.covP (H := menuCovPrimitive D F.Mn F.m) hH F.p
    (K := 1) (f := fun t y => covPolyQ (menuCovPrimitive D F.Mn F.m t) F.p
      (fun y' => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y') y)
    (hQ.mono (by omega))
  have hU := ((hu v).map (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => hr v.1.root)).toContinuousLinearMap)
  have hPU := ClassicalWindowBound.covP (H := menuCovPrimitive D F.Mn F.m) hH F.p
    (K := 1) (f := fun t y => WithLp.ofLp (F.upsilon v t y)) (hU.mono (by omega))
  have h0 : ClassicalWindowBound F.tp F.tf (F.Naux - 2) (fun t x => F.aZ t x v) := hc.field v
  have h1 : ClassicalWindowBound F.tp F.tf (2 + 2 * F.p) (fun t x => F.aZ t x v) :=
    h0.mono (by omega)
  have h2 := ClassicalWindowBound.covOp_iterate (H := menuCovPrimitive D F.Mn F.m) hH F.p h1
  have h3 := ClassicalWindowBound.smul_time (s := fun _ => ((F.p.factorial : ℝ)⁻¹))
    continuous_const h2
  have h4 := ClassicalWindowBound.matGradPi (K := 1)
    (R := fun t => ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t - D.κ (F.m - 1) •
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) (nativeBudget_refFlux_continuous hi) h3
  have key := (((hG.mono (by omega : 1 ≤ 4 * F.p + 2)).sub hPQ).sub hPU).sub h4
  exact key.map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => hr v.1.root)).symm.toContinuousLinearMap

/-- The seven flux budgets of order one. -/
theorem nativeBudget_fluxes_of {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudget F)
    (hu : NativeUpsilonWindow F) (hi : NativeInput F) (dZ dRep dUh : F.Field)
    (hcs : NativeBudgetCurves F dZ dRep dUh) :
    ∀ A ∈ ([F.readFlux, F.macroFluxField, F.mean, F.plain, F.kernel, F.fine, F.lastFlux] :
      List F.Flux), ∀ v, ClassicalWindowBound F.tp F.tf 1 (A v) := by
  intro A hA v
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nativeBudget_readFlux hg hu hi hcs.readout v
  · exact nativeBudget_macroFlux hg hi hcs.prepared v
  · exact nativeBudget_meanFlux hg hu hi hcs.readout v
  · exact nativeBudget_plain hi hcs.lifted v
  · exact nativeBudget_kernel hi hcs.lifted v
  · exact nativeBudget_fine hi hcs.lifted v
  · exact nativeBudget_lastFlux hi hcs.readout v

/-- `NativeReadoutFluxBudget`, from the glued budget. -/
theorem nativeBudget_readoutFluxBudget_of {F : Frame D hr Dm bw j₀}
    (hg : NativeGluedMeanBudget F) (dZ dRep dUh : F.Field) :
    NativeReadoutFluxBudget F dZ dRep dUh :=
  fun hi hcs v => nativeBudget_gFlux hg hi hcs.readout v

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native glued mean flux, step 1: the fixed finite set of pulse indices, the identity of the
glued flux with the sum over it, and the glued budget from the budget of one pulse term. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- A window bound is insensitive to the values of the field outside the window. -/
theorem ClassicalWindowBound.congr_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {a b : ℝ} {K : ℕ} {f g : ℝ → Vec 2 → E}
    (h : ∀ t ∈ Icc a b, f t = g t) (hf : ClassicalWindowBound a b K f) :
    ClassicalWindowBound a b K g := by
  have hfun : ∀ t ∈ Icc a b, g t = f t := fun t ht => (h t ht).symm
  refine ⟨fun t ht => by rw [hfun t ht]; exact hf.smooth t ht,
    fun t ht => by rw [hfun t ht]; exact hf.periodic t ht, ?_, fun n hn w => ?_⟩
  · have e : (fun z : {z : ℝ × Vec 2 // z.1 ∈ Icc a b} => g z.1.1 z.1.2) =
        fun z => f z.1.1 z.1.2 := by
      funext z; rw [hfun z.1.1 z.2]
    rw [e]; exact hf.measurable
  · obtain ⟨B, hB, hbd⟩ := hf.bound n hn w
    exact ⟨B, hB, fun t ht x hx => by rw [hfun t ht]; exact hbd t ht x hx⟩

/-- The pulse term of the glued mean flux at the pulse index `k`: grades `rs`, degrees `ns`. -/
def nativeGluedPulse (F : Frame D hr Dm bw j₀) (rs ns : Finset ℕ) (a : F.Field) (k : ℤ)
    (t : ℝ) (x : Vec 2) (v : CompIn F.G.comps) : Fin 2 → hr v.1.root :=
  ∑ r ∈ rs, ∑ n ∈ ns,
    if hk : Odd k then
      ocCutoff D.α D.q D.Λ F.m k t • pulseMeanFluxEuler (D.cellScaleSq F.m)
        (F.Mn.lenFactor * liftLength D F.m)
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / (F.Mn.lenFactor * liftLength D F.m)) n r
        (familyLiftData D F.m k (nativeChain F.m k) (F.Mn.lenFactor * liftLength D F.m)
          (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩))) (F.CcT k)
        (fun s' y => D.flowOf (F.m - 1) s' y (D.slotAnchor F.m k))
        (fun s' y => D.flowOf (F.m - 1) (D.slotAnchor F.m k) y s') a t x v
    else 0

/-- The fixed set of pulse indices meeting the observation window. -/
def nativeGluedIndices (F : Frame D hr Dm bw j₀) : Finset ℤ :=
  ocObsPulses D.α D.q D.Λ F.m F.tp F.tf

/-- The glued mean flux is the sum of the pulse terms over the time-dependent pulse set. -/
theorem nativeGluedPulse_sum_obs (F : Frame D hr Dm bw j₀) (rs ns : Finset ℕ) (a : F.Field)
    (t : ℝ) (x : Vec 2) (v : CompIn F.G.comps) :
    menuGluedMeanFlux F.Mn F.G F.m rs ns F.CcT a t x v =
      ∑ k ∈ ocObsPulses D.α D.q D.Λ F.m t t, nativeGluedPulse F rs ns a k t x v := by
  unfold menuGluedMeanFlux nativeGluedPulse
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : Odd k
  · simp only [hk, dite_true]
  · simp only [hk, dite_false, Finset.sum_const_zero]

/-- The pulse term vanishes at a time outside the window of the pulse. -/
theorem nativeGluedPulse_eq_zero_of_not_mem (F : Frame D hr Dm bw j₀) (rs ns : Finset ℕ)
    (a : F.Field) {k : ℤ} {t : ℝ}
    (hk : t ∉ ocPulseWindow D.α D.q D.Λ F.m k) (hτ : 0 < ocTau D.α D.q D.Λ F.m)
    (x : Vec 2) (v : CompIn F.G.comps) : nativeGluedPulse F rs ns a k t x v = 0 := by
  have hc : ocCutoff D.α D.q D.Λ F.m k t = 0 := by
    by_contra h
    exact hk (AVRegularity.Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ h)
  unfold nativeGluedPulse
  refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun n _ => ?_
  by_cases hodd : Odd k
  · simp only [hodd, dite_true, hc, zero_smul]
  · simp only [hodd, dite_false]

/-- **The fixed-index-set identity**: on the observation window the glued mean flux is the sum of
the pulse terms over the fixed finite set of indices. -/
theorem nativeGluedPulse_sum_fixed {F : Frame D hr Dm bw j₀} (hi : NativeInput F) (rs ns : Finset ℕ) (a : F.Field)
    {t : ℝ} (ht : t ∈ Icc F.tp F.tf) (x : Vec 2) (v : CompIn F.G.comps) :
    menuGluedMeanFlux F.Mn F.G F.m rs ns F.CcT a t x v =
      ∑ k ∈ nativeGluedIndices F, nativeGluedPulse F rs ns a k t x v := by
  have hτ : 0 < ocTau D.α D.q D.Λ F.m := Construction.Stream.ocTau_pos hi.stage.base
  rw [nativeGluedPulse_sum_obs]
  refine Finset.sum_subset ?_ ?_
  · intro k hk
    simp only [nativeGluedIndices, ocObsPulses, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨h1, h2⟩, hodd, z, hz, hzt⟩ := hk
    have hzt' : z = t := le_antisymm hzt.2 hzt.1
    subst hzt'
    refine ⟨⟨?_, ?_⟩, hodd, z, hz, ht⟩
    · have : ⌊F.tp / ocTau D.α D.q D.Λ F.m⌋ ≤ ⌊z / ocTau D.α D.q D.Λ F.m⌋ :=
        Int.floor_mono (div_le_div_of_nonneg_right ht.1 hτ.le)
      omega
    · have : ⌈z / ocTau D.α D.q D.Λ F.m⌉ ≤ ⌈F.tf / ocTau D.α D.q D.Λ F.m⌉ :=
        Int.ceil_mono (div_le_div_of_nonneg_right ht.2 hτ.le)
      omega
  · intro k hkS hk
    simp only [nativeGluedIndices, ocObsPulses, Finset.mem_filter] at hkS
    refine nativeGluedPulse_eq_zero_of_not_mem F rs ns a ?_ hτ x v
    intro hw
    apply hk
    simp only [ocObsPulses, Finset.mem_filter, Finset.mem_Icc]
    obtain ⟨h1, h2⟩ := hw
    have hu1 : ((k : ℝ) - 61 / 48) ≤ t / ocTau D.α D.q D.Λ F.m := by
      rw [le_div_iff₀ hτ]; exact h1
    have hu2 : t / ocTau D.α D.q D.Λ F.m ≤ ((k : ℝ) + 61 / 48) := by
      rw [div_le_iff₀ hτ]; exact h2
    refine ⟨⟨?_, ?_⟩, hkS.2.1, t, ⟨h1, h2⟩, le_rfl, le_rfl⟩
    · by_contra hlt
      have hk2 : k ≤ ⌊t / ocTau D.α D.q D.Λ F.m⌋ - 2 := by omega
      have hk3 : (k : ℝ) ≤ (⌊t / ocTau D.α D.q D.Λ F.m⌋ : ℝ) - 2 := by exact_mod_cast hk2
      have := Int.floor_le (t / ocTau D.α D.q D.Λ F.m)
      linarith
    · by_contra hlt
      have hk2 : ⌈t / ocTau D.α D.q D.Λ F.m⌉ + 2 ≤ k := by omega
      have hk3 : (⌈t / ocTau D.α D.q D.Λ F.m⌉ : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hk2
      have := Int.le_ceil (t / ocTau D.α D.q D.Λ F.m)
      linarith

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native upsilon budget, step 1: the physical coefficients of the outgoing stage `G'` have
uniform window data, and the retained field `aY` has a window bound. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The outgoing stage is shift invariant. -/
theorem nativeUpsilon_shift {F : Frame D hr Dm bw j₀} (hi : NativeInput F) :
    F.G'.IsShiftInvariant := by
  have hcs := EntryWeakProofs.weakData_cellScaleSq_pos D hi.stage.base hi.stage.profile
    hi.stage.band F.G.level
  exact Construction.Preservation.FullLift.successor_shift_invariant_of_cellScaleSq_nonneg
    hi.stage.profile hcs.le hi.stage.natural hi.shift hi.actual

/-- The physical coefficients of the outgoing family have uniform window data at every order. -/
theorem nativeUpsilon_physCoeff_uniform {F : Frame D hr Dm bw j₀} (hi : NativeInput F)
    (K d : ℕ) (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u) :
    NativeUniformCoeff F.tp F.tf K (F.G'.physCoeff v u γ d) := by
  obtain ⟨k, hc, hr0⟩ := hi.outgoing_context
  have hlev := hi.stage.level
  have hact := hi.actual
  have h21 : F.G'.level = F.G.level - 1 := hact.2.1
  have hε : 0 < D.eps (F.G'.level - 1) := Construction.Stream.ocEpsilon_pos hi.stage.base
  have h := native_context_physical_fields hi.stage.base hi.stage.bandwidth
    (show 1 ≤ F.G'.level by omega) (show j₀ ≤ F.G'.level by omega) hc hact.2.2.2.1
    (nativeUpsilon_shift hi) hr0 F.tp F.tf K d v u γ
  exact nativeBudget_uniformCoeff_of_seminorm _ hε h.2.2
    (fun t ht => (h.1 t ht).1) (fun t ht => (h.1 t ht).2) h.2.1

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end

section
section
/-! Native glued mean flux, step 2: the budget of one pulse term (a named statement) and the
glued budget `NativeGluedMeanBudget` assembled from it. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The budget of one cutoff-weighted pulse term of the glued mean flux. -/
def NativeGluedPulseBudget (F : Frame D hr Dm bw j₀) : Prop :=
  NativeInput F → ∀ (rs ns : Finset ℕ), rs ⊆ Finset.Icc 0 F.depth →
    ns ⊆ Finset.Icc 2 (F.N + Dm) → ∀ (a : F.Field) (K : ℕ),
      (∀ v, ClassicalWindowBound F.tp F.tf (K + nativeGluedLoss F.N Dm) (fun t x => a t x v)) →
      ∀ (k : ℤ) (v : CompIn F.G.comps), ClassicalWindowBound F.tp F.tf K (fun t x =>
        toFluxL (nativeGluedPulse F rs ns a k t x v))

/-- `toFluxL` commutes with finite sums. -/
theorem toFluxL_sum_finset {ι E : Type*} [AddCommGroup E] (s : Finset ι) (f : ι → Fin 2 → E) :
    toFluxL (∑ i ∈ s, f i) = ∑ i ∈ s, toFluxL (f i) := by
  apply WithLp.ofLp_injective 2
  funext j
  simp [toFluxL, WithLp.ofLp_sum, Finset.sum_apply]

/-- **The glued budget from the pulse budget.** -/
theorem nativeGlued_budget_of_pulse {F : Frame D hr Dm bw j₀} (h : NativeGluedPulseBudget F) :
    NativeGluedMeanBudget F := by
  intro hi rs ns hrs hns a K ha v
  have hp := ClassicalWindowBound.sum_finset (a := F.tp) (b := F.tf) (K := K)
    (nativeGluedIndices F) (f := fun k t x => toFluxL (nativeGluedPulse F rs ns a k t x v))
    (fun k _ => h hi rs ns hrs hns a K ha k v)
  refine ClassicalWindowBound.congr_on (fun t ht => ?_) hp
  funext x
  rw [← toFluxL_sum_finset, nativeGluedPulse_sum_fixed hi rs ns a ht x v]

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native upsilon budget, step 2: window bounds of the coefficient terms of the outgoing family,
of the root flux defect, of the omitted flux, and of the readout of a family of window-bounded
fluxes. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The zero field has every window bound. -/
theorem ClassicalWindowBound.zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (a b : ℝ) (K : ℕ) :
    ClassicalWindowBound a b K (fun _ _ => (0 : E)) :=
  ⟨fun _ _ => contDiff_const, fun _ _ _ _ => rfl, measurable_const, fun n _ w =>
    ⟨fun _ => 0, integrableOn_const (by simp), fun t _ x _ => by
      simp [congrFun (orderedDerivative_const_zero w) x]⟩⟩

/-- One coefficient term of the outgoing family. -/
theorem nativeUpsilon_coeffTerm {F : Frame D hr Dm bw j₀} (hi : NativeInput F) {K L : ℕ}
    (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u) (d : ℕ) (hd : d - 1 + K ≤ L)
    {g : ℝ → Vec 2 → hr u.1.root} (hg : ClassicalWindowBound F.tp F.tf L g) :
    ClassicalWindowBound F.tp F.tf K (fun t x =>
      F.G'.physCoeff v u γ d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d - 1) =>
        orderedDerivative word (g t) x)) := by
  have hw := ClassicalWindowBound.pi (V := fun _ : DerivativeWord2 (d - 1) => hr u.1.root)
    (fun word => hg.word word (L := K) hd)
  have hP := hw.map (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : DerivativeWord2 (d - 1) => hr u.1.root)).symm.toContinuousLinearMap
  exact ClassicalWindowBound.clm_apply (nativeUpsilon_physCoeff_uniform hi K d v u γ) hP

/-- The kernel-applied field of an outgoing edge. -/
theorem nativeUpsilon_kernelField {F : Frame D hr Dm bw j₀} (hi : NativeInput F) {K : ℕ}
    (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u) {g : ℝ → Vec 2 → hr u.1.root}
    (hg : ClassicalWindowBound F.tp F.tf K g) :
    ClassicalWindowBound F.tp F.tf K (fun t y =>
      (F.G'.kernelOf F.P F.seedK F.freshK v u γ).applyClassical F.φ₀ t (g t) y) := by
  obtain ⟨Γ, hΓ⟩ := hi.successorKernels
  exact nativeBudget_kernel_windowBound hi.smooth hi.support _ (hΓ v u γ).1 (hΓ v u γ).2.1 hg

/-- The root flux defect, from the window bound of the readout field. -/
theorem nativeUpsilon_rootFluxDefect {F : Frame D hr Dm bw j₀} (hi : NativeInput F) {K : ℕ}
    (haZ : ∀ w, ClassicalWindowBound F.tp F.tf (K + Dm) (fun t x => F.aZ t x w))
    (v : CompIn F.G'.comps) :
    ClassicalWindowBound F.tp F.tf K (fun t x =>
      rootFluxDefect F.P F.seedK F.freshK F.φ₀ F.G F.G' F.aZ v t x) := by
  classical
  unfold rootFluxDefect
  refine ClassicalWindowBound.sum_fintype fun u' => ?_
  by_cases hu : u'.1 ∈ F.G.comps
  · simp only [hu, dite_true]
    refine ClassicalWindowBound.sum_fintype fun γ => ?_
    refine ClassicalWindowBound.sum_fintype fun d => ?_
    have hd := Finset.mem_Icc.1 d.2
    exact nativeUpsilon_coeffTerm hi v u' γ d.1 (by omega)
      ((haZ ⟨u'.1, hu⟩).sub (nativeUpsilon_kernelField hi v u' γ (haZ ⟨u'.1, hu⟩)))
  · simp only [hu, dite_false]
    exact ClassicalWindowBound.zero _ _ _

/-- The omitted flux, from the window bound of the retained field. -/
theorem nativeUpsilon_omittedFlux {F : Frame D hr Dm bw j₀} (hi : NativeInput F) {K : ℕ}
    (haY : ∀ w, ClassicalWindowBound F.tp F.tf (K + Dm) (fun t x => F.aY t x w))
    (v : CompIn F.G'.comps) :
    ClassicalWindowBound F.tp F.tf K (fun t x =>
      omittedFluxClassical F.P F.seedK F.freshK F.φ₀ F.G' F.Gr F.aY v t x) := by
  classical
  unfold omittedFluxClassical
  refine ClassicalWindowBound.sum_fintype fun u => ?_
  by_cases hu : u.1 ∈ F.Gr.comps
  · simp only [hu, dite_true]
    refine ClassicalWindowBound.sum_fintype fun γ => ?_
    refine ClassicalWindowBound.sum_fintype fun d => ?_
    have hd := Finset.mem_Icc.1 d.2
    exact nativeUpsilon_coeffTerm hi v u γ d.1 (by omega)
      (nativeUpsilon_kernelField hi v u γ (haY ⟨u.1, hu⟩))
  · simp only [hu, dite_false]
    exact ClassicalWindowBound.zero _ _ _

/-- Transport of a window bound along an equality of the component root. -/
theorem ClassicalWindowBound.cast_root {r r' : ℕ} (e : r = r') {a b : ℝ} {K : ℕ}
    {f : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr r)} (hf : ClassicalWindowBound a b K f) :
    ClassicalWindowBound a b K (fun t x =>
      cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) (f t x)) := by
  subst e
  simpa using hf

/-- The readout of a family of window-bounded fluxes. -/
theorem nativeUpsilon_readoutFlux {S S' : Finset Comp} (m : ℕ) (E η₀ : ℝ) (sel : Comp → Prop)
    (Fn : ∀ v' : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v'.1.root)) {a b : ℝ} {K : ℕ}
    (h : ∀ v', ClassicalWindowBound a b K (Fn v')) (v : CompIn S) :
    ClassicalWindowBound a b K (fun t x => readoutFlux m E η₀ sel Fn v t x) := by
  classical
  unfold readoutFlux
  refine ClassicalWindowBound.sum_fintype fun v' => ?_
  by_cases hc : compParent m v'.1 = v.1 ∧ sel v'.1
  · simp only [hc, and_self, dite_true]
    have hcast := ClassicalWindowBound.cast_root (hr := hr)
      ((compParent_root m v'.1).symm.trans (congrArg Comp.root hc.1)) (h v')
    exact hcast.map (E ^ (η₀ * ((compWord m v'.1).length : ℝ)) • ContinuousLinearMap.id ℝ _)
  · simp only [hc, dite_false]
    exact ClassicalWindowBound.zero _ _ _

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native upsilon budget, step 3: the window bound of the retained field, and
`NativeUpsilonBudget` (hence `NativeUpsilonWindow`) proved. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.FullLift
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- A continuous Sobolev curve with classical representatives has a window bound two orders
below its Sobolev order. -/
theorem nativeUpsilon_window_of_continuous {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] {k : ℕ} (hk : 2 ≤ k) {a b : ℝ} (U : ℝ → TorusHk k E)
    (f : ℝ → Vec 2 → E) (hf : ∀ t ∈ Icc a b, IsClassicalRep (U t) (f t) k)
    (hU : ContinuousOn U (Icc a b)) : ClassicalWindowBound a b (k - 2) f := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 2 := ⟨k - 2, by omega⟩
  have hf' : ∀ t ∈ Icc a b, IsClassicalRep (U t) (f t) K := fun t ht =>
    classicalRep_order_mono _ _ (hf t ht) (by omega)
  let nativeCurveTimeSecondCountable : SecondCountableTopologyEither
      (Icc a b) (TorusHk (K + 2) E) := secondCountableTopologyEither_of_left _ _
  have hM : StronglyMeasurable (fun t : Icc a b => U t) :=
    (continuousOn_iff_continuous_domRestrict.mp hU).stronglyMeasurable
  simpa using native_classical_window_bound (K := K) U f hf' hM hU.norm.integrableOn_Icc

/-- The retained field has a window bound of order `Naux - 2`. -/
theorem nativeUpsilon_retained_window {F : Frame D hr Dm bw j₀} (hi : NativeInput F)
    (v : CompIn F.Gr.comps) :
    ClassicalWindowBound F.tp F.tf (F.Naux - 2) (fun t x => F.aY t x v) := by
  have hres := hi.auxiliary
  exact nativeUpsilon_window_of_continuous (k := F.Naux) (by omega) (F.Y v)
    (fun t x => F.aY t x v) (F.retained v) (hi.solution.1 v)

/-- **The upsilon budget.** -/
theorem nativeUpsilon_budget (F : Frame D hr Dm bw j₀) (dZ dRep dUh : F.Field) :
    NativeUpsilonBudget F dZ dRep dUh := by
  intro hi hcs v
  have hres := hi.auxiliary
  have hZ : ∀ w, ClassicalWindowBound F.tp F.tf (2 * F.p + 2 + Dm)
      (fun t x => F.aZ t x w) := fun w => (hcs.readout.field w).mono (by omega)
  have hY : ∀ w, ClassicalWindowBound F.tp F.tf (2 * F.p + 2 + Dm)
      (fun t x => F.aY t x w) := fun w => (nativeUpsilon_retained_window hi w).mono (by omega)
  unfold Frame.upsilon upsilonFlux
  exact (nativeUpsilon_readoutFlux F.m _ _ _ _ (nativeUpsilon_rootFluxDefect hi hZ) v).add
    (nativeUpsilon_readoutFlux F.m _ _ _ _ (nativeUpsilon_omittedFlux hi hY) v)

/-- The upsilon window hypothesis of the flux reductions, proved. -/
theorem nativeUpsilon_window {F : Frame D hr Dm bw j₀} {dZ dRep dUh : F.Field}
    (hi : NativeInput F) (hcs : NativeBudgetCurves F dZ dRep dUh) : NativeUpsilonWindow F :=
  fun v => nativeUpsilon_budget F dZ dRep dUh hi hcs v

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native glued mean flux, step 3: a pulse term is a differential operator of order `N + Dm` in
the field, with coefficients that have uniform window data. The jet representation is a named
statement; the pulse budget (hence `NativeGluedMeanBudget`) is assembled from it. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- A pulse term of the glued mean flux is a differential operator of order `N + Dm` in the
field `a` with smooth periodic coefficients that have uniform window data at every order, valid
for every field that is of class `C^{N+Dm}` in space at the times of the window. -/
def NativeGluedPulseJet (F : Frame D hr Dm bw j₀) : Prop :=
  NativeInput F → ∀ (rs ns : Finset ℕ), rs ⊆ Finset.Icc 0 F.depth →
    ns ⊆ Finset.Icc 2 (F.N + Dm) → ∀ (k : ℤ) (v : CompIn F.G.comps),
    ∃ C : ∀ m : Fin (F.N + Dm + 1), DerivativeWord2 m.1 → ∀ u : CompIn F.G.comps,
        ℝ → Vec 2 → (hr u.1.root →L[ℝ] PiLp 2 (fun _ : Fin 2 => hr v.1.root)),
      (∀ K m α u, NativeUniformCoeff F.tp F.tf K (C m α u)) ∧
      ∀ (a : F.Field), ∀ t ∈ Icc F.tp F.tf,
        (∀ w, ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (fun x => a t x w)) → ∀ x,
          toFluxL (nativeGluedPulse F rs ns a k t x v) =
            ∑ m : Fin (F.N + Dm + 1), ∑ α : DerivativeWord2 m.1, ∑ u : CompIn F.G.comps,
              C m α u t x (orderedDerivative α (fun y => a t y u) x)

/-- **The pulse budget from the jet representation.** -/
theorem nativeGlued_pulseBudget_of_jet {F : Frame D hr Dm bw j₀} (h : NativeGluedPulseJet F) :
    NativeGluedPulseBudget F := by
  intro hi rs ns hrs hns a K ha k v
  obtain ⟨C, hC, hrep⟩ := h hi rs ns hrs hns k v
  have hterm : ClassicalWindowBound F.tp F.tf K (fun t x =>
      ∑ m : Fin (F.N + Dm + 1), ∑ α : DerivativeWord2 m.1, ∑ u : CompIn F.G.comps,
        C m α u t x (orderedDerivative α (fun y => a t y u) x)) := by
    refine ClassicalWindowBound.sum_fintype fun m => ?_
    refine ClassicalWindowBound.sum_fintype fun α => ?_
    refine ClassicalWindowBound.sum_fintype fun u => ?_
    have hm := m.2
    have hw := (ha u).word α (L := K) (by unfold nativeGluedLoss; omega)
    exact ClassicalWindowBound.clm_apply (hC K m α u) hw
  refine ClassicalWindowBound.congr_on (fun t ht => ?_) hterm
  funext x
  have hs : ∀ w, ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (fun y => a t y w) := fun w =>
    ((ha w).smooth t ht).of_le (Nat.cast_le.mpr (by unfold nativeGluedLoss; omega))
  exact (hrep a t ht hs x).symm

/-- **`NativeGluedMeanBudget` from the jet representation of a pulse term.** -/
theorem nativeGlued_budget_of_jet {F : Frame D hr Dm bw j₀} (h : NativeGluedPulseJet F) :
    NativeGluedMeanBudget F :=
  nativeGlued_budget_of_pulse (nativeGlued_pulseBudget_of_jet h)

/-- The glued budget with the loss `N + Dm` that the jet representation really costs. -/
def NativeGluedMeanBudgetTight (F : Frame D hr Dm bw j₀) : Prop :=
  NativeInput F → ∀ (rs ns : Finset ℕ), rs ⊆ Finset.Icc 0 F.depth →
    ns ⊆ Finset.Icc 2 (F.N + Dm) → ∀ (a : F.Field) (K : ℕ),
      (∀ v, ClassicalWindowBound F.tp F.tf (K + (F.N + Dm)) (fun t x => a t x v)) →
      ∀ v, ClassicalWindowBound F.tp F.tf K (fun t x =>
        toFluxL (menuGluedMeanFlux F.Mn F.G F.m rs ns F.CcT a t x v))

/-- **The tight glued budget from the jet representation of a pulse term.** -/
theorem nativeGlued_tight_of_jet {F : Frame D hr Dm bw j₀} (h : NativeGluedPulseJet F) :
    NativeGluedMeanBudgetTight F := by
  intro hi rs ns hrs hns a K ha v
  have hp := ClassicalWindowBound.sum_finset (a := F.tp) (b := F.tf) (K := K)
    (nativeGluedIndices F) (f := fun k t x => toFluxL (nativeGluedPulse F rs ns a k t x v))
    (fun k _ => by
      obtain ⟨C, hC, hrep⟩ := h hi rs ns hrs hns k v
      have hterm : ClassicalWindowBound F.tp F.tf K (fun t x =>
          ∑ m : Fin (F.N + Dm + 1), ∑ α : DerivativeWord2 m.1, ∑ u : CompIn F.G.comps,
            C m α u t x (orderedDerivative α (fun y => a t y u) x)) := by
        refine ClassicalWindowBound.sum_fintype fun m => ?_
        refine ClassicalWindowBound.sum_fintype fun α => ?_
        refine ClassicalWindowBound.sum_fintype fun u => ?_
        have hm := m.2
        exact ClassicalWindowBound.clm_apply (hC K m α u)
          ((ha u).word α (L := K) (by omega))
      refine ClassicalWindowBound.congr_on (fun t ht => ?_) hterm
      funext x
      exact (hrep a t ht (fun w => ((ha w).smooth t ht).of_le
        (Nat.cast_le.mpr (by omega))) x).symm)
  refine ClassicalWindowBound.congr_on (fun t ht => ?_) hp
  funext x
  rw [← toFluxL_sum_finset, nativeGluedPulse_sum_fixed hi rs ns a ht x v]

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! The readout flux and the mean flux at a higher order, from the TIGHT glued budget (loss
`N + Dm`) and the upsilon window at the same order. Orders `K ≤ N + 1 + 4p` of the readout flux
and `K ≤ N + 1` of the mean flux are needed by the source budgets. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The upsilon flux has the window bound of every order `K + Dm + 2 ≤ Naux`. -/
theorem upsilon_order {F : Frame D hr Dm bw j₀} (hi : NativeInput F) {dZ : F.Field}
    (hc : ClassicalTimeCurve F F.Naux F.aZ dZ) (K : ℕ) (hK : K + Dm + 2 ≤ F.Naux)
    (v : CompIn F.G.comps) : ClassicalWindowBound F.tp F.tf K (F.upsilon v) := by
  have hres := hi.auxiliary
  have hZ : ∀ w, ClassicalWindowBound F.tp F.tf (K + Dm)
      (fun t x => F.aZ t x w) := fun w => (hc.field w).mono (by omega)
  have hY : ∀ w, ClassicalWindowBound F.tp F.tf (K + Dm)
      (fun t x => F.aY t x w) := fun w => (nativeUpsilon_retained_window hi w).mono (by omega)
  unfold Frame.upsilon upsilonFlux
  exact (nativeUpsilon_readoutFlux F.m _ _ _ _ (nativeUpsilon_rootFluxDefect hi hZ) v).add
    (nativeUpsilon_readoutFlux F.m _ _ _ _ (nativeUpsilon_omittedFlux hi hY) v)

/-- The tight glued budget in the sup-norm product. -/
theorem glued_pi {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudgetTight F)
    (hi : NativeInput F) (rs ns : Finset ℕ) (hrs : rs ⊆ Finset.Icc 0 F.depth)
    (hns : ns ⊆ Finset.Icc 2 (F.N + Dm)) (a : F.Field) (K : ℕ)
    (ha : ∀ v, ClassicalWindowBound F.tp F.tf (K + (F.N + Dm)) (fun t x => a t x v))
    (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf K (fun t x =>
      menuGluedMeanFlux F.Mn F.G F.m rs ns F.CcT a t x v) :=
  (hg hi rs ns hrs hns a K ha v).map
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => hr v.1.root)).toContinuousLinearMap

/-- The readout flux at the order `K ≤ N + 3 + 4p`, in the sup-norm product, from the tight
glued budget. -/
theorem gFlux_pi_order {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudgetTight F)
    (hi : NativeInput F) {dZ : F.Field} (hc : ClassicalTimeCurve F F.Naux F.aZ dZ)
    (K : ℕ) (hK : K ≤ F.N + 3 + 4 * F.p) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf K
      (fun t x => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t x) := by
  have hres := hi.auxiliary
  have hDm := hi.stage.order
  have hH := fun i j => nativeBudget_covPrimitive_continuous hi i j
  have hz : ∀ w : CompIn F.G.comps, ClassicalWindowBound F.tp F.tf (F.Naux - 2)
      (fun t x => F.aZ t x w) := fun w => hc.field w
  have ha2 : ∀ K : ℕ, K + 2 * F.p ≤ F.Naux - 2 → ∀ w : CompIn F.G.comps,
      ClassicalWindowBound F.tp F.tf K
        (fun t x => covPolyP (menuCovPrimitive D F.Mn F.m t) F.p (fun y => F.aZ t y w) x) :=
    fun K hK w => ClassicalWindowBound.covP (H := menuCovPrimitive D F.Mn F.m) hH F.p
      ((hz w).mono hK)
  have hT1 : ClassicalWindowBound F.tp F.tf K (fun t x =>
      ∑ l ∈ Finset.Icc 1 F.p, ((l.factorial : ℝ)⁻¹) • ∑ a' ∈ Finset.range l,
        (covOperator (menuCovPrimitive D F.Mn F.m t))^[a']
          (commFluxE (streamVel (D.Φ (F.m - 1)) t) (menuCovPrimitive D F.Mn F.m t)
            ((covOperator (menuCovPrimitive D F.Mn F.m t))^[l - 1 - a'] (fun y => F.aZ t y v))) x) := by
    refine ClassicalWindowBound.sum_finset _ fun l hl => ?_
    have hl' := Finset.mem_Icc.mp hl
    refine ClassicalWindowBound.smul_time continuous_const ?_
    refine ClassicalWindowBound.sum_finset _ fun a' ha' => ?_
    have ha'' := Finset.mem_range.mp ha'
    have hin : ClassicalWindowBound F.tp F.tf (K + 2 * a' + 1) (fun t x =>
        (covOperator (menuCovPrimitive D F.Mn F.m t))^[l - 1 - a'] (fun y => F.aZ t y v) x) :=
      ClassicalWindowBound.covOp_iterate (H := menuCovPrimitive D F.Mn F.m) hH (l - 1 - a')
        ((hz v).mono (by omega))
    have hcomm := ClassicalWindowBound.commFlux (H := menuCovPrimitive D F.Mn F.m) (D.Φ (F.m - 1))
      (D.hΦ _) hH (K := K + 2 * a') hin
    exact ClassicalWindowBound.covOp_iterate (H := menuCovPrimitive D F.Mn F.m) hH a' hcomm
  let a2 : F.Field := fun t y w =>
    covPolyP (menuCovPrimitive D F.Mn F.m t) F.p (fun y' => F.aZ t y' w) y
  have hG0 := glued_pi hg hi {0} (Finset.Icc 2 (F.N + 1))
    (by intro r hr; simp at hr; simp [hr]) (by
      intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega) a2 K
    (fun w => ha2 _ (by omega) w) v
  have hG1 := glued_pi hg hi (Finset.Icc 1 F.depth) (Finset.Icc 2 (F.N + Dm))
    (by intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega) (fun n hn => hn) a2 K
    (fun w => ha2 _ (by omega) w) v
  have hRef := ClassicalWindowBound.matGradPi (K := K)
    (R := ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m))
    (fun i j => FreshAxes.refFlux_entry_continuous (α := D.α) (q := D.q) (m := F.m)
      hi.stage.base hi.stage.profile (nativeBudget_kappa_pos hi) i j)
    (f := fun t x => a2 t x v) (ha2 (K + 1) (by omega) v)
  exact (hT1.sub (hG0.sub hRef)).sub hG1

/-- **The mean flux at the order `K ≤ N + 1`**, from the tight glued budget. -/
theorem meanFlux_order {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudgetTight F)
    (hi : NativeInput F) {dZ : F.Field} (hc : ClassicalTimeCurve F F.Naux F.aZ dZ)
    (K : ℕ) (hK : K ≤ F.N + 1) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf K (F.mean v) := by
  have hres := hi.auxiliary
  have hH := fun i j => nativeBudget_covPrimitive_continuous hi i j
  have hG := gFlux_pi_order hg hi hc (K + 4 * F.p + 1) (by omega) v
  have hQ := ClassicalWindowBound.covQ (H := menuCovPrimitive D F.Mn F.m) hH F.p
    (K := K + 2 * F.p) (hG.mono (by omega))
  have hPQ := ClassicalWindowBound.covP (H := menuCovPrimitive D F.Mn F.m) hH F.p
    (K := K) (f := fun t y => covPolyQ (menuCovPrimitive D F.Mn F.m t) F.p
      (fun y' => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y') y)
    (hQ.mono (by omega))
  have hU := ((upsilon_order hi hc (K + 2 * F.p) (by omega) v).map (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => hr v.1.root)).toContinuousLinearMap)
  have hPU := ClassicalWindowBound.covP (H := menuCovPrimitive D F.Mn F.m) hH F.p
    (K := K) (f := fun t y => WithLp.ofLp (F.upsilon v t y)) hU
  have h0 : ClassicalWindowBound F.tp F.tf (F.Naux - 2) (fun t x => F.aZ t x v) := hc.field v
  have h1 : ClassicalWindowBound F.tp F.tf (K + 1 + 2 * F.p) (fun t x => F.aZ t x v) :=
    h0.mono (by omega)
  have h2 := ClassicalWindowBound.covOp_iterate (H := menuCovPrimitive D F.Mn F.m) hH F.p h1
  have h3 := ClassicalWindowBound.smul_time (s := fun _ => ((F.p.factorial : ℝ)⁻¹))
    continuous_const h2
  have h4 := ClassicalWindowBound.matGradPi (K := K)
    (R := fun t => ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t - D.κ (F.m - 1) •
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) (nativeBudget_refFlux_continuous hi) h3
  have key := (((hG.mono (by omega : K ≤ K + 4 * F.p + 1)).sub hPQ).sub hPU).sub h4
  exact key.map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => hr v.1.root)).symm.toContinuousLinearMap

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Jet form to word form: a continuous linear map of the `m`-th jet `iteratedFDeriv ℝ m g x`
is a sum over the derivative words `α` and the components `u` of continuous linear maps applied to
`orderedDerivative α (g · u) x`; the word coefficients are the images of the map under FIXED
continuous linear maps, so every regularity property of the map passes to them. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- A continuous linear map on a finite product is the sum of its values on the coordinate
pieces. -/
theorem clm_pi_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] (Ψ : (∀ i, E i) →L[ℝ] W) (v : ∀ i, E i) :
    Ψ v = ∑ i, Ψ (ContinuousLinearMap.single ℝ E i (v i)) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  rfl

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Jet-level coefficients. A coefficient that is a continuous linear map on the whole `m`-jet
space has uniform window data in the sense of `NativeUniformCoeff` when it is smooth, periodic,
jointly continuous on the window and has constant spatial jet bounds (`JetCoeff`); its word
coefficients, the images under fixed linear maps, then have `NativeUniformCoeff`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- Uniform window data of a coefficient with values in the continuous linear maps of a normed
space (the jet space): smooth, periodic, jointly continuous on the window, constant jet bounds. -/
structure JetCoeff {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (a b : ℝ) (K : ℕ) (A : ℝ → Vec 2 → E →L[ℝ] W) :
    Prop where
  smooth : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (A t)
  periodic : ∀ t ∈ Icc a b, IsZ2Periodic (A t)
  continuous : Continuous (fun z : {z : ℝ × Vec 2 // z.1 ∈ Icc a b} => A z.1.1 z.1.2)
  bound : ∀ n ≤ K, ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x, ‖iteratedFDeriv ℝ n (A t) x‖ ≤ C

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Source budgets, part A: the macro flux and the macro residual at the orders the lift needs,
and the lift budget from the jet statement of the glued lift. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The glued lift of a field `g` of class `C^N` in space (at the times of the window) is a
differential operator of order `N` in `g` whose coefficients have uniform window data of order
zero. (Same proof as `NativeGluedPulseJet`, with the lift of one pulse in place of its mean flux.) -/
def NativeGluedLiftJet (F : Frame D hr Dm bw j₀) : Prop :=
  NativeInput F → ∀ v : CompIn F.G.comps,
    ∃ C : ∀ m : Fin (F.N + 1), DerivativeWord2 m.1 → ∀ u : CompIn F.G.comps,
        ℝ → Vec 2 → (hr u.1.root →L[ℝ] hr v.1.root),
      (∀ m α u, NativeUniformCoeff F.tp F.tf 0 (C m α u)) ∧
      ∀ (g : F.Field), ∀ t ∈ Icc F.tp F.tf,
        (∀ w, ContDiff ℝ ((F.N : ℕ) : ℕ∞) (fun x => g t x w)) → ∀ x,
          menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT g t x v =
            ∑ m : Fin (F.N + 1), ∑ α : DerivativeWord2 m.1, ∑ u : CompIn F.G.comps,
              C m α u t x (orderedDerivative α (fun y => g t y u) x)

/-- The lift budget: the glued lift of a field with the window bound of order `N` has the window
bound of order zero. -/
theorem liftBudget_of_jet {F : Frame D hr Dm bw j₀} (h : NativeGluedLiftJet F)
    (hi : NativeInput F) (g : F.Field)
    (hg : ∀ w, ClassicalWindowBound F.tp F.tf F.N (fun t x => g t x w)) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf 0 (fun t x =>
      menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT g t x v) := by
  obtain ⟨C, hC, hrep⟩ := h hi v
  have hterm : ClassicalWindowBound F.tp F.tf 0 (fun t x =>
      ∑ m : Fin (F.N + 1), ∑ α : DerivativeWord2 m.1, ∑ u : CompIn F.G.comps,
        C m α u t x (orderedDerivative α (fun y => g t y u) x)) := by
    refine ClassicalWindowBound.sum_fintype fun m => ?_
    refine ClassicalWindowBound.sum_fintype fun α => ?_
    refine ClassicalWindowBound.sum_fintype fun u => ?_
    have hw := (hg u).word α (L := 0) (by have := m.2; omega)
    exact ClassicalWindowBound.clm_apply (hC m α u) hw
  refine ClassicalWindowBound.congr_on (fun t ht => ?_) hterm
  funext x
  exact (hrep g t ht (fun w => (hg w).smooth t ht) x).symm

/-- A component of a window-bounded flux. -/
theorem fluxComp_window {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → Fin 2 → E}
    (h : ClassicalWindowBound a b K (fun t x => toFluxL (f t x))) (j : Fin 2) :
    ClassicalWindowBound a b K (fun t x => f t x j) :=
  h.map (PiLp.proj 2 (fun _ : Fin 2 => E) j)

/-- The macro flux at every order `K ≤ N + 1`, from the tight glued budget. -/
theorem macroFlux_order {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudgetTight F)
    (hi : NativeInput F) {dRep : F.Field}
    (hp : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep) (K : ℕ) (hK : K ≤ F.N + 1)
    (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf K (F.macroFluxField v) := by
  have hres := hi.auxiliary
  have hDm := hi.stage.order
  have ha : ∀ w, ClassicalWindowBound F.tp F.tf (K + (F.N + Dm))
      (fun t x => F.aRep t x w) := fun w => (hp.field w).mono (by omega)
  have h1 : ClassicalWindowBound F.tp F.tf K (fun t x => toFluxL (fun j => ∑ l : Fin 2,
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t - D.κ (F.m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j l •
        gradE (fun y => F.aRep t y v) x l)) :=
    ClassicalWindowBound.matGrad (nativeBudget_refFlux_continuous hi) (K := K)
      ((hp.field v).mono (by omega))
  have h2 : ClassicalWindowBound F.tp F.tf K (fun t x => toFluxL
      (menuGluedMeanFlux F.Mn F.G F.m {0} (Finset.Icc 2 (F.N + 1)) F.CcT F.aRep t x v)) :=
    hg hi {0} _ (by intro r hr; simp at hr; simp [hr]) (by
      intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega) F.aRep K ha v
  have h3 : ClassicalWindowBound F.tp F.tf K (fun t x => toFluxL (fun j => ∑ l : Fin 2,
      ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t j l • gradE (fun y => F.aRep t y v) x l)) :=
    ClassicalWindowBound.matGrad (fun i j => FreshAxes.refFlux_entry_continuous (α := D.α)
      (q := D.q) (m := F.m) hi.stage.base hi.stage.profile (nativeBudget_kappa_pos hi) i j)
      (K := K) ((hp.field v).mono (by omega))
  have h4 : ClassicalWindowBound F.tp F.tf K (fun t x => toFluxL
      (menuMeanFluxE F.Mn F.G F.m F.N F.depth F.CcT F.aRep t x v)) :=
    hg hi (Finset.Icc 1 F.depth) (Finset.Icc 2 (F.N + Dm)) (by
      intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega) (fun n hn => hn) F.aRep K ha v
  have h5 := (h1.add (h2.sub h3)).add h4
  have e : F.macroFluxField v = fun t x => (toFluxL (fun j => ∑ l : Fin 2,
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t - D.κ (F.m - 1) •
        (1 : Matrix (Fin 2) (Fin 2) ℝ)) j l •
        gradE (fun y => F.aRep t y v) x l) +
      (toFluxL (menuGluedMeanFlux F.Mn F.G F.m {0} (Finset.Icc 2 (F.N + 1)) F.CcT F.aRep t x v) -
        toFluxL (fun j => ∑ l : Fin 2, ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t j l •
          gradE (fun y => F.aRep t y v) x l))) +
      toFluxL (menuMeanFluxE F.Mn F.G F.m F.N F.depth F.CcT F.aRep t x v) := by
    funext t x
    rfl
  rw [e]
  exact h5

/-- The macro residual has the window bound of order `N`. -/
theorem macroRes_window {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudgetTight F)
    (hi : NativeInput F) {dRep : F.Field}
    (hp : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep) (w : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf F.N (fun t x => F.macroResidual dRep t x w) := by
  have hres := hi.auxiliary
  have hdR : ClassicalWindowBound F.tp F.tf F.N (fun t x => dRep t x w) :=
    (hp.derivativeBound w).mono (by omega)
  have hst := streamGrad_window (K := F.N) (D.Φ (F.m - 1)) (D.hΦ _)
    (f := fun t x => F.aRep t x w) ((hp.field w).mono (by omega))
  have hdiv := div_window (K := F.N) (a := F.tp) (b := F.tf)
    (f := fun t y => D.κ (F.m - 1) • gradE (fun y' => F.aRep t y' w) y +
      menuMacroFlux F.Mn F.G F.m F.N F.depth F.CcT F.aRep w t y) (fun j => by
        have e1 := ClassicalWindowBound.smul_time (s := fun _ => D.κ (F.m - 1)) continuous_const
          (gradComp_window (K := F.N + 1) ((hp.field w).mono (by omega)) j)
        have e2 := fluxComp_window (f := fun t y =>
          menuMacroFlux F.Mn F.G F.m F.N F.depth F.CcT F.aRep w t y)
          (macroFlux_order hg hi hp (F.N + 1) le_rfl w) j
        exact e1.add e2)
  exact (hdR.add hst).sub hdiv

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end
