-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.SourcesA
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseMain
import AVRegularity.Proofs.Results.Construction.SuccessorExists
import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativePreparedTime
import AVRegularity.Construction.Residual.Presentation.FluxAe
import AVRegularity.CycleReference.MeanEnhancementScale
import AVRegularity.Proofs.CascadeInvariants.ReserveGrade
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.Results.Construction.ComparisonLiftPositiveLayer
import AVRegularity.Proofs.Results.Construction.ContextCertified.Assemble

section
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! Native glued mean flux: the column aggregation. Each pulse term of the glued mean flux is a
finite operator on the physical jet of order `N + Dm` (`NativeGluedPulseJet`), from the pullback
expansion of the cutoff-weighted cell mean and the word operators: per pulse, grade and degree
the Eulerian factor and the cutoff are moved onto each componentwise cell mean (the fast slice is
continuous where the cutoff is active), the expansion and the word operators turn it into a
finite sum of jet operators, and the sum is split into its word columns.
The degenerate cases are included: an even pulse index gives the zero coefficient; empty
grade/degree sets, an empty component family and an inactive cutoff give zero on both sides. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The pulled-back slice of a pulse lift flux is continuous in the fast variable when the
cutoff is active. -/
theorem glued_slice_continuous
    {F : Frame D hr Dm bw j₀} (hi : NativeInput F) (p : OddSlot) (g n : ℕ) (hg : g ≤ F.depth)
    (a : F.Field) (t : ℝ)
    (ha : ∀ u, ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (fun y => a t y u))
    (hcut : ocCutoff D.α D.q D.Λ F.m p.1 t ≠ 0) (X : Vec 2) (k : Fin 2) :
    let clock := D.cellScaleSq F.m
    let ρ := F.Mn.lenFactor * liftLength D F.m
    let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
      (F.G.fam.fiber p (F.G.actual p))
    let chart := fun s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m p.1)
    Continuous (fun z => liftFluxX Q (F.CcT p.1)
      (fun s Y => a (clock * s) (chart (clock * s) (ρ • Y))) g n (clock⁻¹ * t) X z k) := by
  intro clock ρ Q chart
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hi.stage.base hi.stage.profile
    hi.stage.band F.m
  have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
    (Construction.Stream.ocTau_pos hi.stage.base : 0 < ocTau D.α D.q D.Λ F.m) hcut
  have htcell : clock⁻¹ * t ∈ Icc (D.slotStart F.m p.1 / D.cellScaleSq F.m)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m) := by
    rw [inv_mul_eq_div]
    exact ⟨div_le_div_of_nonneg_right htw.1 hc.le, div_le_div_of_nonneg_right htw.2 hc.le⟩
  let f : Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root := fun Y => a t (chart t (ρ • Y))
  have hchart : ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (fun Y : Vec 2 => chart t (ρ • Y)) :=
    ((CycleReference.streamFlow_spatial_smooth (D.hΦ (F.m - 1)) t
      (D.slotAnchor F.m p.1)).of_le (by simp)).comp (contDiff_const_smul ρ)
  have hf : ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) f :=
    contDiff_pi.mpr fun u => (ha u).comp hchart
  have he : (fun s Y => a (clock * s) (chart (clock * s) (ρ • Y))) (clock⁻¹ * t) =
      (fun _ : ℝ => f) (clock⁻¹ * t) := by
    have h1 : clock * (clock⁻¹ * t) = t := by
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    funext Y
    simp only [f, h1]
  rw [FluxCancellation.right_liftFluxX_time_congr Q (F.CcT p.1) _ (fun _ => f) g n _ he]
  exact native_input_lift_flux_slice_continuous hi p g n hg f hf _ htcell X k

/-- The zero coefficient has uniform window data. -/
theorem nativeUniformCoeff_zero {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace V] [MeasurableSpace W]
    (a b : ℝ) (K : ℕ) :
    NativeUniformCoeff a b K (fun (_ : ℝ) (_ : Vec 2) => (0 : V →L[ℝ] W)) :=
  ⟨fun _ _ => contDiff_const, fun _ _ _ _ => rfl, measurable_const,
    fun n _ => ⟨0, fun t _ x => by simp⟩⟩

/-- One pulse Eulerian term, component `j`: the cutoff and the Eulerian factor are moved onto
each componentwise cell mean (the slice is continuous where the cutoff is active). -/
theorem glued_pulse_component
    {F : Frame D hr Dm bw j₀} (hi : NativeInput F) (p : OddSlot) (g n : ℕ) (hg : g ≤ F.depth)
    (εc : ℝ) (a : F.Field)
    (t : ℝ) (ha : ∀ u, ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (fun y => a t y u)) (x : Vec 2)
    (v : CompIn F.G.comps) (j : Fin 2) :
    let clock := D.cellScaleSq F.m
    let ρ := F.Mn.lenFactor * liftLength D F.m
    let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
      (F.G.fam.fiber p (F.G.actual p))
    let chart := fun s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m p.1)
    let label := fun s y => D.flowOf (F.m - 1) (D.slotAnchor F.m p.1) y s
    (ocCutoff D.α D.q D.Λ F.m p.1 t •
      pulseMeanFluxEuler clock ρ εc n g Q (F.CcT p.1) chart label a t x v) j =
      ∑ k : Fin 2, (jacMatrix (chart t) (label t x) j k * (-(clock⁻¹ * εc ^ n * ρ))) •
        (ocCutoff D.α D.q D.Λ F.m p.1 t • fieldCellMean (fun z =>
          liftFluxX Q (F.CcT p.1) (fun s Y => a (clock * s) (chart (clock * s) (ρ • Y))) g n
            (clock⁻¹ * t) (ρ⁻¹ • label t x) z k v)) := by
  intro clock ρ Q chart label
  by_cases hcut : ocCutoff D.α D.q D.Λ F.m p.1 t = 0
  · simp only [hcut, zero_smul, smul_zero, Finset.sum_const_zero, Pi.zero_apply]
  simp only [Pi.smul_apply, pulseMeanFluxEuler, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [AVRegularity.CycleComparison.Lift.fieldCellMean_pi_apply _
    (glued_slice_continuous hi p g n hg a t ha hcut (ρ⁻¹ • label t x) k) v]
  simp only [smul_smul]
  congr 1
  ring

/-- **Column aggregation.** The pulse term of the glued mean flux is a finite operator on the
physical jet of order `N + Dm`, from the pullback expansion and the word operators. -/
theorem nativeGluedPulseJet_of_parts (hexp : NativeMeanPullbackExpansionStatement)
    (hword : NativeMeanPhysicalWordOperatorStatement) (F : Frame D hr Dm bw j₀) :
    NativeGluedPulseJet F := by
  classical
  intro hi rs ns hrs hns k v
  by_cases hk : Odd k
  swap
  · refine ⟨fun _ _ _ _ _ => 0, fun K _ _ _ => nativeUniformCoeff_zero _ _ K,
      fun a t _ _ x => ?_⟩
    simp only [nativeGluedPulse, hk, dite_false, Finset.sum_const_zero,
      zero_apply, toFluxL, WithLp.toLp_zero]
  let p : OddSlot := ⟨k, hk⟩
  let Jet := NativePhysicalJet (F.N + Dm) (CompIn F.G.comps) (fun u => hr u.1.root)
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let εc := ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ
  let chart := fun s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m k)
  let label := fun s y => D.flowOf (F.m - 1) (D.slotAnchor F.m k) y s
  have hterm (r n : ℕ) (kk j : Fin 2) (m : ℕ) (α : DerivativeWord2 m)
      (c : OrderedFinpartition m) (u : CompIn F.G.comps) :
      ∃ T : ℝ → Vec 2 → Jet →L[ℝ] hr v.1.root,
        r ≤ F.depth → 2 ≤ n → n ≤ F.N + Dm → m ≤ n - 1 →
        (∀ K, NativeUniformCoeff F.tp F.tf K T) ∧
        ∀ (f : Vec 2 → ∀ w : CompIn F.G.comps, hr w.1.root),
          ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (fun y => f y u) →
          ∀ t ∈ Icc F.tp F.tf, ∀ x,
            T t x (fun _q w u => orderedDerivative w (fun y => f y u) x) =
              (jacMatrix (chart t) (label t x) j kk *
                  (-((D.cellScaleSq F.m)⁻¹ * εc ^ n * ρ))) •
                (ocCutoff D.α D.q D.Λ F.m k t •
                  nativeStagePathMeanCoefficient hi.stage p r n kk m α
                    ((D.cellScaleSq F.m)⁻¹ * t) (ρ⁻¹ • label t x) 0 v u
                    ((c.compAlongOrderedFinpartition
                      (iteratedFDeriv ℝ c.length (fun y => f y u) x)
                      (fun i => iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y))
                        (ρ⁻¹ • label t x))) (fun i => basisVec (α (Fin.rev i))))) := by
    by_cases h : r ≤ F.depth ∧ 2 ≤ n ∧ n ≤ F.N + Dm ∧ m ≤ n - 1
    · obtain ⟨T, hT, he⟩ := hword hi p r n m h.1 h.2.1 h.2.2.1 h.2.2.2 kk j α c v u εc
      exact ⟨T, fun _ _ _ _ => ⟨hT, he⟩⟩
    · exact ⟨0, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ h⟩
  choose T hT using hterm
  let S := fun (j : Fin 2) (t : ℝ) (x : Vec 2) =>
    ∑ r ∈ rs, ∑ n ∈ ns, ∑ kk : Fin 2, ∑ m ∈ Finset.range n, ∑ α : DerivativeWord2 m,
      ∑ c : OrderedFinpartition m, ∑ u : CompIn F.G.comps, T r n kk j m α c u t x
  have hS (j : Fin 2) (K : ℕ) : NativeUniformCoeff F.tp F.tf K (S j) := by
    refine NativeUniformCoeff.sum_finset rs _ (fun r hr' => ?_)
    refine NativeUniformCoeff.sum_finset ns _ (fun n hn => ?_)
    refine NativeUniformCoeff.sum_finset Finset.univ _ (fun kk _ => ?_)
    refine NativeUniformCoeff.sum_finset (Finset.range n) _ (fun m hm => ?_)
    refine NativeUniformCoeff.sum_finset Finset.univ _ (fun α _ => ?_)
    refine NativeUniformCoeff.sum_finset Finset.univ _ (fun c _ => ?_)
    refine NativeUniformCoeff.sum_finset Finset.univ _ (fun u _ => ?_)
    have h2 := Finset.mem_Icc.mp (hns hn)
    exact (hT r n kk j m α c u (Finset.mem_Icc.mp (hrs hr')).2 h2.1 h2.2
      (by have := Finset.mem_range.mp hm; omega)).1 K
  let ι := fun j : Fin 2 => ContinuousLinearMap.single ℝ (fun _ : Fin 2 => hr v.1.root) j
  let B := fun t x => ∑ j : Fin 2, (ι j).comp (S j t x)
  have hB (K : ℕ) : NativeUniformCoeff F.tp F.tf K B :=
    NativeUniformCoeff.sum_finset Finset.univ _ (fun j _ => (hS j K).map
      (ContinuousLinearMap.compL ℝ Jet (hr v.1.root) (Fin 2 → hr v.1.root) (ι j)))
  let P :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => hr v.1.root)).symm.toContinuousLinearMap
  let A := fun t x => P.comp (B t x)
  have hA (K : ℕ) : NativeUniformCoeff F.tp F.tf K A :=
    (hB K).map (ContinuousLinearMap.compL ℝ Jet (Fin 2 → hr v.1.root) _ P)
  let E := fun (q : Fin (F.N + Dm + 1)) (w : DerivativeWord2 q.1) (u : CompIn F.G.comps) =>
    (ContinuousLinearMap.single ℝ (fun q : Fin (F.N + Dm + 1) =>
      DerivativeWord2 q.1 → ∀ u : CompIn F.G.comps, hr u.1.root) q).comp
      ((ContinuousLinearMap.single ℝ
        (fun _ : DerivativeWord2 q.1 => ∀ u : CompIn F.G.comps, hr u.1.root) w).comp
        (ContinuousLinearMap.single ℝ (fun u : CompIn F.G.comps => hr u.1.root) u))
  let C := fun q w u t x => (A t x).comp (E q w u)
  refine ⟨C, fun K q w u => (hA K).map
    ((ContinuousLinearMap.compL ℝ (hr u.1.root) Jet
      (PiLp 2 (fun _ : Fin 2 => hr v.1.root))).flip (E q w u)), ?_⟩
  intro a t ht ha x
  have heA : A t x (fun _q w u => orderedDerivative w (fun y => a t y u) x) =
      ∑ q : Fin (F.N + Dm + 1), ∑ w : DerivativeWord2 q.1, ∑ u : CompIn F.G.comps,
        C q w u t x (orderedDerivative w (fun y => a t y u) x) := by
    rw [clm_pi_sum (A t x)]
    refine Finset.sum_congr rfl fun q _ => ?_
    change ((A t x).comp (ContinuousLinearMap.single ℝ
      (fun q : Fin (F.N + Dm + 1) => DerivativeWord2 q.1 → ∀ u : CompIn F.G.comps, hr u.1.root) q))
        (fun w u => orderedDerivative w (fun y => a t y u) x) = _
    rw [clm_pi_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    change ((A t x).comp ((ContinuousLinearMap.single ℝ (fun q : Fin (F.N + Dm + 1) =>
      DerivativeWord2 q.1 → ∀ u : CompIn F.G.comps, hr u.1.root) q).comp
      (ContinuousLinearMap.single ℝ
        (fun _ : DerivativeWord2 q.1 => ∀ u : CompIn F.G.comps, hr u.1.root) w)))
        (fun u => orderedDerivative w (fun y => a t y u) x) = _
    rw [clm_pi_sum]
    rfl
  rw [← heA]
  change toFluxL _ = P (B t x _)
  simp only [P, ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv, toFluxL]
  congr 1
  funext j
  have hR : (∑ j' : Fin 2, (ι j').comp (S j' t x))
      (fun _q w u => orderedDerivative w (fun y => a t y u) x) j =
      S j t x (fun _q w u => orderedDerivative w (fun y => a t y u) x) := by
    fin_cases j <;> simp [ι]
  change nativeGluedPulse F rs ns a k t x v j = (∑ j' : Fin 2, (ι j').comp (S j' t x))
      (fun _q w u => orderedDerivative w (fun y => a t y u) x) j
  rw [hR]
  simp only [nativeGluedPulse, hk, dite_true, Finset.sum_apply, S, FunLike.coe_sum]
  refine Finset.sum_congr rfl fun r hr' => Finset.sum_congr rfl fun n hn => ?_
  have h2 := Finset.mem_Icc.mp (hns hn)
  have hr'' := (Finset.mem_Icc.mp (hrs hr')).2
  refine (glued_pulse_component hi p r n hr'' εc a t ha x v j).trans ?_
  refine Finset.sum_congr rfl fun kk _ => ?_
  have he := hexp hi p r n hr'' h2.1 h2.2 a t ht ha x kk v
  dsimp only at he
  rw [he, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact ((hT r n kk j m α c u hr'' h2.1 h2.2
    (by have := Finset.mem_range.mp hm; omega)).2 (a t) (ha u) t ht x).symm

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
section
/-! Source budgets, part B: `NativeSourceBudgets` from the tight glued budget and the jet
statement of the glued lift. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The mean divergence has the window bound of order `N`. -/
theorem meanDiv_window {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudgetTight F)
    (hi : NativeInput F) {dZ : F.Field} (hc : ClassicalTimeCurve F F.Naux F.aZ dZ)
    (w : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf F.N (fun t x => F.meanDiv t x w) :=
  div_window (K := F.N) (a := F.tp) (b := F.tf)
    (f := fun t y => WithLp.ofLp (F.mean w t y)) (fun j =>
      fluxComp_window (f := fun t y => WithLp.ofLp (F.mean w t y))
        (meanFlux_order hg hi hc (F.N + 1) le_rfl w) j)

/-- `liftedMean` has the window bound of order zero. -/
theorem liftedMean_window {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudgetTight F)
    (hL : NativeGluedLiftJet F) (hi : NativeInput F) {dZ : F.Field}
    (hc : ClassicalTimeCurve F F.Naux F.aZ dZ) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf 0 (fun t x => F.liftedMean t x v) :=
  liftBudget_of_jet hL hi F.meanDiv (fun w => meanDiv_window hg hi hc w) v

/-- `physSource` has the window bound of order zero. -/
theorem physSource_window {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudgetTight F)
    (hL : NativeGluedLiftJet F) (hi : NativeInput F) {dZ dRep dUh : F.Field}
    (hcs : NativeBudgetCurves F dZ dRep dUh) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf 0 (fun t x => F.physSource dRep dUh t x v) := by
  have hDm := hi.stage.order
  have hA : ClassicalWindowBound F.tp F.tf 0 (fun t x => dUh t x v) :=
    (hcs.lifted.derivativeBound v).mono (by omega)
  have hu : ClassicalWindowBound F.tp F.tf 2 (fun t x => F.uh t x v) :=
    (hcs.lifted.field v).mono (by omega)
  have hB := streamGrad_window (K := 0) (D.Φ F.m) (D.hΦ _)
    (f := fun t x => F.uh t x v) (hu.mono (by omega))
  have hC := div_window (K := 0) (a := F.tp) (b := F.tf)
    (f := fun t y => D.κ F.m • gradE (fun y' => F.uh t y' v) y +
      fun j => WithLp.ofLp (F.plain v t y) j) (fun j =>
        (ClassicalWindowBound.smul_time (s := fun _ => D.κ F.m) continuous_const
          (gradComp_window (K := 1) hu j)).add
        (fluxComp_window (f := fun t y => WithLp.ofLp (F.plain v t y))
          (nativeBudget_plain hi hcs.lifted v) j))
  have hD := liftBudget_of_jet hL hi (F.macroResidual dRep)
    (fun w => macroRes_window hg hi hcs.prepared w) v
  exact (liftedMean_window hg hL hi hcs.readout v).add ((hA.add hB |>.sub hC).sub hD)

/-- **`NativeSourceBudgets`** from the tight glued budget and the jet statement of the lift. -/
theorem sourceBudgets_of {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudgetTight F)
    (hL : NativeGluedLiftJet F) (dZ dRep dUh : F.Field) : NativeSourceBudgets F dZ dRep dUh := by
  intro hi hcs f hf v
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact liftedMean_window hg hL hi hcs.readout v
  · exact physSource_window hg hL hi hcs v

/-- The two jet statements together give the source budgets from the tight glued budget. -/
theorem sourceBudgets_of_jets {F : Frame D hr Dm bw j₀} (h : NativeGluedPulseJet F)
    (hL : NativeGluedLiftJet F) (dZ dRep dUh : F.Field) : NativeSourceBudgets F dZ dRep dUh :=
  sourceBudgets_of (nativeGlued_tight_of_jet h) hL dZ dRep dUh

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Final native representative assembly. The Sobolev and Banach time calculus is
re-exported through NativePreparedTime; the remaining mean/source budgets are
closed ingredient propositions on the actual stage and menu. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

section NativeLiftJetCalculus
open AVRegularity.Construction.Preservation.FullLift
local instance nativeLiftJetMeasurableSpace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) :
    MeasurableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V) := borel _
local instance nativeLiftJetBorelSpace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) :
    BorelSpace (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V) := ⟨rfl⟩
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {F : Frame D hr Dm bw j₀}

/-- The coefficient/chart factor acts on the finite physical word-jet carrier. -/
theorem native_input_pulse_physical_jet_operator (hi : NativeInput F) (p : OddSlot)
    (g n m : ℕ) (hg : g ≤ F.depth) (hn : n ≤ F.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (c : OrderedFinpartition m) (v u : CompIn F.G.comps)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label))
    (hcper : ∀ t l y, chart t (y + AVenhance.latticeShift l) = chart t y + AVenhance.latticeShift l)
    (hlper : ∀ t l y, label t (y + AVenhance.latticeShift l) = label t y + AVenhance.latticeShift l) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    ∃ T : ℝ → Vec 2 → NativePhysicalJet F.N (CompIn F.G.comps) (fun u => hr u.1.root) →L[ℝ] hr v.1.root,
      NativeUniformCoeff F.tp F.tf 0 T ∧
      ∀ (a : F.Field), ∀ t ∈ Icc F.tp F.tf,
        (∀ w, ContDiff ℝ (F.N : ℕ∞) (fun y => a t y w)) → ∀ x,
        T t x (fun _q w u => orderedDerivative w (fun y => a t y u) x) =
          ocCutoff D.α D.q D.Λ F.m p.1 t •
          F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
            (ρ⁻¹ • label t x) ((D.eps F.m)⁻¹ • label t x) v u
            ((c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (fun y => a t y u) x)
              (fun i => iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y))
                (ρ⁻¹ • label t x))) (fun i => basisVec (α (Fin.rev i)))) := by
  classical
  let Jet := NativePhysicalJet F.N (CompIn F.G.comps) (fun u => hr u.1.root)
  obtain ⟨L, hL, heL⟩ := native_input_pulse_word_operator_coeff hi p g n m hg hn hm α c v u
    chart label hchart hlabel hcper hlper
  obtain ⟨R, hR⟩ := native_physical_jet_word_projection (h := fun u : CompIn F.G.comps => hr u.1.root) F.N c.length
    (by have := c.length_le; omega) u
  let B := (ContinuousLinearMap.compL ℝ Jet
    (ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root))
    (hr v.1.root)).flip R
  refine ⟨fun t x => B (L t x), (hL 0).map B, ?_⟩
  intro a t ht ha x
  change L t x (R (fun _q w u => orderedDerivative w (fun y => a t y u) x)) = _
  rw [hR (fun y => a t y) (ha u) x]
  exact heL t ht x _

/-- The complete menu lift is a finite operator on the physical order-N jet,
with periodic, uniformly bounded coefficients on the closed observation window. -/
theorem native_input_glued_lift_jet (F : Frame D hr Dm bw j₀) : NativeGluedLiftJet F := by
  classical
  intro hi v
  let Jet := NativePhysicalJet F.N (CompIn F.G.comps) (fun u => hr u.1.root)
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let ε := ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ
  let ps := ocObsPulses D.α D.q D.Λ F.m F.tp F.tf
  let chart := fun (j : ps) s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m j.1)
  let label := fun (j : ps) s y => D.flowOf (F.m - 1) (D.slotAnchor F.m j.1) y s
  have hterm (j : ps) (g : Fin (F.depth + 1)) (n : Fin (F.N + 1))
      (m : Fin (n.1 + 1)) (α : DerivativeWord2 m.1) (c : OrderedFinpartition m.1)
      (u : CompIn F.G.comps) :
      ∃ T : ℝ → Vec 2 → Jet →L[ℝ] hr v.1.root,
        NativeUniformCoeff F.tp F.tf 0 T ∧
        ∀ (a : F.Field), ∀ t ∈ Icc F.tp F.tf,
          (∀ w, ContDiff ℝ (F.N : ℕ∞) (fun y => a t y w)) → ∀ x,
          T t x (fun _q w u => orderedDerivative w (fun y => a t y u) x) =
            ocCutoff D.α D.q D.Λ F.m j.1 t •
              F.CcT j.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
                (ρ⁻¹ • label j t x) ((D.eps F.m)⁻¹ • label j t x) v u
                ((c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (fun y => a t y u) x)
                  (fun i => iteratedFDeriv ℝ (c.partSize i) (fun Y => chart j t (ρ • Y))
                    (ρ⁻¹ • label j t x))) (fun i => basisVec (α (Fin.rev i)))) := by
    exact native_input_pulse_physical_jet_operator hi
      ⟨j.1, (Finset.mem_filter.mp j.2).2.1⟩ g n m (by omega) (by omega) (by omega) α c v u
      (chart j) (label j)
      ((CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
        (contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const (c := D.slotAnchor F.m j.1)))))
      ((CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
        ((contDiff_const (c := D.slotAnchor F.m j.1)).prodMk (contDiff_snd.prodMk contDiff_fst)))
      (fun t l y => FullLift.native_flow_latticeShift D _ _ _ l y)
      (fun t l y => FullLift.native_flow_latticeShift D _ _ _ l y)
  choose T hT heT using hterm
  let A := fun t x => ∑ j : ps, ∑ g : Fin (F.depth + 1), ∑ n : Fin (F.N + 1),
    ε ^ n.1 • ∑ m : Fin (n.1 + 1), ∑ α : DerivativeWord2 m.1,
      ∑ c : OrderedFinpartition m.1, ∑ u : CompIn F.G.comps, T j g n m α c u t x
  have hA : NativeUniformCoeff F.tp F.tf 0 A := by
    refine NativeUniformCoeff.sum_finset Finset.univ _ (fun j _ => ?_)
    refine NativeUniformCoeff.sum_finset Finset.univ _ (fun g _ => ?_)
    refine NativeUniformCoeff.sum_finset Finset.univ _ (fun n _ => ?_)
    have hm : NativeUniformCoeff F.tp F.tf 0 (fun t x =>
        ∑ m : Fin (n.1 + 1), ∑ α : DerivativeWord2 m.1,
          ∑ c : OrderedFinpartition m.1, ∑ u : CompIn F.G.comps, T j g n m α c u t x) := by
      refine NativeUniformCoeff.sum_finset Finset.univ _ (fun m _ => ?_)
      refine NativeUniformCoeff.sum_finset Finset.univ _ (fun α _ => ?_)
      refine NativeUniformCoeff.sum_finset Finset.univ _ (fun c _ => ?_)
      exact NativeUniformCoeff.sum_finset Finset.univ _ (fun u _ => hT j g n m α c u)
    exact hm.map ((ε ^ n.1) • ContinuousLinearMap.id ℝ (Jet →L[ℝ] hr v.1.root))
  let E := fun (q : Fin (F.N + 1)) (w : DerivativeWord2 q.1) (u : CompIn F.G.comps) =>
    (ContinuousLinearMap.single ℝ
      (fun q : Fin (F.N + 1) => DerivativeWord2 q.1 → ∀ u : CompIn F.G.comps, hr u.1.root) q).comp
      ((ContinuousLinearMap.single ℝ (fun _ : DerivativeWord2 q.1 => ∀ u : CompIn F.G.comps, hr u.1.root) w).comp
        (ContinuousLinearMap.single ℝ (fun u : CompIn F.G.comps => hr u.1.root) u))
  let C := fun q w u t x => (A t x).comp (E q w u)
  refine ⟨C, fun q w u => hA.map
    ((ContinuousLinearMap.compL ℝ (hr u.1.root) Jet (hr v.1.root)).flip (E q w u)), ?_⟩
  intro a t ht ha x
  have heA : A t x (fun _q w u => orderedDerivative w (fun y => a t y u) x) =
      ∑ q : Fin (F.N + 1), ∑ w : DerivativeWord2 q.1, ∑ u : CompIn F.G.comps,
        C q w u t x (orderedDerivative w (fun y => a t y u) x) := by
    rw [clm_pi_sum (A t x)]
    refine Finset.sum_congr rfl fun q _ => ?_
    change ((A t x).comp (ContinuousLinearMap.single ℝ
      (fun q : Fin (F.N + 1) => DerivativeWord2 q.1 → ∀ u : CompIn F.G.comps, hr u.1.root) q))
        (fun w u => orderedDerivative w (fun y => a t y u) x) = _
    rw [clm_pi_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    change ((A t x).comp ((ContinuousLinearMap.single ℝ
      (fun q : Fin (F.N + 1) => DerivativeWord2 q.1 → ∀ u : CompIn F.G.comps, hr u.1.root) q).comp
      (ContinuousLinearMap.single ℝ (fun _ : DerivativeWord2 q.1 => ∀ u : CompIn F.G.comps, hr u.1.root) w)))
        (fun u => orderedDerivative w (fun y => a t y u) x) = _
    rw [clm_pi_sum]
    rfl
  rw [← heA]
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hi.stage.base hi.stage.profile hi.stage.band F.m
  have htop : F.m - 1 ≤ D.term := by have := hi.stage.top; rw [hi.level] at this; omega
  have hρ : ρ ≠ 0 :=
    (mul_pos hi.stage.length_factor (Real.sqrt_pos.mpr
      (mul_pos (CycleReference.bandChain_pos hi.stage.base hi.stage.profile hi.stage.band htop)
        (Construction.Stream.ocTauPP_pos hi.stage.base)))).ne'
  have hτ : 0 < ocTau D.α D.q D.Λ F.m := Construction.Stream.ocTau_pos hi.stage.base
  have hpulse (j : ps) :
      ocCutoff D.α D.q D.Λ F.m j.1 t •
        pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m) ε F.N F.depth
          (F.CcT j.1) (chart j) (label j) a t x v =
      (∑ g : Fin (F.depth + 1), ∑ n : Fin (F.N + 1),
        ε ^ n.1 • ∑ m : Fin (n.1 + 1), ∑ α : DerivativeWord2 m.1,
          ∑ c : OrderedFinpartition m.1, ∑ u : CompIn F.G.comps, T j g n m α c u t x)
        (fun _q w u => orderedDerivative w (fun y => a t y u) x) := by
    simp only [sum_apply, smul_apply]
    simp_rw [heT j _ _ _ _ _ _ a t ht ha x]
    rw [FullLift.pulsePhysicalLift_freeze_time,
      show D.cellScaleSq F.m * ((D.cellScaleSq F.m)⁻¹ * t) = t by
        rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul],
      FullLift.pulsePhysicalLift_static_expansion]
    simp only [liftApply]
    rw [Finset.smul_sum]
    simp_rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [smul_comm (ocCutoff D.α D.q D.Λ F.m j.1 t) (ε ^ n.1)]
    apply congrArg (fun z : hr v.1.root => ε ^ n.1 • z)
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hs : ContDiff ℝ (m.1 : ℕ∞) (fun y => a t y u) :=
      (ha u).of_le (Nat.cast_le.mpr (by omega))
    have hfull : ContDiff ℝ (m.1 : ℕ∞) (fun y => a t y) :=
      contDiff_pi.mpr (fun u => (ha u).of_le (Nat.cast_le.mpr (by omega)))
    have hchart : ContDiff ℝ (m.1 : ℕ∞) (fun Y => chart j t (ρ • Y)) := by
      exact ((CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
        ((contDiff_const (c := t)).prodMk
          (((contDiff_const (c := ρ)).smul contDiff_id).prodMk
            (contDiff_const (c := D.slotAnchor F.m j.1))))).of_le (by simp)
    have hfullpull : ContDiff ℝ (m.1 : ℕ∞) (fun Y => a t (chart j t (ρ • Y))) :=
      hfull.comp hchart
    rw [ChartTransport.orderedDerivative_apply α hfullpull u]
    have hfa := native_pullback_word_eq_faa α (fun y => a t y u)
      (fun Y => chart j t (ρ • Y)) hs hchart (ρ⁻¹ • label j t x)
    simp only [Function.comp_def] at hfa
    rw [hfa, smul_inv_smul₀ hρ]
    have hinv : chart j t (label j t x) = x :=
      (CycleReference.streamFlowHomeomorph (D.hΦ (F.m - 1)) t (D.slotAnchor F.m j.1)).right_inv x
    rw [hinv]
    simp only [map_sum, Finset.smul_sum]
  have hsum : menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT a t x v =
      ∑ j : ps, ocCutoff D.α D.q D.Λ F.m j.1 t •
        pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m) ε F.N F.depth
          (F.CcT j.1) (chart j) (label j) a t x v := by
    unfold menuLiftedRep gluedLift
    simp only [Finset.sum_apply, Pi.smul_apply]
    let P : ℤ → hr v.1.root := fun j => ocCutoff D.α D.q D.Λ F.m j t •
      pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m) ε F.N F.depth (F.CcT j)
        (fun s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m j))
        (fun s y => D.flowOf (F.m - 1) (D.slotAnchor F.m j) y s) a t x v
    change (∑ j ∈ ocObsPulses D.α D.q D.Λ F.m t t, P j) = ∑ j : ps, P j
    rw [Finset.sum_coe_sort ps P]
    refine Finset.sum_subset
      (Construction.Residual.Presentation.obsPulses_time_subset D.α D.q D.Λ F.m hτ ht)
      (fun j hj hnj => ?_)
    have hout : t ∉ ocPulseWindow D.α D.q D.Λ F.m j := fun hin => hnj
      (Construction.Residual.Presentation.mem_obsPulses_time D.α D.q D.Λ F.m hτ
        (Finset.mem_filter.mp hj).2.1 hin)
    dsimp only [P]
    rw [WeakEntryProofs.ocCutoff_zero_off_output D.α D.q D.Λ F.m hτ j t hout, zero_smul]
  rw [hsum]
  simp only [A, sum_apply]
  exact Finset.sum_congr rfl (fun j _ => by simpa only [sum_apply] using hpulse j)

/-- Every actual Eulerian mean word is a periodic all-order physical-jet operator. -/
theorem nativeMeanPhysicalWordOperator : NativeMeanPhysicalWordOperatorStatement := by
  intro hr _hnorm _hip _hfd _hms _hbs _hcomplete D Dm bw j₀ F hi p
    g n m hg hn hnN hm k j α c v u εc
  classical
  dsimp only
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let chart := fun s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m p.1)
  let label := fun s y => D.flowOf (F.m - 1) (D.slotAnchor F.m p.1) y s
  have hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart) :=
    (CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const (c := D.slotAnchor F.m p.1))))
  have hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label) :=
    (CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
      ((contDiff_const (c := D.slotAnchor F.m p.1)).prodMk (contDiff_snd.prodMk contDiff_fst))
  obtain ⟨L, hL, heL⟩ := native_input_mean_word_operator_coeff_of_path_action nativeStagePathMeanAction hi p
    g n m hg hn hnN hm k α c v u chart label hchart hlabel
    (fun t l y => native_flow_latticeShift D _ _ _ l y)
    (fun t l y => native_flow_latticeShift D _ _ _ l y)
  let Jet := NativePhysicalJet (F.N + Dm) (CompIn F.G.comps) (fun u => hr u.1.root)
  obtain ⟨R, hR⟩ := native_physical_jet_word_projection (h := fun u : CompIn F.G.comps => hr u.1.root) (F.N + Dm) c.length
    (by have := c.length_le; omega) u
  let B := (ContinuousLinearMap.compL ℝ Jet
    (ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root))
    (hr v.1.root)).flip R
  let U := fun t x => B (L t x)
  have hU : ∀ K, NativeUniformCoeff F.tp F.tf K U := fun K => (hL K).map B
  let scale := -((D.cellScaleSq F.m)⁻¹ * εc ^ n * ρ)
  let w := fun t x => jacMatrix (chart t) (label t x) j k * scale
  have hw : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry w) :=
    ((WeakEntryProofs.jacMatrix_spacetime_entry_smooth hchart j k).comp
      (contDiff_fst.prodMk hlabel)).mul contDiff_const
  have hW := native_smooth_uniform_time_data w hw (a := F.tp) (b := F.tf)
  have hwper : ∀ t ∈ Icc F.tp F.tf, AVenhance.IsZ2Periodic (w t) := by
    intro t _ht l x
    change jacMatrix (chart t) (label t (x + AVenhance.latticeShift l)) j k * scale = _
    have hshift : label t (x + AVenhance.latticeShift l) =
        label t x + AVenhance.latticeShift l :=
      native_flow_latticeShift D (F.m - 1) (D.slotAnchor F.m p.1) t l x
    rw [hshift]
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M j k * scale)
      (CycleReference.streamFlow_jacMatrix_spatial_periodic (D.hΦ (F.m - 1))
        t (D.slotAnchor F.m p.1) (label t x) l)
  let O := Jet →L[ℝ] hr v.1.root
  let nativeMeanPhysicalOperatorNormedSpace : NormedSpace ℝ O := inferInstance
  let nativeMeanPhysicalOperatorBoundedSMul : IsBoundedSMul ℝ O :=
    IsBoundedSMul.of_norm_smul_le (α := ℝ) (β := O) (fun r x => NormedSpace.norm_smul_le r x)
  let S := ContinuousLinearMap.lsmul (E := O) ℝ ℝ
  let T := fun t x => S (w t x) (U t x)
  have hTsp : ∀ R X, IsCompact X → NativeCompactSpatialBudget F.tp F.tf R X T := by
    intro R X hX
    change NativeCompactSpatialBudget F.tp F.tf R X (fun t x => S (w t x) (U t x))
    exact native_uniform_bilinear_spatial_budget (Z := O) S hW.spatial
      (fun R X _ => NativeUniformCoeff.compact_spatial_budget hU R X) R X hX
  have hTm : Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc F.tp F.tf} => T p.1.1 p.1.2) :=
    (((S.continuous.comp continuous_fst).clm_apply continuous_snd).measurable).comp
      (hW.measurable.prodMk (hU 0).measurable)
  have hTp : ∀ t ∈ Icc F.tp F.tf, AVenhance.IsZ2Periodic (T t) := by
    intro t ht l x
    change w t (x + AVenhance.latticeShift l) • U t (x + AVenhance.latticeShift l) = _
    rw [hwper t ht l x, (hU 0).periodic t ht l x]
    rfl
  refine ⟨T, fun K => native_uniform_coeff_of_spatial_data hTsp hTm hTp K, ?_⟩
  intro f hf t ht x
  change w t x • L t x (R (fun _q w u => orderedDerivative w (fun y => f y u) x)) = _
  rw [hR f hf x, heL t ht x]

end NativeLiftJetCalculus

/-- Closed production of the finite physical mean-flux jet on every actual frame. -/
def NativeMeanJetProductionStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (F : Frame D hr Dm bw j₀),
    NativeGluedPulseJet F

/-- All native temporal representatives, from the remaining mean-flux jet ingredient.
The actual time curves, the gluing, finite lift jet and source and upsilon budgets are
discharged by their existing proofs. -/
theorem native_temporal_representatives_of_budget_ingredients
    (hmean : NativeMeanJetProductionStatement) :
    NativeTemporalRepresentativesStatement := by
  intro hr _hnorm _hip _hfd _hms _hbs _hcomplete D Dm bw j₀ F hi
  obtain ⟨dZ, dRep, dUh, hZ, hRep, hUh, hT⟩ := native_input_classical_time_packages hi
  have hcs : NativeBudgetCurves F dZ dRep dUh := ⟨hZ, hRep, hUh⟩
  have hg : NativeGluedMeanBudget F := nativeGlued_budget_of_jet (hmean F)
  have hfields := nativeBudget_fields F hi dZ dRep dUh hcs
    (fun hi' hc => nativeBudget_fluxes_of hg (nativeUpsilon_window hi' hc)
      hi' dZ dRep dUh hc)
    (nativeBudget_readoutFluxBudget_of hg dZ dRep dUh)
    (nativeUpsilon_budget F dZ dRep dUh)
    (sourceBudgets_of_jets (hmean F) (native_input_glued_lift_jet F) dZ dRep dUh)
  have hν : 0 < D.κ F.m := CycleReference.bandChain_pos hi.stage.base
    hi.stage.profile hi.stage.band (by rw [← hi.level]; exact hi.stage.top)
  have hR : Regularity F dZ dRep dUh := {
    reserve := by have := hi.auxiliary; omega
    clock_nonzero := (EntryWeakProofs.weakData_cellScaleSq_pos
      D hi.stage.base hi.stage.profile hi.stage.band F.m).ne'
    covarianceDerivative := ae_of_all _ (fun t i j =>
      native_menu_covariance_derivative D F.Mn F.m hi.stage.base hi.stage.profile hν t i j)
    covarianceSymmetric := native_menu_covariance_symmetric D F.Mn F.m hi.stage.base hi.stage.profile
    readout := hZ
    prepared := hRep
    lifted := hUh
    kernelFields := hfields.kernelFields
    coarseDrift := hfields.coarseDrift
    fineDrift := hfields.fineDrift
    fluxes := hfields.fluxes
    readoutFluxRegularity := hfields.readoutFluxRegularity
    upsilonRegularity := hfields.upsilonRegularity
    sources := hfields.sources }
  exact ⟨dZ, dRep, dUh, hR, hT⟩

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Cascade adapter: a uniform production statement for clauses about the incoming stage `G`
and the full actual successor `G'`, with the same prefix as the covariance-transport statement.
Two clauses admit common thresholds, carrier constants and level floors. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

/-- A clause on the incoming stage and its full actual successor. -/
abbrev CascadeAdapterClause :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ},
    ProvParams → SuccMenu → (ℕ → KernelSpec) → (ℕ → KernelSpec) → InvConsts →
    GenStage D hr Dm bw j₀ → GenStage D hr Dm bw j₀ → Prop

/-- Uniform production of a cascade adapter clause under the covariance-transport prefix. -/
def CascadeAdapterStatement (α s q : ℝ) (ζ : ℝ → ℝ) (clause : CascadeAdapterClause) : Prop :=
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
    ∃ mStar : ℕ,
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      (∃ tA : ℝ, tS ≤ tA ∧
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G) →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      clause (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seedK freshK kI G G'

/-- Two uniform clauses admit common thresholds, carrier constants and starting levels. -/
theorem cascadeAdapter_and {α s q : ℝ} {ζ : ℝ → ℝ} {A B : CascadeAdapterClause}
    (ha : CascadeAdapterStatement α s q ζ A) (hb : CascadeAdapterStatement α s q ζ B) :
    CascadeAdapterStatement α s q ζ (fun P Mn seedK freshK kI G G' =>
      A P Mn seedK freshK kI G G' ∧ B P Mn seedK freshK kI G G') := by
  classical
  obtain ⟨Λa, hΛa, ha⟩ := ha
  obtain ⟨Λb, hΛb, hb⟩ := hb
  refine ⟨max Λa Λb, by omega, ?_⟩
  intro Λ hΛ
  obtain ⟨ca, hca, ha⟩ := ha Λ (by omega)
  obtain ⟨cb, hcb, hb⟩ := hb Λ (by omega)
  refine ⟨min ca cb, lt_min hca hcb, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨ta, CHa, Υa, hCHa, hΥa, ha⟩ := ha φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨tb, CHb, Υb, hCHb, hΥb, hb⟩ := hb φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_right _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨certificateThresholdJoin ta tb, max CHa CHb, max Υa Υb,
    hCHa.trans (le_max_left _ _), hΥa.trans_le (le_max_left _ _), ?_⟩
  intro kI hkI
  obtain ⟨CIa, Cwa, ha⟩ := ha kI (invariant_admissible_threshold_left hkI)
  obtain ⟨CIb, Cwb, hb⟩ := hb kI (invariant_admissible_threshold_right hkI)
  refine ⟨max CIa CIb, max Cwa Cwb, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hLa : IsLedgerAdmissible Ce CI Cw CIa Cwa :=
    ⟨hledger.1, (le_max_left _ _).trans hledger.2.1,
      (le_max_left _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLb : IsLedgerAdmissible Ce CI Cw CIb Cwb :=
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1,
      (le_max_right _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le
  obtain ⟨ma, ha⟩ := ha CI Cw j₀ hLa (IsCarrierStart.mono hA hT
    (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCHa) hΥa.le hstart)
  obtain ⟨mb, hb⟩ := hb CI Cw j₀ hLb (IsCarrierStart.mono hA hT
    (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCHb) hΥb.le hstart)
  refine ⟨max ma mb, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    G G' hcascade hlevel hG hactual
  exact ⟨ha D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM G G' hcascade hlevel hG hactual,
    hb D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM G G' hcascade hlevel hG hactual⟩

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Cascade adapter: the context certificate and the nonnegative reserves of the FULL actual
successor `G'` (`Providers.successor_context_certified` exports only the retained
part). The proof reruns its assembly and keeps the certificate of `G'`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

/-- The outgoing context certificate with nonnegative reserves. -/
def cascadeAdapterContextClause : CascadeAdapterClause :=
  fun _ _ _ _ kI _ G' => G'.IsContextCertified kI ∧ ∀ v : CompIn G'.comps, 0 ≤ compReserve kI v.1

/-- The ledger and the carrier calculus give the context certificate of `G'` under the covariance-transport prefix. -/
theorem cascadeAdapter_context (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    CascadeAdapterStatement α s q ζ cascadeAdapterContextClause := by
  obtain ⟨Λ₂, hΛ₂, hled⟩ := Providers.successor_ledger α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₃, -, hcalc⟩ := Providers.gen_carrier_calculus α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max Λ₂ Λ₃, le_max_of_le_left hΛ₂, fun Λ hΛ => ?_⟩
  obtain ⟨c₂, hc₂, hled⟩ := hled Λ ((le_max_left _ _).trans hΛ)
  have hcalc := hcalc Λ ((le_max_right _ _).trans hΛ)
  refine ⟨c₂, hc₂, ?_⟩
  intro φ₀ hφ₀ hφs hφn hφi hφsupp bw hbw0 hbw1 Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc0 hc0max
    hcr0 hcr1 hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsch hNaux hKres
    hseedA hsX hsZ
  obtain ⟨thr, hled⟩ := hled φ₀ hφ₀ hφs hφn hφi hφsupp bw hbw0 hbw1 Q T₀ hQ hT₀ Ce τe kS r₀ D₀
    hCe hτe hc0 hc0max hcr0 hcr1 hσf hlamC H J N p nk Lc Lf Lpr Acl
    Naux Nout Kres npad sX sZ σ₀ a σ hsch hNaux hKres hseedA hsX hsZ
  obtain ⟨Υ₀, hcalc⟩ := hcalc bw hbw0 hbw1
  have hΥ100 : (100 : ℝ) ≤ max (max Υ₀ (4 * (8 * Real.pi ^ 2))) 100 := le_max_right _ _
  obtain ⟨κ, hκ, hcalc⟩ := hcalc 1 (max (max Υ₀ (4 * (8 * Real.pi ^ 2))) 100)
    ⟨le_rfl, le_max_left _ _⟩
  refine ⟨thr, 1, max (max Υ₀ (4 * (8 * Real.pi ^ 2))) 100, le_rfl, by linarith,
    fun kI hadm => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hHprod, -⟩ := id hadm
  obtain ⟨CIthr, Cwthr, hled⟩ := hled 1 _ le_rfl hΥ100 κ hκ kI hadm
  refine ⟨CIthr, Cwthr, fun CI Cw j₀ hLA hcs => ?_⟩
  obtain ⟨mStar, hled⟩ := hled CI Cw j₀ hcs
  refine ⟨max mStar (j₀ + 2), ?_⟩
  intro D hDα hDq hDΛ hDζ hΦ M hκb hterm Mnat hMnat law hlaw hr _ _ _ _ _ _ _ seedK freshK hfresh
    seed n tS tf hseed m hm hmn hnM G G' hcas hlev hinv hSucc
  have hledG := hled D hDα hDq hDΛ hDζ hΦ M hκb hterm Mnat hMnat law hlaw seedK freshK hfresh
    seed n tS tf hseed m ⟨hLA, (le_max_left _ _).trans hm⟩ hmn hnM G G' hcas hlev hinv hSucc
  have hjm : j₀ + 2 ≤ m := (le_max_right _ _).trans hm
  have hlev' : G'.level = G.level - 1 := hSucc.2.1
  have hj0 : j₀ ≤ G'.level := by omega
  have h1 : 1 ≤ G'.level := by omega
  have hres : ∀ v : CompIn G'.comps, 0 ≤ compReserve kI v.1 := fun v =>
    Providers.CascadeInvariants.compReserve_nonneg_of_succ kI (H := H) hHprod
      (Providers.CascadeInvariants.grade_le_of_succ (Providers.CascadeInvariants.grade_le_of_cascade hseed.2.1 hcas)
        hSucc v)
  have hcert := GenStage.isContextCertified_of_gates G' kI κ
    (fun p hp Δ hΔ leaf hL e hs hsf f hf => hcalc j₀ hcs D hDα hDq hDΛ hDζ hΦ M hκb hterm
      G'.level p h1 hj0 hp Δ hΔ leaf hL e hs hsf f hf) hres hledG
  exact ⟨hcert, hres⟩

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Cascade adapter: the incoming stage-successor certificates as a uniform clause. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- The incoming certificates `StageSuccessor.Input` of the cascade stage. -/
def cascadeAdapterInputClause : CascadeAdapterClause :=
  fun P Mn _ _ _ G _ => StageSuccessor.Input P Mn G

/-- The cascade successor inputs, read as an adapter clause. -/
theorem cascadeAdapter_input {α s q : ℝ} {ζ : ℝ → ℝ}
    (h : Construction.StageSuccessor.CascadeSuccessorInputsStatement α s q ζ) :
    CascadeAdapterStatement α s q ζ cascadeAdapterInputClause := by
  obtain ⟨Λ₀, h128, h⟩ := h
  refine ⟨Λ₀, h128, fun Λ hΛ => ?_⟩
  obtain ⟨c, hc, h⟩ := h Λ hΛ
  refine ⟨c, hc, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, h⟩ := h φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀
    hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, fun kI hkI => ?_⟩
  obtain ⟨CIt, Cwt, h⟩ := h kI hkI
  refine ⟨CIt, Cwt, fun CI Cw j₀ hl hs => ?_⟩
  obtain ⟨mS, h⟩ := h CI Cw j₀ hl hs
  refine ⟨mS, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    G G' hcascade hlevel hG hactual
  exact h D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM G hcascade hlevel hG

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end
