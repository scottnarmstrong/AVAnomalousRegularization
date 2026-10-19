-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofSourceMean
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseMain
import AVRegularity.EntryWeakAssembly.FiniteStagePaths
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofSourceMeanDirect
import AVRegularity.Proofs.GenSem.Transfer.Assemble
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.EntryWeak.NormalizedPulseTransverse
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.Proofs.GenSem.Op.FamChart
import AVenhance.Infra.Construction.StreamAdmissible

section
section
/-! The first-source-flux step, sub-step Diagonal: split and assembly.

`FSStepDiagShift` follows from the per-pulse identity `FSDiagTerm`: for an active finer slot `k`
of the piece, the push-forward by the appended child of the grade-zero label flux of order `n`
(`diagLabelFlux`, scalar lifts `Cc0 k (appended child)`) acting on the translated scalarization
`ℓ ∘ a(x + ·)` is `ℓ` of the Hilbert mean flux of the native family of `k`
(`pulseMeanFluxEuler`, lifts `CcT k`). The glue over the scheduled slots equals the glue over the
observed pulses (`finsum_sched_eq_sum`, `tc_sum_obsPulses_eq_activeSlots`), the reference-flux terms
agree by linearity, and the sum over `n` splits. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The mean flux of order `n` and grade `0` of the native family of the pulse `k` (without the
cut-off), the summand of `menuGluedMeanFlux`. -/
def fsPulseRaw (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (n : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (z : Vec 2)
    (v : CompIn G.comps) (k : ℤ) : Fin 2 → hr v.1.root :=
  if hk : Odd k then
    pulseMeanFluxEuler (D.cellScaleSq G.level) (Mn.lenFactor * liftLength D G.level)
      (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) / (Mn.lenFactor * liftLength D G.level))
      n 0 (familyLiftData D G.level k (nativeChain G.level k) (Mn.lenFactor * liftLength D G.level)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k)
      (fun s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level k))
      (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s') a t z v
  else 0

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem fsDiag_glued_eq (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (n : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (z : Vec 2)
    (v : CompIn G.comps) :
    menuGluedMeanFlux Mn G G.level {0} {n} CcT a t z v =
      ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t,
        ocCutoff D.α D.q D.Λ G.level k t • fsPulseRaw Mn G n CcT a t z v k := by
  unfold menuGluedMeanFlux fsPulseRaw
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_singleton]
  split_ifs <;> simp

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
open scoped Classical in
/-- **The glue.** If the per-pulse identity holds at every pulse of nonzero cut-off, the grade-zero
mean flux of order `n` at the recentred actual context is `ℓ` of the Hilbert mean flux. -/
theorem fsDiag_mean_of_term {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    {depth : ℕ} {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : SplitInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ)
    (hp : G'.fam.weight p t ≠ 0) (x : Vec 2) (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (x' : Vec 2) (j : Fin 2) (n : ℕ)
    (hterm : ∀ k : ℤ, Odd k → ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
      (if IsAdmissibleChain D b j₀ G.level k
          ((fsCtx G' p t x).appendChild D k t
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) then
        pushFlux (((fsCtx G' p t x).appendChild D k t
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMap D t)
          (((fsCtx G' p t x).appendChild D k t
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMapInv D t)
          (diagLabelFlux D Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 k
            ((fsCtx G' p t x).appendChild D k t
              ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) n t)
          (fun y => ℓ (a t (x + y) v)) x'
       else 0) j = ℓ (fsPulseRaw Mn G n CcT a t (x + x') v k j)) :
    diagMeanFluxCtx D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 t
        (fsCtx G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) n
        (fun y => ℓ (a t (x + y) v)) x' j =
      ℓ (menuGluedMeanFlux Mn G G.level {0} {n} CcT a t (x + x') v j) := by
  classical
  obtain ⟨h1, -, hL⟩ := fsAlg_level_pos hin
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  have hΛ : 1 ≤ D.Λ := hin.stage.base
  have hτ : 0 < ocTau D.α D.q D.Λ G'.level := Construction.Stream.ocTau_pos hΛ
  have hcp : ocCutoff D.α D.q D.Λ G'.level p.1 t ≠ 0 := by rw [← hnat.2.1 p t]; exact hp
  have htc : t ∈ ocPulseWindow D.α D.q D.Λ (G.level - 1) p.1 := by
    rw [← hL]; exact Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcp
  have hlev : G.level - 1 + 1 = G.level := by omega
  set X : ℤ → Vec 2 := fun k =>
    if IsAdmissibleChain D b j₀ G.level k
        ((fsCtx G' p t x).appendChild D k t
          ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) then
      pushFlux (((fsCtx G' p t x).appendChild D k t
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMap D t)
          (((fsCtx G' p t x).appendChild D k t
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMapInv D t)
          (diagLabelFlux D Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 k
            ((fsCtx G' p t x).appendChild D k t
              ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) n t)
          (fun y => ℓ (a t (x + y) v)) x'
    else 0 with hX
  have e1 := finsum_sched_eq_sum (D := D) hΛ (m := G.level - 1) (c := p.1) htc X
  rw [hlev] at e1
  have hslot : (fsCtx G' p t x).slot = p.1 := by rw [fsAlg_ctx_native hin]; rfl
  have e2 : diagMeanFluxCtx D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 t
        (fsCtx G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) n
        (fun y => ℓ (a t (x + y) v)) x' =
      ∑ᶠ (k : ℤ) (_ : Odd k ∧ IsScheduledIn D (G.level - 1) k p.1),
        ocCutoff D.α D.q D.Λ G.level k t • X k := by
    unfold diagMeanFluxCtx
    rw [hslot]
    refine finsum_congr fun k => finsum_congr fun hk => ?_
    simp only [hX]
    split_ifs <;> simp
  rw [e2, e1, fsDiag_glued_eq]
  have e3 := tc_sum_obsPulses_eq_activeSlots D hΛ (G.level - 1) t (E := ℝ)
    (fun k => ℓ (fsPulseRaw Mn G n CcT a t (x + x') v k j))
  rw [hlev] at e3
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul] at e3 ⊢
  rw [e3]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hc : ocCutoff D.α D.q D.Λ G.level k.1 t = 0
  · simp [hc]
  · congr 1
    exact hterm k.1 k.2 hc

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The glued mean flux of several degrees is the sum over the degrees. -/
theorem fsDiag_gm_split (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (rs ns : Finset ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (z : Vec 2)
    (v : CompIn G.comps) :
    menuGluedMeanFlux Mn G G.level rs ns CcT a t z v =
      ∑ n ∈ ns, menuGluedMeanFlux Mn G G.level rs {n} CcT a t z v := by
  unfold menuGluedMeanFlux
  simp only [Finset.sum_singleton]
  exact (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans Finset.sum_comm

/-- The reference-flux term, scalarized and translated. -/
theorem fsDiag_ref {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (refM : Matrix (Fin 2) (Fin 2) ℝ) (A : Vec 2 → W) (ℓ : W →L[ℝ] ℝ) (x x' : Vec 2)
    (hA : DifferentiableAt ℝ A (x + x')) (j : Fin 2) :
    ℓ (∑ l : Fin 2, refM j l • gradE A (x + x') l) =
      (refM.mulVec (gradField (fun y => ℓ (A (x + y))) x')) j := by
  have h1 : fderiv ℝ (fun y => ℓ (A (x + y))) x' = ℓ.comp (fderiv ℝ A (x + x')) := by
    rw [fderiv_comp_add_left (f := fun y => ℓ (A y))]
    exact (ℓ.hasFDerivAt.comp (x + x') hA.hasFDerivAt).fderiv
  simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, gradField, gradE, h1]
  rfl

/-- **Sub-step Diagonal** from the per-pulse identity. -/
def FSDiagTerm : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y => a t y v)) →
    ∀ (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (x' : Vec 2) (j : Fin 2) (n : ℕ),
      2 ≤ n → n ≤ Mn.N + 1 → ∀ k : ℤ, Odd k → ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
      (open scoped Classical in
        if IsAdmissibleChain D b j₀ G.level k
            ((fsCtx G' p t x).appendChild D k t
              ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) then
          pushFlux (((fsCtx G' p t x).appendChild D k t
              ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMap D t)
            (((fsCtx G' p t x).appendChild D k t
              ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMapInv D t)
            (diagLabelFlux D Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 k
              ((fsCtx G' p t x).appendChild D k t
                ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) n t)
            (fun y => ℓ (a t (x + y) v)) x'
         else 0) j = ℓ (fsPulseRaw Mn G n CcT a t (x + x') v k j)

/-- **Sub-step Diagonal (translated to the centre) from the per-pulse identity.** -/
theorem fsStepDiagShift_of_term (T : FSDiagTerm) : FSStepDiagShift := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x a ha v ℓ x' j
  have hN : 1 ≤ Mn.N := hin.stage.cutoff
  have hmean : ∀ n, 2 ≤ n → n ≤ Mn.N + 1 →
      diagMeanFluxCtx D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 t
        (fsCtx G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) n
        (fun y => ℓ (a t (x + y) v)) x' j =
      ℓ (menuGluedMeanFlux Mn G G.level {0} {n} CcT a t (x + x') v j) := fun n h2 h3 =>
    fsDiag_mean_of_term hin W p t hp x a v ℓ x' j n (fun k hk hc =>
      T P Mn G G' depth CcT hin W p t hp x a ha v ℓ x' j n h2 h3 k hk hc)
  have hdiff : DifferentiableAt ℝ (fun y => a t y v) (x + x') :=
    ((ha v).differentiable (by norm_cast; omega)) _
  have hsplit : Finset.Icc 2 (Mn.N + 1) = insert 2 (Finset.Icc 3 (Mn.N + 1)) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  unfold diagFluxCtx menuDiagFluxPhys
  rw [fsDiag_gm_split, hsplit, Finset.sum_insert (by simp)]
  simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, map_sub, map_add, map_sum]
  have href := fsDiag_ref (ocRefFlux D.α D.q D.Λ D.ζ G.level (D.κ G.level) t)
    (fun y => a t y v) ℓ x x' hdiff j
  simp only [map_sum] at href
  rw [hmean 2 le_rfl (by omega), href]
  rw [Finset.sum_congr rfl (fun n hn => hmean n (by simp only [Finset.mem_Icc] at hn; omega)
    (by simp only [Finset.mem_Icc] at hn; omega))]
  ring

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **Source mean, Right: regularity of the pushed path mean.**

`right_pathEdge_boxSmooth`: the lifted edges of the path family on the native chain are box smooth
at the pulse clock. `rightPathReg`: the pushed path mean of a smooth field is `C^{2p}`, by
`pulseMeanFluxEuler_contDiff` on the path family. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport CovFluxReg Providers.GenSem Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- Box smoothness of the lifted path edges of a pulse on the native chain at the pulse clock. -/
theorem right_pathEdge_boxSmooth {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    (hin : StageSuccessor.Input P Mn G) (hE : ActualFluxJointSmooth G) {h : ℕ}
    (π : StagePath G h) {k : ℤ} (hk : Odd k)
    (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k)) (ρ t : ℝ)
    (hc : D.cellScaleSq G.level ≠ 0) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) (s : ℕ) :
    ∀ v u d, ∀ γ ∈ (familyLiftData D G.level k (nativeChain G.level k) ρ
        (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩)).edge v u d,
      ∀ α, IsBoxSmooth s s (fun X z => γ.coeff α ((D.cellScaleSq G.level)⁻¹ * t) X z) := by
  intro v u d γ hγ α
  refine AVRegularity.Construction.Preservation.FullLift.liftEdges_boxSmooth_of_joint
    (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1))
    (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩) s s
    {(D.cellScaleSq G.level)⁻¹ * t} {t} ?_ ?_ v u d γ hγ α _ rfl
  · intro t' ht'
    rw [Set.mem_singleton_iff] at ht' ⊢
    rw [ht', ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  · intro v u d γ hγ α t' ht'
    rw [Set.mem_singleton_iff] at ht'
    subst ht'
    have hctx := hl_native_ctx hin hk hadm
    unfold pathEdges at hγ
    split_ifs at hγ with h1 h2
    · rw [List.mem_singleton] at hγ
      subst hγ
      rw [hctx]
      exact hE ⟨k, hk⟩ _ _ _ _ _ t' ht (s + s)
    all_goals exact absurd hγ (by simp)

open scoped Classical in
/-- **The regularity step is proved**: the pushed path mean of a smooth field is `C^{2p}`. -/
theorem rightPathReg : RightPathRegStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W t k hk hcut r hr' n hn π φ hφ
  have hΛ := hin.stage.base
  have hm : 1 ≤ G.level := by have := hin.stage.level; omega
  have hj : j₀ ≤ G.level := by have := hin.stage.level; omega
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hin.stage.base hin.stage.profile
    hin.stage.band G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  have hwin := mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
  have ht' := clock_mem_window D G.level k t hτ hcc hcut
  have hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) := by
    have := (G.actual ⟨k, hk⟩).2
    rwa [hin.stage.natural.2.2.1 ⟨k, hk⟩] at this
  have hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k := ⟨hadm, hk⟩
  have hE : ActualFluxJointSmooth G := actualFluxJointSmooth P Mn G G' depth CcT hin
  obtain ⟨Dord, nMax, hMax, npad, -, -, hD2, -, -, h1, h2⟩ := hin.range
  have hL := (W.lifts (SuccSource.copyQuad [] r π)) k (nativeChain G.level k) hA
  rw [hl_ladder_univ hin.stage hk] at hL
  have hL' := WeakEntryProofs.liftSequence_of_on_univ _ _ _ _ _ _ _ _ hL
  have hs1 : 2 * Mn.p + Dm ≤ Mn.sX := by omega
  have hs2 : 2 * Mn.p + Dm ≤ Mn.sZ := by omega
  have hfun : pathJ Mn G π (W.Cc (SuccSource.copyQuad [] r π)) n k t φ = fun y =>
      pulseMeanFluxEuler (D.cellScaleSq G.level) (Mn.lenFactor * liftLength D G.level)
        (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
          (Mn.lenFactor * liftLength D G.level)) n r
        (familyLiftData D G.level k (nativeChain G.level k) (Mn.lenFactor * liftLength D G.level)
          (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩))
        (W.Cc (SuccSource.copyQuad [] r π) k (nativeChain G.level k))
        (fun s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level k))
        (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s')
        (fun _ z => (Pi.single (0 : Fin (r + 1)) (φ z) : Fin (r + 1) → ℝ)) t y (Fin.last r) := by
    funext y
    funext j
    exact right_pathJ_eq_euler Mn G hA hin.stage.top hm hcc.ne' π _ n t φ y j
  rw [hfun]
  have key := pulseMeanFluxEuler_contDiff (D.cellScaleSq G.level)
    (Mn.lenFactor * liftLength D G.level)
    (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      (Mn.lenFactor * liftLength D G.level)) n r
    (familyLiftData D G.level k (nativeChain G.level k) (Mn.lenFactor * liftLength D G.level)
      (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩))
    (W.Cc (SuccSource.copyQuad [] r π) k (nativeChain G.level k))
    (fun s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level k))
    (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s')
    (fun _ z => (Pi.single (0 : Fin (r + 1)) (φ z) : Fin (r + 1) → ℝ)) t (Fin.last r)
    (2 * Mn.p) Mn.N r hcc.ne' hin.stage.order le_rfl
    (fun hh' hH n' hn' => hL'.2.2.1 hh' hH n' hn')
    (fun hh' hH n' m α v u => (hL'.2.2.2.2.2.1 hh' hH n' m α v u _ ht').1.mono hs1 hs2)
    (fun k' j => (EntryWeakProofs.familyLiftData_metric_entry_smooth D G.level k _
      (by simp [nativeChain]) _ _ _ k' j).of_le (by exact_mod_cast le_top))
    (fun k' => (ocPulseCellDrift_contDiff D.α D.q D.Λ D.ζ G.level (D.kap G.level) hk _ k').of_le
      (by exact_mod_cast le_top))
    (fun _ => right_pathEdge_boxSmooth hin.stage hE π hk hadm _ t hcc.ne' hwin _)
    (contDiff_pi.mpr fun i => by
      by_cases hi : i = 0
      · subst hi
        simpa using (contDiff_infty.mp hφ (2 * Mn.p + Dm + Mn.N))
      · simpa [Pi.single_apply, hi] using contDiff_const)
    ((flowOf_contDiff D (G.level - 1) t (D.slotAnchor G.level k)).of_le (by exact_mod_cast le_top))
    ((CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
      (D.slotAnchor G.level k) t).of_le (by exact_mod_cast le_top))
  exact_mod_cast key

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, final assembly: the first-source identity from the strain step and the three
statements `FSPiolaOperator`, `FSPiolaConstant`, `FSDiagTerm`.

`FSStepStrain` is `fs_strain_of_pos` once `0 < D.α` and `1 < D.q` are available; it is a
hypothesis here. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- **The first-source-flux step from the strain hypothesis and the three statements `FSPiolaOperator`, `FSPiolaConstant`,
`FSDiagTerm`.** -/
theorem firstSourceIdentity_of_lemmas (SS : FSStepStrain) (PA : FSPiolaOperator)
    (PB : FSPiolaConstant) (T : FSDiagTerm) : FirstSourceIdentityStatement :=
  firstSourceIdentity_of_steps firstSourceReadout
    (firstSourcePiece_of_steps' (fsStepPiola_of_lemmas PA PB) SS (fsStepDiagShift_of_term T))
    rootSourceBookkeeping piecePiolaFiniteOrder hilbertLiftGradeZero

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, Lemma Piola-A by jet replacement: statements and assembly.

`FSPiolaOperator` (the label operator of the first source is, at the centre, the differential
operator of its symmetric coefficients, on a field of class `C^K`, `K ≥ N + Dm + 4p`) follows from

* `FSPiolaSmooth`: the same identity for a smooth field (the lemmas
  `firstSourceFlux_applyArr`, `arrOp_eq_sum_fluxCoeff`);
* `FSLabelOpJet`: the value of the label operator at the centre depends only on the jets of the
  orders `≤ K` of the field at the centre, among fields of class `C^K`;

by replacing the field by a smooth function with the same jets at the centre
(`smoothJetRealization`); the right side reads the jets of the orders `≤ N + 4p ≤ K`.

Derivative count: `P_p` takes `2p` derivatives; the diagonal flux of
degree `n ≤ N + 1` is of order `≤ N` in its argument and its jets of order `2p` (needed by `Q_p`)
are determined by the jets of order `2p + Dm + N` of the argument (`pulse_sameJet`, with
`s = 2p`): `N + Dm + 4p ≤ K` in all. The commutator part is of order `4p - 1`.

For a smooth field `FSPiolaSmooth` alone suffices, and for `u = 0` both sides vanish. For `p = 0`
there is no commutator term and `P_0 = Q_0 = id`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **Lemma Piola-A for a smooth field.** -/
def FSPiolaSmooth : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (u : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) u →
      fsLabelOp Mn G G' W.Cc0 p t x u 0 =
        ∑ d ∈ Finset.Icc 1 (Mn.N + 1 + 4 * Mn.p), ∑ I : DerivativeWord2 (d - 1),
          orderedDerivative I u 0 • fluxCoeff (fsLabelOp Mn G G' W.Cc0 p t x) d I 0

/-- **Jet locality of the label operator at the centre**, among fields of class `C^K`,
`K ≥ N + Dm + 4p`. -/
def FSLabelOpJet : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (K : ℕ), Mn.N + Dm + 4 * Mn.p ≤ K →
    ∀ u₁ u₂ : Vec 2 → ℝ, ContDiff ℝ (K : ℕ∞) u₁ → ContDiff ℝ (K : ℕ∞) u₂ →
      SameJetAt K 0 u₁ u₂ →
      fsLabelOp Mn G G' W.Cc0 p t x u₁ 0 = fsLabelOp Mn G G' W.Cc0 p t x u₂ 0

/-- **Lemma Piola-A from the smooth case and jet locality.** -/
theorem fsPiolaOperator_of_jet (S : FSPiolaSmooth) (J : FSLabelOpJet) : FSPiolaOperator := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x K hK u hu
  obtain ⟨T, hT, hjet⟩ := smoothJetRealization K u (by exact_mod_cast hu) (0 : Vec 2)
  have hTK : ContDiff ℝ (K : ℕ∞) T := hT.of_le (by exact_mod_cast le_top)
  rw [J P Mn G G' depth CcT hin W p t hp x K hK u T hu hTK (fun r I hr => (hjet r I hr).symm),
    S P Mn G G' depth CcT hin W p t hp x T hT]
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun I _ => ?_
  rw [hjet (d - 1) I (by have := (Finset.mem_Icc.mp hd).2; omega)]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step: the strain step from the fields `alpha_pos`, `q_gt` of `SplitInput`,
and the final assembly without it. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- **Sub-step Strain.** -/
theorem fsStepStrain : FSStepStrain :=
  fun _ _ _ _ _ _ hin p t hp Y => fs_strain_of_pos hin hin.alpha_pos hin.q_gt p t hp Y

/-- **The first-source-flux step from the three statements `FSPiolaOperator`, `FSPiolaConstant`, `FSDiagTerm`.** -/
theorem firstSourceIdentity_of_three (PA : FSPiolaOperator) (PB : FSPiolaConstant)
    (T : FSDiagTerm) : FirstSourceIdentityStatement :=
  firstSourceIdentity_of_lemmas fsStepStrain PA PB T

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, the per-pulse identity `FSDiagTerm`: statements and assembly.

`FSDiagTerm` is for a field of class `C^{N+Dm}` at the time `t`. Both sides read the field at the
time `t` only, through its jets of the orders `≤ N + Dm` at the point (in fact `≤ n - 1 ≤ N`: at
grade zero `liftFluxX` has no source term). It follows from

* `FSDiagSmooth`: the identity for a smooth field frozen in time (the appended child against the
  recentred native family, the recentring of the grade-zero lifts, the grade-zero part of the
  Hilbert lift);
* `FSDiagJetL`: the left side `fsDiagLhs` (the pushed label flux of the appended child, zero off
  the carrier) depends only on the jets of order `≤ N + Dm` of the scalar field at the point;
* `FSDiagJetR`: the right side `fsPulseRaw` depends only on the jets of order `≤ N + Dm` of the
  components of the field at the time `t` at the point;

by replacing each component of the field at the time `t` by a smooth function with the same jets
at the point (`smoothJetRealization`).

For a smooth field constant in time `FSDiagSmooth` alone suffices, and for `a = 0` both sides
vanish. For `n = N + 1`, the top degree, only derivatives of order `N` occur, so `C^{N+Dm}` is
enough. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The left side of `FSDiagTerm` as an operator on the scalar field: the push-forward by the
child appended to the recentred actual context of the piece `p`, for the finer slot `k`, of its
grade-zero label flux of degree `n`; zero off the carrier. -/
def fsDiagLhs (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (p : OddSlot) (t : ℝ)
    (x : Vec 2) (k : ℤ) (n : ℕ) (f : Vec 2 → ℝ) (x' : Vec 2) : Vec 2 :=
  if IsAdmissibleChain D b j₀ G.level k
      ((fsCtx G' p t x).appendChild D k t
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) then
    pushFlux (((fsCtx G' p t x).appendChild D k t
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMap D t)
      (((fsCtx G' p t x).appendChild D k t
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMapInv D t)
      (diagLabelFlux D Dm G.level (Mn.lenFactor * liftLength D G.level) Cc0 k
        ((fsCtx G' p t x).appendChild D k t
          ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) n t)
      f x'
  else 0

/-- **The per-pulse identity for a smooth field frozen in time.** -/
def FSDiagSmooth : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (T : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => T y v)) →
    ∀ (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (x' : Vec 2) (j : Fin 2) (n : ℕ),
      2 ≤ n → n ≤ Mn.N + 1 → ∀ k : ℤ, Odd k → ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
      fsDiagLhs Mn G G' W.Cc0 p t x k n (fun y => ℓ (T (x + y) v)) x' j =
        ℓ (fsPulseRaw Mn G n CcT (fun _ => T) t (x + x') v k j)

/-- **Jet locality of the left side**, among scalar fields of class `C^{N+Dm}`. -/
def FSDiagJetL : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ) (x : Vec 2) (f₁ f₂ : Vec 2 → ℝ),
      ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) f₁ → ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) f₂ →
    ∀ x' : Vec 2, SameJetAt (Mn.N + Dm) x' f₁ f₂ →
    ∀ (n : ℕ) (k : ℤ), Odd k → ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
      fsDiagLhs Mn G G' W.Cc0 p t x k n f₁ x' = fsDiagLhs Mn G G' W.Cc0 p t x k n f₂ x'

/-- **Jet locality of the right side**, among fields of class `C^{N+Dm}` at the time `t`. -/
def FSDiagJetR : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (t : ℝ) (z : Vec 2) (a₁ a₂ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y => a₁ t y v)) →
      (∀ v, ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y => a₂ t y v)) →
      (∀ v, SameJetAt (Mn.N + Dm) z (fun y => a₁ t y v) (fun y => a₂ t y v)) →
    ∀ (n : ℕ) (v : CompIn G.comps) (k : ℤ), Odd k → ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
      fsPulseRaw Mn G n CcT a₁ t z v k = fsPulseRaw Mn G n CcT a₂ t z v k

/-- **The per-pulse identity from the smooth case and the two jet localities.** -/
theorem fsDiagTerm_of_steps (S : FSDiagSmooth) (JL : FSDiagJetL) (JR : FSDiagJetR) :
    FSDiagTerm := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x a ha v ℓ x' j n h2 hn k hk hc
  have hex : ∀ w : CompIn G.comps, ∃ Tw : Vec 2 → hr w.1.root, ContDiff ℝ (⊤ : ℕ∞) Tw ∧
      ∀ (r : ℕ) (I : DerivativeWord2 r), r ≤ Mn.N + Dm →
        orderedDerivative I Tw (x + x') = orderedDerivative I (fun y => a t y w) (x + x') :=
    fun w => smoothJetRealization (Mn.N + Dm) (fun y => a t y w) (by exact_mod_cast ha w) (x + x')
  choose T hT hTj using hex
  have hTc : ∀ w, ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y => T w y) := fun w =>
    (hT w).of_le (by exact_mod_cast le_top)
  have hR := JR P Mn G G' depth CcT hin t (x + x') a (fun _ y w => T w y) ha hTc
    (fun w r I hr => (hTj w r I hr).symm) n v k hk hc
  have hadd : ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y : Vec 2 => x + y) :=
    contDiff_const.add contDiff_id
  have hj1 : SameJetAt (Mn.N + Dm) x' (fun y => a t (x + y) v) (fun y => T v (x + y)) :=
    sameJet_comp x' (Mn.N + Dm) (fun y => x + y) (fun y => a t y v) (fun y => T v y) hadd
      (ha v) (hTc v) (fun r I hr => (hTj v r I hr).symm)
  have hjL : SameJetAt (Mn.N + Dm) x' (fun y => ℓ (a t (x + y) v)) (fun y => ℓ (T v (x + y))) :=
    sameJet_clm ℓ ((ha v).comp hadd) ((hTc v).comp hadd) hj1
  have hL := JL P Mn G G' depth CcT hin W p t x (fun y => ℓ (a t (x + y) v))
    (fun y => ℓ (T v (x + y))) (ℓ.contDiff.comp ((ha v).comp hadd))
    (ℓ.contDiff.comp ((hTc v).comp hadd)) x' hjL n k hk hc
  have hS := S P Mn G G' depth CcT hin W p t hp x (fun y w => T w y) (fun w => hT w) v ℓ x' j n
    h2 hn k hk hc
  show fsDiagLhs Mn G G' W.Cc0 p t x k n (fun y => ℓ (a t (x + y) v)) x' j = _
  rw [hL, hR]
  exact hS

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end

section
section
/-! **Source mean, Right: reading the pulse term through the Hilbert-lift path sum.**

`right_menuField_smooth`: the composite field of the pulse (the covariance polynomial of the
coarse field, read in the chart) is smooth in the slow variable. `rightPulseRead`: pulse-reading step. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport CovFluxReg Providers.GenSem Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The composite field of a pulse is smooth in the slow variable. -/
theorem right_menuField_smooth (Mn : SuccMenu) {G : GenStage D hr Dm b j₀}
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (hg : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => g y v))
    (ρ : ℝ) (k : ℤ) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun X' : Vec 2 => menuCovPRep Mn D G.level Mn.p (fun _ => g) s
      (D.flowOf (G.level - 1) s (ρ • X') (D.slotAnchor G.level k))) := by
  refine contDiff_pi.mpr fun w => ?_
  rw [contDiff_infty]
  intro n
  have h1 : ContDiff ℝ (n : ℕ∞) (covPolyP (menuCovPrimitive D Mn G.level s) Mn.p
      (fun y' => g y' w)) :=
    covPolyP_contDiff _ Mn.p n (by exact_mod_cast contDiff_infty.mp (hg w) (n + 2 * Mn.p))
  have h2 : ContDiff ℝ (n : ℕ∞) (fun X' : Vec 2 => D.flowOf (G.level - 1) s (ρ • X')
      (D.slotAnchor G.level k)) :=
    ((flowOf_contDiff D (G.level - 1) s (D.slotAnchor G.level k)).comp
      (contDiff_const_smul ρ)).of_le (by exact_mod_cast le_top)
  exact h1.comp h2

open scoped Classical in
/-- **The pulse-reading step is proved**: the Hilbert-lift path sum read through the pulse term. -/
theorem rightPulseRead : RightPulseReadStatement := by
  intro H5 hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W g hg v t ℓ j k hk hcut r hr' n hn y
  have hΛ := hin.stage.base
  have hm : 1 ≤ G.level := by have := hin.stage.level; omega
  have hj : j₀ ≤ G.level := by have := hin.stage.level; omega
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hin.stage.base hin.stage.profile
    hin.stage.band G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  have ht' := clock_mem_window D G.level k t hτ hcc hcut
  have hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) := by
    have := (G.actual ⟨k, hk⟩).2
    rwa [hin.stage.natural.2.2.1 ⟨k, hk⟩] at this
  have hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k := ⟨hadm, hk⟩
  have hE : ActualFluxJointSmooth G := actualFluxJointSmooth P Mn G G' depth CcT hin
  obtain ⟨Dord, nMax, hMax, npad, -, -, hD2, -, -, h1, h2⟩ := hin.range
  have hs1 : Mn.N + Dm + 2 ≤ Mn.sX := by omega
  have hs2 : Mn.N + Dm + 2 ≤ Mn.sZ := by omega
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr').1
  have hrd : r ≤ depth := (Finset.mem_Icc.mp hr').2
  have := Fintype.ofFinite (StagePath G r)
  set c := D.cellScaleSq G.level with hc
  set ρ := Mn.lenFactor * liftLength D G.level with hρ
  set εc := ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
    (Mn.lenFactor * liftLength D G.level) with hεc
  have hclk : c * (c⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hcc.ne', one_mul]
  have hX : ρ⁻¹ • (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s') t y ∈
      ladderOmega D b j₀ G.level k (nativeChain G.level k) ρ := nativeLadder_mem hm hj hk ρ _
  have hpath : ∀ k' : Fin 2, ℓ (fieldCellMean (fun z => liftFluxX
      (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k)
      (fun s' y' => menuCovPRep Mn D G.level Mn.p (fun _ => g) (c * s')
        (D.flowOf (G.level - 1) (c * s') (ρ • y') (D.slotAnchor G.level k))) r n (c⁻¹ * t)
      (ρ⁻¹ • (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s') t y) z k') v) =
      ∑ π : StagePath G r, if hπ : π.tgt = v.1 ∧ π.src ∈ G.comps then
        fieldCellMean (fun z => liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
          (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩))
          (W.Cc (SuccSource.copyQuad [] r π) k (nativeChain G.level k))
          (fun s' X' => Pi.single (0 : Fin (r + 1))
            (ℓ (rootPathMap hr π.src.root π.mapList v.1.root
              (menuCovPRep Mn D G.level Mn.p (fun _ => g) (c * s')
                (D.flowOf (G.level - 1) (c * s') (ρ • X') (D.slotAnchor G.level k))
                ⟨π.src, hπ.2⟩))))
          r n (c⁻¹ * t) (ρ⁻¹ • (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s') t y)
          z k') (Fin.last r)
      else 0 := by
    intro k'
    have key := (H5 P Mn G hin.stage hE hs1 hs2 ρ rfl depth CcT k hk hadm (hin.lift k hk) (c⁻¹ * t)
      ht' (fun s' y' => menuCovPRep Mn D G.level Mn.p (fun _ => g) (c * s')
        (D.flowOf (G.level - 1) (c * s') (ρ • y') (D.slotAnchor G.level k)))
      (fun s' => right_menuField_smooth Mn g hg ρ k (c * s')) n _ hX k' v ℓ).1 r hr1 hrd
      (fun h' π' => W.Cc (SuccSource.copyQuad [] h' π') k (nativeChain G.level k))
      (fun h' _ _ π' => (W.lifts (SuccSource.copyQuad [] h' π')) k (nativeChain G.level k) hA)
    rw [key, finsum_eq_sum_of_fintype]
  have hpj : ∀ (π : StagePath G r) (hπ : π.tgt = v.1 ∧ π.src ∈ G.comps),
      pathJ Mn G π (W.Cc (SuccSource.copyQuad [] r π)) n k t
        (fun z => ℓ (rootPathMap hr π.src.root π.mapList v.1.root
          (menuCovPRep Mn D G.level Mn.p (fun _ => g) t z ⟨π.src, hπ.2⟩))) y j =
      ∑ k' : Fin 2, jacMatrix (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level k))
          ((fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s') t y) j k' *
        ((-(c⁻¹ * εc ^ n * ρ)) *
          fieldCellMean (fun z => liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
            (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩))
            (W.Cc (SuccSource.copyQuad [] r π) k (nativeChain G.level k))
            (fun s' X' => Pi.single (0 : Fin (r + 1))
              (ℓ (rootPathMap hr π.src.root π.mapList v.1.root
                (menuCovPRep Mn D G.level Mn.p (fun _ => g) (c * s')
                  (D.flowOf (G.level - 1) (c * s') (ρ • X') (D.slotAnchor G.level k))
                  ⟨π.src, hπ.2⟩))))
            r n (c⁻¹ * t)
            (ρ⁻¹ • (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s') t y)
            z k') (Fin.last r)) := by
    intro π hπ
    refine Eq.trans (right_pathJ_eq_euler Mn G hA hin.stage.top hm hcc.ne' π
      (W.Cc (SuccSource.copyQuad [] r π)) n t _ y j) ?_
    unfold pulseMeanFluxEuler
    simp only [smul_eq_mul]
    refine Finset.sum_congr rfl fun k' _ => ?_
    have hcongr := right_liftFluxX_time_congr
      (familyLiftData D G.level k (nativeChain G.level k) ρ
        (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩))
      (W.Cc (SuccSource.copyQuad [] r π) k (nativeChain G.level k))
      (fun s' X' => (fun _ z => (Pi.single (0 : Fin (r + 1))
        (ℓ (rootPathMap hr π.src.root π.mapList v.1.root
          (menuCovPRep Mn D G.level Mn.p (fun _ => g) t z ⟨π.src, hπ.2⟩))) : Fin (r + 1) → ℝ))
        (c * s') (D.flowOf (G.level - 1) (c * s') (ρ • X') (D.slotAnchor G.level k)))
      (fun s' X' => Pi.single (0 : Fin (r + 1))
        (ℓ (rootPathMap hr π.src.root π.mapList v.1.root
          (menuCovPRep Mn D G.level Mn.p (fun _ => g) (c * s')
            (D.flowOf (G.level - 1) (c * s') (ρ • X') (D.slotAnchor G.level k))
            ⟨π.src, hπ.2⟩))))
      r n (c⁻¹ * t) (by funext X'; simp only [hclk])
    rw [hcongr]
  have hL : ℓ (pulseMeanFluxEuler c ρ εc n r
      (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k)
      (fun s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level k))
      (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s')
      (menuCovPRep Mn D G.level Mn.p (fun _ => g)) t y v j) =
      ∑ k' : Fin 2, jacMatrix (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level k))
          ((fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s') t y) j k' *
        ((-(c⁻¹ * εc ^ n * ρ)) * ℓ (fieldCellMean (fun z => liftFluxX
          (familyLiftData D G.level k (nativeChain G.level k) ρ
            (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k)
          (fun s' y' => menuCovPRep Mn D G.level Mn.p (fun _ => g) (c * s')
            (D.flowOf (G.level - 1) (c * s') (ρ • y') (D.slotAnchor G.level k))) r n (c⁻¹ * t)
          (ρ⁻¹ • (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s') t y) z k') v)) := by
    unfold pulseMeanFluxEuler
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hL, finsum_eq_sum_of_fintype]
  simp only [hpath, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  by_cases hπ : π.tgt = v.1 ∧ π.src ∈ G.comps
  · simp only [hπ, and_self, dite_true]
    rw [hpj π hπ]
  · simp [hπ]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, jet locality of the label operator, layer 3: the commutator part and the field
under `𝖰_p`.

* `fsj_commFlux_triple`: `𝒥_H u = -(D𝐛 H + H D𝐛ᵀ)∇u` for a smooth velocity loses one derivative;
* `fsj_comm_triple`: the commutator sum `∑_l (1/l!) ∑_{a<l} 𝒞^a 𝒥_H 𝒞^{l-1-a} g` of a field of
  class `C^K`, `4p ≤ K`, is of class `C^{2p}`, with jets of order `2p` determined by the jets of
  order `K` of `g`;
* `fsj_inner_triple`: the same for the whole field under `𝖰_p` in `firstSourceFlux`,
  `-(commutator sum) + 𝓕_A 𝖯_p g`, for `K ≥ N + Dm + 4p`.

For `p = 0` the commutator sum is empty and `𝖯_0 = id`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- A vector field is a triple when its components are. -/
theorem fsj_triple_pi {s : ℕ} {x : Vec 2} {f g : Vec 2 → Fin 2 → ℝ}
    (h : ∀ j, Triple s x (fun y => f y j) (fun y => g y j)) : Triple s x f g :=
  ⟨contDiff_pi.2 fun j => (h j).1, contDiff_pi.2 fun j => (h j).2.1,
    sameJet_pi (h := fun _ : Fin 2 => ℝ) (fun j => (h j).1) (fun j => (h j).2.1)
      (fun j => (h j).2.2)⟩

/-- **The commutator flux loses one derivative.** -/
theorem fsj_commFlux_triple (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (r : ℕ) (x : Vec 2) (u₁ u₂ : Vec 2 → ℝ)
    (hu₁ : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) u₁) (hu₂ : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) u₂)
    (hj : SameJetAt (r + 1) x u₁ u₂) :
    Triple r x (commutatorFluxJH bv Hc u₁) (commutatorFluxJH bv Hc u₂) := by
  rw [fsAlg_JH_eq_commFluxE, fsAlg_JH_eq_commFluxE]
  refine fsj_triple_pi fun j => ?_
  have hjac : ∀ a c : Fin 2, ContDiff ℝ (r : ℕ∞) (fun y => jacMatrix bv y a c) := fun a c =>
    CovFluxReg.jacMatrix_entry_contDiff (s := r) (hbv.of_le (by exact_mod_cast le_top))
      (g := fun y => y) contDiff_id a c
  have hM : ∀ l : Fin 2, ContDiff ℝ (r : ℕ∞)
      (fun y => (jacMatrix bv y * Hc + Hc * Matrix.transpose (jacMatrix bv y)) j l) := by
    intro l
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact (ContDiff.sum fun i _ => (hjac j i).mul contDiff_const).add
      (ContDiff.sum fun i _ => contDiff_const.mul (hjac l i))
  have hgr : ∀ l : Fin 2, Triple r x (fun y => gradE u₁ y l) (fun y => gradE u₂ y l) :=
    fun l => ⟨cd_partial hu₁ l, cd_partial hu₂ l, (sameJet_succ_iff.1 hj).2 l⟩
  unfold commFluxE
  exact triple_neg (triple_sum _ fun l _ => triple_mul (hM l) (hgr l))

/-- **The commutator sum at finite regularity.** -/
theorem fsj_comm_triple (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p K : ℕ) (hK : 4 * p ≤ K) (x : Vec 2) (g₁ g₂ : Vec 2 → ℝ)
    (hg₁ : ContDiff ℝ (K : ℕ∞) g₁) (hg₂ : ContDiff ℝ (K : ℕ∞) g₂) (hj : SameJetAt K x g₁ g₂) :
    Triple (2 * p) x (fsAlgSum Hc p (commutatorFluxJH bv Hc) g₁)
      (fsAlgSum Hc p (commutatorFluxJH bv Hc) g₂) := by
  unfold fsAlgSum
  refine triple_sum _ fun l hl => triple_smul _ (triple_sum _ fun a ha => ?_)
  obtain ⟨hl1, hlp⟩ := Finset.mem_Icc.mp hl
  have hal := Finset.mem_range.mp ha
  have hle : (2 * p + 2 * a + 1) + 2 * (l - 1 - a) ≤ K := by omega
  obtain ⟨h1, h2, h3⟩ := covOperator_iter_jet Hc x (2 * p + 2 * a + 1) (l - 1 - a)
    (cd_le hle hg₁) (cd_le hle hg₂) (sameJet_mono hle hj)
  obtain ⟨k1, k2, k3⟩ := fsj_commFlux_triple bv hbv Hc (2 * p + 2 * a) x _ _ h1 h2 h3
  exact covOperator_iter_jet Hc x (2 * p) a k1 k2 k3

/-- **The field under `𝖰_p` at finite regularity**: `-(commutator sum) + 𝓕_A 𝖯_p g`. -/
theorem fsj_inner_triple {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (D : OCData) (hζ : IsFastProfile D.ζ)
    (Mn : SuccMenu) (m : ℕ) (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hdiag : IsDiagLifts D Dm b j₀ Mn m Cc0) (hDm : 1 ≤ Dm) (hτ : 0 < ocTau D.α D.q D.Λ m)
    (hcc : 0 < D.cellScaleSq m) (hsX : 2 * Mn.p + Dm ≤ Mn.sX) (hsZ : 2 * Mn.p + Dm ≤ Mn.sZ)
    (t : ℝ) (ch : RealChain) (ζ : Vec 2) (S : Finset ℤ)
    (hS : ∀ k, k ∈ S ↔ Odd k ∧ IsScheduledIn D (m - 1) k ch.slot)
    (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (K : ℕ)
    (hK : Mn.N + Dm + 4 * Mn.p ≤ K) (x₀ : Vec 2) (g₁ g₂ : Vec 2 → ℝ)
    (hg₁ : ContDiff ℝ (K : ℕ∞) g₁) (hg₂ : ContDiff ℝ (K : ℕ∞) g₂) (hj : SameJetAt K x₀ g₁ g₂) :
    Triple (2 * Mn.p) x₀
      (fun x' => -(fsAlgSum Hc Mn.p (commutatorFluxJH bv Hc) g₁ x') +
        diagFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) Mn.N Cc0 t ch ζ
          (covPolyP Hc Mn.p g₁) x')
      (fun x' => -(fsAlgSum Hc Mn.p (commutatorFluxJH bv Hc) g₂ x') +
        diagFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) Mn.N Cc0 t ch ζ
          (covPolyP Hc Mn.p g₂) x') := by
  have hcomm := fsj_comm_triple bv hbv Hc Mn.p K (by omega) x₀ g₁ g₂ hg₁ hg₂ hj
  have hKe : K = (K - 2 * Mn.p) + 2 * Mn.p := by omega
  have hP := covPolyPJet Hc Mn.p (K - 2 * Mn.p) x₀ g₁ g₂ (by rw [← hKe]; exact hg₁)
    (by rw [← hKe]; exact hg₂) (by rw [← hKe]; exact hj)
  have hle : 2 * Mn.p + Dm + Mn.N ≤ K - 2 * Mn.p := by omega
  have hdiagT := fsj_diagFlux_triple D hζ Mn m Cc0 hdiag hDm hτ hcc (2 * Mn.p) hsX hsZ t ch ζ S hS
    x₀ _ _ (cd_le hle hP.1) (cd_le hle hP.2.1) (sameJet_mono hle hP.2.2)
  exact triple_add (triple_neg hcomm) hdiagT

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, the per-pulse identity: the Hilbert pulse flux of a smooth frozen field.

For a smooth field `T` frozen in time, an odd slot `k` of nonzero cut-off at the time `t` and a
functional `ℓ` on the component `v`, `ℓ` of the grade-zero Eulerian pulse flux of the Hilbert
fibre (`fsPulseRaw`, lifts `CcT k`) is the push-forward by the natural chart of `k` at the time `t`
of the grade-zero label flux of the native chain of `k` (scalar lifts `Cc0 k (nativeChain)`),
applied to `ℓ ∘ T_v` (`fsd_hilbert_pulse`):

* `hilbertLiftGradeZero` moves `ℓ` through the cell mean of the lift flux (the ladder of the native
  chain is all of `ℝ²`: a recentred native chain is admissible);
* `liftFluxX` reads the coarse field at its time argument only (`fsd_liftFluxX_field_congr`), and
  the clock of the pulse flux at the cell time `ℓ⁻² t` is `t`, so the moving chart is the chart at
  the time `t`;
* `fsj_push_eq_pulse` reads the scalar pulse flux as a push-forward; `D.kap = D.κ` at the levels
  `≤ D.term`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- The grade-zero lift flux reads the coarse field at its time only. -/
theorem fsd_liftFluxX_field_congr {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}
    (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h) {a a' : ℝ → Vec 2 → ∀ i, h i}
    (n : ℕ) {τ : ℝ} (ha : a τ = a' τ) :
    liftFluxX Q Cc a 0 n τ = liftFluxX Q Cc a' 0 n τ := by
  funext X z k
  rw [HLZero.liftFluxX_zero_formula, HLZero.liftFluxX_zero_formula,
    Uniqueness.liftApply_congr (B := Cc 0 (n - 1)) (B' := Cc 0 (n - 1)) (fun _ _ _ => rfl) ha,
    Uniqueness.liftApply_congr (B := Cc 0 (n - 2)) (B' := Cc 0 (n - 2)) (fun _ _ _ => rfl) ha]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀} {depth : ℕ}
  {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}

/-- **`ℓ` of the Hilbert pulse flux of a smooth frozen field is the pushed scalar label flux of
the native chain.** -/
theorem fsd_hilbert_pulse (hin : SplitInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G')
    (t : ℝ) {k : ℤ} (hk : Odd k) (hc : ocCutoff D.α D.q D.Λ G.level k t ≠ 0)
    (T : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hT : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => T y v)) (n : ℕ) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (z₀ : Vec 2) (j : Fin 2) :
    ℓ (fsPulseRaw Mn G n CcT (fun _ => T) t z₀ v k j) =
      pushFlux (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level k))
        (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y t)
        (diagLabelFlux D Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 k
          (nativeChain G.level k) n t) (fun y => ℓ (T y v)) z₀ j := by
  have hi := hin.stage
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hi.base
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hi.base hi.profile hi.band G.level
  have hm1 : 1 ≤ G.level := by have := hi.level; omega
  have hj : j₀ ≤ G.level := by have := hi.level; omega
  have hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) :=
    nativeChain_isCarrier D b j₀ G.level k 2 hm1 hj hk 0
  have ht' := CovFluxReg.clock_mem_window D G.level k t hτ hcc hc
  obtain ⟨Dord, nMax, hMax, npad, -, -, -, -, -, hfX, hfZ⟩ := hin.range
  have hsX : Mn.N + Dm + 2 ≤ Mn.sX := by
    have := le_max_left (Mn.N + Dord) (2 * Mn.p)
    omega
  have hsZ : Mn.N + Dm + 2 ≤ Mn.sZ := by
    have := le_max_left (Mn.N + Dord) (2 * Mn.p)
    omega
  have hkapL : D.kap G.level = D.κ G.level := by simp only [OCData.kap, min_eq_left hi.top]
  have hkapL1 : D.kap (G.level - 1) = D.κ (G.level - 1) := by
    simp only [OCData.kap, min_eq_left ((Nat.sub_le _ _).trans hi.top)]
  have ha : ∀ s : ℝ, ContDiff ℝ (⊤ : ℕ∞) ((fun (s' : ℝ) (X' : Vec 2) =>
      T (D.flowOf (G.level - 1) (D.cellScaleSq G.level * s')
        ((Mn.lenFactor * liftLength D G.level) • X') (D.slotAnchor G.level k))) s) := fun s =>
    contDiff_pi.2 fun w => (hT w).comp
      ((Providers.QuietAtlas.flowOf_contDiff D _ _ _).comp (contDiff_const_smul _))
  have hladder : ∀ X : Vec 2, X ∈ ladderOmega D b j₀ G.level k (nativeChain G.level k)
      (Mn.lenFactor * liftLength D G.level) := by
    intro X
    show IsAdmissibleChain D b j₀ G.level k ((nativeChain G.level k).recenter D _)
    rw [AVRegularity.nativeChain_recenter D]
    exact nativeChain_isCarrier D b j₀ G.level k 2 hm1 hj hk _
  have hGZ := fun k' : Fin 2 => hilbertLiftGradeZero P Mn G hi hsX hsZ _ rfl depth CcT k hk hadm
    (hin.lift k hk) _ ht' _ ha n
    ((Mn.lenFactor * liftLength D G.level)⁻¹ •
      D.flowOf (G.level - 1) (D.slotAnchor G.level k) z₀ t) (hladder _) k' v ℓ
    (W.Cc0 k (nativeChain G.level k)) (W.diag k _ hk hadm)
  have hfield : (fun (s' : ℝ) (X' : Vec 2) => fun _ : Fin 1 =>
      ℓ (T (D.flowOf (G.level - 1) (D.cellScaleSq G.level * s')
        ((Mn.lenFactor * liftLength D G.level) • X') (D.slotAnchor G.level k)) v))
        ((D.cellScaleSq G.level)⁻¹ * t) =
      (fun (_ : ℝ) (X' : Vec 2) => fun _ : Fin 1 =>
      ℓ (T (D.flowOf (G.level - 1) t
        ((Mn.lenFactor * liftLength D G.level) • X') (D.slotAnchor G.level k)) v))
        ((D.cellScaleSq G.level)⁻¹ * t) := by
    funext X' _
    show ℓ (T (D.flowOf (G.level - 1) (D.cellScaleSq G.level * ((D.cellScaleSq G.level)⁻¹ * t))
      _ _) v) = _
    rw [mul_inv_cancel_left₀ hcc.ne']
  have hpush := fsj_push_eq_pulse D G.level (Mn.lenFactor * liftLength D G.level)
    (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k (nativeChain G.level k)
      (Mn.lenFactor * liftLength D G.level) (fun _ _ _ => []))
    (W.Cc0 k (nativeChain G.level k)) n t
    (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level k))
    (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y t) (fun y => ℓ (T y v)) z₀
  unfold diagLabelFlux
  rw [hpush]
  unfold fsPulseRaw pulseMeanFluxEuler
  simp only [hk, dite_true, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [hGZ k', hkapL, hkapL1, fsd_liftFluxX_field_congr
    (a := fun (s' : ℝ) (X' : Vec 2) => fun _ : Fin 1 =>
      ℓ (T (D.flowOf (G.level - 1) (D.cellScaleSq G.level * s')
        ((Mn.lenFactor * liftLength D G.level) • X') (D.slotAnchor G.level k)) v))
    (a' := fun (_ : ℝ) (X' : Vec 2) => fun _ : Fin 1 =>
      ℓ (T (D.flowOf (G.level - 1) t
        ((Mn.lenFactor * liftLength D G.level) • X') (D.slotAnchor G.level k)) v))
    _ _ n hfield]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, the per-pulse identity: the two jet localities.

* `fsDiagJetL : FSDiagJetL`: the pushed label flux of the appended child reads the jets of the
  orders `≤ N + Dm` of the scalar field at the point (`fsj_push_triple` with `s = 0`; the
  grade-zero lifts of an admissible child are a lift sequence by `SplitWitness.diag`, box smooth of
  order `Dm` at the cell time of a time of nonzero cut-off);
* `fsDiagJetR : FSDiagJetR`: the Eulerian pulse flux of the Hilbert fibre reads the jets of the
  orders `≤ N + Dm` of the field at its time (`pulse_sameJet` with `s = 0`, grade `0`, as in
  `menuMeanFluxJet_of_pulse`). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **Jet locality of the left side.** -/
theorem fsDiagJetL : FSDiagJetL := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t x f₁ f₂ hf₁ hf₂ x' hj n k hk hc
  classical
  unfold fsDiagLhs
  by_cases hadm : IsAdmissibleChain D b j₀ G.level k
      ((fsCtx G' p t x).appendChild D k t
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x))
  · simp only [hadm, ↓reduceIte]
    have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hin.stage.base
    have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hin.stage.base hin.stage.profile
      hin.stage.band G.level
    obtain ⟨hX, hZ⟩ := CovFluxReg.floors' P Mn G G' depth CcT hin
    have hseq := W.diag k _ hk hadm
    have ht' := CovFluxReg.clock_mem_window D G.level k t hτ hcc hc
    have hle : 0 + Dm + Mn.N = Mn.N + Dm := by omega
    have hT := fsj_push_triple D hin.stage.profile G.level hk
      (Mn.lenFactor * liftLength D G.level) _ hadm.2.2.1 W.Cc0 n t 0 Mn.N hin.stage.order hcc.ne'
      (fun n' hn' m' α τ X z v u => hseq.2.2.1 0 le_rfl n' hn' m' α τ X z v u)
      (fun n' m' α v u => (hseq.2.2.2.2.2.1 0 le_rfl n' m' α v u _ ht').1.mono (by omega)
        (by omega))
      x' f₁ f₂ (by rw [hle]; exact hf₁) (by rw [hle]; exact hf₂) (by rw [hle]; exact hj)
    exact sameJet_zero_iff.1 hT.2.2
  · simp only [hadm, ↓reduceIte]

/-- **Jet locality of the right side.** -/
theorem fsDiagJetR : FSDiagJetR := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin t z a₁ a₂ h₁ h₂ hj n v k hk hc
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hin.stage.base
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hin.stage.base hin.stage.profile
    hin.stage.band G.level
  obtain ⟨hX, hZ⟩ := CovFluxReg.floors' P Mn G G' depth CcT hin
  have hle : 0 + Dm + Mn.N ≤ Mn.N + Dm := by omega
  have ha : ∀ a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root,
      (∀ v, ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y => a t y v)) →
      ContDiff ℝ ((0 + Dm + Mn.N : ℕ) : ℕ∞) (a t) := fun a h =>
    (contDiff_pi.2 h).of_le (by exact_mod_cast hle)
  have hjj : SameJetAt (0 + Dm + Mn.N) z (a₁ t) (a₂ t) :=
    sameJet_pi (fun w => (h₁ w).of_le (by exact_mod_cast hle))
      (fun w => (h₂ w).of_le (by exact_mod_cast hle)) (fun w => sameJet_mono hle (hj w))
  have ht' := CovFluxReg.clock_mem_window D G.level k t hτ hcc hc
  obtain ⟨_, _, hz3, _, _, hbox, _⟩ := hin.lift k hk
  have hT := pulse_sameJet (D.cellScaleSq G.level) (Mn.lenFactor * liftLength D G.level)
    (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      (Mn.lenFactor * liftLength D G.level)) n 0
    (familyLiftData D G.level k (nativeChain G.level k) (Mn.lenFactor * liftLength D G.level)
      (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k)
    (fun s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level k))
    (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s')
    a₁ a₂ t v 0 Mn.N depth z hcc.ne' hin.stage.order (Nat.zero_le _) hz3
    (fun hh' hH n' m α v u => (hbox hh' hH n' m α v u _ ht').1.mono (by omega) (by omega))
    (fun k' j => (EntryWeakProofs.familyLiftData_metric_entry_smooth D G.level k _
      (by simp [nativeChain]) _ _ _ k' j).of_le (by exact_mod_cast le_top))
    (fun k' => (CovFluxReg.ocPulseCellDrift_contDiff D.α D.q D.Λ D.ζ G.level (D.kap G.level)
      hk _ k').of_le (by exact_mod_cast le_top))
    (fun h0 => absurd rfl h0) (ha a₁ h₁) (ha a₂ h₂) hjj
    ((CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
      (D.slotAnchor G.level k)).of_le (by exact_mod_cast le_top))
    ((CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
      (D.slotAnchor G.level k) t).of_le (by exact_mod_cast le_top))
    (flow_chart_label D (G.level - 1) (D.slotAnchor G.level k) t z)
  unfold fsPulseRaw
  simp only [hk, dite_true]
  exact sameJet_zero_iff.1 hT.2.2

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **Source mean, Right: the right-hand source mean is proved.** -/
@[expose] public section
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- **Source mean, Right**: `ℓ ∘ (Q_p 𝐄^flux P_p g)_j` is the path side. -/
theorem sourceMeanRight : SourceMeanRightStatement :=
  sourceMeanRight_of_steps rightPulseRead rightPathReg rightPathLinear

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, jet locality of the label operator: `fsLabelOpJet : FSLabelOpJet`.

At the recentred actual context of a piece the commutator flux of `firstSourceFlux` is that of the
physical velocity translated to the centre (`fsAlg_JH_rel`, from the strain step), a smooth
coefficient; the pulled-back fields `u_i ∘ 𝒜_t⁻¹` are of class `C^K` with the same jets of order
`K` at `𝒜_t(0)` (`𝒜_t⁻¹(𝒜_t(0)) = 0`); the field under `𝖰_p` then has the same jets of order `2p`
there (`fsj_inner_triple`), and `𝖰_p` reads only those (`covPolyQJet`). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **Jet locality of the label operator at the centre.** -/
theorem fsLabelOpJet : FSLabelOpJet := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x K hK u₁ u₂ hu₁ hu₂ hj
  classical
  have hSS := fsStepStrain P Mn G G' depth CcT hin p t hp
  have hζ := hin.stage.profile
  have hm : 1 ≤ G.level := by have := hin.stage.level; omega
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hin.stage.base
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hin.stage.base hin.stage.profile
    hin.stage.band G.level
  obtain ⟨hX, hZ⟩ := CovFluxReg.floors' P Mn G G' depth CcT hin
  have hbv : ContDiff ℝ (⊤ : ℕ∞) (fun y => streamVel (D.Φ (G.level - 1)) t (x + y)) :=
    (((AVenhance.Infra.Construction.smoothPeriodic_streamVel (D.hΦ (G.level - 1))).smooth).comp
      (contDiff_const.prodMk contDiff_id)).comp (contDiff_const.add contDiff_id)
  have hf := Providers.GenSem.scheduledSlots_finite D (G.level - 1) (fsCtx G' p t x).slot (by
    simpa only [Nat.sub_add_cancel hm] using hτ)
  have hS : ∀ k, k ∈ hf.toFinset ↔ Odd k ∧ IsScheduledIn D (G.level - 1) k (fsCtx G' p t x).slot :=
    fun k => hf.mem_toFinset
  have hΦi : ContDiff ℝ (K : ℕ∞) ((fsCtx G' p t x).famMapInv D t) :=
    (Providers.GenSem.contDiff_famMapInv (fsCtx G' p t x) t).of_le (by exact_mod_cast le_top)
  have h0 : (fsCtx G' p t x).famMapInv D t ((fsCtx G' p t x).famMap D t 0) = 0 :=
    Providers.GenSem.famMapInv_famMap hζ (fsCtx G' p t x) t 0
  have hgj : SameJetAt K ((fsCtx G' p t x).famMap D t 0) (u₁ ∘ (fsCtx G' p t x).famMapInv D t)
      (u₂ ∘ (fsCtx G' p t x).famMapInv D t) :=
    sameJet_comp _ K _ u₁ u₂ hΦi hu₁ hu₂ (by rw [h0]; exact hj)
  have hT := fsj_inner_triple D hζ Mn G.level W.Cc0 W.diag hin.stage.order hτ hcc hX hZ t
    (fsCtx G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) hf.toFinset hS _
    hbv (ocCovariance D.α D.q D.Λ D.ζ G.level (D.κ G.level) (D.κ (G.level - 1)) Mn.anchor t) K hK
    _ _ _ (hu₁.comp hΦi) (hu₂.comp hΦi) hgj
  have hQ := covPolyQJet
    (ocCovariance D.α D.q D.Λ D.ζ G.level (D.κ G.level) (D.κ (G.level - 1)) Mn.anchor t) Mn.p _ _ _
    hT.1 hT.2.1 hT.2.2
  unfold fsLabelOp
  rw [fsAlg_firstSourceFlux_eq, fsAlg_firstSourceFlux_eq, fsAlg_JH_rel hin p t x hSS]
  exact congrArg _ hQ

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The source-mean step with its proved inputs**.

`SourceMeanLetterSumStatement` from the two steps of the identity for smooth fields
(`SourceMeanLeftStatement`, `SourceMeanRightStatement`): the jet locality is `covMeanJet`, the
matching step is `sourceMeanMatch`, the realization of jets is `smoothJetRealization`.
`sourceMeanLetterSum_of_left_right_steps` is the conclusion of the source-mean step with the
root-bookkeeping, transfer and path-sum steps discharged (`rootSourceBookkeeping`,
`transferChartCollapse`, `hilbertLiftPathSum`). -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- **The source-mean step from the left and right steps.** -/
theorem sourceMeanLetterSum_of_left_right_steps (hL : SourceMeanLeftStatement)
    (hR : SourceMeanRightStatement) : SourceMeanLetterSumStatement :=
  sourceMeanLetterSum_of_left_right covMeanJet hL hR

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end
