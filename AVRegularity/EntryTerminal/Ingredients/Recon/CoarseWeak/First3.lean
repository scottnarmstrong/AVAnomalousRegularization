-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Recon.CoarseWeak.First1
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetPoly
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofSourceMeanFinal
import AVRegularity.Proofs.GenSem.Op.FamChart
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseMain
import AVRegularity.Proofs.Results.Construction.SuccessorFluxUnique
import AVRegularity.Construction.StageSuccessor.StageOfFields
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

section
/-! Terminal first-source proof: the generic first-source proof, with the degree cutoff omitted
only from its input. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport CovFluxReg

section Scalar
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The commutator sum of a translated field. -/
theorem fsAlg_sum_shift' (bv : Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (x : Vec 2)
    (f : Vec 2 → ℝ) (z : Vec 2) :
    fsAlgSum' Hc p (commutatorFluxJH (fun y => bv (x + y)) Hc) (fun y => f (x + y)) z =
      fsAlgSum' Hc p (commutatorFluxJH bv Hc) f (x + z) := by
  unfold fsAlgSum'
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fsAlg_covOperator_iterate_shift, fsAlg_JH_shift, fsAlg_covOperator_iterate_shift]

/-- The commutator part of the temporal flux, read through a functional and a coordinate. -/
theorem fsAlg_scalar_sum' (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p K : ℕ) (hK : 4 * p ≤ K) {A : Vec 2 → E}
    (hA : ContDiff ℝ (K : ℕ∞) A) (ℓ : E →L[ℝ] ℝ) (κ : Fin 2) (y : Vec 2) :
    ℓ ((∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a' ∈ Finset.range l,
        (covOperator Hc)^[a'] (commFluxE bv Hc ((covOperator Hc)^[l - 1 - a'] A)) y) κ) =
      fsAlgSum' Hc p (commutatorFluxJH bv Hc) (fun y => ℓ (A y)) y κ := by
  unfold fsAlgSum'
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_Icc.mp hl
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  exact fsAlg_scalar_term bv hbv Hc p K hK hA ℓ κ hl'.2 (Finset.mem_range.mp ha) y

end Scalar

/-- **Sub-step Diagonal, corrected.** At a time of nonzero weight, `diagFluxCtx` at the
recentred actual context of the piece at `x`, applied to the field translated to the centre `x`,
at the relative point `x'`, is the physical diagonal flux at the point `x + x'`, componentwise.
(The untranslated variant of this step is false: its two sides would be evaluated at different physical
points.) The regularity (class `C^{N+Dm}`, the order read by the grade-zero means of orders
`≤ N+1`) is only needed at the time `t`. -/
def FSStepDiagShift' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y => a t y v)) →
    ∀ (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (x' : Vec 2) (j : Fin 2),
      diagFluxCtx D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N W.Cc0 t
          (fsCtx' G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)
          (fun y => ℓ (a t (x + y) v)) x' j =
        ℓ (menuDiagFluxPhys Mn G G.level Mn.N CcT a t (x + x') v j)

/-- The conclusion of sub-step Algebra, without the two hypotheses. -/
def FSStepAlgebraConcl' : Prop :=
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
      fsEulerRead' Mn G G' W.Cc0 p t x (fun y => ℓ (g t y v)) κ =
        -ℓ (covTemporalAt Mn G G.level Mn.N Mn.p CcT g v t x κ)

/-- **Sub-step Algebra from the strain step and the corrected diagonal step.** -/
theorem fs_algebra_of_steps' (SS : FSStepStrain') (SD : FSStepDiagShift') : FSStepAlgebraConcl' := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W K ta tb g hg v t ht x p hp ℓ κ
  have hSS := SS P Mn G G' depth CcT hin p t hp
  have hK := (hg).1
  have hgt : ∀ w, ContDiff ℝ (K : ℕ∞) (fun y => g t y w) := fun w => by
    exact_mod_cast ((hg).2 w t ht).1
  have hDm : 1 ≤ Dm := hin.stage.order
  have hbv : ContDiff ℝ (⊤ : ℕ∞) (streamVel (D.Φ (G.level - 1)) t) :=
    ((AVenhance.Infra.Construction.smoothPeriodic_streamVel (D.hΦ (G.level - 1))).smooth).comp
      (contDiff_const.prodMk contDiff_id)
  have hT := CovFluxReg.s47_menuTemporalFlux_contDiff P Mn G G' depth CcT hin K hK g t hgt v
  -- the diagonal field and its regularity
  set Hc := menuCovPrimitive D Mn G.level t with hHc
  set a' : ℝ → Vec 2 → ∀ w : CompIn G.comps, hr w.1.root := fun s y w =>
    covPolyP (menuCovPrimitive D Mn G.level s) Mn.p (fun y' => g s y' w) y with ha'
  have hreg : ∀ w, ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y => a' t y w) := fun w =>
    CovFluxReg.covPolyP_contDiff Hc Mn.p (Mn.N + Dm)
      ((hgt w).of_le (by exact_mod_cast (by omega : Mn.N + Dm + 2 * Mn.p ≤ K)))
  have hAp : ContDiff ℝ ((2 * Mn.p : ℕ) : ℕ∞) (fun y => g t y v) :=
    (hgt v).of_le (by exact_mod_cast (by omega : 2 * Mn.p ≤ K))
  -- the functional
  set Λ : (Fin 2 → hr v.1.root) →L[ℝ] ℝ := -(ℓ.comp (ContinuousLinearMap.proj κ)) with hΛ
  have hΛ' : ∀ κ' : Fin 2, ∀ y, -ℓ (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y κ') =
      (-(ℓ.comp (ContinuousLinearMap.proj κ'))) (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y) :=
    fun κ' y => rfl
  -- the unfolded left-hand side
  rw [fsAlg_unfold' hin p t x hSS W.Cc0 (fun y => ℓ (g t y v))]
  have hfun : (fun x' => -(fsAlgSum' Hc Mn.p
          (commutatorFluxJH (fun y => streamVel (D.Φ (G.level - 1)) t (x + y)) Hc)
          (fun y => ℓ (g t (x + y) v)) x') +
        diagFluxCtx D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N W.Cc0 t
          (fsCtx' G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)
          (covPolyP Hc Mn.p (fun y => ℓ (g t (x + y) v))) x') =
      fun x' => fun κ' => -ℓ (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v (x + x') κ') := by
    funext x' κ'
    have hd := SD P Mn G G' depth CcT hin W p t hp x a' hreg v ℓ x' κ'
    have hpP : (fun y => ℓ (a' t (x + y) v)) = covPolyP Hc Mn.p (fun y => ℓ (g t (x + y) v)) := by
      funext y
      simp only [ha']
      rw [← hHc]
      rw [← fsAlg_covPolyP_clm Hc ℓ Mn.p hAp (x + y),
        ← fsAlg_covPolyP_shift Hc Mn.p (fun y => ℓ (g t y v)) x y]
    rw [hpP] at hd
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [hd, fsAlg_sum_shift' (streamVel (D.Φ (G.level - 1)) t) Hc Mn.p x (fun y => ℓ (g t y v)) x']
    have hsc := fsAlg_scalar_sum' (streamVel (D.Φ (G.level - 1)) t) hbv Hc Mn.p K (by omega)
      (hgt v) ℓ κ' (x + x')
    unfold menuTemporalFlux
    simp only [Pi.sub_apply, map_sub]
    rw [hsc]
    ring
  have hsh : covPolyQ Hc Mn.p
      (fun x' κ' => -ℓ (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v (x + x') κ')) 0 =
      covPolyQ Hc Mn.p
        (fun y κ' => -ℓ (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y κ')) (x + 0) :=
    fsAlg_covPolyQ_shift Hc Mn.p
      (fun y κ' => -ℓ (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y κ')) x 0
  rw [hfun, hsh, add_zero]
  have hZ : ContDiff ℝ ((2 * Mn.p : ℕ) : ℕ∞)
      (fun y => fun κ' => -ℓ (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y κ')) := by
    refine contDiff_pi.mpr fun κ' => ?_
    simp only [hΛ']
    exact (ContinuousLinearMap.contDiff _).comp hT
  have h1 := fsAlg_covPolyQ_clm Hc (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) κ)
    Mn.p hZ x
  have h2 := fsAlg_covPolyQ_clm Hc Λ Mn.p hT x
  simp only [ContinuousLinearMap.proj_apply] at h1
  rw [← h1]
  simp only [hΛ', hΛ] at h2 ⊢
  rw [h2]
  simp [covTemporalAt, toFluxL, hHc, menuCovPrimitive]

/-- **The second sub-step from the sub-steps, with the corrected diagonal step** (the diagonal step is
translated to the centre). -/
theorem firstSourcePiece_of_steps'' (SP : FSStepPiola') (SS : FSStepStrain') (SD : FSStepDiagShift') :
    FirstSourcePieceStatement' := by
  intro _ _ _ hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W K ta tb g hg v t ht x p hp
  ext κ
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ => ?_
  rw [SP P Mn G G' depth CcT hin W K ta tb g hg v t ht x p hp ℓ κ,
    fs_algebra_of_steps' SS SD P Mn G G' depth CcT hin W K ta tb g hg v t ht x p hp ℓ κ]
  simp

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The mean flux of order `n` and grade `0` of the native family of the pulse `k` (without the
cut-off), the summand of `menuGluedMeanFlux`. -/
def fsPulseRaw' (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (n : ℕ)
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
theorem fsDiag_glued_eq' (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (n : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (z : Vec 2)
    (v : CompIn G.comps) :
    menuGluedMeanFlux Mn G G.level {0} {n} CcT a t z v =
      ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t,
        ocCutoff D.α D.q D.Λ G.level k t • fsPulseRaw' Mn G n CcT a t z v k := by
  unfold menuGluedMeanFlux fsPulseRaw'
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_singleton]
  split_ifs <;> simp

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
open scoped Classical in
/-- **The glue.** If the per-pulse identity holds at every pulse of nonzero cut-off, the grade-zero
mean flux of order `n` at the recentred actual context is `ℓ` of the Hilbert mean flux. -/
theorem fsDiag_mean_of_term' {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    {depth : ℕ} {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : FirstSourceInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ)
    (hp : G'.fam.weight p t ≠ 0) (x : Vec 2) (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (x' : Vec 2) (j : Fin 2) (n : ℕ)
    (hterm : ∀ k : ℤ, Odd k → ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
      (if IsAdmissibleChain D b j₀ G.level k
          ((fsCtx' G' p t x).appendChild D k t
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) then
        pushFlux (((fsCtx' G' p t x).appendChild D k t
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMap D t)
          (((fsCtx' G' p t x).appendChild D k t
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMapInv D t)
          (diagLabelFlux D Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 k
            ((fsCtx' G' p t x).appendChild D k t
              ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) n t)
          (fun y => ℓ (a t (x + y) v)) x'
       else 0) j = ℓ (fsPulseRaw' Mn G n CcT a t (x + x') v k j)) :
    diagMeanFluxCtx D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 t
        (fsCtx' G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) n
        (fun y => ℓ (a t (x + y) v)) x' j =
      ℓ (menuGluedMeanFlux Mn G G.level {0} {n} CcT a t (x + x') v j) := by
  classical
  obtain ⟨h1, -, hL⟩ := fsAlg_level_pos' hin
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  have hΛ : 1 ≤ D.Λ := hin.stage.base
  have hτ : 0 < ocTau D.α D.q D.Λ G'.level := Construction.Stream.ocTau_pos hΛ
  have hcp : ocCutoff D.α D.q D.Λ G'.level p.1 t ≠ 0 := by rw [← hnat.2.1 p t]; exact hp
  have htc : t ∈ ocPulseWindow D.α D.q D.Λ (G.level - 1) p.1 := by
    rw [← hL]; exact Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcp
  have hlev : G.level - 1 + 1 = G.level := by omega
  set X : ℤ → Vec 2 := fun k =>
    if IsAdmissibleChain D b j₀ G.level k
        ((fsCtx' G' p t x).appendChild D k t
          ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) then
      pushFlux (((fsCtx' G' p t x).appendChild D k t
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMap D t)
          (((fsCtx' G' p t x).appendChild D k t
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMapInv D t)
          (diagLabelFlux D Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 k
            ((fsCtx' G' p t x).appendChild D k t
              ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) n t)
          (fun y => ℓ (a t (x + y) v)) x'
    else 0 with hX
  have e1 := finsum_sched_eq_sum (D := D) hΛ (m := G.level - 1) (c := p.1) htc X
  rw [hlev] at e1
  have hslot : (fsCtx' G' p t x).slot = p.1 := by rw [fsAlg_ctx_native' hin]; rfl
  have e2 : diagMeanFluxCtx D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 t
        (fsCtx' G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) n
        (fun y => ℓ (a t (x + y) v)) x' =
      ∑ᶠ (k : ℤ) (_ : Odd k ∧ IsScheduledIn D (G.level - 1) k p.1),
        ocCutoff D.α D.q D.Λ G.level k t • X k := by
    unfold diagMeanFluxCtx
    rw [hslot]
    refine finsum_congr fun k => finsum_congr fun hk => ?_
    simp only [hX]
    split_ifs <;> simp
  rw [e2, e1, fsDiag_glued_eq']
  have e3 := tc_sum_obsPulses_eq_activeSlots D hΛ (G.level - 1) t (E := ℝ)
    (fun k => ℓ (fsPulseRaw' Mn G n CcT a t (x + x') v k j))
  rw [hlev] at e3
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul] at e3 ⊢
  rw [e3]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hc : ocCutoff D.α D.q D.Λ G.level k.1 t = 0
  · simp [hc]
  · congr 1
    exact hterm k.1 k.2 hc

/-- **Sub-step Diagonal** from the per-pulse identity. -/
def FSDiagTerm' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y => a t y v)) →
    ∀ (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (x' : Vec 2) (j : Fin 2) (n : ℕ),
      2 ≤ n → n ≤ Mn.N + 1 → ∀ k : ℤ, Odd k → ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
      (open scoped Classical in
        if IsAdmissibleChain D b j₀ G.level k
            ((fsCtx' G' p t x).appendChild D k t
              ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) then
          pushFlux (((fsCtx' G' p t x).appendChild D k t
              ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMap D t)
            (((fsCtx' G' p t x).appendChild D k t
              ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMapInv D t)
            (diagLabelFlux D Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 k
              ((fsCtx' G' p t x).appendChild D k t
                ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) n t)
            (fun y => ℓ (a t (x + y) v)) x'
         else 0) j = ℓ (fsPulseRaw' Mn G n CcT a t (x + x') v k j)

/-- **Sub-step Diagonal (corrected form) from the per-pulse identity.** -/
theorem fsStepDiagShift_of_term' (T : FSDiagTerm') : FSStepDiagShift' := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x a ha v ℓ x' j
  have hN : 1 ≤ Mn.N := hin.stage.cutoff
  have hmean : ∀ n, 2 ≤ n → n ≤ Mn.N + 1 →
      diagMeanFluxCtx D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) W.Cc0 t
        (fsCtx' G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) n
        (fun y => ℓ (a t (x + y) v)) x' j =
      ℓ (menuGluedMeanFlux Mn G G.level {0} {n} CcT a t (x + x') v j) := fun n h2 h3 =>
    fsDiag_mean_of_term' hin W p t hp x a v ℓ x' j n (fun k hk hc =>
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

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The left side of `FSDiagTerm'` as an operator on the scalar field: the push-forward by the
child appended to the recentred actual context of the piece `p`, for the finer slot `k`, of its
grade-zero label flux of degree `n`; zero off the carrier. -/
def fsDiagLhs' (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (p : OddSlot) (t : ℝ)
    (x : Vec 2) (k : ℤ) (n : ℕ) (f : Vec 2 → ℝ) (x' : Vec 2) : Vec 2 :=
  if IsAdmissibleChain D b j₀ G.level k
      ((fsCtx' G' p t x).appendChild D k t
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) then
    pushFlux (((fsCtx' G' p t x).appendChild D k t
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMap D t)
      (((fsCtx' G' p t x).appendChild D k t
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)).famMapInv D t)
      (diagLabelFlux D Dm G.level (Mn.lenFactor * liftLength D G.level) Cc0 k
        ((fsCtx' G' p t x).appendChild D k t
          ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) n t)
      f x'
  else 0

/-- **The per-pulse identity for a smooth field frozen in time.** -/
def FSDiagSmooth' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (T : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => T y v)) →
    ∀ (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (x' : Vec 2) (j : Fin 2) (n : ℕ),
      2 ≤ n → n ≤ Mn.N + 1 → ∀ k : ℤ, Odd k → ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
      fsDiagLhs' Mn G G' W.Cc0 p t x k n (fun y => ℓ (T (x + y) v)) x' j =
        ℓ (fsPulseRaw' Mn G n CcT (fun _ => T) t (x + x') v k j)

/-- **Jet locality of the left side**, among scalar fields of class `C^{N+Dm}`. -/
def FSDiagJetL' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ) (x : Vec 2) (f₁ f₂ : Vec 2 → ℝ),
      ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) f₁ → ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) f₂ →
    ∀ x' : Vec 2, SameJetAt (Mn.N + Dm) x' f₁ f₂ →
    ∀ (n : ℕ) (k : ℤ), Odd k → ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
      fsDiagLhs' Mn G G' W.Cc0 p t x k n f₁ x' = fsDiagLhs' Mn G G' W.Cc0 p t x k n f₂ x'

/-- **Jet locality of the right side**, among fields of class `C^{N+Dm}` at the time `t`. -/
def FSDiagJetR' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (t : ℝ) (z : Vec 2) (a₁ a₂ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y => a₁ t y v)) →
      (∀ v, ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y => a₂ t y v)) →
      (∀ v, SameJetAt (Mn.N + Dm) z (fun y => a₁ t y v) (fun y => a₂ t y v)) →
    ∀ (n : ℕ) (v : CompIn G.comps) (k : ℤ), Odd k → ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
      fsPulseRaw' Mn G n CcT a₁ t z v k = fsPulseRaw' Mn G n CcT a₂ t z v k

/-- **The per-pulse identity from the smooth case and the two jet localities.** -/
theorem fsDiagTerm_of_steps' (S : FSDiagSmooth') (JL : FSDiagJetL') (JR : FSDiagJetR') :
    FSDiagTerm' := by
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
  show fsDiagLhs' Mn G G' W.Cc0 p t x k n (fun y => ℓ (a t (x + y) v)) x' j = _
  rw [hL, hR]
  exact hS

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀} {depth : ℕ}
  {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}

/-- **`ℓ` of the Hilbert pulse flux of a smooth frozen field is the pushed scalar label flux of
the native chain.** -/
theorem fsd_hilbert_pulse' (hin : FirstSourceInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G')
    (t : ℝ) {k : ℤ} (hk : Odd k) (hc : ocCutoff D.α D.q D.Λ G.level k t ≠ 0)
    (T : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hT : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => T y v)) (n : ℕ) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (z₀ : Vec 2) (j : Fin 2) :
    ℓ (fsPulseRaw' Mn G n CcT (fun _ => T) t z₀ v k j) =
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
  obtain ⟨Dord, nMax, hMax, npad, -, -, -, -, hfX, hfZ⟩ := hin.range
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
  unfold fsPulseRaw' pulseMeanFluxEuler
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

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CycleComparison.LiftMeanEntrywise Uniqueness Providers.GenSem Providers.QuietAtlas

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Providers.QuietAtlas Providers.GenSem

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **Jet locality of the left side.** -/
theorem fsDiagJetL' : FSDiagJetL' := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t x f₁ f₂ hf₁ hf₂ x' hj n k hk hc
  classical
  unfold fsDiagLhs'
  by_cases hadm : IsAdmissibleChain D b j₀ G.level k
      ((fsCtx' G' p t x).appendChild D k t
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x))
  · simp only [hadm, ↓reduceIte]
    have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hin.stage.base
    have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hin.stage.base hin.stage.profile
      hin.stage.band G.level
    obtain ⟨hX, hZ⟩ := CovFluxReg.s47_floors' P Mn G G' depth CcT hin
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
theorem fsDiagJetR' : FSDiagJetR' := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin t z a₁ a₂ h₁ h₂ hj n v k hk hc
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hin.stage.base
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hin.stage.base hin.stage.profile
    hin.stage.band G.level
  obtain ⟨hX, hZ⟩ := CovFluxReg.s47_floors' P Mn G G' depth CcT hin
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
  unfold fsPulseRaw'
  simp only [hk, dite_true]
  exact sameJet_zero_iff.1 hT.2.2

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! Terminal first-source proof: the generic first-source proof, with the degree cutoff omitted
only from its input. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **The commutator sum at finite regularity.** -/
theorem fsj_comm_triple' (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p K : ℕ) (hK : 4 * p ≤ K) (x : Vec 2) (g₁ g₂ : Vec 2 → ℝ)
    (hg₁ : ContDiff ℝ (K : ℕ∞) g₁) (hg₂ : ContDiff ℝ (K : ℕ∞) g₂) (hj : SameJetAt K x g₁ g₂) :
    Triple (2 * p) x (fsAlgSum' Hc p (commutatorFluxJH bv Hc) g₁)
      (fsAlgSum' Hc p (commutatorFluxJH bv Hc) g₂) := by
  unfold fsAlgSum'
  refine triple_sum _ fun l hl => triple_smul _ (triple_sum _ fun a ha => ?_)
  obtain ⟨hl1, hlp⟩ := Finset.mem_Icc.mp hl
  have hal := Finset.mem_range.mp ha
  have hle : (2 * p + 2 * a + 1) + 2 * (l - 1 - a) ≤ K := by omega
  obtain ⟨h1, h2, h3⟩ := covOperator_iter_jet Hc x (2 * p + 2 * a + 1) (l - 1 - a)
    (cd_le hle hg₁) (cd_le hle hg₂) (sameJet_mono hle hj)
  obtain ⟨k1, k2, k3⟩ := fsj_commFlux_triple bv hbv Hc (2 * p + 2 * a) x _ _ h1 h2 h3
  exact covOperator_iter_jet Hc x (2 * p) a k1 k2 k3

/-- **The field under `𝖰_p` at finite regularity**: `-(commutator sum) + 𝓕_A 𝖯_p g`. -/
theorem fsj_inner_triple' {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (D : OCData) (hζ : IsFastProfile D.ζ)
    (Mn : SuccMenu) (m : ℕ) (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hdiag : IsDiagLifts D Dm b j₀ Mn m Cc0) (hDm : 1 ≤ Dm) (hτ : 0 < ocTau D.α D.q D.Λ m)
    (hcc : 0 < D.cellScaleSq m) (hsX : 2 * Mn.p + Dm ≤ Mn.sX) (hsZ : 2 * Mn.p + Dm ≤ Mn.sZ)
    (t : ℝ) (ch : RealChain) (ζ : Vec 2) (S : Finset ℤ)
    (hS : ∀ k, k ∈ S ↔ Odd k ∧ IsScheduledIn D (m - 1) k ch.slot)
    (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (K : ℕ)
    (hK : Mn.N + Dm + 4 * Mn.p ≤ K) (x₀ : Vec 2) (g₁ g₂ : Vec 2 → ℝ)
    (hg₁ : ContDiff ℝ (K : ℕ∞) g₁) (hg₂ : ContDiff ℝ (K : ℕ∞) g₂) (hj : SameJetAt K x₀ g₁ g₂) :
    Triple (2 * Mn.p) x₀
      (fun x' => -(fsAlgSum' Hc Mn.p (commutatorFluxJH bv Hc) g₁ x') +
        diagFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) Mn.N Cc0 t ch ζ
          (covPolyP Hc Mn.p g₁) x')
      (fun x' => -(fsAlgSum' Hc Mn.p (commutatorFluxJH bv Hc) g₂ x') +
        diagFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) Mn.N Cc0 t ch ζ
          (covPolyP Hc Mn.p g₂) x') := by
  have hcomm := fsj_comm_triple' bv hbv Hc Mn.p K (by omega) x₀ g₁ g₂ hg₁ hg₂ hj
  have hKe : K = (K - 2 * Mn.p) + 2 * Mn.p := by omega
  have hP := covPolyPJet Hc Mn.p (K - 2 * Mn.p) x₀ g₁ g₂ (by rw [← hKe]; exact hg₁)
    (by rw [← hKe]; exact hg₂) (by rw [← hKe]; exact hj)
  have hle : 2 * Mn.p + Dm + Mn.N ≤ K - 2 * Mn.p := by omega
  have hdiagT := fsj_diagFlux_triple D hζ Mn m Cc0 hdiag hDm hτ hcc (2 * Mn.p) hsX hsZ t ch ζ S hS
    x₀ _ _ (cd_le hle hP.1) (cd_le hle hP.2.1) (sameJet_mono hle hP.2.2)
  exact triple_add (triple_neg hcomm) hdiagT

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **Lemma Piola-A.** The label operator is a finite-order differential operator at the centre
on fields of class `C^K`. -/
def FSPiolaOperator' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (K : ℕ), Mn.N + Dm + 4 * Mn.p ≤ K →
    ∀ u : Vec 2 → ℝ, ContDiff ℝ (K : ℕ∞) u →
      fsLabelOp' Mn G G' W.Cc0 p t x u 0 =
        ∑ d ∈ Finset.Icc 1 (Mn.N + 1 + 4 * Mn.p), ∑ I : DerivativeWord2 (d - 1),
          orderedDerivative I u 0 • fluxCoeff (fsLabelOp' Mn G G' W.Cc0 p t x) d I 0

/-- **Lemma Piola-B.** The label operator kills constants (no zeroth-order term). -/
def FSPiolaConstant' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (I : DerivativeWord2 (1 - 1)),
      fluxCoeff (fsLabelOp' Mn G G' W.Cc0 p t x) 1 I 0 = 0

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The order of the first-source identity is at most `Dm`. -/
theorem fsPiola_deg_le' {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    {depth : ℕ} {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : FirstSourceInput P Mn G G' depth CcT) : Mn.N + 1 + 4 * Mn.p ≤ Dm := by
  have hdiagA : WordLetter.diag ∈ Mn.A := by
    obtain ⟨Dord, nMax, hMax, npad, hA, -⟩ := hin.range
    rw [hA]; simp [succAlphabet]
  have := (hin.stage.letter_orders _ hdiagA).2
  simp only [letterOrder] at this
  rwa [hin.stage.cutoff_eq, hin.stage.covariance_eq] at this

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The scalar reading of the physical flux of the first source through a piece. -/
theorem fsPiola_phys_scalar' (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (p : OddSlot)
    (t : ℝ) (x : Vec 2) (κ : Fin 2) (ℓ : hr v.1.root →L[ℝ] ℝ)
    (hg : ContDiff ℝ (Dm : ℕ∞) (fun y => g t y v)) :
    ℓ (fsPiecePhys' Mn G G' Cc0 g v p t x κ) =
      ∑ d ∈ Finset.Icc 2 Dm, ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
          (Mn.N + 1 + 4 * Mn.p) (fsPieceArray' Mn G G' Cc0 p t x) (d - 1) A x κ *
          orderedDerivative A (fun y => ℓ (g t y v)) x := by
  have e : fsPiecePhys' Mn G G' Cc0 g v p t x κ =
      ∑ d ∈ Finset.Icc 2 Dm, ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
          (Mn.N + 1 + 4 * Mn.p) (fsPieceArray' Mn G G' Cc0 p t x) (d - 1) A x κ •
          orderedDerivative A (fun y => g t y v) x := rfl
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [map_smul, smul_eq_mul]
  congr 1
  have hd' := (Finset.mem_Icc.mp hd).2
  have hg' : ContDiff ℝ ((d - 1 : ℕ) : ℕ∞) (fun y => g t y v) :=
    hg.of_le (by exact_mod_cast (by omega : d - 1 ≤ Dm))
  exact (congrFun (AVRegularity.orderedDerivative_clm_comp ℓ A hg') x).symm

/-- **Sub-step Piola from the two statements on the label operator.** -/
theorem fsStepPiola_of_lemmas' (PA : FSPiolaOperator') (PB : FSPiolaConstant') : FSStepPiola' := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W K ta tb g hg v t ht x p hp ℓ κ
  have hdeg := fsPiola_deg_le' hin
  obtain ⟨hK, hgg⟩ := hg
  have hgt : ContDiff ℝ (K : ℕ∞) (fun y => g t y v) := by exact_mod_cast (hgg v t ht).1
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  set f : Vec 2 → ℝ := fun y => ℓ (g t y v) with hf
  have hfK : ContDiff ℝ (K : ℕ∞) f := ℓ.contDiff.comp hgt
  rw [fsPiola_phys_scalar' Mn G G' W.Cc0 g v p t x κ ℓ
    (hgt.of_le (by exact_mod_cast (by omega : Dm ≤ K)))]
  set B := fsPieceArray' Mn G G' W.Cc0 p t x with hB
  set ψ : Vec 2 → Vec 2 := ⇑((G'.fam.piece p).material t).symm with hψ
  set Dγ := Mn.N + 1 + 4 * Mn.p with hDγ
  have hB1 : ∀ I, B 1 I = 0 := fun I => by
    simp only [hB, fsPieceArray']
    split_ifs
    · exact PB P Mn G G' depth CcT hin W p t hp x I
    · rfl
  rw [fsPiola_reindex (fun d => ∑ A : DerivativeWord2 (d - 1),
      transportedCoeff (chartInvJacobian ψ) Dγ B (d - 1) A x κ * orderedDerivative A f x) Dγ Dm
    hdeg ?_ ?_]
  · have hmat : ⇑((G'.fam.piece p).material t) =
        fun y => D.flowOf (G'.level - 1) t y (D.slotAnchor G'.level p.1) :=
      (hnat.1 p).2.2.2.2 t
    have hsymm : ψ = fun x' => D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) x' t :=
      tc_material_symm hnat p t
    have hχ : ContDiff ℝ (⊤ : ℕ∞) ⇑((G'.fam.piece p).material t) := by
      rw [hmat]; exact Providers.QuietAtlas.flowOf_contDiff D _ _ _
    have hψc : ContDiff ℝ (⊤ : ℕ∞) ψ := by
      rw [hsymm]; exact Providers.QuietAtlas.flowOf_contDiff D _ _ _
    have h1 : ∀ y, ψ (((G'.fam.piece p).material t) y) = y := fun y =>
      ((G'.fam.piece p).material t).symm_apply_apply y
    have h2 : ∀ x, ((G'.fam.piece p).material t) (ψ x) = x := fun x =>
      ((G'.fam.piece p).material t).apply_symm_apply x
    have hV : ContDiff ℝ ((Dγ - 1 : ℕ) : ℕ∞) (fun y => f (((G'.fam.piece p).material t) y)) :=
      (hfK.of_le (by exact_mod_cast (by omega : Dγ - 1 ≤ K))).comp (hχ.of_le (by exact_mod_cast le_top))
    have hP2 := @piecePiolaFiniteOrder ℝ _ _ ⇑((G'.fam.piece p).material t) ψ hχ hψc h1 h2 Dγ
      (fun y => f (((G'.fam.piece p).material t) y)) hV B x κ
    have hVψ : (fun y => f (((G'.fam.piece p).material t) y)) ∘ ψ = f :=
      funext fun y => by simp only [Function.comp_apply, h2]
    rw [hVψ] at hP2
    simp only [smul_eq_mul] at hP2
    refine hP2.trans ?_
    have hadm := fsAlg_ctx_adm' hin p t x
    have hu : ContDiff ℝ (K : ℕ∞) (fun y => f (((G'.fam.piece p).material t) (ψ x + y))) :=
      hfK.comp ((hχ.of_le (by exact_mod_cast le_top)).comp (contDiff_const.add contDiff_id))
    unfold fsEulerRead'
    simp only [hadm, ↓reduceIte]
    rw [PA P Mn G G' depth CcT hin W p t hp x K hK _ hu, fsPiola_mulVec]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun I _ =>
      Finset.sum_congr rfl fun i _ => ?_
    have hB' : B d I = fluxCoeff (fsLabelOp' Mn G G' W.Cc0 p t x) d I 0 := by
      have hadm' : IsAdmissibleChain D b j₀ G'.level p.1
          (RealChain.recenter D (G'.actual p).1 (((G'.fam.piece p).material t).symm x)) := hadm
      simp only [hB, fsPieceArray', hadm', ↓reduceIte]
      rfl
    have hod : orderedDerivative I (fun y => f (((G'.fam.piece p).material t) (ψ x + y))) 0 =
        orderedDerivative I (fun y => f (((G'.fam.piece p).material t) y)) (ψ x) := by
      rw [Providers.QuietAtlas.orderedDerivative_comp_add_left I
        (fun y => f (((G'.fam.piece p).material t) y)) (ψ x)]
      simp only [add_zero]
    rw [hB', hod]
  · refine Finset.sum_eq_zero fun A _ => ?_
    rw [CycleComparison.Reconstruction.transportedCoeff_low_eq_zero _ _ _ (r := 1 - 1) rfl A x κ hB1]
    simp
  · intro d hd
    refine Finset.sum_eq_zero fun A _ => ?_
    rw [transportedCoeff_eq_zero_of_le _ (by omega : Dγ ≤ d - 1) B A x]
    simp

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **Lemma Piola-A for a smooth field.** -/
def FSPiolaSmooth' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (u : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) u →
      fsLabelOp' Mn G G' W.Cc0 p t x u 0 =
        ∑ d ∈ Finset.Icc 1 (Mn.N + 1 + 4 * Mn.p), ∑ I : DerivativeWord2 (d - 1),
          orderedDerivative I u 0 • fluxCoeff (fsLabelOp' Mn G G' W.Cc0 p t x) d I 0

/-- **Jet locality of the label operator at the centre**, among fields of class `C^K`,
`K ≥ N + Dm + 4p`. -/
def FSLabelOpJet' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (K : ℕ), Mn.N + Dm + 4 * Mn.p ≤ K →
    ∀ u₁ u₂ : Vec 2 → ℝ, ContDiff ℝ (K : ℕ∞) u₁ → ContDiff ℝ (K : ℕ∞) u₂ →
      SameJetAt K 0 u₁ u₂ →
      fsLabelOp' Mn G G' W.Cc0 p t x u₁ 0 = fsLabelOp' Mn G G' W.Cc0 p t x u₂ 0

/-- **Lemma Piola-A from the smooth case and jet locality.** -/
theorem fsPiolaOperator_of_jet' (S : FSPiolaSmooth') (J : FSLabelOpJet') : FSPiolaOperator' := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x K hK u hu
  obtain ⟨T, hT, hjet⟩ := smoothJetRealization K u (by exact_mod_cast hu) (0 : Vec 2)
  have hTK : ContDiff ℝ (K : ℕ∞) T := hT.of_le (by exact_mod_cast le_top)
  rw [J P Mn G G' depth CcT hin W p t hp x K hK u T hu hTK (fun r I hr => (hjet r I hr).symm),
    S P Mn G G' depth CcT hin W p t hp x T hT]
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun I _ => ?_
  rw [hjet (d - 1) I (by have := (Finset.mem_Icc.mp hd).2; omega)]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- **Sub-step Strain, given `0 < α` and `1 < q`.** -/
theorem fs_strain_of_pos' {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    {depth : ℕ} {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : FirstSourceInput P Mn G G' depth CcT) (hα : 0 < D.α) (hq : 1 < D.q)
    (p : OddSlot) (t : ℝ) (hp : G'.fam.weight p t ≠ 0) (Y : Vec 2) :
    contextStrain D (G.level - 1) p.1 t ((G'.actual p).1.recenter D Y)
          ((D.eps (G.level - 1))⁻¹ • Y) =
        jacMatrix (streamVel (D.Φ (G.level - 1)) t)
          (((((G'.actual p).1.recenter D Y).geom D).1 t Y
            (((G'.actual p).1.recenter D Y).geom D).2.2)) := by
  have hsucc := hin.successor
  have hnat : G'.IsNatural Mn.M := hsucc.2.2.2.1
  have hL : G'.level = G.level - 1 := hsucc.2.1
  have hlev := hin.stage.level
  have hcp : ocCutoff D.α D.q D.Λ G'.level p.1 t ≠ 0 := by rw [← hnat.2.1 p t]; exact hp
  have hτ : 0 < ocTau D.α D.q D.Λ G'.level := Construction.Stream.ocTau_pos hin.stage.base
  have htw : t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1 :=
    Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcp
  rw [hnat.2.2.1 p, hL] 
  rw [hL] at htw
  exact Providers.context_strain_physical D.α D.q hα hq D.Λ D.ζ hin.stage.profile D rfl rfl rfl rfl
    hin.stream (G.level - 1) (by omega) p.1 p.2 t htw Y

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- **The first-source flux identity from its statements.** -/
theorem firstSourceIdentity_of_lemmas' (SS : FSStepStrain') (PA : FSPiolaOperator')
    (PB : FSPiolaConstant') (T : FSDiagTerm') : FirstSourceIdentityStatement' :=
  firstSourceIdentity_of_steps' firstSourceReadout'
    (firstSourcePiece_of_steps'' (fsStepPiola_of_lemmas' PA PB) SS (fsStepDiagShift_of_term' T))
    rootSourceBookkeeping piecePiolaFiniteOrder hilbertLiftGradeZero

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- **Sub-step Strain.** -/
theorem fsStepStrain' : FSStepStrain' :=
  fun _ _ _ _ _ _ hin p t hp Y => fs_strain_of_pos' hin hin.alpha_pos hin.q_gt p t hp Y

/-- **The first-source flux identity from the three statements.** -/
theorem firstSourceIdentity_of_three' (PA : FSPiolaOperator') (PB : FSPiolaConstant')
    (T : FSDiagTerm') : FirstSourceIdentityStatement' :=
  firstSourceIdentity_of_lemmas' fsStepStrain' PA PB T

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **Jet locality of the label operator at the centre.** -/
theorem fsLabelOpJet' : FSLabelOpJet' := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x K hK u₁ u₂ hu₁ hu₂ hj
  classical
  have hSS := fsStepStrain' P Mn G G' depth CcT hin p t hp
  have hζ := hin.stage.profile
  have hm : 1 ≤ G.level := by have := hin.stage.level; omega
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hin.stage.base
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hin.stage.base hin.stage.profile
    hin.stage.band G.level
  obtain ⟨hX, hZ⟩ := CovFluxReg.s47_floors' P Mn G G' depth CcT hin
  have hbv : ContDiff ℝ (⊤ : ℕ∞) (fun y => streamVel (D.Φ (G.level - 1)) t (x + y)) :=
    (((AVenhance.Infra.Construction.smoothPeriodic_streamVel (D.hΦ (G.level - 1))).smooth).comp
      (contDiff_const.prodMk contDiff_id)).comp (contDiff_const.add contDiff_id)
  have hf := Providers.GenSem.scheduledSlots_finite D (G.level - 1) (fsCtx' G' p t x).slot (by
    simpa only [Nat.sub_add_cancel hm] using hτ)
  have hS : ∀ k, k ∈ hf.toFinset ↔ Odd k ∧ IsScheduledIn D (G.level - 1) k (fsCtx' G' p t x).slot :=
    fun k => hf.mem_toFinset
  have hΦi : ContDiff ℝ (K : ℕ∞) ((fsCtx' G' p t x).famMapInv D t) :=
    (Providers.GenSem.contDiff_famMapInv (fsCtx' G' p t x) t).of_le (by exact_mod_cast le_top)
  have h0 : (fsCtx' G' p t x).famMapInv D t ((fsCtx' G' p t x).famMap D t 0) = 0 :=
    Providers.GenSem.famMapInv_famMap hζ (fsCtx' G' p t x) t 0
  have hgj : SameJetAt K ((fsCtx' G' p t x).famMap D t 0) (u₁ ∘ (fsCtx' G' p t x).famMapInv D t)
      (u₂ ∘ (fsCtx' G' p t x).famMapInv D t) :=
    sameJet_comp _ K _ u₁ u₂ hΦi hu₁ hu₂ (by rw [h0]; exact hj)
  have hT := fsj_inner_triple' D hζ Mn G.level W.Cc0 W.diag hin.stage.order hτ hcc hX hZ t
    (fsCtx' G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) hf.toFinset hS _
    hbv (ocCovariance D.α D.q D.Λ D.ζ G.level (D.κ G.level) (D.κ (G.level - 1)) Mn.anchor t) K hK
    _ _ _ (hu₁.comp hΦi) (hu₂.comp hΦi) hgj
  have hQ := covPolyQJet
    (ocCovariance D.α D.q D.Λ D.ζ G.level (D.κ G.level) (D.κ (G.level - 1)) Mn.anchor t) Mn.p _ _ _
    hT.1 hT.2.1 hT.2.2
  unfold fsLabelOp'
  rw [fsAlg_firstSourceFlux_eq', fsAlg_firstSourceFlux_eq', fsAlg_JH_rel' hin p t x hSS]
  exact congrArg _ hQ

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **Lemma Piola-A for a smooth field.** -/
theorem fsPiolaSmooth' : FSPiolaSmooth' := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x u hu
  classical
  have hi := hin.stage
  have hm : 1 ≤ G.level := by have := hi.level; omega
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hi.base
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hi.base hi.profile hi.band G.level
  have hκ : 0 < D.κ (G.level - 1) := by
    have hh := EntryWeakProofs.weakData_kap_pos D hi.base hi.profile hi.band (G.level - 1)
    simpa only [OCData.kap, min_eq_left ((Nat.sub_le _ _).trans hi.top)] using hh
  have hρ : Mn.lenFactor * liftLength D G.level ≠ 0 := by
    unfold liftLength
    exact (mul_pos hi.length_factor (Real.sqrt_pos.2 (mul_pos hκ
      (Construction.Stream.ocTauPP_pos hi.base)))).ne'
  have hch : (fsCtx' G' p t x).WellSlotted := (fsAlg_ctx_adm' hin p t x).2.2.1
  have hf := Providers.GenSem.scheduledSlots_finite D (G.level - 1) (fsCtx' G' p t x).slot (by
    simpa only [Nat.sub_add_cancel hm] using hτ)
  have hS : ∀ k, k ∈ hf.toFinset ↔ Odd k ∧ IsScheduledIn D (G.level - 1) k (fsCtx' G' p t x).slot :=
    fun k => hf.mem_toFinset
  have hstrain : ∀ a c, ContDiff ℝ ((4 * Mn.p : ℕ) : WithTop ℕ∞)
      (fun y => Providers.GenSem.strainAt D G.level t (fsCtx' G' p t x)
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) y a c) := by
    intro a c
    exact ((Providers.GenSem.contDiff_contextStrain_recenter D hi.profile (G.level - 1)
      (fsCtx' G' p t x).slot t (fsCtx' G' p t x) hch _ a c).comp
      (Providers.GenSem.contDiff_famMapInv (fsCtx' G' p t x) t)).of_le
        (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨Dord, nMax, hMax, npad, -, -, -, -, hfX, hfZ⟩ := hin.range
  have hR : 2 * Mn.p + Dm + 2 ≤ Mn.sX ∧ 2 * Mn.p + Dm + 2 ≤ Mn.sZ := by
    have := le_max_right (Mn.N + Dord) (2 * Mn.p)
    omega
  have he : ∀ (g : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → ∀ c,
      fsLabelOp' Mn G G' W.Cc0 p t x g 0 c =
        Providers.GenSem.applyArr (Mn.N + 4 * Mn.p)
          (Providers.GenSem.fsArr D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N
            Mn.p Mn.anchor W.Cc0 hf.toFinset t (fsCtx' G' p t x)
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) c) g 0 0 := by
    intro g hg c
    have h1 := Providers.GenSem.firstSourceFlux_applyArr (b := b) (j₀ := j₀) (Dm := Dm)
      (N := Mn.N) (p := Mn.p) (s₀ := Mn.anchor) (Cc0 := W.Cc0) hi.profile hρ hi.cutoff t
      (fsCtx' G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) hf.toFinset hS
      hstrain
      (fun n _ _ k hk hA hcut => Providers.GenSem.liftRegular_of_isLiftSequence D G.level k
        hA.2.2.1 _ (W.diag k _ ((hS k).mp hk).1 hA) hR.1 hR.2 0 le_rfl n _
        (CovFluxReg.clock_mem_window D G.level k t hτ hcc hcut) 0) hg 0 c
    unfold fsLabelOp'
    rw [h1, Providers.GenSem.applyArr_eq_of_supp (by omega)
      (StageSuccessor.first_source_array_support hi.cutoff _ t _ _ c)]
  have key := Providers.QuietAtlas.arrOp_eq_sum_fluxCoeff (Mn.N + 4 * Mn.p) _
    (fsLabelOp' Mn G G' W.Cc0 p t x) he hu
  have hn : Mn.N + 1 + 4 * Mn.p = Mn.N + 4 * Mn.p + 1 := by ring
  rw [Providers.QuietAtlas.sum_Icc_one_eq_sum_range, hn]
  exact key

/-- **Lemma Piola-A.** -/
theorem fsPiolaOperator' : FSPiolaOperator' := fsPiolaOperator_of_jet' fsPiolaSmooth' fsLabelOpJet'

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Uniqueness

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Uniqueness Providers Providers.GenSem

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Uniqueness Providers Providers.GenSem

/-- **Lemma Piola-B.** The label operator kills constants. -/
theorem fsPiolaConstant' : FSPiolaConstant' := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x I
  have hΛ := hin.stage.base
  have hζ := hin.stage.profile
  have hκ := hin.stage.band
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  unfold fluxCoeff fsLabelOp'
  have h1 : (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) = fun _ => 1 := by
    funext Y
    simp
  rw [h1]
  simp only [smul_eq_zero]
  right
  exact fsc_firstSourceFlux_const_zero D Mn G.level hΛ hζ hc W.Cc0 W.diag t _ _ 0

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **The per-pulse identity for a smooth field frozen in time.** -/
theorem fsDiagSmooth' : FSDiagSmooth' := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x T hT v ℓ x' j n h2 hn k hk hc
  have hi := hin.stage
  obtain ⟨h1, hj0, hL'⟩ := fsAlg_level_pos' hin
  have hL : G.level = G'.level + 1 := by have := hi.level; omega
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  have hcp : ocCutoff D.α D.q D.Λ G'.level p.1 t ≠ 0 := by rw [← hnat.2.1 p t]; exact hp
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hi.base hi.profile hi.band G.level
  have hκ : 0 < D.κ (G.level - 1) := by
    have hh := EntryWeakProofs.weakData_kap_pos D hi.base hi.profile hi.band (G.level - 1)
    simpa only [OCData.kap, min_eq_left ((Nat.sub_le _ _).trans hi.top)] using hh
  have hρ : Mn.lenFactor * liftLength D G.level ≠ 0 := by
    unfold liftLength
    exact (mul_pos hi.length_factor (Real.sqrt_pos.2 (mul_pos hκ
      (Construction.Stream.ocTauPP_pos hi.base)))).ne'
  have hctx := fsAlg_ctx_native' hin p t x
  have hsymm : ((G'.fam.piece p).material t).symm x =
      D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) x t :=
    congrFun (tc_material_symm hnat p t) x
  have hxY : D.flowOf (G'.level - 1) t
      (D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) x t) (D.slotAnchor G'.level p.1) = x :=
    flowOf_inv D _ t _ x
  have key := fsd_child_push hi.base hi.profile hin.stream hi.bandwidth hin.start hL h1 hj0 hcc
    W.diag hρ p.2 hk hcp hc (D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) x t) n
    (fun y => ℓ (T y v)) x'
  rw [hxY] at key
  unfold fsDiagLhs'
  rw [hctx, hsymm]
  simp only [key.1, ↓reduceIte]
  rw [key.2]
  exact (fsd_hilbert_pulse' hin W t hk hc T hT n v ℓ (x + x') j).symm

/-- **The per-pulse identity** (sub-step Diagonal). -/
theorem fsDiagTerm' : FSDiagTerm' := fsDiagTerm_of_steps' fsDiagSmooth' fsDiagJetL' fsDiagJetR'

/-- **The first-source part of the plain flux is `-Q_p 𝒟 g`.** -/
theorem firstSourceIdentity : FirstSourceIdentityStatement' :=
  firstSourceIdentity_of_three' fsPiolaOperator' fsPiolaConstant' fsDiagTerm'

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
