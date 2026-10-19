-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCascadeSplitInput
import AVRegularity.EntryWeakAssembly.FiniteStagePaths
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCenteredCoeff
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofSourceMeanDirect
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseMain
import AVRegularity.CycleComparison.Reconstruction.PulseInstance
import AVRegularity.EntryWeak.MolecularHilbertToRawSolution
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! **Source mean, Right: `Q_p` of `rightU`.** -/

section
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- `Q_p` distributes over `rightU`. -/
theorem rightU_covPolyQ (Mn : SuccMenu) {P : ProvParams} {G G' : GenStage D hr Dm b j₀}
    (W : SplitWitness P Mn G G') (depth : ℕ) (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (j : Fin 2)
    (hreg : ∀ k ∈ rightPulses D G.level t, ∀ r ∈ Finset.Icc 1 depth,
      ∀ n ∈ Finset.Icc 2 (Mn.N + Dm), ∀ (π : StagePath G r) (a' : ℕ),
      ContDiff ℝ ((2 * Mn.p : ℕ) : WithTop ℕ∞) (fun y => rightTerm Mn W g v ℓ t j k r n π a' y))
    (x : Vec 2) :
    covPolyQ (menuCovPrimitive D Mn G.level t) Mn.p (rightU Mn W depth g v ℓ t j) x =
      ∑ k ∈ rightPulses D G.level t, ocCutoff D.α D.q D.Λ G.level k t *
        ∑ r ∈ Finset.Icc 1 depth, ∑ n ∈ Finset.Icc 2 (Mn.N + Dm),
          ∑ᶠ π : StagePath G r, ∑ a' ∈ Finset.range (Mn.p + 1),
            ((a'.factorial : ℝ)⁻¹) *
              covPolyQ (menuCovPrimitive D Mn G.level t) Mn.p
                (fun y => rightTerm Mn W g v ℓ t j k r n π a' y) x := by
  have hs : ∀ (k : ℤ), k ∈ rightPulses D G.level t → ∀ r ∈ Finset.Icc 1 depth,
      ∀ n ∈ Finset.Icc 2 (Mn.N + Dm), ∀ π : StagePath G r,
      ContDiff ℝ ((2 * Mn.p : ℕ) : WithTop ℕ∞)
        (fun y => ∑ a' ∈ Finset.range (Mn.p + 1), ((a'.factorial : ℝ)⁻¹) *
          rightTerm Mn W g v ℓ t j k r n π a' y) := fun k hk r hr' n hn π =>
    ContDiff.sum fun a' _ => contDiff_const.mul (hreg k hk r hr' n hn π a')
  have hf : ∀ (k : ℤ), k ∈ rightPulses D G.level t → ∀ r ∈ Finset.Icc 1 depth,
      ∀ n ∈ Finset.Icc 2 (Mn.N + Dm),
      ContDiff ℝ ((2 * Mn.p : ℕ) : WithTop ℕ∞)
        (fun y => ∑ᶠ π : StagePath G r, ∑ a' ∈ Finset.range (Mn.p + 1), ((a'.factorial : ℝ)⁻¹) *
          rightTerm Mn W g v ℓ t j k r n π a' y) := fun k hk r hr' n hn => by
    have := Fintype.ofFinite (StagePath G r)
    simp only [finsum_eq_sum_of_fintype]
    exact ContDiff.sum fun π _ => hs k hk r hr' n hn π
  unfold rightU
  rw [right_covPolyQ_sum _ _ _ _ _ (fun k hk => ?_)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    congr 1
    rw [right_covPolyQ_sum1 _ _ _ _ (fun r hr' => ?_)]
    · refine Finset.sum_congr rfl fun r hr' => ?_
      rw [right_covPolyQ_sum1 _ _ _ _ (fun n hn => ?_)]
      · refine Finset.sum_congr rfl fun n hn => ?_
        rw [right_covPolyQ_finsum _ _ _ (fun π => hs k hk r hr' n hn π)]
        refine finsum_congr fun π => ?_
        rw [right_covPolyQ_sum _ _ _ _ _ (fun a' _ => hreg k hk r hr' n hn π a')]
      · exact hf k hk r hr' n hn
    · exact ContDiff.sum fun n hn => hf k hk r hr' n hn
  · exact ContDiff.sum fun r hr' => ContDiff.sum fun n hn => hf k hk r hr' n hn

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The `j`-th component of a dressed term. -/
theorem right_dressed_apply (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) {h : ℕ}
    (π : StagePath G h)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n a a' : ℕ) (k : ℤ)
    (t : ℝ) (φ : Vec 2 → ℝ) (x : Vec 2) (j : Fin 2)
    (hV : ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞)
      (pathJ Mn G π Cc n k t ((SuccSource.covAt D G.level Mn.anchor t)^[a'] φ))) :
    dressedPathTerm Mn G π Cc n a a' k t φ x j =
      ((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a) *
        (covOperator (menuCovPrimitive D Mn G.level t))^[a]
          (fun y => pathJ Mn G π Cc n k t ((SuccSource.covAt D G.level Mn.anchor t)^[a'] φ) y j) x := by
  unfold dressedPathTerm
  have hs : ∀ (c : ℝ) (V : Vec 2), (c • V) j = c * V j := fun c V => rfl
  rw [hs]
  congr 1
  exact Providers.GenSem.covOperator_iterate_component _ a hV x j

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- A pulse that is not active contributes nothing to the dressed terms. -/
theorem right_dressed_inactive (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    {h : ℕ} (π : StagePath G h)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n a a' : ℕ) (k : ℤ)
    (hk : ¬ Odd k) (t : ℝ) (φ : Vec 2 → ℝ) (x : Vec 2) :
    dressedPathTerm Mn G π Cc n a a' k t φ x = 0 := by
  have e : pushFlux (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level k))
      (fun x' => D.flowOf (G.level - 1) (D.slotAnchor G.level k) x' t)
      (nativePathMean Mn G π Cc n k t) ((SuccSource.covAt D G.level Mn.anchor t)^[a'] φ) =
      fun _ => 0 := by
    funext x'
    rw [nativePathMean_neg Mn G π Cc n t (fun h' => hk h'.2)]
    exact pushFlux_zero _ _ _ _
  unfold dressedPathTerm SuccSource.covAtFlux
  rw [e, ccfo_covOperator_iterate_zero, smul_zero]

open scoped Classical in
omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The `j`-th component of `pathSide`. -/
theorem right_pathSide_apply {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (W : SplitWitness P Mn G G') (depth : ℕ) (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) (j : Fin 2) :
    pathSide W depth g v ℓ t x j =
      ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level k t *
        ∑ h ∈ Finset.Icc 1 depth, ∑ n ∈ Finset.Icc 2 (Mn.N + Dm),
          ∑ᶠ π : StagePath G h, if hπ : π.tgt = v.1 ∧ π.src ∈ G.comps then
            ∑ a ∈ Finset.range (Mn.p + 1), ∑ a' ∈ Finset.range (Mn.p + 1),
              dressedPathTerm Mn G π (W.Cc (SuccSource.copyQuad [] h π)) n a a' k t
                (rightField g v ℓ π hπ.2) x j
          else 0 := by
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Vec 2), (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j :=
    fun s f => by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl
  have hs : ∀ (c : ℝ) (V : Vec 2), (c • V) j = c * V j := fun c V => rfl
  unfold pathSide
  rw [hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hs, hsum]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [hsum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have := Fintype.ofFinite (StagePath G h)
  simp only [finsum_eq_sum_of_fintype]
  rw [hsum]
  refine Finset.sum_congr rfl fun π _ => ?_
  by_cases hπ : π.tgt = v.1 ∧ π.src ∈ G.comps
  · simp only [hπ, and_self, dite_true]
    rw [hsum]
    exact Finset.sum_congr rfl fun a _ => by rw [hsum]; rfl
  · simp [hπ]

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The covariance iterates of the field of a path are smooth. -/
theorem right_field_iter_smooth (Mn : SuccMenu) {G : GenStage D hr Dm b j₀}
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (hg : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => g y v))
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) {r : ℕ} (π : StagePath G r)
    (hπ : π.src ∈ G.comps) (a' : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) ((SuccSource.covAt D G.level Mn.anchor t)^[a'] (rightField g v ℓ π hπ)) := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (rightField g v ℓ π hπ) :=
    (ℓ.comp (rootPathMap hr π.src.root π.mapList v.1.root)).contDiff.comp (hg ⟨π.src, hπ⟩)
  have htop : ∀ r : ℕ, ((r : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun r => by
    exact_mod_cast le_top
  rw [contDiff_infty]
  intro r
  exact Providers.GenSem.contDiff_covOperator_iterate _ a' (hφ.of_le (htop _))
end

/-! The first-source-flux step, step 1, part C: `FirstSourceReadoutStatement`. -/

section
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- A cast of zero is zero. -/
theorem fs_cast_zero [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)] {a b : ℕ}
    (e : b = a) (h : PiLp 2 (fun _ : Fin 2 => hr b) = PiLp 2 (fun _ : Fin 2 => hr a)) :
    cast h (0 : PiLp 2 (fun _ : Fin 2 => hr b)) = 0 := by
  subst e; rfl

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The readout collapses to the single first-source identity. -/
theorem fs_readout_collapse {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
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
          (fsDiagInner G G' g v1 u1 γ0 hu t x) := by
  classical
  unfold diagReadout readoutFlux
  rw [Finset.sum_eq_single v1]
  · simp only [hpar, and_self, ↓reduceDIte]
    congr 2
    refine fs_rootDiag_collapse g v1 u1 γ0 hu hprov0 ?_ t x
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

omit [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- Transport along a root equality is linear. -/
theorem fs_eqrec_linear [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)] {a b : ℕ}
    (h : a = b) : ∃ φ : hr a →ₗ[ℝ] hr b, ∀ y, φ y = h ▸ y := by
  subst h; exact ⟨LinearMap.id, fun _ => rfl⟩

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The component of the single-identity term as the sum over the pieces. -/
theorem fs_inner_apply {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    {depth : ℕ} {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : SplitInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G')
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v1 u1 : CompIn G'.comps) (γ0 : G'.fam.Γ v1 u1) (hu : u1.1 ∈ G.comps)
    (hprov0 : G'.prov v1 u1 γ0 = Prov.letter G.level WordLetter.diag [])
    (hdiag : (W.e v1 u1 γ0).1.IsDiag)
    (h0 : u1.1.root = v1.1.root) (hmaps : (W.e v1 u1 γ0).1.maps = [])
    (t : ℝ) (x : Vec 2) (κ : Fin 2) :
    fsDiagInner G G' g v1 u1 γ0 hu t x κ =
      h0 ▸ ∑ d ∈ Finset.Icc 2 Dm, ∑ p ∈ (G'.fam.locally_finite t t).toFinset,
        G'.fam.weight p t • ∑ A : DerivativeWord2 (d - 1),
          ((W.e v1 u1 γ0).1.lam G.level Mn.η0 *
            transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
              (Mn.N + 1 + 4 * Mn.p) (fsPieceArray Mn G G' W.Cc0 p t x) (d - 1) A x κ) •
            orderedDerivative A (fun y => g t y ⟨u1.1, hu⟩) x := by
  have htags : G'.HasTags P := hin.successor.2.2.2.2.1
  have hmax : (G'.fam.identity v1 u1 γ0).maxOrder = Mn.N + 1 + 4 * Mn.p := by
    rw [(htags v1 u1 γ0).2, hprov0]
    simp only [Prov.tags, letterOrder]
    rw [hin.stage.cutoff_eq, hin.stage.covariance_eq]
  have hmap : (G'.fam.identity v1 u1 γ0).map = rootPathMap hr u1.1.root [] v1.1.root := by
    rw [(W.spec v1 u1 γ0).2.1, hmaps]
  unfold fsDiagInner
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
      fsPieceArray Mn G G' W.Cc0 p t x d' I) (fun d' hd' _ I =>
    fs_dimFlux_eq hin W v1 u1 γ0 hdiag p t x (by omega) I) A x,
    fs_transportedCoeff_smul]

/-- **Step 1 of the first-source-flux step**: the diagonal readout is the glue over the pieces of the physical
flux of the first source. -/
theorem firstSourceReadout : FirstSourceReadoutStatement := by
  classical
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W g v t x
  obtain ⟨v1, u1, γ0, hu1v, hpar, hprov0, hwt, huniq⟩ := fs_diag_data hin W v
  have hu : u1.1 ∈ G.comps := hu1v ▸ v.2
  have hprovS := ((W.spec v1 u1 γ0).1).symm.trans hprov0
  have hdiag : (W.e v1 u1 γ0).1.IsDiag := (rsb_isDiag_iff _ _).2 hprovS
  obtain ⟨t', w', hs⟩ := fs_isDiag_cases G.level _ hprovS
  have hmaps : (W.e v1 u1 γ0).1.maps = [] := by rw [hs]; rfl
  have h0 : u1.1.root = v1.1.root := by rw [hu1v, ← hpar, compParent_root]
  rw [fs_readout_collapse W g v v1 u1 γ0 hu hpar hprov0 huniq t x]
  have hinner := fs_inner_apply hin W g v1 u1 γ0 hu hprov0 hdiag h0 hmaps t x
  rcases v with ⟨c, hc⟩
  rcases u1 with ⟨c', hc'⟩
  simp only at hu1v hu h0 hinner
  subst hu1v
  have hsupp : (Function.support fun p : OddSlot =>
      G'.fam.weight p t • fsPiecePhys Mn G G' W.Cc0 g ⟨c', hc⟩ p t x) ⊆
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
            (Mn.N + 1 + 4 * Mn.p) (fsPieceArray Mn G G' W.Cc0 p t x) (d - 1) A x κ) •
          orderedDerivative A (fun y => g t y ⟨c', hc⟩) x) hinner]
  ext κ
  simp only [fsPiecePhys, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
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
    (fsPieceArray Mn G G' W.Cc0 p t x) (d - 1) A x κ) * hwt
end

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! **The source-mean step, Left: the finite order of the Eulerian operator of a source**.

`sml_sourceEuler_expansion`: for a valid source other than the first source whose recorded order is
at most `Dm`, the Eulerian operator `sourceEulerOp` applied to a smooth scalar field is, at every
point, the differential operator of its own symmetric coefficients of the orders `2 ≤ d ≤ Dm`.
The finer-output step (clause (ii), `centeredCoefficientFiniteOrder`) gives the finite order of the finer output
at every finer label of the point, on the native family of every active pulse; the glue is
`sml_glued_expansion`. -/

open Providers.QuietAtlas Providers.GenSem CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The Eulerian operator of a source is of finite order, on smooth scalar fields.** -/
theorem sml_sourceEuler_expansion (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (hin : StageSuccessor.Input P Mn G)
    (hsucc : IsActualSuccessor D P Mn G G') (hT : TransferInput Mn G)
    (W : SplitWitness P Mn G G') (s : SuccSource G) (hv : s.Valid Mn.A Mn.J) (hnd : ¬ s.IsDiag)
    (hord : ((s.prov G.level).tags P).order ≤ Dm) (t : ℝ) (x : Vec 2) {φ : Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (a₀ : Fin 2) :
    sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor s (W.Cc s) t φ x a₀ =
      ∑ d ∈ Finset.Icc 2 Dm, ∑ I : DerivativeWord2 (d - 1),
        fluxCoeff (sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor s (W.Cc s) t)
          d I x a₀ * orderedDerivative I φ x := by
  have hL : G.level = G'.level + 1 := by
    have h1 := hsucc.1
    have h2 := hsucc.2.1
    omega
  have hΛ := hin.base
  have hlev := hin.level
  have hτk : 0 < ocTau D.α D.q D.Λ (G'.level + 1) := Construction.Stream.ocTau_pos hΛ
  have hsrc : sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor s (W.Cc s) t =
      gluedFluxOp D (G'.level + 1) (fun k => s.fluxOp (Mn.lenFactor * liftLength D G.level)
        Mn.anchor (W.Cc s) k t (nativeChain G.level k)) t := by
    unfold sourceEulerOp
    rw [hL]
  rw [hsrc]
  refine sml_glued_expansion D hΛ G'.level t x _ Dm hord _ ?_ hφ a₀
  intro k hk g hg
  have hck : ocCutoff D.α D.q D.Λ (G'.level + 1) k.1 t ≠ 0 := by simpa [activeSlots] using hk
  have htk : t ∈ ocPulseWindow D.α D.q D.Λ (G'.level + 1) k.1 :=
    mem_ocPulseWindow_of_ocCutoff_ne_zero hτk hck
  have hN : IsAdmissibleChain D b j₀ (G'.level + 1) k.1 (nativeChain (G'.level + 1) k.1) :=
    nativeChain_isCarrier D b j₀ (G'.level + 1) k.1 2 (by omega) (by omega) k.2 0
  rw [← hL] at htk hN
  exact (centeredCoefficientFiniteOrder P Mn G G' hin hsucc W s hv hnd k.1 k.2 t htk
    (nativeChain G.level k.1) hN _
    (isAdmissibleChain_nativeChain_recenter (by omega) (by omega) k _)).2
    (hT.reserve s hv) g hg

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! **Source mean, Right: linearity of a finite-order flux operator at the label `0`.** -/

section
open CovarianceTransport Providers.GenSem Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- A flux operator of finite order at `0` is additive and homogeneous on smooth fields there. -/
theorem right_finiteOrder_comb {K : ℕ} {L : (Vec 2 → ℝ) → Vec 2 → Vec 2} (hL : FiniteOrderAt K L)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Vec 2 → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) :
    L (fun w => ∑ i ∈ s, c i * f i w) 0 = ∑ i ∈ s, c i • L (f i) 0 := by
  have hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun w => c i • f i w) := fun i => (hf i).const_smul (c i)
  have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun w => ∑ i ∈ s, c i * f i w) :=
    ContDiff.sum fun i _ => contDiff_const.mul (hf i)
  rw [hL _ hsum]
  simp only [hL _ (hf _), Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  have e : orderedDerivative I (fun w => ∑ i ∈ s, c i * f i w) =
      fun w => ∑ i ∈ s, c i * orderedDerivative I (f i) w := by
    have := MixedTail.orderedDerivative_sum s I (g := fun i w => c i • f i w)
      (fun i _ => (hg i).of_le (by exact_mod_cast le_top))
    simp only [smul_eq_mul] at this
    rw [this]
    funext w
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 := congrFun (CycleComparison.Reconstruction.orderedDerivative_smul_const I (c i) (f i)) w
    simpa [smul_eq_mul] using h2
  rw [e]
  simp [Finset.sum_smul, mul_smul]

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- **The path mean on the native family is additive and homogeneous on smooth fields**, at every
label and every time of the pulse window. -/
theorem right_nativePathMean_comb (P : ProvParams) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (hin : StageSuccessor.Input P Mn G) (hm : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hX : Dm + 2 ≤ Mn.sX) (hZ : Dm + 2 ≤ Mn.sZ) {h : ℕ} (π : StagePath G h)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hLF : (SuccSource.copyQuad [] h π).IsLiftFamily Mn Cc) (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Vec 2 → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (z : Vec 2) :
    nativePathMean Mn G π Cc n k t (fun w => ∑ i ∈ s, c i * f i w) z =
      ∑ i ∈ s, c i • nativePathMean Mn G π Cc n k t (f i) z := by
  by_cases hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k
  · obtain ⟨kI, hcert⟩ := hin.context
    have hΛ := hin.base
    have hζ := hin.profile
    have hκ := hin.band
    have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
    have hρ : Mn.lenFactor * liftLength D G.level ≠ 0 := by
      have hκm : 0 < D.κ (G.level - 1) :=
        CycleReference.bandChain_pos hΛ hζ hκ (by have := hin.top; omega)
      exact (mul_pos hin.length_factor
        (Real.sqrt_pos.2 (mul_pos hκm (Construction.Stream.ocTauPP_pos hΛ)))).ne'
    have hcov : FluxRecenterShift G := fluxRecenterShift_of_oldCert hΛ hζ hcert.oldCert
    have hBz := isAdmissibleChain_nativeChain_recenter (D := D) (b := b) hm hj ⟨k, hA.2⟩ z
    have key : ∀ f : Vec 2 → ℝ, nativePathMean Mn G π Cc n k t f z =
        pathMeanFlux D G.level (Mn.lenFactor * liftLength D G.level)
          (familyLiftData D G.level k ((nativeChain G.level k).recenter D z)
            (Mn.lenFactor * liftLength D G.level)
            (pathEdges G π ⟨k, hA.2⟩ ⟨(nativeChain G.level k).recenter D z, hBz⟩))
          (Cc k ((nativeChain G.level k).recenter D z)) n t (fun w => f (z + w)) 0 := by
      intro f
      have hpm := ccov_pathMeanFlux_recenter hΛ hζ hcov hc π k hA.2 hA.1 z hBz hρ Mn.sX Mn.sZ
        Mn.N (Cc k ((nativeChain G.level k).recenter D z)) (Cc k (nativeChain G.level k))
        (hLF k _ ⟨hBz, hA.2⟩) (hLF k _ hA) n ht f 0 (by rw [add_zero]; exact hBz)
      rw [add_zero] at hpm
      rw [hpm, nativePathMean_pos Mn G π Cc n t hA]
    have hfo := ccfo_pathMeanFlux hΛ hζ hκ hin.bandwidth hcert.oldCert π k hA.2 hBz hρ hX hZ
      (Cc k ((nativeChain G.level k).recenter D z)) (hLF k _ ⟨hBz, hA.2⟩) ht hn
    have hsm : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun w => f i (z + w)) := fun i =>
      (hf i).comp (contDiff_const.add contDiff_id)
    rw [key]
    have := right_finiteOrder_comb hfo s c (fun i w => f i (z + w)) hsm
    rw [Finset.sum_congr rfl fun i _ => by rw [key (f i)]]
    exact this
  · rw [nativePathMean_neg Mn G π Cc n t hA]
    simp

open scoped Classical in
/-- **The linearity step is proved**: the pushed path mean is linear on smooth fields. -/
theorem rightPathLinear : RightPathLinearStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W t k hk hcut r hr' n hn π φ hφ y
  have hΛ := hin.stage.base
  have hm : 1 ≤ G.level := by have := hin.stage.level; omega
  have hj : j₀ ≤ G.level := by have := hin.stage.level; omega
  obtain ⟨Dord, nMax, hMax, npad, -, -, -, -, -, h1, h2⟩ := hin.range
  have ht := mem_ocPulseWindow_of_ocCutoff_ne_zero (Construction.Stream.ocTau_pos hΛ) hcut
  have hn1 : 1 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
  have htop : ∀ r : ℕ, ((r : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun r => by
    exact_mod_cast le_top
  have hsm : ∀ a' : ℕ, ContDiff ℝ (⊤ : ℕ∞)
      (fun w => (SuccSource.covAt D G.level Mn.anchor t)^[a'] φ
        (D.flowOf (G.level - 1) t w (D.slotAnchor G.level k))) := fun a' => by
    have hg : ContDiff ℝ (⊤ : ℕ∞) ((SuccSource.covAt D G.level Mn.anchor t)^[a'] φ) := by
      rw [contDiff_infty]
      intro r
      exact contDiff_covOperator_iterate _ a' (hφ.of_le (htop _))
    exact hg.comp (flowOf_contDiff D (G.level - 1) t (D.slotAnchor G.level k))
  have hcomb := right_nativePathMean_comb P Mn G hin.stage hm hj (by omega) (by omega) π
    (W.Cc (SuccSource.copyQuad [] r π)) (W.lifts (SuccSource.copyQuad [] r π)) n hn1 k ht
    (Finset.range (Mn.p + 1)) (fun a' => ((a'.factorial : ℝ)⁻¹))
    (fun a' w => (SuccSource.covAt D G.level Mn.anchor t)^[a'] φ
        (D.flowOf (G.level - 1) t w (D.slotAnchor G.level k))) hsm
    (D.flowOf (G.level - 1) (D.slotAnchor G.level k) y t)
  unfold pathJ pushFlux
  have e : (covPolyP (menuCovPrimitive D Mn G.level t) Mn.p φ) ∘
      (fun w => D.flowOf (G.level - 1) t w (D.slotAnchor G.level k)) =
      fun w => ∑ a' ∈ Finset.range (Mn.p + 1), ((a'.factorial : ℝ)⁻¹) *
        (SuccSource.covAt D G.level Mn.anchor t)^[a'] φ
          (D.flowOf (G.level - 1) t w (D.slotAnchor G.level k)) := by
    funext w
    simp [covPolyP, Finset.sum_apply, SuccSource.covAt, menuCovPrimitive]
  rw [e, hcomb, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Matrix.mulVec_smul]
  rfl
end

/-! The first-source-flux step, step 2: the named sub-steps of `FirstSourcePieceStatement` and its
assembly.

For a piece `p` of `G'` at `(t, x)` write `Y = Φ_p(t,·)⁻¹ x`, `ch` the actual context of `p`
recentred at `Y`, `ζ = ε_{m-1}⁻¹ Y`, and `L = firstSourceFlux … t ch ζ` (`fsLabelOp`). Then:
* **Piola** (`FSStepPiola`): the component `ℓ` of `fsPiecePhys` is `K(x) · L(ℓ∘g∘Φ_p(t, Y+·)) (0)`
  (`fsEulerRead`): the arrays reconstruct the operator at the centre (`arrOp_eq_sum_fluxCoeff`,
  `firstSourceFlux_applyArr`, with the word symmetrization), the Piola-transport step transports it, the
  `C^K` field is handled as in the finer-output and transfer steps.
* **Strain** (`FSStepStrain`): at a time of nonzero weight the context strain at the actual
  context is `D𝐛_{m-1}` (`context_strain_physical`, `mem_ocPulseWindow_of_ocCutoff_ne_zero`,
  `IsNatural`).
* **Diagonal** (`FSStepDiagShift`, with the field translated to the centre): `diagFluxCtx` at the
  recentred actual context is the physical
  diagonal flux `menuDiagFluxPhys`, componentwise (`hilbertLiftGradeZero`; every active finer slot
  is scheduled in the piece; recentring covariance of the scalar lifts).
* **Algebra** (`FSStepAlgebraConcl`): from the two identifications, `fsEulerRead` is `-Q_p 𝒟`
  (unfold `firstSourceFlux = pullFlux …`, the chart relation `Φ_p`, `famMap`, conjugation of
  `𝒞`, `Q_p`, `P_p`). -/

section
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The recentred actual context of the piece `p` at the physical point `x`. -/
def fsCtx (G' : GenStage D hr Dm b j₀) (p : OddSlot) (t : ℝ) (x : Vec 2) : RealChain :=
  (G'.actual p).1.recenter D (((G'.fam.piece p).material t).symm x)

/-- The label operator of the first source at the piece `p` and the point `x`. -/
def fsLabelOp (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (p : OddSlot) (t : ℝ)
    (x : Vec 2) : (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  firstSourceFlux D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N Mn.p Mn.anchor Cc0 t
    (fsCtx G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)

open scoped Classical in
/-- The Eulerian reading of the label operator on a scalar field `f`: the Piola factor
`K(x) = chartInvJacobian` times the label operator at the centre on `f∘Φ_p(t, Y + ·)`;
zero off the carrier. -/
def fsEulerRead (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (p : OddSlot) (t : ℝ)
    (x : Vec 2) (f : Vec 2 → ℝ) : Vec 2 :=
  if IsAdmissibleChain D b j₀ G'.level p.1 (fsCtx G' p t x) then
    (chartInvJacobian ⇑((G'.fam.piece p).material t).symm x).mulVec
      (fsLabelOp Mn G G' Cc0 p t x
        (fun y => f ((G'.fam.piece p).material t (((G'.fam.piece p).material t).symm x + y))) 0)
  else 0

/-- **Sub-step Piola.**-/
def FSStepPiola : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (K : ℕ) (ta tb : ℝ)
      (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root), FSField Mn G K ta tb g →
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc ta tb, ∀ x : Vec 2, ∀ p : OddSlot,
      G'.fam.weight p t ≠ 0 → ∀ (ℓ : hr v.1.root →L[ℝ] ℝ) (κ : Fin 2),
      ℓ (fsPiecePhys Mn G G' W.Cc0 g v p t x κ) =
        fsEulerRead Mn G G' W.Cc0 p t x (fun y => ℓ (g t y v)) κ

/-- **Sub-step Strain.**At a time of nonzero weight the context strain at the actual
context recentred at any `Y` is `D𝐛_{m-1}` (the statement of `context_strain_physical`). -/
def FSStepStrain : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 → ∀ Y : Vec 2,
      contextStrain D (G.level - 1) p.1 t ((G'.actual p).1.recenter D Y)
          ((D.eps (G.level - 1))⁻¹ • Y) =
        jacMatrix (streamVel (D.Φ (G.level - 1)) t)
          (((((G'.actual p).1.recenter D Y).geom D).1 t Y
            (((G'.actual p).1.recenter D Y).geom D).2.2))
end

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
