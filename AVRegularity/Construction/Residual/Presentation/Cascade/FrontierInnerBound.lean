-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Cascade.GluedFluxIdentity
import AVRegularity.Construction.Preservation.Frontier.GradeRows.ExtendedLedger
import AVRegularity.Construction.KernelDefect.UniformDefect
public import AVRegularity.Construction.Residual.Presentation.Cascade.CovForms
import AVRegularity.Construction.Residual.Presentation.FluxAe
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Frontier
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The regularizer clause of the kernels of the extended stage** (cascade side of the
bill residual).

The retained data of the frontier bound (the `retainedData`, the retained-data clause) asks the regularizer
clause `RegClause` of the kernels of the EXTENDED stage `G'` (the actual successor of the
incoming stage `G`) at the retained targets, on the window `[t_p, t_f]`. The invariant of the
context is the invariant of `G`, not of `G'`.

* `extendedKernelRegularizers`: for a stage `G` with the stage invariant on `[t_A, t_B]` and
  an actual successor `G'`, every kernel of `G'` is a spatial regularizer on every window inside
  `[t_A, t_B]`, at every radius `ρ > 0` and order `k ≤ k_I.K_s`, with any constants above
  `k_I.c_ker` and the constants `c_f` of the fresh kernels. The old kernels have the clause by
  clause 4 of the invariant of `G`; the fresh kernel of the level `G.level − 1` by
  `uniform_fresh_kernel_regularizer`; `extended_successor_kernel_regularizers` carries both to
  `G'` (the transfer between root spaces asks them nontrivial). The constants `(c_f, m₀)` are
  chosen before the stage, from the template, the kernel order and the scales.
* `succPrefix_regClause`: `RegClause` at every context of level `≥ m_*`, at every order
  `k ≤ k_I.K_s`, with the constants `max k_I.c_ker c_f`, in the common prefix form.

For a successor without fresh edges only the old clause is used; for a non-retained
target nothing is asked; `t_p = t_f` and `k = 0` are allowed. -/

/-- **The kernels of the actual successor of a stage with the stage invariant are spatial
regularizers**, with constants chosen before the stage. -/
theorem extendedKernelRegularizers (φ₀ : Vec 2 → ℝ) (hc : HasCompactSupport φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (nk : ℕ+) (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ cf : ℕ → ℝ, (∀ j, 0 ≤ cf j) ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (P : ProvParams) (Mn : SuccMenu) (law : BirthLaw)
      (seedK freshK : ℕ → KernelSpec) (kI : InvConsts) (cr σ₀ : ℝ), 0 < cr →
      (∀ l, 1 ≤ l → l < D.term → IsFreshKernel D cr σ₀ nk l (freshK l)) →
    ∀ (M : ℕ) (G G' : GenStage D hr Dm bw j₀) (hφ₀ : Integrable φ₀) (tA tB S θK : ℝ),
      IsStageInvariant law P seedK freshK φ₀ hφ₀ M kI tA tB S θK G →
      IsActualSuccessor D P Mn G G' → m₀ ≤ G.level → G.level ≤ D.term →
    ∀ (C : ℕ → ℝ), (∀ j, j + 2 ≤ Dm → kI.cker j ≤ C j ∧ cf j ≤ C j) →
    ∀ a b : ℝ, Set.Icc a b ⊆ Set.Icc tA tB → ∀ ρ : ℝ, 0 < ρ → ∀ k, k ≤ kI.Ks →
    ∀ v u (γ : G'.fam.Γ v u),
      IsSpatialRegularizerTorus ρ k Dm a b C (G'.kernelOf P seedK freshK v u γ).width
        (G'.sysS P seedK freshK φ₀ hφ₀ v u γ) := by
  obtain ⟨cf, hcf, m₀, hm₀, hf⟩ := uniform_fresh_kernel_regularizer
    φ₀ hc hd nk α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ Λ hΛ
  refine ⟨cf, hcf, m₀, hm₀, ?_⟩
  intro hr _ _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq hband Dm bw j₀ P Mn law seedK freshK kI cr σ₀ hcr
    hfresh M G G' hφ₀ tA tB S θK hI hact hlevel hterm C hC a b hwindow ρ hρ k hk
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hlt : G.level - 1 < D.term := by omega
  have hspec := hfresh (G.level - 1) (by omega) hlt
  have hκ : 0 < D.κ (G.level - 1) := CycleReference.bandChain_pos hΛD hζD hband hlt.le
  have hwidth : 0 < (freshK (G.level - 1)).width := by
    rw [hspec.1]
    unfold freshWidth freshLength
    exact mul_pos (mul_pos hcr (Real.sqrt_pos.2
      (mul_pos hκ (Construction.Stream.ocTauPP_pos hΛD))))
      (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛD) _)
  have hreg := hf ℝ D hDα hDq hDΛ hDζ hseq hband (G.level - 1) (by omega) (by omega)
    (freshK (G.level - 1)) hspec.2.1 hwidth hspec.2.2 ρ a b k Dm
  have hfr := spatial_regularizer_constants_mono hreg hwidth.le (fun j hj => (hC j hj).2)
  obtain ⟨_, _, _, _, _, _, _, _, hker, _⟩ := hI
  have hold : ∀ v u (γ : G.fam.Γ v u), IsSpatialRegularizerTorus ρ k Dm a b C
      (G.kernelOf P seedK freshK v u γ).width (G.sysS P seedK freshK φ₀ hφ₀ v u γ) := by
    intro v u γ
    have hsrc := (hker v u γ).2.2.2.2 ρ hρ k hk
    have hpos : 0 ≤ (G.kernelOf P seedK freshK v u γ).width := by
      rw [(hker v u γ).2.1]
      exact (G.fam.identity v u γ).record.width_pos.le
    exact spatial_regularizer_constants_mono
      (Construction.Preservation.Buffer.spatialRegularizerTorus_time_restrict hsrc hwindow) hpos
      (fun j hj => (hC j hj).1)
  exact extended_successor_kernel_regularizers P Mn G G' hact seedK freshK φ₀ hφ₀ ρ a b k C hold
    hfr

/-- **The regularizer clause at every context of level `≥ m_*`**: the regularizer clause of the kernels of the
extended stage at the retained targets, at every order `k ≤ k_I.K_s`, with the constants `C`. -/
def RegClauseCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (C : ℕ → ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m → ∀ k : ℕ, k ≤ kI.Ks →
    RegClause c.G' (c.G'.retained c.m H J)
      (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀ hφ₀ k c.tp c.tf C

/-- **The regularizer clause in the common prefix form**; the constants are `(max k_I.c_ker c_f, m_*)`. -/
theorem succPrefix_regClause (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := (ℕ → ℝ) × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        RegClauseCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ x.1 x.2) := by
  refine SuccPrefix.of_scale (P := fun _ => True) ⟨128, le_rfl, fun _ _ => trivial⟩ ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ hfacts _ CQ Cpr
  obtain ⟨cf, -, m₀, -, h⟩ := extendedKernelRegularizers φ₀
    (Construction.KernelDefect.kd_hasCompactSupport hfacts.support) hfacts.smooth nk.toPNat' α s
    q hα₀ hα₁ hs₀ hs₁ hq ζ hζ Λ hfacts.hΛ
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hcr : 0 < kI.cr := by rw [hkI.2.1]; exact hfacts.hcr
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  refine ⟨(fun j => max (kI.cker j) (cf j), m₀), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm k hk v u γ _
  exact h hr c.D c.hα c.hq c.hΛ c.hζ c.hseq c.bandD _ bw j₀ _
    (succMenu c.Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) c.law c.seedK c.freshK kI kI.cr
    σ₀ hcr (fun l h1 h2 => c.hfresh l h1 (c.hterm ▸ h2)) c.Mnat c.G c.G' hφ₀ c.tA c.tf _ _
    c.hinv c.hactual (by rw [c.hlevel]; exact hm) (by rw [c.hlevel]; exact c.m_le_term) _
    (fun j _ => ⟨le_max_left _ _, le_max_right _ _⟩) c.tp c.tf
    (Set.Icc_subset_Icc (c.tA_le_tp hΛ1) le_rfl) 1 one_pos k hk v u γ

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The lift step of the fine tail at a frame, proof.** Assembly of
`lift_at_order` (the frame's own lifted field at the order `K + 1`), `aesm_of_value`
(strong measurability in time) and `energy_forms` (the forms from `FullLiftClauses`). -/

open AVRegularity AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem menuLiftedRep_eq (F : Frame D hr Dm b j₀) (hlen : F.Mn.lenFactor = 1)
    (hlev : F.G.level = F.m) :
    menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep =
      Glued F.G F.N F.depth F.CcT F.aRep := by
  funext t
  unfold menuLiftedRep Glued
  rw [hlen, one_mul, ← hlev]

theorem fineLiftAt (F : Frame D hr Dm b j₀) (law : BirthLaw) (c₀ cr Ck Ain : ℝ)
    (Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)) (K : ℕ) :
    FineLiftAt' F law c₀ cr Ck Ain Yw K := by
  classical
  intro hk hlen hanc hlev hAin hmass hρ hκ hmeas hhigh hsrc hFL
  obtain ⟨hi, hΛ, hζ, hband, htorus, Kp, kp, Lp, CG, Cw, Cj, S, slotLifts, hres, hrQ⟩ := hsrc
  have hglue := menuLiftedRep_eq F hlen hlev
  have hl1 := F.lift.1
  have hl2 := F.lift.2.1
  simp only [hlen, one_mul] at hl1
  have hl2' : ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      IsCovImage (covPolyP (covPrimitive D F.m t) F.p)
        (succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun v' => F.Y v' t) v)
        (F.PZ v t) ∧ IsClassicalRep (F.PZ v t) (fun x => F.aRep t x v) (F.Naux - 2 * F.p) := by
    intro v t ht
    have h := hl2 v t ht
    unfold menuCovPrimitive at h
    rw [hanc] at h
    exact h
  obtain ⟨u, w, hfield, hu, hw⟩ := lift_at_order slotLifts hi hΛ hζ hband htorus F.m hlev K
    hres hrQ F.p F.Naux F.sX F.sZ hk F.η₀ F.tp F.tf F.Y hhigh F.CcT F.PZ F.aRep hl1 hl2'
  have hval : ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      (u v t).toFunction.jet (valueIndex2 (K + 1)) =ᵐ[volume.restrict unitCube]
        fun x => menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep t x v := by
    intro v t ht
    rw [hglue]
    exact classicalRep_value_ae (u v t) _ (hu v t ht)
  have hmeas' : ∀ v : CompIn F.G.comps, AEStronglyMeasurable (u v)
      (volume.restrict (Set.Icc F.tp F.tf)) := by
    intro v
    refine aesm_of_value F.tp F.tf (u v)
      (fun t x => menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep t x v) ?_ (hval v)
    exact hmeas v
  obtain ⟨hE1, hE2⟩ := hFL.2 F.CcT F.PZ F.aRep u w hfield (fun _ => 1) (Or.inl rfl)
  have hCle : strongEnergy (rhoStar D c₀ F.m) (D.κ F.m) (fun v => F.G.mass law v / 1 ^ 2)
      F.tp F.tf u w ≤ ENNReal.ofReal (Ck * Ck * Ain) := by
    refine hE1.trans ?_
    by_cases hC : 0 ≤ Ck
    · calc ENNReal.ofReal Ck * readoutEnergy law F.G F.Gr F.m F.η₀ (rhoEnh D cr F.m) hk
            (fun _ => 1) F.tp F.tf F.Y Yw
          ≤ ENNReal.ofReal Ck * ENNReal.ofReal (Ck * Ain) := by gcongr
        _ = ENNReal.ofReal (Ck * Ck * Ain) := by
            rw [← ENNReal.ofReal_mul hC, mul_assoc]
    · have : ENNReal.ofReal Ck = 0 := ENNReal.ofReal_of_nonpos (by linarith)
      rw [this, zero_mul]; exact zero_le
  have hπ : (fun v : CompIn F.G.comps => F.G.mass law v / 1 ^ 2) = F.G.mass law := by
    funext v; simp
  rw [hπ] at hCle
  obtain ⟨hM, hI, hS⟩ := energy_forms (E := fun v : CompIn F.G.comps => hr v.1.root)
    (rhoStar D c₀ F.m) (D.κ F.m) (F.G.mass law) hmass hρ hκ F.tp F.tf u w hfield.2 hmeas'
    (Ck * Ck * Ain) (mul_nonneg (mul_self_nonneg Ck) hAin) hCle
  refine ⟨u, ⟨hM, hval, fun v t ht => ?_⟩, hI, hS⟩
  rw [hglue]
  exact ⟨(hu v t ht).2.1, (hu v t ht).2.2.1⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Frontier
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The frontier bound (bound part): the realization of the inner frontier flux at a stage**
(the cascade route of the inner flux).

`hasFluxBound_sel`: for the frontier frame `FF` and a selection `grade`, the three frame-level
frontier statements (`OutsideRowCauchyStatement`, `MarkerReadoutStatement`,
`SourceLayerEnergyStatement` at the value `grade`), `frame_stage_generic` (which keeps `MemLp`),
and the identification of the omitted flux of the edge inputs `yom` with the classical omitted
flux give a realization of the classical readout over the selection with the mass bound
`C^3 E^{exponent grade} ‖Y₀‖`.

No terminal context occurs here.

For `Y₀ = 0` the bound is `0` and the realization has zero mass; for `J = 0` the length
selection is the first prefix; with no row selected the readout is `0`. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The energy of a readout realization with the time integrability of both fluxes kept, at a
value `grade` of the selection (the generic form of `frame_readout_energy_le`, which is stated at
`grade = false`). -/
theorem readout_energy_le (F : Preservation.Frontier.Frame D hr Dm b j₀) (grade : Bool)
    (hν : 0 ≤ D.κ (F.m - 1)) (C g : ℝ)
    (hg : F.rowGain grade * F.markerGain grade * F.layerGain grade = g)
    (OF : F.RowFlux) (hOFlp : ∀ v, MemLp (OF v) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (hrow : F.rowEnergy OF ≤ (C * F.rowGain grade) ^ 2 * F.sourceDissipation grade)
    (hsource : F.sourceDissipation grade ≤ (C * F.layerGain grade * F.initialNorm) ^ 2)
    (RF : F.ReadoutFlux) (hRFlp : ∀ v, MemLp (RF v) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (hpoint : ∀ t ∈ Set.Icc F.tp F.tf,
        massNormSq (rhoEnh D F.cr F.m) (F.G.mass F.law) (fun v => (RF v t).val) ≤
          (C * F.markerGain grade) ^ 2 *
            massNormSq (rhoEnh D F.cr F.m)
              (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) (fun v => (OF v t).val)) :
    F.readoutEnergy RF ≤ (C ^ 3 * g * F.initialNorm) ^ 2 := by
  have hRi := CycleComparison.Error.integrable_massNormSq
    (rhoEnh D F.cr F.m) (F.G.mass F.law) RF hRFlp
  have hOi := CycleComparison.Error.integrable_massNormSq
    (rhoEnh D F.cr F.m)
    (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) OF hOFlp
  have hi := integral_mono_ae hRi (hOi.const_mul ((C * F.markerGain grade) ^ 2))
    ((ae_restrict_mem measurableSet_Icc).mono fun t ht => hpoint t ht)
  have hR : F.readoutEnergy RF ≤ (C * F.markerGain grade) ^ 2 * F.rowEnergy OF := by
    dsimp only [Frame.readoutEnergy, Frame.rowEnergy]
    rw [integral_const_mul] at hi
    exact (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hν)).trans_eq (by ring)
  calc
    F.readoutEnergy RF ≤ (C * F.markerGain grade) ^ 2 * F.rowEnergy OF := hR
    _ ≤ (C * F.markerGain grade) ^ 2 * ((C * F.rowGain grade) ^ 2 * F.sourceDissipation grade) :=
      mul_le_mul_of_nonneg_left hrow (sq_nonneg _)
    _ ≤ (C * F.markerGain grade) ^ 2 *
        ((C * F.rowGain grade) ^ 2 * (C * F.layerGain grade * F.initialNorm) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsource (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by rw [← hg]; ring

/-- **The three analytic inputs at a frame, at a value `grade` of the selection, with `MemLp`
kept** (the generic form of `frame_stage_generic`, which is stated at `grade = false`). -/
theorem stage_generic (F : Preservation.Frontier.Frame D hr Dm b j₀) (grade : Bool)
    (hν : 0 ≤ D.κ (F.m - 1)) (C g : ℝ)
    (hg : F.rowGain grade * F.markerGain grade * F.layerGain grade = g)
    (hR : OutsideRowCauchyStatement F grade C) (hM : MarkerReadoutStatement F grade C)
    (hL : SourceLayerEnergyStatement F grade C) :
    ∃ RF : F.ReadoutFlux, F.RealizesReadout grade RF ∧
      (∀ v, MemLp (RF v) 2 (volume.restrict (Set.Icc F.tp F.tf))) ∧
      F.readoutEnergy RF ≤ (C ^ 3 * g * F.initialNorm) ^ 2 := by
  obtain ⟨OF, hOF, hOFlp, hrow⟩ := hR
  obtain ⟨RF, hRF, hRFlp, hpoint⟩ := hM OF hOF hOFlp
  exact ⟨RF, hRF, hRFlp, readout_energy_le F grade hν C g hg OF hOFlp hrow hL RF hRFlp hpoint⟩

open scoped Classical in
/-- **One selection of the inner frontier flux**: a realization of the classical readout of the
omitted flux over the selection `FF.select grade`, with the mass bound `C³ E^{exponent} ‖Y₀‖`. -/
theorem hasFluxBound_sel (FF : Preservation.Frontier.Frame D hr Dm b j₀) (grade : Bool) (C : ℝ)
    (hC : 0 ≤ C) (hν : 0 < D.κ (FF.m - 1)) (hE : 0 < D.eps (FF.m - 1))
    (hrows : OutsideRowCauchyStatement FF grade C) (hmark : MarkerReadoutStatement FF grade C)
    (hsrc : SourceLayerEnergyStatement FF grade C) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (aY : ℝ → Vec 2 → ∀ v : CompIn (FF.G'.retained FF.m FF.H FF.J).comps, hr v.1.root)
    (hid : ∀ v : CompIn FF.G'.comps, ∀ t ∈ Set.Icc FF.tp FF.tf,
      ∀ᵐ y ∂(volume.restrict AVenhance.unitCube),
        omittedFlux FF.G' FF.k (IsRetained FF.m FF.H FF.J) FF.yom v t y =
          omittedFluxClassical P seedK freshK φ₀ FF.G' (FF.G'.retained FF.m FF.H FF.J) aY v t y) :
    HasFluxBound (ι := CompIn FF.G.comps) (h := fun v => hr v.1.root) FF.k
      (Set.Icc FF.tp FF.tf) (D.κ (FF.m - 1)) (rhoEnh D FF.cr FF.m) (FF.G.mass FF.law)
      (fun v t y => toFluxL (WithLp.ofLp
        (readoutFlux (S := FF.G.comps) FF.m (D.eps (FF.m - 1)) FF.η (FF.select grade)
          (fun v' s y' => omittedFluxClassical P seedK freshK φ₀ FF.G'
            (FF.G'.retained FF.m FF.H FF.J) aY v' s y') v t y)))
      (C ^ 3 * D.eps (FF.m - 1) ^ FF.exponent grade * FF.initialNorm) := by
  obtain ⟨RF, hRF, hRFlp, hen⟩ := stage_generic FF grade hν.le C
    (D.eps (FF.m - 1) ^ FF.exponent grade) (frontier_gain_product FF hE grade) hrows hmark hsrc
  have hg : 0 < D.eps (FF.m - 1) ^ FF.exponent grade := Real.rpow_pos_of_pos hE _
  have hn : 0 ≤ FF.initialNorm := frame_initialNorm_nonneg FF
  refine ⟨RF, ?_, hRFlp, ?_⟩
  · intro v t ht
    have h1 := hRF v t ht
    have h2 : ∀ᵐ y ∂(volume.restrict AVenhance.unitCube), ∀ v' : CompIn FF.G'.comps,
        omittedFlux FF.G' FF.k (IsRetained FF.m FF.H FF.J) FF.yom v' t y =
          omittedFluxClassical P seedK freshK φ₀ FF.G' (FF.G'.retained FF.m FF.H FF.J) aY v' t y :=
      ae_all_iff.2 fun v' => hid v' t ht
    filter_upwards [h1, h2] with y hy1 hy2
    refine hy1.trans ?_
    simp only [toFluxL, WithLp.toLp_ofLp]
    exact readoutFlux_congr FF.m _ _ _ _ (fun _ _ => Iff.rfl) _ _ v t y hy2
  · have hY : Real.sqrt (FF.readoutEnergy RF) ≤
        C ^ 3 * D.eps (FF.m - 1) ^ FF.exponent grade * FF.initialNorm := by
      refine (Real.sqrt_le_sqrt hen).trans ?_
      rw [Real.sqrt_sq (by positivity)]
    exact hY

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The frontier bound: the bound part of `FrontierInnerForm` at a frame**.

`frontierInner_bound`: at a frame `F` of the covariance transport, for every order `kc`
(the order of the readout is `kc + 2p`), from

* the frame-level frontier statements at both values of `grade`
  (`FrontierAt`: row Cauchy, marker readout, source-layer energy, at the frontier frame
  `FrontierFrame F …` of the order `kc + 2p` with the retained data `Y₀, Y_w` and the edge
  inputs `yom`),
* the identification of the omitted flux of `yom` with the classical omitted flux of `F.aY`
  (the proved `omittedFlux_ae_eq_classical`, fed by a classical representative of `Y_w` at the
  order `kc + 2p + 1` and by the kernel compatibility of `yom` at every time of the window),
* `‖Y₀‖ ≤ C_pr A_in` as a named hypothesis,

the classical readout of the omitted flux has a realization of order `kc + 2p` with mass bound
`C³ C_pr (E^{ιΣ_H} + E^{θ₁+Jθ₂}) A_in`, the price `succFrontPrice` of `succBill`.

For `J = 0` the length frontier is the words of length `1`; with no omitted row the readout is
`0`; for `A_in = 0` the bound is `0`; `tp = tf` is allowed.

The smoothness clause of `FrontierInnerForm` is treated separately (`S168Smooth`). -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The frontier frame of a bill frame**: the stages, the passage and the window of `F`, the
order `k = kc + 2p`, and the retained data `Y₀, Y_w` and edge inputs `yom` of the frontier
statements. -/
def FrontierFrame (F : Frame D hr Dm b j₀) (law : BirthLaw) (kc : ℕ) (cr θ₁ θ₂ : ℝ)
    (Y0 : ∀ v : CompIn (F.G'.retained F.m F.H F.J).comps, TorusHk (kc + 2 * F.p) (hr v.1.root))
    (Yw : ∀ v : CompIn (F.G'.retained F.m F.H F.J).comps, ℝ →
      TorusHk (kc + 2 * F.p + 1) (hr v.1.root))
    (yom : ∀ v u (_ : F.G'.fam.Γ v u), ℝ → TorusHk (kc + 2 * F.p + Dm - 1) (hr u.1.root)) :
    Preservation.Frontier.Frame D hr Dm b j₀ :=
  { G := F.G, G' := F.G', law := law, m := F.m, H := F.H, J := F.J, k := kc + 2 * F.p,
    cr := cr, η := F.η₀, θ₁ := θ₁, θ₂ := θ₂, tp := F.tp, tf := F.tf, Y0 := Y0, Yw := Yw,
    yom := yom }

/-- **The three frame-level frontier statements at one value of `grade`**
(the conclusion of `FrontierAnalyticProductionStatement α s q ζ grade`, with its default join,
at the frontier frame). -/
def FrontierAt (FF : Preservation.Frontier.Frame D hr Dm b j₀) (grade : Bool) (C : ℝ) :
    Prop :=
  Preservation.Frontier.OutsideRowCauchyStatement FF grade C ∧
    Preservation.Frontier.MarkerReadoutStatement FF grade C ∧
    Preservation.Frontier.SourceLayerEnergyStatement FF grade C

/-- **The classical representative of the retained solution, indexed by the retained stage**
`F.G'.retained m H J` (the frame carries it indexed by `F.Gr`, which is that stage). -/
def AYret (F : Frame D hr Dm b j₀) (hGr : F.Gr = F.G'.retained F.m F.H F.J) :
    ℝ → Vec 2 → ∀ v : CompIn (F.G'.retained F.m F.H F.J).comps, hr v.1.root :=
  fun t x u => F.aY t x ⟨u.1, by rw [hGr]; exact u.2⟩

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The readout of the omitted flux does not see the name of the retained stage. -/
theorem readout_transport (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' Gr Gr' : GenStage D hr Dm b j₀) (m H J : ℕ) (E η₀ : ℝ) (h : Gr = Gr')
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (y : Vec 2) :
    frontierReadout P seedK freshK φ₀ G G' Gr m H J E η₀ aY v t y =
      frontierReadout P seedK freshK φ₀ G G' Gr' m H J E η₀
        (fun t x u => aY t x ⟨u.1, by rw [h]; exact u.2⟩) v t y := by
  subst h
  rfl

open scoped Classical in
/-- **The frontier bound, the bound part of the inner frontier flux at a frame.** -/
theorem frontierInner_bound (F : Frame D hr Dm b j₀) (law : BirthLaw)
    (hGr : F.Gr = F.G'.retained F.m F.H F.J) (kc : ℕ) (cr θ₁ θ₂ C Cpr Ain : ℝ) (hC : 0 ≤ C)
    (hν : 0 < D.κ (F.m - 1)) (hE : 0 < D.eps (F.m - 1)) (hπ : ∀ v, 0 < F.G.mass law v)
    (hrows : ∀ c ∈ F.G'.comps, compGrade c ≤ F.H + 1 ∧
      (compGrade c ≤ F.H → (compWord F.m c).length ≤ F.J + 1))
    (Y0 : ∀ v : CompIn (F.G'.retained F.m F.H F.J).comps, TorusHk (kc + 2 * F.p) (hr v.1.root))
    (Yw : ∀ v : CompIn (F.G'.retained F.m F.H F.J).comps, ℝ →
      TorusHk (kc + 2 * F.p + 1) (hr v.1.root))
    (yom : ∀ v u (_ : F.G'.fam.Γ v u), ℝ → TorusHk (kc + 2 * F.p + Dm - 1) (hr u.1.root))
    (hgrade : FrontierAt (FrontierFrame F law kc cr θ₁ θ₂ Y0 Yw yom) true C)
    (hlength : FrontierAt (FrontierFrame F law kc cr θ₁ θ₂ Y0 Yw yom) false C)
    (hY0 : (FrontierFrame F law kc cr θ₁ θ₂ Y0 Yw yom).initialNorm ≤ Cpr * Ain)
    (hφ : Integrable F.φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) F.φ₀) (hφc : HasCompactSupport F.φ₀)
    (hkY : Dm - 1 ≤ kc + 2 * F.p + 1)
    (hYcl : ∀ u, ∀ t ∈ Set.Icc F.tp F.tf,
      IsClassicalRep (Yw u t) (fun x => AYret F hGr t x u) (kc + 2 * F.p + 1))
    (hv : ∀ t ∈ Set.Icc F.tp F.tf, ∀ v u (γ : F.G'.fam.Γ v u)
      (hu : u.1 ∈ (F.G'.retained F.m F.H F.J).comps),
      (yom v u γ t).val (valueIndex2 (kc + 2 * F.p + Dm - 1)) =
        (F.G'.kernelOf F.P F.seedK F.freshK v u γ).op F.φ₀ hφ t
          ((Yw ⟨u.1, hu⟩ t).val (valueIndex2 (kc + 2 * F.p + 1)))) :
    HasFluxBound (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) (kc + 2 * F.p)
      (Set.Icc F.tp F.tf) (D.κ (F.m - 1)) (rhoEnh D cr F.m) (F.G.mass law)
      (fun v t y => toFluxL
        (frontierReadout F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.H F.J
          (D.eps (F.m - 1)) F.η₀ F.aY v t y))
      (C ^ 3 * Cpr * succFrontPrice D F.m F.η₀ F.J F.H θ₁ θ₂ * Ain) := by
  classical
  set FF := FrontierFrame F law kc cr θ₁ θ₂ Y0 Yw yom with hFF
  set aY' := AYret F hGr with haY
  have hret : ∀ u : CompIn F.G'.comps,
      IsRetained F.m F.H F.J u.1 ↔ u.1 ∈ (F.G'.retained F.m F.H F.J).comps := by
    intro u
    simp only [GenStage.retained, GenStage.restrict, Finset.mem_filter]
    exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩
  have hid : ∀ v : CompIn FF.G'.comps, ∀ t ∈ Set.Icc FF.tp FF.tf,
      ∀ᵐ y ∂(volume.restrict AVenhance.unitCube),
        omittedFlux FF.G' FF.k (IsRetained FF.m FF.H FF.J) FF.yom v t y =
          omittedFluxClassical F.P F.seedK F.freshK F.φ₀ FF.G'
            (FF.G'.retained FF.m FF.H FF.J) aY' v t y := by
    intro v t ht
    exact omittedFlux_ae_eq_classical F.P F.seedK F.freshK hφ hφs hφc F.G'
      (F.G'.retained F.m F.H F.J) (IsRetained F.m F.H F.J) hret hkY Yw aY' yom t
      (fun u => hYcl u t ht) (hv t ht) v
  have hT := hasFluxBound_sel FF true C hC hν hE hgrade.1 hgrade.2.1 hgrade.2.2 F.P
    F.seedK F.freshK F.φ₀ aY' hid
  have hL := hasFluxBound_sel FF false C hC hν hE hlength.1 hlength.2.1 hlength.2.2 F.P
    F.seedK F.freshK F.φ₀ aY' hid
  have hsum := hasFluxBound_add' (ι := CompIn F.G.comps) (h := fun v => hr v.1.root)
    (kc + 2 * F.p) (Set.Icc F.tp F.tf) (D.κ (F.m - 1)) (rhoEnh D cr F.m) (F.G.mass law) hν hπ _ _
    _ _ hT hL
  have hfun : (fun v t y => toFluxL
        (frontierReadout F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.H F.J
          (D.eps (F.m - 1)) F.η₀ F.aY v t y)) =
      fun v t y => toFluxL (WithLp.ofLp
        (readoutFlux (S := FF.G.comps) FF.m (D.eps (FF.m - 1)) FF.η (FF.select true)
          (fun v' s y' => omittedFluxClassical F.P F.seedK F.freshK F.φ₀ FF.G'
            (FF.G'.retained FF.m FF.H FF.J) aY' v' s y') v t y)) +
      toFluxL (WithLp.ofLp
        (readoutFlux (S := FF.G.comps) FF.m (D.eps (FF.m - 1)) FF.η (FF.select false)
          (fun v' s y' => omittedFluxClassical F.P F.seedK F.freshK F.φ₀ FF.G'
            (FF.G'.retained FF.m FF.H FF.J) aY' v' s y') v t y)) := by
    funext v t y
    rw [readout_transport F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr
      (F.G'.retained F.m F.H F.J) F.m F.H F.J _ _ hGr F.aY v t y]
    unfold frontierReadout
    rw [readoutFlux_add_sel (S := F.G.comps) (S' := F.G'.comps) F.m (D.eps (F.m - 1)) F.η₀
      (fun c => ¬ IsRetained F.m F.H F.J c) (FF.select true) (FF.select false)]
    · simp only [toFluxL, WithLp.toLp_ofLp]
      rfl
    · intro c hc
      have := not_retained_iff (m := F.m) (H := F.H) (J := F.J) (hrows c hc).1 (hrows c hc).2
      simpa only [FF, FrontierFrame, Preservation.Frontier.Frame.select, ite_true,
        Bool.false_eq_true, ite_false] using this
    · intro c _
      simpa only [FF, FrontierFrame, Preservation.Frontier.Frame.select, ite_true,
        Bool.false_eq_true, ite_false] using select_disjoint (H := F.H) (J := F.J) (m := F.m)
  rw [hfun]
  refine hasFluxBound_mono_Y hsum ?_
  have hn : (0 : ℝ) ≤ C ^ 3 := by positivity
  have h1 : 0 ≤ D.eps (F.m - 1) ^ (F.η₀ / 8 * succSigmaH D.q F.H) := by positivity
  have h2 : 0 ≤ D.eps (F.m - 1) ^ (θ₁ + (F.J : ℝ) * θ₂) := by positivity
  have e1 : FF.exponent true = F.η₀ / 8 * succSigmaH D.q F.H := rfl
  have e2 : FF.exponent false = θ₁ + (F.J : ℝ) * θ₂ := rfl
  calc C ^ 3 * D.eps (FF.m - 1) ^ FF.exponent true * FF.initialNorm +
        C ^ 3 * D.eps (FF.m - 1) ^ FF.exponent false * FF.initialNorm
      = C ^ 3 * (D.eps (F.m - 1) ^ (F.η₀ / 8 * succSigmaH D.q F.H) +
          D.eps (F.m - 1) ^ (θ₁ + (F.J : ℝ) * θ₂)) * FF.initialNorm := by
        have hm : FF.m = F.m := rfl
        rw [e1, e2, hm]; ring
    _ ≤ C ^ 3 * (D.eps (F.m - 1) ^ (F.η₀ / 8 * succSigmaH D.q F.H) +
          D.eps (F.m - 1) ^ (θ₁ + (F.J : ℝ) * θ₂)) * (Cpr * Ain) :=
        mul_le_mul_of_nonneg_left hY0 (mul_nonneg hn (add_nonneg h1 h2))
    _ = _ := by unfold succFrontPrice; ring

end AVRegularity.Construction.Residual.Presentation.Cascade
end
