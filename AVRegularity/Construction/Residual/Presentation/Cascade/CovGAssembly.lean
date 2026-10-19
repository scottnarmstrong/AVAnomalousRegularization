-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.Recon.Edge.Main
import AVRegularity.Applications.Construction.StreamTail
public import AVRegularity.Construction.Residual.Presentation.Cascade.Swap
import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.ConvAssembly
import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfOpen
import AVRegularity.CycleJoint.PlaneHkWindowChartH1
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Construction.Residual.Presentation.Cascade.Budget
public import AVRegularity.Construction.Residual.Presentation.Cascade.CtxFineLift
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.EntryTerminal.Route
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The edge coefficients of a cascade frame on a block** (cascade side of the bill residual).

`edge_block` is the terminal `reconEdge_block` at a frame: for a window
`[t_S, t_S + 2τ''_m] ⊆ [a, b]` the pointwise molecular envelope of the incoming stage `F.G` on
`[a, b]` (the named hypothesis `hpw`, in the form of the seed clause `IsSeedPointwiseMolecular`)
and the preparation chart certificate of the actual family on the window give the sampled
envelope (`preparation_sampled_envelope_of_pointwise_certificate`) and with it a uniform bound and
continuity in space of the edge coefficients of the actual family (`edgeBound_of_sampled_uniform`).

For `c_K ≤ 1` the rescaling factor is `1`, and for a stage without identities the bound is
`0`.  The slots are `K_v = ℓ + D_m (depth - rank v)`, `K_max = ℓ + D_m·depth`. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The slots of the frame are at most `ℓ + D_m·depth`. -/
theorem fK_le (ℓ : ℕ) (v : CompIn F.G.comps) : fK F ℓ v ≤ ℓ + Dm * F.depth := by
  have := descSlots_le F.G.actualFamily F.depth Dm v
  show ℓ + descSlots F.G.actualFamily F.depth Dm v ≤ ℓ + Dm * F.depth
  omega

/-- The block of a time of the window. -/
theorem blockOf {aM tp T s h : ℝ} (hh : 0 < h) (hw : aM + 2 * h ≤ T) (hap : aM ≤ tp)
    (hs : s ∈ Set.Icc tp T) :
    aM ≤ max aM (min (s - h) (T - 2 * h)) ∧ max aM (min (s - h) (T - 2 * h)) + 2 * h ≤ T ∧
      s ∈ Set.Icc (max aM (min (s - h) (T - 2 * h))) (max aM (min (s - h) (T - 2 * h)) + 2 * h) := by
  obtain ⟨hs1, hs2⟩ := hs
  refine ⟨le_max_left _ _, ?_, ?_, ?_⟩
  · have := max_le (a := aM) (b := min (s - h) (T - 2 * h)) (c := T - 2 * h) (by linarith)
      (min_le_right _ _)
    linarith
  · refine max_le_iff.2 ⟨hap.trans hs1, ?_⟩
    linarith [min_le_left (s - h) (T - 2 * h)]
  · rcases le_total (s - h) (T - 2 * h) with h1 | h1
    · rw [min_eq_left h1]
      linarith [le_max_right aM (s - h)]
    · rw [min_eq_right h1]
      linarith [le_max_right aM (T - 2 * h)]

/-- **The edge coefficients of a frame on every block**: a uniform bound for all points of the
plane and continuity in space, at every time of every window `[t_S, t_S + 2τ''_m] ⊆ [a, b]`. -/
theorem edge_block (ℓ : ℕ) (kW : InvConsts) (a b' : ℝ)
    (hqq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hlev : F.G.level = F.m) (hmt : F.m ≤ D.term)
    (hν : 0 < D.κ F.m) (hπ : ∀ v, 0 < F.G.mass law v)
    (hρ0 : 0 < rhoStar D kW.c₀ F.m) (hρε : rhoStar D kW.c₀ F.m ≤ ocEpsilon D.q D.Λ F.m)
    (hεε : ocEpsilon D.q D.Λ F.m ≤ ocEpsilon D.q D.Λ (F.m - 1))
    (hact : ∀ p, (F.G.actual p).1 = nativeChain F.G.level p.1) (hi : 1 ≤ F.G.level)
    (hjl : j₀ ≤ F.G.level) (hpw : IsSeedPointwiseMolecular law kW F.G a b')
    (hKs : ∀ v, fK F ℓ v ≤ kW.Ks) (hJm : ℓ + Dm * F.depth + Dm + 2 ≤ kW.Jm)
    (Cpad Cage : ℝ) (Npad : ℕ) (Cchart : ℕ → ℝ)
    (hchart : ∀ tS : ℝ, IsPreparationChartCertificate D.α D.q D.Λ F.m (D.Φ (F.m - 1))
      (D.hΦ (F.m - 1)) tS (tS + 2 * ocTauPP D.α D.q D.Λ F.m) Cpad Cage Npad
      (ℓ + Dm * F.depth + Dm + 2) Cchart (prepBlock (ocTauPP D.α D.q D.Λ F.m) tS) 3
      F.G.actualFamily) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ tS : ℝ, a ≤ tS → tS + 2 * ocTauPP D.α D.q D.Λ F.m ≤ b' →
      ∀ t ∈ Set.Icc tS (tS + 2 * ocTauPP D.α D.q D.Λ F.m), ∀ v u
        (d : admissibleOrders (fK F ℓ) Dm v u),
        Continuous ((edgeCoefficient F.G.actualFamily (D.κ F.m) (ocEpsilon D.q D.Λ F.m)
          (ocEpsilon D.q D.Λ (F.m - 1)) (fun _ => ()) (fK F ℓ)) v u d t) ∧
        ∀ y, ‖(edgeCoefficient F.G.actualFamily (D.κ F.m) (ocEpsilon D.q D.Λ F.m)
          (ocEpsilon D.q D.Λ (F.m - 1)) (fun _ => ()) (fK F ℓ)) v u d t y‖ ≤ CA := by
  have hkap : D.kap F.G.level = D.κ F.m := by
    rw [hlev]
    unfold OCData.kap
    rw [min_eq_left hmt]
  have hrho : rhoStar D kW.c₀ F.G.level = rhoStar D kW.c₀ F.m := by rw [hlev]
  have hE0 : 0 ≤ ocEpsilon D.q D.Λ (F.m - 1) :=
    (AVRegularity.Scales.epsilon_basic (m := F.m - 1) hqq hΛ).1.le
  have hb0 : ∀ v u, 0 ≤ recordMajorant (F.G.mass law) F.G.fam v u := fun v u =>
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun γ _ =>
      mul_nonneg (norm_nonneg _) (F.G.fam.identity v u γ).record.size_nonneg)
  obtain ⟨Cprep, hCprep, hsamp⟩ :=
    CycleJointProofs.preparation_sampled_envelope_of_pointwise_certificate Dm
      (ℓ + Dm * F.depth) (ℓ + Dm * F.depth + Dm + 2) (ℓ + Dm * F.depth + Dm + 2) le_rfl le_rfl
      kW.Cm Cchart
  have hKmax : ∀ v, fK F ℓ v ≤ ℓ + Dm * F.depth := fK_le F ℓ
  have hCb : ∀ v u, 0 ≤ Cprep * recordMajorant (F.G.mass law) F.G.fam v u := fun v u =>
    mul_nonneg (zero_le_one.trans hCprep) (hb0 v u)
  have hpt : ∀ tS : ℝ, a ≤ tS → tS + 2 * ocTauPP D.α D.q D.Λ F.m ≤ b' →
      IsSampledEnvelope F.G.actualFamily (F.G.mass law) (fK F ℓ) (fun _ => ()) tS
        (tS + 2 * ocTauPP D.α D.q D.Λ F.m) (D.κ F.m) (ocEpsilon D.q D.Λ F.m)
        (ocEpsilon D.q D.Λ (F.m - 1)) (rhoStar D kW.c₀ F.m) Cprep
        (recordMajorant (F.G.mass law) F.G.fam) := fun tS h1 h2 => by
    have hWsub : Set.Icc tS (tS + 2 * ocTauPP D.α D.q D.Λ F.m) ⊆ Set.Icc a b' :=
      fun t ht => ⟨h1.trans ht.1, ht.2.trans h2⟩
    have hP := hpw (fK F ℓ) hKs
    rw [hkap, hrho] at hP
    simp only [hlev] at hP
    have hP' := F.G.isPointwiseMolecularEnvelope_actualFamily hWsub kW.mEnv hact hi hjl hP
    have hP'' := (pointwiseMolecularEnvelope_mono _ _ _ _ _ _ _ _ hE0 hJm (fun _ => le_rfl) hb0 hP')
    exact hsamp D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1)) tS _ Cpad Cage Npad _ 3 _ _ _
      hν hρ0 hρε hεε F.G.actualFamily _ hπ
      (fK F ℓ) hKmax (fun _ => ()) _ hb0 (hchart tS) hP''
  have hCA : 0 ≤ edgeBoundConst (F.G.mass law) (fK F ℓ) (D.κ F.m)
      (rhoStar D kW.c₀ F.m) Cprep (recordMajorant (F.G.mass law) F.G.fam) Dm :=
    Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun d _ => by
      have := hCb v u
      have h2 := hπ u
      have h3 := hπ v
      positivity
  refine ⟨_, hCA, ?_⟩
  intro tS h1 h2 t ht v u d
  obtain ⟨-, hbd⟩ := edgeBound_of_sampled_uniform F.G.actualFamily (F.G.mass law) hπ (fK F ℓ)
    (fun _ => ()) hν hρ0 (hpt tS h1 h2) hCb
  exact ⟨CycleComparison.Reconstruction.edgeCoefficient_continuous_of_sampled F.G.actualFamily
    (F.G.mass law) (fK F ℓ) (fun _ => ()) (hpt tS h1 h2) v u d ht, fun y => hbd t ht v u d y⟩
end

/-! **The drift and edge coefficients at a cascade frame** (cascade side of the bill residual).

`frameReconCoeffAt_of_envelope`: `FrameReconCoeffAt F ℓ` from the facts that a cascade
frame does not carry and that the terminal model reads from its context: the scale facts of the
stream (`IsOCStreamSeq`, admissible `q`, fast profile), the pointwise molecular envelope of the
incoming stage on a window `[a, b]` that contains the window of the frame and the preparation chart
certificate of the actual family on every block (named hypotheses, as in `edge_block`).

* drift: `streamVel (D.Φ m)` is continuous, hence measurable, and bounded by `velBound`
  (terminal `reconCoeff_stream`);
* edge: every time of the window `[t_p, t_f]` lies in a block `[t_S, t_S + 2τ''_m] ⊆ [a, b]`,
  `t_S = max a (min (s - τ'') (b - 2τ''))`, where `edge_block` gives the bound and the
  continuity (the terminal `reconEdge_at`).

The endpoints `s = t_p` (the first block) and `s = t_f` are allowed. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The drift clauses of `FrameReconCoeffAt`: measurability and a uniform bound of
`streamVel (D.Φ m)`. -/
theorem drift' {s : ℝ} (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - D.α) / 2) (hq : IsAdmissibleQ D.α s D.q) (hζ : IsFastProfile D.ζ)
    (h128 : 128 ≤ D.Λ) (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ) :
    ∃ Vb : ℝ, (∀ s' ∈ Set.Ioc F.tp (F.tp + fTobs F), ∀ k,
      AEStronglyMeasurable (fun y => streamVel (D.Φ F.m) s' y k)
        (volume.restrict AVenhance.unitCube)) ∧
    ∀ s' ∈ Set.Ioc F.tp (F.tp + fTobs F), ∀ y k, |streamVel (D.Φ F.m) s' y k| ≤ Vb := by
  refine ⟨AVRegularity.Applications.velBound D.α D.q D.Λ, fun s' _ k => ?_, fun s' _ y k => ?_⟩
  · exact ((continuous_apply k).comp ((D.hΦ F.m).vel_continuous.comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (streamVel (D.Φ F.m) s' y) k).trans
      (AVRegularity.Applications.streamVel_norm_le D.α s hα₀ hα₁ hs₀ hs₁ D.q hq D.ζ hζ D.Λ h128
        D.Φ hseq F.m s' y)

/-- **The coefficient step at a frame**: the drift and the edge coefficients on the window. -/
theorem frameReconCoeffAt_of_envelope {s : ℝ} (ℓ : ℕ) (kW : InvConsts)
    (a b' : ℝ) (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hζ : IsFastProfile D.ζ) (h128 : 128 ≤ D.Λ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (hlev : F.G.level = F.m) (hmt : F.m ≤ D.term)
    (hν : 0 < D.κ F.m) (hπ : ∀ v, 0 < F.G.mass law v)
    (hρ0 : 0 < rhoStar D kW.c₀ F.m) (hρε : rhoStar D kW.c₀ F.m ≤ ocEpsilon D.q D.Λ F.m)
    (hεε : ocEpsilon D.q D.Λ F.m ≤ ocEpsilon D.q D.Λ (F.m - 1))
    (hact : ∀ p, (F.G.actual p).1 = nativeChain F.G.level p.1) (hi : 1 ≤ F.G.level)
    (hjl : j₀ ≤ F.G.level) (hpw : IsSeedPointwiseMolecular law kW F.G a b')
    (hKs : ∀ v, fK F ℓ v ≤ kW.Ks) (hJm : ℓ + Dm * F.depth + Dm + 2 ≤ kW.Jm)
    (Cpad Cage : ℝ) (Npad : ℕ) (Cchart : ℕ → ℝ)
    (hchart : ∀ tS : ℝ, IsPreparationChartCertificate D.α D.q D.Λ F.m (D.Φ (F.m - 1))
      (D.hΦ (F.m - 1)) tS (tS + 2 * ocTauPP D.α D.q D.Λ F.m) Cpad Cage Npad
      (ℓ + Dm * F.depth + Dm + 2) Cchart (prepBlock (ocTauPP D.α D.q D.Λ F.m) tS) 3
      F.G.actualFamily)
    (hap : a ≤ F.tp) (htf : F.tf ≤ b')
    (hwait : a + 2 * ocTauPP D.α D.q D.Λ F.m ≤ b') :
    FrameReconCoeffAt F ℓ := by
  have hqq : 1 < D.q := hq.1
  obtain ⟨Vb, hm, hbd⟩ := drift' F hα₀ hα₁ hs₀ hs₁ hq hζ h128 hseq
  obtain ⟨CA, hCA, hblock⟩ := edge_block F law ℓ kW a b' hqq h128 hlev hmt hν hπ
    hρ0 hρε hεε hact hi hjl hpw hKs hJm Cpad Cage Npad Cchart hchart
  have hh : 0 < ocTauPP D.α D.q D.Λ F.m :=
    AVRegularity.Construction.Stream.ocTauPP_pos (le_trans (by norm_num) h128)
  have hwin : F.tp + fTobs F = F.tf := by simp [fTobs]
  have hblk : ∀ s' ∈ Set.Icc F.tp (F.tp + fTobs F), ∃ tS : ℝ, a ≤ tS ∧
      tS + 2 * ocTauPP D.α D.q D.Λ F.m ≤ b' ∧
      s' ∈ Set.Icc tS (tS + 2 * ocTauPP D.α D.q D.Λ F.m) := fun s' hs' => by
    rw [hwin] at hs'
    obtain ⟨h1, h2, h3⟩ := blockOf (T := b') hh hwait hap
      ⟨hs'.1, hs'.2.trans htf⟩
    exact ⟨_, h1, h2, h3⟩
  refine ⟨Vb, CA, hCA, hm, hbd, ?_, ?_⟩
  · intro s' hs' v u d y
    obtain ⟨tS, h1, h2, h3⟩ := hblk s' hs'
    exact (hblock tS h1 h2 s' h3 v u d).2 y
  · intro s' hs' v u d
    obtain ⟨tS, h1, h2, h3⟩ := hblk s' hs'
    exact ((hblock tS h1 h2 s' h3 v u d).1).aestronglyMeasurable
end

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! Macro swap from classical divergence equality, with letters regularity discharged. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- Numerical and native regularity facts supplied by a cascade context. -/
structure FrameFacts : Prop where
  level : F.G.level = F.m
  menuN : F.N = F.Mn.N
  menuX : F.sX = F.Mn.sX
  menuZ : F.sZ = F.Mn.sZ
  base : 1 ≤ D.Λ
  profile : IsFastProfile D.ζ
  band : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ
  order : 1 ≤ Dm
  smooth : ActualFluxJointSmooth F.G
  xfloor : 1 + Dm ≤ F.Mn.sX
  zfloor : 1 + Dm ≤ F.Mn.sZ

private theorem nativeLift (h : FrameFacts F) :
    ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D F.m k (nativeChain F.m k)
          (F.Mn.lenFactor * liftLength D F.m)
          (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩)))
        F.Mn.sX F.Mn.sZ (D.slotStart F.m k / D.cellScaleSq F.m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m) F.Mn.N F.depth
        (F.CcT k) := by
  rw [← h.menuN, ← h.menuX, ← h.menuZ]
  exact F.lift.1

/-- Native macro regularity, using only the bounded-grade periodic glue. -/
theorem macroReg (h : FrameFacts F) (kc : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (hglue : ∀ t ∈ Set.Icc F.tp F.tf, ∀ v,
      CovTruncGluedPeriodicBounded F.Mn F.G F.m F.depth F.CcT t v) : MacroReg F := by
  intro v t ht
  have ht' : t ∈ Set.Icc F.tp F.tf := by simpa [fTobs] using ht
  have hrep : ∀ w, ContDiff ℝ ((F.Naux - 2 * F.p : ℕ) : ℕ∞) (fun y => F.aRep t y w) ∧
      IsZ2Periodic (fun y => F.aRep t y w) := fun w => by
    obtain ⟨-, hd, hp, -⟩ := (F.lift.2.1 w t ht').2
    exact ⟨by exact_mod_cast hd, hp⟩
  have hord : 1 + Dm + F.Mn.N ≤ F.Naux - 2 * F.p := by rw [← h.menuN]; omega
  have hmc := macroFlux_contDiff F.Mn F.G F.m F.N F.depth h.level h.menuN F.CcT
    h.base h.profile h.band h.order (nativeLift F h) (fun _ => h.smooth) h.xfloor h.zfloor F.aRep t
    (fun w => (hrep w).1.of_le (by exact_mod_cast hord)) v
  have hmp := macroFlux_periodic F.Mn F.G F.m F.N F.depth h.level F.CcT F.aRep t v
    (hglue t ht' v) ((hrep v).1.of_le (by exact_mod_cast (by have := h.order; omega : 2 ≤ F.Naux - 2 * F.p)))
    (fun w => (hrep w).2)
  exact ⟨fun k => (contDiff_pi.1 hmc) k, fun k n x => congrArg (fun z => z k) (hmp n x)⟩

def GluedMeanAt (r : ℕ) : Prop :=
  ∀ a : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root,
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) → (∀ t, IsZ2Periodic (a t)) →
    ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), ∀ (y : Vec 2) (v : CompIn F.G.comps),
      gluedMean (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
        (fun k => F.G.actualFamily.weight (oddSlotOf k))
        (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) F.N r
        (fun k => fLiftData F k) F.CcT
        (fun k => ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
          (ocPulseChartIndex D.α D.q D.Λ F.m k))
        (fun k => ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
          (ocPulseChartIndex D.α D.q D.Λ F.m k)) a t y v =
        -divE (fun z => menuGluedMeanFlux F.Mn F.G F.m {r}
          (if r = 0 then Finset.Icc 2 (F.N + 1) else Finset.Icc 2 (F.N + Dm)) F.CcT a t z v) y

/-- The macro divergence identity from smooth glued mean identities and native jet locality. -/
theorem macroDiv (h : FrameFacts F) (kc : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
    (hlet : FrameReconLettersBody F law kc aC B₀C lamC AD CE Aedge Cstar Θc)
    (hG : ∀ r ∈ Finset.range (F.depth + 1), GluedMeanAt F r) :
    MacroDivConc F AD CE := by
  intro v s hs x0
  have hset := hlet.1
  have hD2 : 2 ≤ F.N + Dm := by
    exact hset.D_ge
  have hN : 1 ≤ kc + (0 + F.depth + 3) * ((F.N + Dm) + 8 * 1 + 4) := by
    have : 0 < (0 + F.depth + 3) * ((F.N + Dm) + 8 * 1 + 4) := by positivity
    omega
  have hs' : s ∈ Set.Icc F.tp (F.tf) := by
    rwa [show F.tp + fTobs F = F.tf by simp [fTobs]] at hs
  have hrep : ∀ w, ContDiff ℝ ((F.Naux - 2 * F.p : ℕ) : ℕ∞) (fun y => F.aRep s y w) ∧
      IsZ2Periodic (fun y => F.aRep s y w) := fun w => by
    obtain ⟨-, hd, hp, -⟩ := (F.lift.2.1 w s hs').2
    exact ⟨by exact_mod_cast hd, hp⟩
  have hcd : ∀ w, ContDiff ℝ ((1 + Dm + F.N : ℕ) : ℕ∞) (fun y => F.aRep s y w) := fun w =>
    (hrep w).1.of_le (by exact_mod_cast (by omega : 1 + Dm + F.N ≤ F.Naux - 2 * F.p))
  have hreal : ∀ w : CompIn F.G.comps, ∃ g : Vec 2 → hr w.1.root,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ IsZ2Periodic g ∧ ∀ (r : ℕ) (I : DerivativeWord2 r),
        r ≤ 1 + Dm + F.N →
        orderedDerivative I g x0 = orderedDerivative I (fun y => F.aRep s y w) x0 :=
    fun w => periodic_jet_realization (1 + Dm + F.N) _ (by exact_mod_cast hcd w) x0
  choose P hPs hPp hPj using hreal
  let a' : ℝ → Vec 2 → ∀ w : CompIn F.G.comps, hr w.1.root := fun _ y w => P w y
  have ha's : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (a' t) := fun t => contDiff_pi.2 hPs
  have ha'p : ∀ t, IsZ2Periodic (a' t) := fun t n y => funext fun w => hPp w n y
  have hjet : ∀ w, SameJetAt (1 + Dm + F.N) x0 (fun y => F.aRep s y w) (P w) :=
    fun w r I hr => (hPj w r I hr).symm
  have hP1 : ContDiff ℝ ((1 + Dm + F.N : ℕ) : ℕ∞) (F.aRep s) := contDiff_pi.2 hcd
  have hP2 : ContDiff ℝ ((1 + Dm + F.N : ℕ) : ℕ∞) (a' s) :=
    (ha's s).of_le (by exact_mod_cast le_top)
  have hJ' : SameJetAt (1 + Dm + F.N) x0 (F.aRep s) (a' s) :=
    sameJet_pi hcd (fun w => (hPs w).of_le (by exact_mod_cast le_top)) hjet
  rw [h.menuN] at hP1 hP2 hJ'
  -- the divergence of the macro flux depends on the jets only
  have hmacro : divE (fun y k => menuMacroFlux F.Mn F.G F.m F.N F.depth F.CcT
      F.aRep v s y k) x0 = divE (fun y k => menuMacroFlux F.Mn F.G F.m F.N
      F.depth F.CcT a' v s y k) x0 := by
    refine divE_eq_of_sameJet fun j => ?_
    have T := macroFlux_triple F.Mn F.G F.m F.N F.depth h.level h.menuN F.CcT
      h.base h.profile h.band h.order (nativeLift F h) h.smooth h.xfloor h.zfloor F.aRep a' s x0 hP1 hP2 hJ' v
    exact sameJet_clm (ContinuousLinearMap.proj j :
      (Fin 2 → hr v.1.root) →L[ℝ] hr v.1.root) T.1 T.2.1 T.2.2
  -- the divergence of the classical letters' flux depends on the jets only
  have hADs : ∀ d, ContDiff ℝ 1 (AD d s) := fun d =>
    (hset.AD_smooth d s hs).of_le (by exact_mod_cast hN)
  have hCEs : ∀ r ∈ Finset.Icc 1 F.depth, ∀ v u d, ContDiff ℝ 1 (CE r v u d s) := fun r hr v u d =>
    (hset.CE_smooth r hr v u d s hs).of_le (by exact_mod_cast hN)
  have hcdD : ∀ w, ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (fun y => F.aRep s y w) := fun w =>
    (hcd w).of_le (by exact_mod_cast (by omega : F.N + Dm ≤ 1 + Dm + F.N))
  have hcdD' : ∀ w, ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (fun y => a' s y w) := fun w =>
    (hPs w).of_le (by exact_mod_cast le_top)
  have hJD : ∀ u, SameJetAt (F.N + Dm) x0 (fun y => F.aRep s y u) (fun y => a' s y u) :=
    fun u => sameJet_mono (by omega) (hjet u)
  have hcl : divE (fun y k => ClassicalDefectFlux (D.κ (F.m - 1)) (F.N + Dm) F.depth AD CE
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) F.aRep v s y k) x0 =
      divE (fun y k => ClassicalDefectFlux (D.κ (F.m - 1)) (F.N + Dm) F.depth AD CE
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) a' v s y k) x0 :=
    divE_eq_of_sameJet fun k => (classicalFlux_triple (D.κ (F.m - 1)) (F.N + Dm)
      F.depth hD2 AD CE (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) F.aRep a' v s x0 hcdD hcdD'
      hJD hADs hCEs k).2.2
  -- the smooth case, grade by grade
  let nsr : ℕ → Finset ℕ := fun r => if r = 0 then Finset.Icc 2 (F.N + 1) else
    Finset.Icc 2 (F.N + Dm)
  let Gr : ℕ → Vec 2 → Fin 2 → hr v.1.root := fun r y =>
    menuGluedMeanFlux F.Mn F.G F.m {r} (nsr r) F.CcT a' s y v
  let CG : ℕ → Vec 2 → Fin 2 → hr v.1.root := fun r y k =>
    classicalGradeFlux (F.N + Dm) r AD CE (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m))
      a' v s y k
  let Q : Vec 2 → Fin 2 → hr v.1.root := fun y j =>
    -(D.κ (F.m - 1)) • gradE (fun y' => a' s y' v) y j
  have e1 : (fun y k => menuMacroFlux F.Mn F.G F.m F.N F.depth F.CcT a' v s y k)
      = fun y k => Q y k + ∑ r ∈ Finset.range (F.depth + 1), Gr r y k := by
    funext y k
    rw [macroFlux_decomp]
    simp [Q, Gr, nsr, Pi.add_apply, Finset.sum_apply]
  have e2 : (fun y k => ClassicalDefectFlux (D.κ (F.m - 1)) (F.N + Dm) F.depth AD CE
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) a' v s y k) =
      fun y k => Q y k + ∑ r ∈ Finset.range (F.depth + 1), CG r y k := by
    funext y k
    rw [classicalFlux_decomp]
    rfl
  have hQ : ∀ j, DifferentiableAt ℝ (fun y => Q y j) x0 := fun j =>
    ((gradE_contDiff 1 ((hcdD' v).of_le (by exact_mod_cast (by omega :
      1 + 1 ≤ F.N + Dm))) j).const_smul _).differentiable (by simp) |>.differentiableAt
  have hGd : ∀ r ∈ Finset.range (F.depth + 1), ∀ j, DifferentiableAt ℝ (fun y => Gr r y j) x0 := by
    intro r hr j
    have T := gluedMeanFlux_triple_m F.Mn F.G F.m F.depth h.level F.CcT h.base
      h.profile h.band h.order (nativeLift F h) 1 h.xfloor h.zfloor {r} (nsr r)
      (fun r' hr' => by rw [Finset.mem_singleton] at hr'; have := Finset.mem_range.mp hr; omega)
      (fun _ => h.smooth) a' a' s x0 hP2 hP2 (fun _ _ _ => rfl) v
    exact (((contDiff_pi.1 T.1) j).differentiable (by simp)) x0
  have hCd : ∀ r ∈ Finset.range (F.depth + 1), ∀ j, DifferentiableAt ℝ (fun y => CG r y j) x0 := by
    intro r hr j
    have := classicalGrade_contDiff (F.N + Dm) hD2 r AD CE
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) a' v s hcdD'
      (fun hr0 d => hADs d)
      (fun hr0 v u d => hCEs r (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hr0,
        by have := Finset.mem_range.mp hr; omega⟩) v u d) j
    exact (this.differentiable (by simp)) x0
  have hsum : ∀ r ∈ Finset.range (F.depth + 1), divE (Gr r) x0 = divE (CG r) x0 := by
    intro r hr
    have g1 := hG r hr a' ha's ha'p s hs x0 v
    have g2 := hlet.2 r hr a' ha's ha'p s hs x0 v
    exact neg_injective (g1.symm.trans g2)
  have hsm : divE (fun y k => menuMacroFlux F.Mn F.G F.m F.N F.depth F.CcT a'
      v s y k) x0 = divE (fun y k => ClassicalDefectFlux (D.κ (F.m - 1)) (F.N + Dm) F.depth
      AD CE (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) a' v s y k) x0 := by
    rw [e1, e2, divE_add _ _ x0 hQ (fun j => DifferentiableAt.fun_sum fun r hr =>
      hGd r hr j), divE_add _ _ x0 hQ (fun j => DifferentiableAt.fun_sum fun r hr =>
      hCd r hr j), divE_sum _ _ x0 hGd, divE_sum _ _ x0 hCd]
    exact congrArg _ (Finset.sum_congr rfl hsum)
  exact hmacro.trans (hsm.trans hcl.symm)

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The native facts of the covariance leaf at every context** (cascade side of the bill
residual).

The bill residual uses three facts of the lifted field of a frame that the covariance leaf
produces: the coarse equation of `P_pZ` (`F.macroWeak`, the input of the coarse reconstruction), the
joint measurability of `F.uh` on the window (the input of the lift step of the fine tail and of the fine tail), and the
classical regularity of `F.uh` (the input of the comparison clauses). All three come from the native
representatives `NativeRepresentatives F`.

* `succPrefix_nativeInput`: in the common prefix form, at every context of level `≥ m_*` and at
  the frame of every lifted field with classical representatives, a native input
  `NativeInput F` (the proved `cascadeNativeInputsProduction`) and the readout equation
  `F.cascadeReadoutWeak` (the proved `retainedReadoutWeakEquation`).
* `frame_macroWeak_native`, `frame_liftedMeas`, `frame_liftedReg`: the three facts at a
  frame of the cascade menu from the native representatives (and, for the first, the readout
  equation; the temporal product rule is `temporal_product`).
* `succPrefix_nativeFacts_of_native`: the three facts at every context, given the input statement
  `NativeTemporalRepresentativesStatement` of the covariance leaf (the other ingredients are
  proved: `readoutStrongEquation`, `covarianceMeanReduction`, `macroWeakFromStrong`).

For an empty component family every clause is about an empty product; `t_p = t_f` is allowed. -/

/-! ### At a frame -/

section Frame

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The coarse equation of `P_pZ` at a frame of the cascade menu** from the native
representatives and the readout equation alone: the temporal product rule is
`temporal_product`, whose cell-scale hypothesis is the clause `clock_nonzero` of the native
regularity. -/
theorem frame_macroWeak_native (F : Frame D hr Dm b j₀) (hanchor : F.Mn.anchor = 0)
    (hlength : F.Mn.lenFactor = 1) (hNative : NativeRepresentatives F)
    (hread : F.cascadeReadoutWeak) : F.macroWeak := by
  have hr' : F.readoutWeak := by
    unfold Frame.readoutWeak
    rw [frame_readFlux_cascade F hanchor hlength]
    exact hread
  obtain ⟨dZ, dRep, dUh, hreg, _hglue⟩ := hNative
  have hAdj := frame_covarianceAdjoints F hreg.covarianceSymmetric
  have hEq := frame_prepared_eq F dZ dRep dUh hreg
  have hR := readoutStrongEquation F dZ dRep dUh hreg hAdj hr'
  have hT := temporal_product F hreg hreg.clock_nonzero hEq
  have hM := covarianceMeanReduction F dZ dRep dUh hreg hT hR
  exact macroWeakFromStrong F dZ dRep dUh hreg hM

/-- **The lifted classical field is jointly measurable on the window** (native representatives,
`Regularity.lifted`). -/
theorem frame_liftedMeas (F : Frame D hr Dm b j₀) (hNative : NativeRepresentatives F) :
    ∀ v : CompIn F.G.comps, Measurable
      (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc F.tp F.tf} => F.uh z.1.1 z.1.2 v) := by
  obtain ⟨dZ, dRep, dUh, hreg, -⟩ := hNative
  exact fun v => (hreg.lifted.field v).measurable

/-- **The lifted classical field is `C^{D_m − 1}` and periodic at every time of the window**
(native representatives, `Regularity.lifted`). -/
theorem frame_liftedReg (F : Frame D hr Dm b j₀) (hNative : NativeRepresentatives F) :
    ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((Dm - 1 : ℕ) : ℕ∞)
          (fun x => menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep t x v) ∧
        IsZ2Periodic (fun x => menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep t x v) := by
  obtain ⟨dZ, dRep, dUh, hreg, -⟩ := hNative
  intro v t ht
  have h := hreg.lifted.field v
  have h1 : ContDiff ℝ ((Dm + 4 - 2 : ℕ) : ℕ∞) (fun x => F.uh t x v) := h.smooth t ht
  exact ⟨h1.of_le (by exact_mod_cast (by omega : Dm - 1 ≤ Dm + 4 - 2)), h.periodic t ht⟩

end Frame

/-! ### At every context -/

/-- **The three native facts at every context of level `≥ m_*`**, at the frame of every lifted
field with classical representatives: the coarse equation of `P_pZ`, the joint measurability of
the lifted classical field on the window, and its regularity `C^{D_m − 1}` and periodicity at
every time of the window. -/
def NativeFactsCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      (c.frame CcT PZ aRep û hlift aZ aY hZ hY).macroWeak ∧
      (∀ v : CompIn c.G.comps, Measurable
        (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc c.tp c.tf} =>
          (c.frame CcT PZ aRep û hlift aZ aY hZ hY).uh z.1.1 z.1.2 v)) ∧
      (∀ v, ∀ t ∈ Set.Icc c.tp c.tf,
        ContDiff ℝ ((succSchedD D₀ N p (H + 1) - 1 : ℕ) : ℕ∞)
            (fun x => (c.frame CcT PZ aRep û hlift aZ aY hZ hY).uh t x v) ∧
          IsZ2Periodic (fun x => (c.frame CcT PZ aRep û hlift aZ aY hZ hY).uh t x v))

/-- The native input at every context (`cascadeNativeInputsProduction`). -/
theorem succPrefix_nativeInputOnly (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
          [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
          [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
          (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
            CI Cw j₀ CQ Cpr Q T₀ hr), x ≤ c.m →
          ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
            (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
            (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
            (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
            (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H)
              sX sZ (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
            (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
            (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
            (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
              (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
              (fun x => aZ t x v) Naux)
            (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
              IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
            Nonempty (NativeInput (c.frame CcT PZ aRep û hlift aZ aY hZ hY))) := by
  obtain ⟨Λ₀, h128, h⟩ := cascadeNativeInputsProduction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine SuccPrefix.of_tail (⟨Λ₀, h128, h⟩ : SuccPrefix₀ α s q _) ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ hfacts htail CQ Cpr
  obtain ⟨mStar, hd⟩ := htail CQ Cpr
  refine ⟨mStar, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY
  exact hd c.D c.hα c.hq c.hΛ c.hζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw
    c.seedK c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hmn c.hnM c.tA c.s₀ c.htA
    c.hs₀ c.htf c.hT₀ c.G c.G' c.hcascade c.hlevel c.hinv c.hactual c.tp c.Preg c.hprep c.f
    c.Ain c.hf c.Y0 c.Y c.Yw c.Yk c.htrace c.hsol CcT PZ aRep û hlift aZ aY hZ hY

/-- The readout equation at every context (`retainedReadoutWeakEquation`). -/
theorem succPrefix_readoutWeak (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
          [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
          [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
          (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
            CI Cw j₀ CQ Cpr Q T₀ hr), x ≤ c.m →
          ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
            (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
            (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
            (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
            (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H)
              sX sZ (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
            (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
            (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
            (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
              (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
              (fun x => aZ t x v) Naux)
            (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
              IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
            (c.frame CcT PZ aRep û hlift aZ aY hZ hY).cascadeReadoutWeak) := by
  obtain ⟨Λ₀, h128, h⟩ := retainedReadoutWeakEquation hα₀ hα₁ hs₀ hs₁ hq hζ
  refine SuccPrefix.of_tail (⟨Λ₀, h128, h⟩ : SuccPrefix₀ α s q _) ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ hfacts htail CQ Cpr
  obtain ⟨mStar, hd⟩ := htail CQ Cpr
  refine ⟨mStar, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY
  exact hd c.D c.hα c.hq c.hΛ c.hζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw
    c.seedK c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hmn c.hnM c.tA c.s₀ c.htA
    c.hs₀ c.htf c.hT₀ c.G c.G' c.hcascade c.hlevel c.hinv c.hactual c.tp c.Preg c.hprep c.f
    c.Ain c.hf c.Y0 c.Y c.Yw c.Yk c.htrace c.hsol CcT PZ aRep û hlift aZ aY hZ hY

/-- **The three native facts at every context from the native representatives alone**
(the temporal product rule is `temporal_product`); the constant is the level `m_*`. -/
theorem succPrefix_nativeFacts_of_native (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hNat : NativeTemporalRepresentativesStatement) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        NativeFactsCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ x) := by
  have h1 := succPrefix_nativeInputOnly α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h2 := succPrefix_readoutWeak α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine (h1.and h2).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  refine ⟨max x.1 x.2, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY
  have hm1 : x.1 ≤ c.m := le_trans (le_max_left _ _) hm
  have hm2 : x.2 ≤ c.m := le_trans (le_max_right _ _) hm
  obtain ⟨I⟩ := hx.1 c hm1 CcT PZ aRep û hlift aZ aY hZ hY
  have hN := hNat (c.frame CcT PZ aRep û hlift aZ aY hZ hY) I
  exact ⟨frame_macroWeak_native (c.frame CcT PZ aRep û hlift aZ aY hZ hY) rfl rfl hN
      (hx.2 c hm2 CcT PZ aRep û hlift aZ aY hZ hY),
    frame_liftedMeas (c.frame CcT PZ aRep û hlift aZ aY hZ hY) hN,
    frame_liftedReg (c.frame CcT PZ aRep û hlift aZ aY hZ hY) hN⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
section
section
/-! **The energy step of the window at every context** (cascade side of the bill
residual, the discharge of `frameReconEnergyAt_of_fullLift`).

`succPrefix_reconEnergy`: in the common prefix form, constants `(C_s, m_*)` with `0 ≤ C_s` such
that at every context of level `≥ m_*`, at the frame of every lifted field with classical
representatives, `FrameReconEnergyAt F law A_cl k_c 0 hW C_s A_in` at the coarse order
`k_c = wKcFloor D_m r_H N A_cl 0` of the window: the hypothesis `hR6a` of `frameReconAt_of_steps`.

Inputs: the full-lift bound at the order `k = k_c + D_m + 1` (`succPrefix_fullLift`; the order
fits by the order floor), the size of the covariance primitive at the slow length
(`succPrefix_covSize` at the radius factor `1`: `rhoEnh D 1 m` is the slow length), the retained
pair and the continuity of `Y` from the solution clause of the context.

The case `t_p = t_f` is allowed (no strictness), and so is `A_in = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- The coarse order of the window of a cascade passage. -/
abbrev succKc (r₀ D₀ H J N p Acl : ℕ) : ℕ :=
  wKcFloor (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0

/-- **The window energy step at every context of level `≥ m_*`**, with the constant `C_s`. -/
def ReconEnergyCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl : ℕ) (Cs : ℝ) (mStar : ℕ) :
    Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux)
      (hW : succKc r₀ D₀ H J N p Acl + 1 + (N + succSchedD D₀ N p (H + 1)) ≤ Naux - 2 * p),
      FrameReconEnergyAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law Acl
        (succKc r₀ D₀ H J N p Acl) 0 hW Cs c.Ain

/-- **The window energy step in the common prefix form**; the constants are `(C_s, m_*)`. -/
theorem succPrefix_reconEnergy (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        0 ≤ x.1 ∧
        ReconEnergyCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ Acl x.1 x.2) := by
  have h1 := succPrefix_fullLift α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun r₀ D₀ H J N p _ _ _ _ Acl _ _ _ _ _ _ =>
      succKc r₀ D₀ H J N p Acl + succSchedD D₀ N p (H + 1) + 1)
  have h2 := succPrefix_covSize α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ (fun _ _ => 1)
    (fun _ _ _ _ => one_pos)
  refine (h1.and h2).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨hfl, hcs⟩ := hx
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hcr : 0 < kI.cr := by rw [hkI.2.1]; exact hfacts.hcr
  have hcr1 : kI.cr ≤ 1 := by rw [hkI.2.1]; exact hfacts.hcr_le
  have hD2 : 2 ≤ succSchedD D₀ N p (H + 1) :=
    Construction.Preservation.Buffer.preparation_schedule_order_ge_two D₀ N p H
  have hN1 : 1 ≤ N := le_trans (by norm_num) (succSchedule_two_le_N hfacts.sched)
  have hA1 : 1 ≤ Acl :=
    succSchedule_one_le_Acl hα₁ (ocDelta_pos_of_admissible hα₀ hq) hfacts.sched
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  refine ⟨(max (CovCost (succKc r₀ D₀ H J N p Acl + (N + succSchedD D₀ N p (H + 1)) + 2 * p)
      p * (kI.cr⁻¹) ^ (succKc r₀ D₀ H J N p Acl + succSchedD D₀ N p (H + 1) + 1 + N + 2 * p) *
      x.1.1) 0, max x.1.2 x.2), le_max_right _ _, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY hW
  have hm1 : x.1.2 ≤ c.m := le_trans (le_max_left _ _) hm
  have hm2 : x.2 ≤ c.m := le_trans (le_max_right _ _) hm
  have hk : succKc r₀ D₀ H J N p Acl + succSchedD D₀ N p (H + 1) + 1 + N + 2 * p ≤ Naux := by
    omega
  have hρ : 0 < fRho (c.frame CcT PZ aRep û hlift aZ aY hZ hY) :=
    Real.sqrt_pos.2 (mul_pos (c.kappa_pred_pos hΛ1 hζ)
      (Construction.Stream.ocTauPP_pos (le_trans (by norm_num) (c.lambda_ge hfacts.hΛ))))
  have hS := hcs c hm2 CcT PZ aRep û hlift aZ aY hZ hY
  have e : rhoEnh c.D 1 c.m = fRho (c.frame CcT PZ aRep û hlift aZ aY hZ hY) := one_mul _
  rw [e] at hS
  have hE := frameReconEnergyAt_of_fullLift (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law Acl
    (succKc r₀ D₀ H J N p Acl) 0 hW hk le_rfl
    (frameReconOrders (ℓ := 0) 0 0 hD2 hN1 hA1 le_rfl).2 (hfl hk c hm1)
    (retainedPair_of_isRegSolution (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.hsol)
    hcr hcr1 (c.mass_pos hq.1 hfacts.hΛ) hρ hS c.hsol.1
  have hAin : 0 ≤ c.Ain := le_trans (Real.sqrt_nonneg _) c.hf
  exact ⟨hE.1, hE.2.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hAin))⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The gradient form of the covariance truncation at every context** (cascade side of
the bill residual, the discharge of the `covGradForm_at_frame`).

`succPrefix_covGrad`: in the common prefix form, constants `(C, m_*)` such that at every context
of level `≥ m_*`, at the frame of every lifted field with classical representatives,

    CovGradForm F.Mn G m p k_c aZ π t_p t_f (rhoEnh D k_I.c_r m) (C·ω^p·A_in)

at the coarse order `k_c = succKc` of the window, `ω = frameOmega F k_I.c_r`: the third form of
the covariance truncation bound. Inputs: the full-lift bound at the order `k_c + D_m + 1`
(`succPrefix_fullLift`, with its constant replaced by its positive part: the clauses are
monotone in the constant), the retained pair of the solution clause, the masses.

The case `p = 0` is excluded by the schedule; `A_in = 0` and `t_p = t_f` are allowed. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The full-lift clauses are monotone in their constant (for `A_in ≥ 0`). -/
theorem billCtx_fullLiftClauses_mono {law : BirthLaw} {G Gr : GenStage D hr Dm b j₀}
    {m p Naux N depth sX sZ k : ℕ} {hk : k + N + 2 * p ≤ Naux} {η₀ c₀ cr tp tf Ck Ck' Ain : ℝ}
    {Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root)}
    {Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root)}
    (hC : Ck ≤ Ck') (hAin : 0 ≤ Ain)
    (h : FullLiftClauses law G Gr m p Naux N depth sX sZ k hk η₀ c₀ cr tp tf Ck Ain Y Yw) :
    FullLiftClauses law G Gr m p Naux N depth sX sZ k hk η₀ c₀ cr tp tf Ck' Ain Y Yw := by
  refine ⟨h.1, fun CcT PZ aRep û ŵ hl w hw => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 CcT PZ aRep û ŵ hl w hw
  exact ⟨h1.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC) _),
    h2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC hAin))⟩

/-- **The covariance gradient form at every context of level `≥ m_*`**, from the full-lift clauses at an order `k`. -/
def CovGradRawCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (kc k : ℕ) (Cn : ℝ) (mStar : ℕ) :
    Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux)
      (hk : k + N + 2 * p ≤ Naux), kc + 1 ≤ k + N → ∀ Ck : ℝ, 0 ≤ Ck →
      FullLiftClauses c.law c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ k
        hk (succEta0 α q s) kI.c₀ kI.cr c.tp c.tf Ck c.Ain c.Y c.Yw →
      CovGradForm (c.frame CcT PZ aRep û hlift aZ aY hZ hY).Mn c.G c.m p kc aZ
        (c.G.mass c.law) c.tp c.tf (rhoEnh c.D kI.cr c.m)
        ((((p.factorial : ℝ)⁻¹ * (((kc + 2 * p : ℕ) : ℝ) ^ (2 * p)) * Cn * Ck) *
          frameOmega (c.frame CcT PZ aRep û hlift aZ aY hZ hY) kI.cr ^ p * c.Ain))

/-- **The covariance gradient form at every context of level `≥ m_*`**, at the coarse order of the window, with the
constant `C`. -/
def CovGradCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl : ℕ) (C : ℝ) (mStar : ℕ) :
    Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      CovGradForm (c.frame CcT PZ aRep û hlift aZ aY hZ hY).Mn c.G c.m p
        (succKc r₀ D₀ H J N p Acl) aZ (c.G.mass c.law) c.tp c.tf (rhoEnh c.D kI.cr c.m)
        (C * frameOmega (c.frame CcT PZ aRep û hlift aZ aY hZ hY) kI.cr ^ p * c.Ain)

/-- The covariance gradient form in the common prefix form, before the full-lift clauses are supplied; the
constants are `(C_n, m_*)` with `0 ≤ C_n`. -/
theorem succPrefix_covGradRaw (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (kcf kf : SuccOrder) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
          σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        0 ≤ x.1 ∧
        CovGradRawCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀
          (kcf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ)
          (kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ) x.1 x.2) := by
  refine SuccPrefix.of_scale (covGradForm_at_frame hα₀ hα₁ hs₀ hs₁ hq hζ) ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ hfacts htail CQ Cpr
  obtain ⟨Cn, hCn, h⟩ := htail
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  obtain ⟨mStar, -, h⟩ := h kI.cr (by rw [hkI.2.1]; exact hfacts.hcr)
  refine ⟨(Cn, mStar), hCn, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY hk hkc Ck hCk cl
  exact h c.D c.M c.hα c.hq c.hΛ c.hζ c.hband (c.frame CcT PZ aRep û hlift aZ aY hZ hY) rfl hm
    c.m_le_M c.law (c.mass_pos hq.1 hfacts.hΛ) hk hkc cl
    (retainedPair_of_isRegSolution (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.hsol) hCk
    (le_trans (Real.sqrt_nonneg _) c.hf)

/-- **The covariance gradient form in the common prefix form**; the constants are `(C, m_*)`. -/
theorem succPrefix_covGrad (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        CovGradCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI
          Cw j₀ CQ Cpr Q T₀ Acl x.1 x.2) := by
  have h1 := succPrefix_fullLift α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun r₀ D₀ H J N p _ _ _ _ Acl _ _ _ _ _ _ =>
      succKc r₀ D₀ H J N p Acl + succSchedD D₀ N p (H + 1) + 1)
  have h2 := succPrefix_covGradRaw α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun r₀ D₀ H J N p _ _ _ _ Acl _ _ _ _ _ _ => succKc r₀ D₀ H J N p Acl)
    (fun r₀ D₀ H J N p _ _ _ _ Acl _ _ _ _ _ _ =>
      succKc r₀ D₀ H J N p Acl + succSchedD D₀ N p (H + 1) + 1)
  refine (h1.and h2).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨hfl, -, hraw⟩ := hx
  have hW : succKc r₀ D₀ H J N p Acl + 1 + (N + succSchedD D₀ N p (H + 1)) ≤ Naux - 2 * p :=
    (windowOrders_of_succReconFloor hfacts.recon).1
  have hk : succKc r₀ D₀ H J N p Acl + succSchedD D₀ N p (H + 1) + 1 + N + 2 * p ≤ Naux := by
    omega
  refine ⟨((p.factorial : ℝ)⁻¹ * (((succKc r₀ D₀ H J N p Acl + 2 * p : ℕ) : ℝ) ^ (2 * p)) *
    x.2.1 * max x.1.1 0, max x.1.2 x.2.2), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY
  have hAin : 0 ≤ c.Ain := le_trans (Real.sqrt_nonneg _) c.hf
  exact hraw c (le_trans (le_max_right _ _) hm) CcT PZ aRep û hlift aZ aY hZ hY hk (by omega) _
    (le_max_right _ _)
    (billCtx_fullLiftClauses_mono (le_max_left _ _) hAin
      (hfl hk c (le_trans (le_max_left _ _) hm)))

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
section
/-! **The frontier inner flux at every context: the statement** (cascade side of the bill residual).

`FrontierInnerCtxAt`: at every context of level `≥ m_*`, at the frame of every lifted field of
the context with classical representatives, the inner flux of the response boundary has the form
asked by `frameFrontier_of_forms` (`FrontierInnerForm`) at the coarse
order `k_c = succKc` of the window and the radius `ρ_enh = rhoEnh D k_I.c_r m`, with the bound
`C·(E^{ιΣ_H} + E^{θ₁+Jθ₂})·A_in` (`succFrontPrice`, the letters `θ₁ = succTheta1`,
`θ₂ = succTheta2` of the bill).

`FrontierInnerPrefixStatement`: the same in the common prefix form, with a constant `C ≥ 0` and
a level `m_*` chosen after `C_Q, C_pr`. It is the frontier inner flux part of the bill residual; its proof is
the assembly of proved parts (the `frontierInner_bound` and `frontierSmooth`, the
`retainedData`, `succPrefix_regClause`, the weighted-norm bound of `Y0`, the frontier
productions at both grades).

For a stage without omitted rows the readout is `0`; `A_in = 0`, `J = 0` and
`t_p = t_f` are allowed. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- **The frontier inner flux at every context of level `≥ m_*`**: `FrontierInnerForm` at the frame of every lifted
field with classical representatives, at the coarse order `succKc` and the constant `C`. -/
def FrontierInnerCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl : ℕ) (C : ℝ) (mStar : ℕ) :
    Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      FrontierInnerForm (c.frame CcT PZ aRep û hlift aZ aY hZ hY).P c.seedK c.freshK φ₀ c.G c.G'
        (c.G'.retained c.m H J) c.m p H J (succKc r₀ D₀ H J N p Acl) (c.D.eps (c.m - 1))
        (succEta0 α q s) aY (c.G.mass c.law) c.tp c.tf (rhoEnh c.D kI.cr c.m)
        (C * succFrontPrice c.D c.m (succEta0 α q s) J H
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)) *
          c.Ain)

/-- **The frontier inner flux in the common prefix form**: a constant `C ≥ 0` and a level `m_*`. -/
def FrontierInnerPrefixStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  SuccPrefix α s q (X := ℝ × ℕ)
    (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX sZ
        σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
      0 ≤ x.1 ∧ FrontierInnerCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad
        sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Acl x.1 x.2)

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! The covariance G form: the exact bill covariance G form from its four named flux pieces.
Part 1 is spatial regularity and periodicity; parts 2, 3, 4 are the commutator,
diagonal and inherited mean flux bounds. Part 0 is the requested CovGForm.
The common context interface retains the prefix and the quiet margin.
For `p = 0` only the commutator is removed; empty components and a zero datum
have zero action, and a point window has zero integrated mass. Constants precede data. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The three exact physical terms of the pre-truncation flux. -/
def CovGTerm (F : Frame D hr Dm b j₀) (i : Fin 3) :=
  if i = 0 then gCommTerm F.Mn F.G F.m F.p F.aZ
  else if i = 1 then gDiagTerm F.Mn F.G F.m F.N F.p F.CcT F.aZ
  else gMeanTerm F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ

/-- A realized term bound, at the exact output order and the bill radius. -/
def CovGTermAt (i : Fin 3) (F : Frame D hr Dm b j₀) (law : BirthLaw)
    (cr : ℝ) (kc : ℕ) (Y : ℝ) : Prop :=
  HasFluxBound (h := fun v : CompIn F.G.comps => hr v.1.root) (kc + 4 * F.p)
    (Set.Icc F.tp F.tf) (D.κ (F.m - 1)) (rhoEnh D cr F.m) (F.G.mass law)
    (fun v t y => toFluxL (CovGTerm F i v t y)) Y

/-- The regularity part and the three exact term bounds imply the desired form. -/
theorem CovGForm_of_terms (F : Frame D hr Dm b j₀) (law : BirthLaw) (cr : ℝ) (kc : ℕ)
    (Yc Yd Ym : ℝ) (hν : 0 < D.κ (F.m - 1)) (hπ : ∀ v, 0 < F.G.mass law v)
    (hreg : ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((kc + 4 * F.p : ℕ) : ℕ∞)
        (fun y => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y) ∧
      IsZ2Periodic (fun y => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y))
    (hc : CovGTermAt 0 F law cr kc Yc) (hd : CovGTermAt 1 F law cr kc Yd)
    (hm : CovGTermAt 2 F law cr kc Ym) :
    CovGForm F.Mn F.G F.m F.N F.p F.depth kc F.CcT F.aZ (F.G.mass law)
      F.tp F.tf (rhoEnh D cr F.m) ((Yc + Yd) + Ym) := by
  have h12 := covTruncSub _ _ _ _ _ hν hπ _ _ _ _ hc hd
  have h123 := covTruncSub _ _ _ _ _ hν hπ _ _ _ _ h12 hm
  refine ⟨hreg, ?_⟩
  have he : (fun (v : CompIn F.G.comps) (t : ℝ) (y : Vec 2) => toFluxL
      (menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y)) =
      fun v t y => (toFluxL (CovGTerm F 0 v t y) -
        toFluxL (CovGTerm F 1 v t y)) - toFluxL (CovGTerm F 2 v t y) := by
    funext v t y
    rw [menuGFlux_eq_terms]
    simp [CovGTerm, toFluxL, WithLp.toLp_sub]
  rw [he]
  exact h123

/-- Part 0 is the conclusion; 1 is regularity; 2-4 are the three actual flux pieces. -/
def CovGFrameAt (part : Fin 5) (F : Frame D hr Dm b j₀) (law : BirthLaw)
    (cr : ℝ) (kc : ℕ) (C Ain : ℝ) : Prop :=
  if part = 0 then
    CovGForm F.Mn F.G F.m F.N F.p F.depth kc F.CcT F.aZ (F.G.mass law)
      F.tp F.tf (rhoEnh D cr F.m) (C * Ain)
  else if part = 1 then
    ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((kc + 4 * F.p : ℕ) : ℕ∞)
        (fun y => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y) ∧
      IsZ2Periodic (fun y => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y)
  else if part = 2 then CovGTermAt 0 F law cr kc (C * Ain)
  else if part = 3 then CovGTermAt 1 F law cr kc (C * Ain)
  else CovGTermAt 2 F law cr kc (C * Ain)

/-- Every lifted field at a bill context, with the common quiet margin. -/
def CovGContextAt (part : Fin 5) (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ) (kI : InvConsts)
    (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl : ℕ) (C : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆
      ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      CovGFrameAt part (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law kI.cr
        (succKc r₀ D₀ H J N p Acl) C c.Ain

/-- A named ingredient in the exact successor prefix, constants before data. -/
def CovGPartStatement (α s q : ℝ) (ζ : ℝ → ℝ) (part : Fin 5) : Prop :=
  SuccPrefix α s q (X := ℝ × ℕ)
    (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad
        sX sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
      CovGContextAt part α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad
        sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Acl x.1 x.2)

/-- The covariance G form assembly at every context, from regularity, commutator, diagonal and mean. -/
theorem succPrefix_covGForm_of_ingredients (α s q : ℝ) (ζ : ℝ → ℝ)
    (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ)
    (hreg : CovGPartStatement α s q ζ 1) (hcomm : CovGPartStatement α s q ζ 2)
    (hdiag : CovGPartStatement α s q ζ 3) (hmean : CovGPartStatement α s q ζ 4) :
    CovGPartStatement α s q ζ 0 := by
  refine ((hreg.and hcomm).and (hdiag.and hmean)).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  refine ⟨(x.1.2.1 + x.2.1.1 + x.2.2.1, max (max x.1.1.2 x.1.2.2) (max x.2.1.2 x.2.2.2)), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  have hm1 : x.1.1.2 ≤ c.m := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hm2 : x.1.2.2 ≤ c.m := (le_max_right _ _).trans ((le_max_left _ _).trans hm)
  have hm3 : x.2.1.2 ≤ c.m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm4 : x.2.2.2 ≤ c.m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have h1 := hx.1.1 c hm1 hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  have h2 := hx.1.2 c hm2 hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  have h3 := hx.2.1 c hm3 hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  have h4 := hx.2.2 c hm4 hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  simp only [CovGFrameAt, Fin.isValue, ↓reduceIte] at h1 h2 h3 h4 ⊢
  have hb := CovGForm_of_terms (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law kI.cr
    (succKc r₀ D₀ H J N p Acl) _ _ _
    (c.kappa_pred_pos (le_trans (by norm_num) hfacts.hΛ) hζ)
    (c.mass_pos hq.1 hfacts.hΛ) h1 h2 h3 h4
  refine ⟨hb.1, hasFluxBound_mono_Y hb.2 (le_of_eq ?_)⟩
  ring

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
end
