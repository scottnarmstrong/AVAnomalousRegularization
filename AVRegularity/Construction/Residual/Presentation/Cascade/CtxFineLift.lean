-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Cascade.ReconCoarseParts
import AVRegularity.EntryTerminal.Ingredients.Recon.Conv.Conv
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.CycleComparison.Reconstruction.Continuity
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.EntryTerminal.Ingredients.QuietEntrance.ZeroAssembly
import AVRegularity.Proofs.Results.Construction.SuccessorResidualIdentities
import AVRegularity.Construction.Preservation.Assembly.PreparationJointOfInputs
import AVRegularity.Construction.Preservation.Assembly.FullLiftFromInputs
import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.GluedClosed
import AVRegularity.EntryTerminal.Ingredients.Recon.Energy.Chain
import AVRegularity.Families.TorusCompatible.WeakStage

section
section
section
/-! **Conv at a cascade frame** (cascade side of the bill residual).

`frameReconConvAt_of_natural`: `FrameReconConvAt F law ℓ ρs` from the facts that make
the incoming stage of the frame the natural one at its level: `G.level = m`, `D.term = m`, the
weights are the cutoffs, the menu has `lenFactor = 1`. It is the terminal `reconConv_at` at a
frame: the glued lift is the menu's lifted
field (`stage_gluedLift_eq_menuLiftedRep`), the coefficient is the stage's
(`edgeCoefficient_actualFamily`), and the residual pair is truncated to the order `ℓ`. There is no
change of radius at the cascade (`r_s = r_*`, `L = 1`), so the bound `X_b` is unchanged.

For a stage without identities `K ≡ ℓ` and there is no truncation. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients AVRegularity.EntryTerminal.Ingredients.Recon

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The window of a frame ends at `t_f`. -/
theorem window_end : F.tp + fTobs F = F.tf := by
  simp [fTobs]

/-- The edge coefficients of the stage of a frame, in the form of the window. -/
theorem edge_stage (ℓ : ℕ) (hlev : F.G.level = F.m) (hmt : F.m ≤ D.term) :
    edgeCoefficient F.G.fam (D.kap F.G.level) (D.eps F.G.level) (D.eps (F.G.level - 1))
        F.G.actual (fK F ℓ) =
      edgeCoefficient F.G.actualFamily (D.κ F.m) (ocEpsilon D.q D.Λ F.m)
        (ocEpsilon D.q D.Λ (F.m - 1)) (fun _ => ()) (fK F ℓ) := by
  rw [GenStage.edgeCoefficient_actualFamily]
  have h1 : D.kap F.G.level = D.κ F.m := by simp [OCData.kap, hlev, hmt]
  have h2 : D.eps F.G.level = ocEpsilon D.q D.Λ F.m := by rw [hlev]; rfl
  have h3 : D.eps (F.G.level - 1) = ocEpsilon D.q D.Λ (F.m - 1) := by rw [hlev]; rfl
  rw [h1, h2, h3]

/-- **Conv at a frame.** -/
theorem frameReconConvAt_of_natural (ℓ : ℕ) (ρs : ℝ) (hρs : 0 ≤ ρs)
    (hlev : F.G.level = F.m) (hmt : F.m ≤ D.term) (hΛ : 1 ≤ D.Λ) (hκ : 0 < D.κ F.m)
    (hlen : F.Mn.lenFactor = 1)
    (hw : ∀ (p : OddSlot) (s : ℝ), F.G.fam.weight p s = ocCutoff D.α D.q D.Λ F.m p.1 s)
    (hπ : ∀ v, 0 < F.G.mass law v) : FrameReconConvAt F law ℓ ρs := by
  have hwin := window_end F
  intro hdesc Xb hXb û ŵ Rres qres hval hplain hRm hqi hRb hqb
  rw [hwin] at hval hplain hRm hqi hRb hqb
  have hkK : ∀ v, ℓ ≤ fK F ℓ v := fun v => Nat.le_add_right _ _
  have hKmax : ∀ v, fK F ℓ v ≤ Finset.univ.sup (fK F ℓ) := fun v => Finset.le_sup (Finset.mem_univ v)
  refine ⟨fK F ℓ, hkK, û, ŵ, Rres, qres, ?_⟩
  refine ⟨hdesc, ?_, ?_, ?_, ?_⟩
  · intro t ht v
    filter_upwards [hval t ht v] with y hy
    have hid := stage_gluedLift_eq_menuLiftedRep F.G F.Mn F.m F.N F.depth F.CcT F.aRep
      (tp := F.tp) (tf := F.tf) (t := t) y hΛ hmt hκ.le hlen hw ht
    rw [hy]
    exact congrFun hid v
  · rw [edge_stage F ℓ hlev hmt]
    exact hplain
  · have h := convMass_flux (ι := CompIn F.G.comps) (h := fun v => hr v.1.root)
      (D.κ F.m) ρs ρs 1 hκ hρs le_rfl (by rw [one_mul]) (fK F ℓ) ℓ
      (Finset.univ.sup (fK F ℓ)) hkK hKmax (F.G.mass law) hπ F.tp F.tf Rres Xb hXb hRm hRb
    rwa [one_pow, one_mul] at h
  · have h := convMass_scalar (ι := CompIn F.G.comps) (h := fun v => hr v.1.root)
      ρs ρs 1 hρs le_rfl (by rw [one_mul]) (fK F ℓ) ℓ
      (Finset.univ.sup (fK F ℓ)) hkK hKmax (F.G.mass law) hπ F.tp F.tf qres Xb hqi hqb
    rwa [one_pow, one_mul] at h

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The window energy step: the energy step of the window at a cascade frame** (cascade side of the bill
residual).

`frameReconEnergyAt_of_fullLift` concludes `FrameReconEnergyAt` (the energy hypothesis of the
window theorem at a frame): the coarse field `W = P_pZ` (truncated to
the order `k_c + 1 + N + D_m`) is continuous in time on the window, and its strong energy at the
slow length `fRho = liftLength` and the partition order is at most `C_s·A_in`, with
`C_s = CovCost (k_c + N + D_m + 2p) p · c_r^{-(k + N + 2p)} · C_k`.

Inputs, all hypotheses at the frame: the full-lift clauses at an order `k` with
`k_c + D_m + 1 ≤ k` (the `Z_strongEnergy_liftLength_le`: the energy of the readout `Z`
at the lift length; `energyCovStep`: the covariance step), the retained pair, the size form of the
covariance primitive at the slow length (the covariance size form at `c_r = 1`), and the continuity in time of the
retained solution `Y` (a clause of the regular solution).

* `continuousOn_succReadout`: the finite readout preserves continuity in time (generic roots;
  the terminal lemma is at the scalar roots).
* `frameReconW_continuousOn`: `t ↦ P_pZ(t)` is continuous, by the uniqueness of the covariance
  image and the continuity of the adjoint of the covariance polynomial (the terminal
  `reconW_continuousOn`, at a frame).

For `p = 0` one has `P_0 = I` and the cost is `1`; for `A_in = 0` the bound is `0`; `t_p = t_f`
is allowed. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Coarse AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.EntryTerminal.Ingredients.Recon.Energy
open scoped ENNReal

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- Transport along an equality of roots preserves continuity in time. -/
theorem continuousOn_rootCast {r r' K : ℕ} (heq : r = r') {s : Set ℝ}
    (u : ℝ → TorusHk K (hr r)) (hu : ContinuousOn u s) :
    ContinuousOn (fun t => cast (congrArg (fun s => TorusHk K (hr s)) heq) (u t)) s := by
  subst r'
  exact hu

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- **The finite readout preserves continuity in time.** -/
theorem continuousOn_succReadout {S S' : Finset Comp} {K : ℕ} (m : ℕ) (E η : ℝ) {s : Set ℝ}
    (u : ∀ c : CompIn S', ℝ → TorusHk K (hr c.1.root))
    (hu : ∀ c, ContinuousOn (u c) s) (v : CompIn S) :
    ContinuousOn (fun t => succReadout m E η K (fun c => u c t) v) s := by
  classical
  let f : CompIn S' → ℝ → TorusHk K (hr v.1.root) := fun c t =>
    if heq : compParent m c.1 = v.1 then
      E ^ (η * (compWord m c.1).length) •
        cast (congrArg (fun r => TorusHk K (hr r))
          ((compParent_root m c.1).symm.trans (congrArg Comp.root heq))) (u c t)
    else 0
  change ContinuousOn (fun t => ∑ c, f c t) s
  refine continuousOn_finsetSum _ fun c _ => ?_
  by_cases h : compParent m c.1 = v.1
  · simp only [f, h, ↓reduceDIte]
    exact (continuousOn_rootCast ((compParent_root m c.1).symm.trans (congrArg Comp.root h))
      (u c) (hu c)).const_smul (E ^ (η * (compWord m c.1).length) : ℝ)
  · simp only [f, h, ↓reduceDIte]
    exact continuousOn_const

/-- **Continuity of the coarse field of the window at a frame.** -/
theorem frameReconW_continuousOn (F : Frame D hr Dm b j₀) (kc : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (hcovc : ContinuousOn (fun t => menuCovPrimitive D F.Mn F.m t) (Set.Icc F.tp F.tf))
    (hcont : ∀ v', ContinuousOn (F.Y v') (Set.Icc F.tp F.tf)) (v : CompIn F.G.comps) :
    ContinuousOn (frameReconW F kc hW v) (Set.Icc F.tp F.tf) := by
  have hK2 : F.Naux - 2 * F.p + 2 * F.p ≤ F.Naux := by omega
  have hH : ∀ i j, ContinuousOn (fun t => menuCovPrimitive D F.Mn F.m t i j)
      (Set.Icc F.tp F.tf) := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hcovc)
  have hAc := covPolyP_adj_continuousOn (E := hr v.1.root)
    (fun t => menuCovPrimitive D F.Mn F.m t) (fun t => covBound (menuCovPrimitive D F.Mn F.m t))
    (fun _ => le_rfl) hH F.p 0 F.Naux (F.Naux - 2 * F.p) hK2
  have hZc := continuousOn_succReadout (S := F.G.comps) F.m (D.eps (F.m - 1)) F.η₀ F.Y hcont v
  have hcast : ContinuousOn (fun t => torusCast (E := hr v.1.root)
      (by omega : F.Naux = F.Naux - 2 * F.p + 2 * F.p)
      (succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun v' => F.Y v' t) v))
      (Set.Icc F.tp F.tf) :=
    (torusCast (E := hr v.1.root)
      (by omega : F.Naux = F.Naux - 2 * F.p + 2 * F.p)).continuous.comp_continuousOn hZc
  have hmain := (truncateTorusHk (E := hr v.1.root) hW).continuous.comp_continuousOn
    (hAc.clm_apply hcast)
  refine hmain.congr fun t ht => ?_
  have hPZ := (F.lift.2.1 v t ht).1
  have hadj : IsCovImage (AVRegularity.covPolyP (menuCovPrimitive D F.Mn F.m t) F.p)
      (succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun v' => F.Y v' t) v)
      ((TorusAdj.covPolyP (E := hr v.1.root) (menuCovPrimitive D F.Mn F.m t)
        le_rfl F.p 0 F.Naux).adj (F.Naux - 2 * F.p) hK2
        (torusCast (by omega : F.Naux = F.Naux - 2 * F.p + 2 * F.p)
          (succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun v' => F.Y v' t) v))) := by
    intro φ hφ hp
    have hid := (TorusAdj.covPolyP (E := hr v.1.root) (menuCovPrimitive D F.Mn F.m t)
      le_rfl F.p 0 F.Naux).ident (F.Naux - 2 * F.p) hK2
      (torusCast (by omega : F.Naux = F.Naux - 2 * F.p + 2 * F.p)
        (succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun v' => F.Y v' t) v)) φ
      (hφ.of_le (by exact_mod_cast le_top)) hp
    change cellInner (tval _) φ = cellInner (tval
      (succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun v' => F.Y v' t) v)) _
    rw [hid, tval_torusCast]
  have heq := covImage_unique _ _ _ _ hPZ hadj
  show truncateTorusHk hW (F.PZ v t) = _
  rw [heq]
  rfl

/-- **The window energy step: the energy step of the window at a frame**, from the full-lift clauses at an order
`k ≥ k_c + D_m + 1`. -/
theorem frameReconEnergyAt_of_fullLift (F : Frame D hr Dm b j₀) (law : BirthLaw)
    (Acl kc ℓ : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p) {k : ℕ}
    (hk : k + F.N + 2 * F.p ≤ F.Naux) (hkk : kc + Dm + 1 ≤ k)
    (hkp : wPord Dm F.depth F.N Acl ℓ ≤ kc + (F.N + Dm)) {c₀ cr Ck Ain ω : ℝ}
    {Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)}
    (cl : FullLiftClauses law F.G F.Gr F.m F.p F.Naux F.N F.depth F.sX F.sZ k hk F.η₀ c₀ cr
      F.tp F.tf Ck Ain F.Y Yw)
    (hp : RetainedPair F Yw) (hcr : 0 < cr) (hcr1 : cr ≤ 1)
    (hπ : ∀ v, 0 < F.G.mass law v) (hρ : 0 < fRho F)
    (hS : CovSizeForm F.Mn D F.m F.tp F.tf (fRho F) ω)
    (hcont : ∀ v', ContinuousOn (F.Y v') (Set.Icc F.tp F.tf)) :
    FrameReconEnergyAt F law Acl kc ℓ hW
      (CovCost (kc + (F.N + Dm) + 2 * F.p) F.p * (cr⁻¹) ^ (k + F.N + 2 * F.p) * Ck) Ain := by
  have htf : F.tp + fTobs F = F.tf := by simp only [fTobs]; ring
  have hC0 := covCost_nonneg (kc + (F.N + Dm) + 2 * F.p) F.p
  have hcr0 : (0 : ℝ) ≤ (cr⁻¹) ^ (k + F.N + 2 * F.p) := pow_nonneg (inv_nonneg.2 hcr.le) _
  unfold FrameReconEnergyAt
  rw [htf]
  refine ⟨fun v => frameReconW_continuousOn F kc hW hS.2.2.2 hcont v, ?_⟩
  have h1 := energyCovStep (K := kc + 1 + (F.N + Dm)) (K' := kc + (F.N + Dm)) (p := F.p)
    (L := k + F.N + 2 * F.p) (by omega) hkp (by omega) hρ
    (fun t => menuCovPrimitive D F.Mn F.m t) (D.κ (F.m - 1)) F.tp F.tf
    (CovCost (kc + (F.N + Dm) + 2 * F.p) F.p) hC0 (F.G.mass law) hπ
    (frameReconW F kc hW) (ReadoutZ F hk) (ReadoutZw F Yw hk)
    (fun v => ReadoutZw_memLp F hp hk v) (fun v => ReadoutZw_ae F hp hk v)
    (fun v t ht => isCovImage_truncate_pair hk hW _ _ _ (F.lift.2.1 v t ht).1)
    (covCost_le hρ hS _ _)
  have h2 := Z_strongEnergy_liftLength_le F law hk cl hp hcr hcr1 hπ
  calc strongEnergyUpTo (fRho F) (D.κ (F.m - 1)) (F.G.mass law) F.tp F.tf
        (wPord Dm F.depth F.N Acl ℓ) (frameReconW F kc hW)
      ≤ ENNReal.ofReal (CovCost (kc + (F.N + Dm) + 2 * F.p) F.p) *
          strongEnergy (fRho F) (D.κ (F.m - 1)) (F.G.mass law) F.tp F.tf
            (ReadoutZ F hk) (ReadoutZw F Yw hk) := h1
    _ ≤ ENNReal.ofReal (CovCost (kc + (F.N + Dm) + 2 * F.p) F.p) *
          (ENNReal.ofReal ((cr⁻¹) ^ (k + F.N + 2 * F.p)) * ENNReal.ofReal (Ck * Ain)) :=
        mul_le_mul_right h2 _
    _ = ENNReal.ofReal (CovCost (kc + (F.N + Dm) + 2 * F.p) F.p *
          (cr⁻¹) ^ (k + F.N + 2 * F.p) * Ck * Ain) := by
        rw [← ENNReal.ofReal_mul hcr0, ← ENNReal.ofReal_mul hC0]
        congr 1
        ring

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The quiet entrance at the bill context**.

The glued lift of the classical representative `aRep` at `t_p` is `aRep t_p` when the positive
lifts of the observed slots vanish at the cell time of `t_p` (`CellVanish`): the generic-`hr`
form of `qz_lifted_rep_eq` (stated there for `ScalarH` and `cr * liftLength`), at the lift length
`liftLength D m` of the cascade. Hence `û(t_p)` is the truncation of `P Z(t_p)`.

At least one observed slot has a nonvanishing cutoff, since the cutoffs sum to one; for
`aRep = 0` both sides vanish. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.QuietEntrance

namespace AVRegularity.Construction.Residual.Presentation.Cascade

section Glued

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- **The glued lift of the field is the field** at a time where the positive lifts of the
observed slots with nonvanishing cutoff vanish. -/
theorem gluedLift_eq_of_vanish {Dt : ℕ} {bw : ℝ} {j₀ : ℕ} (D : OCData) (m : ℕ)
    (Gw : GenStage D hr Dt bw j₀) (N H sX sZ : ℕ) (tp : ℝ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, hr v.1.root) (x : Vec 2)
    (hτ : 0 < ocTau D.α D.q D.Λ m) (hcs : D.cellScaleSq m ≠ 0) (hρ : liftLength D m ≠ 0)
    (hseq : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D m k (nativeChain m k) (liftLength D m)
          (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩)))
        sX sZ (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N H (CcT k))
    (hvan : ∀ k ∈ ocObsPulses D.α D.q D.Λ m tp tp, ocCutoff D.α D.q D.Λ m k tp ≠ 0 →
      tp / D.cellScaleSq m ∈ Set.Icc (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) ∧
      ∀ hh ≤ H, ∀ n, 1 ≤ n → ∀ m' (α : DerivativeWord2 m') X z v u,
        CcT k hh n m' α (tp / D.cellScaleSq m) X z v u = 0) :
    gluedLift (ocObsPulses D.α D.q D.Λ m tp tp) (fun k => ocCutoff D.α D.q D.Λ m k)
      (D.cellScaleSq m) (liftLength D m) (D.eps m)
      (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / liftLength D m) N H CcT
      (fun k s' y => D.flowOf (m - 1) s' y (D.slotAnchor m k))
      (fun k s' y => D.flowOf (m - 1) (D.slotAnchor m k) y s') aRep tp x = aRep tp x := by
  classical
  unfold gluedLift
  have hterm : ∀ k ∈ ocObsPulses D.α D.q D.Λ m tp tp,
      ocCutoff D.α D.q D.Λ m k tp • pulsePhysicalLift (D.cellScaleSq m) (liftLength D m)
        (D.eps m) (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / liftLength D m) N H (CcT k)
        (fun s' y => D.flowOf (m - 1) s' y (D.slotAnchor m k))
        (fun s' y => D.flowOf (m - 1) (D.slotAnchor m k) y s') aRep tp x =
      ocCutoff D.α D.q D.Λ m k tp • aRep tp x := by
    intro k hk
    by_cases hcut : ocCutoff D.α D.q D.Λ m k tp = 0
    · simp [hcut]
    · have hodd : Odd k := (Finset.mem_filter.1 hk).2.1
      obtain ⟨hmem, hz⟩ := hvan k hk hcut
      rw [qz_pulse_eq _ (hseq k hodd) _ _ _ _ _ hcs hρ (by rwa [← div_eq_inv_mul])
        (by simpa only [← div_eq_inv_mul] using hz) _ _ aRep x ?_]
      unfold OCData.flowOf
      rw [CycleComparison.Charts.streamFlow_group_law (D.hΦ (m - 1)),
        CycleComparison.Charts.streamFlow_self (D.hΦ (m - 1))]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul,
    Providers.CascadeInvariants.sum_ocCutoff_eq_one hτ _ (fun k hk => (Finset.mem_filter.1 hk).2.1) tp
      (fun k hk hne => qz_mem_obs hτ hk hne), one_smul]

end Glued

section Context

open AVRegularity.Construction.Preservation.Assembly

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀
    CQ Cpr Q T₀ hr)

/-- **The quiet entrance at the context**: the lifted field at `t_p` is the truncation of
`P Z(t_p)`. -/
theorem uhat_eq_trunc
    {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root)}
    {PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root)}
    {aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root}
    {û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)}
    (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
      (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
    (hvan : CellVanish c CcT) (hsc : QuietScale c) (htp : c.tp ≤ c.tf) (v : CompIn c.G.comps) :
    û v c.tp = truncateTorusHk (Nat.zero_le (Naux - 2 * p)) (PZ v c.tp) := by
  have hmem : c.tp ∈ Set.Icc c.tp c.tf := ⟨le_rfl, htp⟩
  have hglue : ∀ x, gluedLift (ocObsPulses c.D.α c.D.q c.D.Λ c.m c.tp c.tp)
      (fun k => ocCutoff c.D.α c.D.q c.D.Λ c.m k) (c.D.cellScaleSq c.m) (liftLength c.D c.m)
      (c.D.eps c.m) (ocDStar c.D.q c.D.Λ c.m (c.D.κ c.m) (c.D.κ (c.m - 1)) / liftLength c.D c.m)
      N (succSchedR r₀ J H) CcT
      (fun k s' y => c.D.flowOf (c.m - 1) s' y (c.D.slotAnchor c.m k))
      (fun k s' y => c.D.flowOf (c.m - 1) (c.D.slotAnchor c.m k) y s') aRep c.tp x = aRep c.tp x :=
    fun x => gluedLift_eq_of_vanish c.D c.m c.G N (succSchedR r₀ J H) sX sZ c.tp CcT aRep x
      hsc.hτ hsc.hcs hsc.hρ hlift.1 hvan
  refine KernelEnergy.torusCarrier_eq_of_value_ae _ _ ?_
  filter_upwards [hlift.2.2 v c.tp hmem, qe_value_trunc (Nat.zero_le (Naux - 2 * p)) (PZ v c.tp),
    qe_value_rep (PZ v c.tp) (fun x => aRep c.tp x v) (hlift.2.1 v c.tp hmem).2] with x h1 h2 h3
  rw [h1, h2, h3, hglue x]

end Context

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The full-lift bound at a context** (cascade side of the bill residual).

The proved full-lift bound of the successor (`Providers.successor_full_lift_bound`) in the common
prefix form, at an order `k` chosen as a function of the orders of the schedule:
`FullLiftAt … k C_k m_*` is `FullLiftClauses` at every context of level `≥ m_*`. The cascade
pieces take `FullLiftClauses` as a hypothesis at a frame (the lift step of the fine tail at `k = D_* + L_f + 1`, the energy step at the
orders of the window, the producer at `k = 0`).

For an order with `k + N + 2p > N_aux` the statement is vacuous and the constants are `0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- An order chosen from the orders of the schedule
`r₀, D₀, H, J, N, p, n_k, L_c, L_f, L_pr, A_cl, N_aux, N_out, K_res, n_pad, s_X, s_Z`. -/
abbrev SuccOrder : Type :=
  ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ

/-- **The full-lift clauses at every context of level `≥ m_*`**, at the order `k`, with the
constant `C_k`. -/
def FullLiftAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (k : ℕ) (Ck : ℝ) (mStar : ℕ) : Prop :=
  ∀ (hk : k + N + 2 * p ≤ Naux)
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    FullLiftClauses c.law c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ k hk
      (succEta0 α q s) kI.c₀ kI.cr c.tp c.tf Ck c.Ain c.Y c.Yw

/-- **The full-lift bound in the common prefix form**, at the order `kf` of the schedule's
orders; the constants are `(C_k, m_*)`. -/
theorem succPrefix_fullLift (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (kf : SuccOrder) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
          σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        FullLiftAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
          j₀ CQ Cpr Q T₀ (kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ) x.1 x.2) := by
  refine SuccPrefix.of_tail
    (Providers.successor_full_lift_bound α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ : SuccPrefix₀ α s q _) ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ _hfacts htail CQ Cpr
  by_cases hk : kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ + N + 2 * p ≤ Naux
  · obtain ⟨Ck, mStar, h⟩ := htail _ hk CQ Cpr
    refine ⟨(Ck, mStar), ?_⟩
    intro _ hr _ _ _ _ _ _ _ c hm
    exact h c.D c.hα c.hq c.hΛ c.hζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw
      c.seedK c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hmn c.hnM c.tA c.s₀ c.htA
      c.hs₀ c.htf c.hT₀ c.G c.G' c.hcascade c.hlevel c.hinv c.hactual c.tp c.Preg c.hprep c.f
      c.Ain c.hf c.Y0 c.Y c.Yw c.Yk c.htrace c.hsol
  · exact ⟨(0, 0), fun hk' => absurd hk' hk⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
section
/-! **The retained production bundle and the native inputs at a context** (cascade side of the
bill residual).

Two proved library statements in the common prefix form:

* `succPrefix_retainedProductionBundle`: the retained production bundle
  (`retained_production_bundle_of_certificates`, with the certificates
  `retained_stage_certificates`) at an order `k` of the schedule's orders: the geometry of the
  incoming lift, the retained solution at the order `N_aux + 3` (the hypothesis of the frame
  producer), and the budget of the readout energy at the order `k + N + 2p`.
* `succPrefix_nativeInput`: the qualitative native inputs `NativeInput F` at the frame of every
  lifted field of the context with classical representatives (`cascadeNativeInputsProduction`).

For `k + N + 2p > N_aux` the bundle statement is vacuous, and for an empty component family the
frame exists and the inputs are those of the empty stage. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- **The retained production bundle at every context of level `≥ m_*`**, at the order `k`,
with the readout constant `C_read`. -/
def RetainedProductionBundleAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (k : ℕ) (Cread : ℝ) (mStar : ℕ) :
    Prop :=
  ∀ (hk : k + N + 2 * p ≤ Naux)
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    IncomingLiftGeometryStatement c.G kI (succSchedR r₀ J H) 2 2 ∧
      RetainedHigherValuesStatement (c.G'.retained c.m H J) Naux c.tp c.tf c.Y ∧
      RetainedReadoutBudgetStatement c.law c.G (c.G'.retained c.m H J) c.m p Naux N k hk
        (succEta0 α q s) kI.cr c.tp c.tf Cread c.Ain c.Y c.Yw

/-- **The retained production bundle in the common prefix form**; the constants are
`(C_read, m_*)` with `0 ≤ C_read`. -/
theorem succPrefix_retainedProductionBundle (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (kf : SuccOrder) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
          σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        0 ≤ x.1 ∧ RetainedProductionBundleAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad
          sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀
          (kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ) x.1 x.2) := by
  obtain ⟨Λ₀, h128, -, hbundle⟩ := retained_production_bundle_of_certificates hα₀ hα₁ hs₀ hs₁ hq
    hζ (retained_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ) 128 le_rfl
  refine SuccPrefix.of_tail (⟨Λ₀, h128, hbundle⟩ : SuccPrefix₀ α s q _) ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ _hfacts htail CQ Cpr
  by_cases hk : kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ + N + 2 * p ≤ Naux
  · obtain ⟨Cread, mStar, hCread, h⟩ := htail _ hk CQ Cpr 2 2 le_rfl le_rfl
    refine ⟨(Cread, mStar), hCread, ?_⟩
    intro _ hr _ _ _ _ _ _ _ c hm
    exact h c.D c.hα c.hq c.hΛ c.hζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw
      c.seedK c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hmn c.hnM c.tA c.s₀ c.htA
      c.hs₀ c.htf c.hT₀ c.G c.G' c.hcascade c.hlevel c.hinv c.hactual c.tp c.Preg c.hprep c.f
      c.Ain c.hf c.Y0 c.Y c.Yw c.Yk c.htrace c.hsol
  · exact ⟨(0, 0), le_rfl, fun hk' => absurd hk' hk⟩

/-- **The native inputs at the frame of every lifted field of a context of level `≥ m_*`**. -/
def NativeInputAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
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
      Nonempty (NativeInput (c.frame CcT PZ aRep û hlift aZ aY hZ hY))

/-- **The native inputs in the common prefix form**; the constant is the level `m_*`. -/
theorem succPrefix_nativeInput (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        NativeInputAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ x) := by
  refine SuccPrefix.of_tail
    (cascadeNativeInputsProduction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ : SuccPrefix₀ α s q _) ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ _hfacts htail CQ Cpr
  obtain ⟨mStar, h⟩ := htail CQ Cpr
  refine ⟨mStar, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY
  exact h c.D c.hα c.hq c.hΛ c.hζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw
    c.seedK c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hmn c.hnM c.tA c.s₀ c.htA
    c.hs₀ c.htf c.hT₀ c.G c.G' c.hcascade c.hlevel c.hinv c.hactual c.tp c.Preg c.hprep c.f
    c.Ain c.hf c.Y0 c.Y c.Yw c.Yk c.htrace c.hsol CcT PZ aRep û hlift aZ aY hZ hY

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The native slot lifts at a context** (cascade side of the bill residual).

The proved uniform slot lifts of the native lift of a stage (`uniform_native_slot_lifts`,
short prefix `Λ₀ → (b, D_m, H, N, K, k, L) → (C_G, C_w, C_j, m₀)`) in the common prefix form, at
orders `(K, k, L)` chosen as functions of the orders of the schedule: `NativeSlotLiftsAt` gives, at
every context of level `≥ m_*` with the geometry of the incoming lift (the first clause of the
retained production bundle), a slot lift at every odd slot. They are the slot lifts of
`LiftSource` (the lift step of the fine tail) and of the lift settings.

For a stage without identities the slot lift has empty edges. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.FullLift

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- The lift order `N` of a successor schedule is at least `2`. -/
theorem succSchedule_two_le_N {α q s Q σ₀ a σ σf lamC : ℝ}
    {D₀ H J N p nk Lc Lf Lpr Acl Naux Nout : ℕ}
    (h : IsSuccessorSchedule α q s Q σ₀ a σ σf lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout) :
    2 ≤ N :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The native slot lifts at every context of level `≥ m_*`**, at the orders `(K, k, L)`,
with the constants `(C_G, C_w, C_j)`. -/
def NativeSlotLiftsAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (K k L : ℕ)
    (CG Cwl : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    IncomingLiftGeometryStatement c.G kI (succSchedR r₀ J H) 2 2 →
    ∀ slot : OddSlot, Nonempty (NativeSlotLift c.G slot (c.G.mass c.law)
      (succSchedR r₀ J H) N K k L CG Cwl Cj (CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe))

/-- **The native slot lifts in the common prefix form**, at the orders `(Kf, kf, Lf)` of the
schedule's orders; the constants are `(C_G, C_w, C_j, m_*)`. -/
theorem succPrefix_nativeSlotLifts (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Kf kf Lf' : SuccOrder) :
    SuccPrefix α s q (X := (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℕ → ℝ) × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
          σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        NativeSlotLiftsAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀
          (Kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ)
          (kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ)
          (Lf' r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ) x.1 x.2.1 x.2.2.1
          x.2.2.2) := by
  refine SuccPrefix.of_scale
    (uniform_native_slot_lifts hα₀ hα₁ hs₀ hs₁ hq hζ) ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ hfacts htail CQ Cpr
  obtain ⟨CG, Cwl, Cj, m₀, -, h⟩ := htail bw hfacts.hbw (succSchedD D₀ N p (H + 1))
    (succSchedR r₀ J H) N
    (Kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ)
    (kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ)
    (Lf' r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ)
    (Construction.Preservation.Buffer.preparation_schedule_order_ge_two D₀ N p H)
    (le_trans (by norm_num) (succSchedule_two_le_N hfacts.sched))
  refine ⟨(CG, Cwl, Cj, m₀), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hgeom slot
  obtain ⟨-, -, hterm, hj, hdepth, hres, hres2, hlen, -, -⟩ := hgeom
  have hband : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [c.hα, c.hq, c.hΛ, c.hζ, c.hterm]
    exact c.hband
  have hS := h hr c.D c.hα c.hq c.hΛ c.hζ c.hseq hband j₀ c.G c.law
    (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀ hφ₀ c.Mnat kI
    c.tA c.tf (CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe)
    (CI * c.D.eps (c.m - 1) ^ (q * min (ocDelta α q / 4) τe)) c.hinv
    (c.hlevel.symm ▸ hm) hterm hj hdepth hres hres2 hlen slot
  exact hS

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
end

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The lift step at every context, at an arbitrary order** (cascade side of the bill
residual).

`succPrefix_fineLiftAt kf`: in the common prefix form, for an order `K = kf(schedule)` paid by
the schedule (`K + 1 + N + 2p ≤ N_aux`, a hypothesis of the statement), at every context of level
`≥ m_*` and at the frame of every lifted field of the context with classical representatives
whose lifted classical field `F.uh` is jointly measurable on the window,
`FrameFineLiftAt F law k_I.c₀ K A_in (C_k·C_k)`: a representative `Û` of order `K + 1` of the
lifted field on the window, with the gradient energy `≤ C·A_in`.

Two orders are used: `K = D_* + L_f` (the fine tail, `succPrefix_fineLift` below) and
`K = D_m·R` (the realization of the lifted field at the descending slots on a degenerate window,
`succPrefix_reconDegenerate`).

Sources of the hypotheses of the `fineLiftAt`: the full-lift clauses at the order `K + 1`
(`succPrefix_fullLift`), the higher retained values and the geometry of the incoming lift
(`succPrefix_retainedProductionBundle`), the native slot lifts at the orders
`(K + 2 + N + D_m, K + 2, 0)` (`succPrefix_nativeSlotLifts`), torus compatibility from the stage
invariant, positivity of the masses from a slot lift's setting and of `κ_m` from the band chain.

The cases `K = 0`, an empty component family, `A_in = 0` and `t_p = t_f` are allowed. -/

/-- **The lift step of the fine tail at every context of level `≥ m_*`, at the order `K`** paid by the schedule: the lift
step at the frame of every lifted field with classical representatives whose lifted classical
field is jointly measurable on the window. -/
def FineLiftOrderCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (K : ℕ) (C : ℝ) (mStar : ℕ) :
    Prop :=
  K + 1 + N + 2 * p ≤ Naux →
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
      (∀ v : CompIn c.G.comps, Measurable
        (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc c.tp c.tf} =>
          (c.frame CcT PZ aRep û hlift aZ aY hZ hY).uh z.1.1 z.1.2 v)) →
      FrameFineLiftAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law kI.c₀ K c.Ain C

/-- **The lift step of the fine tail at the order `kf` in the common prefix form**; the constants are `(C_k·C_k, m_*)`. -/
theorem succPrefix_fineLiftAt (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (kf : SuccOrder) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        FineLiftOrderCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ (kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ)
          x.1 x.2) := by
  have h1 := succPrefix_fullLift α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ =>
      kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ + 1)
  have h2 := succPrefix_retainedProductionBundle α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
  have h3 := succPrefix_nativeSlotLifts α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ =>
      kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ + 2 + N +
        succSchedD D₀ N p (H + 1))
    (fun r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ =>
      kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ + 2)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
  refine ((h1.and h2).and h3).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨⟨hfl, -, hpk⟩, hlp⟩ := hx
  refine ⟨(x.1.1.1 * x.1.1.1, max (max x.1.1.2 x.1.2.2) (max x.2.2.2.2 2)), ?_⟩
  intro hk hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY hmeas
  have hm1 : x.1.1.2 ≤ c.m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : x.1.2.2 ≤ c.m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm3 : x.2.2.2.2 ≤ c.m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hm4 : 2 ≤ c.m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  obtain ⟨hgeom, hhigh, -⟩ := hpk (by omega : 0 + N + 2 * p ≤ Naux) c hm2
  have hP := hlp c hm3 hgeom
  have hΛ1 : 1 ≤ c.D.Λ := by rw [c.hΛ]; exact le_trans (by norm_num) hfacts.hΛ
  have hζD : IsFastProfile c.D.ζ := by rw [c.hζ]; exact hζ
  have hbandD : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [c.hα, c.hq, c.hΛ, c.hζ, c.hterm]
    exact c.hband
  have hmM : c.m ≤ c.M := le_trans c.hmn c.hnM.le
  have hκ : 0 < c.D.κ c.m :=
    CycleReference.bandChain_pos (le_trans (by norm_num) hfacts.hΛ) hζ c.hband hmM
  have hAin : 0 ≤ c.Ain := le_trans (Real.sqrt_nonneg _) c.hf
  have hρ : 0 < rhoStar c.D kI.c₀ c.m := c.hlevel ▸ hgeom.2.2.2.2.2.2.2.2.1
  have hmass : ∀ v, 0 < c.G.mass c.law v :=
    ((hP ⟨1, odd_one⟩).some).setting.mass_pos
  have hsrc : LiftSource (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law
      (kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ) := by
    refine ⟨?_, hΛ1, hζD, hbandD, c.hinv.isTorusCompatible, _, _, _, _, _, _, _,
      fun slot => (hP slot).some, ?_, ?_⟩
    · show 1 ≤ c.G.level
      rw [c.hlevel]
      omega
    · intro slot
      have hcap := ((hP slot).some).cap_le
      show kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ + 2 +
          (N + ((hP slot).some).cap) ≤
        kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ + 2 + N +
            succSchedD D₀ N p (H + 1) +
          4 * (succSchedR r₀ J H + 1) * (N + ((hP slot).some).cap) ^ 2
      omega
    · exact le_max_left _ _
  exact fineLiftAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law kI.c₀ kI.cr x.1.1.1
    c.Ain c.Yw (kf r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ) hk rfl rfl
    c.hlevel hAin hmass hρ hκ hmeas hhigh hsrc (hfl hk c hm1)

/-! **The lift step of the fine tail at every context** (cascade side of the bill residual,
the discharge of the hypotheses of the `fineLiftAt`).

`succPrefix_fineLift`: in the common prefix form, at every context of level `≥ m_*` and at the
frame of every lifted field of the context with classical representatives,
`FrameFineLiftAt F law k_I.c₀ (D_* + L_f) A_in (C_k·C_k)`, provided the lifted classical field
`F.uh` is jointly measurable on the window (the one hypothesis of the lift step of the fine tail
that the prefix does not supply: it is `Regularity.lifted.field.measurable` of the native
representatives of the covariance leaf).

It is the instance at the order `D_* + L_f` of `succPrefix_fineLiftAt`.
Sources of the other hypotheses of the lift step of the fine tail: the full-lift clauses at the order `D_* + L_f + 1`
(`succPrefix_fullLift`; the schedule pays `D_* + L_f + N + 2p + 1 ≤ N_aux`), the higher retained
values and the geometry of the incoming lift (`succPrefix_retainedProductionBundle`), the native
slot lifts at the orders `(K + 2 + N + D_m, K + 2, 0)` (`succPrefix_nativeSlotLifts`), torus
compatibility from the stage invariant, positivity of the masses from a slot lift's setting and of
`κ_m` from the band chain.

The cases `L_f = 0`, an empty component family and `A_in = 0` are allowed. -/

/-- **The lift step of the fine tail at every context of level `≥ m_*`**, at the frame of
every lifted field with classical representatives whose lifted classical field is jointly
measurable on the window. -/
def FineLiftCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Lf : ℕ) (C : ℝ) (mStar : ℕ) :
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
      (∀ v : CompIn c.G.comps, Measurable
        (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc c.tp c.tf} =>
          (c.frame CcT PZ aRep û hlift aZ aY hZ hY).uh z.1.1 z.1.2 v)) →
      FrameFineLiftAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law kI.c₀
        (succDstar D₀ N p H + Lf) c.Ain C

/-- **The lift step of the fine tail in the common prefix form**; the constants are `(C_k·C_k, m_*)`. It is
`succPrefix_fineLiftAt` at the order `D_* + L_f`, paid by the schedule
(`D_* + L_f + 1 + N + 2p ≤ N_aux`). -/
theorem succPrefix_fineLift (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        FineLiftCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Lf x.1 x.2) := by
  refine (succPrefix_fineLiftAt α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ D₀ H _ N p _ _ Lf _ _ _ _ _ _ _ _ => succDstar D₀ N p H + Lf)).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  have hk15 := hfacts.sched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk : succDstar D₀ N p H + Lf + 1 + N + 2 * p ≤ Naux := by
    have := (le_max_right _ _).trans hk15
    omega
  exact ⟨x, fun c hm => hx hk c hm⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
