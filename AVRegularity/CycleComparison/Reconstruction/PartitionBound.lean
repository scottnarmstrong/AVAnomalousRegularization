-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.ReconChains
public import AVRegularity.CycleComparison.Reconstruction.ApproxMeasurableBlocks
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.Coarse.Energy.Zero
public import AVRegularity.CycleComparison.Reconstruction.PulseInstance
import AVRegularity.CycleComparison.Reconstruction.FiniteRankIdentity
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.LiftSetting.Metric
import AVRegularity.CycleComparison.Reconstruction.Continuity

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The weak identity of the Galerkin approximants on a reconstruction window**.
On a reconstruction window (`ReconWindow`), cleanup chains of the approximant `a_n` exist
(`ReconWindowAt.exists_approxChains`, from the module `Reconstruction.ReconChains`), and the
glued lift of `a_n` solves the coupled weak identity with the residual `(approxFlux, approxForce)`
(`ReconWindowAt.approx_identity`): this is `approx_weak_identity` with every continuity
hypothesis discharged (with `PulseTail.setting_restTail_continuous` for the tails). -/

/-- The velocity of an admissible stream is continuous at every time. -/
theorem continuous_streamVel_of_admissible {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) : Continuous (streamVel φ s) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (φ s) := hφ.1.comp (contDiff_const.prodMk contDiff_id)
  have hg : Continuous (spaceGrad (φ s)) := continuous_pi fun i =>
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (Matrix.mulVecLin sigmaMat).continuous_of_finiteDimensional.comp hg

/-- A pulse whose partition weight moves at a time is active at that time: the weight vanishes
off the closed pulse window. -/
theorem mem_pulseWindow_of_deriv_ne_zero {α q : ℝ} {Λ m : ℕ} {kset : Finset ℤ}
    {ϖ : ℤ → ℝ → ℝ} {quiet I : Set ℝ} {τ Cpart : ℝ}
    (hpart : IsLiftPartition kset ϖ (ocPulseWindow α q Λ m) quiet I τ Cpart) {k : ℤ}
    (hk : k ∈ kset) {s : ℝ} (hd : deriv (ϖ k) s ≠ 0) : s ∈ ocPulseWindow α q Λ m k := by
  by_contra hs
  have hopen : IsOpen (ocPulseWindow α q Λ m k)ᶜ := isClosed_Icc.isOpen_compl
  have hev : ϖ k =ᶠ[nhds s] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hs] with t ht
    by_contra hne
    exact ht (hpart.2.2.2.1 k hk t hne)
  exact hd (by rw [hev.deriv_eq, deriv_const])

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **Cleanup chains of the Galerkin approximant `a_n` on the window**: tail chains `Vc` of the
lifts of `a_n` at the orders `(sXc, sZc, Acl)`, and chains `Vn` of the positive degrees of the
lifts of the divergence of the flux approximant at the orders `(sXl, sZl, Acl)`. -/
def ReconWindowAt.IsApproxChains
    (_w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (n sXc sZc Acl sXl sZl : ℕ) (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) : Prop :=
  (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H →
    ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
    IsCleanupChain sXc sZc Acl
      (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
        (chartField (coarseCoeff n W) (coarseMode n) (ocChart α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2)
          ρ) τ)
      (tailFluxField (fun n' => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1))
          hφ ν B ρ
          (ρ / ocEpsilon q Λ (m - 1)) k
          (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n') Nc D
        (ocDStar q Λ m ν B / ρ)
        (chartField (coarseCoeff n W) (coarseMode n) (ocChart α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2)
          ρ) τ)
      (fun j => Vc k hh j τ)) ∧
  (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
    ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
    IsCleanupChain sXl sZl Acl
      (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s X => fluxApproxDiv n Fc
        (ocEll q Λ m ν ^ 2 * s) ((ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (ocEll q Λ m ν ^ 2 * s) (ρ • X))) τ)
      (fun _ _ _ => 0) (fun j => Vn k hh n' j τ))

/-- **Cleanup chains of every Galerkin approximant exist** at chain orders below the orders of
the lift sequences. -/
theorem ReconWindowAt.exists_approxChains
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (sXc sZc Acl sXl sZl : ℕ) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc + Acl ≤ Klift + D + 2) (hZ : sZc + 1 ≤ Llift + 2) (hXl : 1 ≤ sXl)
    (hZl : 1 ≤ sZl) (hXl' : sXl + Acl ≤ Klift + Nc + 2 * D + 2)
    (hZl' : sZl + 1 ≤ Llift + 2 + 2 * D) :
    ∃ (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
      (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i),
      ∀ n, w.IsApproxChains n sXc sZc Acl sXl sZl (Vc n) (Vn n) := by
  choose Vc hVc using fun n => w.exists_tail_chains n sXc sZc Acl hXc hZc hX hZ
  choose Vn hVn using fun n => w.exists_lift_chains n sXl sZl Acl hXl hZl hXl' hZl'
  exact ⟨Vc, Vn, fun n => ⟨hVc n, hVn n⟩⟩

/-- **The weak identity of the glued lift of the Galerkin approximant on the window.** -/
theorem ReconWindowAt.approx_identity
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (hDL : D ≤ Llift + 2) (n sXc sZc Acl sXl sZl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc)
    (hZc : 1 ≤ sZc) (hX : sXc ≤ Klift + D + 2) (hZ : sZc ≤ Llift + 2) (hXl : 1 ≤ sXl)
    (hZl : 1 ≤ sZl) (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : w.IsApproxChains n sXc sZc Acl sXl sZl Vc Vn) :
    ∀ t ∈ Set.Icc tp (tp + Tobs), ∀ v, ∀ φ : Vec 2 → h v, ContDiff ℝ (⊤ : ℕ∞) φ →
      AVenhance.IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict unitCube) ν tp t (streamVel (Φ m))
        (fun x => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp
          (tp + Tobs) (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) t x v)
        (fun x => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp
          (tp + Tobs) (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) tp x v)
        φ (fun k x => fderiv ℝ φ x (basisVec k))
        (fun s k x => fderiv ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B
          ρ tp (tp + Tobs) (fun k => F.weight (pp k)) Nc H Cc
          (coarseTraj n W) s y v) x (basisVec k))
        (fun s x => edgeFluxOf K
          (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) s
          (obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
            (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s) v x)
        (approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Vc Vn n Fc v)
        (approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp
          (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl Cc Vc Vn n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v) := by
  obtain ⟨hV, hVn⟩ := hch
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have hm1 : 1 ≤ m := by have := w.hm; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hρ : 0 < ρ :=
    lt_of_lt_of_le w.hρs w.hρs_R
  have htAZ : tp ≤ tp + Tobs := by linarith [w.hTobs]
  have hNf : Nc + 1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) := by
    have := Nat.le_mul_of_pos_left ((Nc + D) + 8 * pc + 4) (by omega : 0 < Jc + H + 3)
    omega
  have hsZ : 1 ≤ max (Llift + 1) (Llift + 2) := le_max_of_le_left (by omega)
  have hcast : ∀ a b : ℕ, a ≤ b → (((a : ℕ∞)) : WithTop ℕ∞) ≤ ((b : ℕ) : WithTop ℕ∞) :=
    fun a b hab => WithTop.coe_le_coe.mpr (by exact_mod_cast hab)
  -- the charts
  have hχ : ∀ k s, ContDiff ℝ (⊤ : ℕ∞)
      (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) s) := fun k s =>
    contDiff_ocChart hφ α q Λ m _ s
  have hψ : ∀ k s, ContDiff ℝ (⊤ : ℕ∞)
      (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) s) := fun k s =>
    contDiff_ocChartInv hφ α q Λ m _ s
  have hψχ : ∀ k s y, ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) s
      (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) s y) = y := fun k s y =>
    Charts.ocChartInv_ocChart α q Λ m (Φ (m - 1)) hφ _ s y
  have hχψ : ∀ k s x, ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) s
      (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) s x) = x := fun k s x =>
    Charts.ocChart_ocChartInv α q Λ m (Φ (m - 1)) hφ _ s x
  -- the velocities
  have hadm : ∀ j, IsAdmissibleStream (Φ j) := Velocity.streamSeq_admissible w.hζ w.hΛ w.hΦ
  -- the coefficients of the coarse equation on the window
  have hEN : ∀ s ∈ Set.Icc tp (tp + Tobs), ContDiff ℝ (Nc : ℕ∞)
      (defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W
        aRep s) := fun s hs =>
    defectRemainder_contDiff n W aRep
      (fun d => (w.hcs.AD_smooth d s hs).of_le (hcast _ _ hNf))
      (fun r hr v u d => (w.hcs.CE_smooth r hr v u d s hs).of_le (hcast _ _ hNf))
      ((w.hcs.drift_smooth s hs).of_le (by exact_mod_cast le_top))
  -- the glued lift of a field of class `C^{N+J}` is of class `C^J`
  have hglue : ∀ (J : ℕ), J ≤ 1 → ∀ (a : ℝ → Vec 2 → ∀ i, h i), ∀ s ∈ Set.Icc tp (tp + Tobs),
      ContDiff ℝ ((Nc + J : ℕ) : ℕ∞) (a s) → ContDiff ℝ (J : ℕ∞) (fun y =>
        obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc a s y) := fun J hJ a s hs ha =>
    gluedLift_contDiff_oc hφ hℓ (fun k => F.fiber (pp k) (actual (pp k)))
      (fun k => F.weight (pp k)) w.hpart w.hsetting (Klift + D + 2) (max (Llift + 1) (Llift + 2))
      hsZ Cc w.hseq (by omega) (by omega) (ocEpsilon q Λ m)
      (ocDStar q Λ m ν B / ρ) a hs ha
  -- the approximant field as a weighted sum of pulse lifts
  have hUfun : ∀ s, obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp
      (tp + Tobs) (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s = fun y =>
      ∑ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), F.weight (pp k) s •
        obsLift α q Λ m (Φ (m - 1)) hφ ν B ρ Cc Nc H
          (coarseCoeff n W) (coarseMode n) k s y := fun s => by
    funext y
    simp only [obsGlued, gluedLift]
    rfl
  refine approx_weak_identity w.hΦ hm1 hΛ1 w.hζ hφ w.hν w.hB hρ F actual K w.hdesc w.htorus T
    htAZ w.hTcons w.hTcov w.hTq w.hTact pp w.hpp w.hppinj w.hpart w.hquiet w.hsetting
    (hDL.trans (le_max_right _ _)) Cc w.hseq sXc sZc Acl hAcl hXc hZc hX
    (hZ.trans (le_max_right _ _)) w.hcd aRep w.hrep w.hcs.D_ge w.hDr w.hr₀ w.hmean
    (fun s hs d => (w.hcs.AD_smooth d s hs).of_le (hcast 1 _ (le_trans (by omega) hNf)))
    (fun s hs d => w.hcs.AD_per d s hs)
    (fun s hs r hr v u d => (w.hcs.CE_smooth r hr v u d s hs).of_le (hcast 1 _ (le_trans (by omega) hNf)))
    (fun s hs r hr v u d => w.hcs.CE_per r hr v u d s hs)
    (continuous_streamVel_of_admissible hφ)
    (Velocity.streamSeq_velocity_spatial_periodic w.hζ w.hΛ w.hΦ (m - 1))
    (continuous_streamVel_of_admissible (hadm m)) n Vc hV sXl sZl hXl hZl Vn hVn ?_ ?_ ?_ ?_ ?_
    ?_ hEN ?_ ?_ ?_
  -- hUc: the approximant lift is `C¹`
  · intro s hs v
    exact contDiff_pi.1 (hglue 1 le_rfl (coarseTraj n W) s hs
      ((coarseTraj_contDiff n W s).of_le (by exact_mod_cast le_top))) v
  -- hEc: its edge flux is continuous
  · intro s hs v
    refine (glued_edges_continuous hΛ1 w.hζ hφ w.hν w.hB hρ F actual K w.hdesc w.htorus T
      w.hTcons w.hTcov w.hTq w.hTact pp w.hpp w.hppinj w.hpart w.hsetting (Klift + D + 2)
      (max (Llift + 1) (Llift + 2)) hsZ Cc w.hseq (coarseCoeff n W) (coarseMode n)
      (coarseMode_contDiff n) (coarseMode_periodic n) hs v).congr fun x => ?_
    rw [hUfun s]
    rfl
  -- hTFc, hTfc: the glued tail flux and force are continuous
  · intro s hs v a₀
    simp only [gluedTailFlux, Finset.sum_apply, Pi.smul_apply]
    refine continuous_finsetSum _ fun k hk => ?_
    by_cases hw : F.weight (pp k) s = 0
    · simp only [hw, zero_smul]
      exact continuous_const
    · exact (((setting_restTail_continuous (w.hsetting k hk) (Klift + D + 2)
        (max (Llift + 1) (Llift + 2)) (by omega) (by omega) (Cc k) (w.hseq k hk) sXc sZc Acl hAcl
        hXc hZc hX (hZ.trans (le_max_right _ _)) (ocDStar q Λ m ν B /
          ρ) (c := ocEll q Λ m ν ^ 2)
        (ρs := ρ) (es := ocEpsilon q Λ m) _ (Vc k) (hV k hk)
        (weighted_cellTime_mem_liftWindow hℓ w.hpart hk hs hw)
        (chartField_contDiff (coarseCoeff n W) (coarseMode n) (coarseMode_contDiff n) _
          (Charts.contDiff_ocChart_joint hφ α q Λ m _) _ _ _) (hχ k s) (hψ k s) (hψχ k s)
        (hχψ k s) v).1 a₀).const_smul (F.weight (pp k) s))
  · intro s hs v
    simp only [gluedTailForce, Finset.sum_apply, Pi.smul_apply]
    refine continuous_finsetSum _ fun k hk => ?_
    by_cases hw : F.weight (pp k) s = 0
    · simp only [hw, zero_smul]
      exact continuous_const
    · exact ((setting_restTail_continuous (w.hsetting k hk) (Klift + D + 2)
        (max (Llift + 1) (Llift + 2)) (by omega) (by omega) (Cc k) (w.hseq k hk) sXc sZc Acl hAcl
        hXc hZc hX (hZ.trans (le_max_right _ _)) (ocDStar q Λ m ν B /
          ρ) (c := ocEll q Λ m ν ^ 2)
        (ρs := ρ) (es := ocEpsilon q Λ m) _ (Vc k) (hV k hk)
        (weighted_cellTime_mem_liftWindow hℓ w.hpart hk hs hw)
        (chartField_contDiff (coarseCoeff n W) (coarseMode n) (coarseMode_contDiff n) _
          (Charts.contDiff_ocChart_joint hφ α q Λ m _) _ _ _) (hχ k s) (hψ k s) (hψχ k s)
        (hχψ k s) v).2).const_smul (F.weight (pp k) s)
  -- hLFc, hLfc: the glued lifted coarse flux and force are continuous
  · intro s hs v a₀
    simp only [gluedLiftFlux, Finset.sum_apply, Pi.smul_apply]
    refine continuous_finsetSum _ fun k hk => ?_
    by_cases hw : F.weight (pp k) s = 0
    · simp only [hw, zero_smul]
      exact continuous_const
    · exact (((liftPhys_continuous hAcl hXl hZl (ocDStar q Λ m ν B /
          ρ) (ρs := ρ)
        (es := ocEpsilon q Λ m) _ (Cc k) (Vn k) (hVn k hk)
        (weighted_cellTime_mem_liftWindow hℓ w.hpart hk hs hw) (hχ k s) (hψ k s) (hψχ k s)
        (hχψ k s) v).1 a₀).const_smul (F.weight (pp k) s))
  · intro s hs v
    simp only [gluedLiftForce, Finset.sum_apply, Pi.smul_apply]
    refine continuous_finsetSum _ fun k hk => ?_
    by_cases hw : F.weight (pp k) s = 0
    · simp only [hw, zero_smul]
      exact continuous_const
    · exact ((liftPhys_continuous hAcl hXl hZl (ocDStar q Λ m ν B /
          ρ) (ρs := ρ)
        (es := ocEpsilon q Λ m) _ (Cc k) (Vn k) (hVn k hk)
        (weighted_cellTime_mem_liftWindow hℓ w.hpart hk hs hw) (hχ k s) (hψ k s) (hψχ k s)
        (hχψ k s) v).2).const_smul (F.weight (pp k) s)
  -- hENc, hGc: the glued lifts of the remainder and of the flux divergence are continuous
  · intro s hs v
    exact (contDiff_pi.1 (hglue 0 (Nat.zero_le 1) _ s hs (hEN s hs)) v).continuous
  · intro s hs v
    exact (contDiff_pi.1 (hglue 0 (Nat.zero_le 1) _ s hs
      ((fluxApproxDiv_contDiff n Fc s).of_le (by exact_mod_cast le_top))) v).continuous
  -- hPc: the pulse lifts are continuous where the partition weights move
  · intro s hs v k hk hd
    have hwin := mem_pulseWindow_of_deriv_ne_zero w.hpart hk hd
    have hcell := AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 hwin hs
    exact (contDiff_pi.1 (pulsePhysicalLift_contDiff (w.hsetting k hk) (Klift + D + 2)
      (max (Llift + 1) (Llift + 2)) hsZ (Cc k) (w.hseq k hk) (J := 0) (by omega) (by omega)
      hc0.ne' ρ (ocEpsilon q Λ m)
      (ocDStar q Λ m ν B / ρ)
      (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
      (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n W) hcell
      ((hχ k s).of_le (by exact_mod_cast le_top)) ((hψ k s).of_le (by exact_mod_cast le_top))
      ((coarseTraj_contDiff n W s).of_le (by exact_mod_cast le_top))) v).continuous

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The start of the physical reconstruction**.

* `ReconWindowAt.gluedLift_start_rep`: at the start `t_p` of the window, the glued lift of the
  classical representative `aRep` of the retained coarse field is `aRep(t_p)`, pointwise. The
  representative is only finitely smooth, while the start of the lift (`gluedLift_start`) is
  stated for smooth inputs; it is applied to the Galerkin approximants `a_n` of `W(t_p)`. The
  glued lift is additive in its input (`gluedLift_sub_input_oc`), its values are bounded by the
  jets of order at most `N` of the input (`gluedLift_jet_le_pulseChart`), and these jets of
  `a_n - aRep(t_p)` tend to zero uniformly (`H^{N+2}(𝕋²) ⊂ C^N`,
  `classicalRep_orderedDerivative_le`, and `galerkinProj_tendsto`).
* `ReconWindowAt.physicalLift_start`: the torus carrier (`periodicHk`) of the glued lift at `t_p` is
  the truncation of every `X` whose truncation to the order of the datum is the datum `f₀`: its
  value is `aRep(t_p)`, a.e. the value of `W(t_p)`, which pairs with every smooth periodic test as
  `f₀` does (the coarse defect identity at `t = t_p`, `coarseDefect_tested_initial`), and a
  periodic Sobolev field is determined by these pairings (`torusHk_eq_of_cellInner`). -/

/-- A classical representative at the order `r` is one at every lower order. -/
theorem isClassicalRep_of_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K r r' : ℕ} {V : TorusHk K E}
    {a : Vec 2 → E} (ha : IsClassicalRep V a r) (hr : r' ≤ r) : IsClassicalRep V a r' :=
  ⟨hr.trans ha.1, classicalRep_contDiff_le ha hr, ha.2.2.1,
    fun j hj wd => ha.2.2.2 j (hj.trans hr) wd⟩

/-- A constant summed over the derivative words of length `i`. -/
theorem sum_const_derivativeWord2 (i : ℕ) (c : ℝ) :
    ∑ _wd : DerivativeWord2 i, c = (2 : ℝ) ^ i * c := by
  rw [Finset.sum_const, ChartTransport.card_derivativeWord2]
  simp

/-- Two vectors at distance at most `δ n` for a null sequence `δ` are equal. -/
theorem eq_of_norm_sub_le_tendsto {E : Type*} [NormedAddCommGroup E] {a b : E} (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (h : ∀ n, ‖a - b‖ ≤ δ n) : a = b :=
  sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' hδ h))

/-- Splitting through an approximant: if `gD = gB - gA` and `gB = p`, then
`‖gA - r‖ ≤ ‖gD‖ + ‖p - r‖`. -/
theorem norm_sub_le_of_glued_split {E : Type*} [NormedAddCommGroup E] {gA gB gD r p : E}
    (hD : gD = gB - gA) (hB : gB = p) : ‖gA - r‖ ≤ ‖gD‖ + ‖p - r‖ := by
  rw [hD, hB, norm_sub_rev p gA]
  exact norm_sub_le_norm_sub_add_norm_sub gA p r

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The glued lift of the classical representative at the start of the window** is the
representative: `𝒯 aRep (t_p, x) = aRep(t_p, x)`. The
hypothesis `1 ≤ D` gives the embedding `H^{Nc+2} ⊂ C^{Nc}` at the order `kc + 1 + (Nc + D)` of
the retained field (in the comparison window `2 ≤ D`). -/
theorem ReconWindowAt.gluedLift_start_rep
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (hD : 1 ≤ D) (εc : ℝ) (x : Vec 2) :
    gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
        (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) εc Nc H Cc
        (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) aRep tp x =
      aRep tp x := by
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hρ : 0 < ρ := w.hρs.trans_le w.hρs_R
  have htAZ : tp ≤ tp + Tobs := le_add_of_nonneg_right w.hTobs.le
  have hmem : tp ∈ Set.Icc tp (tp + Tobs) := ⟨le_rfl, htAZ⟩
  have hsZ : 1 ≤ max (Llift + 1) (Llift + 2) := le_max_of_le_left (by omega)
  have hNcK : Nc ≤ kc + 1 + (Nc + D) := by omega
  have hrK : Nc + 2 ≤ kc + 1 + (Nc + D) := by omega
  -- the classical representative at the order `Nc` of the lift
  have hrep : ∀ v, IsClassicalRep (W v tp) (fun y => aRep tp y v) Nc := fun v =>
    isClassicalRep_of_le (w.hrep tp hmem v) ((Nat.le_add_right Nc D).trans w.hDr)
  have haRep : ContDiff ℝ (Nc : ℕ∞) (aRep tp) :=
    contDiff_pi.2 fun v => classicalRep_contDiff_le (hrep v) le_rfl
  -- the Galerkin approximants of `W(t_p)`: smooth classical representatives of the cutoffs
  have hApp : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (coarseApprox n (fun v => W v tp)) := fun n => by
    rw [← coarseTraj_eq n W tp]
    exact coarseTraj_contDiff n W tp
  have hdiffC : ∀ n, ContDiff ℝ (Nc : ℕ∞)
      (fun y => coarseApprox n (fun v => W v tp) y - aRep tp y) := fun n =>
    ((hApp n).of_le (by exact_mod_cast le_top)).sub haRep
  have hkey : ∀ n v, IsClassicalRep (galerkinProj n (W v tp) - W v tp)
      (fun y => coarseApprox n (fun u => W u tp) y v - aRep tp y v) Nc := fun n v =>
    isClassicalRep_sub (coarseApprox_isClassicalRep n (fun u => W u tp) v hNcK) (hrep v)
  -- the quantitative embedding `H^{Nc+2} ⊂ C^{Nc}`, componentwise
  choose C hC0 hC using fun v : ι =>
    classicalRep_orderedDerivative_le (E := h v) (kc + 1 + (Nc + D)) Nc hrK
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, ∀ n,
      δ n = ∑ v, (2 : ℝ) ^ Nc * (C v * ‖galerkinProj n (W v tp) - W v tp‖) :=
    ⟨fun n => ∑ v, (2 : ℝ) ^ Nc * (C v * ‖galerkinProj n (W v tp) - W v tp‖),
      fun _ => rfl⟩
  have hδ0 : ∀ n, 0 ≤ ∑ v, (2 : ℝ) ^ Nc * (C v * ‖galerkinProj n (W v tp) - W v tp‖) :=
    fun n => Finset.sum_nonneg fun u _ =>
      mul_nonneg (pow_nonneg zero_le_two _) (mul_nonneg (hC0 u) (norm_nonneg _))
  -- the jets of order at most `Nc` of `a_n(t_p) - aRep(t_p)` are bounded by `δ n`
  have hA : ∀ n, ∀ i ≤ Nc + 0, ∀ y : Vec 2, ‖iteratedFDeriv ℝ i
      (fun y => coarseApprox n (fun v => W v tp) y - aRep tp y) y‖ ≤ δ n := by
    intro n i hi y
    have hi' : i ≤ Nc := by omega
    refine le_of_le_of_eq ?_ (hδ n).symm
    refine norm_iteratedFDeriv_le_of_apply_le ((hdiffC n).of_le (by exact_mod_cast hi')) y
      (hδ0 n) fun v => ?_
    show ‖iteratedFDeriv ℝ i
      (fun y => coarseApprox n (fun u => W u tp) y v - aRep tp y v) y‖ ≤ _
    calc ‖iteratedFDeriv ℝ i
          (fun y => coarseApprox n (fun u => W u tp) y v - aRep tp y v) y‖
        ≤ ∑ wd : DerivativeWord2 i, ‖orderedDerivative wd
            (fun y => coarseApprox n (fun u => W u tp) y v - aRep tp y v) y‖ :=
          ChartTransport.norm_iteratedFDeriv_le_sum_words
            (classicalRep_contDiff_le (hkey n v) hi') y
      _ ≤ ∑ _wd : DerivativeWord2 i, C v * ‖galerkinProj n (W v tp) - W v tp‖ :=
          Finset.sum_le_sum fun wd _ => hC v _ _ (hkey n v) i hi' wd y
      _ = (2 : ℝ) ^ i * (C v * ‖galerkinProj n (W v tp) - W v tp‖) :=
          sum_const_derivativeWord2 i _
      _ ≤ (2 : ℝ) ^ Nc * (C v * ‖galerkinProj n (W v tp) - W v tp‖) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi')
            (mul_nonneg (hC0 v) (norm_nonneg _))
      _ ≤ ∑ u, (2 : ℝ) ^ Nc * (C u * ‖galerkinProj n (W u tp) - W u tp‖) :=
          Finset.single_le_sum
            (f := fun u => (2 : ℝ) ^ Nc * (C u * ‖galerkinProj n (W u tp) - W u tp‖))
            (fun u _ => mul_nonneg (pow_nonneg zero_le_two _)
              (mul_nonneg (hC0 u) (norm_nonneg _))) (Finset.mem_univ v)
  -- `δ n → 0`: the Galerkin cutoffs converge in `H^{kc+1+(Nc+D)}`
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto
        (fun n => ∑ v, (2 : ℝ) ^ Nc * (C v * ‖galerkinProj n (W v tp) - W v tp‖))
        atTop (𝓝 (∑ v : ι, (2 : ℝ) ^ Nc * (C v * 0))) :=
      tendsto_finsetSum _ fun v _ =>
        ((tendsto_iff_norm_sub_tendsto_zero.1 (galerkinProj_tendsto (W v tp))).const_mul
          (C v)).const_mul ((2 : ℝ) ^ Nc)
    have h0 : (∑ v : ι, (2 : ℝ) ^ Nc * (C v * 0)) = 0 := by simp
    rw [h0] at h1
    exact h1.congr fun n => (hδ n).symm
  -- the values of the glued lift are bounded by the jets of order at most `Nc` of the input
  obtain ⟨M, -, hM⟩ := gluedLift_jet_le_pulseChart w.hα₀ w.hα₁ w.hs₀ w.hs₁ w.hq w.hζ w.hΛ w.hΦ
    w.hm hφ hℓ (fun k => F.fiber (pp k) (actual (pp k))) (fun k => F.weight (pp k)) w.hpart
    w.hsetting (Klift + D + 2) (max (Llift + 1) (Llift + 2)) hsZ Cc w.hseq (J := 0)
    (Nat.zero_le _) (Nat.zero_le _) (ocEpsilon q Λ m) εc
  refine eq_of_norm_sub_le_tendsto (fun n => M * δ n + δ n) ?_ fun n => ?_
  · simpa only [mul_zero, add_zero] using (hδlim.const_mul M).add hδlim
  · -- additivity, the start of the smooth approximant, and the two bounds
    have hsub := gluedLift_sub_input_oc (α := α) hφ hℓ (ocObsPulses α q Λ m tp (tp + Tobs))
      (fun k => F.weight (pp k)) ρ (ocEpsilon q Λ m) εc Nc H
      Cc (fun τ => coarseApprox n (fun v => W v τ)) aRep (t := tp)
      ((hApp n).of_le (by exact_mod_cast le_top)) haRep x
    have hst := gluedLift_start hφ hℓ hρ.ne' (fun k => F.fiber (pp k) (actual (pp k))) htAZ
      (fun k => F.weight (pp k)) w.hpart (Klift + D + 2) (max (Llift + 1) (Llift + 2)) Nc H
      Cc w.hseq εc (fun τ => coarseApprox n (fun v => W v τ)) (hApp n) x
    have hjet := hM (fun τ y => coarseApprox n (fun v => W v τ) y - aRep τ y) tp hmem
      (hdiffC n) (δ n) (hA n) 0 le_rfl x
    have hval := hA n 0 (Nat.zero_le _) x
    exact (norm_sub_le_of_glued_split hsub hst).trans
      (add_le_add ((norm_iteratedFDeriv_zero (𝕜 := ℝ)).symm.trans_le hjet)
        ((norm_iteratedFDeriv_zero (𝕜 := ℝ)
          (f := fun y => coarseApprox n (fun v => W v tp) y - aRep tp y) (x := x)).symm.trans_le
          hval))

/-- **The physical lift starts at the joint model** (`û(t_p) = 𝑷f`): in the slot `K_v`, the torus
carrier of the glued lift of `aRep` at `t_p` is the truncation of every `X` whose truncation to the
order of the datum `f₀` of the coarse defect equation is `f₀ v`. -/
theorem ReconWindowAt.physicalLift_start
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (hD : 1 ≤ D) (εc : ℝ) (v : ι)
    (hU : ContDiff ℝ (K v : ℕ∞) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs))
      (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ
      (ocEpsilon q Λ m) εc Nc H Cc
      (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
      (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) aRep tp x v))
    (hp : AVenhance.IsZ2Periodic (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs))
      (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ
      (ocEpsilon q Λ m) εc Nc H Cc
      (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
      (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) aRep tp x v))
    {M : ℕ} (hNM : kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) ≤ M) (hKM : K v ≤ M)
    (X : TorusHk M (h v)) (hX : truncateTorusHk hNM X = f0 v) :
    periodicHk (K v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs))
      (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ
      (ocEpsilon q Λ m) εc Nc H Cc
      (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
      (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) aRep tp x v)
      hU hp = truncateTorusHk hKM X := by
  have htAZ : tp ≤ tp + Tobs := le_add_of_nonneg_right w.hTobs.le
  have hmem : tp ∈ Set.Icc tp (tp + Tobs) := ⟨le_rfl, htAZ⟩
  -- the value of the carrier is `aRep(t_p)`, a.e. the value of `W(t_p)`
  have hfun : (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs))
      (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ
      (ocEpsilon q Λ m) εc Nc H Cc
      (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
      (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) aRep tp x v) =
      fun x => aRep tp x v :=
    funext fun x => congrFun (w.gluedLift_start_rep hD εc x) v
  have hae : Coarse.tval (periodicHk (K v) _ hU hp) =ᵐ[volume.restrict AVenhance.unitCube]
      Coarse.tval (W v tp) :=
    (periodicHk_value_ae (K v) _ hU hp).trans ((Filter.EventuallyEq.of_eq hfun).trans
      ((classicalRep_value_ae (w.hrep tp hmem v)).trans (Coarse.tvalL2_ae (W v tp)).symm))
  -- the value of the datum, read through the truncations
  have e1 : Coarse.tval (truncateTorusHk hKM X) = Coarse.tval X :=
    Coarse.tval_truncateTorusHk hKM X
  have e2 : Coarse.tval (f0 v) = Coarse.tval X := by
    rw [← hX]
    exact Coarse.tval_truncateTorusHk hNM X
  -- both sides pair with every smooth periodic test as `f₀ v` does
  refine Coarse.torusHk_eq_of_cellInner fun ψ hψ hψp => ?_
  have h1 : cellInner (Coarse.tval (periodicHk (K v) _ hU hp)) ψ =
      cellInner (Coarse.tval (W v tp)) ψ := by
    unfold cellInner
    exact integral_congr_ae (hae.mono fun x hx => congrArg (fun z => inner ℝ z (ψ x)) hx)
  have h2 : cellInner (Coarse.tval (W v tp)) ψ = cellInner (Coarse.tval (f0 v)) ψ :=
    coarseDefect_tested_initial w.hcd htAZ v ψ (hψ.of_le (by exact_mod_cast le_top)) hψp
  exact h1.trans (h2.trans (congrArg (fun g => cellInner g ψ) (e2.trans e1.symm)))

end AVRegularity.CycleComparison.Reconstruction
end
end

section
/-! **The partition term of the glued lift** (the term `ℓ√(B_p/τ) e^{-cτ/ℓ²}` of the bill).

The forcing of the glued lift of a coarse field `a` (`approxForce`) contains the partition term
`∑_k ϖ_k'(t) (𝒯_k a)(t, x)`. On the interior of the window it equals
`∑_{k, σ} ψ_{k,σ}(t) ∑_hh labelSrc_hh(a ∘ χ_k)(t, χ_k⁻¹(t, x))` with the rising and falling pieces
`ψ_{k,σ}` of `ϖ_k'` (`partition_term_decomp`). Each piece is the transition source of one lift on
one quiet gap:

* the rising piece of `k` and the falling piece of `k` when the window starts inside the
  falling overlap enter at the start of the lift window, with zero entrance trace, and cost
  nothing (`piece_zero`);
* the falling piece of `k` sits on the gap `[(k + 17/24)τ, (k + 61/48)τ]` of length at most `τ`,
  after the stretch `τ/48` from the entrance `(k + 17/24)τ`; with `|ϖ_k'| ≤ Cpart/τ` it costs
  `C (∑_b Θ^{hh-b} I_b) Cpart ℓ τ^{-1/2} e^{-(c/48)τ/ℓ²}` times the energy
  (`transition_label_bound`, `decay_factor_le`).

The gaps `[(k + 17/24)τ, (k + 61/48)τ]` and `[(k - 61/48)τ, (k - 17/24)τ]` lie in the trimmed
quiet times (`odd_trimmed_gap`), on which the family is fast independent; the entrance
`(k + 17/24)τ` is the first trimmed time after the pulse.

At each time at most two pieces are active (`card_active_le_two`), the charts transport the slice
norms (`slice_bound`), and the time integral is summed piece by piece (`lintegral_nested_sum`).

`partition_bound_core` is the statement for general lifts, charts and partitions with windows
`[(k ∓ 61/48)τ]`; `partition_term_bound` is its instance in the OC window context. The entrance
traces `I_b` of the falling gaps and the time measurability of the label fields are hypotheses
(see the docstring of `partition_term_bound`). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory Set AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open scoped ENNReal

universe u v w z

namespace AVRegularity.CycleComparison.Reconstruction

/-- Normalized chart jets through a higher order bound those through a lower order. -/
theorem jetBound_mono {Θ : Vec 2 → Vec 2} {N N' : ℕ} {D R : ℝ} (h : JetBound Θ N' D R)
    (hN : N ≤ N') : JetBound Θ N D R := by
  intro p hp1 hp2 y
  exact h p hp1 (hp2.trans hN) y

/-- **The partition term for general lifts, charts and time partitions.** -/
theorem partition_bound_core (Acl N D H kl Ll r : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (Dχ Cpart : ℝ) (hAcl : 1 ≤ Acl) (hDχ : 1 ≤ Dχ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, CompleteSpace (h i)]
        (Q : ℤ → LiftOperatorData ι h D) (π : ι → ℝ)
        (τ tA tZ e ν B ρ rs E ℓ dstar εc lam Rχ : ℝ) (kset : Finset ℤ) (par : ℤ → Fin 2)
        (V : ℤ → ℝ → ℝ → ℝ) (qs qf : ℕ) (bm : ι → ι → ℝ) (Θ : ℝ)
        (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (χ χi : ℤ → ℝ → Vec 2 → Vec 2) (ϖ : ℤ → ℝ → ℝ)
        (quiet : Set ℝ) (I : ℕ → ℝ) (a : ℝ → Vec 2 → ∀ i, h i),
        0 < τ → 0 < rs → rs ≤ e → e ≤ ρ → ρ ≤ Rχ → (∃ M : ℕ, e⁻¹ = (M : ℝ)) →
        0 ≤ Θ → (∀ b, 0 ≤ I b) → (∀ k ∈ kset, Odd k) →
        IsLiftPartition kset ϖ (fun k => Set.Icc (((k : ℝ) - 61 / 48) * τ)
          (((k : ℝ) + 61 / 48) * τ)) quiet (Set.Icc tA tZ) τ Cpart →
        (∀ k ∈ kset, IsLiftSetting (Q k) π (max (((k : ℝ) - 61 / 48) * τ) tA / ℓ ^ 2)
          (min (((k : ℝ) + 61 / 48) * τ) tZ / ℓ ^ 2) e ν B ρ E ℓ dstar εc lam (par k) (V k) H N
          (Acl + 2 + r + D * (H + 1) * N) (kl + r + D * (H + 1) * N)
          (Ll + r + D * (H + 1) * N) qs qf CG Cw Cj bm Θ) →
        (∀ k ∈ kset, IsLiftSequence (Q k) (Acl + 2 + r + D * (H + 1) * N + D + 2)
          (max (kl + r + D * (H + 1) * N + 1) (Ll + r + D * (H + 1) * N + 2))
          (max (((k : ℝ) - 61 / 48) * τ) tA / ℓ ^ 2)
          (min (((k : ℝ) + 61 / 48) * τ) tZ / ℓ ^ 2) N H (Cc k)) →
        (∀ k ∈ kset, ∀ (n : Fin 2 → ℤ) t X i j,
          (Q k).G t (X + ρ⁻¹ • latticeShift n) i j = (Q k).G t X i j) →
        (∀ k ∈ kset, ∀ (n : Fin 2 → ℤ) v u d, ∀ γ ∈ (Q k).edge v u d, ∀ α t X z,
          γ.coeff α t (X + ρ⁻¹ • latticeShift n) z = γ.coeff α t X z) →
        (∀ k t, IsChart (χ k t) (χi k t)) → (∀ k t, ContDiff ℝ (⊤ : ℕ∞) (χ k t)) →
        (∀ k t, ContDiff ℝ (⊤ : ℕ∞) (χi k t)) →
        (∀ k ∈ kset, ∀ t ∈ Set.Icc (((k : ℝ) - 61 / 48) * τ) (((k : ℝ) + 61 / 48) * τ),
          JetBound (χ k t) (4 * (N + D) + 2 * Acl + 16 + r + 2) Dχ Rχ ∧
          JetBound (χi k t) (4 * (N + D) + 2 * Acl + 16 + r + 2) Dχ Rχ) →
        (∀ k ∈ kset, ∀ S : Set ℝ, (∀ s ∈ S, ℓ ^ 2 * s ∈ (Set.Icc (((k : ℝ) + 17 / 24) * τ)
          (((k : ℝ) + 61 / 48) * τ) ∪ Set.Icc (((k : ℝ) - 61 / 48) * τ)
            (((k : ℝ) - 17 / 24) * τ)) ∩ Set.Icc tA tZ) →
          IsQuietOn (Q k).edge (fun τ' z => Real.sqrt (Q k).η • (Q k).v τ' z) S) →
        (∀ k ∈ kset, tA ≤ ((k : ℝ) + 17 / 24) * τ → ((k : ℝ) + 35 / 48) * τ ≤ tZ →
          HasQuietEntranceTrace π (Cc k) (((k : ℝ) + 17 / 24) * τ / ℓ ^ 2) lam N H
            (Acl + 2 + r + D * (H + 1) * N) (max (kl + r) (Ll + r + 2) + D * (H + 1) * N) I) →
        (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) → (∀ t, IsZ2Periodic (a t)) →
        (∀ k ∈ kset, ∀ hh, hh ≤ H → ∀ j, j ≤ r → ∀ w : DerivativeWord2 j,
          AEMeasurable (fun t => scalInt π (fun y => rs ^ j • orderedDerivative w
            (labelSrc N hh ℓ ρ e εc (Cc k) (fun t' y' => a t' (χ k t' y')) t) y))
            (volume.restrict (Set.Icc (max (((k : ℝ) - 61 / 48) * τ) tA)
              (min (((k : ℝ) + 61 / 48) * τ) tZ)))) →
        ∫⁻ t in Set.Icc tA tZ, (∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
          scalInt π (fun x => rs ^ j • orderedDerivative w (fun x' => ∑ k ∈ kset,
            deriv (ϖ k) t • pulsePhysicalLift (ℓ ^ 2) ρ e εc N H (Cc k) (χ k) (χi k) a t x')
              x)) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * (kset.card : ℝ) *
            (∑ hh ∈ Finset.range (H + 1), ∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) *
            ℓ * Real.sqrt (1 / τ) * Real.exp (-(c * τ / ℓ ^ 2))) *
          classicalStrongEnergy ρ B π (Set.Icc tA tZ) (4 * (N + D) + 2 * Acl + 16 + r) a := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hL1⟩ :=
    transition_label_bound.{u, v} Acl N D H kl Ll r CG Cw Cj Dχ hAcl
  refine ⟨sliceConst H r Dχ ^ (1 / 2 : ℝ) *
      (2 * ((∑ i ∈ Finset.range (r + 1), 2 ^ i * (H + 1) : ℕ) : ℝ)) * C₁ * |Cpart|, c₁ / 48,
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (sliceConst_nonneg H r Dχ) _)
      (by positivity)) hC₁) (abs_nonneg _), div_pos hc₁ (by norm_num), ?_⟩
  intro ι _ h _ _ _ _ Q π τ tA tZ e ν B ρ rs E ℓ dstar εc lam Rχ kset par V qs qf bm Θ Cc χ χi ϖ
    quiet I a hτ hrs hrse heρ hρR hM hΘ hI0 hodd hpart P hseq hGs hcs hC hχ hχi hJ hquiet hI ha
    hap hmeas
  -- the empty window
  rcases kset.eq_empty_or_nonempty with hk0 | ⟨k₀, hk₀⟩
  · subst hk0
    have hz : ∀ t, (∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j, scalInt π (fun x =>
        rs ^ j • orderedDerivative w (fun x' => ∑ k ∈ (∅ : Finset ℤ), deriv (ϖ k) t •
          pulsePhysicalLift (ℓ ^ 2) ρ e εc N H (Cc k) (χ k) (χi k) a t x') x)) ^
          (1 / 2 : ℝ) = 0 := by
      intro t
      simp only [Finset.sum_empty, orderedDerivative_zero_fun, smul_zero, scalInt_zero,
        Finset.sum_const_zero]
      exact ENNReal.zero_rpow_of_pos (by norm_num)
    simp only [hz, lintegral_zero]
    exact zero_le
  -- scales and the chart-frame field
  obtain ⟨Mn, hMe⟩ := hM
  have hℓ : 0 < ℓ := by
    rw [(P k₀ hk₀).ℓ_eq]
    exact div_pos (P k₀ hk₀).e_pos (Real.sqrt_pos.2 (P k₀ hk₀).ν_pos)
  have hρ : 0 < ρ := (P k₀ hk₀).ρ_pos
  have hc0 : 0 < ℓ ^ 2 := pow_pos hℓ 2
  have hsR : rs ≤ Rχ := hrse.trans (heρ.trans hρR)
  have hãs : ∀ k t, ContDiff ℝ (⊤ : ℕ∞) (fun y => a t (χ k t y)) := fun k t =>
    (ha t).comp (hχ k t)
  have hãp : ∀ k t, IsZ2Periodic (fun y => a t (χ k t y)) := fun k t n y => by
    show a t (χ k t (y + latticeShift n)) = a t (χ k t y)
    rw [(hC k t).equiv n y, hap t n (χ k t y)]
  have hJt : ∀ hh ∈ Finset.range (H + 1),
      ∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b ≤
        ∑ hh' ∈ Finset.range (H + 1), ∑ b ∈ Finset.range (hh' + 1), Θ ^ (hh' - b) * I b :=
    fun hh hhm => Finset.single_le_sum (f := fun hh' => ∑ b ∈ Finset.range (hh' + 1),
      Θ ^ (hh' - b) * I b) (fun hh' _ => Finset.sum_nonneg fun b _ =>
        mul_nonneg (pow_nonneg hΘ _) (hI0 b)) hhm
  obtain ⟨X, hX⟩ : ∃ X : ℝ≥0∞, X = ENNReal.ofReal (C₁ *
      (∑ hh ∈ Finset.range (H + 1), ∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) *
      |Cpart| * ℓ * Real.sqrt (1 / τ) * Real.exp (-(c₁ / 48 * τ / ℓ ^ 2))) *
      classicalStrongEnergy ρ B π (Set.Icc tA tZ) (4 * (N + D) + 2 * Acl + 16 + r) a :=
    ⟨_, rfl⟩
  -- the bound of each transition piece
  have hpiece : ∀ p ∈ kset ×ˢ (Finset.univ : Finset Bool), ∀ i ∈ Finset.range (r + 1),
      ∀ w' : DerivativeWord2 i, ∀ hh ∈ Finset.range (H + 1),
      ∫⁻ t, scalInt π (fun y => rs ^ i • orderedDerivative w' (fun y' =>
        trWeight ϖ τ tA tZ p.1 p.2 t • labelSrc N hh ℓ ρ e εc (Cc p.1)
          (fun t' y'' => a t' (χ p.1 t' y'')) t y') y) ^ (1 / 2 : ℝ) ≤ X := by
    intro p hp i hi w' hh hhm
    obtain ⟨k, σ⟩ := p
    have hk : k ∈ kset := (Finset.mem_product.1 hp).1
    have hir : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hhH : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
    show ∫⁻ t, scalInt π (fun y => rs ^ i • orderedDerivative w' (transitionSourceField N hh ℓ
        ρ e εc (trWeight ϖ τ tA tZ k σ) (Cc k) (fun t' y'' => a t' (χ k t' y'')) t) y) ^
        (1 / 2 : ℝ) ≤ X
    have hψM : ∀ t, |trWeight ϖ τ tA tZ k σ t| ≤ |Cpart| / τ := fun t =>
      (abs_trWeight_le ϖ τ tA tZ k σ t).trans ((hpart.2.2.2.2.1 k hk t).trans
        (div_le_div_of_nonneg_right (le_abs_self Cpart) hτ.le))
    have ht₀ : ℓ ^ 2 * (max (((k : ℝ) - 61 / 48) * τ) tA / ℓ ^ 2) =
        max (((k : ℝ) - 61 / 48) * τ) tA := mul_div_cancel₀ _ hc0.ne'
    have ht₁ : ℓ ^ 2 * (min (((k : ℝ) + 61 / 48) * τ) tZ / ℓ ^ 2) =
        min (((k : ℝ) + 61 / 48) * τ) tZ := mul_div_cancel₀ _ hc0.ne'
    have hJsub : ∀ g g', ((k : ℝ) - 61 / 48) * τ ≤ g → g' ≤ ((k : ℝ) + 61 / 48) * τ →
        ∀ t ∈ Set.Icc g g', JetBound (χ k t) (4 * (N + D) + 2 * Acl + 16 + r + 2) Dχ Rχ ∧
          JetBound (χi k t) (4 * (N + D) + 2 * Acl + 16 + r + 2) Dχ Rχ :=
      fun g g' h1 h2 t ht => hJ k hk t ⟨h1.trans ht.1, ht.2.trans h2⟩
    cases σ with
    | false =>
      -- the rising piece: the lift starts at the beginning of its gap
      have hmin1 := min_le_left (((k : ℝ) - 35 / 48) * τ) tZ
      have hmin2 := min_le_right (((k : ℝ) - 35 / 48) * τ) tZ
      refine (le_of_eq (piece_zero hL1 hrs hrse heρ hρR (P k hk) ⟨Mn, hMe⟩ (hseq k hk) (hC k)
        (hχ k) (hχi k) (min (((k : ℝ) - 35 / 48) * τ) tZ) ?_ ?_ ?_ (trWeight ϖ τ tA tZ k false)
        hψM ?_ hhH ha hap hir w')).trans zero_le
      · rw [ht₁]
        exact min_le_min (by linarith) le_rfl
      · rw [ht₀]
        exact hJsub _ _ (le_max_left _ _) (by linarith)
      · intro _
        refine hquiet k hk _ fun s hs => ?_
        obtain ⟨h1, h2⟩ := mul_mem_Icc_of_mem_div hc0 hs
        have h3 := le_trans h2 hmin1
        exact ⟨Or.inr ⟨le_trans (le_max_left _ _) h1, by linarith⟩,
          le_trans (le_max_right _ _) h1, le_trans h2 hmin2⟩
      · rw [ht₀]
        exact support_trWeight ϖ τ tA tZ k false
    | true =>
      by_cases hne : trLo τ tA k true < trHi τ tZ k true
      · have hlo : trLo τ tA k true = max (((k : ℝ) + 35 / 48) * τ) tA := rfl
        have hhi : trHi τ tZ k true = min (((k : ℝ) + 61 / 48) * τ) tZ := rfl
        have hmin1 := min_le_left (((k : ℝ) + 61 / 48) * τ) tZ
        have hmin2 := min_le_right (((k : ℝ) + 61 / 48) * τ) tZ
        rw [hlo, hhi] at hne
        by_cases hA : tA ≤ ((k : ℝ) + 17 / 24) * τ
        · -- the falling piece: decay across the gap `[(k + 17/24)τ, (k + 61/48)τ]`
          have hlo' : max (((k : ℝ) + 35 / 48) * τ) tA = ((k : ℝ) + 35 / 48) * τ :=
            max_eq_left (by linarith)
          rw [hlo'] at hne
          have hd : 0 < min (((k : ℝ) + 61 / 48) * τ) tZ - ((k : ℝ) + 17 / 24) * τ := by
            linarith
          have hgd : ((k : ℝ) + 17 / 24) * τ +
              (min (((k : ℝ) + 61 / 48) * τ) tZ - ((k : ℝ) + 17 / 24) * τ) =
              min (((k : ℝ) + 61 / 48) * τ) tZ := by ring
          have e1 : ((k : ℝ) + 17 / 24) * τ + τ / 48 = trLo τ tA k true := by
            rw [hlo, hlo']
            ring
          have hb := hL1 (Q k) π (max (((k : ℝ) - 61 / 48) * τ) tA / ℓ ^ 2)
            (min (((k : ℝ) + 61 / 48) * τ) tZ / ℓ ^ 2) e ν B ρ rs E ℓ dstar εc lam Rχ (par k)
            (V k) qs qf bm Θ hrs hrse heρ hρR (P k hk) ⟨Mn, hMe⟩ (Cc k) (hseq k hk) (χ k)
            (χi k) (hC k) (hχ k) (hχi k) (((k : ℝ) + 17 / 24) * τ)
            (min (((k : ℝ) + 61 / 48) * τ) tZ - ((k : ℝ) + 17 / 24) * τ) hd
            (by rw [ht₀]; exact max_le (by linarith) hA)
            (le_of_eq (by rw [hgd, ht₁]))
            (by rw [hgd]; exact hJsub _ _ (by linarith) hmin1)
            (hquiet k hk _ fun s hs => by
              obtain ⟨h1, h2⟩ := mul_mem_Icc_of_mem_div hc0 hs
              exact ⟨Or.inl ⟨h1, by linarith⟩, by linarith, by linarith⟩)
            I (hI k hk hA (by linarith)) (trWeight ϖ τ tA tZ k true) (|Cpart| / τ) (τ / 48)
            (div_nonneg hτ.le (by norm_num)) (by linarith) hψM
            (by
              rw [e1, hgd]
              exact support_trWeight ϖ τ tA tZ k true)
            hh hhH a ha hap i hir w'
          refine hb.trans ?_
          rw [hX]
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_)
            (classicalStrongEnergy_mono_set ρ B π ?_ _ a)
          · have hJ0 : 0 ≤ ∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b :=
              Finset.sum_nonneg fun b _ => mul_nonneg (pow_nonneg hΘ _) (hI0 b)
            refine (decay_factor_le hC₁ hJ0 (abs_nonneg Cpart) hℓ.le hτ
              (by linarith)).trans ?_
            have hR : 0 ≤ |Cpart| * ℓ * Real.sqrt (1 / τ) *
                Real.exp (-(c₁ / 48 * τ / ℓ ^ 2)) :=
              mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hℓ.le) (Real.sqrt_nonneg _))
                (Real.exp_pos _).le
            calc C₁ * (∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) * |Cpart| * ℓ *
                  Real.sqrt (1 / τ) * Real.exp (-(c₁ / 48 * τ / ℓ ^ 2))
                = (C₁ * ∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) *
                    (|Cpart| * ℓ * Real.sqrt (1 / τ) * Real.exp (-(c₁ / 48 * τ / ℓ ^ 2))) := by
                  ring
              _ ≤ (C₁ * ∑ hh' ∈ Finset.range (H + 1), ∑ b ∈ Finset.range (hh' + 1),
                    Θ ^ (hh' - b) * I b) *
                    (|Cpart| * ℓ * Real.sqrt (1 / τ) * Real.exp (-(c₁ / 48 * τ / ℓ ^ 2))) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hJt hh hhm) hC₁) hR
              _ = _ := by ring
          · rw [hgd]
            exact Set.Icc_subset_Icc hA hmin2
        · -- the falling piece of a lift starting inside its falling gap
          have hA' : ((k : ℝ) + 17 / 24) * τ < tA := not_le.1 hA
          have hmax : max (((k : ℝ) - 61 / 48) * τ) tA = tA := max_eq_right (by linarith)
          refine (le_of_eq (piece_zero hL1 hrs hrse heρ hρR (P k hk) ⟨Mn, hMe⟩ (hseq k hk)
            (hC k) (hχ k) (hχi k) (min (((k : ℝ) + 61 / 48) * τ) tZ) (le_of_eq ht₁.symm) ?_ ?_
            (trWeight ϖ τ tA tZ k true) hψM ?_ hhH ha hap hir w')).trans zero_le
          · rw [ht₀]
            exact hJsub _ _ (le_max_left _ _) hmin1
          · intro _
            refine hquiet k hk _ fun s hs => ?_
            obtain ⟨h1, h2⟩ := mul_mem_Icc_of_mem_div hc0 hs
            rw [hmax] at h1
            exact ⟨Or.inl ⟨by linarith, le_trans h2 hmin1⟩, h1, le_trans h2 hmin2⟩
          · rw [ht₀]
            refine (support_trWeight ϖ τ tA tZ k true).trans (Set.Icc_subset_Icc ?_ le_rfl)
            exact max_le_max (by linarith) le_rfl
      · -- an empty falling region
        exact (le_of_eq (lintegral_eq_zero_of_support_Icc (not_lt.1 hne)
          (support_transition_subset (support_trWeight ϖ τ tA tZ k true) N hh ℓ ρ e εc (Cc k)
            _ π rs w'))).trans zero_le
  -- measurability of the pieces
  have hZm : ∀ p ∈ kset ×ˢ (Finset.univ : Finset Bool), ∀ i ∈ Finset.range (r + 1),
      ∀ w' : DerivativeWord2 i, ∀ hh ∈ Finset.range (H + 1),
      AEMeasurable (fun t => scalInt π (fun y => rs ^ i • orderedDerivative w' (fun y' =>
        trWeight ϖ τ tA tZ p.1 p.2 t • labelSrc N hh ℓ ρ e εc (Cc p.1)
          (fun t' y'' => a t' (χ p.1 t' y'')) t y') y) ^ (1 / 2 : ℝ))
        (volume.restrict (Set.Ioo tA tZ)) := by
    intro p hp i hi w' hh hhm
    have hk : p.1 ∈ kset := (Finset.mem_product.1 hp).1
    obtain ⟨S, hS⟩ : ∃ S : Set ℝ, S = Set.Icc (max (((p.1 : ℝ) - 61 / 48) * τ) tA)
        (min (((p.1 : ℝ) + 61 / 48) * τ) tZ) := ⟨_, rfl⟩
    have hSm : MeasurableSet S := hS ▸ measurableSet_Icc
    have hY := hmeas p.1 hk hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) i
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) w'
    rw [← hS] at hY
    have hψm := (ENNReal.measurable_ofReal.comp
      ((measurable_trWeight ϖ τ tA tZ p.1 p.2).pow_const 2)).aemeasurable
      (μ := (volume.restrict (Set.Ioo tA tZ)).restrict S)
    have hY' : AEMeasurable (fun t => scalInt π (fun y => rs ^ i • orderedDerivative w'
        (labelSrc N hh ℓ ρ e εc (Cc p.1) (fun t' y'' => a t' (χ p.1 t' y'')) t) y))
        ((volume.restrict (Set.Ioo tA tZ)).restrict S) := by
      rw [Measure.restrict_restrict hSm]
      exact hY.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
    have hzero : ∀ t ∉ S, trWeight ϖ τ tA tZ p.1 p.2 t = 0 := fun t ht => by
      by_contra hne
      have hw := mem_window_of_trIcc hτ (trWeight_ne_zero hne).1
      apply ht
      rw [hS]
      exact ⟨max_le hw.1.1 hw.2.1, le_min hw.1.2 hw.2.2⟩
    have hind : (fun t => scalInt π (fun y => rs ^ i • orderedDerivative w' (fun y' =>
        trWeight ϖ τ tA tZ p.1 p.2 t • labelSrc N hh ℓ ρ e εc (Cc p.1)
          (fun t' y'' => a t' (χ p.1 t' y'')) t y') y) ^ (1 / 2 : ℝ)) =
        S.indicator (fun t => scalInt π (fun y => rs ^ i • orderedDerivative w' (fun y' =>
          trWeight ϖ τ tA tZ p.1 p.2 t • labelSrc N hh ℓ ρ e εc (Cc p.1)
            (fun t' y'' => a t' (χ p.1 t' y'')) t y') y) ^ (1 / 2 : ℝ)) := by
      funext t
      by_cases ht : t ∈ S
      · rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, scalInt_word_smul π rs (trWeight ϖ τ tA tZ p.1 p.2 t) w'
          (labelSrc N hh ℓ ρ e εc (Cc p.1) (fun t' y'' => a t' (χ p.1 t' y'')) t), hzero t ht]
        simp
    rw [hind, aemeasurable_indicator_iff hSm]
    refine AEMeasurable.pow_const (AEMeasurable.congr (hψm.mul hY')
      (ae_of_all _ fun t => (scalInt_word_smul π rs (trWeight ϖ τ tA tZ p.1 p.2 t) w'
        (labelSrc N hh ℓ ρ e εc (Cc p.1) (fun t' y'' => a t' (χ p.1 t' y'')) t)).symm)) _
  -- the bound at each time of the open window
  have hpt : ∀ t ∈ Set.Ioo tA tZ,
      (∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j, scalInt π (fun x => rs ^ j •
        orderedDerivative w (fun x' => ∑ k ∈ kset, deriv (ϖ k) t • pulsePhysicalLift (ℓ ^ 2)
          ρ e εc N H (Cc k) (χ k) (χi k) a t x') x)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (sliceConst H r Dχ ^ (1 / 2 : ℝ)) *
        ∑ p ∈ kset ×ˢ (Finset.univ : Finset Bool), ∑ i ∈ Finset.range (r + 1),
          ∑ w' : DerivativeWord2 i, ∑ hh ∈ Finset.range (H + 1),
            scalInt π (fun y => rs ^ i • orderedDerivative w' (fun y' =>
              trWeight ϖ τ tA tZ p.1 p.2 t • labelSrc N hh ℓ ρ e εc (Cc p.1)
                (fun t' y'' => a t' (χ p.1 t' y'')) t y') y) ^ (1 / 2 : ℝ) := by
    intro t ht
    have htI : t ∈ Set.Icc tA tZ := Set.Ioo_subset_Icc_self ht
    have hcell : ∀ k ∈ kset,
        t ∈ Set.Icc (((k : ℝ) - 61 / 48) * τ) (((k : ℝ) + 61 / 48) * τ) →
        (ℓ ^ 2)⁻¹ * t ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * τ) tA / ℓ ^ 2)
          (min (((k : ℝ) + 61 / 48) * τ) tZ / ℓ ^ 2) := fun _ _ hw =>
      Assembly.cellTime_mem_liftWindow hc0 hw htI
    have hrep : (fun x' => ∑ k ∈ kset, deriv (ϖ k) t • pulsePhysicalLift (ℓ ^ 2) ρ e εc N H
          (Cc k) (χ k) (χi k) a t x') =
        fun x' => ∑ p ∈ kset ×ˢ (Finset.univ : Finset Bool), trWeight ϖ τ tA tZ p.1 p.2 t •
          ∑ hh ∈ Finset.range (H + 1), labelSrc N hh ℓ ρ e εc (Cc p.1)
            (fun t' y => a t' (χ p.1 t' y)) t (χi p.1 t x') := by
      funext x'
      exact partition_term_decomp hodd hτ hpart ht
        (fun k => pulsePhysicalLift (ℓ ^ 2) ρ e εc N H (Cc k) (χ k) (χi k) a t x') (a t x')
        (fun k => ∑ hh ∈ Finset.range (H + 1), labelSrc N hh ℓ ρ e εc (Cc k)
          (fun t' y => a t' (χ k t' y)) t (χi k t x'))
        (fun k hk hd => pulsePhysicalLift_split (hseq k hk) hℓ.ne' hρ.ne' e εc (χ k) (χi k)
          (fun t' x'' => (hC k t').right x'') a (hcell k hk (mem_window_of_deriv hpart hk hd))
          x')
    rw [hrep]
    have hoddP : ∀ p ∈ kset ×ˢ (Finset.univ : Finset Bool), Odd p.1 := fun p hp =>
      hodd p.1 (Finset.mem_product.1 hp).1
    have hact : ∀ p ∈ kset ×ˢ (Finset.univ : Finset Bool),
        trWeight ϖ τ tA tZ p.1 p.2 t ≠ 0 → p.1 ∈ kset ∧
          t ∈ Set.Icc (((p.1 : ℝ) - 61 / 48) * τ) (((p.1 : ℝ) + 61 / 48) * τ) :=
      fun p hp hψ => ⟨(Finset.mem_product.1 hp).1,
        (mem_window_of_trIcc hτ (trWeight_ne_zero hψ).1).1⟩
    have hS := slice_bound (P := kset ×ˢ (Finset.univ : Finset Bool)) (H := H) (r := r) hDχ
      hrs hsR π (fun p => trWeight ϖ τ tA tZ p.1 p.2 t)
      (fun p => χ p.1 t) (fun p => χi p.1 t)
      (fun p hh => labelSrc N hh ℓ ρ e εc (Cc p.1) (fun t' y => a t' (χ p.1 t' y)) t)
      (fun p x' => ∑ hh ∈ Finset.range (H + 1), labelSrc N hh ℓ ρ e εc (Cc p.1)
        (fun t' y => a t' (χ p.1 t' y)) t (χi p.1 t x'))
      (fun _ _ => rfl) (fun p _ _ => hC p.1 t)
      (fun p _ _ => (hχi p.1 t).of_le (natCast_le_top_order _))
      (fun p hp hψ => jetBound_mono (hJ p.1 (hact p hp hψ).1 t (hact p hp hψ).2).2
        (by omega))
      (fun p hp hψ hh hhm => labelSrc_contDiff (hseq p.1 (hact p hp hψ).1)
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) (by omega) (le_max_of_le_left (by omega))
        ℓ ρ e εc (fun t' y => a t' (χ p.1 t' y)) (hãs p.1)
        (hcell p.1 (hact p hp hψ).1 (hact p hp hψ).2))
      (fun p hp hψ hh hhm => setting_labelSrc_periodic (P p.1 (hact p hp hψ).1)
        (hseq p.1 (hact p hp hψ).1) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) ℓ ρ e εc
        hρ.ne' Mn hMe (fun t' y => a t' (χ p.1 t' y)) (hãs p.1) (hãp p.1)
        (hGs p.1 (hact p hp hψ).1) (hcs p.1 (hact p hp hψ).1)
        (hcell p.1 (hact p hp hψ).1 (hact p hp hψ).2))
      (card_active_le_two hoddP ϖ hτ tA tZ t)
    refine (ENNReal.rpow_le_rpow hS (by norm_num)).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / 2 by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (sliceConst_nonneg H r Dχ)
        (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    exact mul_le_mul_right (rpow_half_nested_le _ r H _) _
  -- integrate over the window
  rw [setLIntegral_congr Ioo_ae_eq_Icc.symm]
  refine (setLIntegral_mono' measurableSet_Ioo hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_nested_sum _ r H _ hZm]
  refine (mul_le_mul_right (Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun i hi =>
    Finset.sum_le_sum fun w' _ => Finset.sum_le_sum fun hh hhm =>
      (setLIntegral_le_lintegral _ _).trans (hpiece p hp i hi w' hh hhm)) _).trans ?_
  rw [nested_sum_const, hX, final_count_eq (Real.rpow_nonneg (sliceConst_nonneg H r Dχ) _)]
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) _
  have hcardP : (((kset ×ˢ (Finset.univ : Finset Bool)).card : ℕ) : ℝ) = (kset.card : ℝ) * 2 := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  rw [Nat.cast_mul, hcardP]
  ring

/-- **The partition term of the glued lift in the OC window context**.

For the observed pulses `k` of `[tA, tZ]`, renewal charts `χ_k = ocChart … (ocPulseChartIndex k)`,
lift data `pulseLiftData … k` with lift settings and zero-start lift sequences on the clipped lift
windows at the raised orders of `Providers.cycle_residual_partition_differentiated`, a lift
partition `ϖ` of the window (`IsLiftPartition`, `|ϖ_k'| ≤ Cpart/τ`), and a smooth periodic coarse
field `a`: the weighted word derivatives of order at most `r` of the partition term
`∑_k ϖ_k'(t) (𝒯_k a)(t, ·)` have `L¹_t L²_x` norm at most
`C · #pulses · (∑_{hh ≤ H} ∑_{b ≤ hh} Θ^{hh-b} I_b) · ℓ τ^{-1/2} e^{-c τ/ℓ²}` times the strong
energy of `a` of order `4(N + D) + 2A + 16 + r`, with `C, c` depending only on the orders, the
setting constants and `Cpart`.

Hypotheses beyond the window data:
* `I` bounds the actual quiet entrance traces (`HasQuietEntranceTrace`) of the lift of `k` at the
  start `(k + 17/24)τ` of its falling gap (when that gap starts inside `[tA, tZ]` and its falling
  overlap meets the window). The rising and clipped gaps have zero trace by construction.
* the lower integrals are additive over the finitely many pieces: the slice norms of the word
  derivatives of the label fields `labelSrc` are a.e.-measurable in time on the window.
* the scale facts `rs ≤ ε_m ≤ ρ ≤ ε_{m-1}`. -/
theorem partition_term_bound (Acl N D H kl Ll r : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (Cpart : ℝ) (hAcl : 1 ≤ Acl) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, CompleteSpace (h i)] {Pc : Type w} {Ctx : Pc → Type z}
        (α sq q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ),
        0 < α → α < 1 / 3 → 0 < sq → sq < (1 - α) / 2 → IsAdmissibleQ α sq q →
        IsFastProfile ζ → 128 ≤ Λ → IsOCStreamSeq α q Λ ζ Φ → 2 ≤ m →
        ∀ (hφs : IsAdmissibleStream (Φ (m - 1))) (ν B ρ E rs tA tZ : ℝ),
        0 < rs → rs ≤ ocEpsilon q Λ m → ocEpsilon q Λ m ≤ ρ → ρ ≤ ocEpsilon q Λ (m - 1) →
        ∀ (F : ChartedFamily ι h D Pc Ctx) (actual : ∀ p, Ctx p),
        IsTorusCompatible F actual E →
        ∀ pp : ℤ → Pc, (∀ k ∈ ocObsPulses α q Λ m tA tZ,
          ocPulseWindow α q Λ m k ∩ Set.Icc tA tZ ⊆ (F.piece (pp k)).output) →
        F.IsFastIndependentOn (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tA tZ) →
        ∀ (ϖ : ℤ → ℝ → ℝ) (quiet : Set ℝ), IsLiftPartition (ocObsPulses α q Λ m tA tZ) ϖ
          (ocPulseWindow α q Λ m) quiet (Set.Icc tA tZ) (ocTau α q Λ m) Cpart →
        ∀ (π : ι → ℝ) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ) (qs qf : ℕ) (bm : ι → ι → ℝ)
          (Θ : ℝ),
        (∀ k ∈ ocObsPulses α q Λ m tA tZ,
          IsLiftSetting (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k
              (F.fiber (pp k) (actual (pp k)))) π
            (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
            (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
            (ocEpsilon q Λ m) ν B ρ E (ocEll q Λ m ν) (ocDStar q Λ m ν B)
            (ocDStar q Λ m ν B / ρ) (ρ / E) (par k) (V k) H N (Acl + 2 + r + D * (H + 1) * N)
            (kl + r + D * (H + 1) * N) (Ll + r + D * (H + 1) * N) qs qf CG Cw Cj bm Θ) →
        ∀ Cc : ℤ → ℕ → ℕ → LiftCoeff ι h,
        (∀ k ∈ ocObsPulses α q Λ m tA tZ,
          IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k
              (F.fiber (pp k) (actual (pp k)))) (Acl + 2 + r + D * (H + 1) * N + D + 2)
            (max (kl + r + D * (H + 1) * N + 1) (Ll + r + D * (H + 1) * N + 2))
            (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
            (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k)) →
        ∀ I : ℕ → ℝ, 0 ≤ Θ → (∀ b, 0 ≤ I b) →
        (∀ k ∈ ocObsPulses α q Λ m tA tZ, tA ≤ ((k : ℝ) + 17 / 24) * ocTau α q Λ m →
          ((k : ℝ) + 35 / 48) * ocTau α q Λ m ≤ tZ →
          HasQuietEntranceTrace π (Cc k) (((k : ℝ) + 17 / 24) * ocTau α q Λ m / ocEll q Λ m ν ^ 2)
            (ρ / E) N H (Acl + 2 + r + D * (H + 1) * N)
            (max (kl + r) (Ll + r + 2) + D * (H + 1) * N) I) →
        ∀ a : ℝ → Vec 2 → ∀ i, h i, (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) →
        (∀ t, IsZ2Periodic (a t)) →
        (∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ hh, hh ≤ H → ∀ j, j ≤ r →
          ∀ w : DerivativeWord2 j,
          AEMeasurable (fun t => scalInt π (fun y => rs ^ j • orderedDerivative w
            (labelSrc N hh (ocEll q Λ m ν) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) (Cc k)
              (fun t' y' => a t'
                (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) t' y')) t) y))
            (volume.restrict (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA)
              (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ)))) →
        ∫⁻ t in Set.Icc tA tZ, (∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
          scalInt π (fun x => rs ^ j • orderedDerivative w (fun x' =>
            ∑ k ∈ ocObsPulses α q Λ m tA tZ, deriv (ϖ k) t •
              pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ)
                N H (Cc k) (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
                (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) a t x')
              x)) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * ((ocObsPulses α q Λ m tA tZ).card : ℝ) *
            (∑ hh ∈ Finset.range (H + 1), ∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) *
            ocEll q Λ m ν * Real.sqrt (1 / ocTau α q Λ m) *
            Real.exp (-(c * ocTau α q Λ m / ocEll q Λ m ν ^ 2))) *
          classicalStrongEnergy ρ B π (Set.Icc tA tZ) (4 * (N + D) + 2 * Acl + 16 + r) a := by
  obtain ⟨C, c, hC, hc, hcore⟩ := partition_bound_core.{u, v} Acl N D H kl Ll r CG Cw Cj
    (pulseChartD (4 * (N + D) + 2 * Acl + 16 + r + 2)) Cpart hAcl (one_le_pulseChartD _)
  refine ⟨C, c, hC, hc, ?_⟩
  intro ι _ h _ _ _ _ Pc Ctx α sq q Λ m ζ Φ hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ hm hφs ν B ρ E rs tA tZ
    hrs hrse heρ hρR F actual htorus pp hpp hquietF ϖ quiet hpart π par V qs qf bm Θ P Cc hseq
    I hΘ hI0 hI a ha hap hmeas
  have hΛ1 : 1 ≤ Λ := by omega
  have hτ : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ1
  have hρ : 0 < ρ := (Construction.Stream.ocEpsilon_pos hΛ1).trans_le heρ
  have hquietCore : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ S : Set ℝ,
      (∀ s ∈ S, ocEll q Λ m ν ^ 2 * s ∈
        (Set.Icc (((k : ℝ) + 17 / 24) * ocTau α q Λ m) (((k : ℝ) + 61 / 48) * ocTau α q Λ m) ∪
          Set.Icc (((k : ℝ) - 61 / 48) * ocTau α q Λ m) (((k : ℝ) - 17 / 24) * ocTau α q Λ m)) ∩
          Set.Icc tA tZ) →
      IsQuietOn (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k
          (F.fiber (pp k) (actual (pp k)))).edge
        (fun τ' z => Real.sqrt (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k
            (F.fiber (pp k) (actual (pp k)))).η •
          (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k
            (F.fiber (pp k) (actual (pp k)))).v τ' z) S := by
    intro k hk S hS
    have hko := LiftSetting.obsPulse_odd hk
    refine pulse_isQuietOn hΛ1 hζ hφs ν B ρ (ρ / E) hko F (pp k) (actual (pp k)) hquietF
      fun s' hs' => ?_
    obtain ⟨hgap, hI'⟩ := hS s' hs'
    have hwin : ocEll q Λ m ν ^ 2 * s' ∈ Set.Icc (((k : ℝ) - 61 / 48) * ocTau α q Λ m)
        (((k : ℝ) + 61 / 48) * ocTau α q Λ m) := by
      rcases hgap with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith, h2⟩
      · exact ⟨h1, by linarith⟩
    have hqt : ocEll q Λ m ν ^ 2 * s' ∈ ocTrimmedQuietTimes α q Λ ζ m := by
      rcases hgap with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact odd_trimmed_gap hΛ1 hζ hko h1 (by linarith)
      · exact odd_trimmed_gap_left hΛ1 hζ hko (by linarith) h2
    have hmem : ocEll q Λ m ν ^ 2 * s' ∈ ocPulseWindow α q Λ m k ∩ Set.Icc tA tZ :=
      ⟨hwin, hI'⟩
    exact ⟨⟨hqt, hI'⟩, hpp k hk hmem⟩
  exact hcore (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k
      (F.fiber (pp k) (actual (pp k)))) π (ocTau α q Λ m) tA tZ (ocEpsilon q Λ m) ν B ρ rs E
    (ocEll q Λ m ν) (ocDStar q Λ m ν B) (ocDStar q Λ m ν B / ρ) (ρ / E) (ocEpsilon q Λ (m - 1))
    (ocObsPulses α q Λ m tA tZ) par V qs qf bm Θ Cc
    (fun k => ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
    (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) ϖ quiet I a
    hτ hrs hrse heρ hρR (pulse_e_inv_nat q Λ m) hΘ hI0 (fun k hk => LiftSetting.obsPulse_odd hk)
    hpart P hseq
    (fun k _ => pulse_G_slow_invariant α q Λ m ζ hφs ν B hρ.ne' (ρ / E) k _)
    (fun k _ => pulse_edge_slow_invariant α q Λ m ζ hφs ν B hρ.ne' k htorus (pp k))
    (fun k t => isChart_ocChart hφs α q Λ m _ t) (fun k t => contDiff_ocChart hφs α q Λ m _ t)
    (fun k t => contDiff_ocChartInv hφs α q Λ m _ t)
    (fun k _ t ht => pulseChart_jetBound α sq hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm hφs k
      ht _)
    hquietCore hI ha hap hmeas

end AVRegularity.CycleComparison.Reconstruction
end
end
