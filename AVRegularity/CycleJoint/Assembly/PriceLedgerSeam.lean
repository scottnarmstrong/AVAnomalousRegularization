-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.SeamAllocationScales
import AVRegularity.CycleJoint.Assembly.FollowingExplicitEnergyError

section
/-! **The two-block theorem on its window, the energy and the finish**.

`twoBlockJoint_energy`: from the outputs of the old block (`TwoBlockOldFacts`) and of the future
block (`TwoBlockFutureFacts`, with `Tpre'`, `Tpre` from the old block), the following-block
energy error with the explicit physical endpoint (`following_explicit_original_energy_error`,
endpoint the return of `Tret`) bounds the physical solution at `t_p` against the return of the
future word sum, and `twoBlockWordGeometry_finish` reads the allocation sum and concludes the
conclusion `TwoBlockJointConclusion`.

* `JointPremisesGen.physical_exists`, `JointPremisesGen.future_diag_solutions`: the outputs in the
  form of the hypotheses of the two-block theorem (their own declarations: the solution clauses are
  elaborated separately in the named propositions and in that statement). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

attribute [local instance] twoBlockFutureTorusNormed twoBlockFutureTorusInner
  twoBlockFutureTorusSpace twoBlockFutureTorusPiAdd twoBlockFutureTorusPiModule

/-- The order reserve `max Kmax 1 ≤ qJ` of the following block. -/
theorem max_one_le_of_reserve {Ks Kmax qJ : ℕ} (hqJ : Ks + 1 + Kmax ≤ qJ) : max Kmax 1 ≤ qJ := by
  omega

section Energy

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- The physical solutions of the patch data, in the form of the hypothesis of the two-block theorem. -/
theorem JointPremisesGen.physical_exists
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hζ : IsFastProfile ζ) (Npatch : ℕ)
    (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (uphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : twoPhysical hp hζ Npatch hNpatch patch uphys wphys) :
    ∀ ξ, ∃ f : ∀ i, PlaneHk Set.univ (K i) (h i),
      IsCoupledWeakSolutionPlane ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D K
        (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
        f (fun _ _ => 0) (fun _ _ => 0) (uphys ξ) (wphys ξ) :=
  fun ξ => ⟨_, hs ξ⟩

/-- The future cell solutions at the diagonal datum, in the form of the hypothesis of the two-block theorem: their datum
is the transition (the family map) of the old endpoint `Tpre`. -/
theorem JointPremisesGen.future_diag_solutions
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (s : Finset (List Bool))
    (V₀' Tpre' : (List Bool → (∀ i, TorusHk (K i) (h i))) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Tpre : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (uphys' : (List Bool → (∀ i, TorusHk (K i) (h i))) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys' : (List Bool → (∀ i, TorusHk (K i) (h i))) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hcell : BlockCellSolutions D K (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoTp α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYcPost hp)) (twoGpost hp)
      (preparationReferenceCellSourceCoefficient F hφ (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) ν
        (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K (twoYcPost hp))
      V₀' (twoUHpost hp hΛ hchart uphys') (twoWHpost hp hΛ hchart wphys'))
    (hident : ∀ η i, V₀' η i = twoTransit hp hΛ hchart i (Tpre' η i))
    (hdiag : ∀ ξ, Tpre' (wordDiag s ξ) = Tpre ξ) :
    ∀ ξ, IsCoupledWeakSolutionPlane 1 (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoTp α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYcPost hp)) D K
      (planeMetricSourceCoefficient K D (twoGpost hp)
        (preparationReferenceCellSourceCoefficient F hφ (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K (twoYcPost hp)))
      (preparationReferenceCellTransitionFamilyLinearMap hp.hprep hp.hcover
        (Construction.Stream.ocTauPP_pos hΛ).le (ocA_nonneg_of hΛ (m - 1)) K
        (slot_le_chart hp.hK hchart) (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (hp.windows hΛ).next
        (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne' (twoYc hp) (twoYcPost hp)
        (ν⁻¹ * (ocEpsilon q Λ m ^ 2 * cellTime q Λ m ν (twoSeam α q Λ m l₀)))
        (hp.windows hΛ).seamMem (Tpre ξ))
      (fun _ _ => 0) (fun _ _ => 0) (twoUHpost hp hΛ hchart uphys' (wordDiag s ξ))
      (twoWHpost hp hΛ hchart wphys' (wordDiag s ξ)) := by
  intro ξ
  have hd : V₀' (wordDiag s ξ) = preparationReferenceCellTransitionFamilyLinearMap hp.hprep
      hp.hcover (Construction.Stream.ocTauPP_pos hΛ).le (ocA_nonneg_of hΛ (m - 1)) K
      (slot_le_chart hp.hK hchart) (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (hp.windows hΛ).next
      (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne' (twoYc hp) (twoYcPost hp)
      (ν⁻¹ * (ocEpsilon q Λ m ^ 2 * cellTime q Λ m ν (twoSeam α q Λ m l₀)))
      (hp.windows hΛ).seamMem (Tpre ξ) := by
    funext i
    rw [hident, hdiag, preparationReferenceCellTransitionFamilyLinearMap_apply]
    rfl
  exact coupled_datum_congr (hcell (wordDiag s ξ)) hd

end Energy

/-- **The body of the energy step** for the constants of the block word geometry, the first-block energy constant
`Cenergy1` and the following-block energy constant `Cenergy2`: for every family with the joint
premises, every patch, the weights of the future window, and the outputs of the old and future
blocks, the conclusion of the two-block theorem holds. -/
def TwoBlockEnergyBody (D Ks Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (Cm Cchart CG : ℕ → ℝ) (Cprep CR Cterminal Crem : ℝ) (α q : ℝ) {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (Cw : ℕ → ℝ) (Cenergy1 Cenergy2 : ℝ) (Npre Npost Lpre Lpost : ℕ) :
    Prop :=
  ∀ (Λ : ℕ) (_hΛ128 : 128 ≤ Λ) (hΛ : 1 ≤ Λ) (g₀ : ℝ) (_hg₀ : g₀ ≤ 1 / 32) (H Ls qJ : ℕ)
    (_hD : 2 ≤ D) (_hqJ : Ks + 1 + Kmax ≤ qJ) (Ca Cth Cb COld Crat Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (r ρold : ℝ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ) (Jpre Jpost : ℕ)
    (_hNle : Npost ≤ Npre) (θM₁ θS₁ θM₂ θS₂ : ℝ) (bM₁ bS₁ bM₂ bS₂ : ι → ι → ℝ)
    (_W : ChartWeights (twoGpost hp) (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
      (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoTp α q Λ m l₀) - cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0 Npost Cw)
    (uphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (Upre : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Bdpre : (∀ i, TorusHk (K i) (h i)) → ℝ≥0∞)
    (hpre : BlockWordConclusion K Jpre H (fun t => twoGpre hp t 0) (twoMpre hp θM₁ bM₁)
      (twoSpre hp θS₁ bS₁) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp)
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) (cellTime q Λ m ν tS)
      (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYc hp))
      (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch)
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m) Npost π
      (twoUH hp hΛ hchart uphys) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) Bdpre)
    (Tpre' : (List Bool → (∀ i, TorusHk (K i) (h i))) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Tpre : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (_hO : TwoBlockOldFacts hp hΛ hchart hζ Cw Cenergy1 Cprep CR Cterminal Crem Npre Npost Lpre
      Npatch hNpatch patch Jpre θM₁ θS₁ bM₁ bS₁ uphys wphys Upre Bdpre hpre Tpre' Tpre)
    (V₀' : (List Bool → (∀ i, TorusHk (K i) (h i))) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (uphys' : (List Bool → (∀ i, TorusHk (K i) (h i))) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys' : (List Bool → (∀ i, TorusHk (K i) (h i))) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (Bdpost : (List Bool → (∀ i, TorusHk (K i) (h i))) → ℝ≥0∞)
    (hpost : BlockWordConclusion K Jpost H (fun t => twoGpost hp t 0) (twoMpost hp θM₂ bM₂)
      (twoSpost hp θS₂ bS₂) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYcPost hp)
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoTp α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYcPost hp)) V₀'
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m) 0 π
      (twoUHpost hp hΛ hchart uphys') (cellTime q Λ m ν (twoTp α q Λ m l₀)) Bdpost)
    (Tret : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (_hF : TwoBlockFutureFacts hp hΛ hchart Cw Cprep CR Cterminal Crem Npost Lpost Jpre Jpost θM₂
      θS₂ bM₂ bS₂ Tpre' Tpre V₀' uphys' wphys' Bdpost hpost Tret),
    TwoBlockJointConclusion hp hΛ hchart hζ Cw Cenergy1 Cenergy2 Cprep CR Cterminal Crem Npre
      Npost Lpre Lpost Npatch hNpatch patch Jpre Jpost θM₁ θS₁ θM₂ θS₂ bM₁ bS₁ bM₂ bS₂

/-- **The two-block theorem on its window, the energy and the finish.** The following-block energy constant
`Cenergy2` is chosen with `TwoBlockEnergyBody`. -/
theorem twoBlockJoint_energy (D Ks Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm Cchart CG : ℕ → ℝ) (Cprep CR Cterminal Crem : ℝ)
    {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Cenergy2 : ℝ, 1 ≤ Cenergy2 ∧ ∀ (Cw : ℕ → ℝ) (Cenergy1 : ℝ) (Npre Npost Lpre Lpost : ℕ),
      TwoBlockEnergyBody.{u, v, w, x} D Ks Kmax Jchart Jm hchart Cm Cchart CG Cprep CR Cterminal
        Crem α q hζ Cw Cenergy1 Cenergy2 Npre Npost Lpre Lpost := by
  obtain ⟨Cenergy2, hCe2, hmix⟩ := following_explicit_original_energy_error.{u, v, w, x, max u v}
    D Kmax Jchart Jm hchart hmol Cm Cchart
  refine ⟨Cenergy2, hCe2, ?_⟩
  intro Cw Cenergy1 Npre Npost Lpre Lpost Λ hΛ128 hΛ g₀ hg₀ H Ls qJ hD hqJ Ca Cth Cb COld Crat Cpad
    Cage Npad mStar ι _ _ h _ _ _ _ _ _ π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ P' Ctx F actual A
    Θ T r ρold hp Npatch hNpatch patch Jpre Jpost hNle θM₁ θS₁ θM₂ θS₂ bM₁ bS₁ bM₂ bS₂ W uphys wphys
    Upre Bdpre hpre Tpre' Tpre hO V₀' uphys' wphys' Bdpost hpost Tret hF
  obtain ⟨heE, hper, hgsmall, -, hm⟩ := hp.scales hq hΛ128 hg₀
  obtain ⟨hBnn, hrow, hcol, -⟩ := hp.sums
  have hwin := hp.windows hΛ
  have hsc := windowCover_native_subwindow_scales hΛ hφ hp.cov
    (windowCoverFollowingChartIndex P hp.cov.P_pos) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
    (cellTime q Λ m ν (twoTp α q Λ m l₀)) hwin.windowPost
  have hτend : cellTime q Λ m ν (twoTp α q Λ m l₀) ∈
      Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (cellTime q Λ m ν (twoTp α q Λ m l₀)) :=
    ⟨hwin.bd.le, le_rfl⟩
  have hdiagSol := hp.future_diag_solutions hΛ hchart (blockWords Jpre H) V₀' Tpre' Tpre uphys'
    wphys' hF.1 hF.2.1 hO.2.2.2.2.2.1
  have hbound := hmix α q Λ m Φ hφ tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad l₀ P ν
    (ocEpsilon q Λ m) r hp.cov.pos.1 hp.cov.pos.2.2 hp.cov.rho_e heE F π hp.hπ K hp.hK actual
    (fun v u => Real.sqrt (π u / π v) * A v u) hBnn hp.hprep hp.hcover hp.hmeas hp.hwmeas
    hp.hpointwise hwin.next (cellTime q Λ m ν (twoSeam α q Λ m l₀))
    (cellTime q Λ m ν (twoTp α q Λ m l₀)) (max Cth 0 * Θ) hsc.1 hrow hcol H hp.hdepth hp.hdesc ζ B
    g g₀ a B₀ lam Cb qJ CG y₀ hp.cov hΛ128 hζ hwin.bd.le hwin.windowPost
    (max_one_le_of_reserve hqJ) (by linarith only [hgsmall]) hD rfl hp.htorus
    (Classical.choose hper) (Classical.choose_spec hper) s hα0 hα1 hs0 hs1 hq hp.hΦ hm
    (ocA_nonneg_of hΛ (m - 1)) (ν⁻¹ * (ocEpsilon q Λ m ^ 2 * cellTime q Λ m ν (twoSeam α q Λ m l₀)))
    hwin.seamMem hwin.seamTime.symm hwin.blockPost 0 Cw
    (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    (chartWeightsReserveRestriction W (Nat.zero_le Npost)) Upre Tpre Tret
    (fun ξ i => hO.2.2.2.1 ξ 0 (Nat.zero_le _) i) (fun ξ i => hO.2.2.2.2.2.2.2.1 ξ 0 i) uphys wphys
    (fun ξ => twoUHpost hp hΛ hchart uphys' (wordDiag (blockWords Jpre H) ξ))
    (fun ξ => twoWHpost hp hΛ hchart wphys' (wordDiag (blockWords Jpre H) ξ))
    (hp.physical_exists hζ Npatch hNpatch patch uphys wphys hO.1) hO.2.1 hdiagSol
    (twoTp α q Λ m l₀) hwin.tpMem hτend (cellTime q Λ m ν (twoTp α q Λ m l₀)) rfl _ hF.2.2.2 Npost
    (twoEin hp hΛ hchart hζ Npatch hNpatch patch Npre) (twoCfirst hp Cw Cenergy1 Npre)
    (twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre)
    (twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre)
    (twoEpsPost hp Cw Cprep CR Cterminal Crem Npost Lpost Jpost)
    (fun ξ => le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_right
      (weightedFactorialNormSq_moment_mono hNle _ 0 _ (K i) _) _) (hO.2.2.1 ξ))
    (fun ξ => le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_right
      (weightedFactorialNormSq_moment_mono (Nat.zero_le Npost) _ 0 _ (K i) _) _)
      (hO.2.2.2.2.2.2.2.2 ξ))
    hO.2.2.2.2.2.2.2.2 (fun ξ => le_refl _)
  exact twoBlockWordGeometry_finish K ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m))
    (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
    (twoLoc hp hζ Npatch hNpatch patch) Jpre Jpost H (fun t => twoGpre hp t 0)
    (fun t => twoGpost hp t 0) (twoMpre hp θM₁ bM₁) (twoSpre hp θS₁ bS₁) (twoMpost hp θM₂ bM₂)
    (twoSpost hp θS₂ bS₂) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp)
    ((ocEpsilon q Λ (m - 1))⁻¹ • twoYcPost hp) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
    (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
    (cellTime q Λ m ν (twoTp α q Λ m l₀)) hwin.ab.le (ocCellDrift α q Λ ζ m ν (twoYc hp))
    (ocCellDrift α q Λ ζ m ν (twoYcPost hp)) (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch)
    (twoTransit hp hΛ hchart) (twoReturn hp hΛ hchart)
    (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m) r π
    (twoTp α q Λ m l₀) (cellTime q Λ m ν (twoTp α q Λ m l₀)) hτend _ Npost 0
    (twoUH hp hΛ hchart uphys) Bdpre hpre V₀' (twoUHpost hp hΛ hchart uphys') Bdpost hpost
    (fun η x => (hF.2.1 η x).trans (congrArg (twoTransit hp hΛ hchart x) (hO.2.2.2.2.1 η x)))
    uphys wphys hO.1
    (physicalBound_congr π r (twoTp α q Λ m l₀) uphys (twoReturn hp hΛ hchart) Tret _ _ hbound
      hF.2.2.1)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The constants of the seam on the two-block window**.

The word weight `Θ_w` of a word of the two block letters is at most `Cθ^{|w|}` when both letters'
`θ` lie in `[0, Cθ]` and `0 < ηg ≤ 1`; the seam's budget and price of an allocation (exponent
`Q_σ ≤ Q`, rate `c_σ ≥ c`, at most `4 + τ''/τ` regions, buffer `τ/(4ℓ²)`) are bounded by those of
the window (`seamWindowBudget`, `seamWindowPrice`). -/

section Theta

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ}

theorem wordTheta_nonneg_le {M S : CycleLetter ι h D} {ηg Cθ : ℝ} (hη0 : 0 < ηg) (hη1 : ηg ≤ 1)
    (hM0 : 0 ≤ M.theta) (hM1 : M.theta ≤ Cθ) (hS0 : 0 ≤ S.theta) (hS1 : S.theta ≤ Cθ)
    (w : List Bool) :
    0 ≤ wordTheta ηg (blockWordLetters M S w) ∧
      wordTheta ηg (blockWordLetters M S w) ≤ Cθ ^ w.length := by
  have hf : ∀ i : Fin w.length,
      0 ≤ (blockWordLetters M S w i).theta *
          (if (blockWordLetters M S w i).positive then ηg else 1) ∧
        (blockWordLetters M S w i).theta *
          (if (blockWordLetters M S w i).positive then ηg else 1) ≤ Cθ := by
    intro i
    refine blockWordLetters_forall (fun L => 0 ≤ L.theta * (if L.positive then ηg else 1) ∧
      L.theta * (if L.positive then ηg else 1) ≤ Cθ) ?_ ?_ w i
    · split_ifs
      · exact ⟨mul_nonneg hM0 hη0.le, (mul_le_of_le_one_right hM0 hη1).trans hM1⟩
      · exact ⟨by simpa using hM0, by simpa using hM1⟩
    · split_ifs
      · exact ⟨mul_nonneg hS0 hη0.le, (mul_le_of_le_one_right hS0 hη1).trans hS1⟩
      · exact ⟨by simpa using hS0, by simpa using hS1⟩
  unfold wordTheta
  refine ⟨Finset.prod_nonneg fun i _ => (hf i).1, ?_⟩
  calc ∏ i, (blockWordLetters M S w i).theta *
        (if (blockWordLetters M S w i).positive then ηg else 1)
      ≤ ∏ _i : Fin w.length, Cθ := Finset.prod_le_prod₀ (fun i _ => (hf i).1) fun i _ => (hf i).2
    _ = Cθ ^ w.length := by simp

end Theta

section Budget

variable {α q : ℝ} {Λ m : ℕ} {ν B : ℝ}

theorem one_le_peFactor (η : ℝ) : 1 ≤ peFactor η := by
  unfold peFactor
  have := inv_nonneg.2 (Real.sqrt_nonneg η)
  linarith

theorem pow_mul_pow_mono {P A : ℝ} {Q Qσ : ℕ} (hP : 1 ≤ P) (hA : 1 ≤ A) (hQ : Qσ ≤ Q) :
    0 ≤ P ^ Qσ * A ^ Qσ ∧ P ^ Qσ * A ^ Qσ ≤ P ^ Q * A ^ Q :=
  ⟨mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _),
    mul_le_mul (pow_le_pow_right₀ hP hQ) (pow_le_pow_right₀ hA hQ)
      (pow_nonneg (by linarith) _) (pow_nonneg (by linarith [one_le_pow₀ (n := Q) hP]) _)⟩

theorem exp_neg_mul_anti {c cσ b : ℝ} (hc : c ≤ cσ) (hb : 0 ≤ b) :
    Real.exp (-cσ * b) ≤ Real.exp (-c * b) :=
  Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_right hc hb; linarith)

/-- The seam's budget of an allocation from the window's budget. -/
theorem seamBudget_of_window {Q Qσ : ℕ} {c cσ : ℝ} (hQ : Qσ ≤ Q) (hc : c ≤ cσ)
    {joins : ℕ} (hj : (joins : ℝ) ≤ ocTauPP α q Λ m / ocTau α q Λ m + 4)
    (hS : 0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) (hb : 0 ≤ seamBuffer α q Λ m ν)
    (hbudget : seamWindowBudget α q Λ m ν B Q c ≤ 1) :
    peFactor (ν / B) ^ Qσ * (1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ Qσ * (1 + joins) *
      Real.exp (-cσ * seamBuffer α q Λ m ν) ≤ 1 := by
  refine le_trans ?_ hbudget
  unfold seamWindowBudget
  obtain ⟨h0, h1⟩ := pow_mul_pow_mono (one_le_peFactor (ν / B))
    (show (1 : ℝ) ≤ 1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 by linarith) hQ
  have hJ0 : (0 : ℝ) ≤ 1 + joins := by positivity
  exact mul_le_mul (mul_le_mul h1 (by linarith) hJ0 (h0.trans h1)) (exp_neg_mul_anti hc hb)
    (Real.exp_pos _).le (mul_nonneg (h0.trans h1) (by linarith))

/-- The seam's price of an allocation is nonnegative and at most the window's price. -/
theorem seamPrice_le_window {Q Qσ Ns : ℕ} {c cσ : ℝ} (hQ : Qσ ≤ Q) (hc : c ≤ cσ)
    {joins : ℕ} (hj : (joins : ℝ) ≤ ocTauPP α q Λ m / ocTau α q Λ m + 4) {buf : ℝ}
    (hbuf : buf = seamBuffer α q Λ m ν)
    (hS : 0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) (hb : 0 ≤ seamBuffer α q Λ m ν)
    (ha : 0 ≤ (ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2) :
    0 ≤ peFactor (ν / B) ^ Qσ * (1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ Qσ *
        (Real.exp (-cσ * (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)) +
          (1 + joins) * Real.exp (-cσ * buf) +
          Real.exp (-cσ * ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2)) +
          (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ (-(Ns : ℝ) / 2)) ∧
    peFactor (ν / B) ^ Qσ * (1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ Qσ *
        (Real.exp (-cσ * (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)) +
          (1 + joins) * Real.exp (-cσ * buf) +
          Real.exp (-cσ * ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2)) +
          (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ (-(Ns : ℝ) / 2)) ≤
      seamWindowPrice α q Λ m ν B Q Ns c := by
  subst hbuf
  unfold seamWindowPrice
  obtain ⟨h0, h1⟩ := pow_mul_pow_mono (one_le_peFactor (ν / B))
    (show (1 : ℝ) ≤ 1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 by linarith) hQ
  have hJ0 : (0 : ℝ) ≤ 1 + joins := by positivity
  have hs := Real.rpow_nonneg hS (-(Ns : ℝ) / 2)
  have e1 := exp_neg_mul_anti hc hS
  have e2 := exp_neg_mul_anti hc hb
  have e3 := exp_neg_mul_anti hc ha
  have hsum : Real.exp (-cσ * (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)) +
        (1 + joins) * Real.exp (-cσ * seamBuffer α q Λ m ν) +
        Real.exp (-cσ * ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2)) +
        (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ (-(Ns : ℝ) / 2) ≤
      Real.exp (-c * (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)) +
        (5 + ocTauPP α q Λ m / ocTau α q Λ m) * Real.exp (-c * seamBuffer α q Λ m ν) +
        Real.exp (-c * ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2)) +
        (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ (-(Ns : ℝ) / 2) := by
    have := mul_le_mul (show (1 : ℝ) + joins ≤ 5 + ocTauPP α q Λ m / ocTau α q Λ m by linarith)
      e2 (Real.exp_pos _).le (by linarith)
    linarith
  have hpos : 0 ≤ Real.exp (-cσ * (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)) +
        (1 + joins) * Real.exp (-cσ * seamBuffer α q Λ m ν) +
        Real.exp (-cσ * ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2)) +
        (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ (-(Ns : ℝ) / 2) := by
    have := Real.exp_pos (-cσ * (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2))
    have := Real.exp_pos (-cσ * ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2))
    have := mul_nonneg hJ0 (Real.exp_pos (-cσ * seamBuffer α q Λ m ν)).le
    linarith
  exact ⟨mul_nonneg h0 hpos, mul_le_mul h1 hsum hpos (h0.trans h1)⟩

theorem seamWindowPrice_nonneg (hΛ : 1 ≤ Λ) {Q Ns : ℕ} {c : ℝ}
    (hS : 0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) : 0 ≤ seamWindowPrice α q Λ m ν B Q Ns c := by
  have hP := one_le_peFactor (ν / B)
  unfold seamWindowPrice
  refine mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)) ?_
  have := Real.exp_pos (-c * (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2))
  have := Real.exp_pos (-c * ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2))
  have h5 : (0 : ℝ) ≤ 5 + ocTauPP α q Λ m / ocTau α q Λ m := by
    have := Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
    have := (Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ).le
    positivity
  have := mul_nonneg h5 (Real.exp_pos (-c * seamBuffer α q Λ m ν)).le
  have := Real.rpow_nonneg hS (-(Ns : ℝ) / 2)
  linarith

end Budget

section Generic

/-- Raising the real factor of a bound. -/
theorem ennreal_bound_mono {X Y : ℝ≥0∞} {a b : ℝ} (hab : a ≤ b)
    (h : X ≤ ENNReal.ofReal a * Y) : X ≤ ENNReal.ofReal b * Y :=
  h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hab) _)

/-- Two word weights in `[0, C^n]`, `[0, C^k]` multiply to one in `[0, C^{n+k}]`. -/
theorem theta_pair_le {a b C : ℝ} {n k : ℕ} (hC : 0 ≤ C) (h1 : 0 ≤ a ∧ a ≤ C ^ n)
    (h2 : 0 ≤ b ∧ b ≤ C ^ k) : 0 ≤ a * b ∧ a * b ≤ C ^ (n + k) :=
  ⟨mul_nonneg h1.1 h2.1, (pow_add C n k).symm ▸ mul_le_mul h1.2 h2.2 h2.1 (pow_nonneg hC _)⟩

/-- The error constant of an allocation: `CN Θ P A S ≤ CN C price`. -/
theorem error_const_le {CN Θ C P A S price : ℝ} (hCN : 0 ≤ CN) (hΘ : 0 ≤ Θ ∧ Θ ≤ C)
    (hpr : 0 ≤ P * A * S ∧ P * A * S ≤ price) : CN * Θ * P * A * S ≤ CN * C * price := by
  calc CN * Θ * P * A * S = CN * Θ * (P * A * S) := by ring
    _ ≤ CN * C * price :=
      mul_le_mul (mul_le_mul_of_nonneg_left hΘ.2 hCN) hpr.2 hpr.1
        (mul_nonneg hCN (hΘ.1.trans hΘ.2))

end Generic

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The energy of the cell datum by the prepared norm**.

The prices of the two-block theorem multiply `twoEin N` (the moment-`N` energy of the cell datum at radius `r/ε`), and the
error of the one-patch statement is measured by the prepared norm `Σ π⁻¹ |loc f|²_{ρold}`. With the cover centred at the
transported patch centre and `8 ≤ N R`, the localized initial energy in the reference chart
(`preparationReference_localized_initial_family_return_energy_le`) gives
`ε² twoEin N ≤ (1 + 2 (B₁/8)²)^N C_comp² Σ π⁻¹ |loc f|²_r`, and the radius conversion
(`r ≤ Lr ρold`, `Lr = max 1 (Crat E^{-qδ})`, from `hρrat`) gives
`Σ π⁻¹ |loc f|²_r ≤ Lr^{2 Kmax} Σ π⁻¹ |loc f|²_{ρold}`.

For an empty index type both sides are `0`, and for `N = 0` the moment factor is `1`. When all
slots are `0` only the value counts, so the radius conversion costs nothing (`Lr^0 = 1`). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev Set
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
  AVRegularity.CycleReference
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

section Datum

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- The price of the cell datum's energy at moment order `N`. -/
def datumEnergyPrice (Cchart : ℕ → ℝ) (E : ℝ) (Jchart N : ℕ) : ℝ :=
  (1 + 2 * (preparationPieceFlowJetBudget Cchart E 1 * (1 / 8)) ^ 2) ^ N *
    compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) ^ 2

theorem datumEnergyPrice_nonneg (Cchart : ℕ → ℝ) (E : ℝ) (Jchart N : ℕ) :
    0 ≤ datumEnergyPrice Cchart E Jchart N := by
  unfold datumEnergyPrice
  positivity

/-- **The energy of the cell datum** of a recentred patch. -/
theorem twoEin_le (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (hNR : 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m)) (Nm : ℕ)
    (ξ : ∀ i, TorusHk (K i) (h i)) :
    ENNReal.ofReal (ocEpsilon q Λ m ^ 2) *
        twoEin hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) Nm ξ ≤
      ENNReal.ofReal (datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Nm *
        ∑ i, (π i)⁻¹ * factorialNormSq r
          (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (ξ i)).val) := by
  subst hyc
  have hεpos : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hRpos : 0 < Real.sqrt (B * ocTauPP α q Λ m) :=
    Real.sqrt_pos.2 (mul_pos hp.cov.pos.2.1 (Construction.Stream.ocTauPP_pos hΛ))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmesh : ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ m / (N : ℝ) ≤
      1 / 8 := by
    have e : ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ m / (N : ℝ) =
        1 / ((N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m)) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h := preparationReference_localized_initial_family_return_energy_le hp.hprep hp.hcover
    (Construction.Stream.ocTauPP_pos hΛ).le (ocA_nonneg_of hΛ (m - 1))
    (Construction.Stream.ocEpsilon_pos hΛ) K (slot_le_chart hp.hK hchart) (twoWindow_le hΛ tS) hζ
    N hN (fun k => (j k : ℤ)) ξ π Nm (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (1 / 8)
    r (ocEpsilon q Λ m) 1 hεpos.ne' (div_nonneg (div_pos hεpos hRpos).le hεpos.le)
    (by norm_num) hmesh hp.cov.pos.2.2.le (hp.cov.rho_e.trans heE)
  have hS : ∑ i, ENNReal.ofReal ((π i)⁻¹) * ENNReal.ofReal (factorialNormSq r
      (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (ξ i)).val) =
      ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq r
        (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (ξ i)).val) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
      mul_nonneg (inv_nonneg.2 (hp.hπ i).le) (factorialNormSq_nonneg _ _)]
    exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_mul (inv_nonneg.2 (hp.hπ i).le)).symm
  unfold twoEin twoV₀
  rw [twoYc_eq hp]
  calc ENNReal.ofReal (ocEpsilon q Λ m ^ 2) * _
      = ENNReal.ofReal ((1 * |ocEpsilon q Λ m|) ^ 2) * _ := by rw [one_mul, sq_abs]; rfl
    _ ≤ _ := h
    _ = _ := by
      rw [hS, one_pow, ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      rfl

/-- **The radius conversion of the prepared norm** (`hρrat`). -/
theorem prepared_radius_le
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (U : ∀ i, PlaneHk Set.univ (K i) (h i)) :
    ∑ i, (π i)⁻¹ * factorialNormSq r (U i).val ≤
      max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))) ^ (2 * Kmax) *
        ∑ i, (π i)⁻¹ * factorialNormSq ρold (U i).val := by
  set L := max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hrL : r ≤ L * ρold := by
    have h1 : r / ρold ≤ L := hp.hρrat.trans (le_max_right _ _)
    rwa [div_le_iff₀ hp.hρpos] at h1
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hc := factorialNormSq_radius_conversion hp.cov.pos.2.2.le hL1 hrL (U i).val
  have hpow : L ^ (2 * K i) ≤ L ^ (2 * Kmax) :=
    pow_le_pow_right₀ hL1 (Nat.mul_le_mul_left 2 (hp.hK i))
  have hπ : 0 ≤ (π i)⁻¹ := inv_nonneg.2 (hp.hπ i).le
  have hf : 0 ≤ factorialNormSq ρold (U i).val := factorialNormSq_nonneg _ _
  calc (π i)⁻¹ * factorialNormSq r (U i).val
      ≤ (π i)⁻¹ * (L ^ (2 * K i) * factorialNormSq ρold (U i).val) :=
        mul_le_mul_of_nonneg_left hc hπ
    _ ≤ (π i)⁻¹ * (L ^ (2 * Kmax) * factorialNormSq ρold (U i).val) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hf) hπ
    _ = L ^ (2 * Kmax) * ((π i)⁻¹ * factorialNormSq ρold (U i).val) := by ring

end Datum

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The `L²` norm of the cell datum**.

The model bound of the one-patch statement is in terms of the `L²` norm of the slot-`0` localization of the truncated datum,
and the seam's model bound in terms of `momentNorm π 0 ϖ` of the values of the cell datum `twoV₀`.
They agree up to the volume factor of the cell scaling:
`momentNorm π 0 ϖ (value ∘ twoV₀ ξ)² = ε⁻² Σ π⁻¹ ‖loc⁰ (trunc₀ ξ_i)‖²`
(the flow pull is measure preserving; the affine map `z ↦ yc + ε z` costs `ε⁻²`; truncation and
localization keep the value).

Also `weightedFactorialNormSq_truncate_le`: truncation does not increase a weighted factorial
energy of any order (the jets above the truncation order read as `0`).

For an empty index type both sides are `0`; when all slots are `0` the truncation is the identity. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev Set
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
  AVRegularity.CycleReference AVRegularity.CoupledEnergyPlane.Fourier
  AVRegularity.Analysis.Convolution
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- Truncation does not increase a weighted factorial energy of any order. -/
theorem weightedFactorialNormSq_truncate_le {K L : ℕ} (hKL : K ≤ L) (U : PlaneHk Set.univ L E)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (r : ℝ) (M : ℕ) :
    weightedFactorialNormSq n ϖ zc r M (truncatePlaneHk hKL U) ≤
      weightedFactorialNormSq n ϖ zc r M U := by
  unfold weightedFactorialNormSq
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j ≤ K
  · simp_rw [planeJetOrder_truncate hKL hj U]
    exact le_rfl
  · have h0 : ∀ w : DerivativeWord2 j, planeJetOrder (truncatePlaneHk hKL U) j w = 0 := by
      intro w
      funext z
      simp only [planeJetOrder, hj, ↓reduceDIte, Pi.zero_apply]
    simp_rw [h0, Pi.zero_apply, norm_zero]
    simp

omit [FiniteDimensional ℝ E] in
/-- The value of a plane carrier in `L²` is its value component. -/
theorem planeHkValueOperator_norm {K : ℕ} (V : PlaneHk Set.univ K E) :
    ‖planeHkValueOperator K V‖ = ‖V.val (valueIndex2 K)‖ := by
  rw [planeHkValueOperator_apply]
  exact univToPlane.norm_map _

omit [FiniteDimensional ℝ E] in
/-- The `L²` norm of the value function. -/
theorem eLpNorm_planeValue {K : ℕ} (V : PlaneHk Set.univ K E) :
    eLpNorm (planeValue V) 2 volume = ENNReal.ofReal ‖planeHkValueOperator K V‖ := by
  rw [← eLpNorm_congr_ae (planeValueLp_ae V), Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

/-- The window chart pull keeps the `L²` norm of the value. -/
theorem planeHkWindowChartPull_value_norm {K : ℕ} (a b : ℝ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ t ∈ Icc a b, ∀ j, 1 ≤ j → j ≤ K → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => streamFlow φ hφ t y s) x‖ ≤ B j)
    (t : ℝ) (ht : t ∈ Icc a b) (U : PlaneHk Set.univ K E) :
    ‖planeHkValueOperator K (planeHkWindowChartPull a b hφ s B hB hb t U)‖ =
      ‖planeHkValueOperator K U‖ := by
  rw [planeHkWindowChartPull_value_eq a b hφ s B hB hb t ht U]
  exact LinearIsometry.norm_map _ _

omit [FiniteDimensional ℝ E] in
/-- The affine cell scaling multiplies the squared `L²` norm of the value by `|e²|⁻¹`. -/
theorem planeCarrierAffine_value_norm_sq {K : ℕ} (e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (U : PlaneHk Set.univ K E) :
    ‖planeHkValueOperator K (planeCarrierAffine e he yc U)‖ ^ 2 =
      |(e ^ 2)⁻¹| * ‖planeHkValueOperator K U‖ ^ 2 := by
  rw [planeHkValueOperator_norm, planeHkValueOperator_norm,
    planeCarrierAffine_component_norm_sq e he yc U (valueIndex2 K)]
  simp [valueIndex2, valueIndex]

/-- The slot-`0` localization of the truncated datum has the `L²` norm of the value of the
slot-`K` localization. -/
theorem spatialPatchLocalizationCLM_truncate_norm_sq {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N) {K : ℕ} (f : TorusHk K E) :
    ‖spatialPatchLocalizationCLM hζ N hN j (truncateTorusHk (Nat.zero_le K) f)‖ ^ 2 =
      ‖planeHkValueOperator K (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) K f)‖ ^ 2 := by
  rw [planeHkValueOperator_norm]
  change ‖(spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0
      (truncateTorusHk (Nat.zero_le K) f)).val‖ ^ 2 = _
  rw [zeroOrderJet_norm_sq]
  change ‖(localizeTorusCarrier (truncateTorusHk (Nat.zero_le K) f) _ _ _).val (valueIndex2 0)‖ ^ 2 =
    ‖(localizeTorusCarrier f _ _ _).val (valueIndex2 K)‖ ^ 2
  rw [localizeTorusCarrier_component_norm_sq, localizeTorusCarrier_component_norm_sq]
  simp_rw [multiplicationRawJet_value]
  rfl

end Carrier

section Datum

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- The value of the cell datum in `L²`: `ε⁻²` times that of the localized datum. -/
theorem twoV₀_value_norm_sq (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ) (ξ : ∀ i, TorusHk (K i) (h i))
    (i : ι) :
    ‖planeHkValueOperator (K i) (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ i)‖ ^ 2 =
      |(ocEpsilon q Λ m ^ 2)⁻¹| *
        ‖planeHkValueOperator (K i) (spatialPatchLocalization hζ Npatch hNpatch patch (K i)
          (ξ i))‖ ^ 2 := by
  unfold twoV₀
  rw [preparationReferenceCellLocalizedInitialFamilyLinearMap_apply,
    planeCarrierAffine_value_norm_sq]
  congr 2
  exact planeHkWindowChartPull_value_norm _ _ hφ _ _ _ _ tS ⟨le_rfl, twoWindow_le hΛ tS⟩ _

/-- The order-`0` moment norm is the mass-weighted `L²` norm, whatever its scale. -/
theorem momentNorm_zero_sq {ι' : Type*} [Fintype ι'] {h' : ι' → Type*}
    [∀ i, NormedAddCommGroup (h' i)] [∀ i, NormedSpace ℝ (h' i)] (π' : ι' → ℝ) (s : ℝ)
    (G : ∀ v, Vec 2 → h' v) :
    momentNorm π' 0 s G ^ 2 = ∑ v, ENNReal.ofReal ((π' v)⁻¹) * eLpNorm (G v) 2 volume ^ 2 := by
  have hidx : momentIndices 0 = {(0, 0)} := by decide
  simp only [momentNorm, hidx, Finset.sum_singleton, pow_zero, one_smul, Nat.factorial_zero,
    mul_one, Nat.cast_one, inv_one, ENNReal.ofReal_one, one_mul]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **The `L²` norm of the cell datum**: `momentNorm π 0 ϖ (value ∘ twoV₀ ξ)² = ε⁻² Σ π⁻¹ ‖loc⁰‖²`. -/
theorem twoV₀_momentNorm_sq (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart)
    (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N) (ξ : ∀ i, TorusHk (K i) (h i)) (s : ℝ) :
    momentNorm π 0 s (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)) ^ 2
      = ENNReal.ofReal ((ocEpsilon q Λ m ^ 2)⁻¹ * ∑ i, (π i)⁻¹ *
          ‖spatialPatchLocalizationCLM hζ N hN j (truncateTorusHk (Nat.zero_le (K i)) (ξ i))‖ ^ 2) := by
  have hε : 0 ≤ (ocEpsilon q Λ m ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
  rw [momentNorm_zero_sq, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    mul_nonneg hε (mul_nonneg (inv_nonneg.2 (hp.hπ i).le) (sq_nonneg _)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eLpNorm_planeValue, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (inv_nonneg.2 (hp.hπ i).le), twoV₀_value_norm_sq,
    spatialPatchLocalizationCLM_truncate_norm_sq, abs_of_nonneg hε]
  congr 1
  ring

end Datum

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The seam allocation: preliminary statements**.

The seam (`cycle_seam`) is applied to the word chains of the two-block theorem on the two blocks. Three adaptations are
needed before the instantiation:

* `PackageBufferShrinkStatement`: a scalar package stays a package when its quiet buffer is
  shrunk (every field is monotone in `reg.buffer`); the seam's `hseam` asks the old block's last
  quiet stretch to contain the future buffer, so the buffer is shrunk to that stretch.
* `CoupledPlaneCongrStatement`, `PlaneChainMetricCongrStatement`: a plane solution, and a word
  chain, depend on the drift and the coefficients (the metric) only on the time window.
* `ClampedMetricStatement`: the seam and the scalar packages ask the frozen cell metric to be a
  cell metric near the identity at EVERY time, while the cover controls the chart metric on the
  chart's anchor window only; the metric frozen at the centre and clamped in time to a subwindow
  `[a, b]` of that window has both properties and agrees with the chart metric on `[a, b]`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleJointProofs
open scoped ENNReal

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

/-- **Shrinking the quiet buffer of a scalar package.** -/
def PackageBufferShrinkStatement : Prop :=
  ∀ (K : ScalarConstants) (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (t₀ S ϖ : ℝ) (reg : BlockRegions) (b : ℝ), 0 ≤ b → b ≤ reg.buffer →
    (CoreScalarPackage K η G v t₀ S ϖ reg →
      Nonempty (CoreScalarPackage K η G v t₀ S ϖ { reg with buffer := b })) ∧
    (ScalarPackage K η G v t₀ S ϖ reg →
      Nonempty (ScalarPackage K η G v t₀ S ϖ { reg with buffer := b }))

/-- **A plane solution depends on its drift and coefficients only on the time window.** -/
def CoupledPlaneCongrStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (ν t₀ t₁ : ℝ) (vd vd' : ℝ → Vec 2 → Vec 2) (D : ℕ) (K : ι → ℕ)
    (A A' : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (U : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (W : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    (∀ s ∈ Set.Icc t₀ t₁, vd s = vd' s) →
    (∀ i i' d, ∀ s ∈ Set.Icc t₀ t₁, A i i' d s = A' i i' d s) →
    IsCoupledWeakSolutionPlane ν t₀ t₁ vd D K A f F g U W →
    IsCoupledWeakSolutionPlane ν t₀ t₁ vd' D K A' f F g U W

/-- **A word chain depends on its frozen metric only on the time window.** -/
def PlaneChainMetricCongrStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
    (G G' : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (letters : Fin Nw → CycleLetter ι h D) (X₀ : Vec 2)
    (δ : ℝ) (κ : Fin (Nw + 1) → ι → ℕ) (t₀ t₁ : ℝ) (vd : ℝ → Vec 2 → Vec 2)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (F : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (uc : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (wc : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    (∀ s ∈ Set.Icc t₀ t₁, G s = G' s) →
    IsPlaneChain (wordChainData G letters X₀ δ) κ t₀ t₁ vd f F uc wc →
    IsPlaneChain (wordChainData G' letters X₀ δ) κ t₀ t₁ vd f F uc wc

/-- The chart metric of the chart `ic`, frozen at the centre and clamped in time to `[a, b]`. -/
def clampedFrozenMetric (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (l₀ : ℤ) (P : ℕ) (ν : ℝ) (y₀ : Vec 2) (ic : Fin (P + 2)) (a b : ℝ) :
    ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun t => windowCoverCellMetric α q Λ m φ hφ l₀ P ν y₀ ic (max a (min b t)) 0

/-- **The clamped frozen metric is a cell metric near the identity.** -/
def ClampedMetricStatement : Prop :=
  ∀ {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (_hΛ : 1 ≤ Λ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (_cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (ic : Fin (P + 2)) (a b : ℝ), a ≤ b →
    Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P ic → g ≤ 1 / 2 →
    IsCellMetric (fun t _ => clampedFrozenMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic a b t) ∧
    IsMetricNearIdentity (fun t _ => clampedFrozenMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic a b t)
      g ∧
    ∀ t ∈ Set.Icc a b, clampedFrozenMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic a b t =
      windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic t 0

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs.Assembly

/-! Shrinking a quiet buffer restricts the agreement intervals and weakens the exponential
replacement price. The actual and extended scalar histories remain the same. -/

private theorem seamBufferPrice_mono {c C b B : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hb : b ≤ B) : C * Real.exp (-c * B) ≤ C * Real.exp (-c * b) :=
  mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hb (neg_nonpos.mpr hc))) hC

private def seamCoreBufferShrink {K : ScalarConstants} {η : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {t₀ S ϖ : ℝ}
    {reg : BlockRegions} (P : CoreScalarPackage K η G v t₀ S ϖ reg)
    (b : ℝ) (hb : 0 ≤ b) (hB : b ≤ reg.buffer) :
    CoreScalarPackage K η G v t₀ S ϖ { reg with buffer := b } where
  consts_pos := P.consts_pos
  actual := P.actual
  contraction := P.contraction
  high_smoothing := P.high_smoothing
  quiet_zero := P.quiet_zero
  quiet_mean := P.quiet_mean
  quiet_gap := P.quiet_gap
  cover := P.cover
  buffer_nonneg := hb
  buffer_le := hB.trans P.buffer_le
  joins_ge := P.joins_ge
  buffer_inside := fun p t ht => P.buffer_inside p
    ⟨(sub_le_sub_left hB _).trans ht.1, ht.2.trans (add_le_add_right hB _)⟩
  buffer_quiet := fun p =>
    ⟨fun t ht => (P.buffer_quiet p).1
      ⟨(sub_le_sub_left hB _).trans ht.1, ht.2⟩,
     fun t ht => (P.buffer_quiet p).2
      ⟨ht.1, ht.2.trans (add_le_add_right hB _)⟩⟩
  ext := P.ext
  ext_local := P.ext_local
  ext_shear := P.ext_shear
  ext_drift := P.ext_drift
  ext_agree := fun p t ht => P.ext_agree p t
    ⟨(sub_le_sub_left hB _).trans ht.1, ht.2.trans (add_le_add_right hB _)⟩
  replace_graph := by
    intro j p ξ hξ hsmall t ht
    have hpos := P.consts_pos.2.2.2.2.2.2.2.1 j
    refine (P.replace_graph j p ξ hξ hsmall t
      ⟨ht.1, ht.2.trans (add_le_add_right hB _)⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    apply seamBufferPrice_mono hpos.2.le _ hB
    exact mul_nonneg (mul_nonneg hpos.1.le (pow_nonneg
      (by unfold peFactor; positivity) _)) (Real.sqrt_nonneg _)
  replace_row := by
    intro j p ξ hξ hsmall t ht
    have hpos := P.consts_pos.2.2.2.2.2.2.2.1 j
    refine (P.replace_row j p ξ hξ hsmall t
      ⟨(sub_le_sub_left hB _).trans ht.1, ht.2⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    apply seamBufferPrice_mono hpos.2.le _ hB
    exact mul_nonneg (mul_nonneg hpos.1.le (pow_nonneg
      (by unfold peFactor; positivity) _)) (Real.sqrt_nonneg _)
  replace_symbol := by
    intro p ξ hξ hsmall t ht
    have hpos := P.consts_pos.2.2.2.2.2.2.2.1 0
    refine (P.replace_symbol p ξ hξ hsmall t
      ⟨ht.1, ht.2.trans (add_le_add_right hB _)⟩).trans ?_
    apply seamBufferPrice_mono hpos.2.le _ hB
    exact mul_nonneg (mul_nonneg hpos.1.le (pow_nonneg
      (by unfold peFactor; positivity) _)) (sq_nonneg _)
  weights := P.weights
  neg_adjoint := P.neg_adjoint

/-- Both scalar packages retain their original histories when their buffer shrinks. -/
theorem packageBufferShrink : PackageBufferShrinkStatement := by
  intro K η G v t₀ S ϖ reg b hb hB
  refine ⟨fun P => ⟨seamCoreBufferShrink P b hb hB⟩, fun P => ?_⟩
  exact ⟨{
    toCoreScalarPackage := seamCoreBufferShrink P.toCoreScalarPackage b hb hB
    gauss := by simpa only [seamCoreBufferShrink] using P.gauss
    phase_jets := by simpa only [seamCoreBufferShrink] using P.phase_jets
    marks_in := P.marks_in
    marks_sep := P.marks_sep
    marks_count := P.marks_count
    high_marks := P.high_marks }⟩

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! Drift and coefficient changes outside the solution window preserve the plane weak identity
and the word chain. No ordering or nonemptiness assumption on the window is needed. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleWords

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

private theorem seamWeakIdentity_congr_drift {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {μ : Measure (Vec 2)} {ν t₀ t : ℝ}
    {v v' : ℝ → Vec 2 → Vec 2} {u₀ f φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H}
    {du : ℝ → Fin 2 → Vec 2 → H}
    {flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g : ℝ → Vec 2 → H}
    (hv : ∀ s ∈ Set.Ioc t₀ t, v s = v' s)
    (h : CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du flux F g) :
    CoupledWeakIdentity μ ν t₀ t v' u₀ f φ dφ du flux F g := by
  unfold CoupledWeakIdentity at h ⊢
  dsimp only at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, fun s hs => by rw [← hv s hs]; exact h3 s hs, ?_, ?_⟩
  · exact h4.congr_fun (fun s hs => by simp only [hv s hs]) measurableSet_Ioc
  · rw [h5]
    exact setIntegral_congr_fun measurableSet_Ioc (fun s hs => by simp only [hv s hs])

/-- The coupled plane solution sees its drift and coefficients only on its time window. -/
theorem coupledPlaneCongr : CoupledPlaneCongrStatement.{u, v} := by
  intro ι _ h _ _ _ _ _ _ ν t₀ t₁ vd vd' D K A A' f F g U W hv hA hsol
  have hc := isCoupledWeakSolutionPlane_congr_coeff
    (fun i i' d s hs => (hA i i' d s hs).symm) hsol
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  refine ⟨h1, h2, h3, h4, fun i t ht φ => seamWeakIdentity_congr_drift ?_ (h5 i t ht φ)⟩
  intro s hs
  exact hv s ⟨hs.1.le, hs.2.trans ht.2⟩

/-- A word chain sees the frozen metric only on its time window. -/
theorem planeChainMetricCongr : PlaneChainMetricCongrStatement.{u, v} := by
  intro ι _ h _ _ _ _ _ _ D Nw G G' letters X₀ δ κ t₀ t₁ vd f F uc wc hG hsol
  unfold IsPlaneChain at hsol ⊢
  refine coupledPlaneCongr (ι := Fin (Nw + 1) × ι) (h := fun p => h p.2) 1 t₀ t₁ vd vd D (fun p => κ p.1 p.2)
    _ _ _ _ _ _ _
    (fun _ _ => rfl) (fun i i' d s hs => ?_) hsol
  funext z
  simp only [planeChainCoefficient, wordChainData, hG s hs]

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.CycleJointProofs
namespace AVRegularity.CycleJointProofs.Assembly

/-! The frozen chart metric, evaluated at the centre and clamped to a chart subwindow,
is globally admissible and agrees with the original metric on that subwindow. -/

private theorem seamNearIdentity_cellBounds
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {g : ℝ}
    (hg : g ≤ 1 / 2) (hG : IsMetricNearIdentity G g) (t : ℝ) (z ξ : Vec 2) :
    (1 / 2) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * G t z i j * ξ j ∧
      ∑ i, ∑ j, ξ i * G t z i j * ξ j ≤ 2 * ∑ i, ξ i ^ 2 := by
  have h := hG t z ξ
  have hid : (∑ i, ∑ j, ξ i * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j * ξ j) =
      ∑ i, ξ i ^ 2 := by simp [Matrix.one_apply, pow_two]
  have hsub : (∑ i, ∑ j, ξ i * (G t z - 1) i j * ξ j) =
      (∑ i, ∑ j, ξ i * G t z i j * ξ j) - ∑ i, ξ i ^ 2 := by
    simp only [Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib, hid]
  rw [hsub, abs_le] at h
  have he : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (ξ i))
  have hge := mul_le_mul_of_nonneg_right hg he
  constructor <;> linarith

/-- Clamping the centre-frozen metric to a chart subwindow gives a global cell metric. -/
theorem clampedMetric : ClampedMetricStatement := by
  intro α q Λ m ζ Φ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀
    _hΛ hφ cov ic a b hab hwindow hg
  have htime (t : ℝ) : max a (min b t) ∈ Set.Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hnear : IsMetricNearIdentity
      (fun t _ => clampedFrozenMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic a b t) g := by
    intro t z ξ
    exact cov.metric_near ic _ (hwindow (htime t)) 0 ξ
  refine ⟨⟨?_, ?_, ?_, seamNearIdentity_cellBounds hg hnear⟩, hnear, ?_⟩
  · apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    have hc := (ocCellMetric_joint_contDiff α q Λ m hφ (l₀ - 1 + ic) ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic) i j).continuous
    have hm : Continuous (fun p : ℝ × Vec 2 => (max a (min b p.1), (0 : Vec 2))) := by
      fun_prop
    exact (hc.comp hm).measurable
  · intro t z k
    rfl
  · intro t z
    exact ocCellMetric_symmetric α q Λ m hφ (l₀ - 1 + ic) ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic) _ 0
  · intro t ht
    simp only [clampedFrozenMetric, min_eq_right ht.2, max_eq_right ht.1]

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The seam price of the two-block window in powers of `E`**.

With the scale ledger (`b1_scale_ledger`): the Péclet factor `peFactor (ν/B) = 1 + √(B/ν) ≤ 2 C
E^{-qγ}`, the block `S = τ''/ℓ² ≥ C⁻¹ E^{-6δ}`, the pulse `τ/ℓ² ≥ C⁻¹ E^{-4δ}`, the pulse count
`τ''/τ ≤ C E^{-2δ}`, and the trimmed quiet margin `(τ' - τ/24)/ℓ² ≥ τ/ℓ²` (`τ' = L τ`, `L ≥ 5`). The
abstract seam price (`seamPrice_abstract`) then gives `seamWindowPrice ≤ Cs E^a` for any
`a`, with `Ns` chosen from `Q` and `a`, and the budget `seamWindowBudget ≤` the price.

For `a ≤ 0` the bound is a constant. -/

/-- The trimmed quiet margin contains a pulse: `τ ≤ τ' - τ/24`. -/
theorem ocTau_le_trimmedQuietMargin {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) :
    ocTau α q Λ m ≤ ocTauP α q Λ m - ocTau α q Λ m / 24 := by
  have hT := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ
  have hE := Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ
  have hceil : 1 ≤ ⌈ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)⌉₊ :=
    Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hE _)).ne'
  have hL5 : (5 : ℝ) ≤ ocL α q Λ m := by
    have : 5 ≤ ocL α q Λ m := by unfold ocL; omega
    exact_mod_cast this
  have hLp : (0 : ℝ) < ocL α q Λ m := by linarith
  have hτ : ocTauP α q Λ m = ocL α q Λ m * ocTau α q Λ m := by
    unfold ocTau ocTauP
    field_simp
  have hτ0 : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ
  rw [hτ]
  nlinarith

/-- The budget of the seam is at most its price. -/
theorem seamWindowBudget_le_price {α q : ℝ} {Λ m : ℕ} {ν B : ℝ} (hΛ : 1 ≤ Λ)
    (Q Ns : ℕ) (c : ℝ) :
    seamWindowBudget α q Λ m ν B Q c ≤ seamWindowPrice α q Λ m ν B Q Ns c := by
  have hP := one_le_peFactor (ν / B)
  have hS : 0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 :=
    div_nonneg (Construction.Stream.ocTauPP_pos hΛ).le (sq_nonneg _)
  unfold seamWindowBudget seamWindowPrice
  rw [mul_assoc (peFactor (ν / B) ^ Q * (1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ Q)]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (pow_nonneg (by linarith) _)
    (pow_nonneg (by linarith) _))
  have h1 := Real.exp_pos (-c * (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2))
  have h2 := Real.exp_pos (-c * ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2))
  have h3 := Real.rpow_nonneg hS (-(Ns : ℝ) / 2)
  linarith

/-- **The seam price of the two-block window.** -/
theorem seamWindowPrice_ledger {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ (Q : ℕ) (a : ℝ),
    ∃ Ns : ℕ, 1 ≤ Ns ∧ ∀ c : ℝ, 0 < c → ∃ Cs : ℝ, 0 ≤ Cs ∧
    ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
    ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B → 0 < ν →
      ocEll q Λ m ν ^ 2 ≤ ocTauPP α q Λ m →
      seamWindowPrice α q Λ m ν B Q Ns c ≤ Cs * ocEpsilon q Λ (m - 1) ^ a := by
  obtain ⟨C, hC1, Λ₀, hΛ₀, hL⟩ := b1_scale_ledger hα0 hα1 hs0 hs1 hq hζ
  have hex := Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have hδ : 0 < ocDelta α q := hex.2.1
  have hqγ : 0 ≤ q * ocGamma α q := mul_nonneg (lt_trans zero_lt_one hq.1).le hex.1.le
  refine ⟨Λ₀, hΛ₀, fun Q a => ?_⟩
  obtain ⟨Ns, hNs, hP⟩ := seamPrice_abstract Q (qγ := q * ocGamma α q) (a := a) hδ
  refine ⟨Ns, hNs, fun c hc => ?_⟩
  obtain ⟨Cs, hCs, hPc⟩ := hP c C hc hC1
  refine ⟨Cs, hCs, fun Λ hΛ M hM κ hκ m hm hmM ν B hν hB hν0 hellT => ?_⟩
  obtain ⟨hRh, hSlow, hPe, -, hell, hTT⟩ := hL Λ hΛ M hM κ hκ m hm hmM ν B hν hB
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) h128
  obtain ⟨hE0, hE1, -⟩ := Scales.epsilon_basic (q := q) (m := m - 1) hq.1 h128
  have hl := ocEll_sq_pos_of (q := q) (m := m) hΛ1 hν0
  have hτ0 := Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ1
  have hT0 := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ1
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  -- the pulse length in cell time
  have hTq : C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-(4 * ocDelta α q)) ≤
      ocTau α q Λ m / ocEll q Λ m ν ^ 2 := by
    have h1 : ocTau α q Λ m / ocEll q Λ m ν ^ 2 = (ocEll q Λ m ν ^ 2 / ocTau α q Λ m)⁻¹ := by
      rw [inv_div]
    rw [h1, Real.rpow_neg hE0.le, ← mul_inv]
    exact inv_anti₀ (div_pos hl hτ0) hell
  -- the Péclet factor
  have hpe : peFactor (ν / B) ≤ 2 * C * ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)) := by
    have hsq : (Real.sqrt (ν / B))⁻¹ = Real.sqrt (B / ν) := by
      rw [← Real.sqrt_inv, inv_div]
    have h1 : 1 ≤ ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hE0 hE1 (by linarith)
    have h2 : 1 ≤ C * ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)) := by nlinarith
    unfold peFactor
    rw [hsq]
    linarith
  have hbuf : seamBuffer α q Λ m ν = ocTau α q Λ m / ocEll q Λ m ν ^ 2 / 4 := by
    unfold seamBuffer
    ring
  have h := hPc (ocEpsilon q Λ (m - 1)) (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (ocTau α q Λ m / ocEll q Λ m ν ^ 2)
    ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2)
    (ocTauPP α q Λ m / ocTau α q Λ m) (peFactor (ν / B)) hE0 hE1
    (seamS_ge_one hΛ1 hν0 hellT) hSlow hTq
    (div_le_div_of_nonneg_right (ocTau_le_trimmedQuietMargin hΛ1) hl.le)
    (div_nonneg hT0.le hτ0.le) hTT (by field_simp)
    (zero_le_one.trans (one_le_peFactor _)) hpe
  unfold seamWindowPrice
  rw [hbuf]
  exact h

end AVRegularity.CycleJointProofs.Assembly
end
end
