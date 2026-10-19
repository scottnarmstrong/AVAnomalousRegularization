-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.PatchUniqueness
import AVRegularity.CycleJoint.PreparationFollowingRetainedEndpointErrorSummary
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

section
/-! **The two-block theorem on its window, the future block**.

`twoBlockJoint_future`: on the future block `[seam, t_p]` (cell times), for a datum family
`Tpre'` over the space `List Bool → X` (one old word endpoint per word) with finite moments, the
following-block summary gives the cell solutions `uH'` from the transitions `V₀' = transit ∘ Tpre'`;
The block word geometry gives the future word chains; `post_word_maps` gives the future endpoint `Tret` at the diagonal
datum, and the transition energy (`JointPremisesGen.transit_energy_le`) bounds the price of the block word geometry through
the energy of `Tpre`. The output is the named proposition `TwoBlockFutureFacts`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

local instance twoBlockFutureTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance twoBlockFutureTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance twoBlockFutureTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance
local instance twoBlockFutureTorusPiAdd {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    AddCommMonoid (∀ i, TorusHk (K i) (h i)) := inferInstance
local instance twoBlockFutureTorusPiModule {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    Module ℝ (∀ i, TorusHk (K i) (h i)) := inferInstance

section Future

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

/-- **The transition energy**: the chart transition at the seam costs the moment budget. -/
theorem JointPremisesGen.transit_energy_le {s : ℝ}
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ128 : 128 ≤ Λ) (hΛ : 1 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ)
    (U : ∀ i, PlaneHk Set.univ (K i) (h i)) (n : ℕ) :
    (∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
        (r / ocEpsilon q Λ m) (K i) (twoTransit hp hΛ hchart i (U i))) ≤
      ENNReal.ofReal (cellTransitionMomentBudget Kmax n) *
        ∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq n (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
            (r / ocEpsilon q Λ m) (K i) (U i) := by
  have he : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hr0 : 0 ≤ r / ocEpsilon q Λ m := div_nonneg hp.cov.pos.2.2.le he.le
  have hr1 : r / ocEpsilon q Λ m ≤ 1 := (div_le_one he).mpr hp.cov.rho_e
  exact preparationReferenceCellTransitionOperator_renewal_family_energy_le hp.hprep hp.hcover
    (Construction.Stream.ocTauPP_pos hΛ).le (ocA_nonneg_of hΛ (m - 1)) K
    (slot_le_chart hp.hK hchart)
    s hα0 hα1 hs0 hs1 hq hζ hΛ128 hp.hΦ (le_trans (by norm_num) hp.hm2) (hp.windows hΛ).next ν
    hp.cov.pos.1.ne' he.ne' y₀ U π _ (hp.windows hΛ).seamMem n n Kmax le_rfl hp.hK
    (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m) hr0 hr1

/-- **The facts of the future block** for the cell datum family `V₀'` (over `List Bool → X`), the
physical curves `uphys'`, `wphys'` of the following block, the conclusion `hpost` of the block word geometry on the future
block (bound `Bdpost`) and the future endpoint `Tret` at the diagonal datum, given the old word
endpoints `Tpre'`, `Tpre`. -/
def TwoBlockFutureFacts
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart)
    (Cw : ℕ → ℝ) (Cprep CR Cterminal Crem : ℝ) (Npost Lpost : ℕ) (Jpre Jpost : ℕ)
    (θM₂ θS₂ : ℝ) (bM₂ bS₂ : ι → ι → ℝ)
    (Tpre' : (List Bool → (∀ i, TorusHk (K i) (h i))) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Tpre : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
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
    (Tret : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i))) : Prop :=
  BlockCellSolutions D K (cellTime q Λ m ν (twoSeam α q Λ m l₀))
    (cellTime q Λ m ν (twoTp α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYcPost hp)) (twoGpost hp)
    (preparationReferenceCellSourceCoefficient F hφ (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) ν
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K (twoYcPost hp))
    V₀' (twoUHpost hp hΛ hchart uphys') (twoWHpost hp hΛ hchart wphys') ∧
  (∀ η i, V₀' η i = twoTransit hp hΛ hchart i (Tpre' η i)) ∧
  (∀ ξ i, Tret ξ i = ∑ wf ∈ blockWords Jpost H, Classical.choose hpost wf
    (wordDiag (blockWords Jpre H) ξ) (Fin.last _) i (cellTime q Λ m ν (twoTp α q Λ m l₀))) ∧
  ∀ ξ, (∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
        (r / ocEpsilon q Λ m) (K i)
        (twoUHpost hp hΛ hchart uphys' (wordDiag (blockWords Jpre H) ξ) i
          (cellTime q Λ m ν (twoTp α q Λ m l₀)) - Tret ξ i)) ≤
    twoEpsPost hp Cw Cprep CR Cterminal Crem Npost Lpost Jpost *
      ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq Npost (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
          (r / ocEpsilon q Λ m) (K i) (Tpre ξ i)

/-- **The output of the future block**: the cell datum family, the following block's physical
curves, the conclusion of the block word geometry on the future block and the future endpoint, with `TwoBlockFutureFacts`. -/
def TwoBlockFutureOut
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart)
    (Cw : ℕ → ℝ) (Cprep CR Cterminal Crem : ℝ) (Npost Lpost : ℕ) (Jpre Jpost : ℕ)
    (θM₂ θS₂ : ℝ) (bM₂ bS₂ : ι → ι → ℝ)
    (Tpre' : (List Bool → (∀ i, TorusHk (K i) (h i))) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Tpre : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i))) : Prop :=
  ∃ (V₀' : (List Bool → (∀ i, TorusHk (K i) (h i))) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (uphys' : (List Bool → (∀ i, TorusHk (K i) (h i))) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys' : (List Bool → (∀ i, TorusHk (K i) (h i))) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (Bdpost : (List Bool → (∀ i, TorusHk (K i) (h i))) → ℝ≥0∞)
    (hpost : BlockWordConclusion K Jpost H (fun t => twoGpost hp t 0) (twoMpost hp θM₂ bM₂)
      (twoSpost hp θS₂ bS₂) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYcPost hp)
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoTp α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYcPost hp)) V₀'
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m) 0 π
      (twoUHpost hp hΛ hchart uphys') (cellTime q Λ m ν (twoTp α q Λ m l₀)) Bdpost)
    (Tret : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i))),
    TwoBlockFutureFacts hp hΛ hchart Cw Cprep CR Cterminal Crem Npost Lpost Jpre Jpost θM₂ θS₂ bM₂
      bS₂ Tpre' Tpre V₀' uphys' wphys' Bdpost hpost Tret

end Future

/-- **The body of the future block** for the constants of the block word geometry and the following-block gain constant
`CTb`: for every family with the joint premises, the weights of the future window and old word
endpoints `Tpre'`, `Tpre` with finite moments and `Tpre'` at the diagonal equal to `Tpre`, the
future block's output `TwoBlockFutureOut` holds. -/
def TwoBlockFutureBody (D Ks Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (Cm Cchart CG : ℕ → ℝ) (Cprep CT CR Cterminal Crem : ℝ) (α q : ℝ) (ζ : ℝ → ℝ) (CTb : ℝ) :
    Prop :=
    ∀ (Λ : ℕ) (_hΛ128 : 128 ≤ Λ) (hΛ : 1 ≤ Λ) (g₀ : ℝ) (_hg₀ : g₀ ≤ 1 / 32) (H Ls qJ : ℕ)
    (_hD : 2 ≤ D) (_hKs : Ks + 1 ≤ Jm) (_hqJ : Ks + 1 + Kmax ≤ qJ)
    (Ca Cth Cb COld Crat Cpad Cage : ℝ) (Npad mStar : ℕ)
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
    (S : Set ℝ) (_hcoreS : IsCoreOutside α q Λ m F tS (tS + 2 * ocTauPP α q Λ m) S)
    (_hquiet : F.IsFastIndependentOn (S ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
    (Jpre Jpost Npost : ℕ) (_hNpost : (Ks + 1) + (Jpost + H) * (Ks + 1) ≤ Npost) (Cw : ℕ → ℝ)
    (_W : ChartWeights (twoGpost hp) (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
      (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoTp α q Λ m l₀) - cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0 Npost Cw)
    (_WM : ChartWeights (fun t _ => twoGpost hp t 0) (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
      (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoTp α q Λ m l₀) - cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0 Npost Cw)
    (Lpost : ℕ) (_hL : 1 ≤ Lpost)
    (_hreserve : ∀ k ≤ Npost, Real.exp (18 * Cw k) / (Lpost : ℝ) ^ 2 ≤ 1 / 16)
    (_hgain : ENNReal.ofReal (max CTb CT * g *
      (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1))) ≤ 1)
    (θM₂ θS₂ : ℝ) (bM₂ bS₂ : ι → ι → ℝ)
    (Tpre' : (List Bool → (∀ i, TorusHk (K i) (h i))) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Tpre : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (_hTpre' : ∀ η k i, weightedFactorialNormSq k
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0 (r / ocEpsilon q Λ m) (K i)
        (Tpre' η i) ≠ ⊤)
    (_hdiag : ∀ ξ, Tpre' (wordDiag (blockWords Jpre H) ξ) = Tpre ξ),
    TwoBlockFutureOut hp hΛ hchart Cw Cprep CR Cterminal Crem Npost Lpost Jpre Jpost θM₂ θS₂ bM₂
      bS₂ Tpre' Tpre

/-- **The two-block theorem on its window, the future block.** For the constants of the block word geometry (`hC`), the following-block
gain constant `CTb` is chosen with `TwoBlockFutureBody`. -/
theorem twoBlockJoint_future (D Ks Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm Cchart CG : ℕ → ℝ) (Cprep CT CR Cterminal Crem : ℝ)
    (hC : BlockWordBody.{u, v, w, x, max u v} D Ks Kmax Jchart Jm Cm Cchart CG Cprep CT CR
      Cterminal Crem) {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ CTb : ℝ, 0 ≤ CTb ∧
      TwoBlockFutureBody.{u, v, w, x} D Ks Kmax Jchart Jm hchart Cm Cchart CG Cprep CT CR Cterminal
        Crem α q ζ CTb := by
  obtain ⟨CprepB, CTb, CRB, CterminalB, -, hCTb, -, -, hfollowS⟩ :=
    preparation_following_retained_endpoint_error_summary.{u, v, w, x, max u v}
      D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG hα0 hα1 hs0 hs1 hq hζ
  refine ⟨CTb, hCTb, ?_⟩
  intro Λ hΛ128 hΛ g₀ hg₀ H Ls qJ hD hKs hqJ Ca Cth Cb COld Crat Cpad Cage Npad mStar ι _ _ h _ _
    _ _ _ _ π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ P' Ctx F actual A Θ T r ρold hp S hcoreS
    hquiet Jpre Jpost Npost hNpost Cw W WM Lpost hL hreserve hgain θM₂ θS₂ bM₂ bS₂ Tpre' Tpre
    hTpre' hdiag
  obtain ⟨heE, hper, hgsmall, hg0, hm⟩ := hp.scales hq hΛ128 hg₀
  obtain ⟨hBnn, hrow, hcol, hθ⟩ := hp.sums
  have hwin := hp.windows hΛ
  have hE : 0 < ocEpsilon q Λ (m - 1) := Construction.Stream.ocEpsilon_pos hΛ
  have hζc : 0 ≤ Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1) :=
    div_nonneg (Real.sqrt_nonneg _) hE.le
  have hgain2 := gain_of_max hp.cov.g_range.1 hζc hgain
  have hτend : cellTime q Λ m ν (twoTp α q Λ m l₀) ∈
      Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (cellTime q Λ m ν (twoTp α q Λ m l₀)) :=
    ⟨hwin.bd.le, le_rfl⟩
  have hL' : (1 : ℝ) ≤ (Lpost : ℝ) := Nat.one_le_cast.mpr hL
  have hN' : 0 + (Ks + 1) + (Jpost + H) * (Ks + 1) ≤ Npost := by rw [zero_add]; exact hNpost
  have hfol := hfollowS Λ m hΛ128 Φ hφ tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad l₀ P ν B r g
    g₀ a B₀ lam Cb qJ y₀ hp.cov hΛ heE (ocA_nonneg_of hΛ (m - 1)) hgsmall hg0 hD F hp.hmeas
    hp.hwmeas π hp.hπ K hp.hK actual (fun v u => Real.sqrt (π u / π v) * A v u) hBnn hp.hprep
    hp.hpointwise hp.hcover hwin.next hm hp.hΦ hp.htorus (Classical.choose hper)
    (Classical.choose_spec hper) (max Cth 0 * Θ) hrow hcol hp.hdesc hKs hθ hqJ H hp.hdepth
    (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (cellTime q Λ m ν (twoTp α q Λ m l₀)) hwin.bd hwin.dZ
    hwin.blockPost hwin.windowPost hwin.lengthPost 0 Npost Jpost Cw W WM (Lpost : ℝ) hL'
    hreserve hgain2.1 hN' _ hτend (X := List Bool → (∀ i, TorusHk (K i) (h i))) Tpre' hTpre'
  have hq1 := Classical.choose_spec (Classical.choose_spec hfol)
  have hq2 := hq1.2
  dsimp only at hq2
  have hq3 := Classical.choose_spec hq2
  have hcpl := coupled_following_windowCover α q Λ m ζ (Φ (m - 1)) hφ l₀ P hp.cov.P_pos ν y₀ D K
    (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (cellTime q Λ m ν (twoTp α q Λ m l₀))
    (preparationReferenceCellSourceCoefficient F hφ (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) ν
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K (twoYcPost hp))
    (⇑(Classical.choose hq2)) (twoUHpost hp hΛ hchart (Classical.choose hfol))
    (twoWHpost hp hΛ hchart (Classical.choose (Classical.choose_spec hfol))) hq3.1
  have hH := blockCellSolutions_of D K (cellTime q Λ m ν (twoSeam α q Λ m l₀))
    (cellTime q Λ m ν (twoTp α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYcPost hp)) (twoGpost hp)
    (preparationReferenceCellSourceCoefficient F hφ (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) ν
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K (twoYcPost hp))
    (Classical.choose hq2) (twoUHpost hp hΛ hchart (Classical.choose hfol))
    (twoWHpost hp hΛ hchart (Classical.choose (Classical.choose_spec hfol))) hcpl
  have hpost0 := hC α q Λ m ζ hζ Φ hφ tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad l₀ P ν B r g
    g₀ a B₀ lam Cb qJ y₀ hp.cov hΛ heE (ocA_nonneg_of hΛ (m - 1)) hgsmall hg0 hD F hp.hmeas
    hp.hwmeas π hp.hπ K hp.hK actual (fun v u => Real.sqrt (π u / π v) * A v u) hBnn hp.hprep
    hp.hcover (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hp.hpointwise
    (windowCoverFollowingChartIndex P hp.cov.P_pos) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
    (cellTime q Λ m ν (twoTp α q Λ m l₀)) hwin.bd hwin.windowPost (l₀ + 1) rfl (Or.inr hwin.next)
    hwin.blockPost S hcoreS hquiet (max Cth 0 * Θ) hrow hcol hp.hdesc hKs hθ hqJ hwin.lengthPost
    (X := List Bool → (∀ i, TorusHk (K i) (h i))) 0 H Npost Jpost hp.hdepth Cw W WM
    (Classical.choose hq2) hq3.2.1
    (twoUHpost hp hΛ hchart (Classical.choose hfol)) _ hH (Lpost : ℝ) hL' hreserve hgain2.2 hN' _
    hτend θM₂ θS₂ bM₂ bS₂
  have hpost : BlockWordConclusion K Jpost H (fun t => twoGpost hp t 0) (twoMpost hp θM₂ bM₂)
      (twoSpost hp θS₂ bS₂) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYcPost hp)
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoTp α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
      (Classical.choose hq2) (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
      (r / ocEpsilon q Λ m) 0 π (twoUHpost hp hΛ hchart (Classical.choose hfol))
      (cellTime q Λ m ν (twoTp α q Λ m l₀)) _ := hpost0
  have hident : ∀ η i, (Classical.choose hq2) η i = twoTransit hp hΛ hchart i (Tpre' η i) :=
    hq3.2.2.1
  have hmW := post_word_maps K Jpost H _ _ _ _ _ _ _ _ _ _ _ 0 π _ _ hτend _ (blockWords Jpre H)
    hpost
  have hmW' := Classical.choose_spec hmW
  have hdat := datum_diag_eq (Classical.choose hq2) Tpre' Tpre (twoTransit hp hΛ hchart)
    (blockWords Jpre H) hident hdiag
  have hEn := fun ξ => hp.transit_energy_le hΛ128 hΛ hchart hα0 hα1 hs0 hs1 hq hζ (Tpre ξ) Npost
  refine ⟨Classical.choose hq2, Classical.choose hfol,
    Classical.choose (Classical.choose_spec hfol),
    _, hpost, Classical.choose hmW, hH, hident, hmW'.1, fun ξ => ?_⟩
  exact (hmW'.2 ξ).trans (pricePost_le (datumEnergy_le π Npost
    (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m) _
    (fun ξ => (Classical.choose hq2) (wordDiag (blockWords Jpre H) ξ)) (⇑Tpre)
    (twoTransit hp hΛ hchart) hdat hEn ξ))

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The seam on the two blocks: statement**.

The two-block theorem (`TwoBlockJointStatement`) gives, for the patch datum `ξ`, old word chains `uO wo ξ` on the old
block `[a, b]` (cell times of `tS` and of the seam `(l₀ + 1/2) τ''`) and future word chains
`uF wo wf ξ` on the future block `[b, d]` (`d` the cell time of `t_p = (l₀ + 3/2) τ''`) started from
the chart transition of the old endpoints. The seam (`cycle_seam`, applied to every allocation
`(wo, wf)`) gives, for every future word `wf`, a kernel `Kp wf`, and the cell model of the patch is
`Mc ξ = Σ_{wf} Kp wf (Σ_{wo} cutoff (uO wo ξ (last) b) ∘ Υ)`.

`SeamAllocationStatement`: the cell model is linear in the datum and smooth, with, in the seam's
norms (`ϖ = ε/√(B τ'')`, moment weight of order `pout`),
- the model bound: its weighted jet norm of every order `M ≤ Mb` at radius `1/ϖ` is at most `CM`
  times the mass-weighted `L²` norm of the cell datum `V₀ ξ` (`momentNorm π 0 ϖ`);
- the allocation error: the weighted jet norm at radius `r/ε` of the jets of order at most `K i`
  of `Σ_{wo,wf} uF wo wf ξ (last) d - Mc ξ` is at most `CN` times the seam price
  `seamWindowPrice` of the window times the same `L²` norm.

The letters are those of `BlockLettersStatement` (the constant `CL`). The scale conditions are
premises, discharged at the starting level:
- the strain of the transition `g + A τ''` is at most `g₁` (this also bounds the cover strain `g`);
- the pulses are long, `Θlong ≤ τ/ℓ²` (the admissibility of the two renewal blocks);
- the budget `seamWindowBudget ≤ 1` (the seam's `hC0` with `C0 = 1`: the region count of a block
  is at most `4 + τ''/τ` and the quiet buffer is shrunk to `τ/(4ℓ²)`);
- `0 ≤ Cth Θ` (the source letter's `θ`; from the envelope when the family is nonempty).
The datum is supported in the cell disc of radius `Cs/ϖ` (after the recentring of the cover at the
patch).

Edge-free clause: for a family without edges, given the word chains of the two-block theorem at slot `0` and the
finite moments of the old chains' fields at both slot assignments, there is a cell model at slot
`0` with the same bounds that agrees on truncated data with the cell model at slots `K`.

For an empty index type `momentNorm` and `weightedJetNorm` are sums over the empty type, both sides
are `0`, and `Mc = 0` works. For `g = 0` (identity metric) the metric letters have `θ = 0`, so a word
with a metric insertion contributes `0` to the seam's bounds, which the statement allows. For
minimal orders `Jpre = Jpost = H = 0` the only allocation is the empty word pair, and the model is
the scalar seam `Kp (cutoff (V₀ ξ evolved) ∘ Υ)`. Only the letters see the component labels
(`BlockLettersStatement`); the bounds are mass-weighted sums over the components. The premises
exclude low levels, where `Θlong ≤ τ/ℓ²` fails (there is no admissible block) and the budget fails
(the seam's `hC0`), and a strain above `g₁`, which leaves the seam's metric range. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- The quiet buffer of the future block after the shrink, `τ/(4ℓ²)`. -/
def seamBuffer (α q : ℝ) (Λ m : ℕ) (ν : ℝ) : ℝ :=
  ocTau α q Λ m / (4 * ocEll q Λ m ν ^ 2)

/-- The seam's budget `hC0` on the two-block window (`η = ν/B`, `S = τ''/ℓ²`, at most `4 + τ''/τ` regions,
buffer `τ/(4ℓ²)`). -/
def seamWindowBudget (α q : ℝ) (Λ m : ℕ) (ν B : ℝ) (Q : ℕ) (c : ℝ) : ℝ :=
  peFactor (ν / B) ^ Q * (1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ Q *
    (5 + ocTauPP α q Λ m / ocTau α q Λ m) * Real.exp (-c * seamBuffer α q Λ m ν)

/-- The seam price of the two-block window (`S = τ''/ℓ²`, `η = ν/B`; at most `4 + τ''/τ` regions, buffer
`τ/(4ℓ²)`, quiet margin `(τ' - τ/24)/ℓ²` (the trimmed quiet times of the renewal quiet margin),
cutoff order `Ns`). -/
def seamWindowPrice (α q : ℝ) (Λ m : ℕ) (ν B : ℝ) (Q Ns : ℕ) (c : ℝ) : ℝ :=
  peFactor (ν / B) ^ Q * (1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ Q *
    (Real.exp (-c * (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)) +
      (5 + ocTauPP α q Λ m / ocTau α q Λ m) * Real.exp (-c * seamBuffer α q Λ m ν) +
      Real.exp (-c * ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2)) +
      (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ (-(Ns : ℝ) / 2))

section Clauses

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type*} {Ctx : P' → Type*} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- The seam's premise on the cell datum of the patch: it is supported in the cell disc of radius
`Cs/ϖ` (`ϖ = ε/√(B τ'')`). -/
def SeamDatumSupport
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (Cs : ℝ) (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ) : Prop :=
  ∀ (ξ : ∀ i, TorusHk (K i) (h i)) i, ∀ᵐ z : Vec 2 ∂volume,
    (Cs * (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ m)) ^ 2 < z 0 ^ 2 + z 1 ^ 2 →
    planeValue (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ i) z = 0

/-- The seam's word chains (those of the two-block theorem): the old word chains on `[a, b]` from the cell datum, the future word
chains on `[b, d]` from the transitions of the old endpoints (letters of the strengths `CL` of `BlockLettersStatement`),
and the linearity of the old chains in the datum. -/
def SeamWordChains
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (CL : ℝ) (Jpre Jpost : ℕ) (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (uO : ∀ wo : List Bool, (∀ i, TorusHk (K i) (h i)) → ∀ (_ : Fin (wo.length + 1)) (x : ι),
      ℝ → PlaneHk Set.univ (K x) (h x))
    (wO : ∀ wo : List Bool, (∀ i, TorusHk (K i) (h i)) → ∀ (_ : Fin (wo.length + 1)) (x : ι),
      ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (uF : List Bool → ∀ wf : List Bool, (∀ i, TorusHk (K i) (h i)) →
      ∀ (_ : Fin (wf.length + 1)) (x : ι), ℝ → PlaneHk Set.univ (K x) (h x))
    (wF : List Bool → ∀ wf : List Bool, (∀ i, TorusHk (K i) (h i)) →
      ∀ (_ : Fin (wf.length + 1)) (x : ι), ℝ → PlaneHk Set.univ (K x + 1) (h x)) : Prop :=
  (∀ wo ∈ blockWords Jpre H, ∀ ξ, IsPlaneChain (wordChainData (fun t => twoGpre hp t 0)
    (blockWordLetters (twoMpre hp (CL * g) (fun v u => if v = u then CL * g else 0))
      (twoSpre hp (CL * (Cth * Θ)) (fun v u => CL * (Real.sqrt (π u / π v) * A v u))) wo)
    ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
    (fun _ x => K x) (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
    (ocCellDrift α q Λ ζ m ν (twoYc hp)) (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ)
    (fun _ _ _ => 0) (uO wo ξ) (wO wo ξ)) ∧
  (∀ wo ∈ blockWords Jpre H, ∀ wf ∈ blockWords Jpost H, ∀ ξ,
    IsPlaneChain (wordChainData (fun t => twoGpost hp t 0)
      (blockWordLetters (twoMpost hp (CL * g) (fun v u => if v = u then CL * g else 0))
        (twoSpost hp (CL * (Cth * Θ)) (fun v u => CL * (Real.sqrt (π u / π v) * A v u))) wf)
      ((ocEpsilon q Λ (m - 1))⁻¹ • twoYcPost hp) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
      (fun _ x => K x) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoTp α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
      (fun x => twoTransit hp hΛ hchart x
        (uO wo ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀))))
      (fun _ _ _ => 0) (uF wo wf ξ) (wF wo wf ξ)) ∧
  (∀ wo ∈ blockWords Jpre H, ∀ (c' : ℝ) (ξ ξ' : ∀ i, TorusHk (K i) (h i)) j x,
    ∀ t ∈ Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)),
    uO wo (c' • ξ + ξ') j x t = c' • uO wo ξ j x t + uO wo ξ' j x t)

/-- The fields of the old word chains have finite time-integrated moments at every level (as given by the two-block theorem). -/
def SeamOldMoments
    (_hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (Jpre : ℕ)
    (wO : ∀ wo : List Bool, (∀ i, TorusHk (K i) (h i)) → ∀ (_ : Fin (wo.length + 1)) (x : ι),
      ℝ → PlaneHk Set.univ (K x + 1) (h x)) : Prop :=
  ∀ wo ∈ blockWords Jpre H, ∀ ξ j x n,
    (∫⁻ t in Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)),
      weightedFactorialNormSq n (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
        (r / ocEpsilon q Λ m) (K x + 1) (wO wo ξ j x t)) ≠ ⊤

/-- The seam's clauses of a cell model `Mc`: smooth, the model bound of every order `M ≤ Mb`, and the
masked allocation error. -/
def SeamModelClauses
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (Jpre Jpost Mb pout Q Ns : ℕ) (CM CN c : ℝ) (Npatch : ℕ) (hNpatch : 0 < Npatch)
    (patch : Fin 2 → ℤ)
    (uF : List Bool → ∀ wf : List Bool, (∀ i, TorusHk (K i) (h i)) →
      ∀ (_ : Fin (wf.length + 1)) (x : ι), ℝ → PlaneHk Set.univ (K x) (h x))
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x)) : Prop :=
  (∀ ξ x (M : ℕ), ContDiff ℝ M (Mc ξ x)) ∧
  (∀ ξ, ∀ M ≤ Mb,
    weightedJetNorm π (pout : ℝ) M (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc ξ x) z) ≤
      ENNReal.ofReal CM *
        momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
          (fun x => planeValue (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ x))) ∧
  ∀ ξ, weightedJetNorm π (pout : ℝ) Kmax (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
      (r / ocEpsilon q Λ m)
      (fun x a' wd z => if a' ≤ K x then
        planeJetOrder (∑ wo ∈ blockWords Jpre H, ∑ wf ∈ blockWords Jpost H,
          uF wo wf ξ (Fin.last _) x (cellTime q Λ m ν (twoTp α q Λ m l₀))) a' wd z -
          orderedDerivative wd (Mc ξ x) z else 0) ≤
    ENNReal.ofReal (CN * seamWindowPrice α q Λ m ν B Q Ns c) *
      momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ x))

/-- The old word chains at slot `0` read with the window objects of the slot-`K` premises. -/
theorem SeamWordChains.slotZero_old
    {hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold} {hedge : ∀ v u, IsEmpty (F.Γ v u)} {hΛ : 1 ≤ Λ}
    {hchart : Kmax + D + 2 ≤ Jchart} {hζ : IsFastProfile ζ} {CL : ℝ} {Jpre Jpost Npatch : ℕ}
    {hNpatch : 0 < Npatch} {patch : Fin 2 → ℤ}
    {uO : ∀ wo : List Bool, (∀ i, TorusHk 0 (h i)) → ∀ (_ : Fin (wo.length + 1)) (x : ι),
      ℝ → PlaneHk Set.univ 0 (h x)}
    {wO : ∀ wo : List Bool, (∀ i, TorusHk 0 (h i)) → ∀ (_ : Fin (wo.length + 1)) (x : ι),
      ℝ → PlaneHk Set.univ (0 + 1) (h x)}
    {uF : List Bool → ∀ wf : List Bool, (∀ i, TorusHk 0 (h i)) →
      ∀ (_ : Fin (wf.length + 1)) (x : ι), ℝ → PlaneHk Set.univ 0 (h x)}
    {wF : List Bool → ∀ wf : List Bool, (∀ i, TorusHk 0 (h i)) →
      ∀ (_ : Fin (wf.length + 1)) (x : ι), ℝ → PlaneHk Set.univ (0 + 1) (h x)}
    (hch : SeamWordChains (hp.slotZero hedge) hΛ hchart hζ CL Jpre Jpost Npatch hNpatch patch
      uO wO uF wF) :
    ∀ wo ∈ blockWords Jpre H, ∀ ξ, IsPlaneChain (wordChainData (fun t => twoGpre hp t 0)
      (blockWordLetters (twoMpre hp (CL * g) (fun v u => if v = u then CL * g else 0))
        (twoSpre hp (CL * (Cth * Θ)) (fun v u => CL * (Real.sqrt (π u / π v) * A v u))) wo)
      ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
      (fun _ x => (fun _ => 0 : ι → ℕ) x) (cellTime q Λ m ν tS)
      (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYc hp))
      (twoV₀ (hp.slotZero hedge) hΛ hchart hζ Npatch hNpatch patch ξ)
      (fun _ _ _ => 0) (uO wo ξ) (wO wo ξ) :=
  hch.1

/-- The future word chains at slot `0` read with the window objects of the slot-`K` premises. -/
theorem SeamWordChains.slotZero_future
    {hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold} {hedge : ∀ v u, IsEmpty (F.Γ v u)} {hΛ : 1 ≤ Λ}
    {hchart : Kmax + D + 2 ≤ Jchart} {hζ : IsFastProfile ζ} {CL : ℝ} {Jpre Jpost Npatch : ℕ}
    {hNpatch : 0 < Npatch} {patch : Fin 2 → ℤ}
    {uO : ∀ wo : List Bool, (∀ i, TorusHk 0 (h i)) → ∀ (_ : Fin (wo.length + 1)) (x : ι),
      ℝ → PlaneHk Set.univ 0 (h x)}
    {wO : ∀ wo : List Bool, (∀ i, TorusHk 0 (h i)) → ∀ (_ : Fin (wo.length + 1)) (x : ι),
      ℝ → PlaneHk Set.univ (0 + 1) (h x)}
    {uF : List Bool → ∀ wf : List Bool, (∀ i, TorusHk 0 (h i)) →
      ∀ (_ : Fin (wf.length + 1)) (x : ι), ℝ → PlaneHk Set.univ 0 (h x)}
    {wF : List Bool → ∀ wf : List Bool, (∀ i, TorusHk 0 (h i)) →
      ∀ (_ : Fin (wf.length + 1)) (x : ι), ℝ → PlaneHk Set.univ (0 + 1) (h x)}
    (hch : SeamWordChains (hp.slotZero hedge) hΛ hchart hζ CL Jpre Jpost Npatch hNpatch patch
      uO wO uF wF) :
    ∀ wo ∈ blockWords Jpre H, ∀ wf ∈ blockWords Jpost H, ∀ ξ,
      IsPlaneChain (wordChainData (fun t => twoGpost hp t 0)
        (blockWordLetters (twoMpost hp (CL * g) (fun v u => if v = u then CL * g else 0))
          (twoSpost hp (CL * (Cth * Θ)) (fun v u => CL * (Real.sqrt (π u / π v) * A v u))) wf)
        ((ocEpsilon q Λ (m - 1))⁻¹ • twoYcPost hp) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
        (fun _ x => (fun _ => 0 : ι → ℕ) x) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoTp α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
        (fun x => twoTransit (hp.slotZero hedge) hΛ hchart x
          (uO wo ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀))))
        (fun _ _ _ => 0) (uF wo wf ξ) (wF wo wf ξ) :=
  hch.2.1

end Clauses

/-- The body of the seam statement for given constants: every family with the joint premises and the scale
conditions has, for the word chains of the two-block theorem, the cell model with the model and error bounds; for a
family without edges, the cell model at slot `0` (from the word chains of the two-block theorem at slot `0`) has the same
bounds and agrees on truncated data with the cell model at slots `K` (the edge-free clause). -/
def SeamAllocationBody (α q : ℝ) (Λ : ℕ) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (g₁ Θlong : ℝ)
    (D H Kmax Ks Jpre Jpost Mb pout Q Ns Ls Jm qJ Jchart : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (Ca Cs Cpad Cage : ℝ) (Cm CG Cchart : ℕ → ℝ) (CL Cth CM CN c : ℝ) : Prop :=
  ∀ (g₀ Cb COld Crat : ℝ) (Npad mStar : ℕ) (hΛ : 1 ≤ Λ)
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
      A Θ T r ρold),
    g₀ ≤ g₁ → 0 ≤ Cth * Θ → g + ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ g₁ →
    Θlong ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2 → seamWindowBudget α q Λ m ν B Q c ≤ 1 →
  ∀ (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ),
    SeamDatumSupport hp hΛ hchart hζ Cs Npatch hNpatch patch →
  ∀ uO wO uF wF, SeamWordChains hp hΛ hchart hζ CL Jpre Jpost Npatch hNpatch patch uO wO uF wF →
  ∃ Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x),
    SeamModelClauses hp hΛ hchart hζ Jpre Jpost Mb pout Q Ns CM CN c Npatch hNpatch patch uF Mc ∧
    ∀ hedge : ∀ v u, IsEmpty (F.Γ v u), SeamOldMoments hp Jpre wO →
      SeamDatumSupport (hp.slotZero hedge) hΛ hchart hζ Cs Npatch hNpatch patch →
    ∀ uO0 wO0 uF0 wF0, SeamWordChains (hp.slotZero hedge) hΛ hchart hζ CL Jpre Jpost Npatch
      hNpatch patch uO0 wO0 uF0 wF0 → SeamOldMoments (hp.slotZero hedge) Jpre wO0 →
    ∃ Mc0 : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x),
      SeamModelClauses (hp.slotZero hedge) hΛ hchart hζ Jpre Jpost Mb pout Q Ns CM CN c Npatch
        hNpatch patch uF0 Mc0 ∧
      ∀ ξ, Mc0 (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i)) = Mc ξ

/-- **The seam on the two blocks.** -/
def SeamAllocationStatement : Prop :=
  ∀ {α s q : ℝ} (_hα0 : 0 < α) (_hα1 : α < 1 / 3) (_hs0 : 0 < s) (_hs1 : s < (1 - α) / 2)
    (_hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ),
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₁ Θlong : ℝ, 0 < g₁ ∧
  ∀ (D H Kmax Ks Jpre Jpost Mb pout : ℕ), 2 ≤ D →
  ∃ Q Jstar : ℕ, ∀ Ns : ℕ, 1 ≤ Ns → ∃ qΥ : ℕ,
  ∀ (Ls Jm qJ Jchart : ℕ) (hchart : Kmax + D + 2 ≤ Jchart), Jstar ≤ Ls → Ks + Jstar ≤ qJ →
    Ks + Jstar + D ≤ Jchart → qΥ ≤ Jchart + 1 →
  ∀ (Ca Cs Cpad Cage : ℝ) (Cm CG Cchart : ℕ → ℝ),
  ∃ CL : ℝ, 0 ≤ CL ∧ ∀ Cth : ℝ, ∃ CM CN c : ℝ, 0 ≤ CM ∧ 0 ≤ CN ∧ 0 < c ∧
    SeamAllocationBody.{u, v, w, x} α q Λ hζ g₁ Θlong D H Kmax Ks Jpre Jpost Mb pout Q Ns Ls Jm qJ
      Jchart hchart Ca Cs Cpad Cage Cm CG Cchart CL Cth CM CN c

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The support of the recentred cell datum**.

The patch localization of mesh `N` lives in the box of half-width `(2/3)/N` around the patch
centre `c`. The cell datum `twoV₀` evaluates it at `X (yc + ε z)`, where `X` is the flow from the
reference time `l₀ τ''` back to `tS`. When the chart centre is the transported patch centre,
`yc = Y c` with `Y = X⁻¹` the forward flow (Lipschitz with the first-jet budget
`B₁ = 1 + max (Cchart 0) 0 / 2`), so `ε z = Y x - Y c` and a point of the box gives
`ε² |z|² ≤ (8/9) B₁² / N² ≤ B₁² R² / 72` when `8 ≤ N R`. Hence the cell datum vanishes a.e. outside
the disc of radius `(B₁/8) R/ε` (the seam's `hfsupp` with `Cs = B₁/8`).

`JointPremisesGen.recenter` moves the cover's centre (the premises mention it only through the
cover), and `twoYc` of the recentred premises is the new centre.

The statement is over the components, so it is vacuous for an empty index type. If `Cchart 0 ≤ 0`
then `B₁ = 1`, and the radius condition `8 ≤ N R` is the patch mesh of the one-patch statement. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev Set
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
  AVRegularity.CycleReference
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- The first-jet budget of the chart flows. -/
theorem preparationPieceFlowJetBudget_one (Cchart : ℕ → ℝ) (e : ℝ) :
    preparationPieceFlowJetBudget Cchart e 1 = 1 + max (Cchart 0) 0 / 2 := by
  unfold preparationPieceFlowJetBudget preparationFlowJetConstant
  simp only [↓reduceIte, pow_zero, mul_one, Nat.sub_self]
  exact abs_of_nonneg (by have := le_max_right (Cchart 0) 0; positivity)

/-- The patch box in the sup norm. -/
theorem spatialPatch_box_norm {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N)
    (k : Fin 2 → ℤ) (x : Vec 2) (hx : x ∈ tsupport (spatialPatchCutoff ζ N k)) :
    ‖x - spatialPatchCenter N k‖ ≤ (2 / 3 : ℝ) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  have hb := spatialPatchCutoff_tsupport_coordinate hζ N k x hx i
  have he : x i - (k i : ℝ) / N = ((N : ℝ) * x i - k i) / N := by field_simp
  change ‖x i - (k i : ℝ) / N‖ ≤ _
  rw [Real.norm_eq_abs, he, abs_div, abs_of_pos hNr]
  exact div_le_div_of_nonneg_right hb hNr.le

/-- The arithmetic of the support statement: a cell point whose image lies in the box is inside the disc. -/
theorem cell_disc_of_box {B₁ R N ε : ℝ} (hB : 0 ≤ B₁) (hN : 0 < N) (hε : 0 < ε) (hNR : 8 ≤ N * R)
    (z : Vec 2) (hz : ‖ε • z‖ ≤ B₁ * ((2 / 3) / N)) :
    z 0 ^ 2 + z 1 ^ 2 ≤ (B₁ / 8 * (R / ε)) ^ 2 := by
  have hR : 0 < R := by
    by_contra hR
    have hR' := not_lt.mp hR
    nlinarith
  have hc : ∀ i, (ε * z i) ^ 2 ≤ (B₁ * ((2 / 3) / N)) ^ 2 := by
    intro i
    have h1 : |ε * z i| ≤ B₁ * ((2 / 3) / N) := by
      have := norm_le_pi_norm (ε • z) i
      rw [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs] at this
      exact this.trans hz
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hinvN : 1 / N ≤ R / 8 := by
    rw [div_le_div_iff₀ hN (by norm_num)]
    linarith
  have hinvN0 : 0 ≤ 1 / N := by positivity
  have hq : (B₁ * ((2 / 3) / N)) ^ 2 ≤ (B₁ * ((2 / 3) * (R / 8))) ^ 2 := by
    have : (2 / 3 : ℝ) / N = (2 / 3) * (1 / N) := by ring
    rw [this]
    have h0 : 0 ≤ B₁ * ((2 / 3) * (1 / N)) := by positivity
    exact pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hinvN (by norm_num)) hB) 2
  have hsum : ε ^ 2 * (z 0 ^ 2 + z 1 ^ 2) ≤ ε ^ 2 * (B₁ / 8 * (R / ε)) ^ 2 := by
    have e2 : ε ^ 2 * (B₁ / 8 * (R / ε)) ^ 2 = (B₁ * R) ^ 2 / 64 := by
      field_simp
      ring
    rw [e2]
    have h0 := hc 0
    have h1 := hc 1
    have hk : (B₁ * ((2 / 3) * (R / 8))) ^ 2 = (B₁ * R) ^ 2 / 144 := by ring
    rw [hk] at hq
    have hpos : 0 ≤ (B₁ * R) ^ 2 := sq_nonneg _
    nlinarith
  exact le_of_mul_le_mul_left hsum (by positivity)

section Support

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

/-- **Recentring the premises** at any point `yd` (only the cover mentions the centre). -/
theorem JointPremisesGen.recenter (hΛ : 1 ≤ Λ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (yd : Vec 2) :
    JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P yd F actual
      A Θ T r ρold :=
  { hp with cov := windowCover_recenter hΛ hφ hp.cov yd }

/-- The chart centre of the old block is the cover's centre. -/
theorem twoYc_eq
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) : twoYc hp = y₀ :=
  windowCover_reference_centre_eq α q Λ m hφ l₀ P y₀

/-- The value of the cell datum: the localized datum at `X (yc + ε z)`. -/
theorem twoV₀_value_ae (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ) (ξ : ∀ i, TorusHk (K i) (h i))
    (i : ι) :
    planeValue (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ i) =ᵐ[volume]
      fun z => planeValue (spatialPatchLocalization hζ Npatch hNpatch patch (K i) (ξ i))
        (streamFlow (Φ (m - 1)) hφ tS (twoYc hp + ocEpsilon q Λ m • z)
          ((l₀ : ℝ) * ocTauPP α q Λ m)) := by
  have he := (Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).ne'
  unfold twoV₀
  rw [preparationReferenceCellLocalizedInitialFamilyLinearMap_apply]
  have hh := (plane_affine_quasiMeasurePreserving (ocEpsilon q Λ m) he (twoYc hp)).ae_eq_comp
    (preparationReferenceHkWindowPull_value_ae hp.hprep hp.hcover
      (Construction.Stream.ocTauPP_pos hΛ).le (ocA_nonneg_of hΛ (m - 1)) (K i)
      (slot_le_chart hp.hK hchart i) tS ⟨le_rfl, twoWindow_le hΛ tS⟩
      (spatialPatchLocalization hζ Npatch hNpatch patch (K i) (ξ i)))
  exact (planeCarrierAffine_value_ae _ he _ _).trans hh

/-- **Support of the cell datum.** When the cover is centred at the transported patch centre, the cell datum vanishes
a.e. outside the disc of radius `(B₁/8) R/ε`, for every `R` with `8 ≤ N R`. -/
theorem twoV₀_support (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCenter Npatch patch) tS)
    (R : ℝ) (hNR : 8 ≤ (Npatch : ℝ) * R) (ξ : ∀ i, TorusHk (K i) (h i)) (i : ι) :
    ∀ᵐ z : Vec 2 ∂volume,
      ((1 + max (Cchart 0) 0 / 2) / 8 * (R / ocEpsilon q Λ m)) ^ 2 < z 0 ^ 2 + z 1 ^ 2 →
      planeValue (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ i) z = 0 := by
  set ε := ocEpsilon q Λ m with hε
  have hεpos : 0 < ε := Construction.Stream.ocEpsilon_pos hΛ
  set τ₀ := (l₀ : ℝ) * ocTauPP α q Λ m with hτ₀
  set c := spatialPatchCenter Npatch patch with hc
  set B₁ := 1 + max (Cchart 0) 0 / 2 with hB₁
  have hB₁0 : 0 ≤ B₁ := by have := le_max_right (Cchart 0) 0; positivity
  -- the localized datum vanishes off the box
  have hloc : ∀ᵐ y ∂volume, y ∉ tsupport (spatialPatchCutoff ζ Npatch patch) →
      planeValue (spatialPatchLocalization hζ Npatch hNpatch patch (K i) (ξ i)) y = 0 := by
    filter_upwards [spatialPatchLocalization_jet_support_ae hζ Npatch hNpatch patch (K i) (ξ i)
      ⟨⟨0, Nat.succ_pos _⟩, fun k => k.elim0⟩] with y hy hny
    simp only [planeValue, planeJetOrder, Nat.zero_le, ↓reduceDIte]
    exact hy hny
  -- through the affine map and the flow
  have hqmp : Measure.QuasiMeasurePreserving
      (fun z : Vec 2 => streamFlow (Φ (m - 1)) hφ tS (twoYc hp + ε • z) τ₀) volume volume :=
    (streamFlow_measurePreserving hφ tS τ₀).quasiMeasurePreserving.comp
      (plane_affine_quasiMeasurePreserving ε hεpos.ne' (twoYc hp))
  have hcomp := hqmp.ae hloc
  -- the forward flow is Lipschitz with constant `B₁`
  have hb : ∀ y, ‖iteratedFDeriv ℝ 1 (fun y => streamFlow (Φ (m - 1)) hφ τ₀ y tS) y‖ ≤
      ((⟨B₁, hB₁0⟩ : NNReal) : ℝ) := fun y => by
    have := preparation_reference_inverse_flow_jets hp.hprep hp.hcover
      (Construction.Stream.ocTauPP_pos hΛ).le (ocA_nonneg_of hΛ (m - 1)) tS
      ⟨le_rfl, twoWindow_le hΛ tS⟩ 1 le_rfl (by omega) y
    rw [preparationPieceFlowJetBudget_one] at this
    exact this
  have hlip := CycleJointProofs.lipschitzWith_of_first_jet_bound _
    ((streamFlow_spatial_smooth hφ τ₀ tS).differentiable (by simp)) _ hb
  filter_upwards [hcomp, twoV₀_value_ae hΛ hchart hζ hp Npatch hNpatch patch ξ i]
    with z hz hval hdisc
  rw [hval]
  apply hz
  intro hbox
  set x := streamFlow (Φ (m - 1)) hφ tS (twoYc hp + ε • z) τ₀ with hx
  have hY : streamFlow (Φ (m - 1)) hφ τ₀ x tS = twoYc hp + ε • z :=
    (streamFlowHomeomorph hφ τ₀ tS).apply_symm_apply (twoYc hp + ε • z)
  have hYc : streamFlow (Φ (m - 1)) hφ τ₀ c tS = twoYc hp := by
    rw [twoYc_eq hp, hyc]
  have hd := hlip.dist_le_mul x c
  rw [dist_eq_norm, dist_eq_norm, hY, hYc, add_sub_cancel_left] at hd
  have hxbox := spatialPatch_box_norm hζ Npatch hNpatch patch x hbox
  have hz' : ‖ε • z‖ ≤ B₁ * ((2 / 3) / Npatch) :=
    hd.trans (mul_le_mul_of_nonneg_left hxbox hB₁0)
  have := cell_disc_of_box hB₁0 (by exact_mod_cast hNpatch) hεpos hNR z hz'
  linarith

end Support

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The scales of the seam on the two-block window**.

Scalar facts for the application of `cycle_seam` on the two renewal blocks: cell times are physical
times over `ℓ²`; the cell drift vanishes exactly at the cell times of quiet physical times; the
time scales are ordered `τ ≤ τ' ≤ τ''`; and the seam's scales `η = ν/B`, `S = τ''/ℓ²`,
`ϖ = √(η/S) = ε/√(B τ'')`, `ηg = √(B τ'')/E` (so that `δ = ε/E = ϖ ηg`). -/

section Scales

variable {α q : ℝ} {Λ m : ℕ} {ν : ℝ}

theorem ocEll_sq_pos_of (hΛ : 1 ≤ Λ) (hν : 0 < ν) : 0 < ocEll q Λ m ν ^ 2 := by
  rw [CycleReference.ocEll_sq_eq hν]
  exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ) 2) hν

/-- Cell times are physical times over `ℓ²`. -/
theorem cellTime_eq_div (hΛ : 1 ≤ Λ) (hν : 0 < ν) (t : ℝ) :
    cellTime q Λ m ν t = t / ocEll q Λ m ν ^ 2 := by
  have he := (Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).ne'
  rw [CycleReference.ocEll_sq_eq hν]
  unfold cellTime
  field_simp

/-- The cell time of the seam. -/
theorem cellTime_twoSeam (hΛ : 1 ≤ Λ) (hν : 0 < ν) (l₀ : ℤ) :
    cellTime q Λ m ν (twoSeam α q Λ m l₀) =
      ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 := by
  rw [cellTime_eq_div hΛ hν]
  rfl

/-- The cell time of the endpoint is the seam's plus `S = τ''/ℓ²`. -/
theorem cellTime_twoTp (hΛ : 1 ≤ Λ) (hν : 0 < ν) (l₀ : ℤ) :
    cellTime q Λ m ν (twoTp α q Λ m l₀) =
      cellTime q Λ m ν (twoSeam α q Λ m l₀) + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 := by
  rw [cellTime_eq_div hΛ hν, cellTime_eq_div hΛ hν, ← add_div]
  unfold twoTp twoSeam
  ring_nf

/-- The cell drift vanishes at the cell times of quiet physical times. -/
theorem ocCellDrift_eq_zero_of_quiet {ζ : ℝ → ℝ} (yc : Vec 2) {t : ℝ}
    (ht : ocEll q Λ m ν ^ 2 * t ∈ ocQuietTimes α q Λ ζ m) (z : Vec 2) :
    ocCellDrift α q Λ ζ m ν yc t z = 0 := by
  unfold ocCellDrift
  rw [ht (yc + ocEpsilon q Λ m • z), smul_zero]

/-- A cell time at which the cell drift vanishes is the cell time of a quiet physical time. -/
theorem quiet_of_ocCellDrift_eq_zero (hΛ : 1 ≤ Λ) (hν : 0 < ν) {ζ : ℝ → ℝ} (yc : Vec 2)
    {t : ℝ} (h0 : ∀ z, ocCellDrift α q Λ ζ m ν yc t z = 0) :
    ocEll q Λ m ν ^ 2 * t ∈ ocQuietTimes α q Λ ζ m := by
  intro y
  have he := (Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).ne'
  have hc : ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m ≠ 0 :=
    div_ne_zero (ocEll_sq_pos_of hΛ hν).ne' he
  have h1 := h0 ((ocEpsilon q Λ m)⁻¹ • (y - yc))
  unfold ocCellDrift at h1
  rw [smul_smul, mul_inv_cancel₀ he, one_smul, add_sub_cancel] at h1
  exact (smul_eq_zero.mp h1).resolve_left hc

theorem ocL_ge_one : (1 : ℝ) ≤ ocL α q Λ m := by
  have : 1 ≤ ocL α q Λ m := by unfold ocL; omega
  exact_mod_cast this

theorem ocTau_le_ocTauP (hΛ : 1 ≤ Λ) : ocTau α q Λ m ≤ ocTauP α q Λ m := by
  have hT := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ
  have hL : (1 : ℝ) ≤ ocL α q Λ m := ocL_ge_one
  unfold ocTau ocTauP
  rw [pow_two, ← div_div]
  exact div_le_self (div_nonneg hT.le (by linarith)) hL

theorem ocTauP_le_ocTauPP (hΛ : 1 ≤ Λ) : ocTauP α q Λ m ≤ ocTauPP α q Λ m := by
  have hT := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ
  unfold ocTauP
  exact div_le_self hT.le ocL_ge_one

theorem ocTau_le_ocTauPP (hΛ : 1 ≤ Λ) : ocTau α q Λ m ≤ ocTauPP α q Λ m :=
  (ocTau_le_ocTauP hΛ).trans (ocTauP_le_ocTauPP hΛ)

/-- `ϖ = √(η/S) = ε/√(B τ'')`. -/
theorem seamVarpi_eq (hΛ : 1 ≤ Λ) (hν : 0 < ν) {B : ℝ} (hB : 0 < B) :
    Real.sqrt ((ν / B) / (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)) =
      ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m) := by
  have he := Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hT := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ
  have hsq : (ν / B) / (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) =
      ocEpsilon q Λ m ^ 2 / (B * ocTauPP α q Λ m) := by
    rw [CycleReference.ocEll_sq_eq hν]
    field_simp
  rw [hsq, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq he.le]

/-- The positive-letter scale `ηg = √(B τ'')/E`. -/
def seamEtaG (α q : ℝ) (Λ m : ℕ) (B : ℝ) : ℝ :=
  Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)

theorem seamEtaG_pos (hΛ : 1 ≤ Λ) {B : ℝ} (hB : 0 < B) : 0 < seamEtaG α q Λ m B :=
  div_pos (Real.sqrt_pos.2 (mul_pos hB (Construction.Stream.ocTauPP_pos hΛ)))
    (Construction.Stream.ocEpsilon_pos hΛ)

theorem seamEtaG_le_one (hΛ : 1 ≤ Λ) {B : ℝ}
    (hRE : Real.sqrt (B * ocTauPP α q Λ m) ≤ ocEpsilon q Λ (m - 1)) :
    seamEtaG α q Λ m B ≤ 1 :=
  div_le_one_of_le₀ hRE (Construction.Stream.ocEpsilon_pos hΛ).le

/-- `δ = ε/E = ϖ ηg`. -/
theorem seam_delta_eq (hΛ : 1 ≤ Λ) {B : ℝ} (hB : 0 < B) :
    ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) =
      ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m) * seamEtaG α q Λ m B := by
  have hR := (Real.sqrt_pos.2 (mul_pos hB (Construction.Stream.ocTauPP_pos (α := α) (q := q)
    (m := m) hΛ))).ne'
  have hE := (Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ).ne'
  unfold seamEtaG
  field_simp

/-- `S = τ''/ℓ² ≥ 1`. -/
theorem seamS_ge_one (hΛ : 1 ≤ Λ) (hν : 0 < ν)
    (hellT : ocEll q Λ m ν ^ 2 ≤ ocTauPP α q Λ m) :
    1 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 :=
  (one_le_div (ocEll_sq_pos_of hΛ hν)).2 hellT

theorem seamBuffer_nonneg (hΛ : 1 ≤ Λ) (hν : 0 < ν) : 0 ≤ seamBuffer α q Λ m ν :=
  div_nonneg (Construction.Stream.ocTau_pos hΛ).le
    (mul_nonneg (by norm_num) (ocEll_sq_pos_of hΛ hν).le)

theorem seamBuffer_le_quiet_margin (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    seamBuffer α q Λ m ν ≤ ocTauP α q Λ m / ocEll q Λ m ν ^ 2 := by
  have hl := ocEll_sq_pos_of (q := q) (m := m) hΛ hν
  have hτ := Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  unfold seamBuffer
  rw [← div_div]
  exact div_le_div_of_nonneg_right ((div_le_self hτ.le (by norm_num)).trans
    (ocTau_le_ocTauP hΛ)) hl.le

theorem quietMargin_le_seamS (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    ocTauP α q Λ m / ocEll q Λ m ν ^ 2 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 :=
  div_le_div_of_nonneg_right (ocTauP_le_ocTauPP hΛ) (ocEll_sq_pos_of hΛ hν).le

/-- The trimmed quiet margin `(τ' - τ/24)/ℓ²` is nonnegative. -/
theorem trimmedQuietMargin_nonneg (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    0 ≤ (ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2 := by
  have hτ := ocTau_le_ocTauP (α := α) (q := q) (m := m) hΛ
  have hτ0 := Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  exact div_nonneg (by linarith) (ocEll_sq_pos_of hΛ hν).le

/-- The trimmed quiet margin fits in the block. -/
theorem trimmedQuietMargin_le_seamS (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    (ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2 ≤
      ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 := by
  have hτ0 := Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  exact div_le_div_of_nonneg_right (by linarith [ocTauP_le_ocTauPP (α := α) (q := q) (m := m) hΛ])
    (ocEll_sq_pos_of hΛ hν).le

end Scales

end AVRegularity.CycleJointProofs.Assembly
end
end
