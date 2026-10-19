-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.PatchBodies

section
/-! **One patch with the edge-free clause**.

* `realizeCellModel_congr`, `patchModel_slotZero_agree`: the patch model at slot `0` on
  truncated data is the truncation of the patch model at slots `K`, once the cell models agree
  (the return and the realization read only the cell model).
* `edgeFreeClauses_of_clausesK`: the clauses of a slot-`0` patch model give the bound and the error
  of the edge-free clause of the one-patch statement (order `Mout ≤ Mb`, truncation to slot `0` is the identity).

For the empty index type all sums are `0`. For slots `K = 0` the agreement is an identity of
truncations of order `0`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev Set
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
  AVRegularity.CycleReference
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

attribute [local instance] planeModelTorusNormed planeModelTorusInner planeModelTorusSpace
  planeModelPlaneNormed planeModelPlaneInner planeModelPlaneSpace planeModelTorusPiAdd
  planeModelTorusPiModule planeModelPlanePiAdd planeModelPlanePiModule

section Generic

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The realization of a cell model depends only on the cell model's value. -/
theorem realizeCellModel_congr {X X' : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup X']
    [Module ℝ X'] (Mb : ℕ) (Mc : X →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (Mc' : X' →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm' : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc' ξ x))
    (hmem' : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc' ξ x)) 2 volume)
    (ξ : X) (ξ' : X') (hξ : Mc ξ = Mc' ξ') :
    realizeCellModel Mb Mc hsm hmem ξ = realizeCellModel Mb Mc' hsm' hmem' ξ' := by
  funext x
  change CycleWords.smoothPlaneHk Mb (Mc ξ x) (contDiff_infty.2 fun k => hsm ξ x k) (hmem ξ x) =
    CycleWords.smoothPlaneHk Mb (Mc' ξ' x) (contDiff_infty.2 fun k => hsm' ξ' x k) (hmem' ξ' x)
  congr 1
  exact congrFun hξ x

end Generic

section Clauses

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The clauses of a slot-`0` patch model give the edge-free clause of the one-patch statement** (bound of order
`Mout ≤ Mb`, error at slot `0`). -/
theorem edgeFreeClauses_of_clausesK {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) {Mout Mb D : ℕ}
    {C c ε : ℝ} {n : ℕ} {π : ι → ℝ} {ν tS tp ρs ρold R : ℝ} {N : ℕ} {hN : 0 < N}
    {j : Fin 2 → Fin N} {y : Vec 2} {b : ℝ → Vec 2 → Vec 2}
    {A0 : ∀ (i i' : ι) (d : admissibleOrders (fun _ => 0) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {P₀ : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout 0) (h i))}
    (hMo : Mout ≤ Mb)
    (hP : PatchModelClausesK hζ Mout Mb D C c ε n π (fun _ => 0) ν tS tp ρs ρold R N hN j y b A0
      P₀) :
    (∀ g, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n R⁻¹ y (c * R) Mout (P₀ g i) ≤
      ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ *
        ‖spatialPatchLocalizationCLM hζ N hN j (g i)‖ ^ 2)) ∧
    IsPatchError π (fun _ => 0) Mout D ν tS tp ρs ρold R ε n y b A0
      (fun _ => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0) P₀ := by
  have htr : ∀ g : ∀ i, TorusHk 0 (h i),
      (fun i => truncateTorusHk (Nat.zero_le ((fun _ => 0 : ι → ℕ) i)) (g i)) = g :=
    fun g => funext fun i => truncateTorusHk_self (g i)
  refine ⟨fun g => ?_, fun f U W hU => ?_⟩
  · refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_right
      (weightedFactorialNormSq_order_mono n R⁻¹ y (c * R) hMo (P₀ g i)) _) ?_
    have hb := hP.1 g
    simp only [truncateTorusHk_self] at hb
    exact hb
  · have he := hP.2 f U W hU
    rw [← htr f] at he
    exact he

end Clauses

section Agree

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

/-- **The patch model at slot `0` agrees with the patch model at slots `K`** on truncated data,
when the cell models agree. -/
theorem patchModel_slotZero_agree (hΛ : 1 ≤ Λ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hedge : ∀ v u, IsEmpty (F.Γ v u)) (Mout : ℕ) {Mb : ℕ}
    (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb)
    (hmax0 : ∀ i, max Mout ((fun _ => 0 : ι → ℕ) i) ≤ Mb)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (Mc0 : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm0 : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc0 ξ x))
    (hmem0 : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc0 ξ x)) 2 volume)
    (hagree : ∀ ξ, Mc0 (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i)) = Mc ξ)
    (f : ∀ i, TorusHk (K i) (h i)) :
    patchModel hΛ (hp.slotZero hedge) Mout hMb hmax0 Mc0 hsm0 hmem0
        (fun i => truncateTorusHk (Nat.zero_le (K i)) (f i)) =
      planeFamilyTruncation (fun _ => max Mout 0) (fun i => max Mout (K i))
        (fun _ => max_le_max le_rfl (Nat.zero_le _))
        (patchModel hΛ hp Mout hMb hmax Mc hsm hmem f) := by
  funext i
  rw [patchModel_apply, realizeCellModel_congr Mb Mc0 hsm0 hmem0 Mc hsm hmem _ f (hagree f)]
  change _ = truncatePlaneHk _ (patchModel hΛ hp Mout hMb hmax Mc hsm hmem f i)
  rw [patchModel_apply, truncatePlaneHk_truncatePlaneHk]
  rfl

/-- **The slot-`K` patch model from the outputs of the two-block theorem and the seam** (the moments are taken from
their body here). -/
theorem patchClausesK_of_C2 (hI : MassInterpolationStatement.{u, v})
    (hW : WeightedPullbackStatement.{v}) {s : ℝ} (hq : IsAdmissibleQ α s q)
    {Λ₀' : ℕ} (hΛ₀' : Λ₀' ≤ Λ) (hΛ128 : 128 ≤ Λ) (hΛ : 1 ≤ Λ)
    (hg₀ : g₀ ≤ 1 / 32) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (hD : 2 ≤ D) (hKs : Ks + 1 ≤ Jm) (hqJ : Ks + 1 + Kmax ≤ qJ) (hζ : IsFastProfile ζ)
    -- the moment body
    {Cw' : ℕ → ℝ} {Cenergy1' Cprep' CTm : ℝ} {Mb n' Npre : ℕ} {CM CNp : ℝ}
    (hG4 : TwoBlockMomentBody.{u, v, w, x} α q hζ Cw' Λ₀' D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1' Cprep' CTm n' Npre)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (hNR : 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m))
    (hNpre' : (Ks + 1) + H * (Ks + 1) ≤ Npre)
    (hgain' : ENNReal.ofReal (CTm * g * (Real.sqrt (B * ocTauPP α q Λ m) /
      ocEpsilon q Λ (m - 1))) ≤ 1)
    (Mout : ℕ) (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb)
    (n : ℕ) (hnn : n ≤ n') (hn' : 0 < n') (εB : ℝ) (hCM : 0 ≤ CM) (hCNp : 0 ≤ CNp)
    -- the two-block theorem
    (uphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : twoPhysical hp hζ N hN (fun k => (j k : ℤ)) uphys wphys)
    (uFsum : (∀ i, TorusHk (K i) (h i)) → ∀ i, PlaneHk Set.univ (K i) (h i))
    (Cpost Cseam Cfirst εlow εhigh εpost : ℝ≥0∞) (q2 : ℝ) (hq2 : 0 ≤ q2)
    (hQ2 : 2 * (Cpost * Cseam * εlow + εpost * (2 * (Cfirst + εhigh))) ≤ ENNReal.ofReal q2)
    (herrC2 : ∀ ξ, ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq r
        (uphys ξ i (twoTp α q Λ m l₀) - twoReturn hp hΛ hchart i (uFsum ξ i)).val) ≤
      twoBlockOriginalEnergyPrice
        (ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart)
          (Jchart + 1) * |ocEpsilon q Λ m|) ^ 2)) Cpost Cseam Cfirst εlow εhigh εpost *
        twoEin hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) Npre ξ)
    -- the seam
    (Mc0 : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm0 : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc0 ξ x))
    (hmodel0 : ∀ ξ, weightedJetNorm π (n' : ℝ) Mb
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc0 ξ x) z) ≤
      ENNReal.ofReal CM * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    (herr0 : ∀ ξ, weightedJetNorm π (n' : ℝ) Kmax
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m)
        (fun x a' wd z => if a' ≤ K x then
          planeJetOrder (uFsum ξ x) a' wd z - orderedDerivative wd (Mc0 ξ x) z else 0) ≤
      ENNReal.ofReal CNp * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    -- the prices
    (qm : ℝ) (hqm : 0 ≤ qm)
    (hQm : twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0 * Θ) n' *
        twoCfirst hp Cw' Cenergy1' Npre ≤ ENNReal.ofReal qm)
    (hprice : patchErrorPrice0 Cchart (ocEpsilon q Λ (m - 1)) Kmax
        (compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) ^ 2 * q2 *
          datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre) CNp
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ (1 - (n : ℝ) / n') *
      patchErrorPrice1 Cchart (ocEpsilon q Λ (m - 1)) Kmax Mb n'
        (qm * datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre) CM
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ ((n : ℝ) / n') ≤
      εB ^ 2) :
    PatchModelClausesK hζ Mout Mb D
      (Real.sqrt (patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM)) 1 εB n π K ν tS
      (twoTp α q Λ m l₀) r ρold (Real.sqrt (B * ocTauPP α q Λ m)) N hN j
      (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) (streamVel (Φ m))
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (patchModel hΛ hp Mout hMb hmax Mc0 hsm0
        (cellModel_memLp hΛ hchart hζ hp N hN j Mb n' CM Mc0 hsm0 hmodel0)) := by
  obtain ⟨uphys', wphys', hsol', hmom⟩ := hG4 Λ hΛ₀' hΛ g₀ hg₀ H Ls qJ hD hKs hqJ Ca Cth Cb
    COld Crat Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A
    Θ T r ρold hp (ocTrimmedQuietTimes α q Λ ζ m) (JointPremisesGen.coreOutside hΛ hp)
    hp.hquiet N hN (fun k => (j k : ℤ)) hNpre' hgain'
  exact patchModelClausesK_of_outputs hI hW hq hΛ128 hΛ hg₀
    hchart hmol hζ hp N hN j hyc hNR Mout hMb hmax n n' Npre hnn hn' CM CNp εB hCM hCNp uphys
    wphys hsol uFsum Cpost Cseam Cfirst εlow εhigh εpost q2 hq2 hQ2 herrC2 Mc0 hsm0 hmodel0 herr0
    uphys' wphys' hsol' _ qm hqm hQm (fun ξ => (hmom ξ).trans (le_of_eq (mul_assoc _ _ _).symm))
    hprice

/-- **A lower-slot patch model from the outputs of the two-block theorem and the seam** (edge-free clause; the moments are taken
from their body here). -/
theorem patchSlotLower_of_C2 (hI : MassInterpolationStatement.{u, v})
    (hW : WeightedPullbackStatement.{v}) {s : ℝ} (hq : IsAdmissibleQ α s q)
    {Λ₀' : ℕ} (hΛ₀' : Λ₀' ≤ Λ) (hΛ128 : 128 ≤ Λ) (hΛ : 1 ≤ Λ)
    (hg₀ : g₀ ≤ 1 / 32) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (hD : 2 ≤ D) (hKs : Ks + 1 ≤ Jm) (hqJ : Ks + 1 + Kmax ≤ qJ) (hζ : IsFastProfile ζ)
    -- the moment body
    {Cw' : ℕ → ℝ} {Cenergy1' Cprep' CTm : ℝ} {Mb n' Npre : ℕ} {CM CNp : ℝ}
    (hG4 : TwoBlockMomentBody.{u, v, w, x} α q hζ Cw' Λ₀' D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1' Cprep' CTm n' Npre)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    {K0 : ι → ℕ} (hK0 : ∀ i, K0 i ≤ K i)
    (hp0 : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K0 Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F
      actual A Θ T r ρold) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (hNR : 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m))
    (hNpre' : (Ks + 1) + H * (Ks + 1) ≤ Npre)
    (hgain' : ENNReal.ofReal (CTm * g * (Real.sqrt (B * ocTauPP α q Λ m) /
      ocEpsilon q Λ (m - 1))) ≤ 1)
    (Mout : ℕ) (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb) (hMo : Mout ≤ Mb)
    (n : ℕ) (hnn : n ≤ n') (hn' : 0 < n') (εB : ℝ) (hCM : 0 ≤ CM) (hCNp : 0 ≤ CNp)
    -- the two-block theorem at the lower slots
    (uphys : (∀ i, TorusHk (K0 i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K0 i) (h i))
    (wphys : (∀ i, TorusHk (K0 i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K0 i + 1) (h i))
    (hsol : twoPhysical hp0 hζ N hN (fun k => (j k : ℤ)) uphys wphys)
    (uFsum : (∀ i, TorusHk (K0 i) (h i)) → ∀ i, PlaneHk Set.univ (K0 i) (h i))
    (Cpost Cseam Cfirst εlow εhigh εpost : ℝ≥0∞) (q2 : ℝ) (hq2 : 0 ≤ q2)
    (hQ2 : 2 * (Cpost * Cseam * εlow + εpost * (2 * (Cfirst + εhigh))) ≤ ENNReal.ofReal q2)
    (herrC2 : ∀ ξ, ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq r
        (uphys ξ i (twoTp α q Λ m l₀) - twoReturn hp0 hΛ hchart i (uFsum ξ i)).val) ≤
      twoBlockOriginalEnergyPrice
        (ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart)
          (Jchart + 1) * |ocEpsilon q Λ m|) ^ 2)) Cpost Cseam Cfirst εlow εhigh εpost *
        twoEin hp0 hΛ hchart hζ N hN (fun k => (j k : ℤ)) Npre ξ)
    -- the seam at the lower slots
    (Mc0 : (∀ i, TorusHk (K0 i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm0 : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc0 ξ x))
    (hmodel0 : ∀ ξ, weightedJetNorm π (n' : ℝ) Mb
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc0 ξ x) z) ≤
      ENNReal.ofReal CM * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp0 hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    (herr0 : ∀ ξ, weightedJetNorm π (n' : ℝ) Kmax
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m)
        (fun x a' wd z => if a' ≤ K0 x then
          planeJetOrder (uFsum ξ x) a' wd z - orderedDerivative wd (Mc0 ξ x) z else 0) ≤
      ENNReal.ofReal CNp * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp0 hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    -- the prices
    (qm : ℝ) (hqm : 0 ≤ qm)
    (hQm : twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0 * Θ) n' *
        twoCfirst hp0 Cw' Cenergy1' Npre ≤ ENNReal.ofReal qm)
    (hprice : patchErrorPrice0 Cchart (ocEpsilon q Λ (m - 1)) Kmax
        (compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) ^ 2 * q2 *
          datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre) CNp
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ (1 - (n : ℝ) / n') *
      patchErrorPrice1 Cchart (ocEpsilon q Λ (m - 1)) Kmax Mb n'
        (qm * datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre) CM
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ ((n : ℝ) / n') ≤
      εB ^ 2)
    -- the slot-`K` cell model and the agreement
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmodel : ∀ ξ, weightedJetNorm π (n' : ℝ) Mb
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc ξ x) z) ≤
      ENNReal.ofReal CM * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    (hagree : ∀ ξ, Mc0 (fun i => truncateTorusHk (hK0 i) (ξ i)) = Mc ξ)
    (hP : ∀ (hmax0 : ∀ i, max Mout (K0 i) ≤ Mb)
      (Mc0 : (∀ i, TorusHk (K0 i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
      (hsm0 : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc0 ξ x))
      (hmem0 : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc0 ξ x)) 2 volume),
      (∀ ξ, Mc0 (fun i => truncateTorusHk (hK0 i) (ξ i)) = Mc ξ) → ∀ f,
      patchModel hΛ hp0 Mout hMb hmax0 Mc0 hsm0 hmem0
          (fun i => truncateTorusHk (hK0 i) (f i)) =
        planeFamilyTruncation (fun i => max Mout (K0 i)) (fun i => max Mout (K i))
          (fun i => max_le_max le_rfl (hK0 i))
          (patchModel hΛ hp Mout hMb hmax Mc hsm
            (cellModel_memLp hΛ hchart hζ hp N hN j Mb n' CM Mc hsm hmodel) f)) :
    ∃ P₀ : (∀ i, TorusHk (K0 i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K0 i)) (h i)),
      (∀ f, P₀ (fun i => truncateTorusHk (hK0 i) (f i)) =
        planeFamilyTruncation (fun i => max Mout (K0 i)) (fun i => max Mout (K i))
          (fun i => max_le_max le_rfl (hK0 i))
          (patchModel hΛ hp Mout hMb hmax Mc hsm
            (cellModel_memLp hΛ hchart hζ hp N hN j Mb n' CM Mc hsm hmodel) f)) ∧
      PatchModelClausesK hζ Mout Mb D
        (Real.sqrt (patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM)) 1 εB n π K0 ν tS
        (twoTp α q Λ m l₀) r ρold (Real.sqrt (B * ocTauPP α q Λ m)) N hN j
        (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) (streamVel (Φ m))
        (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K0) P₀ := by
  obtain ⟨uphys', wphys', hsol', hmom⟩ := hG4 Λ hΛ₀' hΛ g₀ hg₀ H Ls qJ hD hKs hqJ Ca Cth Cb
    COld Crat Cpad Cage Npad mStar π K0 Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A
    Θ T r ρold hp0 (ocTrimmedQuietTimes α q Λ ζ m) (JointPremisesGen.coreOutside hΛ hp0)
    hp0.hquiet N hN (fun k => (j k : ℤ)) hNpre' hgain'
  have hmax0 : ∀ i, max Mout (K0 i) ≤ Mb := fun i =>
    max_le hMo ((hK0 i).trans ((le_max_right _ _).trans (hmax i)))
  exact ⟨_, hP hmax0 Mc0 hsm0 _ hagree, patchModelClausesK_of_outputs hI hW hq hΛ128 hΛ hg₀
    hchart hmol hζ hp0 N hN j hyc hNR Mout hMb hmax0 n n' Npre hnn hn' CM CNp εB hCM hCNp uphys
    wphys hsol uFsum Cpost Cseam Cfirst εlow εhigh εpost q2 hq2 hQ2 herrC2 Mc0 hsm0 hmodel0 herr0
    uphys' wphys' hsol' _ qm hqm hQm (fun ξ => (hmom ξ).trans (le_of_eq (mul_assoc _ _ _).symm))
    hprice⟩

/-- **A lower-slot patch model from the bodies** (edge-free clause, generic in the lower slots `K0 ≤ K` and
their premises `hp0`): the two-block theorem, the seam's lower-slot clause and the moments at slots `K0` give a
patch model at slots `K0` with its clauses, agreeing on truncated data with the slot-`K` patch
model of the cell model `Mc`. The edge-free clause of the one-patch statement is the instance `K0 = 0`. -/
theorem patchSlotLower_of_bodies (hI : MassInterpolationStatement.{u, v})
    (hW : WeightedPullbackStatement.{v}) {s : ℝ} (hq : IsAdmissibleQ α s q)
    {Λ₀ Λ₀' : ℕ} (hΛ₀ : Λ₀ ≤ Λ) (hΛ₀' : Λ₀' ≤ Λ) (hΛ128 : 128 ≤ Λ) (hΛ : 1 ≤ Λ)
    (hg₀ : g₀ ≤ 1 / 32) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (hD : 2 ≤ D) (hKs : Ks + 1 ≤ Jm) (hqJ : Ks + 1 + Kmax ≤ qJ) (hζ : IsFastProfile ζ)
    -- body of the two-block theorem
    {Cw : ℕ → ℝ} {Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem : ℝ} {Npre Npost Lpre Lpost : ℕ}
    (hC2 : TwoBlockJointBody.{u, v, w, x} α q hζ Cw Λ₀ D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem Npre Npost Lpre Lpost)
    -- the moment body
    {Cw' : ℕ → ℝ} {Cenergy1' Cprep' CTm : ℝ} {Jpre Jpost Mb Q Ns n' : ℕ} {CL CM CN c : ℝ}
    (hG4 : TwoBlockMomentBody.{u, v, w, x} α q hζ Cw' Λ₀' D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1' Cprep' CTm n' Npre)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    {K0 : ι → ℕ} (hK0 : ∀ i, K0 i ≤ K i)
    (hp0 : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K0 Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F
      actual A Θ T r ρold) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (hNR : 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m))
    -- premises of the two-block theorem
    (hNpre : Npost + (Ks + 1) + (Jpre + H) * (Ks + 1) ≤ Npre)
    (hNpost : (Ks + 1) + (Jpost + H) * (Ks + 1) ≤ Npost)
    (hgain : ENNReal.ofReal (CT * g * (Real.sqrt (B * ocTauPP α q Λ m) /
      ocEpsilon q Λ (m - 1))) ≤ 1)
    (hCN : 0 ≤ CN) (hCM : 0 ≤ CM)
    -- the moment premises
    (hNpre' : (Ks + 1) + H * (Ks + 1) ≤ Npre)
    (hgain' : ENNReal.ofReal (CTm * g * (Real.sqrt (B * ocTauPP α q Λ m) /
      ocEpsilon q Λ (m - 1))) ≤ 1)
    -- orders and prices
    (Mout : ℕ) (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb) (hMo : Mout ≤ Mb)
    (n : ℕ) (hnn : n ≤ n') (hn' : 0 < n') (εB q2 qm : ℝ) (hq2 : 0 ≤ q2) (hqm : 0 ≤ qm)
    (hQ2 : 2 * (twoCactual hp0 Cw Cenergy2 * ENNReal.ofReal (cellTransitionMomentBudget Kmax 0) *
        twoEpsPre hp0 Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre +
        twoEpsPost hp0 Cw Cprep CR Cterminal Crem Npost Lpost Jpost *
          (2 * (twoCfirst hp0 Cw Cenergy1 Npre +
            twoEpsPre hp0 Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre))) ≤ ENNReal.ofReal q2)
    (hQm : twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0 * Θ) n' *
        twoCfirst hp0 Cw' Cenergy1' Npre ≤ ENNReal.ofReal qm)
    (hprice : patchErrorPrice0 Cchart (ocEpsilon q Λ (m - 1)) Kmax
        (compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) ^ 2 * q2 *
          datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre)
        (CN * seamWindowPrice α q Λ m ν B Q Ns c)
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ (1 - (n : ℝ) / n') *
      patchErrorPrice1 Cchart (ocEpsilon q Λ (m - 1)) Kmax Mb n'
        (qm * datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre) CM
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ ((n : ℝ) / n') ≤
      εB ^ 2)
    -- the slot-`K` cell model and the seam's edge-free clause
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmodel : ∀ ξ, weightedJetNorm π (n' : ℝ) Mb
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc ξ x) z) ≤
      ENNReal.ofReal CM * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    (hG2e : SeamDatumSupport hp0 hΛ hchart hζ ((1 + max (Cchart 0) 0 / 2) / 8) N
        hN (fun k => (j k : ℤ)) →
      ∀ uO0 wO0 uF0 wF0, SeamWordChains hp0 hΛ hchart hζ CL Jpre Jpost N hN
        (fun k => (j k : ℤ)) uO0 wO0 uF0 wF0 → SeamOldMoments hp0 Jpre wO0 →
      ∃ Mc0 : (∀ i, TorusHk (K0 i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x),
        SeamModelClauses hp0 hΛ hchart hζ Jpre Jpost Mb n' Q Ns CM CN c N hN
          (fun k => (j k : ℤ)) uF0 Mc0 ∧
        ∀ ξ, Mc0 (fun i => truncateTorusHk (hK0 i) (ξ i)) = Mc ξ)
    (hP : ∀ (hmax0 : ∀ i, max Mout (K0 i) ≤ Mb)
      (Mc0 : (∀ i, TorusHk (K0 i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
      (hsm0 : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc0 ξ x))
      (hmem0 : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc0 ξ x)) 2 volume),
      (∀ ξ, Mc0 (fun i => truncateTorusHk (hK0 i) (ξ i)) = Mc ξ) → ∀ f,
      patchModel hΛ hp0 Mout hMb hmax0 Mc0 hsm0 hmem0
          (fun i => truncateTorusHk (hK0 i) (f i)) =
        planeFamilyTruncation (fun i => max Mout (K0 i)) (fun i => max Mout (K i))
          (fun i => max_le_max le_rfl (hK0 i))
          (patchModel hΛ hp Mout hMb hmax Mc hsm
            (cellModel_memLp hΛ hchart hζ hp N hN j Mb n' CM Mc hsm hmodel) f)) :
    ∃ P₀ : (∀ i, TorusHk (K0 i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K0 i)) (h i)),
      (∀ f, P₀ (fun i => truncateTorusHk (hK0 i) (f i)) =
        planeFamilyTruncation (fun i => max Mout (K0 i)) (fun i => max Mout (K i))
          (fun i => max_le_max le_rfl (hK0 i))
          (patchModel hΛ hp Mout hMb hmax Mc hsm
            (cellModel_memLp hΛ hchart hζ hp N hN j Mb n' CM Mc hsm hmodel) f)) ∧
      PatchModelClausesK hζ Mout Mb D
        (Real.sqrt (patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM)) 1 εB n π K0 ν tS
        (twoTp α q Λ m l₀) r ρold (Real.sqrt (B * ocTauPP α q Λ m)) N hN j
        (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) (streamVel (Φ m))
        (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K0) P₀ := by
  have hcore0 := JointPremisesGen.coreOutside hΛ hp0
  obtain ⟨uphys0, wphys0, hsol0, uO0, wO0, uF0, wF0, hchO0, hchF0, hlinO0, -, -, hEO0, herr0⟩ :=
    hC2 Λ hΛ₀ hΛ g₀ hg₀ H Ls qJ hD hKs hqJ Ca Cth Cb COld Crat Cpad Cage Npad mStar π K0
      Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T r ρold hp0
      (ocTrimmedQuietTimes α q Λ ζ m) hcore0 hp0.hquiet N hN (fun k => (j k : ℤ))
      Jpre Jpost hNpre hNpost hgain (CL * g) (CL * (Cth * Θ)) (CL * g) (CL * (Cth * Θ))
      (fun v u => if v = u then CL * g else 0) (fun v u => CL * (Real.sqrt (π u / π v) * A v u))
      (fun v u => if v = u then CL * g else 0) (fun v u => CL * (Real.sqrt (π u / π v) * A v u))
  obtain ⟨Mc0, ⟨hsm0, hmodel0, herrS0⟩, hagree⟩ := hG2e
    (fun ξ i => twoV₀_support hΛ hchart hζ hp0 N hN (fun k => (j k : ℤ)) hyc
      (Real.sqrt (B * ocTauPP α q Λ m)) hNR ξ i) uO0 wO0 uF0 wF0 ⟨hchO0, hchF0, hlinO0⟩ hEO0
  have hS : 0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 :=
    div_nonneg (Construction.Stream.ocTauPP_pos hΛ).le (sq_nonneg _)
  exact patchSlotLower_of_C2 hI hW hq hΛ₀' hΛ128 hΛ hg₀ hchart hmol hD hKs hqJ hζ hG4 hp hK0 hp0
    N hN j hyc hNR hNpre' hgain' Mout hMb hmax hMo n hnn hn' εB hCM
    (mul_nonneg hCN (seamWindowPrice_nonneg hΛ hS)) uphys0 wphys0 hsol0
    (fun ξ i => ∑ wo ∈ blockWords Jpre H, ∑ wf ∈ blockWords Jpost H,
      uF0 wo wf ξ (Fin.last _) i (cellTime q Λ m ν (twoTp α q Λ m l₀)))
    _ _ _ _ _ _ q2 hq2 hQ2 herr0 Mc0 hsm0 (fun ξ => hmodel0 ξ Mb le_rfl) herrS0 qm hqm hQm hprice
    Mc hsm hmodel hagree hP

/-- **The edge-free clause of the one-patch statement for one patch from the bodies**: for a family without edges, the
lower-slot patch model at slot `0` (`patchSlotLower_of_bodies` at `hp.slotZero`). -/
theorem patchEdgeFree_of_bodies (hI : MassInterpolationStatement.{u, v})
    (hW : WeightedPullbackStatement.{v}) {s : ℝ} (hq : IsAdmissibleQ α s q)
    {Λ₀ Λ₀' : ℕ} (hΛ₀ : Λ₀ ≤ Λ) (hΛ₀' : Λ₀' ≤ Λ) (hΛ128 : 128 ≤ Λ) (hΛ : 1 ≤ Λ)
    (hg₀ : g₀ ≤ 1 / 32) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (hD : 2 ≤ D) (hKs : Ks + 1 ≤ Jm) (hqJ : Ks + 1 + Kmax ≤ qJ) (hζ : IsFastProfile ζ)
    -- body of the two-block theorem
    {Cw : ℕ → ℝ} {Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem : ℝ} {Npre Npost Lpre Lpost : ℕ}
    (hC2 : TwoBlockJointBody.{u, v, w, x} α q hζ Cw Λ₀ D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem Npre Npost Lpre Lpost)
    -- the moment body
    {Cw' : ℕ → ℝ} {Cenergy1' Cprep' CTm : ℝ} {Jpre Jpost Mb Q Ns n' : ℕ} {CL CM CN c : ℝ}
    (hG4 : TwoBlockMomentBody.{u, v, w, x} α q hζ Cw' Λ₀' D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1' Cprep' CTm n' Npre)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (hedge : ∀ v u, IsEmpty (F.Γ v u)) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (hNR : 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m))
    -- premises of the two-block theorem
    (hNpre : Npost + (Ks + 1) + (Jpre + H) * (Ks + 1) ≤ Npre)
    (hNpost : (Ks + 1) + (Jpost + H) * (Ks + 1) ≤ Npost)
    (hgain : ENNReal.ofReal (CT * g * (Real.sqrt (B * ocTauPP α q Λ m) /
      ocEpsilon q Λ (m - 1))) ≤ 1)
    (hCN : 0 ≤ CN) (hCM : 0 ≤ CM)
    -- the moment premises
    (hNpre' : (Ks + 1) + H * (Ks + 1) ≤ Npre)
    (hgain' : ENNReal.ofReal (CTm * g * (Real.sqrt (B * ocTauPP α q Λ m) /
      ocEpsilon q Λ (m - 1))) ≤ 1)
    -- orders and prices
    (Mout : ℕ) (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb) (hMo : Mout ≤ Mb)
    (n : ℕ) (hnn : n ≤ n') (hn' : 0 < n') (εB q2 qm : ℝ) (hq2 : 0 ≤ q2) (hqm : 0 ≤ qm)
    (hQ2 : 2 * (twoCactual hp Cw Cenergy2 * ENNReal.ofReal (cellTransitionMomentBudget Kmax 0) *
        twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre +
        twoEpsPost hp Cw Cprep CR Cterminal Crem Npost Lpost Jpost *
          (2 * (twoCfirst hp Cw Cenergy1 Npre +
            twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre))) ≤ ENNReal.ofReal q2)
    (hQm : twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0 * Θ) n' *
        twoCfirst hp Cw' Cenergy1' Npre ≤ ENNReal.ofReal qm)
    (hprice : patchErrorPrice0 Cchart (ocEpsilon q Λ (m - 1)) Kmax
        (compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) ^ 2 * q2 *
          datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre)
        (CN * seamWindowPrice α q Λ m ν B Q Ns c)
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ (1 - (n : ℝ) / n') *
      patchErrorPrice1 Cchart (ocEpsilon q Λ (m - 1)) Kmax Mb n'
        (qm * datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre) CM
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ ((n : ℝ) / n') ≤
      εB ^ 2)
    -- the slot-`K` cell model and the seam's edge-free clause
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmodel : ∀ ξ, weightedJetNorm π (n' : ℝ) Mb
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc ξ x) z) ≤
      ENNReal.ofReal CM * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    (hG2e : SeamDatumSupport (hp.slotZero hedge) hΛ hchart hζ ((1 + max (Cchart 0) 0 / 2) / 8) N
        hN (fun k => (j k : ℤ)) →
      ∀ uO0 wO0 uF0 wF0, SeamWordChains (hp.slotZero hedge) hΛ hchart hζ CL Jpre Jpost N hN
        (fun k => (j k : ℤ)) uO0 wO0 uF0 wF0 → SeamOldMoments (hp.slotZero hedge) Jpre wO0 →
      ∃ Mc0 : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x),
        SeamModelClauses (hp.slotZero hedge) hΛ hchart hζ Jpre Jpost Mb n' Q Ns CM CN c N hN
          (fun k => (j k : ℤ)) uF0 Mc0 ∧
        ∀ ξ, Mc0 (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i)) = Mc ξ) :
    ∃ P₀ : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout 0) (h i)),
      (∀ f, P₀ (fun i => truncateTorusHk (Nat.zero_le (K i)) (f i)) =
        planeFamilyTruncation (fun _ => max Mout 0) (fun i => max Mout (K i))
          (fun _ => max_le_max le_rfl (Nat.zero_le _))
          (patchModel hΛ hp Mout hMb hmax Mc hsm
            (cellModel_memLp hΛ hchart hζ hp N hN j Mb n' CM Mc hsm hmodel) f)) ∧
      (∀ g, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq n (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
            (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j)
            (1 * Real.sqrt (B * ocTauPP α q Λ m)) Mout (P₀ g i) ≤
        ENNReal.ofReal (Real.sqrt (patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM) ^ 2
          * ∑ i, (π i)⁻¹ * ‖spatialPatchLocalizationCLM hζ N hN j (g i)‖ ^ 2)) ∧
      IsPatchError π (fun _ => 0) Mout D ν tS (twoTp α q Λ m l₀) r ρold
        (Real.sqrt (B * ocTauPP α q Λ m)) εB n
        (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) (streamVel (Φ m))
        (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (fun _ => 0))
        (fun _ => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0) P₀ := by
  obtain ⟨P₀, hagr, hcl⟩ := patchSlotLower_of_bodies hI hW hq hΛ₀ hΛ₀' hΛ128 hΛ hg₀ hchart hmol hD
    hKs hqJ hζ hC2 hG4 hp (fun i => Nat.zero_le (K i)) (hp.slotZero hedge) N hN j hyc hNR hNpre
    hNpost hgain hCN hCM hNpre' hgain' Mout hMb hmax hMo n hnn hn' εB q2 qm hq2 hqm hQ2 hQm hprice
    Mc hsm hmodel hG2e (fun hmax0 Mc0 hsm0 hmem0 hag f =>
      patchModel_slotZero_agree hΛ hp hedge Mout hMb hmax hmax0 Mc hsm _ Mc0 hsm0 hmem0 hag f)
  exact ⟨P₀, hagr, edgeFreeClauses_of_clausesK hζ hMo hcl⟩

/-- **One patch with the edge-free clause of the one-patch statement, from the bodies**: the slot-`K` patch model with its
clauses (`patchClausesK_of_C2`) and, for a family without edges, the slot-`0` patch model agreeing
with it (`patchEdgeFree_of_bodies`). -/
theorem patchSmoothModel_of_bodies (hI : MassInterpolationStatement.{u, v})
    (hW : WeightedPullbackStatement.{v}) {s : ℝ} (hq : IsAdmissibleQ α s q)
    {Λ₀ Λ₀' : ℕ} (hΛ₀ : Λ₀ ≤ Λ) (hΛ₀' : Λ₀' ≤ Λ) (hΛ128 : 128 ≤ Λ) (hΛ : 1 ≤ Λ)
    (hg₀ : g₀ ≤ 1 / 32) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (hD : 2 ≤ D) (hKs : Ks + 1 ≤ Jm) (hqJ : Ks + 1 + Kmax ≤ qJ) (hζ : IsFastProfile ζ)
    -- body of the two-block theorem
    {Cw : ℕ → ℝ} {Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem : ℝ} {Npre Npost Lpre Lpost : ℕ}
    (hC2 : TwoBlockJointBody.{u, v, w, x} α q hζ Cw Λ₀ D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem Npre Npost Lpre Lpost)
    -- the seam's body
    {g₁ Θlong : ℝ} {Jpre Jpost Mb Q Ns n' : ℕ} {CL CM CN c : ℝ}
    (hG2 : SeamAllocationBody.{u, v, w, x} α q Λ hζ g₁ Θlong D H Kmax Ks Jpre Jpost Mb n' Q Ns Ls
      Jm qJ Jchart hchart Ca ((1 + max (Cchart 0) 0 / 2) / 8) Cpad Cage Cm CG Cchart CL Cth CM CN
      c)
    -- the moment body
    {Cw' : ℕ → ℝ} {Cenergy1' Cprep' CTm : ℝ}
    (hG4 : TwoBlockMomentBody.{u, v, w, x} α q hζ Cw' Λ₀' D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1' Cprep' CTm n' Npre)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (hNR : 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m))
    -- premises of the two-block theorem
    (hNpre : Npost + (Ks + 1) + (Jpre + H) * (Ks + 1) ≤ Npre)
    (hNpost : (Ks + 1) + (Jpost + H) * (Ks + 1) ≤ Npost)
    (hgain : ENNReal.ofReal (CT * g * (Real.sqrt (B * ocTauPP α q Λ m) /
      ocEpsilon q Λ (m - 1))) ≤ 1)
    -- the seam's premises
    (hg₀₁ : g₀ ≤ g₁) (hCth : 0 ≤ Cth * Θ) (hg₁ : g + ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ g₁)
    (hlong : Θlong ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2)
    (hbudget : seamWindowBudget α q Λ m ν B Q c ≤ 1) (hCN : 0 ≤ CN) (hCM : 0 ≤ CM)
    -- the moment premises
    (hNpre' : (Ks + 1) + H * (Ks + 1) ≤ Npre)
    (hgain' : ENNReal.ofReal (CTm * g * (Real.sqrt (B * ocTauPP α q Λ m) /
      ocEpsilon q Λ (m - 1))) ≤ 1)
    -- orders and prices
    (Mout : ℕ) (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb) (hMo : Mout ≤ Mb)
    (n : ℕ) (hnn : n ≤ n') (hn' : 0 < n') (εB q2 qm : ℝ) (hq2 : 0 ≤ q2) (hqm : 0 ≤ qm)
    (hQ2 : 2 * (twoCactual hp Cw Cenergy2 * ENNReal.ofReal (cellTransitionMomentBudget Kmax 0) *
        twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre +
        twoEpsPost hp Cw Cprep CR Cterminal Crem Npost Lpost Jpost *
          (2 * (twoCfirst hp Cw Cenergy1 Npre +
            twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre))) ≤ ENNReal.ofReal q2)
    (hQm : twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0 * Θ) n' *
        twoCfirst hp Cw' Cenergy1' Npre ≤ ENNReal.ofReal qm)
    (hprice : patchErrorPrice0 Cchart (ocEpsilon q Λ (m - 1)) Kmax
        (compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) ^ 2 * q2 *
          datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre)
        (CN * seamWindowPrice α q Λ m ν B Q Ns c)
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ (1 - (n : ℝ) / n') *
      patchErrorPrice1 Cchart (ocEpsilon q Λ (m - 1)) Kmax Mb n'
        (qm * datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre) CM
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ ((n : ℝ) / n') ≤
      εB ^ 2) :
    PatchSmoothModel hζ Mout Mb D
      (Real.sqrt (patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM)) 1 εB n π K ν tS
      (twoTp α q Λ m l₀) r ρold (Real.sqrt (B * ocTauPP α q Λ m)) N hN j
      (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) (streamVel (Φ m))
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (fun _ => 0))
      (∀ v u, IsEmpty (F.Γ v u)) := by
  have hcore := hp.coreOutside hΛ
  obtain ⟨uphys, wphys, hsol, uO, wO, uF, wF, hchO, hchF, hlinO, -, -, hEO, herrC2⟩ :=
    hC2 Λ hΛ₀ hΛ g₀ hg₀ H Ls qJ hD hKs hqJ Ca Cth Cb COld Crat Cpad Cage Npad mStar π K Φ M' κ m ν
      B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T r ρold hp (ocTrimmedQuietTimes α q Λ ζ m) hcore
      hp.hquiet N hN (fun k => (j k : ℤ)) Jpre Jpost hNpre hNpost hgain (CL * g) (CL * (Cth * Θ))
      (CL * g) (CL * (Cth * Θ)) (fun v u => if v = u then CL * g else 0)
      (fun v u => CL * (Real.sqrt (π u / π v) * A v u)) (fun v u => if v = u then CL * g else 0)
      (fun v u => CL * (Real.sqrt (π u / π v) * A v u))
  obtain ⟨Mc, ⟨hsm, hmodel, herr⟩, hG2e⟩ := hG2 g₀ Cb COld Crat Npad mStar hΛ π K Φ M' κ m ν B hφ
    tS g a B₀ lam l₀ P y₀ F actual A Θ T r ρold hp hg₀₁ hCth hg₁ hlong hbudget N hN
    (fun k => (j k : ℤ)) (fun ξ i => twoV₀_support hΛ hchart hζ hp N hN (fun k => (j k : ℤ)) hyc
      (Real.sqrt (B * ocTauPP α q Λ m)) hNR ξ i) uO wO uF wF ⟨hchO, hchF, hlinO⟩
  have hS : 0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 :=
    div_nonneg (Construction.Stream.ocTauPP_pos hΛ).le (sq_nonneg _)
  have hK := patchClausesK_of_C2 hI hW hq hΛ₀' hΛ128 hΛ hg₀ hchart hmol hD hKs hqJ hζ hG4 hp N hN
    j hyc hNR hNpre' hgain' Mout hMb hmax n hnn hn' εB hCM
    (mul_nonneg hCN (seamWindowPrice_nonneg hΛ hS)) uphys wphys hsol
    (fun ξ i => ∑ wo ∈ blockWords Jpre H, ∑ wf ∈ blockWords Jpost H,
      uF wo wf ξ (Fin.last _) i (cellTime q Λ m ν (twoTp α q Λ m l₀)))
    _ _ _ _ _ _ q2 hq2 hQ2 herrC2 Mc hsm (fun ξ => hmodel ξ Mb le_rfl) herr qm hqm hQm hprice
  exact ⟨_, hK.1, hK.2, fun hedge => patchEdgeFree_of_bodies hI hW hq hΛ₀ hΛ₀' hΛ128 hΛ hg₀
    hchart hmol hD hKs hqJ hζ hC2 hG4 hp hedge N hN j hyc hNR hNpre hNpost hgain hCN hCM hNpre'
    hgain' Mout hMb hmax hMo n hnn hn' εB q2 qm hq2 hqm hQ2 hQm hprice Mc hsm
    (fun ξ => hmodel ξ Mb le_rfl) (hG2e hedge hEO)⟩

/-- **Every patch of a family from the bodies, with the edge-free clause** (the premises
recentred at each patch). -/
theorem patches_of_bodies (hI : MassInterpolationStatement.{u, v})
    (hW : WeightedPullbackStatement.{v}) {s : ℝ} (hq : IsAdmissibleQ α s q)
    {Λ₀ Λ₀' : ℕ} (hΛ₀ : Λ₀ ≤ Λ) (hΛ₀' : Λ₀' ≤ Λ) (hΛ128 : 128 ≤ Λ) (hΛ : 1 ≤ Λ)
    (hg₀ : g₀ ≤ 1 / 32) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (hD : 2 ≤ D) (hKs : Ks + 1 ≤ Jm) (hqJ : Ks + 1 + Kmax ≤ qJ) (hζ : IsFastProfile ζ)
    {Cw : ℕ → ℝ} {Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem : ℝ} {Npre Npost Lpre Lpost : ℕ}
    (hC2 : TwoBlockJointBody.{u, v, w, x} α q hζ Cw Λ₀ D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem Npre Npost Lpre Lpost)
    {g₁ Θlong : ℝ} {Jpre Jpost Mb Q Ns n' : ℕ} {CL CM CN c : ℝ}
    (hG2 : SeamAllocationBody.{u, v, w, x} α q Λ hζ g₁ Θlong D H Kmax Ks Jpre Jpost Mb n' Q Ns Ls
      Jm qJ Jchart hchart Ca ((1 + max (Cchart 0) 0 / 2) / 8) Cpad Cage Cm CG Cchart CL Cth CM CN
      c)
    {Cw' : ℕ → ℝ} {Cenergy1' Cprep' CTm : ℝ}
    (hG4 : TwoBlockMomentBody.{u, v, w, x} α q hζ Cw' Λ₀' D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1' Cprep' CTm n' Npre)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (hNpre : Npost + (Ks + 1) + (Jpre + H) * (Ks + 1) ≤ Npre)
    (hNpost : (Ks + 1) + (Jpost + H) * (Ks + 1) ≤ Npost)
    (hgain : ENNReal.ofReal (CT * g * (Real.sqrt (B * ocTauPP α q Λ m) /
      ocEpsilon q Λ (m - 1))) ≤ 1)
    (hg₀₁ : g₀ ≤ g₁) (hCth : 0 ≤ Cth * Θ) (hg₁ : g + ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ g₁)
    (hlong : Θlong ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2)
    (hbudget : seamWindowBudget α q Λ m ν B Q c ≤ 1) (hCN : 0 ≤ CN) (hCM : 0 ≤ CM)
    (hNpre' : (Ks + 1) + H * (Ks + 1) ≤ Npre)
    (hgain' : ENNReal.ofReal (CTm * g * (Real.sqrt (B * ocTauPP α q Λ m) /
      ocEpsilon q Λ (m - 1))) ≤ 1)
    (Mout : ℕ) (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb) (hMo : Mout ≤ Mb)
    (n : ℕ) (hnn : n ≤ n') (hn' : 0 < n') (εB q2 qm : ℝ) (hq2 : 0 ≤ q2) (hqm : 0 ≤ qm)
    (hQ2 : 2 * (twoCactual hp Cw Cenergy2 * ENNReal.ofReal (cellTransitionMomentBudget Kmax 0) *
        twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre +
        twoEpsPost hp Cw Cprep CR Cterminal Crem Npost Lpost Jpost *
          (2 * (twoCfirst hp Cw Cenergy1 Npre +
            twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre))) ≤ ENNReal.ofReal q2)
    (hQm : twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0 * Θ) n' *
        twoCfirst hp Cw' Cenergy1' Npre ≤ ENNReal.ofReal qm)
    (hprice : patchErrorPrice0 Cchart (ocEpsilon q Λ (m - 1)) Kmax
        (compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) ^ 2 * q2 *
          datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre)
        (CN * seamWindowPrice α q Λ m ν B Q Ns c)
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ (1 - (n : ℝ) / n') *
      patchErrorPrice1 Cchart (ocEpsilon q Λ (m - 1)) Kmax Mb n'
        (qm * datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre) CM
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ ((n : ℝ) / n') ≤
      εB ^ 2)
    (N : ℕ) (hN : 0 < N) (hNR : 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m))
    (j : Fin 2 → Fin N) :
    PatchSmoothModel hζ Mout Mb D
      (Real.sqrt (patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM)) 1 εB n π K ν tS
      (twoTp α q Λ m l₀) r ρold (Real.sqrt (B * ocTauPP α q Λ m)) N hN j
      (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) (streamVel (Φ m))
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (fun _ => 0))
      (∀ v u, IsEmpty (F.Γ v u)) :=
  patchSmoothModel_of_bodies hI hW hq hΛ₀ hΛ₀' hΛ128 hΛ hg₀ hchart hmol hD hKs hqJ hζ hC2 hG2 hG4
    (hp.recenter hΛ (streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)) N hN j rfl hNR hNpre hNpost hgain hg₀₁
    hCth hg₁ hlong hbudget hCN hCM hNpre' hgain' Mout hMb hmax hMo n hnn hn' εB q2 qm hq2 hqm hQ2 hQm
    hprice

end Agree

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The one-patch statement for one family at a high level**.

From the bodies of the two-block theorem, the seam and the moments, the scale ledger at the level (`R ≤ Cl E^{1+ocC}`,
`A τ'' ≤ Cl E^{2δ}`, `ℓ²/τ ≤ Cl E^{4δ}`, the seam price `≤ Cs E^{a_s}`) and the smallness of `E`
at the level (the gains, the strain, the pulse length, the seam budget), every patch of the family
has its smooth model (slot `K`, and for a family without edges the agreeing slot-`0` model of the
edge-free clause), with the level-independent model constant
`C² = patchModelConstant … 8 Mb CM` and accuracy `CP E^{Pacc}`.

An empty family is handled by the caller, so `0 ≤ Cth Θ` is then not needed. For the moment
orders `n = 4`, `n' = 8` the interpolation exponent is `1/2`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev Set
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
  AVRegularity.CycleReference
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

theorem ratio_le_of_rpow {R E Cl c : ℝ} (hE : 0 < E) (h : R ≤ Cl * E ^ (1 + c)) :
    R / E ≤ Cl * E ^ c := by
  rw [div_le_iff₀ hE]
  rw [Real.rpow_add hE, Real.rpow_one] at h
  linarith

theorem gain_le_one {CT g x Cl E c : ℝ} (hCT : 0 ≤ CT) (hg1 : g ≤ 1)
    (hx0 : 0 ≤ x) (hx : x ≤ Cl * E ^ c) (hs : CT * Cl * E ^ c ≤ 1) :
    ENNReal.ofReal (CT * g * x) ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : CT * g * x ≤ CT * x := by
    have := mul_nonneg hCT hx0
    nlinarith
  have h2 : CT * x ≤ CT * (Cl * E ^ c) := mul_le_mul_of_nonneg_left hx hCT
  linarith

theorem long_le_of_small {Θlong τ ℓ2 Cl E d : ℝ} (hτ : 0 < τ) (hℓ : 0 < ℓ2)
    (hell : ℓ2 / τ ≤ Cl * E ^ d) (hs : Θlong * (Cl * E ^ d) ≤ 1) : Θlong ≤ τ / ℓ2 := by
  have hq : 0 < ℓ2 / τ := div_pos hℓ hτ
  by_cases hΘ : Θlong ≤ 0
  · exact hΘ.trans (div_pos hτ hℓ).le
  · push Not at hΘ
    have h1 : Θlong * (ℓ2 / τ) ≤ 1 := (mul_le_mul_of_nonneg_left hell hΘ.le).trans hs
    rw [le_div_iff₀ hℓ]
    have h2 : Θlong * (ℓ2 / τ) * τ ≤ 1 * τ := mul_le_mul_of_nonneg_right h1 hτ.le
    rwa [mul_assoc, div_mul_cancel₀ _ hτ.ne', one_mul] at h2

theorem strain_le {g g₀ g₁ At Cl E d : ℝ} (hg : g ≤ g₀) (hg₀ : g₀ ≤ g₁ / 2)
    (hAt : At ≤ Cl * E ^ d) (hs : Cl * E ^ d ≤ g₁ / 2) : g + At ≤ g₁ := by
  linarith

section Family

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

/-- **The one-patch statement for one family at a high level.** -/
theorem family_of_parts (hI : MassInterpolationStatement.{u, v})
    (hW : WeightedPullbackStatement.{v}) {s : ℝ} (hq : IsAdmissibleQ α s q)
    {Λ₀ Λ₀' : ℕ} (hΛ₀ : Λ₀ ≤ Λ) (hΛ₀' : Λ₀' ≤ Λ) (hΛ128 : 128 ≤ Λ) (hΛ : 1 ≤ Λ)
    (hg₀ : g₀ ≤ 1 / 32) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (hD : 2 ≤ D) (hKs : Ks + 1 ≤ Jm) (hqJ : Ks + 1 + Kmax ≤ qJ) (hζ : IsFastProfile ζ)
    {Cw : ℕ → ℝ} {Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem : ℝ} {Npre Npost Lpre Lpost : ℕ}
    (hC2 : TwoBlockJointBody.{u, v, w, x} α q hζ Cw Λ₀ D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem Npre Npost Lpre Lpost)
    {g₁ Θlong : ℝ} {Mb Q Ns : ℕ} {CL CM CN c : ℝ}
    (hG2 : SeamAllocationBody.{u, v, w, x} α q Λ hζ g₁ Θlong D H Kmax Ks Ks Ks Mb 8 Q Ns Ls
      Jm qJ Jchart hchart Ca ((1 + max (Cchart 0) 0 / 2) / 8) Cpad Cage Cm CG Cchart CL Cth CM CN
      c)
    {Cw' : ℕ → ℝ} {Cenergy1' Cprep' CTm : ℝ}
    (hG4 : TwoBlockMomentBody.{u, v, w, x} α q hζ Cw' Λ₀' D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1' Cprep' CTm 8 Npre)
    (hCe1 : 0 ≤ Cenergy1) (hCe2 : 0 ≤ Cenergy2) (hCprep : 0 ≤ Cprep) (hCT : 0 ≤ CT)
    (hCR : 0 ≤ CR) (hCterm : 0 ≤ Cterminal) (hCrem : 0 ≤ Crem) (hCN : 0 ≤ CN) (hCM : 0 ≤ CM)
    (hCTm : 0 ≤ CTm) (hCprep' : 0 ≤ Cprep') (hCe1' : 0 ≤ Cenergy1')
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (hNpre : Npost + (Ks + 1) + (Ks + H) * (Ks + 1) ≤ Npre)
    (hNpost : (Ks + 1) + (Ks + H) * (Ks + 1) ≤ Npost)
    (hNpre' : (Ks + 1) + H * (Ks + 1) ≤ Npre)
    (hg₀₁ : g₀ ≤ g₁ / 2) (hg₁0 : 0 < g₁) (hCth : 0 ≤ Cth * Θ)
    (Cl Cs as : ℝ)
    (hE1 : ocEpsilon q Λ (m - 1) ≤ 1)
    (hR : Real.sqrt (B * ocTauPP α q Λ m) ≤ Cl * ocEpsilon q Λ (m - 1) ^ (1 + ocC α q))
    (hAt : ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ Cl * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q))
    (hell : ocEll q Λ m ν ^ 2 / ocTau α q Λ m ≤ Cl * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q))
    (hsp : seamWindowPrice α q Λ m ν B Q Ns c ≤ Cs * ocEpsilon q Λ (m - 1) ^ as)
    (hk : ocC α q * ((2 * (Ks + 1) : ℕ) : ℝ) ≤ 2 * as)
    (s1 : CT * Cl * ocEpsilon q Λ (m - 1) ^ ocC α q ≤ 1)
    (s1' : CTm * Cl * ocEpsilon q Λ (m - 1) ^ ocC α q ≤ 1)
    (s2 : Cl * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) ≤ g₁ / 2)
    (s3 : Θlong * (Cl * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)) ≤ 1)
    (s4 : Cs * ocEpsilon q Λ (m - 1) ^ as ≤ 1)
    (hcC : 0 ≤ ocC α q) (hqδ : 0 ≤ q * ocDelta α q)
    (Pacc : ℝ) (hP : 2 * Pacc ≤ (1 - (4 : ℝ) / 8) *
      (ocC α q * ((2 * (Ks + 1) : ℕ) : ℝ) - 2 * (q * ocDelta α q) * Kmax) -
        (4 : ℝ) / 8 * (2 * (q * ocDelta α q) * Kmax))
    (CP : ℝ)
    (hCP : (2 * (compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) ^ 2 *
          (c2RemainingConstant.{u, v} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR Cterminal Crem
            (max Cth 0) Cl Npre Npost Lpre Lpost Ks Ks).toReal *
          datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre +
          returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax 0 * (CN * Cs) ^ 2) *
          max 1 Crat ^ (2 * Kmax)) ^ (1 - (4 : ℝ) / 8) *
        (2 * (returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax 8 *
          ((twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0) 8 *
            energyConstant.{u, v} Cw' Kmax D H CG Cenergy1' (max Cth 0) Npre).toReal *
            datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre) +
          patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) 8 Mb CM) *
          max 1 Crat ^ (2 * Kmax)) ^ ((4 : ℝ) / 8) ≤ CP ^ 2)
    (Mout : ℕ) (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb) (hMo : Mout ≤ Mb)
    (N : ℕ) (hN : 0 < N) (hNR : 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m))
    (j : Fin 2 → Fin N) :
    PatchSmoothModel hζ Mout Mb D
      (Real.sqrt (patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) 8 Mb CM)) 1
      (CP * ocEpsilon q Λ (m - 1) ^ Pacc) 4 π K ν tS
      (twoTp α q Λ m l₀) r ρold (Real.sqrt (B * ocTauPP α q Λ m)) N hN j
      (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) (streamVel (Φ m))
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (fun _ => 0))
      (∀ v u, IsEmpty (F.Γ v u)) := by
  have hE := Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ
  have hν := hp.cov.pos.1
  have hg1 : g ≤ 1 := by linarith [hp.cov.g_range.2]
  have hRE := ratio_le_of_rpow hE hR
  have hRE0 : 0 ≤ Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1) :=
    div_nonneg (Real.sqrt_nonneg _) hE.le
  have hgain := gain_le_one hCT hg1 hRE0 hRE s1
  have hgain' := gain_le_one hCTm hg1 hRE0 hRE s1'
  have hg₀g₁ : g₀ ≤ g₁ := by linarith
  have hg₁ := strain_le hp.cov.g_range.2 hg₀₁ hAt s2
  have hlong := long_le_of_small (Construction.Stream.ocTau_pos hΛ) (ocEll_sq_pos_of hΛ hν) hell s3
  have hbudget := (seamWindowBudget_le_price (B := B) hΛ Q Ns c).trans (hsp.trans s4)
  -- the price of the two-block theorem
  have hK2 := c2RemainingConstant_ne_top.{u, v} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR
    Cterminal Crem (max Cth 0) Cl Npre Npost Lpre Lpost Ks Ks
  have hEk0 : 0 ≤ ocEpsilon q Λ (m - 1) ^ (ocC α q * ((2 * (Ks + 1) : ℕ) : ℝ)) :=
    (Real.rpow_pos_of_pos hE _).le
  have heq : c2RemainingConstant.{u, v} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR Cterminal
      Crem (max Cth 0) Cl Npre Npost Lpre Lpost Ks Ks *
        ENNReal.ofReal (ocEpsilon q Λ (m - 1) ^ (ocC α q * ((2 * (Ks + 1) : ℕ) : ℝ))) =
      ENNReal.ofReal ((c2RemainingConstant.{u, v} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR
        Cterminal Crem (max Cth 0) Cl Npre Npost Lpre Lpost Ks Ks).toReal *
        ocEpsilon q Λ (m - 1) ^ (ocC α q * ((2 * (Ks + 1) : ℕ) : ℝ))) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK2]
  have hQ2 := (c2_remaining_le hp hΛ hg1 Cw hCe1 hCe2 hCprep hCR hCterm hCrem Npre Npost Lpre
    Lpost Ks Ks le_rfl le_rfl hcC hE1 hRE).trans heq.le
  -- the moment price
  have hKm := ENNReal.mul_ne_top (twoMomentPrice_ne_top.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0) 8)
    (energyConstant_ne_top.{u, v} Cw' Kmax D H CG Cenergy1' (max Cth 0) Npre)
  have hQm := (mul_le_mul' (twoMomentPrice_le hp Cw' hCprep' 8)
    (twoCfirst_le hp Cw' hCe1' Npre)).trans (le_of_eq (ENNReal.ofReal_toReal hKm).symm)
  -- the interpolated price
  have hθ : ((4 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = (4 : ℝ) / 8 := by norm_num
  have hpb := b1_price_bound (E := ocEpsilon q Λ (m - 1))
    (q2 := (c2RemainingConstant.{u, v} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR Cterminal Crem
      (max Cth 0) Cl Npre Npost Lpre Lpost Ks Ks).toReal *
      ocEpsilon q Λ (m - 1) ^ (ocC α q * ((2 * (Ks + 1) : ℕ) : ℝ)))
    (K2 := (c2RemainingConstant.{u, v} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR Cterminal Crem
      (max Cth 0) Cl Npre Npost Lpre Lpost Ks Ks).toReal)
    (k := ocC α q * ((2 * (Ks + 1) : ℕ) : ℝ))
    (CNp := CN * seamWindowPrice α q Λ m ν B Q Ns c) (CN := CN) (Cs := Cs) (as := as)
    (cb := compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1))
    (dP := datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre)
    (rc0 := returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax 0)
    (rc1 := returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax 8)
    (qm := (twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0) 8 *
      energyConstant.{u, v} Cw' Kmax D H CG Cenergy1' (max Cth 0) Npre).toReal)
    (Cmod := patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) 8 Mb CM)
    (qδ := q * ocDelta α q) (θ := (4 : ℝ) / 8)
    (Crat := Crat) (P := Pacc) Kmax hE hE1
    (mul_nonneg ENNReal.toReal_nonneg hEk0) ENNReal.toReal_nonneg le_rfl
    (mul_nonneg hCN (seamWindowPrice_nonneg hΛ (div_nonneg
      (Construction.Stream.ocTauPP_pos hΛ).le (sq_nonneg _))))
    (mul_le_mul_of_nonneg_left hsp hCN) hk
    (datumEnergyPrice_nonneg Cchart _ Jchart Npre) (returnConstant_nonneg Cchart _ Kmax 0)
    (returnConstant_nonneg Cchart _ Kmax 8) ENNReal.toReal_nonneg (by
      unfold patchModelConstant
      rw [preparationPieceFlowJetBudget_one]
      have := le_max_right (Cchart 0) 0
      positivity) hqδ (by norm_num) (by norm_num) hP
  have hprice : patchErrorPrice0 Cchart (ocEpsilon q Λ (m - 1)) Kmax
        (compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) ^ 2 *
          ((c2RemainingConstant.{u, v} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR Cterminal Crem
            (max Cth 0) Cl Npre Npost Lpre Lpost Ks Ks).toReal *
            ocEpsilon q Λ (m - 1) ^ (ocC α q * ((2 * (Ks + 1) : ℕ) : ℝ))) *
          datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre)
        (CN * seamWindowPrice α q Λ m ν B Q Ns c)
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^
          (1 - ((4 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) *
      patchErrorPrice1 Cchart (ocEpsilon q Λ (m - 1)) Kmax Mb 8
        ((twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0) 8 *
          energyConstant.{u, v} Cw' Kmax D H CG Cenergy1' (max Cth 0) Npre).toReal *
          datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre) CM
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^
          (((4 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) ≤
      (CP * ocEpsilon q Λ (m - 1) ^ Pacc) ^ 2 := by
    have hsq : (CP * ocEpsilon q Λ (m - 1) ^ Pacc) ^ 2 =
        CP ^ 2 * ocEpsilon q Λ (m - 1) ^ (2 * Pacc) := by
      rw [mul_pow, ← Real.rpow_natCast (ocEpsilon q Λ (m - 1) ^ Pacc) 2, ← Real.rpow_mul hE.le,
        show Pacc * ((2 : ℕ) : ℝ) = 2 * Pacc by push_cast; ring]
    rw [hθ, hsq]
    unfold patchErrorPrice0 patchErrorPrice1
    exact hpb.trans (mul_le_mul_of_nonneg_right hCP (Real.rpow_pos_of_pos hE _).le)
  exact patches_of_bodies hI hW hq hΛ₀ hΛ₀' hΛ128 hΛ hg₀ hchart hmol hD hKs hqJ hζ hC2 hG2 hG4 hp
    hNpre hNpost hgain hg₀g₁ hCth hg₁ hlong hbudget hCN hCM hNpre' hgain' Mout hMb hmax hMo 4
    (by norm_num) (by norm_num) _ _ _ (mul_nonneg ENNReal.toReal_nonneg hEk0)
    ENNReal.toReal_nonneg hQ2 hQm hprice N hN hNR j

end Family

end AVRegularity.CycleJointProofs.Assembly
end
end
