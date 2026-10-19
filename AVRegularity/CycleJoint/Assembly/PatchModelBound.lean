-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.PriceLedgerSeam
import AVRegularity.CycleJoint.Assembly.WordGeometryOfRetained
public import AVRegularity.CycleJoint.Assembly.BlockEdgeSlowSample
import AVRegularity.CycleJoint.ActualPreparationHomogeneousFamilyNativeTraceLinearMap
import AVRegularity.CycleJoint.ActualPreparationHomogeneousPlaneExistence
import AVRegularity.CycleJoint.PlaneMetricSourceAllMomentMapConstruction
public import AVRegularity.CycleWords.MixedWords.B1WSourceL2
public import AVRegularity.CycleJoint.Assembly.BlockTransportedRemainderTime
import AVRegularity.CycleComparison.Charts.ChartDeviation
import AVRegularity.CycleJoint.PreparationReferenceCellInitialHomogeneousResponsePair
import AVRegularity.CycleWords.Assembly.SeamNorms

section
/-! **The seam on one allocation**.

`seamPair_apply`: the body of `cycle_seam` for the shape of an allocation `(wo, wf)`, applied to
the two blocks: the future block `[b, b + S]` (`b` the cell time of the seam, `S = τ''/ℓ²`) with
the package `pkgF` and the future word's letters, the old piece `[a, b]` (`a` the cell time of
`tS`) inside the old block `[b - S, b]` with the package `pkgO`, the transition `Υ` of the block transition, and the
word chains of the two-block theorem, moved to the clamped metrics and, for the future chain, to the window
`[b, b + S]`. The letter hypotheses are bundled per letter (`SeamLetterOK`) and hold for every
letter of a word once they hold for the metric and the source letter.

The seam's kernel `Kp` is obtained from the future block alone, before the slot assignment
`K'`, the cell datum `V₀`, the transition on the slot-`K'` endpoints and the chains; so one kernel
serves the slots `K` and, for a family without edges, the slot `0` (the edge-free clause). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- The seam's hypotheses on one letter: a cycle letter on `dom` with reserve `R` and depth `H`,
transverse on the regions of `reg`, quiet on `reg.quiet ∩ Qt`, measurable in time, and with
constant slots `K` descending along its edges. -/
def SeamLetterOK {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (π : ι → ℝ) (K : ι → ℕ) (L : CycleLetter ι h D)
    (dom : Set (ℝ × Vec 2)) (R H : ℕ) (reg : BlockRegions) (vd : ℝ → Vec 2 → Vec 2)
    (Qt : Set ℝ) : Prop :=
  IsCycleLetter π L dom R H ∧
    IsTransverseOnPulses L.edge (fun p : Fin reg.P => Set.Icc (reg.lo p) (reg.hi p))
      reg.orient ∧
    IsQuietOn L.edge vd (reg.quiet ∩ Qt) ∧
    (∀ x y o, ∀ γ ∈ L.edge x y o, ∀ β X z, Measurable fun t => γ.coeff β t X z) ∧
    ∀ x y (o : Finset.Icc 2 D), L.edge x y o ≠ [] → K x + o.1 ≤ K y + 2

/-- The seam's input from an old endpoint `U`: the cutoff at frequency `√η` composed with `Υ`. -/
def seamInput {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {K : ι → ℕ} (χm : Vec 2 → ℝ) (η : ℝ) (Υ : Vec 2 → Vec 2)
    (U : ∀ x, PlaneHk Set.univ (K x) (h x)) : ∀ x, Vec 2 → h x :=
  fun x z => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (planeValue (U x)) (Υ z)

/-- A plane chain on `[t₀, t₁]` is a chain on any equal window. -/
theorem isPlaneChain_times {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D N : ℕ} {cd : PlaneChainData ι h D N}
    {κ : Fin (N + 1) → ι → ℕ} {t₀ t₁ t₀' t₁' : ℝ} {vd : ℝ → Vec 2 → Vec 2}
    {f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)}
    {F : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x))}
    {uc : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x)}
    {wc : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)}
    (h₀ : t₀ = t₀') (h₁ : t₁ = t₁') (hc : IsPlaneChain cd κ t₀ t₁ vd f F uc wc) :
    IsPlaneChain cd κ t₀' t₁' vd f F uc wc := by
  subst h₀ h₁
  exact hc

section Pair

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

/-- **The seam on one allocation `(wo, wf)` of the two blocks.** -/
theorem seamPair_apply (hcongr : PlaneChainMetricCongrStatement.{u, v})
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) {Kc : ScalarConstants} {g₁ : ℝ} {pout Q Mb Ns qΥ : ℕ}
    {Cs CU c : ℝ} {χm : Vec 2 → ℝ} {CM CN : ℕ → ℝ} (wo wf : List Bool)
    (hbody : SeamPairBody.{u, v} Kc g₁ D H Kmax pout (seamOrderK D Kmax wo) wo.length wf.length
      (wordOrders D wo) (wordSlow Ks wo) (wordPositive wo) (wordOrders D wf) (wordSlow Ks wf)
      (wordPositive wf) Q Mb Ns qΥ 1 1 Cs CU 1 χm c CM CN)
    (hNs : 1 ≤ Ns) (hν : 0 < ν) (hB : 0 < B) (hνB : ν ≤ B)
    (hS : 1 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (hRE : Real.sqrt (B * ocTauPP α q Λ m) ≤ ocEpsilon q Λ (m - 1)) (hr : 0 < r)
    (hrε : r ≤ ocEpsilon q Λ m)
    (GO GF : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hGmO : IsCellMetric (fun t _ => GO t)) (hGnO : IsMetricNearIdentity (fun t _ => GO t) g)
    (hGO : ∀ t ∈ Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)),
      GO t = twoGpre hp t 0)
    (hGmF : IsCellMetric (fun t _ => GF t)) (hGnF : IsMetricNearIdentity (fun t _ => GF t) g)
    (hGF : ∀ t ∈ Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoTp α q Λ m l₀)), GF t = twoGpost hp t 0)
    (hg0 : 0 ≤ g) (hgK : g ≤ Kc.g0) (hg₁ : g ≤ g₁)
    (hdO : IsCellDrift (ocCellDrift α q Λ ζ m ν (twoYc hp)) ∧
      (∀ t (k : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν (twoYc hp) t x k : ℂ)) = 0) ∧
      (∀ t, ContDiff ℝ (⊤ : ℕ∞) (ocCellDrift α q Λ ζ m ν (twoYc hp) t)) ∧
      (∀ t x, Real.sqrt (ν / B) *
        Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν (twoYc hp) t x i ^ 2) ≤ Kc.Cw) ∧
      (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j
        (fun z' => Real.sqrt (ν / B) • ocCellDrift α q Λ ζ m ν (twoYc hp) t z') z‖ ≤ Kc.Cvj j))
    (hdF : IsCellDrift (ocCellDrift α q Λ ζ m ν (twoYcPost hp)) ∧
      (∀ t (k : Fin 2),
        cellMean (fun x => (ocCellDrift α q Λ ζ m ν (twoYcPost hp) t x k : ℂ)) = 0) ∧
      (∀ t, ContDiff ℝ (⊤ : ℕ∞) (ocCellDrift α q Λ ζ m ν (twoYcPost hp) t)) ∧
      (∀ t x, Real.sqrt (ν / B) *
        Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν (twoYcPost hp) t x i ^ 2) ≤ Kc.Cw) ∧
      (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j
        (fun z' => Real.sqrt (ν / B) • ocCellDrift α q Λ ζ m ν (twoYcPost hp) t z') z‖ ≤
          Kc.Cvj j))
    (regO regF : BlockRegions)
    (pkgO : ScalarPackage Kc (ν / B) GO (ocCellDrift α q Λ ζ m ν (twoYc hp))
      ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
      (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) regO)
    (pkgF : ScalarPackage Kc (ν / B) GF (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
      (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) regF)
    (hseam : Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀) - regF.buffer)
        (cellTime q Λ m ν (twoSeam α q Λ m l₀)) ⊆
      regO.quiet ∩ Set.Icc ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
        ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
          ocTauPP α q Λ m / ocEll q Λ m ν ^ 2))
    (hquietMargin : Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoSeam α q Λ m l₀) +
        (ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2) ⊆ regF.quiet)
    (hC0 : peFactor (ν / B) ^ Q * (1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ Q *
      (1 + regF.joins) * Real.exp (-c * regF.buffer) ≤ 1)
    (hC0O : peFactor (ν / B) ^ Q * (1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ Q *
      (1 + regO.joins) * Real.exp (-c * regO.buffer) ≤ 1)
    (Υ Υinv : Vec 2 → Vec 2)
    (hΥ : IsCenteredTransition Υ Υinv (g + ocA α q Λ (m - 1) * ocTauPP α q Λ m)
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) CU qΥ)
    (hΥs : ContDiff ℝ (⊤ : ℕ∞) Υinv)
    (hgU : 0 ≤ g + ocA α q Λ (m - 1) * ocTauPP α q Λ m ∧
      g + ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ Kc.g0)
    (MO SO MF SF : CycleLetter ι h D)
    (hMOs : MO.order = 2 ∧ MO.slow = Ks ∧ MO.positive = true)
    (hSOs : SO.order = D ∧ SO.slow = Ks ∧ SO.positive = false)
    (hMFs : MF.order = 2 ∧ MF.slow = Ks ∧ MF.positive = true)
    (hSFs : SF.order = D ∧ SF.slow = Ks ∧ SF.positive = false)
    (hMO : SeamLetterOK π K MO
      (Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) ×ˢ Set.univ)
      (seamReserve D Kmax pout Ks wo wf) H regO (ocCellDrift α q Λ ζ m ν (twoYc hp))
      (Set.Icc ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
        ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
          ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)))
    (hSO : SeamLetterOK π K SO
      (Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) ×ˢ Set.univ)
      (seamReserve D Kmax pout Ks wo wf) H regO (ocCellDrift α q Λ ζ m ν (twoYc hp))
      (Set.Icc ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
        ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
          ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)))
    (hMF : SeamLetterOK π K MF
      (Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoSeam α q Λ m l₀) + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ×ˢ
        Set.univ)
      (seamReserve D Kmax pout Ks wo wf) H regF (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
      (Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoSeam α q Λ m l₀) + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)))
    (hSF : SeamLetterOK π K SF
      (Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoSeam α q Λ m l₀) + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ×ˢ
        Set.univ)
      (seamReserve D Kmax pout Ks wo wf) H regF (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
      (Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoSeam α q Λ m l₀) + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2))) :
    ∃ Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x),
    ∀ (K' : ι → ℕ) (_hK' : ∀ x, K' x ≤ Kmax)
      (_hdMO : ∀ x y (o : Finset.Icc 2 D), MO.edge x y o ≠ [] → K' x + o.1 ≤ K' y + 2)
      (_hdSO : ∀ x y (o : Finset.Icc 2 D), SO.edge x y o ≠ [] → K' x + o.1 ≤ K' y + 2)
      (_hdMF : ∀ x y (o : Finset.Icc 2 D), MF.edge x y o ≠ [] → K' x + o.1 ≤ K' y + 2)
      (_hdSF : ∀ x y (o : Finset.Icc 2 D), SF.edge x y o ≠ [] → K' x + o.1 ≤ K' y + 2)
      (V₀ : (∀ i, TorusHk (K' i) (h i)) → ∀ i, PlaneHk Set.univ (K' i) (h i))
      (_hsupp : ∀ (ξ : ∀ i, TorusHk (K' i) (h i)) i, ∀ᵐ z : Vec 2 ∂volume,
        (Cs * (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ m)) ^ 2 < z 0 ^ 2 + z 1 ^ 2 →
        planeValue (V₀ ξ i) z = 0)
      (transit : ∀ x, PlaneHk Set.univ (K' x) (h x) →L[ℝ] PlaneHk Set.univ (K' x) (h x))
      (_hΥt : ∀ (U : ∀ x, PlaneHk Set.univ (K' x) (h x)) x,
        planeValue (transit x (U x)) =ᵐ[volume] fun z => planeValue (U x) (Υ z))
      (uO : (∀ i, TorusHk (K' i) (h i)) → ∀ (_ : Fin (wo.length + 1)) (x : ι),
        ℝ → PlaneHk Set.univ (K' x) (h x))
      (wO : (∀ i, TorusHk (K' i) (h i)) → ∀ (_ : Fin (wo.length + 1)) (x : ι),
        ℝ → PlaneHk Set.univ (K' x + 1) (h x))
      (uF : (∀ i, TorusHk (K' i) (h i)) → ∀ (_ : Fin (wf.length + 1)) (x : ι),
        ℝ → PlaneHk Set.univ (K' x) (h x))
      (wF : (∀ i, TorusHk (K' i) (h i)) → ∀ (_ : Fin (wf.length + 1)) (x : ι),
        ℝ → PlaneHk Set.univ (K' x + 1) (h x))
      (_hchO : ∀ ξ, IsPlaneChain (wordChainData (fun t => twoGpre hp t 0)
        (blockWordLetters MO SO wo) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp)
        (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
        (fun _ x => K' x) (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (ocCellDrift α q Λ ζ m ν (twoYc hp)) (V₀ ξ) (fun _ _ _ => 0) (uO ξ) (wO ξ))
      (_hchF : ∀ ξ, IsPlaneChain (wordChainData (fun t => twoGpost hp t 0)
        (blockWordLetters MF SF wf) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYcPost hp)
        (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
        (fun _ x => K' x) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoTp α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
        (fun x => transit x (uO ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀))))
        (fun _ _ _ => 0) (uF ξ) (wF ξ)) (ξ : ∀ i, TorusHk (K' i) (h i)),
      (∀ x (M : ℕ), ContDiff ℝ M (Kp (seamInput χm (ν / B) Υ
        (fun x => uO ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀)))) x)) ∧
      (∀ M ≤ Mb,
        weightedJetNorm π (pout : ℝ) M (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
            (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
            (fun x _ wd z => orderedDerivative wd (Kp (seamInput χm (ν / B) Υ
              (fun x => uO ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀)))) x) z) ≤
          ENNReal.ofReal (CM M * (wordTheta (seamEtaG α q Λ m B) (blockWordLetters MO SO wo) *
            wordTheta (seamEtaG α q Λ m B) (blockWordLetters MF SF wf))) *
            momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
              (fun x => planeValue (V₀ ξ x))) ∧
      weightedJetNorm π (pout : ℝ) Kmax (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
          (r / ocEpsilon q Λ m)
          (fun x a' wd z => if a' ≤ K' x then
            planeJetOrder (uF ξ (Fin.last _) x (cellTime q Λ m ν (twoTp α q Λ m l₀))) a' wd z -
              orderedDerivative wd (Kp (seamInput χm (ν / B) Υ
                (fun x => uO ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀)))) x) z
            else 0) ≤
        ENNReal.ofReal (CN Ns * (wordTheta (seamEtaG α q Λ m B) (blockWordLetters MO SO wo) *
            wordTheta (seamEtaG α q Λ m B) (blockWordLetters MF SF wf)) *
            peFactor (ν / B) ^ Q * (1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ Q *
            (Real.exp (-c * (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)) +
              (1 + regF.joins) * Real.exp (-c * regF.buffer) +
              Real.exp (-c * ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2)) +
              (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ (-(Ns : ℝ) / 2))) *
          momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
            (fun x => planeValue (V₀ ξ x)) := by
  have hε := Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hl := ocEll_sq_pos_of (q := q) (m := m) hΛ hν
  have hwin := hp.windows hΛ
  have hd := cellTime_twoTp (α := α) (q := q) (m := m) hΛ hν l₀
  have hb := cellTime_twoSeam (α := α) (q := q) (m := m) hΛ hν l₀
  obtain ⟨hvF, hv0F, hvsF, hvwF, hvjF⟩ := hdF
  obtain ⟨hvO, hv0O, hvsO, hvwO, hvjO⟩ := hdO
  have hLF := blockWordLetters_forall (fun L => SeamLetterOK π K L _ _ H regF _ _) hMF hSF wf
  have hLO := blockWordLetters_forall (fun L => SeamLetterOK π K L _ _ H regO _ _) hMO hSO wo
  obtain ⟨Kp, hKp⟩ := hbody π hp.hπ (blockWordLetters MF SF wf)
    (blockWordLetters_shape hMFs hSFs wf) (ν / B) (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (seamEtaG α q Λ m B) (r / ocEpsilon q Λ m) (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    (div_pos hν hB) ((div_le_one hB).2 hνB) hS (seamEtaG_pos hΛ hB) (seamEtaG_le_one hΛ hRE)
    (div_pos hr hε) ((div_le_one hε).2 hrε) (seamVarpi_eq hΛ hν hB).symm
    (cellTime q Λ m ν (twoSeam α q Λ m l₀)) GF (ocCellDrift α q Λ ζ m ν (twoYcPost hp)) g
    hGmF hvF hv0F hvsF hvwF hvjF hg0 hgK hg₁ hGnF regF pkgF
    (fun i => (hLF i).1) (fun i => (hLF i).2.1) (fun i => (hLF i).2.2.1)
    (fun i => (hLF i).2.2.2.1) ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2)
    (trimmedQuietMargin_nonneg hΛ hν) (trimmedQuietMargin_le_seamS hΛ hν) hquietMargin
    ((ocEpsilon q Λ (m - 1))⁻¹ • twoYcPost hp) hC0
  refine ⟨Kp, fun K' hK' hdMO hdSO hdMF hdSF V₀ hsupp transit hΥt uO wO uF wF hchO hchF ξ => ?_⟩
  have hwinO : (((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 ≤
        cellTime q Λ m ν tS ∧
      cellTime q Λ m ν tS ≤ cellTime q Λ m ν (twoSeam α q Λ m l₀) ∧
      cellTime q Λ m ν (twoSeam α q Λ m l₀) ≤
        (((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
          ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 := by
    refine ⟨?_, hwin.ab.le, ?_⟩
    · rw [cellTime_eq_div hΛ hν]
      exact div_le_div_of_nonneg_right hp.cov.window.1 hl.le
    · rw [hb, ← add_div]
      exact le_of_eq (by ring_nf)
  have hdur : cellTime q Λ m ν (twoSeam α q Λ m l₀) - cellTime q Λ m ν tS ≤
      1 * (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) := by
    rw [one_mul]
    exact hwin.lengthPre
  have hsupp' : ∀ x, ∀ᵐ z : Vec 2 ∂volume,
      (Cs / (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))) ^ 2 < z 0 ^ 2 + z 1 ^ 2 →
      planeValue (V₀ ξ x) z = 0 := by
    intro x
    rw [div_div_eq_mul_div, mul_div_assoc]
    exact hsupp ξ x
  have hchO' := hcongr (fun t => twoGpre hp t 0) GO (blockWordLetters MO SO wo)
    ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
    (fun _ x => K' x) _ _ _ _ _ _ _ (fun s hs => (hGO s hs).symm) (hchO ξ)
  have hchF' := isPlaneChain_times rfl hd (hcongr (fun t => twoGpost hp t 0) GF
    (blockWordLetters MF SF wf) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYcPost hp)
    (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) (fun _ x => K' x) _ _ _ _ _ _ _
    (fun s hs => (hGF s hs).symm) (hchF ξ))
  obtain ⟨h1, h2, h3⟩ := hKp (fun _ x => K' x) K' hK' (fun _ => le_rfl)
    (fun j x y o hne => blockWordLetters_forall
      (fun L => ∀ x y (o : Finset.Icc 2 D), L.edge x y o ≠ [] → K' x + o.1 ≤ K' y + 2)
      hdMF hdSF wf j x y o hne)
    (blockWordLetters MO SO wo) (blockWordLetters_shape hMOs hSOs wo)
    Υ Υinv (g + ocA α q Λ (m - 1) * ocTauPP α q Λ m) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
    (seam_delta_eq hΛ hB) hgU hΥ hΥs
    ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
    (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) (cellTime q Λ m ν tS)
    (cellTime q Λ m ν (twoSeam α q Λ m l₀)) GO (ocCellDrift α q Λ ζ m ν (twoYc hp)) g
    hGmO hvO hv0O hvsO hvwO hvjO hg0 hgK hg₁ hGnO regO pkgO.toCoreScalarPackage hwinO hdur hC0O hseam
    (fun i => (hLO i).1) (fun i => (hLO i).2.1) (fun i => (hLO i).2.2.1)
    (fun i => (hLO i).2.2.2.1) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp) (fun _ x => K' x)
    (fun j x y o hne => blockWordLetters_forall
      (fun L => ∀ x y (o : Finset.Icc 2 D), L.edge x y o ≠ [] → K' x + o.1 ≤ K' y + 2)
      hdMO hdSO wo j x y o hne) (fun _ => le_rfl)
    (V₀ ξ) hsupp' (uO ξ) (wO ξ) hchO'
    (fun x => transit x (uO ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀))))
    (fun x => hΥt (fun x => uO ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀))) x)
    (uF ξ) (wF ξ) hchF'
  refine ⟨h1, h2, ?_⟩
  rw [hd]
  exact h3 Ns hNs le_rfl

end Pair

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The block word geometry, the common finish**.

`retained_trace_clean`: the curve `u` of the retained endpoint clause is continuous and is the
truncation of `w` (from the error equation for `(uH - u, wH - w)` and the equation for `uH`).

`blockWordGeometry_finish`: from the outputs of the shared core on one block, with the source
insertion read through the block letters (the raw readout `blockLetterRawConstituent`), the word
chains of the block letters exist, are linear in the datum, have finite moments at every time, and
the actual solution minus the sum of their last values obeys the retained bound. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleJointProofs

namespace AVRegularity.CycleJointProofs.Assembly

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The retained curve of the endpoint clause is continuous and truncates its lift. The
hypotheses are the continuity and truncation clauses of the two weak solutions (the actual one and
the error), so that callers pass projections and no forcing term is re-elaborated. -/
theorem retained_trace_clean (K : ι → ℕ) (a b : ℝ)
    (uH : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (wH : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hHc : ∀ i, ContinuousOn (uH i) (Set.Icc a b))
    (hHt : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncatePlaneHk (Nat.le_succ (K i)) (wH i t) = uH i t)
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hec : ∀ i, ContinuousOn (fun t => uH i t - u i t) (Set.Icc a b))
    (het : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncatePlaneHk (Nat.le_succ (K i)) (wH i t - w i t) = uH i t - u i t) :
    (∀ i, ContinuousOn (u i) (Set.Icc a b)) ∧
    (∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncatePlaneHk (Nat.le_succ (K i)) (w i t) = u i t) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · refine ((hHc i).sub (hec i)).congr fun t _ => ?_
    change u i t = uH i t - (uH i t - u i t)
    rw [sub_sub_cancel]
  · filter_upwards [hHt i, het i] with t ht1 ht2
    have hsub : truncatePlaneHk (Nat.le_succ (K i)) (w i t) =
        truncatePlaneHk (Nat.le_succ (K i)) (wH i t) -
          truncatePlaneHk (Nat.le_succ (K i)) (wH i t - w i t) := by
      rw [map_sub, sub_sub_cancel]
    rw [hsub, ht1, ht2, sub_sub_cancel]

universe u v w x y

/-- **The block word geometry, the common finish.** -/
theorem blockWordGeometry_finish (hFM : MetricLetterFluxStatement.{u, v})
    (hFS : SourceLetterFluxStatement.{u, v, w, x})
    {α q : ℝ} {Λ m : ℕ} {ζfast : ℝ → ℝ} (hζ : IsFastProfile ζfast) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream (Φ (m - 1))) {ν Bcover ρ g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ}
    {CG : ℕ → ℝ} {tS tZ : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG
      l₀ P y₀)
    (hΛ : 1 ≤ Λ) (hgsmall : 4 * g ≤ 1 / 8) (hg0 : g0 ≤ 1 / 4)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D : ℕ} (hD : 2 ≤ D) {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (hK : ∀ v, K v ≤ Kmax) (hdesc : F.IsDescending K)
    (ic : Fin (P + 2)) (a b : ℝ) (hab : a < b)
    (hwindow : Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic)
    (hlength : b - a ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (Ks : ℕ) (l : ℤ) (σ : ℝ) (θM θS : ℝ) (bM bS : ι → ι → ℝ)
    {X : Type y} [AddCommGroup X] [Module ℝ X] (J H : ℕ) (π : ι → ℝ) (n : ℕ)
    (Bd : X → ENNReal) :
    ∀ (ϖ rs : ℝ) (yc : Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
      (vd : ℝ → Vec 2 → Vec 2) (X₀ : Vec 2) (δ ℓ2 : ℝ) (S₀ : Finset P')
      (_hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m))
      (_hrs : rs = ρ / ocEpsilon q Λ m)
      (_hyc : yc = windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic)
      (_hG : G = windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic)
      (_hvd : vd = ocCellDrift α q Λ ζfast m ν yc)
      (_hX₀ : X₀ = (ocEpsilon q Λ (m - 1))⁻¹ • yc)
      (_hδ : δ = ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
      (_hℓ2 : ℓ2 = ν⁻¹ * ocEpsilon q Λ m ^ 2)
      (_hS₀ : S₀ = (F.locally_finite tS tZ).toFinset)
      (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
      (_hf : ∀ ξ r i, weightedFactorialNormSq r ϖ 0 rs (K i) (V₀ ξ i) ≠ ⊤)
      (uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (wH : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
      (_hHc : ∀ ξ i, ContinuousOn (uH ξ i) (Set.Icc a b))
      (_hHt : ∀ ξ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
        truncatePlaneHk (Nat.le_succ (K i)) (wH ξ i t) = uH ξ i t)
      (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ rs 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
          PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ rs 0 (volume.restrict (Set.Icc a b)))
      (_hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) (fun t => G t 0) vd (K i) a b ϖ rs
        (R i))
      (positive : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ rs 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
          PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ rs 0
            (volume.restrict (Set.Icc a b)))
      (_hpos : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ rs 0 (volume.restrict (Set.Icc a b))
        (fun X t => planeMatrixGradientFlux (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (E := h i) (K i + 1) ϖ rs 0
            (volume.restrict (Set.Icc a b)) X t)) (positive i))
      (Ledge : ∀ i j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ rs 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
          PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ rs 0
            (volume.restrict (Set.Icc a b)))
      (_hLedge : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ rs 0 (volume.restrict (Set.Icc a b))
        (fun x t z => ∑ u, ∑ γ, blockLetterRawConstituent Ks F S₀ actual K ℓ2 hφ l σ
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc ϖ rs (volume.restrict (Set.Icc a b))
          i u γ (x u) t z) (nativeFamilyEdgeForcingMap Ledge i))
      (u0 : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w0 : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
      (Z : X →ₗ[ℝ] (∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ rs 0
        (volume.restrict (Set.Icc a b))))
      (_h0 : ∀ ξ, IsPlaneChainFrom (geometryScalarData 2 (fun t _ => G t 0)) (fun _ i => K i)
        a b vd (fun _ i => V₀ ξ i) (fun _ _ _ => 0) (fun _ i => u0 ξ i) (fun _ i => w0 ξ i))
      (_hZ : ∀ ξ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ rs 0 (volume.restrict (Set.Icc a b))
        (Z ξ i) (w0 ξ i))
      (T : X → ∀ i, PlaneHk Set.univ (K i) (h i)) (τ : ℝ) (_hτ : τ ∈ Set.Icc a b)
      (_hT : ∀ ξ, ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
        (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
        (∀ i, ContinuousOn (fun t => uH ξ i t - u i t) (Set.Icc a b)) ∧
        (∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
          truncatePlaneHk (Nat.le_succ (K i)) (wH ξ i t - w i t) = uH ξ i t - u i t) ∧
        (∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ rs 0 (volume.restrict (Set.Icc a b))
          ((∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1),
            finiteResponse 1 (nativeDiagonalResponseOperator R positive)
              (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) (Z ξ) j k) i)
          (w i)) ∧
        (∀ i, T ξ i = u i τ) ∧
        (∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq n ϖ 0 rs (K i) (uH ξ i τ - T ξ i)) ≤ Bd ξ),
    BlockWordConclusion K J H (fun t => G t 0) (blockMetricLetter (D := D) (h := h) G X₀ δ Ks θM bM)
      (blockSourceLetter F S₀ actual hφ (Set.Icc tS tZ) l σ yc (ocEpsilon q Λ m)
        (ocEpsilon q Λ (m - 1)) ℓ2 Ks θS bS) X₀ δ a b vd V₀ ϖ rs n π uH τ Bd := by
  intro ϖ rs yc G vd X₀ δ ℓ2 S₀ hϖdef hrsdef hycdef hGdef hvddef hX₀def hδdef hℓ2def hS₀def
    V₀ hf uH wH hHc hHt R hR positive hpos Ledge hLedge u0 w0 Z h0 hZ T τ hτ hT
  let Ml := blockMetricLetter (D := D) (h := h) G X₀ δ Ks θM bM
  let Sl := blockSourceLetter F S₀ actual hφ (Set.Icc tS tZ) l σ yc (ocEpsilon q Λ m)
    (ocEpsilon q Λ (m - 1)) ℓ2 Ks θS bS
  have he : ocEpsilon q Λ m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hE : ocEpsilon q Λ (m - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hδ : δ ≠ 0 := by rw [hδdef]; exact div_ne_zero he hE
  have hsc := windowCover_native_subwindow_scales hΛ hφ cov ic a b hwindow
  have htime : ∀ t ∈ Set.Icc a b, ℓ2 * t ∈ Set.Icc tS tZ := by
    intro t ht
    have h1 := hsc.2.1 t ht
    rwa [hℓ2def, show ν⁻¹ * ocEpsilon q Λ m ^ 2 * t = ν⁻¹ * (ocEpsilon q Λ m ^ 2 * t) by ring]
  have hfluxM : ∀ (N : ℕ) (j : Fin N) (x : ι) (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u))
      (t : ℝ), t ∈ Set.Icc a b →
      (fun z => Weighted.letterAdmissibleFlux Ml (fun p : Fin (N + 1) × ι => K p.2) (j.succ, x)
        (fun u => (j.castSucc, u)) x 1 X₀ δ W t z) =
        (fun t W => planeMatrixGradientFlux
          (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z) W) t (W x) := by
    intro N j x W t _
    funext z
    exact hFM hD G X₀ δ hδ Ks θM bM K j x W t z
  have hfluxS : ∀ (N : ℕ) (j : Fin N) (x : ι) (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u))
      (t : ℝ), t ∈ Set.Icc a b →
      (fun z => Weighted.letterAdmissibleFlux Sl (fun p : Fin (N + 1) × ι => K p.2) (j.succ, x)
        (fun u => (j.castSucc, u)) x 0 X₀ δ W t z) =
        (fun i t W z => ∑ u, ∑ γ : F.Γ i u, blockLetterFieldFlux Ks F S₀ actual K ℓ2 hφ l σ
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc i u γ (W u) t z) x t W := by
    intro N j x W t ht
    funext z
    rw [hX₀def, hδdef]
    exact hFS F S₀ actual hφ (Set.Icc tS tZ) l σ yc (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1))
      ℓ2 he hE Ks θS bS K hdesc N j x W t (htime t ht) z
  have hfin : ∀ (Fo : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
      (f : ∀ x, PlaneHk Set.univ (K x) (h x)) (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
      (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x)),
      (∀ n x, weightedFactorialNormSq n ϖ 0 rs (K x) (f x) ≠ ⊤) →
      (∀ x, ∃ g : PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h x)) (K x) ϖ rs 0
        (volume.restrict (Set.Icc a b)),
        PlaneTimeAllMomentRepresents (K x) ϖ rs 0 (volume.restrict (Set.Icc a b)) g (Fo x)) →
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ => G t 0)) (fun _ x => K x) a b vd
        (fun _ x => f x) (fun _ x => Fo x) (fun _ x => u x) (fun _ x => w x) →
      ∀ n x t, t ∈ Set.Icc a b → weightedFactorialNormSq n ϖ 0 rs (K x) (u x t) ≠ ⊤ := by
    intro Fo f u w hf' hg hs
    choose Q hQ using hg
    subst hϖdef hrsdef hvddef hGdef hycdef
    exact windowCover_frozen_response_endpoint_all_moments hΛ hζ hφ cov K hK ic a b hab hwindow
      hgsmall hg0 hlength _ rfl Fo Q hQ f hf' u w hs
  have hT' : ∀ ξ, ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      (∀ i, ContinuousOn (u i) (Set.Icc a b)) ∧
      (∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
        truncatePlaneHk (Nat.le_succ (K i)) (w i t) = u i t) ∧
      (∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ rs 0 (volume.restrict (Set.Icc a b))
        ((∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1),
          finiteResponse 1 (nativeDiagonalResponseOperator R positive)
            (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) (Z ξ) j k) i)
          (w i)) ∧
      ∀ i, T ξ i = u i τ := by
    intro ξ
    obtain ⟨u, w, hec, het, hrep, hTu, -⟩ := hT ξ
    obtain ⟨hcu, htr⟩ := retained_trace_clean K a b (uH ξ) (wH ξ) (hHc ξ) (hHt ξ) u w hec het
    exact ⟨u, w, hcu, htr, hrep, hTu⟩
  obtain ⟨uW, wW, hchain, hlin, hfinW, hfldW, hsum⟩ := wordGeometry_of_retained hD K hab ϖ rs
    (fun t => G t 0) vd R hR positive (nativeFamilyEdgeForcingMap Ledge)
    (fun _ t W => planeMatrixGradientFlux
      (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z) W)
    (fun i t W z => ∑ u, ∑ γ : F.Γ i u, blockLetterFieldFlux Ks F S₀ actual K ℓ2 hφ l σ
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc i u γ (W u) t z)
    hpos hLedge Ml Sl X₀ δ rfl rfl hfluxM hfluxS J H V₀ (fun ξ n i => hf ξ n i) u0 w0 Z h0 hZ
    hfin T τ hτ hT'
  unfold BlockWordConclusion
  refine ⟨uW, wW, fun wd _ ξ => hchain wd ξ, fun wd _ => hlin wd, fun wd _ => hfinW wd,
    fun wd _ => hfldW wd, ?_⟩
  intro ξ
  obtain ⟨-, -, -, -, -, -, hb⟩ := hT ξ
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) hb
  rw [← hsum ξ i]

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **One renewal block in word form**.

`blockWordGeometry_of_package`: the block edge package (`BlockEdgePackageStatement`) and the two letter-flux
identities give `BlockWordGeometryStatement`. The proof feeds the block package, the metric maps and frozen
response into the shared core
(`windowCover_constructed_homogeneous_retained_linear_endpoint_all_moments_bound`) with the block
raw readout `blockLetterRawConstituent` and the remainder constant `Crem`, and concludes with
`blockWordGeometry_finish`. The source coefficient's data come from the window lemma
(`σ ∈ [tS, tZ]`) or reference lemma (`σ = l₀ τ''`).

Elaboration note: the statement is a `def`, so its instance proofs are auxiliary constants; the
finish lemma therefore receives only `0`-free projections of the cell solution and of the endpoint
clause, shares the named conclusion `BlockWordConclusion`, and the endpoint existential is read
with `choose`/`choose_spec` (a `casesOn` on it would make every later unification expensive). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

universe u v w x y

namespace AVRegularity.CycleJointProofs.Assembly

/-- **The block word geometry**, from the block edge package and the letter-flux identities. -/
theorem blockWordGeometry_of_package (hpkg : BlockEdgePackageStatement.{u, v, w, x})
    (hFM : MetricLetterFluxStatement.{u, v}) (hFS : SourceLetterFluxStatement.{u, v, w, x}) :
    BlockWordGeometryStatement.{u, v, w, x, y} := by
  intro D Ks Kmax Jchart Jm hchart hmol hKsJ Cm Cchart CG
  obtain ⟨Cprep, Crem, hCprep, hCrem, hpkgB⟩ := hpkg D Kmax Jchart Jm hchart hmol Cm Cchart Ks hKsJ
  obtain ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, hcore⟩ :=
    windowCover_constructed_homogeneous_retained_linear_endpoint_all_moments_bound.{u, v, w, x, y}
      Ks Kmax CG
  refine ⟨Cprep, CT, CR, Cterminal, Crem, hCprep, hCT, hCR, hCterminal, hCrem, ?_⟩
  intro α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb qJ
    y₀
    cov hΛ heE ha hgsmall hg0 hD ι _ _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hc hcover σ henv ic a b hab hwindow l hσl hdisj hblock S hcoreS hquiet θ hrow hcol hdesc hKs
    hθ hqJ
    hlength ϖ ζ yc G vd A X _ _ n H N J hdepth Cw W WM V₀ hf uH wH hH L hL hreserve hgain hN τ hτ
    θM θS bM bS X₀ δ Ml Sl C cm cs ct θcap ζcap η G0
  have hdisj' : l = l₀ ∨ σ ∈ Set.Icc tS tZ := hdisj.imp (fun h => h.1) id
  obtain ⟨Rs, Ledge, hsource, hrem, -, hrows, hcols⟩ := hpkgB α q Λ m ζfast Φ hφ tS tZ Cpad
    Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb qJ CG y₀ cov hΛ heE ha F hmeas hwmeas π hπ
    K hK actual B hB hc hcover σ henv yc ic a b hab.le hwindow l hσl hdisj' hblock S hcoreS hquiet
    θ hrow
    hcol hdesc hKs hθ
  obtain ⟨diag, positive, Rm, hmetric, -⟩ :=
    windowCover_exists_metric_source_originalEdge_allMoment_maps (h := h) hΛ hφ cov Ks hqJ K hK
      ic a b hwindow ϖ rfl D hD A Ledge Rs hsource.1
  obtain ⟨R, hR⟩ := windowCover_frozen_family_component_all_moment_response (h := h) hΛ hζ hφ
    cov K hK ic a b hab hwindow hgsmall hg0 hlength ϖ rfl
  obtain ⟨hsub, -, hϖ, hscale, hζslow, hζslow1, hδ⟩ :=
    windowCover_native_subwindow_scales hΛ hφ cov ic a b hwindow
  have hdata : (∀ v u d, coefficientSeminorm (ρ / ocEpsilon q Λ m) (K v) a b (A v u d) ≠ ⊤) ∧
      (∀ v u d t, t ∈ Set.Icc a b → ContDiff ℝ (K v : ℕ) (A v u d t)) ∧
      (∀ v u d, Measurable (fun p : Set.Icc a b × Vec 2 => A v u d p.1 p.2)) := by
    rcases hdisj' with hl | hσ
    · have hσ' : σ = (l₀ : ℝ) * ocTauPP α q Λ m := by rw [hσl, hl]
      have hd := preparationReferenceCellSource_pointwise_subwindow_data
        F hc ν (ocEpsilon q Λ m) ρ cov.pos.1 cov.pos.2.2 cov.rho_e heE K Kmax Jm
        hK hchart hmol Cm hmeas hwmeas actual yc π hπ B hB henv a b
        (ρ / ocEpsilon q Λ m) hsub
      simp only [A, hσ']
      exact ⟨hd.1, hd.2.1, hd.2.2.1⟩
    · have hd := preparationWindowReferenceCellSource_pointwise_subwindow_data
        F hc hcover σ hσ ν (ocEpsilon q Λ m) ρ cov.pos.1 cov.pos.2.2 cov.rho_e heE K Kmax Jm
        hK hchart hmol Cm hmeas hwmeas actual yc π hπ B hB henv a b
        (ρ / ocEpsilon q Λ m) hsub
      exact ⟨hd.1, hd.2.1, hd.2.2.1⟩
  obtain ⟨u0, w0, Z, h0, hZ, hrest⟩ := hcore (ι := ι) (h := h)
    α q Λ m ζfast hζ Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ l₀ P y₀ cov
    hΛ heE ic a b hab hwindow hqJ hgsmall hg0 hlength
    (ρ / ocEpsilon q Λ m) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) vd G rfl rfl rfl rfl
    n D H N Cw Cprep Crem θ hθ π hπ K hK ϖ rfl W hD A hdata.1 hdata.2.1 hdata.2.2 hrows hcols
    (sourceDepthRank F H) (sourceDepthRank_le F H)
    (fun i j hr d => preparationReferenceCellSourceCoefficient_zero_of_rank F hφ H hdepth
      σ ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc i j d hr)
    V₀ hf uH wH hH (fun t => G t 0) R positive Ledge F J hdepth
    (blockLetterRawConstituent Ks F (F.locally_finite tS tZ).toFinset actual K
      (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) hφ l σ (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc
      ϖ (ρ / ocEpsilon q Λ m) (volume.restrict (Set.Icc a b)))
    (blockLetterRawConstituent_zero Ks F (F.locally_finite tS tZ).toFinset actual K
      (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) hφ l σ (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc
      ϖ (ρ / ocEpsilon q Λ m) (volume.restrict (Set.Icc a b)))
    hsource.2.1 hR Rs diag Rm rfl hsource.1 hmetric.1 hmetric.2.1 hmetric.2.2 WM
    L ζ hL hζslow hζslow1 hϖ hscale hδ hreserve hrem hgain hN τ hτ
  dsimp only at hrest
  have hT := hrest.choose_spec.2
  exact blockWordGeometry_finish hFM hFS hζ hφ cov hΛ hgsmall hg0 hD F actual K hK hdesc ic a b
    hab hwindow hlength Ks l σ θM θS bM bS J H π n _ ϖ (ρ / ocEpsilon q Λ m) yc G vd X₀ δ
    (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) (F.locally_finite tS tZ).toFinset rfl rfl rfl rfl rfl rfl rfl
    rfl rfl V₀ hf uH wH (fun ξ i => (hH ξ).1 i) (fun ξ i => (hH ξ).2.2.1 i) R hR positive
    hmetric.2.1 Ledge hsource.2.1 u0 w0 Z h0 hZ hrest.choose τ hτ
    (fun ξ => (hT ξ).imp fun _ => Exists.imp fun _ hf => hf.elim fun _ h =>
      ⟨fun i => h.1.1 i, fun i => h.1.2.2.1 i, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Word chains and data at slot `0`**.

* `metricEdges_order`: the metric letter has edges of order `2` only; the source letter of a
  family without edges has no edges (`blockSourceEdges_eq_nil`); so every word of these letters
  descends at slot `0`.
* `isPlaneChain_truncate`: a word chain truncates to lower slots when every nonempty edge is
  admitted at both slot assignments.
* `twoV₀_slotZero`: the cell datum at slot `0` of the truncated torus datum is the truncation of
  the cell datum at slot `K`.

For the empty word there is a single level and the chain is the truncation of a scalar chain. -/

@[expose] public section

open Homogenization AVenhance AVRegularity.Sobolev MeasureTheory

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

section Letters

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ}

/-- The metric letter's edges have order `2`. -/
theorem metricEdges_order [DecidableEq ι] (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (X₀ : Vec 2) (δ : ℝ) (x y : ι) (o : Finset.Icc 2 D)
    (hne : metricEdges (D := D) (h := h) G X₀ δ x y o ≠ []) : o.1 = 2 := by
  unfold metricEdges at hne
  by_contra hc
  exact hne (dite_eq_right_iff.2 fun hv => absurd hv.2 hc)

/-- The metric letter descends at slot `0`. -/
theorem blockMetricLetter_slotZero [DecidableEq ι] (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (X₀ : Vec 2) (δ : ℝ) (Ks : ℕ) (θ : ℝ) (b : ι → ι → ℝ) (x y : ι) (o : Finset.Icc 2 D)
    (hne : (blockMetricLetter (D := D) (h := h) G X₀ δ Ks θ b).edge x y o ≠ []) :
    0 + o.1 ≤ 0 + 2 := by
  rw [metricEdges_order G X₀ δ x y o hne]

/-- The source letter of a family without edges descends at slot `0` (it has no edges). -/
theorem blockSourceLetter_slotZero {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    (hedge : ∀ v u, IsEmpty (F.Γ v u)) (S : Finset P) (actual : ∀ p, Ctx p)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (W : Set ℝ) (l : ℤ) (σ : ℝ) (yc : Vec 2)
    (e E ℓ2 : ℝ) (Ks : ℕ) (θ : ℝ) (b : ι → ι → ℝ) (x y : ι) (o : Finset.Icc 2 D)
    (hne : (blockSourceLetter F S actual hφ W l σ yc e E ℓ2 Ks θ b).edge x y o ≠ []) :
    0 + o.1 ≤ 0 + 2 :=
  absurd (blockSourceEdges_eq_nil F S actual hφ W l σ yc e E ℓ2 x y (hedge x y) o) hne

end Letters

section Chains

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The truncation of the level data of a chain is the level data of the truncated datum. -/
theorem chainDatum_truncate (κ κ' : Fin (N + 1) → ι → ℕ) (hκ : ∀ j x, κ' j x ≤ κ j x)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)) :
    (fun j x => truncatePlaneHk (hκ j x) (CycleWords.Assembly.chainDatum κ f j x)) =
      CycleWords.Assembly.chainDatum κ' (fun x => truncatePlaneHk (hκ 0 x) (f x)) := by
  funext j x
  by_cases hj : j = 0
  · subst hj
    simp [CycleWords.Assembly.chainDatum]
  · simp [CycleWords.Assembly.chainDatum, hj]

/-- **A word chain truncates to lower slots** at which every nonempty edge is admitted. -/
theorem isPlaneChain_truncate (hD : 2 ≤ D) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (κ κ' : Fin (N + 1) → ι → ℕ)
    (hκ : ∀ j x, κ' j x ≤ κ j x)
    (hc : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ j.succ x + o.1 ≤ κ j.castSucc y + 2)
    (hc' : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ' j.succ x + o.1 ≤ κ' j.castSucc y + 2)
    (X₀ : Vec 2) (δ a b : ℝ) (vd : ℝ → Vec 2 → Vec 2) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ j x, ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ j x, ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hs : IsPlaneChain (wordChainData G letters X₀ δ) κ a b vd f (fun _ _ _ => 0) u w) :
    IsPlaneChain (wordChainData G letters X₀ δ) κ' a b vd
      (fun x => truncatePlaneHk (hκ 0 x) (f x)) (fun _ _ _ => 0)
      (fun j x t => truncatePlaneHk (hκ j x) (u j x t))
      (fun j x t => truncatePlaneHk (Nat.succ_le_succ (hκ j x)) (w j x t)) := by
  rw [CycleWords.Assembly.isPlaneChain_iff_from] at hs ⊢
  have ht := CycleWords.wordChainFrom_truncate hD G letters κ κ' hκ hc hc' X₀ δ a b vd
    (CycleWords.Assembly.chainDatum κ f) (fun _ _ _ => 0) u w hs
  refine CycleWords.Assembly.IsPlaneChainFrom.congr_data ht (chainDatum_truncate κ κ' hκ f) ?_
  funext j x t
  exact map_zero _

end Chains

section Datum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- The value of a truncation is the value. -/
theorem planeValue_truncate {k K : ℕ} (hk : k ≤ K) (U : PlaneHk Set.univ K E) :
    planeValue (truncatePlaneHk hk U) = planeValue U :=
  CycleWords.planeJetOrder_truncate hk (Nat.zero_le k) U _

omit [FiniteDimensional ℝ E] in
theorem planeValue_eq_jet {K : ℕ} (U : PlaneHk Set.univ K E) :
    planeValue U = U.toFunction.jet (valueIndex2 K) := by
  funext z
  simp only [planeValue, planeJetOrder, dite_eq_left (Nat.zero_le K)]
  rfl

/-- The patch localization commutes with truncation. -/
theorem spatialPatchLocalization_truncate {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ)
    (hN : 0 < N) (j : Fin 2 → ℤ) {k K : ℕ} (hk : k ≤ K) (f : TorusHk K E) :
    spatialPatchLocalization hζ N hN j k (truncateTorusHk hk f) =
      truncatePlaneHk hk (spatialPatchLocalization hζ N hN j K f) := by
  apply CycleWords.planeHk_eq_of_planeValue_ae
  have htr : planeValue (truncatePlaneHk hk (spatialPatchLocalization hζ N hN j K f)) =
      planeValue (spatialPatchLocalization hζ N hN j K f) :=
    CycleWords.planeJetOrder_truncate hk (Nat.zero_le k) _ _
  rw [htr, planeValue_eq_jet, planeValue_eq_jet]
  have h1 := localizeTorusCarrier_value_ae (truncateTorusHk hk f) (spatialPatchCoefficient ζ N j)
    (spatialPatchCoefficient_smooth hζ N j k) (spatialPatchCoefficient_compact hζ N hN j)
  have h2 := localizeTorusCarrier_value_ae f (spatialPatchCoefficient ζ N j)
    (spatialPatchCoefficient_smooth hζ N j K) (spatialPatchCoefficient_compact hζ N hN j)
  exact h1.trans h2.symm

end Datum

section TwoDatum

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

/-- **The cell datum at slot `0`** of the truncated torus datum is the truncation of the cell
datum at slot `K`. -/
theorem twoV₀_slotZero
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hedge : ∀ v u, IsEmpty (F.Γ v u)) (hΛ : 1 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ) (Npatch : ℕ) (hNpatch : 0 < Npatch)
    (patch : Fin 2 → ℤ) (ξ : ∀ i, TorusHk (K i) (h i)) (i : ι) :
    twoV₀ (hp.slotZero hedge) hΛ hchart hζ Npatch hNpatch patch
        (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i)) i =
      truncatePlaneHk (Nat.zero_le (K i)) (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ i) := by
  unfold twoV₀
  rw [preparationReferenceCellLocalizedInitialFamilyLinearMap_apply,
    preparationReferenceCellLocalizedInitialFamilyLinearMap_apply,
    spatialPatchLocalization_truncate, ← planeCarrierAffine_truncate]
  congr 1
  unfold preparationReferenceHkWindowPull
  exact (planeHkWindowChartPull_truncate (Nat.zero_le (K i)) _ _ hφ _ _ _ _ _
    ⟨le_rfl, (twoWindow_le hΛ tS)⟩ _).symm

end TwoDatum

section Unique

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

/-- The gradient moments of a field are finite when its full moments of one more order are
finite. -/
theorem gradMoment_ne_top_of_full {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {k L : ℕ}
    (hkL : k + 1 ≤ L) (ϖ ρ : ℝ) (hρ : 0 < ρ) (S : Set ℝ) (W : ℝ → PlaneHk Set.univ L E) (n : ℕ)
    (hW : (∫⁻ t in S, weightedFactorialNormSq n ϖ 0 ρ L (W t)) ≠ ⊤) :
    (∫⁻ t in S, weightedGradFactorialNormSq n ϖ 0 ρ k (truncatePlaneHk hkL (W t))) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top
    (ENNReal.ofReal_ne_top (r := (((k + 1 : ℕ) : ℝ) ^ 2 / ρ ^ 2))) hW) ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun t => ?_
  refine (weightedGradFactorialNormSq_le_full_lift n ϖ 0 ρ hρ _).trans ?_
  gcongr
  exact (weightedFactorialNormSq_truncate_le hkL (W t) n ϖ 0 ρ (k + 1)).trans
    (weightedFactorialNormSq_order_mono n ϖ 0 ρ hkL (W t))

/-- The gradient moments of a field of order `k + 1` are finite when its full moments are. -/
theorem gradMoment_ne_top_of_lift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {k : ℕ}
    (ϖ ρ : ℝ) (hρ : 0 < ρ) (S : Set ℝ) (W : ℝ → PlaneHk Set.univ (k + 1) E) (n : ℕ)
    (hW : (∫⁻ t in S, weightedFactorialNormSq n ϖ 0 ρ (k + 1) (W t)) ≠ ⊤) :
    (∫⁻ t in S, weightedGradFactorialNormSq n ϖ 0 ρ k (W t)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top
    (ENNReal.ofReal_ne_top (r := (((k + 1 : ℕ) : ℝ) ^ 2 / ρ ^ 2))) hW) ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun t => weightedGradFactorialNormSq_le_full_lift n ϖ 0 ρ hρ (W t)

/-- A chain with an equal level-zero datum. -/
private theorem isPlaneChain_datum_congr {N : ℕ} {cd : PlaneChainData ι h D N}
    {κ : Fin (N + 1) → ι → ℕ} {t₀ t₁ : ℝ} {vd : ℝ → Vec 2 → Vec 2}
    {f f' : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)}
    {F : ∀ (j : Fin (N + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x))}
    {u : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x)}
    {w : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)}
    (hff : f = f') (hs : IsPlaneChain cd κ t₀ t₁ vd f F u w) :
    IsPlaneChain cd κ t₀ t₁ vd f' F u w :=
  hff ▸ hs

/-- **Uniqueness at the seam**: an old word chain at slot `0` from the truncated datum is the truncation
of the old word chain at slots `Kv`, when the letters descend at both slot assignments and both
fields have finite moments. -/
theorem oldChain_slotZero_eq (hU : WordChainUniqueStatement.{u, v})
    (hcongr : PlaneChainMetricCongrStatement.{u, v}) (hD : 2 ≤ D) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (G GO : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ) (hab : a ≤ b)
    (hGO : ∀ s ∈ Set.Icc a b, G s = GO s) (hGm : IsCellMetric (fun t _ => GO t)) (g : ℝ)
    (hg : g ≤ 1 / 4) (hGn : IsMetricNearIdentity (fun t _ => GO t) g)
    (vd : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift vd) (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (vd t))
    (J H : ℕ) (Kv : ι → ℕ) (MO SO : CycleLetter ι h D)
    (hM : IsCycleLetter π MO (Set.Icc a b ×ˢ Set.univ) J H)
    (hS : IsCycleLetter π SO (Set.Icc a b ×ˢ Set.univ) J H)
    (hMm : ∀ x y o, ∀ γ ∈ MO.edge x y o, ∀ β X z, Measurable fun t => γ.coeff β t X z)
    (hSm : ∀ x y o, ∀ γ ∈ SO.edge x y o, ∀ β X z, Measurable fun t => γ.coeff β t X z)
    (hMK : ∀ x y (o : Finset.Icc 2 D), MO.edge x y o ≠ [] → Kv x + o.1 ≤ Kv y + 2)
    (hSK : ∀ x y (o : Finset.Icc 2 D), SO.edge x y o ≠ [] → Kv x + o.1 ≤ Kv y + 2)
    (hM0 : ∀ x y (o : Finset.Icc 2 D), MO.edge x y o ≠ [] → 0 + o.1 ≤ 0 + 2)
    (hS0 : ∀ x y (o : Finset.Icc 2 D), SO.edge x y o ≠ [] → 0 + o.1 ≤ 0 + 2)
    (wo : List Bool) (X₀ : Vec 2) (δ : ℝ)
    (f : ∀ x, PlaneHk Set.univ (Kv x) (h x)) (f0 : ∀ x, PlaneHk Set.univ 0 (h x))
    (hf : ∀ x, f0 x = truncatePlaneHk (Nat.zero_le (Kv x)) (f x))
    (uO : ∀ (_ : Fin (wo.length + 1)) (x : ι), ℝ → PlaneHk Set.univ (Kv x) (h x))
    (wO : ∀ (_ : Fin (wo.length + 1)) (x : ι), ℝ → PlaneHk Set.univ (Kv x + 1) (h x))
    (hc : IsPlaneChain (wordChainData G (blockWordLetters MO SO wo) X₀ δ) (fun _ x => Kv x) a b
      vd f (fun _ _ _ => 0) uO wO)
    (uO0 : ∀ (_ : Fin (wo.length + 1)) (x : ι), ℝ → PlaneHk Set.univ 0 (h x))
    (wO0 : ∀ (_ : Fin (wo.length + 1)) (x : ι), ℝ → PlaneHk Set.univ (0 + 1) (h x))
    (hc0 : IsPlaneChain (wordChainData G (blockWordLetters MO SO wo) X₀ δ) (fun _ _ => 0) a b
      vd f0 (fun _ _ _ => 0) uO0 wO0)
    (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ)
    (hE : ∀ j x n,
      (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ (Kv x + 1) (wO j x t)) ≠ ⊤)
    (hE0 : ∀ j x n,
      (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ (0 + 1) (wO0 j x t)) ≠ ⊤) :
    ∀ j x, ∀ t ∈ Set.Icc a b, uO0 j x t = truncatePlaneHk (Nat.zero_le (Kv x)) (uO j x t) := by
  have hcK := hcongr G GO (blockWordLetters MO SO wo) X₀ δ (fun _ x => Kv x) a b vd f _ uO wO
    hGO hc
  have hcA := hcongr G GO (blockWordLetters MO SO wo) X₀ δ (fun _ _ => 0) a b vd f0 _ uO0 wO0
    hGO hc0
  have hcB := isPlaneChain_truncate hD GO (blockWordLetters MO SO wo) (fun _ x => Kv x)
    (fun _ _ => 0) (fun _ x => Nat.zero_le (Kv x))
    (fun j x y o hne => blockWordLetters_forall
      (fun L => ∀ x y (o : Finset.Icc 2 D), L.edge x y o ≠ [] → Kv x + o.1 ≤ Kv y + 2)
      hMK hSK wo j x y o hne)
    (fun j x y o hne => blockWordLetters_forall
      (fun L => ∀ x y (o : Finset.Icc 2 D), L.edge x y o ≠ [] → 0 + o.1 ≤ 0 + 2)
      hM0 hS0 wo j x y o hne) X₀ δ a b vd f uO wO hcK
  have hf' : (fun x => truncatePlaneHk (Nat.zero_le (Kv x)) (f x)) = f0 :=
    funext fun x => (hf x).symm
  replace hcB := isPlaneChain_datum_congr (κ := fun _ _ => 0) hf' hcB
  have hL : ∀ j, IsCycleLetter π (blockWordLetters MO SO wo j) (Set.Icc a b ×ˢ Set.univ) J H :=
    fun j => blockWordLetters_forall (fun L => IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H)
      hM hS wo j
  have hm : ∀ j x y o, ∀ γ ∈ (blockWordLetters MO SO wo j).edge x y o, ∀ β X z,
      Measurable fun t => γ.coeff β t X z :=
    fun j => blockWordLetters_forall
      (fun L => ∀ x y o, ∀ γ ∈ L.edge x y o, ∀ β X z, Measurable fun t => γ.coeff β t X z)
      hMm hSm wo j
  have he0 : ∀ (j : Fin (wo.length + 1)) (x : ι) (n : ℕ),
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ 0 ρ 0 (wO0 j x t)) ≠ ⊤ :=
    fun j x n => gradMoment_ne_top_of_lift ϖ ρ hρ _ (wO0 j x) n (hE0 j x n)
  have heK : ∀ (j : Fin (wo.length + 1)) (x : ι) (n : ℕ),
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ 0 ρ 0
        (truncatePlaneHk (Nat.succ_le_succ (Nat.zero_le (Kv x))) (wO j x t))) ≠ ⊤ :=
    fun j x n => gradMoment_ne_top_of_full _ ϖ ρ hρ _ (wO j x) n (hE j x n)
  intro j x t ht
  exact hU hD π hπ GO hGm g hg hGn vd hv hvs a b hab J H (blockWordLetters MO SO wo) hL hm
    X₀ δ (fun _ _ => 0) (fun _ _ => Nat.zero_le J) f0 uO0 _ wO0 _ hcA hcB ϖ ρ hϖ hρ he0 heK
    j x t ht

end Unique

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The model bound of one patch**.

The cell model of the seam (`Mc`) realized as a plane carrier of order `Mb` and returned
to physical variables at `t_p` by the following chart. With the cover centred at the
transported patch centre, the return sends the cell origin to the patch output centre
(`twoYcPost_eq`, flow cocycle), and its weighted energy with the weight `⟨(x - y)/R⟩^{2n}` at radius
`R` is at most
`(2 B₁)^{2n} C_comp² ε² Σ π⁻¹ wFNS n ϖ 0 ϖ⁻¹ Mb (realize Mc ξ)` (the weighted pullback bound, `ϖ = ε/R`)
`≤ … ε² weightedJetNorm² ≤ … ε² CM² momentNorm(V₀ ξ)²` (the jet-norm conversion and the seam's model bound)
`= (2 B₁)^{2n} C_comp² CM² Σ π⁻¹ ‖loc⁰ (trunc₀ ξ_i)‖²` (the `L²` norm of the cell datum).

For an empty index type both sides are `0`, and `CM = 0` is the zero model. For `Mb = 0` only the
value enters, with the composition constant at order `0`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev Set
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
  AVRegularity.CycleReference
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

section Model

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

/-- The chart centre of the future block: the cover's centre carried to `(l₀ + 1) τ''`. -/
theorem twoYcPost_eq
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) :
    twoYcPost hp = streamFlow (Φ (m - 1)) hφ (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) y₀
      ((l₀ : ℝ) * ocTauPP α q Λ m) := by
  unfold twoYcPost windowCoverChartCentre windowCoverFollowingChartIndex
  change ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1)
    (ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀) (1 + 1) = _
  rw [ocCellCentre, ocCellCentre, ocCellCentre]
  have h1 : l₀ - 1 + ((0 : ℕ) : ℤ) + 1 = l₀ := by omega
  have h2 : l₀ - 1 + ((0 : ℕ) : ℤ) = l₀ - 1 := by omega
  have h3 : l₀ - 1 + ((1 : ℕ) : ℤ) + 1 = l₀ + 1 := by omega
  have h4 : l₀ - 1 + ((1 : ℕ) : ℤ) = l₀ := by omega
  rw [h1, h2, h3, h4]
  unfold ocTransition
  rw [CycleComparison.Charts.streamFlow_group_law, CycleComparison.Charts.streamFlow_group_law]

/-- **The return sends the cell origin to the patch output centre** when the cover is centred at
the transported patch centre. -/
theorem return_centre_eq
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (N : ℕ) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS) :
    streamFlowHomeomorph hφ (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (twoTp α q Λ m l₀)
      (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) = twoYcPost hp := by
  rw [twoYcPost_eq, hyc]
  change streamFlow (Φ (m - 1)) hφ _ (streamFlow (Φ (m - 1)) hφ (twoTp α q Λ m l₀) _ tS)
    (twoTp α q Λ m l₀) = _
  rw [CycleComparison.Charts.streamFlow_group_law, CycleComparison.Charts.streamFlow_group_law]

/-- The return of the future block at order `Mb` (following chart, endpoint `t_p`). -/
def patchReturn (hΛ : 1 ≤ Λ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (Mb : ℕ) (hMb : Mb ≤ Jchart + 1) (i : ι) :
    PlaneHk Set.univ Mb (h i) →L[ℝ] PlaneHk Set.univ Mb (h i) :=
  preparationWindowReferenceCellReturnOperator hp.hprep hp.hcover
    (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (hp.windows hΛ).next (ocA_nonneg_of hΛ (m - 1)) Mb hMb
    (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne' (twoYcPost hp)
    (twoTp α q Λ m l₀) (hp.windows hΛ).tpMem

/-- The constant of the model bound: the Lipschitz and composition constants of the return. -/
def patchModelConstant (Cchart : ℕ → ℝ) (E : ℝ) (n Mb : ℕ) (CM : ℝ) : ℝ :=
  (2 * preparationPieceFlowJetBudget Cchart E 1) ^ (2 * n) *
    compositionFactorialNormBound (preparationFlowJetConstant Cchart) Mb ^ 2 * CM ^ 2

/-- The weighted pullback bound for the patch return: the weighted energy around the patch output centre at radius `R`
is at most `(2 B₁)^{2n} C_comp² ε²` times the cell energy at scale `ϖ = ε/R`, radius `1/ϖ`, centred
at the cell origin. -/
theorem patchReturn_weighted_le (hW : WeightedPullbackStatement.{v}) (hΛ : 1 ≤ Λ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (N : ℕ) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (Mb : ℕ) (hMb : Mb ≤ Jchart + 1) (n : ℕ) (i : ι) (V : PlaneHk Set.univ Mb (h i)) :
    weightedFactorialNormSq n (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j)
        (Real.sqrt (B * ocTauPP α q Λ m)) Mb (patchReturn hΛ hp Mb hMb i V) ≤
      ENNReal.ofReal ((2 * preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) 1) ^ (2 * n) *
          compositionFactorialNormBound (preparationFlowJetConstant Cchart) Mb ^ 2) *
        (ENNReal.ofReal (ocEpsilon q Λ m ^ 2) *
          weightedFactorialNormSq n (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
            (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹ Mb V) := by
  have hεpos : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hRpos : 0 < Real.sqrt (B * ocTauPP α q Λ m) :=
    Real.sqrt_pos.2 (mul_pos hp.cov.pos.2.1 (Construction.Stream.ocTauPP_pos hΛ))
  have hE : 0 < ocEpsilon q Λ (m - 1) := Construction.Stream.ocEpsilon_pos hΛ
  obtain ⟨hL1, hlip⟩ := preparationWindowReference_inverse_flow_lipschitz hp.hprep hp.hcover
    (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (hp.windows hΛ).next (ocA_nonneg_of hΛ (m - 1))
    (twoTp α q Λ m l₀) (hp.windows hΛ).tpMem
  have h := preparationWindowReferenceCellReturn_weighted_le hW hp.hprep hp.hcover
    (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (hp.windows hΛ).next (ocA_nonneg_of hΛ (m - 1)) Mb
    hMb hE (ocEpsilon q Λ m) hεpos.ne' (twoYcPost hp) (twoTp α q Λ m l₀) (hp.windows hΛ).tpMem
    hRpos.le hp.cov.RE _ hL1 hlip n (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
    (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) V
  rw [return_centre_eq hp N j hyc, sub_self, smul_zero] at h
  have e1 : (Real.sqrt (B * ocTauPP α q Λ m))⁻¹ * ocEpsilon q Λ m =
      ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m) := by ring
  have e2 : Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ m =
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹ := by rw [inv_div]
  have e3 : |((ocEpsilon q Λ m)⁻¹ ^ 2)⁻¹| = ocEpsilon q Λ m ^ 2 := by
    rw [inv_pow, inv_inv, abs_of_nonneg (sq_nonneg _)]
  rw [e1, e2, e3] at h
  exact h

end Model

section Chain

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The chain of the model bound with abstract scales: the return bound, the jet identification
of the realized model, the seam's model bound and the `L²` norm of the cell datum. -/
theorem model_bound_chain (π : ι → ℝ) (n Mb : ℕ) (ϖ ε : ℝ) (hϖ : 0 < ϖ) (Rw ρ : ℝ) (y : Vec 2)
    (c CM S : ℝ) (hc : 0 ≤ c) (hCM : 0 ≤ CM) (hε : ε ≠ 0)
    (W V : ∀ i, PlaneHk Set.univ Mb (h i)) (J : ∀ v (a : ℕ), DerivativeWord2 a → Vec 2 → h v)
    (h1 : ∀ i, weightedFactorialNormSq n Rw y ρ Mb (W i) ≤
      ENNReal.ofReal c * (ENNReal.ofReal (ε ^ 2) * weightedFactorialNormSq n ϖ 0 ϖ⁻¹ Mb (V i)))
    (hJ : ∀ v a, a ≤ Mb → ∀ w, planeJetOrder (V v) a w =ᵐ[volume] J v a w)
    (hmeas : ∀ v a w, AEStronglyMeasurable (J v a w) volume) (Mn : ℝ≥0∞)
    (hmodel : weightedJetNorm π (n : ℝ) Mb ϖ ϖ⁻¹ J ≤ ENNReal.ofReal CM * Mn)
    (hmom : Mn ^ 2 = ENNReal.ofReal ((ε ^ 2)⁻¹ * S)) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n Rw y ρ Mb (W i) ≤
      ENNReal.ofReal (c * CM ^ 2 * S) := by
  have h3 := weightedFactorialNormSq_family_le_weightedJetNorm_sq π n Mb ϖ ϖ⁻¹
    (inv_nonneg.2 hϖ.le) V J hJ hmeas
  calc ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n Rw y ρ Mb (W i)
      ≤ ∑ i, ENNReal.ofReal ((π i)⁻¹) * (ENNReal.ofReal c *
          (ENNReal.ofReal (ε ^ 2) * weightedFactorialNormSq n ϖ 0 ϖ⁻¹ Mb (V i))) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_right (h1 i) _
    _ = ENNReal.ofReal c * ENNReal.ofReal (ε ^ 2) *
          ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 ϖ⁻¹ Mb (V i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal CM * Mn) ^ 2 :=
        mul_le_mul_right (h3.trans (pow_le_pow_left₀ zero_le hmodel 2)) _
    _ = ENNReal.ofReal (c * CM ^ 2 * S) := by
        rw [mul_pow, hmom, ← ENNReal.ofReal_pow hCM, ← ENNReal.ofReal_mul hc,
          ← ENNReal.ofReal_mul (sq_nonneg CM),
          ← ENNReal.ofReal_mul (mul_nonneg hc (sq_nonneg ε))]
        congr 1
        field_simp

end Chain

section Patch

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

/-- **The model bound of one patch.** -/
theorem patch_model_bound (hW : WeightedPullbackStatement.{v}) (hΛ : 1 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (Mb : ℕ) (hMb : Mb ≤ Jchart + 1) (n : ℕ)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (CM : ℝ) (hCM : 0 ≤ CM) (ξ : ∀ i, TorusHk (K i) (h i))
    (hmodel : weightedJetNorm π (n : ℝ) Mb
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc ξ x) z) ≤
      ENNReal.ofReal CM * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x))) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n
        (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j)
        (Real.sqrt (B * ocTauPP α q Λ m)) Mb
        (patchReturn hΛ hp Mb hMb i (realizeCellModel Mb Mc hsm hmem ξ i)) ≤
      ENNReal.ofReal (patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n Mb CM *
        ∑ i, (π i)⁻¹ *
          ‖spatialPatchLocalizationCLM hζ N hN j (truncateTorusHk (Nat.zero_le (K i)) (ξ i))‖ ^ 2) := by
  have hεpos : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hRpos : 0 < Real.sqrt (B * ocTauPP α q Λ m) :=
    Real.sqrt_pos.2 (mul_pos hp.cov.pos.2.1 (Construction.Stream.ocTauPP_pos hΛ))
  have hL1 := (preparationWindowReference_inverse_flow_lipschitz hp.hprep hp.hcover
    (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (hp.windows hΛ).next (ocA_nonneg_of hΛ (m - 1))
    (twoTp α q Λ m l₀) (hp.windows hΛ).tpMem).1
  have hc : 0 ≤ (2 * preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) 1) ^ (2 * n) *
      compositionFactorialNormBound (preparationFlowJetConstant Cchart) Mb ^ 2 :=
    mul_nonneg (pow_nonneg (by linarith) _) (sq_nonneg _)
  exact model_bound_chain π n Mb _ _ (div_pos hεpos hRpos) _ _ _ _ CM _ hc hCM hεpos.ne'
    (fun i => patchReturn hΛ hp Mb hMb i (realizeCellModel Mb Mc hsm hmem ξ i))
    (realizeCellModel Mb Mc hsm hmem ξ) (fun v a w => orderedDerivative w (Mc ξ v))
    (fun i => patchReturn_weighted_le hW hΛ hp N j hyc Mb hMb n i _)
    (fun v a ha w => realizeCellModel_jet_ae Mb Mc hsm hmem ξ v a ha w)
    (fun v a w => (CycleWords.Assembly.orderedDerivative_continuous w (hsm ξ v a)).aestronglyMeasurable)
    _ hmodel (twoV₀_momentNorm_sq hΛ hchart hζ hp N hN j ξ _)

end Patch

end AVRegularity.CycleJointProofs.Assembly
end
end
