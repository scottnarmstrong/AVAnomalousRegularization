-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.TransitionJetTermDerivative
public import AVRegularity.CycleJoint.Assembly.SeamStatement
import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.Construction.Scales.Times
public import AVRegularity.Statements.Intermediate.Families.AtlasIsConsecutiveClosed
public import AVRegularity.Statements.Intermediate.Families.AtlasCoversQuiet
public import AVRegularity.Statements.Intermediate.Families.AtlasIsQuiet
public import AVRegularity.Statements.Intermediate.CycleJoint.IsWindowCover
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointModel
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointError
public import AVRegularity.Statements.Intermediate.Families.IsEnvelope
public import AVRegularity.Statements.Intermediate.CycleReference.OcRhoMol
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTransverseOnPulses
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsFastIndependentOn
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import AVRegularity.Construction.Stream.NextAdmissible

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The letters of a renewal block**.

In the cell frame of a block (reference time `σ`, chart centre `yc`, cell scale `e`, slow scale
`E`, cell time `τ ↦ ℓ² τ`, slow evaluation `X₀ = E⁻¹ yc`, `δ = e / E`) the seam (`cycle_seam`) and the
word chains (`wordChainData`) read every insertion as a letter whose coefficients are periodic in
the fast variable `z` and Taylor-expanded in the slow variable `X` at `X₀` with increment `δ z`.

* `blockMetricLetter`: the metric Taylor letter (`positive`), one diagonal order-2 constituent per
  component, with coefficient `G τ (δ⁻¹ (X - X₀)) - G τ 0`; its Taylor polynomial of degrees `1..Ks`
  at `X₀` with increment `δ z` is the Taylor polynomial of the cell metric at `0` with increment
  `z`.
* `blockSourceLetter`: one constituent per identity `γ` and order `d ≤ D_γ`, whose coefficient is
  the sum over the active pieces `p` of the time weight of `p` (restricted to the family's time
  window `W`, outside of which the premises say nothing) times the coefficient of `p`:
  - A piece of the block's label (anchor `σ`) is read in its own natural variables:
    `F.flux p c v u γ d α (ℓ² τ) X (z + e⁻¹ yc)` (the cell fiber).
  - Any other piece is active in the block only at quiet times, where its flux is fast
    independent; it is read as the transported slow field
    `transportedCoeff J_p (D_γ) (flux at E⁻¹ Y_p(x)) (d - 1) α x` at the cell point
    `x = δ⁻¹ (X - X₀)`, where `Y_p(x)` is the anchor-time label of `yc + e x` and `J_p` the
    natural preparation Jacobian; its fast argument is `0`. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ}

/-- The positive record of the metric letter. -/
def metricLetterRecord : ConstituentRecord where
  size := 0
  size_nonneg := le_rfl
  birthLevel := 0
  birthExcess := 0
  length := 1
  length_pos := one_pos
  width := 1
  width_pos := one_pos
  births := []

/-- The order-2 metric constituent of the component `u`: the flux `k` of the derivative `α` has
coefficient `G τ (δ⁻¹ (X - X₀)) k α - G τ 0 k α`. The frozen value `G τ 0` is the principal part
of the word chain and does not enter the letter (its Taylor degrees start at `1`), so it is
subtracted: the coefficient is then of size `O(g)` at every point (`IsMetricNearIdentity`). -/
def metricConstituent (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (X₀ : Vec 2) (δ : ℝ) : Constituent 2 H H where
  map := ContinuousLinearMap.id ℝ H
  coeff := fun α τ X _ k =>
    G τ (δ⁻¹ • (X - X₀)) k (α ⟨0, Nat.one_pos⟩) - G τ 0 k (α ⟨0, Nat.one_pos⟩)
  periodic := fun _ _ _ _ _ => rfl
  record := metricLetterRecord
  birthExcess_ge := le_rfl

/-- The metric edges: one order-2 constituent on every diagonal entry. -/
def metricEdges [DecidableEq ι] (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (X₀ : Vec 2)
    (δ : ℝ) : ConstituentEdges D h :=
  fun v u d =>
    if hvu : v = u ∧ d.1 = 2 then by
      obtain ⟨rfl, hd⟩ := hvu
      rw [hd]
      exact [metricConstituent (h v) G X₀ δ]
    else []

/-- **The metric letter of a block.** -/
def blockMetricLetter [DecidableEq ι] (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (X₀ : Vec 2) (δ : ℝ)
    (Ks : ℕ) (θ : ℝ) (b : ι → ι → ℝ) : CycleLetter ι h D where
  order := 2
  slow := Ks
  positive := true
  edge := metricEdges G X₀ δ
  theta := θ
  majorant := b

variable {P : Type*} {Ctx : P → Type*}

/-- The coefficient of a block letter, before the time weight of the piece, for the order `d`
and the derivative word `α`, at cell time `τ`, slow variable `X` and fast variable `z`.
* A piece of the block's label `l`: its flux in its own natural variables, fast variable shifted
  by `e⁻¹ yc`.
* Any other piece: the transported slow field at the cell point `x = δ⁻¹ (X - X₀)`
  (`X₀ = E⁻¹ yc`, `δ = e / E`), fast argument `0`. -/
def blockLetterCoefficient (F : ChartedFamily ι h D P Ctx) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (l : ℤ) (σ : ℝ)
    (yc : Vec 2) (e E ℓ2 : ℝ) (d : ℕ) (α : DerivativeWord2 (d - 1)) (τ : ℝ) (X z : Vec 2) :
    Vec 2 :=
  if (F.piece p).label = l then F.flux p c v u γ d α (ℓ2 * τ) X (z + e⁻¹ • yc)
  else transportedCoeff
      (fun x => naturalPreparationJacobian hφ (F.piece p).anchor σ (yc + e • x))
      (F.identity v u γ).maxOrder
      (fun d' A k => F.flux p c v u γ d' A (ℓ2 * τ)
        (E⁻¹ • streamFlow φ hφ (F.piece p).anchor
          (yc + e • ((e / E)⁻¹ • (X - E⁻¹ • yc))) σ) 0 k)
      (d - 1) α ((e / E)⁻¹ • (X - E⁻¹ • yc))

theorem blockLetterCoefficient_periodic (F : ChartedFamily ι h D P Ctx) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (l : ℤ) (σ : ℝ)
    (yc : Vec 2) (e E ℓ2 : ℝ) (d : ℕ) (α : DerivativeWord2 (d - 1)) (τ : ℝ) (X : Vec 2) :
    IsZ2Periodic (blockLetterCoefficient F hφ p c v u γ l σ yc e E ℓ2 d α τ X) := by
  intro n z
  unfold blockLetterCoefficient
  split_ifs
  · rw [show z + latticeShift n + e⁻¹ • yc = z + e⁻¹ • yc + latticeShift n by abel]
    exact F.flux_periodic p c v u γ d α (ℓ2 * τ) X n (z + e⁻¹ • yc)
  · rfl

/-- The constituent of the identity `γ` and order `d ≤ D_γ` of a block letter: the coefficients of
all pieces in `S`, weighted by their time weights and summed (one constituent per identity, so that
its jets are bounded by the supremum over the pieces, the weights summing to at most one). -/
def sourceConstituent (F : ChartedFamily ι h D P Ctx) (S : Finset P) (actual : ∀ p, Ctx p)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (hd : d ≤ (F.identity v u γ).maxOrder) (W : Set ℝ) (l : ℤ) (σ : ℝ) (yc : Vec 2)
    (e E ℓ2 : ℝ) : Constituent d (h u) (h v) where
  map := (F.identity v u γ).map
  coeff := fun α τ X z => ∑ p ∈ S, (W.indicator (F.weight p) (ℓ2 * τ)) •
    blockLetterCoefficient F hφ p (actual p) v u γ l σ yc e E ℓ2 d α τ X z
  periodic := fun α τ X n z => by
    change ∑ p ∈ S, (W.indicator (F.weight p) (ℓ2 * τ)) • blockLetterCoefficient F hφ p (actual p)
        v u γ l σ yc e E ℓ2 d α τ X (z + latticeShift n) = ∑ p ∈ S,
      (W.indicator (F.weight p) (ℓ2 * τ)) •
        blockLetterCoefficient F hφ p (actual p) v u γ l σ yc e E ℓ2 d α τ X z
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [blockLetterCoefficient_periodic F hφ p (actual p) v u γ l σ yc e E ℓ2 d α τ X n z]
  record := (F.identity v u γ).record
  birthExcess_ge := le_trans hd (F.identity v u γ).le_birth

/-- The source edges of a block of label `l` from the pieces in `S`, restricted to the physical
time window `W`: one constituent for every identity `γ` and order `d ≤ D_γ`. -/
def blockSourceEdges (F : ChartedFamily ι h D P Ctx) (S : Finset P) (actual : ∀ p, Ctx p)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (W : Set ℝ) (l : ℤ) (σ : ℝ) (yc : Vec 2)
    (e E ℓ2 : ℝ) : ConstituentEdges D h :=
  fun v u d => (Finset.univ.toList : List (F.Γ v u)).filterMap fun γ =>
    if hd : d.1 ≤ (F.identity v u γ).maxOrder then
      some (sourceConstituent F S actual hφ v u γ d.1 hd W l σ yc e E ℓ2)
    else none

/-- **The source letter of a block of label `l`.** -/
def blockSourceLetter (F : ChartedFamily ι h D P Ctx) (S : Finset P) (actual : ∀ p, Ctx p)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (W : Set ℝ) (l : ℤ) (σ : ℝ) (yc : Vec 2)
    (e E ℓ2 : ℝ) (Ks : ℕ) (θ : ℝ) (b : ι → ι → ℝ) : CycleLetter ι h D where
  order := D
  slow := Ks
  positive := false
  edge := blockSourceEdges F S actual hφ W l σ yc e E ℓ2
  theta := θ
  majorant := b

/-- The words with at most `J` metric (`false`) and `H` source (`true`) insertions, listed last
insertion first (`responseWordSet`). -/
def blockWords (J H : ℕ) : Finset (List Bool) :=
  (Finset.range (J + 1)).biUnion fun j => (Finset.range (H + 1)).biUnion fun k => responseWordSet j k

/-- The letters of a word in chronological order: `S` for a source insertion, `M` for a metric
insertion. -/
def blockWordLetters (M S : CycleLetter ι h D) (w : List Bool) :
    Fin w.length → CycleLetter ι h D :=
  fun i => if w.reverse[i.1]'(by rw [List.length_reverse]; exact i.2) then S else M

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The seam's body after its constants**.

`SeamPairBody` is the part of `CycleSeamStatement` after `∃ c CM CN, 0 < c ∧ … ∧`, with the scalar
constants, the threshold `g₁`, the shape, the orders, the supplied constants, the cutoff and the
seam's constants as parameters. `cycleSeam_body` restates `CycleSeamStatement` with it (by
definitional unfolding), so that the seam's constants can be chosen per word shape and its body
applied separately. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

/-- The body of `cycle_seam` after its constants. -/
def SeamPairBody (K : ScalarConstants) (g₁ : ℝ) (D H Kmax pout k Nm Np : ℕ)
    (dO KsO : Fin Nm → ℕ) (posO : Fin Nm → Bool) (dF KsF : Fin Np → ℕ) (posF : Fin Np → Bool)
    (Q Mmod Nmod qΥ : ℕ) (Cout C0 Cs CU CH : ℝ) (χm : Vec 2 → ℝ) (c : ℝ) (CM CN : ℕ → ℝ) :
    Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
    (lettersF : Fin Np → CycleLetter ι h D)
    (_hlF : ∀ i, (lettersF i).order = dF i ∧ (lettersF i).slow = KsF i ∧
      (lettersF i).positive = posF i)
    -- the common scales
    (η S ηg rstar ϖ : ℝ) (_hη : 0 < η) (_hη1 : η ≤ 1) (_hS : 1 ≤ S) (_hηg : 0 < ηg)
    (_hηg1 : ηg ≤ 1) (_hrstar : 0 < rstar) (_hrstarC : rstar ≤ Cout) (_hϖ : ϖ = Real.sqrt (η / S))
    -- the future complete block
    (tF : ℝ) (GF : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vF : ℝ → Vec 2 → Vec 2) (gF : ℝ)
    (_hGmF : IsCellMetric (fun t _ => GF t)) (_hvF : IsCellDrift vF)
    (_hv0F : ∀ t (k : Fin 2), cellMean (fun x => (vF t x k : ℂ)) = 0)
    (_hvsF : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (vF t))
    (_hvwF : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, vF t x i ^ 2) ≤ K.Cw)
    (_hvjF : ∀ (j : ℕ) t z,
      ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • vF t z') z‖ ≤ K.Cvj j)
    (_hg0F : 0 ≤ gF) (_hgF : gF ≤ K.g0) (_hg₁F : gF ≤ g₁) (_hGnF : IsMetricNearIdentity (fun t _ => GF t) gF)
    (regF : BlockRegions) (_pkgF : ScalarPackage K η GF vF tF S ϖ regF)
    (_hletF : ∀ i, IsCycleLetter π (lettersF i) (Set.Icc tF (tF + S) ×ˢ Set.univ)
      (2 * (k + Kmax + pout + (∑ i, KsO i + ∑ i, KsF i) + ∑ i, dF i + 2) +
        max (Finset.univ.sup dO) (Finset.univ.sup dF) + 2) H)
    (_htransF : ∀ i, IsTransverseOnPulses (lettersF i).edge
      (fun p : Fin regF.P => Set.Icc (regF.lo p) (regF.hi p)) regF.orient)
    (_hquietF : ∀ i, IsQuietOn (lettersF i).edge vF (regF.quiet ∩ Set.Icc tF (tF + S)))
    (_hmeasF : ∀ i x y o, ∀ γ ∈ (lettersF i).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z)
    (a : ℝ) (_ha : 0 ≤ a) (_haS : a ≤ S) (_hquietMargin : Set.Icc tF (tF + a) ⊆ regF.quiet)
    (X₀F : Vec 2)
    (_hC0 : peFactor η ^ Q * (1 + S) ^ Q * (1 + regF.joins) *
      Real.exp (-c * regF.buffer) ≤ C0),
  ∃ Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x),
    -- the future slots and output orders (the kernel is uniform in them), the old
    -- letters, the chart transition and the old partial piece
    ∀ (κF : Fin (Np + 1) → ι → ℕ) (Kout : ι → ℕ) (_hKout : ∀ x, Kout x ≤ Kmax)
      (_hκFf : ∀ x, Kout x ≤ κF (Fin.last Np) x)
      (_hκF : ∀ (j : Fin Np) x y (o : Finset.Icc 2 D), (lettersF j).edge x y o ≠ [] →
        κF j.succ x + o.1 ≤ κF j.castSucc y + 2)
      (lettersO : Fin Nm → CycleLetter ι h D)
      (_hlO : ∀ i, (lettersO i).order = dO i ∧ (lettersO i).slow = KsO i ∧
        (lettersO i).positive = posO i)
      (Υ Υinv : Vec 2 → Vec 2) (gU δ : ℝ) (_hδ : δ = ϖ * ηg)
      (_hgU : 0 ≤ gU ∧ gU ≤ K.g0) (_hΥ : IsCenteredTransition Υ Υinv gU δ CU qΥ)
      (_hΥs : ContDiff ℝ (⊤ : ℕ∞) Υinv)
      (tO SO aO bO : ℝ) (GO : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vO : ℝ → Vec 2 → Vec 2) (gO : ℝ)
      (_hGmO : IsCellMetric (fun t _ => GO t)) (_hvO : IsCellDrift vO)
      (_hv0O : ∀ t (k : Fin 2), cellMean (fun x => (vO t x k : ℂ)) = 0)
      (_hvsO : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (vO t))
      (_hvwO : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, vO t x i ^ 2) ≤ K.Cw)
      (_hvjO : ∀ (j : ℕ) t z,
        ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • vO t z') z‖ ≤ K.Cvj j)
      (_hg0O : 0 ≤ gO) (_hgO : gO ≤ K.g0) (_hg₁O : gO ≤ g₁) (_hGnO : IsMetricNearIdentity (fun t _ => GO t) gO)
      (regO : BlockRegions) (_pkgO : CoreScalarPackage K η GO vO tO SO ϖ regO)
      (_hwin : tO ≤ aO ∧ aO ≤ bO ∧ bO ≤ tO + SO) (_hdur : bO - aO ≤ CH * S)
      (_hC0O : peFactor η ^ Q * (1 + S) ^ Q * (1 + regO.joins) *
        Real.exp (-c * regO.buffer) ≤ C0)
      (_hseam : Set.Icc (bO - regF.buffer) bO ⊆ regO.quiet ∩ Set.Icc tO (tO + SO))
      (_hletO : ∀ i, IsCycleLetter π (lettersO i) (Set.Icc aO bO ×ˢ Set.univ)
        (2 * (k + Kmax + pout + (∑ i, KsO i + ∑ i, KsF i) + ∑ i, dF i + 2) +
          max (Finset.univ.sup dO) (Finset.univ.sup dF) + 2) H)
      (_htransO : ∀ i, IsTransverseOnPulses (lettersO i).edge
        (fun p : Fin regO.P => Set.Icc (regO.lo p) (regO.hi p)) regO.orient)
      (_hquietO : ∀ i, IsQuietOn (lettersO i).edge vO (regO.quiet ∩ Set.Icc tO (tO + SO)))
      (_hmeasO : ∀ i x y o, ∀ γ ∈ (lettersO i).edge x y o, ∀ α X z,
        Measurable fun t => γ.coeff α t X z)
      (X₀O : Vec 2) (κO : Fin (Nm + 1) → ι → ℕ)
      (_hκO : ∀ (j : Fin Nm) x y (o : Finset.Icc 2 D), (lettersO j).edge x y o ≠ [] →
        κO j.succ x + o.1 ≤ κO j.castSucc y + 2)
      (_hκmatch : ∀ x, κF 0 x ≤ κO (Fin.last Nm) x)
      (f : ∀ x, PlaneHk Set.univ (κO 0 x) (h x))
      (_hfsupp : ∀ x, ∀ᵐ z : Vec 2 ∂volume, (Cs / ϖ) ^ 2 < z 0 ^ 2 + z 1 ^ 2 →
        planeValue (f x) z = 0)
      (uO : ∀ (j : Fin (Nm + 1)) (x : ι), ℝ → PlaneHk Set.univ (κO j x) (h x))
      (wO : ∀ (j : Fin (Nm + 1)) (x : ι), ℝ → PlaneHk Set.univ (κO j x + 1) (h x))
      (_hchainO : IsPlaneChain (wordChainData GO lettersO X₀O δ) κO aO bO vO f
        (fun _ _ _ => 0) uO wO)
      (fF : ∀ x, PlaneHk Set.univ (κF 0 x) (h x))
      (_hfF : ∀ x, planeValue (fF x) =ᵐ[volume]
        fun z => planeValue (uO (Fin.last Nm) x bO) (Υ z))
      (uF : ∀ (j : Fin (Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x) (h x))
      (wF : ∀ (j : Fin (Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x + 1) (h x))
      (_hchainF : IsPlaneChain (wordChainData GF lettersF X₀F δ) κF tF (tF + S) vF fF
        (fun _ _ _ => 0) uF wF),
    (∀ x, ∀ M : ℕ, ContDiff ℝ M
      (Kp (fun x' z => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
          (planeValue (uO (Fin.last Nm) x' bO)) (Υ z)) x)) ∧
    (∀ M : ℕ, M ≤ Mmod →
      weightedJetNorm π (pout : ℝ) M ϖ ϖ⁻¹
          (fun x _ wd z => orderedDerivative wd
            (Kp (fun x' z' => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
              (planeValue (uO (Fin.last Nm) x' bO)) (Υ z')) x) z) ≤
        ENNReal.ofReal (CM M * (wordTheta ηg lettersO * wordTheta ηg lettersF)) *
          momentNorm π 0 ϖ (fun x => planeValue (f x))) ∧
    (∀ N : ℕ, 1 ≤ N → N ≤ Nmod →
      weightedJetNorm π (pout : ℝ) Kmax ϖ rstar
          (fun x a' wd z => if a' ≤ Kout x then planeJetOrder (uF (Fin.last Np) x (tF + S)) a' wd z -
            orderedDerivative wd
              (Kp (fun x' z' => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
                (planeValue (uO (Fin.last Nm) x' bO)) (Υ z')) x) z else 0) ≤
        ENNReal.ofReal (CN N * (wordTheta ηg lettersO * wordTheta ηg lettersF) *
            peFactor η ^ Q * (1 + S) ^ Q *
            (Real.exp (-c * S) + (1 + regF.joins) * Real.exp (-c * regF.buffer) +
              Real.exp (-c * a) + S ^ (-(N : ℝ) / 2))) *
          momentNorm π 0 ϖ (fun x => planeValue (f x)))

/-- `cycle_seam` with its body named. -/
theorem cycleSeam_body (hs : CycleSeamStatement.{u, v}) (K : ScalarConstants) :
    ∃ g₁ : ℝ, 0 < g₁ ∧
    ∀ (D H Kmax pout k : ℕ) (_hD : 2 ≤ D) (Nm Np : ℕ) (dO KsO : Fin Nm → ℕ) (posO : Fin Nm → Bool)
      (dF KsF : Fin Np → ℕ) (posF : Fin Np → Bool) (_hk : Kmax + ∑ i, dO i + 2 ≤ k),
    ∃ Q : ℕ, ∀ Mmod Nmod : ℕ, ∃ qΥ : ℕ,
    ∀ (Cout C0 Cs CU CH : ℝ) (_hCout : 0 < Cout) (_hCH : 0 < CH) (χm : Vec 2 → ℝ)
      (_hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χm) (_hχ_even : ∀ ξ, χm (-ξ) = χm ξ)
      (_hχ_supp : ∀ ξ, 2 * K.ξlo ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0)
      (_hχ_one : ∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → χm ξ = 1),
    ∃ (c : ℝ) (CM CN : ℕ → ℝ), 0 < c ∧ (∀ M, 0 < CM M) ∧ (∀ N, 0 < CN N) ∧
      SeamPairBody.{u, v} K g₁ D H Kmax pout k Nm Np dO KsO posO dF KsF posF Q Mmod Nmod qΥ Cout C0
        Cs CU CH χm c CM CN :=
  hs K

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The word letters for the seam**.

The letters of a word (`blockWordLetters M S w`) are the metric letter `M` or the source letter
`S`; every letter property shared by `M` and `S` holds for all of them. The shape of a word (orders
`2` and `D`, slow order `Ks`, positivity of the metric insertions) depends on the word only, and so
do the seam's order `k` and fast reserve of an allocation `(wo, wf)` (`seamOrderK`,
`seamReserve`). Constant slots `K` descend along the letters of a family with `IsDescending K`. -/

section Words

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ}

/-- Every letter of a word is `M` or `S`. -/
theorem blockWordLetters_forall {M S : CycleLetter ι h D} (Pr : CycleLetter ι h D → Prop)
    (hM : Pr M) (hS : Pr S) (w : List Bool) (i : Fin w.length) :
    Pr (blockWordLetters M S w i) := by
  unfold blockWordLetters
  split_ifs
  · exact hS
  · exact hM

/-- The orders of the letters of a word: `D` for a source insertion, `2` for a metric one. -/
def wordOrders (D : ℕ) (w : List Bool) : Fin w.length → ℕ :=
  fun i => if w.reverse[i.1]'(by rw [List.length_reverse]; exact i.2) then D else 2

/-- The positivity of the letters of a word (the metric insertions). -/
def wordPositive (w : List Bool) : Fin w.length → Bool :=
  fun i => if w.reverse[i.1]'(by rw [List.length_reverse]; exact i.2) then false else true

/-- The slow orders of the letters of a word. -/
def wordSlow (Ks : ℕ) (w : List Bool) : Fin w.length → ℕ := fun _ => Ks

/-- The letters of a word have the word's shape. -/
theorem blockWordLetters_shape {M S : CycleLetter ι h D} {Ks : ℕ}
    (hM : M.order = 2 ∧ M.slow = Ks ∧ M.positive = true)
    (hS : S.order = D ∧ S.slow = Ks ∧ S.positive = false) (w : List Bool) (i : Fin w.length) :
    (blockWordLetters M S w i).order = wordOrders D w i ∧
      (blockWordLetters M S w i).slow = wordSlow Ks w i ∧
      (blockWordLetters M S w i).positive = wordPositive w i := by
  unfold blockWordLetters wordOrders wordSlow wordPositive
  split_ifs
  · exact hS
  · exact hM

/-- The seam's order `k` of an allocation with old word `wo`. -/
def seamOrderK (D Kmax : ℕ) (wo : List Bool) : ℕ := Kmax + ∑ i, wordOrders D wo i + 2

/-- The seam's fast reserve of the allocation `(wo, wf)`. -/
def seamReserve (D Kmax pout Ks : ℕ) (wo wf : List Bool) : ℕ :=
  2 * (seamOrderK D Kmax wo + Kmax + pout + (∑ i, wordSlow Ks wo i + ∑ i, wordSlow Ks wf i) +
    ∑ i, wordOrders D wf i + 2) +
    max (Finset.univ.sup (wordOrders D wo)) (Finset.univ.sup (wordOrders D wf)) + 2

end Words

section Slots

variable {ι : Type*} [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The metric edges are diagonal of order `2`: constant slots descend along them. -/
theorem metricEdges_slots (K : ι → ℕ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (X₀ : Vec 2)
    (δ : ℝ) (x y : ι) (o : Finset.Icc 2 D) (hne : metricEdges (D := D) (h := h) G X₀ δ x y o ≠ []) :
    K x + o.1 ≤ K y + 2 := by
  unfold metricEdges at hne
  split_ifs at hne with hvu
  · obtain ⟨rfl, ho⟩ := hvu
    omega
  · exact absurd rfl hne

omit [DecidableEq ι] in
/-- The source edges are edges of the family: constant slots descend along them when the family
is descending. -/
theorem blockSourceEdges_slots {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    (K : ι → ℕ) (hdesc : F.IsDescending K) (S : Finset P) (actual : ∀ p, Ctx p)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (W : Set ℝ) (l : ℤ) (σ : ℝ) (yc : Vec 2)
    (e E ℓ2 : ℝ) (x y : ι) (o : Finset.Icc 2 D)
    (hne : blockSourceEdges F S actual hφ W l σ yc e E ℓ2 x y o ≠ []) :
    K x + o.1 ≤ K y + 2 := by
  unfold blockSourceEdges at hne
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨γ, -, hγ⟩ := List.mem_filterMap.1 hc
  split_ifs at hγ with hd
  exact (Nat.add_le_add_left hd _).trans (hdesc x y γ)

end Slots

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The scale ledger of the two-block window**.

The scales that enter the prices of the two-block theorem and of the seam, as powers of `E = ε_{m-1}`, from the
band-chain ledger (`bandChain_uniform_ledger`): the renewal radius `R = √(B τ'') ≤ C E^{1 + γ/2 + δ}`
(so `R/E ≤ C E^{γ/2 + δ}`), the cell length of a block `S = τ''/ℓ² ≥ C⁻¹ E^{-6δ}`, the Péclet
factor `√(B/ν) ≤ C E^{-qγ}`, the age `A τ'' ≤ C E^{2δ}`, the pulse length `ℓ²/τ ≤ C E^{4δ}`, and
the number of pulses of a block `τ''/τ = L² ≤ 81 E^{-2δ}`. Every level `2 ≤ m ≤ M` of the band
chain is covered, the terminal one included. -/

/-- The pulse count `L = 4 ⌈E^{-δ}⌉ + 1` is at most `9 E^{-δ}`. -/
theorem ocL_le_nine_rpow {α q : ℝ} {Λ m : ℕ} (hE0 : 0 < ocEpsilon q Λ (m - 1))
    (hE1 : ocEpsilon q Λ (m - 1) ≤ 1) (hδ : 0 ≤ ocDelta α q) :
    (ocL α q Λ m : ℝ) ≤ 9 * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) := by
  have hx : 1 ≤ ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hE0 hE1 (by linarith)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) by linarith)
  unfold ocL
  push_cast
  linarith

/-- **The scale ledger.** -/
theorem b1_scale_ledger {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ M : ℕ, 1 ≤ M →
      ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ → ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
        Real.sqrt (B * ocTauPP α q Λ m) ≤ C * ocEpsilon q Λ (m - 1) ^ (1 + ocC α q) ∧
        C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-(6 * ocDelta α q)) ≤
          ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 ∧
        Real.sqrt (B / ν) ≤ C * ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)) ∧
        ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ C * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) ∧
        ocEll q Λ m ν ^ 2 / ocTau α q Λ m ≤ C * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) ∧
        ocTauPP α q Λ m / ocTau α q Λ m ≤ C * ocEpsilon q Λ (m - 1) ^ (-(2 * ocDelta α q)) := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hL⟩ :=
    CycleReference.bandChain_uniform_ledger hα0 hα1 hs0 hs1 hq hζ
  have hδ := (Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  refine ⟨max C 81, le_trans hC (le_max_left _ _), Λ₀, hΛ₀,
    fun Λ hΛ M hM κ hκ m hm hmM ν B hν hB => ?_⟩
  obtain ⟨-, hlev⟩ := hL Λ hΛ M hM κ hκ
  obtain ⟨-, -, -, -, hRh, -, -, -, -, hell, hS, hPe, hA, -⟩ := hlev m hm hmM ν B hν hB
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  obtain ⟨hE0, hE1, -⟩ := Scales.epsilon_basic (q := q) (m := m - 1) hq.1 h128
  have hCC : C ≤ max C 81 := le_max_left _ _
  have hpow (x : ℝ) : 0 ≤ ocEpsilon q Λ (m - 1) ^ x := Real.rpow_nonneg hE0.le x
  have hτ := Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) (by omega : 1 ≤ Λ)
  refine ⟨hRh.2.trans (mul_le_mul_of_nonneg_right hCC (hpow _)), ?_,
    hPe.trans (mul_le_mul_of_nonneg_right hCC (hpow _)),
    hA.trans (mul_le_mul_of_nonneg_right hCC (hpow _)),
    hell.trans (mul_le_mul_of_nonneg_right hCC (hpow _)), ?_⟩
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ (hpow _)) hS
    exact inv_anti₀ (by linarith) hCC
  · have hratio : ocTauPP α q Λ m / ocTau α q Λ m = (ocL α q Λ m : ℝ) ^ 2 := by
      have hL0 : (0 : ℝ) < ocL α q Λ m := by
        have : 0 < ocL α q Λ m := by unfold ocL; omega
        exact_mod_cast this
      have hT := (Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m)
        (by omega : 1 ≤ Λ)).ne'
      unfold ocTau
      field_simp
    rw [hratio]
    have h9 := ocL_le_nine_rpow (α := α) (q := q) (Λ := Λ) (m := m) hE0 hE1 hδ.le
    have hL0 : (0 : ℝ) ≤ ocL α q Λ m := Nat.cast_nonneg _
    calc (ocL α q Λ m : ℝ) ^ 2 ≤ (9 * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)) ^ 2 :=
          pow_le_pow_left₀ hL0 h9 2
      _ = 81 * ocEpsilon q Λ (m - 1) ^ (-(2 * ocDelta α q)) := by
          rw [mul_pow, ← Real.rpow_natCast (ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)) 2,
            ← Real.rpow_mul hE0.le]
          norm_num
          ring_nf
      _ ≤ max C 81 * ocEpsilon q Λ (m - 1) ^ (-(2 * ocDelta α q)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (hpow _)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Ingredient statements of the route to `cycle_joint`**.

The statement `cycle_joint` is reduced to three analytic statements and one algebraic normalization:

* `RawJointStatement` — the analytic core: for EVERY family satisfying the premises of
  `cycle_joint` (with the duration `C_H = 2`), a single linear operator `Tm` on the whole
  family whose mass-weighted model bound (`IsRawMassModel`; `IsRawMassL2` with constant
  `1 + C_P E^P` when the family has no edges) and mass-weighted physical error
  (`IsRawMassError`) hold at the common renewal endpoint `t_p = (l₀ + 3/2) τ''`. No block or
  path structure is asserted: the model and the error are clauses about the SAME `Tm`.
* `PathReductionStatement` — the core, applied to every source path of the family (a chain
  family with masses adapted to the edge entries), yields the triangular blocks of `cycle_joint`
  with entrywise bounds `C (A^h)_{vu}` and the joint error. This is where the entrywise path
  sums of the joint model bound come from.
* `MeanConservationStatement` — torus solutions with a stream drift conserve the cell mean.
* `NormalizationStatement` — the mean projection `Π₀ + Q₀ 𝐏 Q₀` turns raw triangular blocks
  into blocks that fix constants exactly (in place of a constant-matrix inverse; it uses only
  the exact mean conservation).

Universes: `u v w x` are those of `ι`, `h`, `P'`, `Ctx` in `cycle_joint`. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- The cell mean `∫_{[0,1]²} f` of a periodic carrier. -/
noncomputable def torusMean {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} (f : TorusHk K E) : E :=
  ∫ x in AVenhance.unitCube, f.toFunction.jet (valueIndex2 K) x

section Predicates

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The first four clauses of `IsJointModel` (path support, diagonal `L²` bound, diagonal and
source jets): the model before the normalization of constants. -/
def IsRawTriangularModel [DecidableEq ι] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (K : ι → ℕ) (Mout H : ℕ) (F : ChartedFamily ι h D P Ctx) (A : Matrix ι ι ℝ)
    (E Pacc ρm C CP : ℝ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v)) : Prop :=
  (∀ h', 1 ≤ h' → h' ≤ H → ∀ v u, ¬ HasEdgePath F h' u v → Pg h' v u = 0) ∧
  (∀ v f, torusHkNorm 1 (Nat.zero_le _) (Pd v f) ≤
    (1 + CP * E ^ Pacc) * torusHkNorm 1 (le_refl 0) f) ∧
  (∀ v f, torusHkNorm ρm (le_max_left Mout (K v)) (Pd v f) ≤ C * torusHkNorm 1 (le_refl 0) f) ∧
  (∀ h', 1 ≤ h' → h' ≤ H → ∀ v u f, torusHkNorm ρm (le_max_left Mout (K v)) (Pg h' v u f) ≤
    C * (A ^ h') v u * torusHkNorm 1 (le_refl 0) f)

/-- Mass-weighted model bound of one linear operator `Tm` on the whole family: scaled jets at
radius `ρm` through order `Mout` with constant `C` on arbitrary `L²` input. -/
def IsRawMassModel (π : ι → ℝ) (K : ι → ℕ) (Mout : ℕ) (ρm C : ℝ)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v))) : Prop :=
  ∀ f, ∑ v, (π v)⁻¹ * torusHkNorm ρm (le_max_left Mout (K v)) (Tm f v) ^ 2 ≤
    C ^ 2 * ∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (f u) ^ 2

/-- The `L²` near-contraction `δ` of `Tm` (used for edge-free families, where it is the
order-zero specialization of the scalar diagonal). -/
def IsRawMassL2 (π : ι → ℝ) (K : ι → ℕ) (Mout : ℕ) (δ : ℝ)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v))) : Prop :=
  ∀ f, ∑ v, (π v)⁻¹ * torusHkNorm 1 (Nat.zero_le _) (Tm f v) ^ 2 ≤
    δ ^ 2 * ∑ u, (π u)⁻¹ * torusHkNorm 1 (le_refl 0) (f u) ^ 2

/-- The physical error of `IsJointError`, for one linear operator `Tm` on the whole family. -/
def IsRawMassError (π : ι → ℝ) (K : ι → ℕ) (Mout D : ℕ) (ν tS tp ρs ρold E Pacc CP : ℝ)
    (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v))) : Prop :=
  ∀ (f : ∀ v, TorusHk (K v) (h v)) (Fv : ι → ℝ),
    (∀ v, torusHkNorm ρold (le_refl (K v)) (f v) ≤ Fv v) →
    ∀ (u : ∀ v, ℝ → TorusHk (K v) (h v)) (w : ∀ v, ℝ → TorusHk (K v + 1) (h v)),
      IsCoupledWeakSolutionTorus ν tS tp b D K A f (fun _ _ => 0) (fun _ _ => 0) u w →
      Real.sqrt (massNormSq (E := h) (K := K) ρs π
          (fun v => (u v tp - truncateTorusHk (le_max_right Mout (K v))
            (Tm (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v)).val)) ≤
        CP * E ^ Pacc * Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2)

end Predicates

/-- The statement of `cycle_joint`, verbatim (named universes, unused binders
underscored). -/
def CycleJointStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (Mout H D Kmax : ℕ), 2 ≤ D →
      ∃ (Ks Ls Jm qJ Jchart : ℕ) (CH : ℝ), 0 < CH ∧ CH = 2 ∧
      ∀ (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad : ℕ), 0 < cMol → 0 < cOld →
      ∃ (C CP c : ℝ) (mStar : ℕ), 0 < c ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (K : ι → ℕ) (_hK : ∀ x, K x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmStar : mStar ≤ m) (_hmM : m ≤ M') (ν B : ℝ)
        (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζ Φ hφ ν B tS (tS + CH * ocTauPP α q Λ m) (ocRhoMol α q Λ m cMol ν) g g₀ a B₀
          lam Cb qJ Kmax CG l₀ P y₀)
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hwmeas : ∀ p, Measurable (F.weight p))
        (_hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ
          tS (tS + CH * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P F)
        (actual : ∀ p, Ctx p) (_hdepth : F.HasDepthAtMost H) (_hdesc : F.IsDescending K)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (_hcover : Set.Icc tS (tS + CH * ocTauPP α q Λ m) ⊆ ⋃ p, (F.piece p).output)
        (_hmeas : F.IsTimeMeasurable)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (_hΘ₀ : 0 ≤ Θ) (_hΘ₁ : Θ ≤ 1)
        (_htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS (tS + CH * ocTauPP α q Λ m))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (_hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tS (tS + CH * ocTauPP α q Λ m)))
        (T : F.Atlas)
        (_hTcons : T.IsConsecutiveClosed (Set.Icc tS (tS + CH * ocTauPP α q Λ m)))
        (_hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m)
          (Set.Icc tS (tS + CH * ocTauPP α q Λ m)))
        (_hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)))
        (ρold : ℝ)
        (_hρold : cOld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) ≤ ρold ∧
          ρold ≤ COld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q))
        (_hρrat : ocRhoMol α q Λ m cMol ν / ρold ≤
          Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))),
      ∃ (tp : ℝ) (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
        (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v)),
        tp ∈ Set.Ioc tS (tS + CH * ocTauPP α q Λ m) ∧ tp ∈ ocQuietTimes α q Λ ζ m ∧
        Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆ ocQuietTimes α q Λ ζ m ∧
        ∀ (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
          (_henv : IsEnvelope F π K
            (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + CH * ocTauPP α q Λ m))) ν
            (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
            (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm)
          (_hpointwise : IsPointwiseMolecularEnvelope F π K
            (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + CH * ocTauPP α q Λ m))) ν
            (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
            Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u)),
          IsJointModel π K Mout H F A Θ (ocEpsilon q Λ (m - 1)) Pacc
            (c * Real.sqrt (B * ocTauPP α q Λ m)) C CP Pd Pg ∧
          IsJointError π K Mout H D ν tS tp (ocRhoMol α q Λ m cMol ν) ρold
            (ocEpsilon q Λ (m - 1)) Pacc CP (streamVel (Φ m))
            (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) Pd Pg

/-- **Analytic core.** `cycle_joint` with the duration `C_H = 2`, the endpoint fixed at the renewal
`t_p = (l₀ + 3/2) τ''` (the first renewal after `t_S` plus `τ''`) and the triangular operator
replaced by one linear operator `Tm` on the whole family with mass-weighted model bounds and the
physical error of the same `Tm`. The chart and molecular reserves exceed `Kmax + D + 2` (so that the
actual torus solutions of every restricted family exist and are unique); the constants are
nonnegative. The proof: patch models from finite words and the seam, weighted Taylor comparison,
spatial and image sums. -/
def RawJointStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (Mout H D Kmax : ℕ), 2 ≤ D →
      ∃ (Ks Ls Jm qJ Jchart : ℕ), Kmax + D + 2 ≤ Jchart ∧ Kmax + D + 2 ≤ Jm ∧
      ∀ (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad : ℕ),
        0 < cMol → 0 < cOld →
      ∃ (C CP c : ℝ) (mStar : ℕ), 0 < c ∧ 0 ≤ C ∧ 0 ≤ CP ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x) (K : ι → ℕ) (_hK : ∀ x, K x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmStar : mStar ≤ m) (_hmM : m ≤ M') (ν B : ℝ)
        (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζ Φ hφ ν B tS (tS + 2 * ocTauPP α q Λ m)
          (ocRhoMol α q Λ m cMol ν) g g₀ a B₀ lam Cb qJ Kmax CG l₀ P y₀)
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hwmeas : ∀ p, Measurable (F.weight p))
        (_hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ
          tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P F)
        (actual : ∀ p, Ctx p) (_hdepth : F.HasDepthAtMost H) (_hdesc : F.IsDescending K)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (_hcover : Set.Icc tS (tS + 2 * ocTauPP α q Λ m) ⊆ ⋃ p, (F.piece p).output)
        (_hmeas : F.IsTimeMeasurable)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (_hΘ₀ : 0 ≤ Θ) (_hΘ₁ : Θ ≤ 1)
        (_henv : IsEnvelope F π K
          (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
          (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm)
        (_hpointwise : IsPointwiseMolecularEnvelope F π K
          (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
          Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u))
        (_htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (_hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
        (T : F.Atlas)
        (_hTcons : T.IsConsecutiveClosed (Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
        (_hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m)
          (Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
        (_hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)))
        (ρold : ℝ)
        (_hρold : cOld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) ≤ ρold ∧
          ρold ≤ COld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q))
        (_hρrat : ocRhoMol α q Λ m cMol ν / ρold ≤
          Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))),
      ∃ Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v)),
        IsRawMassModel π K Mout (c * Real.sqrt (B * ocTauPP α q Λ m)) C Tm ∧
        ((∀ v u, IsEmpty (F.Γ v u)) →
          IsRawMassL2 π K Mout (1 + CP * ocEpsilon q Λ (m - 1) ^ Pacc) Tm) ∧
        IsRawMassError π K Mout D ν tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m)
          (ocRhoMol α q Λ m cMol ν) ρold (ocEpsilon q Λ (m - 1)) Pacc CP (streamVel (Φ m))
          (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) Tm

/-- **The analytic core at an abstract radius**: the
core `RawJointStatement` with the cascade radius `ocRhoMol α q Λ m cMol ν` replaced by a radius
`r` in the window cover, the envelopes and the error clause, and the prepared radius `ρold`
constrained only by `0 < ρold`, `ρold ≤ COld √(B τ'')` (the patch mesh bound) and the ratio
`r / ρold ≤ Crat ε_{m−1}^{−qδ}`. `RawJointStatement` is its instance at `r = ocRhoMol` with the
cascade's `ρold`. -/
def RawJointGenStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (Mout H D Kmax : ℕ), 2 ≤ D →
      ∃ (Ks Ls Jm qJ Jchart : ℕ), Kmax + D + 2 ≤ Jchart ∧ Kmax + D + 2 ≤ Jm ∧
      ∀ (Ca Cth Cb COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad : ℕ),
      ∃ (C CP c : ℝ) (mStar : ℕ), 0 < c ∧ 0 ≤ C ∧ 0 ≤ CP ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x) (K : ι → ℕ) (_hK : ∀ x, K x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmStar : mStar ≤ m) (_hmM : m ≤ M') (ν B : ℝ)
        (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (r : ℝ)
        (_cov : IsWindowCover α q Λ m ζ Φ hφ ν B tS (tS + 2 * ocTauPP α q Λ m)
          r g g₀ a B₀ lam Cb qJ Kmax CG l₀ P y₀)
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hwmeas : ∀ p, Measurable (F.weight p))
        (_hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ
          tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P F)
        (actual : ∀ p, Ctx p) (_hdepth : F.HasDepthAtMost H) (_hdesc : F.IsDescending K)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (_hcover : Set.Icc tS (tS + 2 * ocTauPP α q Λ m) ⊆ ⋃ p, (F.piece p).output)
        (_hmeas : F.IsTimeMeasurable)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (_hΘ₀ : 0 ≤ Θ) (_hΘ₁ : Θ ≤ 1)
        (_henv : IsEnvelope F π K
          (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) r
          (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm)
        (_hpointwise : IsPointwiseMolecularEnvelope F π K
          (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) r
          Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u))
        (_htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (_hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
        (T : F.Atlas)
        (_hTcons : T.IsConsecutiveClosed (Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
        (_hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m)
          (Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
        (_hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)))
        (ρold : ℝ)
        (_hρpos : 0 < ρold) (_hρR : ρold ≤ COld * Real.sqrt (B * ocTauPP α q Λ m))
        (_hρrat : r / ρold ≤
          Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))),
      ∃ Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v)),
        IsRawMassModel π K Mout (c * Real.sqrt (B * ocTauPP α q Λ m)) C Tm ∧
        ((∀ v u, IsEmpty (F.Γ v u)) →
          IsRawMassL2 π K Mout (1 + CP * ocEpsilon q Λ (m - 1) ^ Pacc) Tm) ∧
        IsRawMassError π K Mout D ν tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m)
          r ρold (ocEpsilon q Λ (m - 1)) Pacc CP (streamVel (Φ m))
          (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) Tm

/-- `cycle_joint` with `IsJointModel` replaced by `IsRawTriangularModel` (no constants clause,
no total mass clause); the binders are those of `cycle_joint` verbatim. -/
def TriangularRawStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (Mout H D Kmax : ℕ), 2 ≤ D →
      ∃ (Ks Ls Jm qJ Jchart : ℕ) (CH : ℝ), 0 < CH ∧ CH = 2 ∧
      ∀ (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad : ℕ),
        0 < cMol → 0 < cOld →
      ∃ (C CP c : ℝ) (mStar : ℕ), 0 < c ∧ 0 ≤ C ∧ 0 ≤ CP ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (K : ι → ℕ) (_hK : ∀ x, K x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmStar : mStar ≤ m) (_hmM : m ≤ M') (ν B : ℝ)
        (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζ Φ hφ ν B tS (tS + CH * ocTauPP α q Λ m)
          (ocRhoMol α q Λ m cMol ν) g g₀ a B₀ lam Cb qJ Kmax CG l₀ P y₀)
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hwmeas : ∀ p, Measurable (F.weight p))
        (_hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ
          tS (tS + CH * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P F)
        (actual : ∀ p, Ctx p) (_hdepth : F.HasDepthAtMost H) (_hdesc : F.IsDescending K)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (_hcover : Set.Icc tS (tS + CH * ocTauPP α q Λ m) ⊆ ⋃ p, (F.piece p).output)
        (_hmeas : F.IsTimeMeasurable)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (_hΘ₀ : 0 ≤ Θ) (_hΘ₁ : Θ ≤ 1)
        (_htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS (tS + CH * ocTauPP α q Λ m))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (_hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tS (tS + CH * ocTauPP α q Λ m)))
        (T : F.Atlas)
        (_hTcons : T.IsConsecutiveClosed (Set.Icc tS (tS + CH * ocTauPP α q Λ m)))
        (_hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m)
          (Set.Icc tS (tS + CH * ocTauPP α q Λ m)))
        (_hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)))
        (ρold : ℝ)
        (_hρold : cOld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) ≤ ρold ∧
          ρold ≤ COld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q))
        (_hρrat : ocRhoMol α q Λ m cMol ν / ρold ≤
          Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))),
      ∃ (tp : ℝ) (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
        (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v)),
        tp ∈ Set.Ioc tS (tS + CH * ocTauPP α q Λ m) ∧ tp ∈ ocQuietTimes α q Λ ζ m ∧
        Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆ ocQuietTimes α q Λ ζ m ∧
        ∀ (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
          (_henv : IsEnvelope F π K
            (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + CH * ocTauPP α q Λ m))) ν
            (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
            (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm)
          (_hpointwise : IsPointwiseMolecularEnvelope F π K
            (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + CH * ocTauPP α q Λ m))) ν
            (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
            Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u)),
          IsRawTriangularModel K Mout H F A (ocEpsilon q Λ (m - 1)) Pacc
            (c * Real.sqrt (B * ocTauPP α q Λ m)) C CP Pd Pg ∧
          IsJointError π K Mout H D ν tS tp (ocRhoMol α q Λ m cMol ν) ρold
            (ocEpsilon q Λ (m - 1)) Pacc CP (streamVel (Φ m))
            (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) Pd Pg

/-- **Path reduction.** The core, applied to the source paths of the family (each path a
chain family `Fin (n+1)` with the restricted constituents and masses adapted to its edge entries;
`Θ = 1` on a path and `Θ = 0` on a trivial path), gives the triangular blocks: `Pd v` is the core
operator of the trivial path at `v`, `Pg n v u` the sum over the paths `u → v` of length `n` of
the corner block of the path operator. Entrywise bounds `C (A^n)_{vu}` are the path sums;
the physical error is the sum over paths of the path errors, by
linearity and uniqueness (path expansion of the actual solution) and the mass Schur inequality.
The core is used at index universe `0` (paths are indexed by
`Fin (n+1)`). -/
def PathReductionStatement : Prop :=
  RawJointStatement.{0, v, w, x} → TriangularRawStatement.{u, v, w, x}

/-- **Mean conservation.** A torus solution of the coupled system with a stream drift and
zero forcing keeps the cell mean of its datum (test the weak identity with a constant vector;
the transport term vanishes by periodicity and incompressibility). -/
def MeanConservationStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (φ : ℝ → Vec 2 → ℝ) (_hφ : IsAdmissibleStream φ) (ν t₀ t₁ : ℝ) (D : ℕ) (K : ι → ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (f : ∀ i, TorusHk (K i) (h i))
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
    IsCoupledWeakSolutionTorus ν t₀ t₁ (streamVel φ) D K A f (fun _ _ => 0) (fun _ _ => 0) u w →
    ∀ i, ∀ t ∈ Set.Icc t₀ t₁, torusMean (u i t) = torusMean (f i)

/-- **Normalization of constants (algebraic).** Raw triangular blocks with the joint error, for a
solution class that conserves cell means, become blocks fixing constants:
`Pd' = Π₀ + Q₀ Pd Q₀`, `Pg' = Q₀ Pg Q₀`, with constants `jointModelConstant (1 + 2C) Cth H` and
`4 CP`. -/
def NormalizationStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D' : ℕ} {P' : Type w} {Ctx : P' → Type x}
    (F : ChartedFamily ι h D' P' Ctx) (K : ι → ℕ)
    (Mout H D : ℕ) (A : Matrix ι ι ℝ)
    (Θ E Pacc ρm C CP Cth : ℝ) (_hC : 0 ≤ C) (_hCP : 0 ≤ CP) (_hE : 0 ≤ E) (_hCth : 0 ≤ Cth)
    (_hΘ₀ : 0 ≤ Θ) (_hΘ₁ : Θ ≤ 1)
    (ν tS tp ρs ρold : ℝ) (b : ℝ → Vec 2 → Vec 2)
    (Acoef : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v)),
    ∃ (Pd' : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
      (Pg' : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v)),
    ∀ (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (_hA : ∀ v u, 0 ≤ A v u)
      (_hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * A v u ≤ Cth * Θ)
      (_hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * A v u ≤ Cth * Θ),
      IsRawTriangularModel K Mout H F A E Pacc ρm C CP Pd Pg →
      IsJointError π K Mout H D ν tS tp ρs ρold E Pacc CP b Acoef Pd Pg →
      (∀ (f : ∀ i, TorusHk (K i) (h i)) (u : ∀ i, ℝ → TorusHk (K i) (h i))
          (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
        IsCoupledWeakSolutionTorus ν tS tp b D K Acoef f (fun _ _ => 0) (fun _ _ => 0) u w →
        ∀ i, torusMean (u i tp) = torusMean (f i)) →
      IsJointModel π K Mout H F A Θ E Pacc ρm (jointModelConstant (1 + 2 * C) Cth H) (4 * CP)
        Pd' Pg' ∧
      IsJointError π K Mout H D ν tS tp ρs ρold E Pacc (4 * CP) b Acoef Pd' Pg'

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Conditional assembly of `cycle_joint`**.

`cycle_joint_of_ingredients` proves the exact statement of
`cycle_joint` from the four ingredient propositions:

* `RawJointStatement` (the analytic core, reduced further at level B);
* `PathReductionStatement`;
* `MeanConservationStatement`;
* `NormalizationStatement` (algebraic).

The common witnesses: the core gives ONE operator per family, from which the path reduction
builds the blocks `Pd`, `Pg` and the error of those same blocks; the normalization keeps the
witnesses common. The constants `C' = jointModelConstant (1 + 2C) (max Cth 0) H`, `CP' = 4 CP`
are chosen before the family, as the statement requires. The admissibility of the stream `Φ m`
comes from `IsOCStreamSeq` at index `m + 1`. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- **`cycle_joint` from its ingredients.** `CycleJointStatement` is the type of `cycle_joint`
verbatim, with the universes named explicitly. -/
theorem cycle_joint_of_ingredients
    (hcore : RawJointStatement.{0, v, w, x}) (hpath : PathReductionStatement.{u, v, w, x})
    (hmean : MeanConservationStatement.{u, v}) (hnorm : NormalizationStatement.{u, v, w, x}) :
    CycleJointStatement.{u, v, w, x} := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, hΛ⟩ := hpath hcore α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛΛ => ?_⟩
  obtain ⟨g₀, hg₀, hP⟩ := hΛ Λ hΛΛ
  refine ⟨g₀, hg₀, fun Pacc hPacc Mout H D Kmax hD => ?_⟩
  obtain ⟨Ks, Ls, Jm, qJ, Jchart, CH, hCH, hCH2, hcst⟩ := hP Pacc hPacc Mout H D Kmax hD
  refine ⟨Ks, Ls, Jm, qJ, Jchart, CH, hCH, hCH2,
    fun Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad hcMol hcOld => ?_⟩
  obtain ⟨C, CP, c, mStar, hc, hC, hCP, hfam⟩ :=
    hcst Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad hcMol hcOld
  refine ⟨jointModelConstant (1 + 2 * C) (max Cth 0) H, 4 * CP, c, mStar, hc, ?_⟩
  intro ι _ _ h _ _ _ _ _ _ K hK Φ hΦ M' κ hband m hm2 hmStar hmM ν B hν hB hφ
    tS g a B₀ lam l₀ P y₀ cov P' Ctx F hwmeas hprep actual hdepth hdesc htorus hcover hmeas
    A Θ hΘ₀ hΘ₁ htrans hquiet T hTcons hTcov hTq ρold hρold hρrat
  obtain ⟨tp, Pd, Pg, htpI, htpQ, hquietMargin, hall⟩ := hfam K hK Φ hΦ M' κ hband m hm2 hmStar
    hmM ν B hν hB hφ tS g a B₀ lam l₀ P y₀ cov F hwmeas hprep actual hdepth hdesc htorus hcover
    hmeas A Θ hΘ₀ hΘ₁ htrans hquiet T hTcons hTcov hTq ρold hρold hρrat
  have hE : 0 ≤ ocEpsilon q Λ (m - 1) :=
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)).le
  obtain ⟨hadm, -⟩ := hΦ.2 (m + 1) (by omega)
  rw [Nat.add_sub_cancel] at hadm
  have hmean' : ∀ (f : ∀ i, TorusHk (K i) (h i)) (u : ∀ i, ℝ → TorusHk (K i) (h i))
      (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsCoupledWeakSolutionTorus ν tS tp (streamVel (Φ m)) D K
        (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) f
        (fun _ _ => 0) (fun _ _ => 0) u w →
      ∀ i, torusMean (u i tp) = torusMean (f i) := fun f u w hs i =>
    hmean (Φ m) hadm ν tS tp D K _ f u w hs i tp ⟨htpI.1.le, le_rfl⟩
  obtain ⟨Pd', Pg', hnormAll⟩ := hnorm F K Mout H D A Θ (ocEpsilon q Λ (m - 1)) Pacc
    (c * Real.sqrt (B * ocTauPP α q Λ m)) C CP (max Cth 0) hC hCP hE (le_max_right _ _)
    hΘ₀ hΘ₁ ν tS tp (ocRhoMol α q Λ m cMol ν) ρold (streamVel (Φ m))
    (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) Pd Pg
  refine ⟨tp, Pd', Pg', htpI, htpQ, hquietMargin, fun π hπ henv hpointwise => ?_⟩
  obtain ⟨hraw, herr⟩ := hall π hπ henv hpointwise
  have hA : ∀ v u, 0 ≤ A v u := fun v u =>
    (mul_nonneg_iff_of_pos_left (Real.sqrt_pos.2 (div_pos (hπ u) (hπ v)))).1
      (henv.nonneg v u)
  have hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * A v u ≤ max Cth 0 * Θ := fun v =>
    (henv.row_sum v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hΘ₀)
  have hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * A v u ≤ max Cth 0 * Θ := fun u =>
    (henv.col_sum u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hΘ₀)
  exact hnormAll π hπ hA hrow hcol hraw herr hmean'

end AVRegularity.CycleJointProofs.Assembly
end
end
