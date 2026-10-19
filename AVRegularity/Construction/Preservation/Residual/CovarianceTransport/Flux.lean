-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfIngredients
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
public import AVRegularity.Construction.StageSuccessor.Assembly.SuccessorExistsOfIngredients
public import AVRegularity.Construction.Residual.Presentation.ProofMeanFluxSplit
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleReference.TorusChartEquation
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.ReadoutStrongCore
import AVRegularity.Applications.Transfer.TubeK
import AVenhance.Infra.Construction.StreamAdmissible

section
section
/-! Assembly of covariance transport; the conclusion is the original residual statement itself.

The uniform prefix is shared by a predicate on one concrete frame. The three long weak
identities are not copied: they are instances of `Frame.weakEquation`. Derivative witnesses
are selected before all tests. At zero Sobolev output order the same frame and scalar weak
calculus apply. Empty component families make the component clauses vacuous. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.FullLift

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The actual data used by the local covariance argument. No time regularity is presumed. -/
structure Frame (D : OCData) (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) where
  G : GenStage D hr Dm bw j₀
  G' : GenStage D hr Dm bw j₀
  Gr : GenStage D hr Dm bw j₀
  Mn : SuccMenu
  P : ProvParams
  seedK : ℕ → KernelSpec
  freshK : ℕ → KernelSpec
  φ₀ : Vec 2 → ℝ
  m : ℕ
  H : ℕ
  J : ℕ
  N : ℕ
  p : ℕ
  depth : ℕ
  Naux : ℕ
  sX : ℕ
  sZ : ℕ
  η₀ : ℝ
  tp : ℝ
  tf : ℝ
  Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root)
  CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)
  PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root)
  aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root
  aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root
  aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root
  û : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root)
  lift : IsMenuLiftedField Mn G Gr m p Naux N depth sX sZ η₀ tp tf Y CcT PZ aRep û
  readout : ∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep
    (succReadout m (D.eps (m - 1)) η₀ Naux (fun v' => Y v' t) v) (fun x => aZ t x v) Naux
  retained : ∀ v', ∀ t ∈ Set.Icc tp tf, IsClassicalRep (Y v' t) (fun x => aY t x v') Naux

namespace Frame
variable (F : Frame D hr Dm bw j₀)

abbrev Field := ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root
abbrev Flux := ∀ v : CompIn F.G.comps, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v.1.root)

def uh : F.Field := menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep

def upsilon : F.Flux := upsilonFlux F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.H F.J
  (D.eps (F.m - 1)) F.η₀ F.aZ F.aY

def mean : F.Flux := fun v t x => toFluxL (menuMeanFluxF F.Mn F.G F.m F.N F.p F.depth F.CcT
  F.aZ F.upsilon v t x)

def meanDiv : F.Field := fun t x v => divE (fun y => WithLp.ofLp (F.mean v t y)) x

def readFlux : F.Flux := fun v t x => -(toFluxL (covPolyQ (menuCovPrimitive D F.Mn F.m t) F.p
  (fun y => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y) x) + F.upsilon v t x)

def macroFluxField : F.Flux := fun v t x => toFluxL (menuMacroFlux F.Mn F.G F.m F.N F.depth F.CcT F.aRep v t x)

def plain : F.Flux := coeffFluxOn F.P F.seedK F.freshK F.φ₀ F.G .plain F.uh

def kernel : F.Flux := coeffFluxOn F.P F.seedK F.freshK F.φ₀ F.G .kernel F.uh

def fine : F.Flux := fineFluxF F.P F.seedK F.freshK F.φ₀ F.G F.uh

def liftedMean : F.Field := menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.meanDiv

def physSource (dRep dUh : F.Field) : F.Field := fun t x v => F.liftedMean t x v +
  menuPhysRes F.Mn F.P F.seedK F.freshK F.φ₀ F.G F.m F.N F.depth F.CcT F.aRep dRep dUh v t x

/-- One common convention for all weak equations, including every integrability conjunct. -/
def weakEquation (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) (a : F.Field)
    (A B : F.Flux) (f : F.Field) : Prop :=
  ∀ w : CompIn F.G.comps, ∀ t ∈ Set.Icc F.tp F.tf, ∀ φ : Vec 2 → hr w.1.root,
    ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν F.tp t v
      (fun x => a t x w) (fun x => a F.tp x w) φ (fun k x => gradE φ x k)
      (fun s k x => gradE (fun y => a s y w) x k)
      (A w) (B w) (fun s x => f s x w)

def readoutWeak : Prop := F.weakEquation (D.κ (F.m - 1))
  (streamVel (D.Φ (F.m - 1))) F.aZ 0 F.readFlux 0

def macroWeak : Prop := F.weakEquation (D.κ (F.m - 1))
  (streamVel (D.Φ (F.m - 1))) F.aRep F.macroFluxField F.mean 0

def plainWeak (dRep dUh : F.Field) : Prop := F.weakEquation (D.κ F.m)
  (streamVel (D.Φ F.m)) F.uh F.plain 0 (F.physSource dRep dUh)

def kernelWeak (dRep dUh : F.Field) : Prop := F.weakEquation (D.κ F.m)
  (streamVel (D.Φ F.m)) F.uh F.kernel F.fine (F.physSource dRep dUh)

/-- The classical coarse operator with the selected derivative representative. -/
def coarseRes (dZ : F.Field) : F.Field := fun t x v => dZ t x v +
  ∑ k : Fin 2, streamVel (D.Φ (F.m - 1)) t x k • gradE (fun y => F.aZ t y v) x k -
  divE (fun y => D.κ (F.m - 1) • gradE (fun y' => F.aZ t y' v) y) x

def macroResidual (dRep : F.Field) : F.Field := menuMacroRes F.Mn F.G F.m F.N F.depth F.CcT F.aRep dRep

/-- The last term of the finite temporal conjugation, as a flux. -/
def lastFlux : F.Flux := fun v t x => toFluxL (fun k => ∑ l : Fin 2,
  (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t - D.κ (F.m - 1) • 1) k l •
    gradE (fun y => ((F.p.factorial : ℝ)⁻¹) •
      (covOperator (menuCovPrimitive D F.Mn F.m t))^[F.p] (fun y' => F.aZ t y' v) y) x l)

/-- The precise temporal product formula, before substituting the readout equation. -/
def TemporalProduct (dZ dRep : F.Field) : Prop :=
  ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf), ∀ x v,
    F.macroResidual dRep t x v = menuCovPRep F.Mn D F.m F.p (F.coarseRes dZ) t x v +
      divE (fun y => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y) x -
      divE (fun y => WithLp.ofLp (F.lastFlux v t y)) x

/-- The classical strong readout equation, on one common set of times. -/
def StrongReadout (dZ : F.Field) : Prop :=
  ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf), ∀ x v,
    F.coarseRes dZ t x v = divE (fun y => WithLp.ofLp (F.readFlux v t y)) x

/-- The strong mean equation transported by the complete lift in the residual definition. -/
def StrongMean (dRep : F.Field) : Prop :=
  ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf), ∀ x v,
    F.macroResidual dRep t x v = F.meanDiv t x v

end Frame

/-- Spatial regularity and an integrable uniform spatial bound for a literal time-dependent field. -/
structure ClassicalWindowBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (a b : ℝ) (K : ℕ) (f : ℝ → Vec 2 → E) : Prop where
  smooth : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (f t)
  periodic : ∀ t ∈ Set.Icc a b, IsZ2Periodic (f t)
  measurable : Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc a b} => f z.1.1 z.1.2)
  bound : ∀ n ≤ K, ∀ w : DerivativeWord2 n, ∃ B : ℝ → ℝ,
    IntegrableOn B (Set.Icc a b) ∧ ∀ t ∈ Set.Icc a b, ∀ x ∈ AVenhance.unitCube,
      ‖orderedDerivative w (f t) x‖ ≤ B t

/-- Genuine absolute continuity of the retained jets, with a single derivative field.
At order zero the value clause remains meaningful; differentiated clauses require two reserves. -/
structure ClassicalTimeCurve (F : Frame D hr Dm bw j₀) (K : ℕ) (f df : F.Field) : Prop where
  field : ∀ v, ClassicalWindowBound F.tp F.tf (K - 2) (fun t x => f t x v)
  uniform : ∀ v, ∀ n, n + 2 ≤ K → ∀ w : DerivativeWord2 n, ∃ B : ℝ,
    ∀ t ∈ Set.Icc F.tp F.tf, ∀ x ∈ AVenhance.unitCube,
      ‖orderedDerivative w (fun y => f t y v) x‖ ≤ B
  derivative : IsTimeDerivRep (Set.Icc F.tp F.tf) f df
  derivativeBound : ∀ v, ClassicalWindowBound F.tp F.tf (K - 4) (fun t x => df t x v)
  primitive : ∀ n, n + 4 ≤ K → ∀ w : DerivativeWord2 n, ∀ v, ∀ t ∈ Set.Icc F.tp F.tf, ∀ x,
    orderedDerivative w (fun y => f t y v) x - orderedDerivative w (fun y => f F.tp y v) x =
      ∫ s in Set.Ioc F.tp t, orderedDerivative w (fun y => df s y v) x
  valuePrimitive : ∀ v, ∀ t ∈ Set.Icc F.tp F.tf, ∀ x,
    f t x v - f F.tp x v = ∫ s in Set.Ioc F.tp t, df s x v

/-- Analytic input, not a weak residual identity: regularity, time primitives, and finite budgets. -/
structure Regularity (F : Frame D hr Dm bw j₀) (dZ dRep dUh : F.Field) : Prop where
  reserve : 4 * F.p + 4 ≤ F.Naux
  clock_nonzero : D.cellScaleSq F.m ≠ 0
  covarianceDerivative : ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf), ∀ i j,
    HasDerivAt (fun r => menuCovPrimitive D F.Mn F.m r i j)
      ((ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t - D.κ (F.m - 1) • 1) i j) t
  covarianceSymmetric : ∀ t (i j : Fin 2), menuCovPrimitive D F.Mn F.m t i j = menuCovPrimitive D F.Mn F.m t j i
  readout : ClassicalTimeCurve F F.Naux F.aZ dZ
  prepared : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep
  lifted : ClassicalTimeCurve F (Dm + 4) F.uh dUh
  kernelFields : ∀ v u (γ : F.G.fam.Γ v u), ∀ t ∈ Set.Icc F.tp F.tf,
    ContDiff ℝ ((Dm + 1 : ℕ) : ℕ∞)
      ((F.G.kernelOf F.P F.seedK F.freshK v u γ).applyClassical F.φ₀ t (fun y => F.uh t y u))
  coarseDrift : ClassicalWindowBound F.tp F.tf 1 (streamVel (D.Φ (F.m - 1)))
  fineDrift : ClassicalWindowBound F.tp F.tf 1 (streamVel (D.Φ F.m))
  fluxes : ∀ A ∈ ([F.readFlux, F.macroFluxField, F.mean, F.plain, F.kernel, F.fine, F.lastFlux] : List F.Flux),
    ∀ v, ClassicalWindowBound F.tp F.tf 1 (A v)
  readoutFluxRegularity : ∀ v,
    ClassicalWindowBound F.tp F.tf (4 * F.p + 2)
      (fun t x => toFluxL (menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t x))
  upsilonRegularity : ∀ v, ClassicalWindowBound F.tp F.tf (2 * F.p + 2) (F.upsilon v)
  sources : ∀ f ∈ ([F.liftedMean, F.physSource dRep dUh] : List F.Field),
    ∀ v, ClassicalWindowBound F.tp F.tf 0 (fun t x => f t x v)

/-- Static duality for both covariance polynomials, already supplied by the classical API. -/
def CovarianceAdjoints (F : Frame D hr Dm bw j₀) : Prop :=
  ∀ (t : ℝ) (v : CompIn F.G.comps) (u φ : Vec 2 → hr v.1.root),
    ContDiff ℝ ((2 * F.p : ℕ) : ℕ∞) u → ContDiff ℝ ((2 * F.p : ℕ) : ℕ∞) φ →
    IsZ2Periodic u → IsZ2Periodic φ →
    cellInner (covPolyP (menuCovPrimitive D F.Mn F.m t) F.p u) φ =
      cellInner u (covPolyP (menuCovPrimitive D F.Mn F.m t) F.p φ) ∧
    cellInner (covPolyQ (menuCovPrimitive D F.Mn F.m t) F.p u) φ =
      cellInner u (covPolyQ (menuCovPrimitive D F.Mn F.m t) F.p φ)

/-- A predicate on an actual frame, with root spaces remaining generic. -/
abbrev FramePredicate := ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}, Frame D hr Dm bw j₀ → Prop

/-- The native time-regularity package selected once, before testing either equation. -/
def NativeRepresentatives : FramePredicate :=
  fun {_hr} _ _ _ _ _ _ {D} {_Dm} {_bw} {_j₀} F =>
  ∃ dZ dRep dUh : F.Field, Regularity F dZ dRep dUh ∧
    ∃ dT : ℤ → F.Field,
      dUh = Construction.Residual.Presentation.gluedTimeDeriv
        F.Mn F.G F.m F.N F.depth F.CcT F.aRep dT ∧
      ∀ j, Odd j → IsTimeDerivRep (Set.Icc F.tp F.tf ∩ ocPulseWindow D.α D.q D.Λ F.m j)
        (Construction.Residual.Presentation.pulseLiftRep F.Mn F.G F.m F.N F.depth F.CcT j F.aRep)
        (dT j)

/-- Qualitative native inputs shared by cascade and terminal menus.
These are source data and finite reserve hypotheses, not time derivative or PDE conclusions. -/
structure NativeInput (F : Frame D hr Dm bw j₀) where
  stage : StageSuccessor.Input F.P F.Mn F.G
  actual : IsActualSuccessor D F.P F.Mn F.G F.G'
  retained : F.Gr = F.G'.retained F.m F.H F.J
  level : F.G.level = F.m
  generated : F.G.IsGenerated
  shift : F.G.IsShiftInvariant
  depth : F.G.fam.HasDepthAtMost F.depth
  /-- The context and ledger results supply these certificates before the analytic
  time calculus; covariance transport does not reconstruct generated contexts. -/
  incoming_context : ∃ k : InvConsts, F.G.IsContextCertified k ∧
    ∀ v : CompIn F.G.comps, 0 ≤ compReserve k v.1
  outgoing_context : ∃ k : InvConsts, F.G'.IsContextCertified k ∧
    ∀ v : CompIn F.G'.comps, 0 ≤ compReserve k v.1
  menuN : F.Mn.N = F.N
  menup : F.Mn.p = F.p
  menuH : F.Mn.H = F.H
  menuJ : F.Mn.J = F.J
  menuEta : F.Mn.η0 = F.η₀
  menuSlow : F.Mn.sX = F.sX
  menuFast : F.Mn.sZ = F.sZ
  window : F.tp ≤ F.tf
  /-- Numeric source carrier-start bound, shared by cascade and terminal entry.
  It licenses the appended chains consumed by the successor coefficient transfer. -/
  carrier_start : ∀ k : ℕ, j₀ ≤ k + 1 →
    2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤
      bw / (64 * (8 * Real.pi ^ 2))
  auxiliary : 4 * (F.N + Dm) + 16 + Dm + 6 * F.p ≤ F.Naux
  slow : max (F.N + 2) (2 * F.p) + Dm + 2 ≤ F.sX
  fast : max (F.N + 2) (2 * F.p) + Dm + 2 ≤ F.sZ
  integrable : Integrable F.φ₀
  smooth : ContDiff ℝ (⊤ : ℕ∞) F.φ₀
  nonnegative : ∀ z, 0 ≤ F.φ₀ z
  mass : ∫ z, F.φ₀ z = 1
  support : Function.support F.φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall
  kernels : ∃ Γ : ℝ, ∀ v u (γ : F.G.fam.Γ v u),
    (F.G.kernelOf F.P F.seedK F.freshK v u γ).IsAdmissible Γ 0
  successorKernels : ∃ Γ : ℝ, ∀ v u (γ : F.G'.fam.Γ v u),
    (F.G'.kernelOf F.P F.seedK F.freshK v u γ).IsAdmissible Γ 0
  Y0 : ∀ v : CompIn F.Gr.comps, TorusHk F.Naux (hr v.1.root)
  Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)
  Yk : ∀ v u (_ : F.Gr.fam.Γ v u), ℝ → TorusHk (F.Naux + Dm - 1) (hr u.1.root)
  solution : F.Gr.IsRegSolution F.P F.seedK F.freshK F.φ₀ integrable
    (D.κ (F.m - 1)) (streamVel (D.Φ (F.m - 1))) F.Naux F.tp F.tf Y0
    (fun _ _ => 0) (fun _ _ => 0) F.Y Yw Yk

/-- Native time regularity for any stage and any menu, including the terminal level. -/
def NativeTemporalRepresentativesStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (F : Frame D hr Dm bw j₀),
    NativeInput F → NativeRepresentatives F

/-- Recover the common-time strong equation from the tested readout equation. -/
def ReadoutStrongEquationStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (F : Frame D hr Dm bw j₀)
    (dZ dRep dUh : F.Field), Regularity F dZ dRep dUh → CovarianceAdjoints F →
    F.readoutWeak → F.StrongReadout dZ

/-- Product rule for the finite temporal covariance polynomial, with its last flux retained. -/
def CovarianceTemporalProductStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (F : Frame D hr Dm bw j₀)
    (dZ dRep dUh : F.Field), Regularity F dZ dRep dUh →
    (∀ t ∈ Set.Icc F.tp F.tf, ∀ x v, F.aRep t x v = menuCovPRep F.Mn D F.m F.p F.aZ t x v) →
    F.TemporalProduct dZ dRep

/-- Substitute the readout equation and group the exact finite mean flux. -/
def CovarianceMeanReductionStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (F : Frame D hr Dm bw j₀)
    (dZ dRep dUh : F.Field), Regularity F dZ dRep dUh →
    F.TemporalProduct dZ dRep → F.StrongReadout dZ → F.StrongMean dRep

/-- Integrate the strong macro equation against periodic tests. -/
def MacroWeakFromStrongStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (F : Frame D hr Dm bw j₀)
    (dZ dRep dUh : F.Field), Regularity F dZ dRep dUh → F.StrongMean dRep → F.macroWeak

/-- Use the literal complete lift and the definition of the unregularized physical residual. -/
def LiftResidualWeakStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (F : Frame D hr Dm bw j₀)
    (dZ dRep dUh : F.Field), Regularity F dZ dRep dUh → F.StrongMean dRep → F.plainWeak dRep dUh

/-- Split the plain coefficient flux into its kernel part and its literal fine defect. -/
def KernelDefectRegularizationStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (F : Frame D hr Dm bw j₀)
    (dZ dRep dUh : F.Field), Regularity F dZ dRep dUh →
    F.plainWeak dRep dUh → F.kernelWeak dRep dUh

/-- The already proved spatial covariance duality, applied to the native matrix. -/
theorem frame_covarianceAdjoints (F : Frame D hr Dm bw j₀)
    (hSym : ∀ t i j, menuCovPrimitive D F.Mn F.m t i j = menuCovPrimitive D F.Mn F.m t j i) :
    CovarianceAdjoints F := by
  intro t v u φ hu hφ hpu hpφ
  constructor
  · simpa only [covariancePolynomial_eq_P] using
      covariancePolynomial_cellInner_adjoint (menuCovPrimitive D F.Mn F.m t) (hSym t) F.p
        (fun l => (l.factorial : ℝ)⁻¹) u φ hu hφ hpu hpφ
  · simpa only [covariancePolynomial_eq_Q] using
      covariancePolynomial_cellInner_adjoint (menuCovPrimitive D F.Mn F.m t) (hSym t) F.p
        (fun l => (-1 : ℝ) ^ l / (l.factorial : ℝ)) u φ hu hφ hpu hpφ

/-- Uniqueness of the classical covariance image identifies the prepared field pointwise. -/
theorem frame_prepared_eq (F : Frame D hr Dm bw j₀) (dZ dRep dUh : F.Field)
    (hreg : Regularity F dZ dRep dUh) :
    ∀ t ∈ Set.Icc F.tp F.tf, ∀ x v, F.aRep t x v = menuCovPRep F.Mn D F.m F.p F.aZ t x v := by
  intro t ht x v
  have horder : F.Naux - 2 * F.p + 2 * F.p = F.Naux := by have := hreg.reserve; omega
  have hZ := F.readout v t ht
  have hZ' : IsClassicalRep
      (succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun v' => F.Y v' t) v)
      (fun x => F.aZ t x v) (F.Naux - 2 * F.p + 2 * F.p) := by
    simpa only [horder] using hZ
  obtain ⟨W, hW, hrep⟩ := covPolyP_carrier_exists (menuCovPrimitive D F.Mn F.m t)
    (hreg.covarianceSymmetric t) F.p (F.Naux - 2 * F.p) _ _ hZ'
  have he := classical_covImage_rep_unique _ _ (F.PZ v t) W
    (F.lift.2.1 v t ht).1 hW _ _ (F.lift.2.1 v t ht).2 hrep
  exact congrFun he x

/-- The original data prefix evaluated on a concrete frame; no weak equations are copied. -/
def CovarianceTransportDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ)
    (Qframe : FramePredicate) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (û : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root)),
      ∀ hlift : IsLiftedField G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) tp tf Y CcT PZ aRep û,
    ∀ (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (G'.retained m H J).comps, hr v.1.root),
      ∀ hZ : (∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep
        (succReadout m (D.eps (m - 1)) (succEta0 α q s) Naux (fun v' => Y v' t) v) (fun x => aZ t x v) Naux),
      ∀ hY : (∀ v', ∀ t ∈ Set.Icc tp tf, IsClassicalRep (Y v' t) (fun x => aY t x v') Naux),
    Qframe ({
      G := G, G' := G', Gr := G'.retained m H J,
      Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s),
      P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p,
      seedK := seedK, freshK := freshK, φ₀ := φ₀, m := m, H := H, J := J, N := N,
      p := p, depth := succSchedR r₀ J H, Naux := Naux, sX := sX, sZ := sZ,
      η₀ := succEta0 α q s, tp := tp, tf := tf, Y := Y, CcT := CcT, PZ := PZ,
      aRep := aRep, aZ := aZ, aY := aY, û := û, lift := (isMenuLiftedField_cascade (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) rfl rfl G
        (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) tp tf Y CcT PZ aRep û).2 hlift,
      readout := hZ,
      retained := hY } : Frame D hr (succSchedD D₀ N p (H + 1)) bw j₀)

/-- Production of the covariance-transport data, with the pre-data constants chosen in the same
order as in the covariance-transport statement. -/
def CovarianceTransportProductionStatement (α s q : ℝ) (ζ : ℝ → ℝ)
    (Qframe : FramePredicate) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ mStar : ℕ,
    CovarianceTransportDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar Qframe

/-- Cascade-specific adapter: supply qualitative native source inputs in the
uniform choice order. All seven analytic ingredients are independent of this prefix. -/
def CascadeNativeInputsProductionStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  CovarianceTransportProductionStatement α s q ζ (fun F => Nonempty (NativeInput F))

/-- Fixed-frame assembly. All derivative representatives are chosen before all tests. -/
theorem frame_transport_of_ingredients (F : Frame D hr Dm bw j₀)
    (hNative : NativeRepresentatives F)
    (hRead : ReadoutStrongEquationStatement)
    (hTemporal : CovarianceTemporalProductStatement)
    (hMean : CovarianceMeanReductionStatement)
    (hMacro : MacroWeakFromStrongStatement)
    (hLift : LiftResidualWeakStatement)
    (hKernel : KernelDefectRegularizationStatement)
    (hreadout : F.readoutWeak) :
    ∃ dRep dUh : F.Field,
      IsTimeDerivRep (Set.Icc F.tp F.tf) F.aRep dRep ∧
      IsTimeDerivRep (Set.Icc F.tp F.tf) F.uh dUh ∧
      F.macroWeak ∧ F.kernelWeak dRep dUh := by
  obtain ⟨dZ, dRep, dUh, hreg, _hglue⟩ := hNative
  have hAdj := frame_covarianceAdjoints F hreg.covarianceSymmetric
  have hEq := frame_prepared_eq F dZ dRep dUh hreg
  have hR := hRead F dZ dRep dUh hreg hAdj hreadout
  have hT := hTemporal F dZ dRep dUh hreg hEq
  have hM := hMean F dZ dRep dUh hreg hT hR
  exact ⟨dRep, dUh, hreg.prepared.derivative, hreg.lifted.derivative,
    hMacro F dZ dRep dUh hreg hM,
    hKernel F dZ dRep dUh hreg (hLift F dZ dRep dUh hreg hM)⟩

namespace Frame
variable (F : Frame D hr Dm bw j₀)

/-- The original cascade readout equation, through the shared weak-equation convention. -/
def cascadeReadoutWeak : Prop := F.weakEquation (D.κ (F.m - 1))
  (streamVel (D.Φ (F.m - 1))) F.aZ 0 (fun v t x =>
    -(toFluxL (covPolyQ (covPrimitive D F.m t) F.p
      (fun y => gFlux F.G F.m F.N F.p F.depth F.CcT F.aZ v t y) x) + F.upsilon v t x)) 0

/-- The original cascade macro equation. -/
def cascadeMacroWeak : Prop := F.weakEquation (D.κ (F.m - 1))
  (streamVel (D.Φ (F.m - 1))) F.aRep
  (fun v t x => toFluxL (macroFlux F.G F.m F.N F.depth F.CcT F.aRep v t x))
  (fun v t x => toFluxL (meanFluxF F.G F.m F.N F.p F.depth F.CcT F.aZ F.upsilon v t x)) 0

/-- The original cascade transported clause, including its common derivative witnesses. -/
def cascadeTransported : Prop :=
  ∃ dRep dUh : F.Field,
    IsTimeDerivRep (Set.Icc F.tp F.tf) F.aRep dRep ∧
    IsTimeDerivRep (Set.Icc F.tp F.tf) (liftedRep F.G F.m F.N F.depth F.CcT F.aRep) dUh ∧
    F.cascadeMacroWeak ∧
    F.weakEquation (D.κ F.m) (streamVel (D.Φ F.m))
      (liftedRep F.G F.m F.N F.depth F.CcT F.aRep)
      (coeffFluxOn F.P F.seedK F.freshK F.φ₀ F.G .kernel
        (liftedRep F.G F.m F.N F.depth F.CcT F.aRep))
      (fineFluxF F.P F.seedK F.freshK F.φ₀ F.G
        (liftedRep F.G F.m F.N F.depth F.CcT F.aRep))
      (fun t x v =>
        liftedRep F.G F.m F.N F.depth F.CcT
          (fun s y w => divE (fun z =>
            meanFluxF F.G F.m F.N F.p F.depth F.CcT F.aZ F.upsilon w s z) y) t x v +
        physRes F.P F.seedK F.freshK F.φ₀ F.G F.m F.N F.depth F.CcT F.aRep dRep dUh v t x)

end Frame

/-- Operator equalities keep menu specialization outside the weak-equation elaborator. -/
theorem frame_readFlux_cascade (F : Frame D hr Dm bw j₀)
    (hanchor : F.Mn.anchor = 0) (hlength : F.Mn.lenFactor = 1) :
    F.readFlux = fun v t x =>
      -(toFluxL (covPolyQ (covPrimitive D F.m t) F.p
        (fun y => gFlux F.G F.m F.N F.p F.depth F.CcT F.aZ v t y) x) + F.upsilon v t x) := by
  unfold Frame.readFlux
  rw [menuGFlux_cascade F.Mn hanchor hlength]
  simp only [menuCovPrimitive_cascade F.Mn hanchor]

theorem frame_macroFlux_cascade (F : Frame D hr Dm bw j₀)
    (hlength : F.Mn.lenFactor = 1) :
    F.macroFluxField = fun v t x => toFluxL (macroFlux F.G F.m F.N F.depth F.CcT F.aRep v t x) := by
  unfold Frame.macroFluxField
  rw [menuMacroFlux_cascade F.Mn hlength]

theorem frame_mean_cascade (F : Frame D hr Dm bw j₀)
    (hanchor : F.Mn.anchor = 0) (hlength : F.Mn.lenFactor = 1) :
    F.mean = fun v t x => toFluxL (meanFluxF F.G F.m F.N F.p F.depth F.CcT F.aZ F.upsilon v t x) := by
  unfold Frame.mean
  rw [menuMeanFluxF_cascade F.Mn hanchor hlength]

theorem frame_physSource_cascade (F : Frame D hr Dm bw j₀)
    (hanchor : F.Mn.anchor = 0) (hlength : F.Mn.lenFactor = 1) (dRep dUh : F.Field) :
    F.physSource dRep dUh = fun t x v =>
      liftedRep F.G F.m F.N F.depth F.CcT
        (fun s y w => divE (fun z =>
          meanFluxF F.G F.m F.N F.p F.depth F.CcT F.aZ F.upsilon w s z) y) t x v +
      physRes F.P F.seedK F.freshK F.φ₀ F.G F.m F.N F.depth F.CcT F.aRep dRep dUh v t x := by
  unfold Frame.physSource Frame.liftedMean Frame.meanDiv
  rw [frame_mean_cascade F hanchor hlength, menuLiftedRep_cascade F.Mn hlength,
    menuPhysRes_cascade F.Mn hlength]
  rfl

/-- Specialize the shared menu identity separately from the long uniform data prefix. -/
theorem frame_cascade_transport_of_ingredients (F : Frame D hr Dm bw j₀)
    (hanchor : F.Mn.anchor = 0) (hlength : F.Mn.lenFactor = 1)
    (hNative : NativeRepresentatives F)
    (hRead : ReadoutStrongEquationStatement) (hTemporal : CovarianceTemporalProductStatement)
    (hMean : CovarianceMeanReductionStatement) (hMacro : MacroWeakFromStrongStatement)
    (hLift : LiftResidualWeakStatement) (hKernel : KernelDefectRegularizationStatement)
    (hreadout : F.cascadeReadoutWeak) : F.cascadeTransported := by
  have hread : F.readoutWeak := by
    unfold Frame.readoutWeak
    rw [frame_readFlux_cascade F hanchor hlength]
    exact hreadout
  obtain ⟨dRep, dUh, hdRep, hdUh, hmacro, hkernel⟩ :=
    frame_transport_of_ingredients F hNative hRead hTemporal hMean hMacro hLift hKernel hread
  have huh : F.uh = liftedRep F.G F.m F.N F.depth F.CcT F.aRep :=
    menuLiftedRep_cascade F.Mn hlength F.G F.m F.N F.depth F.CcT F.aRep
  refine ⟨dRep, dUh, hdRep, ?_, ?_, ?_⟩
  · rw [huh] at hdUh
    exact hdUh
  · unfold Frame.macroWeak at hmacro
    rw [frame_macroFlux_cascade F hlength, frame_mean_cascade F hanchor hlength] at hmacro
    exact hmacro
  · unfold Frame.kernelWeak Frame.kernel Frame.fine at hkernel
    rw [huh, frame_physSource_cascade F hanchor hlength dRep dUh] at hkernel
    exact hkernel

/-- Produce common representatives before the weak-equation adapter. -/
theorem covariance_transport_native_data (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ)
    (hInputs : CovarianceTransportDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar
      (fun F => Nonempty (NativeInput F)))
    (hNative : NativeTemporalRepresentativesStatement) :
    CovarianceTransportDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar
      NativeRepresentatives := by
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  have hI := hInputs D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  exact hNative _ hI.some

/-- Adapter to the original three-clause residual data statement. -/
theorem covariance_transport_data_of_ingredients (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ)
    (hNativeData : CovarianceTransportDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar
      NativeRepresentatives)
    (hRead : ReadoutStrongEquationStatement) (hTemporal : CovarianceTemporalProductStatement)
    (hMean : CovarianceMeanReductionStatement) (hMacro : MacroWeakFromStrongStatement)
    (hLift : LiftResidualWeakStatement) (hKernel : KernelDefectRegularizationStatement) :
    ResidualDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
      σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar (fun readout transported _ => readout → transported) := by
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY hreadout
  let F : Frame D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
    { G := G, G' := G', Gr := G'.retained m H J,
      Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s),
      P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p,
      seedK := seedK, freshK := freshK, φ₀ := φ₀, m := m, H := H, J := J, N := N,
      p := p, depth := succSchedR r₀ J H, Naux := Naux, sX := sX, sZ := sZ,
      η₀ := succEta0 α q s, tp := tp, tf := tf, Y := Y, CcT := CcT, PZ := PZ,
      aRep := aRep, aZ := aZ, aY := aY, û := û, lift := (isMenuLiftedField_cascade (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) rfl rfl G
        (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) tp tf Y CcT PZ aRep û).2 hlift, readout := hZ, retained := hY }
  have hNF : NativeRepresentatives F := hNativeData D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  obtain ⟨dRep, dUh, hdRep, hdUh, hmacro, hkernel⟩ :=
    frame_cascade_transport_of_ingredients F rfl rfl hNF hRead hTemporal hMean hMacro hLift hKernel
      hreadout
  exact ⟨dRep, dUh, hdRep, hdUh, fun v t ht φ hφ hpφ =>
    ⟨hmacro v t ht φ hφ hpφ, hkernel v t ht φ hφ hpφ⟩⟩

/-- Assembly of the exact native covariance/lift leaf.
The first ingredient chooses all pre-data constants in their original order. -/
theorem native_lift_covariance_residual_identity_of_ingredients {α s q : ℝ} {ζ : ℝ → ℝ}
    (hInputs : CascadeNativeInputsProductionStatement α s q ζ)
    (hNative : NativeTemporalRepresentativesStatement)
    (hRead : ReadoutStrongEquationStatement) (hTemporal : CovarianceTemporalProductStatement)
    (hMean : CovarianceMeanReductionStatement) (hMacro : MacroWeakFromStrongStatement)
    (hLift : LiftResidualWeakStatement) (hKernel : KernelDefectRegularizationStatement) :
    NativeLiftCovarianceResidualIdentityStatement α s q ζ := by
  obtain ⟨Λ₀, hΛ₀, hN⟩ := hInputs
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨c₀max, hc₀max, hN⟩ := hN Λ hΛ
  refine ⟨c₀max, hc₀max, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hfloorX hfloorZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hN⟩ := hN φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hfloorX hfloorZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hN⟩ := hN kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨mStar, hN⟩ := hN CI Cw j₀ hledger hstart CQ Cpr
  exact ⟨mStar, covariance_transport_data_of_ingredients α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
    r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar
    (covariance_transport_native_data α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar
      hN hNative) hRead hTemporal hMean hMacro hLift hKernel⟩

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Splitting the plain coefficient flux into its kernel part and its fine defect, and the
resulting transfer of the weak identity (ingredient `KernelDefectRegularizationStatement`). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.FullLift

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The plain flux is the kernel flux plus the fine defect, at every time of the window. -/
theorem kernelDefect_plain_eq_add (F : Frame D hr Dm bw j₀) {dZ dRep dUh : F.Field}
    (hR : Regularity F dZ dRep dUh) (v : CompIn F.G.comps) (t : ℝ)
    (ht : t ∈ Set.Icc F.tp F.tf) (x : Vec 2) :
    F.plain v t x = F.kernel v t x + F.fine v t x := by
  simp only [Frame.plain, Frame.kernel, Frame.fine, fineFluxF, coeffFluxOn]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← map_add]
  congr 1
  ext word
  have hd : d.1 - 1 ≤ Dm + 4 - 2 := by
    have := (Finset.mem_Icc.mp d.2).2
    omega
  have hu : ContDiff ℝ ((d.1 - 1 : ℕ) : ℕ∞) (fun y => F.uh t y u) :=
    ((hR.lifted.field u).smooth t ht).of_le (Nat.cast_le.mpr hd)
  have hk : ContDiff ℝ ((d.1 - 1 : ℕ) : ℕ∞)
      ((F.G.kernelOf F.P F.seedK F.freshK v u γ).applyClassical F.φ₀ t (fun y => F.uh t y u)) :=
    (hR.kernelFields v u γ t ht).of_le (by
      have := (Finset.mem_Icc.mp d.2).2
      exact Nat.cast_le.mpr (by omega : d.1 - 1 ≤ Dm + 1))
  have hs := congrFun (orderedDerivative_sub word hu hk) x
  simp only [PiLp.add_apply]
  rw [hs]
  simp

/-- The weak identity only sees the sum of the two fluxes, and only for times in the interval. -/
theorem kernelDefect_weak_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure (Vec 2)) (ν t₀ t : ℝ) (v : ℝ → Vec 2 → Vec 2) (u₀ f φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (A₁ B₁ A₂ B₂ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hAB : ∀ s ∈ Set.Ioc t₀ t, ∀ x, A₁ s x + B₁ s x = A₂ s x + B₂ s x)
    (h : AVRegularity.CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du A₁ B₁ g) :
    AVRegularity.CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du A₂ B₂ g := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hrhs : ∀ s ∈ Set.Ioc t₀ t, ∀ x,
      (-(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)
        - ∑ k : Fin 2, inner ℝ (A₂ s x k + B₂ s x k) (dφ k x) + inner ℝ (g s x) (φ x)) =
      (-(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)
        - ∑ k : Fin 2, inner ℝ (A₁ s x k + B₁ s x k) (dφ k x) + inner ℝ (g s x) (φ x)) := by
    intro s hs x
    have e : ∀ k, A₂ s x k + B₂ s x k = A₁ s x k + B₁ s x k := fun k => by
      have := congrArg (fun z : PiLp 2 (fun _ : Fin 2 => E) => z k) (hAB s hs x)
      simpa using this.symm
    simp only [e]
  have hint : ∀ s ∈ Set.Ioc t₀ t,
      (∫ x, (-(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)
        - ∑ k : Fin 2, inner ℝ (A₂ s x k + B₂ s x k) (dφ k x) + inner ℝ (g s x) (φ x)) ∂μ) =
      ∫ x, (-(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)
        - ∑ k : Fin 2, inner ℝ (A₁ s x k + B₁ s x k) (dφ k x) + inner ℝ (g s x) (φ x)) ∂μ :=
    fun s hs => integral_congr_ae (Filter.Eventually.of_forall (hrhs s hs))
  refine ⟨h1, h2, fun s hs => ?_, ?_, ?_⟩
  · exact (h3 s hs).congr (Filter.Eventually.of_forall (fun x => (hrhs s hs x).symm))
  · exact h4.congr_fun (fun s hs => (hint s hs).symm) measurableSet_Ioc
  · rw [h5]
    exact setIntegral_congr_fun measurableSet_Ioc (fun s hs => (hint s hs).symm)

/-- Ingredient: the plain weak equation implies the kernel weak equation. -/
theorem kernelDefectRegularization : KernelDefectRegularizationStatement := by
  intro hr _ _ _ _ _ _ D Dm bw j₀ F dZ dRep dUh hR h w t ht φ hφ hper
  refine kernelDefect_weak_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ (h w t ht φ hφ hper)
  intro s hs x
  have hs' : s ∈ Set.Icc F.tp F.tf := ⟨hs.1.le, hs.2.trans ht.2⟩
  have := kernelDefect_plain_eq_add F hR w s hs' x
  simp [this]

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Ingredient `LiftResidualWeakStatement`, step 1: time locality of the complete lift (when its
slow length is nonzero) and the pointwise strong identity for the lifted equation. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.FullLift

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem liftResidual_liftApply_congr {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (n : ℕ) (C : LiftCoeff ι h)
    (a a' : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (hat : a t = a' t) :
    liftApply n C a t = liftApply n C a' t := by
  funext X z v
  simp only [liftApply, hat]

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The complete lift at time `t` only sees the lifted field at time `t`. -/
theorem liftResidual_menuLiftedRep_local (Mn : SuccMenu) (G : GenStage D hr Dm bw j₀)
    (m N depth : ℕ) (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hc : D.cellScaleSq m ≠ 0)
    (g g' : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (hgt : g t = g' t) :
    menuLiftedRep Mn G m N depth CcT g t = menuLiftedRep Mn G m N depth CcT g' t := by
  funext x
  simp only [menuLiftedRep, gluedLift, pulsePhysicalLift, diagSample]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun hh _ => Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [liftResidual_liftApply_congr]
  funext X'
  simp only [mul_inv_cancel_left₀ hc, hgt]

/-- The pointwise strong identity for the lift, at a time where the strong mean equation holds. -/
theorem liftResidual_pointwise (F : Frame D hr Dm bw j₀) (hc : D.cellScaleSq F.m ≠ 0)
    (dRep dUh : F.Field) (t : ℝ) (hSM : ∀ x v, F.macroResidual dRep t x v = F.meanDiv t x v)
    (x : Vec 2) (v : CompIn F.G.comps) :
    dUh t x v + ∑ j : Fin 2, streamVel (D.Φ F.m) t x j • gradE (fun y => F.uh t y v) x j -
      divE (fun y => D.κ F.m • gradE (fun y' => F.uh t y' v) y +
        fun j => WithLp.ofLp (F.plain v t y) j) x =
      F.physSource dRep dUh t x v := by
  have hloc : menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT (F.macroResidual dRep) t =
      menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.meanDiv t :=
    liftResidual_menuLiftedRep_local F.Mn F.G F.m F.N F.depth F.CcT hc _ _ t
      (funext fun x => funext fun v => hSM x v)
  have hx := congrFun hloc x
  have hxv := congrFun hx v
  unfold Frame.physSource menuPhysRes
  change _ = menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.meanDiv t x v + (_ - _)
  rw [← hxv]
  change _ = _ + (_ - menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT (F.macroResidual dRep) t x v)
  abel

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end

section
section
/-! Native budgets, stream part: the two drift fields of `Regularity` depend only on the
admissible streams of the data, so they follow from joint smoothness and periodicity. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- A jointly smooth field, periodic in space, has order-one window budgets. -/
theorem nativeBudget_windowBound_one_of_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {g : ℝ → Vec 2 → E} (hg : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry g))
    (hp : ∀ t, IsZ2Periodic (g t)) (a b : ℝ) :
    ClassicalWindowBound a b 1 g := by
  have hslice : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (g t) := fun t =>
    hg.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨Q, hQc, hQ⟩ : ∃ Q : Set (Vec 2), IsCompact Q ∧ unitCube ⊆ Q :=
    ⟨Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1),
      isCompact_univ_pi fun _ => isCompact_Icc,
      fun x hx i _ => Set.Ioo_subset_Icc_self (hx i (Set.mem_univ i))⟩
  have hS : IsCompact (Icc a b ×ˢ Q) := isCompact_Icc.prod hQc
  have hder : ∀ t x (v : Vec 2), fderiv ℝ (g t) x v =
      fderiv ℝ (Function.uncurry g) (t, x) (0, v) := by
    intro t x v
    have hd : DifferentiableAt ℝ (Function.uncurry g) (t, x) :=
      (hg.differentiable (by simp)) _
    have hcomp := hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
    have : fderiv ℝ (g t) x = (fderiv ℝ (Function.uncurry g) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) := hcomp.fderiv
    rw [this]; simp
  refine ⟨fun t _ => (hslice t).of_le (by exact_mod_cast le_top), fun t _ => hp t,
    (hg.continuous.comp continuous_subtype_val).measurable, ?_⟩
  intro n hn w
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (f := Function.uncurry g)
      hg.continuous.continuousOn
    refine ⟨fun _ => C, integrableOn_const (by simp), fun t ht x hx => ?_⟩
    have := hC (t, x) ⟨ht, hQ hx⟩
    rw [AVRegularity.orderedDerivative_zero]
    exact this
  · have hc : Continuous (fun p : ℝ × Vec 2 => fderiv ℝ (Function.uncurry g) p (0, basisVec (w 0))) :=
      ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨fun _ => C, integrableOn_const (by simp), fun t ht x hx => ?_⟩
    rw [AVRegularity.CycleWords.orderedDerivative_one_literal]
    show ‖fderiv ℝ (g t) x (basisVec (w 0))‖ ≤ C
    rw [hder]
    exact hC (t, x) ⟨ht, hQ hx⟩

/-- Window budgets of the velocity of an admissible stream. -/
theorem nativeBudget_streamVel_windowBound (φ : ℝ → Vec 2 → ℝ) (h : IsAdmissibleStream φ)
    (a b : ℝ) : ClassicalWindowBound a b 1 (streamVel φ) :=
  nativeBudget_windowBound_one_of_jointSmooth
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel h).smooth
    (fun t => AVRegularity.CycleReference.admissible_streamVel_periodic h t) a b

/-- The coarse drift field of `Regularity`. -/
theorem nativeBudget_coarseDrift (F : Frame D hr Dm bw j₀) :
    ClassicalWindowBound F.tp F.tf 1 (streamVel (D.Φ (F.m - 1))) :=
  nativeBudget_streamVel_windowBound _ (D.hΦ _) _ _

/-- The fine drift field of `Regularity`. -/
theorem nativeBudget_fineDrift (F : Frame D hr Dm bw j₀) :
    ClassicalWindowBound F.tp F.tf 1 (streamVel (D.Φ F.m)) :=
  nativeBudget_streamVel_windowBound _ (D.hΦ _) _ _

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Frame-level bookkeeping for the temporal product: the stream velocity of an admissible stream,
and the pointwise flux identity between the macro flux, the readout flux and the commutator flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

theorem stream_smooth_div {φ : ℝ → Vec 2 → ℝ} (h : IsAdmissibleStream φ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (streamVel φ t) ∧
      ∀ x, ∑ k : Fin 2, fderiv ℝ (streamVel φ t) x (basisVec k) k = 0 := by
  have hφ : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (φ s) := fun s =>
    h.1.comp (contDiff_const.prodMk contDiff_id)
  have hvs : ContDiff ℝ (⊤ : ℕ∞) (streamVel φ t) :=
    contDiff_pi.2 (AVRegularity.Applications.streamVel_comp_smooth hφ t)
  refine ⟨hvs, fun x => ?_⟩
  have hd := AVRegularity.Applications.streamVel_classical_div hφ t x
  unfold AVRegularity.Applications.pd at hd
  rw [AVRegularity.Velocity.Port.MaterialSpatial.fderiv_component_apply hvs x 0 0,
    AVRegularity.Velocity.Port.MaterialSpatial.fderiv_component_apply hvs x 1 1] at hd
  rw [Fin.sum_univ_two]
  exact hd

theorem rate_flux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ) (w : Fin 2 → E) (j : Fin 2) :
    ∑ l : Fin 2, (R - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j l • w l =
      ∑ l : Fin 2, R j l • w l - κ • w j := by
  simp [Matrix.sub_apply, Matrix.one_apply, sub_smul, Finset.sum_sub_distrib, ite_smul]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The macro flux, the readout flux and the commutator flux of the finite temporal conjugation
add up pointwise to the flux of `R ∇ P_p φ` plus the commutator flux. -/
theorem flux_identity' (F : Frame D hr Dm bw j₀) (hc : D.cellScaleSq F.m ≠ 0) (t : ℝ)
    (hid : ∀ x v, F.aRep t x v = menuCovPRep F.Mn D F.m F.p F.aZ t x v)
    (v : CompIn F.G.comps) (y : Vec 2) :
    D.κ (F.m - 1) • gradE (fun y' => F.aRep t y' v) y +
        menuMacroFlux F.Mn F.G F.m F.N F.depth F.CcT F.aRep v t y =
      Tcomm (streamVel (D.Φ (F.m - 1)) t) (menuCovPrimitive D F.Mn F.m t) F.p
          (fun y' => F.aZ t y' v) y +
        FluxA (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t)
          (AVRegularity.covPolyP (menuCovPrimitive D F.Mn F.m t) F.p (fun y' => F.aZ t y' v)) y -
        menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y := by
  have hg : (fun y' => F.aRep t y' v) =
      AVRegularity.covPolyP (menuCovPrimitive D F.Mn F.m t) F.p (fun y' => F.aZ t y' v) :=
    funext fun y' => hid y' v
  have hdiag := menuDiagFluxPhys_local F.Mn F.G F.m F.N F.CcT F.aRep
    (fun s y w => AVRegularity.covPolyP (menuCovPrimitive D F.Mn F.m s) F.p
      (fun y' => F.aZ s y' w) y) t y v hc (funext fun y' => funext fun w => hid y' w)
  have hmean := menuMeanFluxE_local F.Mn F.G F.m F.N F.depth F.CcT F.aRep
    (menuCovPRep F.Mn D F.m F.p F.aZ) t y v hc (funext fun y' => funext fun w => hid y' w)
  funext j
  simp only [menuMacroFlux, menuGFlux, menuTemporalFlux, Tcomm, FluxA, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply]
  rw [hdiag, hmean, hg, rate_flux]
  abel

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end
