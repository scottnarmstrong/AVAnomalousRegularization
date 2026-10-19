-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Construction.DiagLetter
public import AVRegularity.Statements.Intermediate.KernelEnergy.KernelWeakSolutionTorus
public import AVRegularity.Statements.Intermediate.CycleComparison.CellInner
public import AVRegularity.Statements.Intermediate.CycleJoint.OcQuietTimes
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! Definition: the actual construction of the next family of a
passage, and the cascade from a seed.

`IsActualSuccessor D P Mn G G'`: the stage `G'` of level `m-1` is the *extended* next family of the
stage `G` of level `m`:
* its components are the extended set `{(v,𝔱)}` (`succExtComps`), its pieces the natural renewal
  charts of level `m-1` with the partition `ϖ_{m-1,·}`, its records the tags of the provenance;
* it inherits the certified seed exports (`G'.exports e ↔ G.exports e`: production forms
  new transverse inverses and never registers a newly solved problem as seed data);
* its identities on every edge are in bijection (`e`) with the valid sources `SuccSource` of that
  edge (copies of the transported old block `𝖮 = 𝖤_2 + 𝖤_{dir,>2}` into every word, the letters
  `𝖣, 𝖬_{n,h}, 𝖵_{n,h,a,a'}` from every word of length at most `J`), with the provenance of the
  source and the ordered product of the path maps (`rootPathMap`, the identity for `𝖣`);
* the coefficient of every identity except `𝖣` is the transfer to the coarser chart
  (`transferAt`, with the letter normalization `ε_{m-1}^{-η₀}`) of the finer output of its source,
  computed from the lift coefficients `Cc` of the scalar path family on every real family over
  every slot of level `m`; the lifts are characterized by the relation `IsLiftSequence`,
  localized to the admissible slow offsets (`IsLiftSequenceOn (ladderOmega …)`), on
  the original interval `J_k` of the pulse, from zero at its original start `inf J_𝗉`
  (uniqueness is that of the cell inverse);
* the first source `𝖣` is fixed by the construction (`firstSourceFlux`:
  the grade-zero lifts `Cc0` on the appended children, the assembled diagonal flux with the
  reference bridge, the Eulerian commutator, the Piola pullback, coefficient extraction
  normalized by `B ε_{m-1}^{d-2}`, then the word normalization `ε_{m-1}^{-η₀}`).
The objects characterized by equations (the lifts) are existentially quantified inside the
relation, as witnesses of `IsLiftSequence`; no witness is chosen. `successor_exists`
asserts that a next family exists, `successor_flux_unique` that two of them have the same
coefficients, except those of the first source `𝖣`.

`GenStage.retained G' m H J`: the production family of the passage (the retained part).

`IsCascadeStage D P Mn seed G`: `G` is obtained from the seed by finitely many actual successors,
each restricted to its retained components `Π` (birth grade at most `H`, word length at most
`J`). -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The finite menus and reserves of the construction: terminal level `M`, padded alphabet `A`,
grade cutoff `H`, word length `J`, cell cutoff `N`, covariance degree `p`, lift reserves
`(sX, sZ)`, readout exponent `η₀`. -/
structure SuccMenu where
  /-- The terminal level `M`. -/
  M : ℕ
  /-- The padded alphabet. -/
  A : Finset WordLetter
  /-- The grade cutoff `H`. -/
  H : ℕ
  /-- The word length `J`. -/
  J : ℕ
  /-- The cell cutoff `N`. -/
  N : ℕ
  /-- The covariance degree `p`. -/
  p : ℕ
  /-- The slow reserve of the lifts. -/
  sX : ℕ
  /-- The fast reserve of the lifts. -/
  sZ : ℕ
  /-- The readout exponent `η₀`. -/
  η0 : ℝ
  /-- The anchor of the covariance primitive of the passage: `0` in the cascade,
  the quiet endpoint `t_p` at terminal entry. -/
  anchor : ℝ
  /-- The factor of the lift slow length: `1` in the cascade (`ρ_m = √(κ_{m-1}τ_m'')`), `c_r` at
  terminal entry (`ρ = c_r√(Bh)`). -/
  lenFactor : ℝ

/-- The lift slow length `ρ_m = √(κ_{m-1} τ_m'')` of the passage at level `m`. -/
def liftLength (D : OCData) (m : ℕ) : ℝ := Real.sqrt (D.κ (m - 1) * ocTauPP D.α D.q D.Λ m)

namespace SuccSource

variable {G : GenStage D hr Dm b j₀}

/-- The lift coefficients of the path of a source are the lift sequences of its scalar path
family on every admissible real family over every slot of level `m = G.level`, on the original
interval of the pulse in cell time, for the admissible slow offsets `ladderOmega` of the family
(the old fluxes are pinned to zero off the carrier, so the lift relation is
localized to the slow offsets whose recentering is admissible). -/
def IsLiftFamily (Mn : SuccMenu) (s : SuccSource G)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)) : Prop :=
  match s, Cc with
  | .copyQuad _ h π, Cc | .letterMean _ _ h π, Cc | .letterCov _ _ h _ _ π, Cc =>
      ∀ (k : ℤ) (A : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k),
        IsLiftSequenceOn (ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level))
          (familyLiftData D G.level k A (Mn.lenFactor * liftLength D G.level)
            (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩))
          Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
          ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
          Mn.N h (Cc k A)
  | .copyDir .., _ | .letterDiag .., _ => True

/-- The source is the first source `𝖣`. -/
def IsDiag : SuccSource G → Prop
  | .letterDiag .. => True
  | _ => False

end SuccSource

/-- The grade-zero lifts of level `m`: the lift sequences of the scalar family with no edge on
every admissible real family over every odd slot of level `m` (in particular on the appended
children `𝒜^♮_k` of the first source), on the original interval of the slot. -/
def IsDiagLifts (D : OCData) (Dm : ℕ) (b : ℝ) (j₀ : ℕ) (Mn : SuccMenu) (m : ℕ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) : Prop :=
  ∀ (k : ℤ) (A : RealChain), Odd k → IsAdmissibleChain D b j₀ m k A →
    IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A
        (Mn.lenFactor * liftLength D m) (fun _ _ _ => []))
      Mn.sX Mn.sZ (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) Mn.N 0 (Cc0 k A)

open scoped Classical in
/-- `G'` is the extended next family of `G` by the actual construction. Coefficients are pinned
by the construction on the outer carrier and to zero off it. -/
def IsActualSuccessor (D : OCData) (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) : Prop :=
  1 ≤ G.level ∧ G'.level = G.level - 1 ∧
    G'.comps = succExtComps G.level Mn.A Mn.J G.comps ∧ G'.IsNatural Mn.M ∧ G'.HasTags P ∧
    (∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), G'.exports e ↔ G.exports e) ∧
    ∃ (e : ∀ v' u', G'.fam.Γ v' u' ≃ {s : SuccSource G //
          s.Valid Mn.A Mn.J ∧ s.srcComp G.level = u'.1 ∧ s.tgtComp G.level = v'.1})
      (Cc : ∀ s : SuccSource G, ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
      (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)),
      (∀ s : SuccSource G, s.IsLiftFamily Mn (Cc s)) ∧ IsDiagLifts D Dm b j₀ Mn G.level Cc0 ∧
      ∀ v' u' (γ' : G'.fam.Γ v' u'),
        G'.prov v' u' γ' = (e v' u' γ').1.prov G.level ∧
        (G'.fam.identity v' u' γ').map = rootPathMap hr u'.1.root (e v' u' γ').1.maps v'.1.root ∧
        ((¬ (e v' u' γ').1.IsDiag →
          ∀ (p : OddSlot) (c : StageCtx D b j₀ G'.level p) (d : ℕ) (I : DerivativeWord2 (d - 1))
            (t : ℝ) (X z : Vec 2), 2 ≤ d →
            G'.fam.flux p c v' u' γ' d I t X z =
              if IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
              then transferAt D G.level p.1 ((e v' u' γ').1.lam G.level Mn.η0)
                (((e v' u' γ').1.prov G.level).tags P).order
                ((e v' u' γ').1.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor
                  (Cc (e v' u' γ').1)) t
                (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
              else 0) ∧
         ((e v' u' γ').1.IsDiag →
          ∀ (p : OddSlot) (c : StageCtx D b j₀ G'.level p) (d : ℕ) (I : DerivativeWord2 (d - 1))
            (t : ℝ) (X z : Vec 2), 2 ≤ d →
            G'.fam.flux p c v' u' γ' d I t X z =
              if IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
              then ((e v' u' γ').1.lam G.level Mn.η0 *
                  (D.κ G'.level * D.eps G'.level ^ (d - 2))⁻¹) •
                fluxCoeff (firstSourceFlux D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N Mn.p
                  Mn.anchor Cc0 t
                  (c.1.recenter D (D.eps (G'.level - 1) • X)) z) d I 0
              else 0))

/-- The retained part `Π G'` of an extended next family of the passage `m → m-1`: the components
of birth grade at most `H` and word length at most `J`. -/
def GenStage.retained (G' : GenStage D hr Dm b j₀) (m H J : ℕ) : GenStage D hr Dm b j₀ :=
  G'.restrict (G'.comps.filter (IsRetained m H J)) (Finset.filter_subset _ _)

/-- `G` is a stage of the cascade from the seed: finitely many actual successors, each restricted
to its retained components. -/
inductive IsCascadeStage (D : OCData) (P : ProvParams) (Mn : SuccMenu)
    (seed : GenStage D hr Dm b j₀) : GenStage D hr Dm b j₀ → Prop
  | seed : IsCascadeStage D P Mn seed seed
  | step {G G' : GenStage D hr Dm b j₀} :
      IsCascadeStage D P Mn seed G → IsActualSuccessor D P Mn G G' →
      IsCascadeStage D P Mn seed (G'.retained G.level Mn.H Mn.J)

end AVRegularity
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Definitions for `succ_window_data`: the window
bounds of the lift operators of the scalar path families of a stage, on the cell-time window of
each admissible odd pulse. -/

/-- Window bounds of a cell operator on `[a, b]`: ellipticity `lo > 0`, entries bounded by `A`, and
drift bounded by `Mv`. -/
def IsCellWindowBound (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (a b lo A Mv : ℝ) : Prop :=
  0 < lo ∧ (∀ t ∈ Set.Icc a b, ∀ ξ : Fin 2 → ℝ, lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j) ∧
    (∀ t ∈ Set.Icc a b, ∀ i j, |G t i j| ≤ A) ∧ ∀ t ∈ Set.Icc a b, ∀ z k, |v t z k| ≤ Mv

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {Dm : ℕ}

/-- The window data of the stage `G`: for every scalar path family, every admissible odd chain and
every slow point, the molecular metric and the pulse drift of the family's lift operator satisfy
window bounds on the cell-time window `[s_k/ℓ², (k + 61/48)τ/ℓ²]` of the pulse. -/
def SuccWindowData (D : OCData) (b : ℝ) (j₀ : ℕ) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) :
    Prop :=
  ∀ (h : ℕ) (π : StagePath G h) (k : ℤ) (A : RealChain)
    (hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k) (X : Vec 2),
    ∃ lo A' Mv : ℝ, IsCellWindowBound
      (fun t => Matrix.of ((familyLiftData D G.level k A (Mn.lenFactor * liftLength D G.level)
        (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)).G t X))
      (familyLiftData D G.level k A (Mn.lenFactor * liftLength D G.level)
        (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)).v
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) lo A' Mv

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! Definition: the regularized system of a stage, its masses, markers and readout,
and the duality images of the covariance polynomials.

* `GenStage.mass law`, `marker law`, `readoutWeight law`: `π_v`, `d_v`, `ω_v` computed from the
  history (`compMass`, `compMarker`, `compReadout`).
* `GenStage.IsRegSolution`: the stage's regularized system
  `(∂_t + 𝐛·∇ - νΔ)U_v = div(∑_{u,γ,d} a^phys_{γ,d} ∇^{d-1} S_γ U_u + F_v) + g_v` (the system
  (4.6) of the paper) in the kernel-regularized solution class `IsKernelWeakSolutionTorus`, with
  the physical coefficients of the stage (the map `C_γ` is inside `a^phys`, so the `C` of that
  class is the identity and its `G` is the source space), and the kernels of the identities.
  
* `compParent m c`: the component of the incoming family from which `c` was born at the passage
  `m → m-1`; `succReadout`: `(𝖱X)_v = ∑_𝔱 E^{η₀|𝔱|} X_{(v,𝔱)}`.
* `IsCovImage Hc P W Z`: `W = 𝖯 Z` in the duality sense for a formally self-adjoint constant
  coefficient operator `P` (here `𝖯_p` or `𝖰_p` with `H = Hc`): `⟨W, φ⟩ = ⟨Z, Pφ⟩` for every smooth
  periodic test field (`IsCoarseWitness` uses the same device). -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

namespace GenStage

/-- The masses `π_v`. -/
def mass (law : BirthLaw) (G : GenStage D hr Dm b j₀) (v : CompIn G.comps) : ℝ :=
  compMass D.q D.Λ law v.1

/-- The markers `d_v = ∏_{k ∈ 𝖡(v)} ε_k^{-ι}`. -/
def marker (law : BirthLaw) (G : GenStage D hr Dm b j₀) (v : CompIn G.comps) : ℝ :=
  compMarker D.q D.Λ law v.1

/-- The readout factors `ω_v`. -/
def readoutWeight (law : BirthLaw) (G : GenStage D hr Dm b j₀) (v : CompIn G.comps) : ℝ :=
  compReadout D.q D.Λ law v.1

/-- The kernel operators `S_γ(t)` of the identities. -/
def sysS (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (G : GenStage D hr Dm b j₀) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (t : ℝ) :
    Lp (hr u.1.root) 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp (hr u.1.root) 2 (volume.restrict AVenhance.unitCube) :=
  (G.kernelOf P seedK freshK v u γ).op φ₀ hφ₀ t

/-- `(U, W, Y)` solves the regularized system of the stage on `[t₀, t₁]` at the common order `k`,
with diffusivity `ν`, drift `bv`, initial value `f` and forcing `(F, g)`. -/
def IsRegSolution (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm b j₀) (ν : ℝ) (bv : ℝ → Vec 2 → Vec 2)
    (k : ℕ) (t₀ t₁ : ℝ) (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (F : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (g : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (γ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)) : Prop :=
  IsKernelWeakSolutionTorus (ι := CompIn G.comps) (h := fun v => hr v.1.root) (Γ := G.fam.Γ)
    (G := fun _ u _ => hr u.1.root) ν t₀ t₁ bv k Dm
    (fun v u γ d => G.physCoeff v u γ d.1) (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
    (fun v u γ => G.sysS P seedK freshK φ₀ hφ₀ v u γ) f F g U W Y

end GenStage

/-- The component of the incoming family from which `c` was born at the passage `m → m-1`. -/
def compParent (m : ℕ) (c : Comp) : Comp :=
  match c.births with
  | e :: rest => if e.scale = m - 1 then ⟨c.root, rest⟩ else c
  | [] => c

theorem compParent_root (m : ℕ) (c : Comp) : (compParent m c).root = c.root := by
  unfold compParent
  split
  · split <;> rfl
  · rfl

/-- The readout `(𝖱X)_v = ∑_𝔱 E^{η₀|𝔱|} X_{(v,𝔱)}` of fields on the components `S'` of the next
family to fields on the components `S` of the incoming family. -/
def succReadout (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp} (k : ℕ)
    (X : ∀ v' : CompIn S', TorusHk k (hr v'.1.root)) : ∀ v : CompIn S, TorusHk k (hr v.1.root) :=
  fun v => ∑ v' : CompIn S', if h : compParent m v'.1 = v.1 then
    (E ^ (η₀ * ((compWord m v'.1).length : ℝ))) •
      cast (congrArg (fun r => TorusHk k (hr r))
        ((compParent_root m v'.1).symm.trans (congrArg Comp.root h))) (X v')
    else 0

/-- `W = P Z` by duality, for the formally self-adjoint operator `P` on smooth periodic fields. -/
def IsCovImage {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] {k l : ℕ} (P : (Vec 2 → E) → Vec 2 → E) (Z : TorusHk k E)
    (W : TorusHk l E) : Prop :=
  ∀ φ : Vec 2 → E, ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
    cellInner (fun x => W.toFunction.jet (valueIndex2 l) x) φ =
      cellInner (fun x => Z.toFunction.jet (valueIndex2 k) x) (P φ)
end

/-! Definition: the common preparation of a stage, as the property of
the pair `(t_p, 𝐏_reg)` asserted by Proposition 4.3(a) of the paper, used by the successor (the
common preparation gives one quiet `t_p ≤ s + 4τ_m''` and `h = 𝐏_reg f`).

The construction of the preparation is the regularized family: the stage itself with the kernels
of its identities (`GenStage.IsRegSolution`; fresh kernels `IsFreshKernel`, inherited and
converted kernels by the provenance). The pair
`(t_p, 𝐏_reg)` is not a construction: the proposition asserts that one exists, before the datum.
`IsCommonPreparation` records its asserted properties used by the successor (the molecular
buffer at `ρ_⋆ = c₀ min{e, √(ν/a_m)}` is omitted), at the radius
`ρ = c_r √(B τ_m'')`, for both weights `w = I` and `w = d`
(the marker of the stage):
* `t_p` is quiet (`ocQuietTimes`), `s ≤ t_p ≤ s + 4τ_m''`;
* `𝐏_reg` is linear (by type) and fixes every constant component vector;
* the error `‖w(𝐏_reg f - 𝒰(t_p,s)f)‖_π ≤ C_Q E^Q ‖wf‖_π` and the model bounds
  `‖w𝐏_reg f‖_π ≤ (1 + C_Q E^Q)‖wf‖_π`, `|w𝐏_reg f|_{ρ,N_out;π} ≤ C_Q ‖wf‖_π`,
  for the regularized
  evolution `𝒰(t,s)f` (order zero, drift `𝐛_m`, diffusivity
  `κ_m`, from `s`);
* the prepared covariance bound `|wQ_p h|_{ρ,N_aux;π} ≤ C A_in` for `h = 𝐏_reg f`, `A_in ≥ ‖wf‖_π`,
  with `Q_p` at the original anchor of
  the covariance primitive (`IsCovImage`). -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The molecular radius `ρ_⋆ = c₀ min{ε_m, √(κ_m/a_m)}` of level `m`. -/
def rhoStar (D : OCData) (c₀ : ℝ) (m : ℕ) : ℝ :=
  c₀ * min (D.eps m) (Real.sqrt (D.κ m / ocA D.α D.q D.Λ m))

/-- The enhanced radius `ρ = c_r √(κ_{m-1} τ_m'')` of the passage at level `m`. -/
def rhoEnh (D : OCData) (cr : ℝ) (m : ℕ) : ℝ :=
  cr * Real.sqrt (D.κ (m - 1) * ocTauPP D.α D.q D.Λ m)

/-- The weighted mass norm `‖wX‖_{ρ,k;π} = (∑_v π_v⁻¹ w_v² |X_v|²_{ρ,k})^{1/2}`. -/
def weightedNorm {S : Finset Comp} {k : ℕ} (ρ : ℝ) (π w : CompIn S → ℝ)
    (X : ∀ v : CompIn S, TorusHk k (hr v.1.root)) : ℝ :=
  Real.sqrt (massNormSq (E := fun v : CompIn S => hr v.1.root) (K := fun _ => k) ρ
    (fun v => π v / w v ^ 2) (fun v => (X v).val))

/-- The covariance primitive `𝖧_m(t)` of level `m` with its original anchor `0`. -/
def covPrimitive (D : OCData) (m : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) 0 t

/-- The asserted properties of the common preparation `(t_p, 𝐏_reg)` of the stage `G` (level `m`)
from the start `s` on the window `[s, t_f]`. -/
def IsCommonPreparation (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm b j₀) (cr Q CQ C : ℝ)
    (p Nout Naux : ℕ) (s tf tp : ℝ)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))) : Prop :=
  tp ∈ ocQuietTimes D.α D.q D.Λ D.ζ G.level ∧ s ≤ tp ∧
    tp ≤ s + 4 * ocTauPP D.α D.q D.Λ G.level ∧
    (∀ (cv : ∀ v : CompIn G.comps, hr v.1.root) (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)),
      (∀ v, (f v).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube]
        fun _ => cv v) →
      ∀ v, (Preg f v).toFunction.jet (valueIndex2 Nout) =ᵐ[volume.restrict AVenhance.unitCube]
        fun _ => cv v) ∧
    ∀ (w : CompIn G.comps → ℝ), (w = fun _ => 1) ∨ w = G.marker law →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)),
      (∀ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
         (W : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
         (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root)),
        G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ G.level) (streamVel (D.Φ G.level)) 0 s tf f
          (fun _ _ => 0) (fun _ _ => 0) U W Y →
        weightedNorm 1 (G.mass law) w
            (fun v => truncateTorusHk (Nat.zero_le Nout) (Preg f v) - U v tp) ≤
          CQ * D.eps (G.level - 1) ^ Q * weightedNorm 1 (G.mass law) w f) ∧
      weightedNorm 1 (G.mass law) w (fun v => truncateTorusHk (Nat.zero_le Nout) (Preg f v)) ≤
        (1 + CQ * D.eps (G.level - 1) ^ Q) * weightedNorm 1 (G.mass law) w f ∧
      weightedNorm (rhoEnh D cr G.level) (G.mass law) w (Preg f) ≤
        CQ * weightedNorm 1 (G.mass law) w f ∧
      ∀ (Ain : ℝ), weightedNorm 1 (G.mass law) w f ≤ Ain →
        ∀ (Qh : ∀ v : CompIn G.comps, TorusHk Naux (hr v.1.root)),
          (∀ v, IsCovImage (covPolyQ (covPrimitive D G.level tp) p) (Preg f v) (Qh v)) →
          weightedNorm (rhoEnh D cr G.level) (G.mass law) w Qh ≤ C * Ain
end

end AVRegularity
end
