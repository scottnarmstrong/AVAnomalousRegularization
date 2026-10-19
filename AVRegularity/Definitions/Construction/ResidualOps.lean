-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.IsPointwiseMolecularEnvelope
public import AVRegularity.Definitions.Construction.ScheduleFloor
public import AVRegularity.Statements.Intermediate.CycleOutput.GluedLift
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep
public import AVRegularity.Statements.Intermediate.CycleOutput.ObsErrorNorm
public import AVRegularity.Statements.Intermediate.CycleComparison.ResidualNorm
public import AVRegularity.Statements.Intermediate.Families.ChartedFiber
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
public import AVRegularity.Statements.Intermediate.CycleOutput.OcObsPulses

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! Seed carrier of the pointwise molecular envelope.

The first passage of the cascade prepares the supplied seed itself (`IsCascadeStage.seed`,
`iteration_passage` and `preservation_successor` at `m = n`). Its common preparation applies
`cycle_joint` to the seed, and `cycle_joint` carries the pointwise molecular premise `hpointwise`.
`IsGeneratedSeed` supplies only the essential envelopes (clause 2 of
`IsStageInvariant`), and the pointwise molecular bound of a general seed does not follow from its
context certificate: its record must also dominate its supplied independent molecular envelope at
the seed radius, with the same positive entry matrix, and this is an input for a general seed,
since `R_γ ≤ ε_n` does not imply `R_γ ≤ ρ_*`. At the seed the forward conclusions use its
supplied molecular envelope; descendant bounds follow from the construction. The supremum of the
construction is pointwise in time, so the supplied envelope is the pointwise one.

`IsSeedPointwiseMolecular` is exactly the pointwise form of the molecular half of the seed's own
essential envelope clause (`IsStageInvariant` at `kS` on `[tS, tf]`): the same family, masses,
orders, inner domain, scales, radius, constants `kS.Cm`, order `kS.Jm` and record matrix. It is a
hypothesis of the cascade statements and a conclusion of the terminal seed clauses. The marked
family and the analytic envelope are not carried. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The supplied pointwise molecular envelope of the seed at its own constants `kS` on `[tS, tf]`:
the pointwise form of the molecular half of the seed's essential envelope clause. -/
def IsSeedPointwiseMolecular (law : BirthLaw) (kS : InvConsts) (seed : GenStage D hr Dm b j₀)
    (tS tf : ℝ) : Prop :=
  ∀ K : CompIn seed.comps → ℕ, (∀ v, K v ≤ kS.Ks) →
    IsPointwiseMolecularEnvelope seed.fam (seed.mass law) K
      (seed.innerDomain (Set.Icc tS tf) kS.mEnv)
      (D.kap seed.level) (D.eps seed.level) (D.eps (seed.level - 1))
      (rhoStar D kS.c₀ seed.level) kS.Cm kS.Jm (recordMajorant (seed.mass law) seed.fam)

end AVRegularity
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! Definition: the clauses of the conclusion of `preservation_successor`,
as named predicates on the incoming stage `G` (level `m`),
the retained next stage `Gr = Π G'` (level `m-1`) and the seed.

* `NextFamilyClauses`: generated membership of the next family; the kernel-priced action
  (`kernelSchurMatrix`) at most `1/8` at the enhanced radius in both weights; total mass at most
  twice the seed's root mass; the readout norm `‖𝖱‖ ≤ 1 + √T_w E^{η₀+η_b/2}`. The next-stage
  invariant is `stage_invariant_propagation`.
* `IsLiftedField`: the shared lifted field `û = 𝒯P_pZ`.
* `IsRetainedTrace`: `Y_{v,∅}(t_p) = Q_p(t_p)h_v` (duality), zero elsewhere.
* `RetainedSolutionClauses`: existence of the genuine energy solution of the retained system at the
  order `k`, uniqueness, the energy contraction in both weights and the marked `L²` bound.
* `ComparisonClauses`: a lifted field exists, and every lifted field solves the actual regularized
  incoming equation with a residual presentation of size `≤ resBound`, and the error bound for
  `U - û`. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The conclusions on the retained next family `Gr` of the passage `m → m-1`: generated
membership, the kernel-priced action at most `1/8` at the enhanced radius in both weights,
the mass bound, and the readout norm. The next-stage invariant (envelopes, ledger, certificates,
widths, quiet matching) is **not** asserted here at the incoming constants: it is the conclusion of
`stage_invariant_propagation`, whose constants are chosen there. -/
def NextFamilyClauses (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (k : InvConsts) (seed G Gr : GenStage D hr Dm b j₀) (m : ℕ) (η₀ : ℝ) (Kres Tw : ℕ)
    (tp tf : ℝ) : Prop :=
  Gr.IsGenerated ∧
    (∀ kk ≤ Kres, ∀ w : CompIn Gr.comps → ℝ, (w = fun _ => 1) ∨ w = Gr.marker law →
      SchurBound (1 / 8) (kernelSchurMatrix (ι := CompIn Gr.comps) (h := fun v => hr v.1.root)
        (Γ := Gr.fam.Γ) (G := fun _ u _ => hr u.1.root) (D.κ (m - 1)) (rhoEnh D k.cr m)
        (fun v => Gr.mass law v / w v ^ 2) kk Dm tp tf k.cker
        (fun v u γ => (Gr.kernelOf P seedK freshK v u γ).width)
        (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
        (fun v u γ d => Gr.physCoeff v u γ d.1))) ∧
    ∑ v, Gr.mass law v ≤ 2 * ∑ v, seed.mass law v ∧
    ∀ (kk : ℕ) (X : ∀ v' : CompIn Gr.comps, TorusHk kk (hr v'.1.root)),
      weightedNorm (rhoEnh D k.cr m) (G.mass law) (fun _ => 1)
          (succReadout m (D.eps (m - 1)) η₀ kk X) ≤
        (1 + Real.sqrt (Tw : ℝ) * D.eps (m - 1) ^ (η₀ + η₀ / 4)) *
          weightedNorm (rhoEnh D k.cr m) (Gr.mass law) (fun _ => 1) X

/-- The trace of the retained system: `Q_p(t_p)h` on the incoming components, zero on new words. -/
def IsRetainedTrace (G Gr : GenStage D hr Dm b j₀) (m p : ℕ) (tp : ℝ) {Nh k : ℕ}
    (h : ∀ v : CompIn G.comps, TorusHk Nh (hr v.1.root))
    (Y0 : ∀ v' : CompIn Gr.comps, TorusHk k (hr v'.1.root)) : Prop :=
  (∀ v' (hv : v'.1 ∈ G.comps), IsCovImage (covPolyQ (covPrimitive D m tp) p) (h ⟨v'.1, hv⟩) (Y0 v')) ∧
    ∀ v', v'.1 ∉ G.comps → Y0 v' = 0

/-- The retained system at the order `k`: existence, uniqueness, energy contraction in both
weights, and the marked `L²` bound. -/
def RetainedSolutionClauses (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (Gr : GenStage D hr Dm b j₀) (m k : ℕ)
    (cr C Q Ain tp tf : ℝ) (Y0 : ∀ v' : CompIn Gr.comps, TorusHk k (hr v'.1.root)) : Prop :=
  (∃ (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk k (hr v.1.root))
      (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)),
    Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) k tp tf Y0
      (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk) ∧
  ∀ (Y Y' : ∀ v : CompIn Gr.comps, ℝ → TorusHk k (hr v.1.root))
    (Yw Yw' : ∀ v : CompIn Gr.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Yk Yk' : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)),
    Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) k tp tf Y0
      (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) k tp tf Y0
      (fun _ _ => 0) (fun _ _ => 0) Y' Yw' Yk' →
    (∀ v, ∀ t ∈ Set.Icc tp tf, Y v t = Y' v t) ∧
    ∀ w : CompIn Gr.comps → ℝ, (w = fun _ => 1) ∨ w = Gr.marker law →
      ∀ t ∈ Set.Icc tp tf,
        weightedNorm (rhoEnh D cr m) (Gr.mass law) w (fun v => Y v t) ^ 2
            + 5 * D.κ (m - 1) / 4 * ∫ τ' in Set.Icc tp t,
              massGradNormSq (E := fun v : CompIn Gr.comps => hr v.1.root) (K := fun _ => k)
                (rhoEnh D cr m) (fun v => Gr.mass law v / w v ^ 2) (fun v => (Yw v τ').val)
          ≤ weightedNorm (rhoEnh D cr m) (Gr.mass law) w Y0 ^ 2 ∧
        weightedNorm (rhoEnh D cr m) (Gr.mass law) w Y0 ≤ C * Ain ∧
        weightedNorm 1 (Gr.mass law) (Gr.marker law)
            (fun v => truncateTorusHk (Nat.zero_le k) (Y v t)) ≤
          (1 + C * (D.eps (m - 1) ^ Q + D.eps (m - 1) ^ ocDelta D.α D.q)) * Ain

/-- The lifted field `û = 𝒯P_pZ`, `Z = 𝖱Y`, at the order `K` (shared by the comparison, the
initial value, the full-lift bound and the residual identities): the lift
coefficients `CcT` of the actual pulse-local lift of the incoming family (the relation
`IsLiftSequence` of its Hilbert fiber on the native chart of every pulse, from the original start
`inf J_k`), the duality image `PZ = P_pZ` with its classical representative `aRep`, and
`û` whose value is the glued Eulerian lift of `aRep` on the window. -/
def IsLiftedField (G Gr : GenStage D hr Dm b j₀) (m p Naux N depth sX sZ : ℕ) (η₀ tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root)) {K : ℕ}
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (û : ∀ v : CompIn G.comps, ℝ → TorusHk K (hr v.1.root)) : Prop :=
  (∀ (k : ℤ) (hk : Odd k),
    IsLiftSequence (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      sX sZ (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N depth (CcT k)) ∧
  (∀ v, ∀ t ∈ Set.Icc tp tf,
    IsCovImage (covPolyP (covPrimitive D m t) p)
      (succReadout m (D.eps (m - 1)) η₀ Naux (fun v' => Y v' t) v) (PZ v t) ∧
    IsClassicalRep (PZ v t) (fun x => aRep t x v) (Naux - 2 * p)) ∧
  ∀ v, ∀ t ∈ Set.Icc tp tf,
    (û v t).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => gluedLift (ocObsPulses D.α D.q D.Λ m t t) (fun k => ocCutoff D.α D.q D.Λ m k)
        (D.cellScaleSq m) (liftLength D m) (D.eps m)
        (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / liftLength D m) N depth CcT
        (fun k s' y => D.flowOf (m - 1) s' y (D.slotAnchor m k))
        (fun k s' y => D.flowOf (m - 1) (D.slotAnchor m k) y s') aRep t x v

/-- The physical comparison of the retained system with the actual regularized incoming solution,
with the bounds `resBound` on the residual presentation and `errBound` on the error: the lifted
field exists, and every lifted field (unique by `lift_sequence_unique` and the classical
representative) has a residual presentation in the actual regularized incoming equation and the
error bound. -/
def ComparisonClauses (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr : GenStage D hr Dm b j₀) (m p Naux N depth sX sZ : ℕ)
    (η₀ s₀ tp tf resBound errBound : ℝ) (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root)) : Prop :=
  (∃ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (û : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root)),
    IsLiftedField G Gr m p Naux N depth sX sZ η₀ tp tf Y CcT PZ aRep û) ∧
  ∀ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root)),
    G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) 0 s₀ tf f
      (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (û : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root)),
      IsLiftedField G Gr m p Naux N depth sX sZ η₀ tp tf Y CcT PZ aRep û →
      ∃ (ŵ : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
        (ŷ : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root))
        (Rres : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
        (qres : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root)),
        G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) 0 tp tf
          (fun v => û v tp) Rres qres û ŵ ŷ ∧
        residualNorm (D.κ m) (G.mass law) (Set.Icc tp tf)
            (fun t x k v => ((Rres v t).toFunction.jet (valueIndex2 0) x) k)
            (fun t x v => (qres v t).toFunction.jet (valueIndex2 0) x) ≤
          ENNReal.ofReal resBound ∧
        obsErrorNorm (D.κ m) (G.mass law) (fun _ => 0) tp tf (fun v t => U v t - û v t)
            (fun v t => Uw v t - ŵ v t) ≤
          ENNReal.ofReal errBound
end

/-! Definition: objects of the displays of
`preservation_successor` omitted from its statement, for their separate statements.

* `omittedFlux G' K yom isRet v t x`: the flux `F_om = (I - Π)𝖠^S Y` into a component `v` of the
  extended family from the retained components (`isRet`), with the kernel-lifted inputs `yom`
  (`∇^{d-1} S_γ Y_u` as jets), Y extended by zero.
* `readoutFlux m E η₀ sel F`: `(𝖱F)_v = ∑_{(v,𝔱) selected} E^{η₀|𝔱|} F_{(v,𝔱)}` into the incoming
  components (`sel` selects the grade-`H+1` rows for `F_gr`, the grade-`≤ H`, length-`J+1` rows for
  `F_len`).
* `succBill`: the bill of the successor,
  `E^{-qγ}[ω^p + ω^{p+1} + ε_o^{L_c} + E^{ιΣ_H} + E^{θ₁+Jθ₂}] + ε_c^N(1 + Z_cl)
   + ℓ√(B_tr/τ_m) e^{-cτ_m/ℓ²} + ε_f^{L_f}`, with `ε_c = d_*/ρ`, `ω = ‖𝖧‖_∞/ρ²` (entrywise `ℓ¹`
  norm of the covariance primitive), `Z_cl = √|W| ℓ^{-1}(e/ρ)^{A_cl}`,
  `ε_o = max{E^{σ₀}, max_γ r_γ/ρ}`, `ε_f = max_γ r_γ/ρ_⋆` over the incoming identities, and
  `B_tr = 1 + |W|/τ_m` (`B_tr ≤ C(1 + |W|/τ_m)`, the constant absorbed in `C`). -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The flux `(I - Π)𝖠^S Y` into the component `v` of the extended family `G'`, from the retained
components, with the kernel-lifted inputs `yom` at the common order `k`. -/
def omittedFlux (G' : GenStage D hr Dm b j₀) (k : ℕ) (isRet : Comp → Prop)
    (yom : ∀ v u (_ : G'.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (v : CompIn G'.comps) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  ∑ u : CompIn G'.comps, if isRet u.1 then
    ∑ γ : G'.fam.Γ v u, ∑ d : Finset.Icc 2 Dm,
      G'.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (yom v u γ t).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x)
    else 0

open scoped Classical in
/-- The readout `(𝖱F)_v = ∑ E^{η₀|𝔱|} F_{(v,𝔱)}` of the selected rows of a flux on the components
`S'` to the incoming components `S`. -/
def readoutFlux (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp} (sel : Comp → Prop)
    (F : ∀ v' : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v'.1.root)) :
    ∀ v : CompIn S, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  fun v t x => ∑ v' : CompIn S', if h : compParent m v'.1 = v.1 ∧ sel v'.1 then
    (E ^ (η₀ * ((compWord m v'.1).length : ℝ))) •
      cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r))
        ((compParent_root m v'.1).symm.trans (congrArg Comp.root h.1))) (F v' t x)
    else 0

/-- The bill of the successor at the passage `m`, for the incoming stage `G`, the
window `[tp, tf]` and the constant `c`: the explicit bound on the residual of the lift
(Proposition 12.11 of the paper). -/
def succBill (D : OCData) (G : GenStage D hr Dm b j₀) (m : ℕ) (c₀ cr c σ₀ η₀ : ℝ)
    (p N Lc Lf Acl J H : ℕ) (tp tf : ℝ) (θ₁ θ₂ : ℝ) : ℝ :=
  let E := D.eps (m - 1)
  let ρ := rhoEnh D cr m
  let ℓ := Real.sqrt (D.cellScaleSq m)
  let ω := (⨆ t : Set.Icc tp tf, ∑ a : Fin 2, ∑ a' : Fin 2, |covPrimitive D m t a a'|) / ρ ^ 2
  let εc := ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / ρ
  let Zcl := Real.sqrt (tf - tp) / ℓ * (D.eps m / ρ) ^ Acl
  let εo := max (E ^ σ₀) (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
    (G.fam.identity v u γ).record.width / ρ)
  let εf := ⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
    (G.fam.identity v u γ).record.width / rhoStar D c₀ m
  E ^ (-(D.q * ocGamma D.α D.q)) *
      (ω ^ p + ω ^ (p + 1) + εo ^ Lc + E ^ (η₀ / 8 * succSigmaH D.q H) + E ^ (θ₁ + J * θ₂)) +
    εc ^ N * (1 + Zcl) +
    ℓ * Real.sqrt ((1 + (tf - tp) / ocTau D.α D.q D.Λ m) / ocTau D.α D.q D.Λ m) *
      Real.exp (-(c * ocTau D.α D.q D.Λ m / ℓ ^ 2)) +
    εf ^ Lf
end

/-! Definition: the clauses of the full-lift
bound at the order `k` (`k + N + 2p ≤ N_aux`) (Proposition 12.10(ii) of the paper), as a named
predicate, so that the statements that use it do not unfold the clauses inline.

* `readoutEnergy`: `𝓔^B_{ρ,k+N+2p;π}(wZ;W)` of `Z = 𝖱Y` truncated to the order `k + N + 2p`, with
  gradient representative the readout of `Y_w`.
* `FullLiftClauses`: a lifted field of order `k` with its gradient representative exists, and every
  such lifted field satisfies `𝓔^ν_{ρ⋆,k;π}(wTP_pZ;W) ≤ C_k 𝓔^B_{ρ,k+N+2p;π}(wZ;W) ≤ C_k A_in`
  for `w = 1` and `w = d`. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- `𝓔^B_{ρ,K;π}(wZ;W)`, `Z = 𝖱Y` truncated to the order `K ≤ N_aux`. -/
def readoutEnergy (law : BirthLaw) (G Gr : GenStage D hr Dm b j₀) (m : ℕ) (η₀ ρ : ℝ) {Naux K : ℕ}
    (hK : K ≤ Naux) (w : CompIn G.comps → ℝ) (tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root)) : ENNReal :=
  strongEnergy ρ (D.κ (m - 1)) (fun v => G.mass law v / w v ^ 2) tp tf
    (fun v t => truncateTorusHk hK (succReadout m (D.eps (m - 1)) η₀ Naux (fun v' => Y v' t) v))
    (fun v t => truncateTorusHk (Nat.succ_le_succ hK)
      (succReadout m (D.eps (m - 1)) η₀ (Naux + 1) (fun v' => Yw v' t) v))

/-- The lifted field `û` of order `k` with gradient representative `ŵ`. -/
def IsLiftedFieldW (G Gr : GenStage D hr Dm b j₀) (m p Naux N depth sX sZ : ℕ) (η₀ tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root)) {k : ℕ}
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (û : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (ŵ : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root)) : Prop :=
  IsLiftedField G Gr m p Naux N depth sX sZ η₀ tp tf Y CcT PZ aRep û ∧
    ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc tp tf)), truncateTorusHk (Nat.le_succ k) (ŵ v t) = û v t

/-- The clauses of the full-lift bound at the order `k`. -/
def FullLiftClauses (law : BirthLaw) (G Gr : GenStage D hr Dm b j₀) (m p Naux N depth sX sZ k : ℕ)
    (hk : k + N + 2 * p ≤ Naux) (η₀ c₀ cr tp tf Ck Ain : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root)) : Prop :=
  (∃ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (û : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
      (ŵ : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root)),
    IsLiftedFieldW G Gr m p Naux N depth sX sZ η₀ tp tf Y CcT PZ aRep û ŵ) ∧
  ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (û : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (ŵ : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root)),
    IsLiftedFieldW G Gr m p Naux N depth sX sZ η₀ tp tf Y CcT PZ aRep û ŵ →
    ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = G.marker law →
      strongEnergy (rhoStar D c₀ m) (D.κ m) (fun v => G.mass law v / w v ^ 2) tp tf û ŵ ≤
          ENNReal.ofReal Ck * readoutEnergy law G Gr m η₀ (rhoEnh D cr m) hk w tp tf Y Yw ∧
        readoutEnergy law G Gr m η₀ (rhoEnh D cr m) hk w tp tf Y Yw ≤ ENNReal.ofReal (Ck * Ain)
end

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Analysis.Convolution
namespace AVRegularity

/-! Definition: the classical objects of the
residual identities, on classical representatives.

* `KernelSpec.applyClassical`: `S(t)f(y) = ∫∫ 𝗄(z)𝗄(z') f(y - rH₁(t)z - rH₂(t)z') dz dz'` on a
  classical field (the same kernel as `KernelSpec.op`).
* `pulseMeanFluxEuler`: the Eulerian flux of the grade-`r` degree-`n` mean of one pulse,
  `DΦ(y) · (-ℓ^{-2}ε_c^nρ) P₀(liftFluxX)(t/ℓ², y/ρ)` at the label `y = Φ⁻¹(t,x)` of the natural chart
  `Φ` (the Piola pushforward of the label flux).
* `meanFluxE`: the inherited-source mean flux `𝐄^flux = ∑_k ϖ_k ∑_{r=1}^{depth} ∑_{n=2}^{N+D}` of
  the actual pulse-local lifts `CcT`.
* `diagFluxPhys`: the diagonal flux `𝓕_A = (K_2 - 𝖩_m∇) + ∑_{n=3}^{N+1} K_n` from the grade-zero
  means (physical form).
* `temporalFlux`: `𝒟 = ∑_{l=1}^p (1/l!) ∑_{a<l} 𝒞^a𝒥_H𝒞^{l-1-a} - 𝓕_AP_p`,
  `𝒥_H = -(D𝐛 H + H D𝐛ᵀ)∇` (the flux `𝓕_p` of the temporal conjugation, Lemma 12.7 of the
  paper).
* `rootFluxDefect`, `omittedFluxClassical`: the fluxes of the copies and letters from the roots on
  `(I - S)Z`, and `(I - Π)𝖠^SY`, on classical representatives.
All operators act on classical fields; time-only polynomials act componentwise; no kernel is
commuted past its coefficient. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The moving paired kernel on a classical field. -/
def KernelSpec.applyClassical (φ₀ : Vec 2 → ℝ) (S : KernelSpec) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (t : ℝ) (f : Vec 2 → E) : Vec 2 → E :=
  fun y => ∫ z, momentKernel φ₀ S.order z • ∫ z', momentKernel φ₀ S.order z' •
    f (y - S.width • S.H₁ t z - S.width • S.H₂ t z')

/-- The Eulerian flux of the grade-`r` degree-`n` mean of one pulse with chart `chart` and inverse
`label`, at `(t, x)`, component `v`. -/
def pulseMeanFluxEuler {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ} (c ρ εc : ℝ) (n r : ℕ) (Q : LiftOperatorData ι h Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (x : Vec 2) (v : ι) : Fin 2 → h v :=
  fun j => ∑ k : Fin 2, jacMatrix (chart t) (label t x) j k •
    ((-(c⁻¹ * εc ^ n * ρ)) • fieldCellMean (fun z =>
      liftFluxX Q Cc (fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) r n (c⁻¹ * t)
        (ρ⁻¹ • label t x) z k) v)

/-- The glued Eulerian mean flux of the grades `r ∈ rs` and degrees `n ∈ ns` of the incoming family
`G` at level `m`, from the pulse lifts `CcT`. -/
def gluedMeanFlux (G : GenStage D hr Dm b j₀) (m : ℕ) (rs ns : Finset ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (v : CompIn G.comps) : Fin 2 → hr v.1.root :=
  ∑ k ∈ ocObsPulses D.α D.q D.Λ m t t, ∑ r ∈ rs, ∑ n ∈ ns,
    if hk : Odd k then
      ocCutoff D.α D.q D.Λ m k t • pulseMeanFluxEuler (D.cellScaleSq m) (liftLength D m)
        (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / liftLength D m) n r
        (familyLiftData D m k (nativeChain m k) (liftLength D m)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k)
        (fun s' y => D.flowOf (m - 1) s' y (D.slotAnchor m k))
        (fun s' y => D.flowOf (m - 1) (D.slotAnchor m k) y s') a t x v
    else 0

/-- The inherited-source mean flux `𝐄^flux` (grades `1..depth`, degrees `2..N+Dm`). -/
def meanFluxE (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (v : CompIn G.comps) : Fin 2 → hr v.1.root :=
  gluedMeanFlux G m (Finset.Icc 1 depth) (Finset.Icc 2 (N + Dm)) CcT a t x v

/-- The gradient of a classical field, as a flux. -/
def gradE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Vec 2 → E) (x : Vec 2) :
    Fin 2 → E :=
  fun j => fderiv ℝ f x (basisVec j)

/-- The divergence of a classical flux. -/
def divE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Vec 2 → Fin 2 → E)
    (x : Vec 2) : E :=
  ∑ j : Fin 2, fderiv ℝ (fun y => F y j) x (basisVec j)

/-- The physical diagonal flux `𝓕_A g = (K_2 g - 𝖩_m∇g) + ∑_{n=3}^{N+1} K_n g`. -/
def diagFluxPhys (G : GenStage D hr Dm b j₀) (m N : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (v : CompIn G.comps) : Fin 2 → hr v.1.root :=
  gluedMeanFlux G m {0} (Finset.Icc 2 (N + 1)) CcT a t x v -
    fun j => ∑ l : Fin 2, ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t j l •
      gradE (fun y => a t y v) x l

/-- `𝒥_H g = -(D𝐛 H + H D𝐛ᵀ)∇g` on a classical field. -/
def commFluxE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (bv : Vec 2 → Vec 2)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (g : Vec 2 → E) (x : Vec 2) : Fin 2 → E :=
  fun j => -(∑ l : Fin 2, (jacMatrix bv x * Hc + Hc * Matrix.transpose (jacMatrix bv x)) j l •
    gradE g x l)

/-- The temporal flux `𝒟 = ∑_{l=1}^p (1/l!) ∑_{a<l} 𝒞^a𝒥_H𝒞^{l-1-a} - 𝓕_A P_p` applied to
the classical field `a` at time `t`, component `v`. -/
def temporalFlux (G : GenStage D hr Dm b j₀) (m N p : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (v : CompIn G.comps) :
    Vec 2 → Fin 2 → hr v.1.root :=
  fun x => (∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a' ∈ Finset.range l,
      (covOperator (covPrimitive D m t))^[a'] (commFluxE (streamVel (D.Φ (m - 1)) t)
        (covPrimitive D m t) ((covOperator (covPrimitive D m t))^[l - 1 - a'] (fun y => a t y v))) x) -
    diagFluxPhys G m N CcT (fun s y w => covPolyP (covPrimitive D m s) p (fun y' => a s y' w) y) t x v

open scoped Classical in
/-- The flux `∑_{u,γ} 𝖡_γ ∇^{d-1}(I - S_γ)Z_u` of the identities of the extended family `G'` from
the incoming components (the roots `(u, ∅)`) into `v'`, on a classical representative `aZ` of `Z`. -/
def rootFluxDefect (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' : GenStage D hr Dm b j₀) (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v' : CompIn G'.comps) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v'.1.root) :=
  ∑ u' : CompIn G'.comps, if hu : u'.1 ∈ G.comps then
    ∑ γ : G'.fam.Γ v' u', ∑ d : Finset.Icc 2 Dm,
      G'.physCoeff v' u' γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word (fun y => aZ t y ⟨u'.1, hu⟩ -
          (G'.kernelOf P seedK freshK v' u' γ).applyClassical φ₀ t (fun y' => aZ t y' ⟨u'.1, hu⟩) y) x)
    else 0

open scoped Classical in
/-- The omitted flux `(I - Π)𝖠^SY` into `v` from the retained components, on a classical
representative `aY` of `Y` (extended by zero). -/
def omittedFluxClassical (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G' Gr : GenStage D hr Dm b j₀) (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root)
    (v : CompIn G'.comps) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  ∑ u : CompIn G'.comps, if hu : u.1 ∈ Gr.comps then
    ∑ γ : G'.fam.Γ v u, ∑ d : Finset.Icc 2 Dm,
      G'.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word ((G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t
          (fun y => aY t y ⟨u.1, hu⟩)) x)
    else 0
end

/-! Definition: the fields of the residual identities on
classical representatives, for the incoming stage `G` (level `m`), its actual extended successor
`G'`, the retained family `Gr`, the readout `Z = 𝖱Y` (classical representative `aZ`), the retained
solution (classical representative `aY`), `P_pZ` (classical representative `aRep`) and the lift
coefficients `CcT`.

* `liftedRep`: `TP_pZ`, the glued Eulerian lift of `aRep` (the same `gluedLift` as `IsLiftedField`).
* `upsilonFlux`: `Υ = ∑ 𝖮_γ(I - S_γ)Z + ∑ 𝖥_{𝔩,γ}(I - S_m)Z + 𝖱F_om` (the readout of the root
  fluxes of `G'` on `(I - S)Z`, all rows, and of the omitted flux `F_om = (I - Π)𝖠^SY` on the
  **omitted rows only**, `¬ IsRetained m H J`: grade `H+1` or length `J+1`, the rows of
  `successor_frontier_bounds`).
* `gFlux`: `G = (𝒟 - 𝐄^flux P_p)Z`.
* `meanFluxF`: `F_mean = (I - P_pQ_p)G - P_pΥ - (𝖩 - BI)∇(𝒞^p/p!)Z`.
* `fineFluxF`: `F_fine = ∑ 𝖠_{m,γ}(I - S_γ)(TP_pZ)`.
* `macroFlux`: the flux of `MI - 𝐄` on a classical field: `𝖩∇g + 𝓕_A g + 𝐄^flux g` (with
  `M = ∂_t + 𝐛_{m-1}·∇ - div(𝖩∇ + 𝓕_A)`, the grade-zero means).
* `physRes`: `𝓡_phys P_pZ = (𝓛_m I - div 𝖠_m)TP_pZ - T(MI - 𝐄)P_pZ` on classical fields, with
  a.e. time-derivative representatives (`IsTimeDerivRep`), never the pointwise `deriv`.
Time-only polynomials act on classical fields; a kernel is never commuted past its coefficient. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- `T g` for a classical field `g` on the incoming components: the glued Eulerian lift. -/
def liftedRep (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root :=
  fun t x => gluedLift (ocObsPulses D.α D.q D.Λ m t t) (fun k => ocCutoff D.α D.q D.Λ m k)
    (D.cellScaleSq m) (liftLength D m) (D.eps m)
    (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / liftLength D m) N depth CcT
    (fun k s' y => D.flowOf (m - 1) s' y (D.slotAnchor m k))
    (fun k s' y => D.flowOf (m - 1) (D.slotAnchor m k) y s') g t x

/-- `P_p(t)` on a classical field (original covariance anchor). -/
def covPRep (D : OCData) (m p : ℕ) {S : Finset Comp} (g : ℝ → Vec 2 → ∀ v : CompIn S, hr v.1.root) :
    ℝ → Vec 2 → ∀ v : CompIn S, hr v.1.root :=
  fun t y v => covPolyP (covPrimitive D m t) p (fun y' => g t y' v) y

/-- A classical flux as a `PiLp` field. -/
def toFluxL {E : Type*} (F : Fin 2 → E) : PiLp 2 (fun _ : Fin 2 => E) := WithLp.toLp 2 F

/-- `Υ` on the incoming components. -/
def upsilonFlux (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' Gr : GenStage D hr Dm b j₀) (m H J : ℕ) (E η₀ : ℝ)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  readoutFlux m E η₀ (fun _ => True)
      (fun v' s y => rootFluxDefect P seedK freshK φ₀ G G' aZ v' s y) v t x +
    readoutFlux m E η₀ (fun c => ¬ IsRetained m H J c)
      (fun v' s y => omittedFluxClassical P seedK freshK φ₀ G' Gr aY v' s y) v t x

/-- `G = (𝒟 - 𝐄^flux P_p)Z`. -/
def gFlux (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : Fin 2 → hr v.1.root :=
  temporalFlux G m N p CcT aZ t v x - meanFluxE G m N depth CcT (covPRep D m p aZ) t x v

/-- `F_mean = (I - P_pQ_p)G - P_pΥ - (𝖩 - BI)∇(𝒞^p/p!)Z`, with `Υ` given. -/
def meanFluxF (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (Υ : ∀ v : CompIn G.comps, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v.1.root))
    (v : CompIn G.comps) (t : ℝ) (x : Vec 2) : Fin 2 → hr v.1.root :=
  (gFlux G m N p depth CcT aZ v t x -
      covPolyP (covPrimitive D m t) p
        (covPolyQ (covPrimitive D m t) p (fun y => gFlux G m N p depth CcT aZ v t y)) x) -
    covPolyP (covPrimitive D m t) p (fun y => WithLp.ofLp (Υ v t y)) x -
    fun j => ∑ l : Fin 2, (ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t - D.κ (m - 1) • 1) j l •
      gradE (fun y => ((p.factorial : ℝ)⁻¹) •
        (covOperator (covPrimitive D m t))^[p] (fun y' => aZ t y' v) y) x l

/-- The kernel mode of a coefficient flux: no kernel, the kernel `S_γ`, or the defect `I - S_γ`. -/
inductive KerMode | plain | kernel | defect

/-- The flux `∑_{u,γ,d} 𝖠_{v u γ d}(t,x)∇^{d-1}(K_γ g_u)` of the incoming family on a classical
field `g`, with `K_γ = I`, `S_γ` or `I - S_γ` according to the mode. -/
def coeffFluxOn (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G : GenStage D hr Dm b j₀) (mode : KerMode) (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  ∑ u : CompIn G.comps, ∑ γ : G.fam.Γ v u, ∑ d : Finset.Icc 2 Dm,
    G.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      orderedDerivative word (fun y =>
        match mode with
        | .plain => g t y u
        | .kernel => (G.kernelOf P seedK freshK v u γ).applyClassical φ₀ t (fun y' => g t y' u) y
        | .defect => g t y u - (G.kernelOf P seedK freshK v u γ).applyClassical φ₀ t
            (fun y' => g t y' u) y) x)

/-- `F_fine = ∑ 𝖠_{m,γ}(I - S_γ)(TP_pZ)`. -/
def fineFluxF (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G : GenStage D hr Dm b j₀) (uh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  coeffFluxOn P seedK freshK φ₀ G .defect uh v t x

/-- The flux of `MI - 𝐄` beyond `B∇g`, in the form used by the weak identity with diffusivity
`B = κ_{m-1}`: `(𝖩 - BI)∇g + 𝓕_A g + 𝐄^flux g`, where `𝓕_A = (K_2 - 𝖩∇) + ∑_{n≥3} K_n`. -/
def macroFlux (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : Fin 2 → hr v.1.root :=
  (fun j => ∑ l : Fin 2, (ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t - D.κ (m - 1) • 1) j l •
      gradE (fun y => g t y v) x l) +
    diagFluxPhys G m N CcT g t x v + meanFluxE G m N depth CcT g t x v

/-- `dg` is an a.e.-in-time derivative representative of `g` on the window `W`: for a.e. `t ∈ W`
and every `x`, `s ↦ g s x` has derivative `dg t x` at `t` (the residual is
used only under the time integral, so any such representative gives the same identity). -/
def IsTimeDerivRep {S : Finset Comp} (W : Set ℝ) (g dg : ℝ → Vec 2 → ∀ v : CompIn S, hr v.1.root) :
    Prop :=
  ∀ᵐ t ∂(volume.restrict W), ∀ x, HasDerivAt (fun s => g s x) (dg t x) t

/-- `(MI - 𝐄)g = ∂_t g + 𝐛_{m-1}·∇g - div(B∇g + macroFlux g)` on a classical field, with the
time-derivative representative `dg`. -/
def macroRes (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (g dg : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2) :
    ∀ v : CompIn G.comps, hr v.1.root :=
  fun v => dg t x v +
    ∑ j : Fin 2, streamVel (D.Φ (m - 1)) t x j • gradE (fun y => g t y v) x j -
    divE (fun y => D.κ (m - 1) • gradE (fun y' => g t y' v) y +
      macroFlux G m N depth CcT g v t y) x

/-- `𝓡_phys P_pZ = (𝓛_m I - div 𝖠_m)TP_pZ - T(MI - 𝐄)P_pZ` on classical fields, with
`𝓛_m = ∂_t + 𝐛_m·∇ - κ_mΔ`, `div 𝖠_m` without kernels, and the a.e. time-derivative
representatives `dRep` of `P_pZ` and `dUh` of `TP_pZ` (`IsTimeDerivRep`). -/
def physRes (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aRep dRep dUh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : hr v.1.root :=
  let uh := liftedRep G m N depth CcT aRep
  (dUh t x v +
      ∑ j : Fin 2, streamVel (D.Φ m) t x j • gradE (fun y => uh t y v) x j -
      divE (fun y => D.κ m • gradE (fun y' => uh t y' v) y +
        fun j => WithLp.ofLp (coeffFluxOn P seedK freshK φ₀ G .plain
          uh v t y) j) x) -
    liftedRep G m N depth CcT (macroRes G m N depth CcT aRep dRep) t x v
end

end AVRegularity
end
end
end
