-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.PrepCore.JetFacts
import AVRegularity.CycleJoint.ConstituentPhysicalOrderSupport
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.Local
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
public import AVRegularity.Statements.Intermediate.Families.FamilyEdges

section
section
/-! **Integrability of the right-hand side of the weak identity from square integrability**.

`cwiRhs_integrable_of_memLp`: at one time, if the drift is bounded in each component and
measurable, and the gradient of the unknown, the total flux plus forcing, the scalar forcing, the
test and its gradient are square integrable on the cell, then the right-hand side of the
`CoupledWeakIdentity` is integrable. It is used at the times where the carrier is replaced by `0`.

When all the data vanish every term is `0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The right-hand side of the weak identity is integrable at a time where all data are square
integrable and the drift is bounded. -/
theorem cwiRhs_integrable_of_memLp {μ : Measure (Vec 2)} {ν : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {du : ℝ → Fin 2 → Vec 2 → H}
    {flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g : ℝ → Vec 2 → H} (s : ℝ)
    (hvm : ∀ k, AEStronglyMeasurable (fun x => v s x k) μ)
    (hvb : ∃ C : ℝ, ∀ x k, ‖v s x k‖ ≤ C) (hφ : MemLp φ 2 μ)
    (hdφ : ∀ k, MemLp (dφ k) 2 μ) (hdu : ∀ k, MemLp (du s k) 2 μ)
    (hQ : MemLp (fun x => flux s x + F s x) 2 μ) (hg : MemLp (g s) 2 μ) :
    Integrable (EntryTerminal.Ingredients.cwiRhs ν v φ dφ du flux F g s) μ := by
  obtain ⟨C, hC⟩ := hvb
  have h1 : Integrable (fun x => ∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x)) μ :=
    integrable_finsetSum _ fun k _ =>
      (CycleJointProofs.integrable_inner_of_memLp_two μ _ _ (hdu k) hφ).bdd_mul (hvm k)
        (c := C) (Filter.Eventually.of_forall fun x => hC x k)
  have h2 : Integrable (fun x => ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)) μ :=
    (integrable_finsetSum _ fun k _ =>
      CycleJointProofs.integrable_inner_of_memLp_two μ _ _ (hdu k) (hdφ k)).const_mul ν
  have hQk : ∀ k : Fin 2, MemLp (fun x => flux s x k + F s x k) 2 μ := fun k =>
    (PiLp.proj 2 (fun _ : Fin 2 => H) k : PiLp 2 (fun _ : Fin 2 => H) →L[ℝ] H).comp_memLp' hQ
  have h3 : Integrable (fun x => ∑ k : Fin 2, inner ℝ (flux s x k + F s x k) (dφ k x)) μ :=
    integrable_finsetSum _ fun k _ =>
      CycleJointProofs.integrable_inner_of_memLp_two μ _ _
        (hQk k) (hdφ k)
  have h4 : Integrable (fun x => inner ℝ (g s x) (φ x)) μ :=
    CycleJointProofs.integrable_inner_of_memLp_two μ _ _ hg hφ
  exact (((h1.neg.sub h2).sub h3).add h4)


/-- **Transfer of the coupled weak identity**: the data may change on null sets of space, the
right-hand sides agree almost everywhere in space at almost every time, and the new right-hand
side is integrable at every time. -/
theorem coupledWeakIdentity_transfer {μ : Measure (Vec 2)} {ν t₀ t : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {u₀ u₀' f f' φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {du du' : ℝ → Fin 2 → Vec 2 → H}
    {flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g g' : ℝ → Vec 2 → H}
    (h : CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du flux F g) (hu : u₀ =ᵐ[μ] u₀')
    (hf : f =ᵐ[μ] f')
    (hae : ∀ᵐ s ∂(volume.restrict (Set.Ioc t₀ t)),
      EntryTerminal.Ingredients.cwiRhs ν v φ dφ du' flux' F' g' s =ᵐ[μ]
        EntryTerminal.Ingredients.cwiRhs ν v φ dφ du flux F g s)
    (hint : ∀ s ∈ Set.Ioc t₀ t,
      Integrable (EntryTerminal.Ingredients.cwiRhs ν v φ dφ du' flux' F' g' s) μ) :
    CoupledWeakIdentity μ ν t₀ t v u₀' f' φ dφ du' flux' F' g' := by
  rw [EntryTerminal.Ingredients.coupledWeakIdentity_iff] at h ⊢
  obtain ⟨h1, h2, -, h4, h5⟩ := h
  have hu' : (fun x => inner ℝ (u₀ x) (φ x)) =ᵐ[μ] fun x => inner ℝ (u₀' x) (φ x) := by
    filter_upwards [hu] with x hx
    rw [hx]
  have hf' : (fun x => inner ℝ (f x) (φ x)) =ᵐ[μ] fun x => inner ℝ (f' x) (φ x) := by
    filter_upwards [hf] with x hx
    rw [hx]
  have hae' : (fun s => ∫ x, EntryTerminal.Ingredients.cwiRhs ν v φ dφ du' flux' F' g' s x ∂μ)
      =ᵐ[volume.restrict (Set.Ioc t₀ t)]
      fun s => ∫ x, EntryTerminal.Ingredients.cwiRhs ν v φ dφ du flux F g s x ∂μ := by
    filter_upwards [hae] with s hs
    exact integral_congr_ae hs
  refine ⟨h1.congr hu', h2.congr hf', hint, h4.congr_fun_ae hae'.symm, ?_⟩
  rw [← integral_congr_ae hu', ← integral_congr_ae hf', h5]
  exact (integral_congr_ae hae').symm


/-- Almost everywhere equal data give almost everywhere equal right-hand sides at one time. -/
theorem cwiRhs_congr_ae_at {μ : Measure (Vec 2)} {ν : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {du du' : ℝ → Fin 2 → Vec 2 → H}
    {flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g g' : ℝ → Vec 2 → H} (s : ℝ)
    (hx : ∀ᵐ x ∂μ, (∀ m, du' s m x = du s m x) ∧ flux' s x + F' s x = flux s x + F s x ∧
      g' s x = g s x) :
    EntryTerminal.Ingredients.cwiRhs ν v φ dφ du' flux' F' g' s =ᵐ[μ]
      EntryTerminal.Ingredients.cwiRhs ν v φ dφ du flux F g s := by
  filter_upwards [hx] with x ⟨h1, h2, h3⟩
  have h4 : ∀ k : Fin 2, flux' s x k + F' s x k = flux s x k + F s x k := fun k => by
    simpa using congrArg (fun z : PiLp 2 (fun _ : Fin 2 => H) => z k) h2
  simp only [EntryTerminal.Ingredients.cwiRhs, h1, h3, h4]

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The residual presentation of a lifted field: the named pieces** (generic over the stage and
the menu; shared by the cascade's `successor_residual_identities` / `SuccessorBillResidualStatement`
and the terminal `entry_terminal_residual`).

Every piece is at a menu `Mn` (the menu operators of `CovarianceTransport.Local`): the
covariance anchor `Mn.anchor` and the slow length `Mn.lenFactor · liftLength`. The cascade menu has
anchor `0` and factor `1`; the terminal menu `termMenu` has anchor `t_p` and factor `c_r`
(a menu with a different anchor requires the corresponding slow-length convention).

The third residual identity presents the lifted field `û = T P_p Z` (`menuLiftedRep Mn … aRep`) as a weak
solution of the fine operator with kernel flux, forcing flux `F_fine` and scalar source
`T div F_mean + 𝓡_phys P_pZ` (`Frame.kernelWeak`). The bills (`succBill`,
`termBill`) price this source in six groups; the pieces below are those groups:

1. **cell residual**: the pulse-local part of `𝓡_phys`,
   `∑_k ϖ_k [(𝓛_m - div𝖠_m) T_k P_pZ - T_k(MI - 𝐄)P_pZ]` (bill `ε_c^N(1 + Z_cl)`);
2. **covariance truncation** `menuCovTruncFlux`: `(I - P_pQ_p)G - (𝖩 - BI)∇(𝒞^p/p!)Z` (bill
   `ω^p`, `E^{δ p_T}`), and the **response boundary** `menuFrontierFlux`: `P_p` of the readout of
   the omitted flux on the omitted rows (grade `H+1`, length `J+1`; bill `E^{ιΣ_H} + E^{θ₁+Jθ₂}`,
   `E^{δ(R_T+1)/2}`);
3. **coarse filter tails** `menuFilterFlux`: `P_p` of the readout of the root flux defects
   `∑ 𝖮_γ(I - S_γ)Z + ∑ 𝖥_{𝔩,γ}(I - S_m)Z` (bill `ε_o^{L_c}`; fresh and old filters);
4. **fine matrix tail** `fineFluxF` on `û` (bill `ε_f^{L_f}`, `x^{χ_w + σ_w L_f}`);
5. **gluing**: `∑_k ϖ_k' T_k P_pZ`, the partition derivative (bill
   `ℓ √(B/d) e^{-cd/ℓ²}`, quiet decay through the gaps);
6. **collection**: the flux pieces enter through `T div F_mean`, presented in flux form by a
   lifted flux presentation (`T div F = div R + q` weakly at each time; the conversion is priced
   by `cycle_residual_coarse_flux`). The total presentation of `û` has the flux `F_fine + R` and
   the scalar source given by the cell residual, the gluing term and `q`.

The three flux pieces of groups 2 and 3 are defined with their bounds below. The split of `𝓡_phys`
holds for the glued time-derivative representative `gluedTimeDeriv` of `û` built from pulse-local
representatives `dT k`; the split of `F_mean` is `MenuMeanFluxSplitStatement`. On the reconstruction
route of the bounds (`IsStageRecon`) the groups 1, 5, 6 come as one existential residual pair; the
cell residual and the gluing term are the explicit form when that route is not used.

For an edge-free stage `F_fine = 0`, the root flux defects vanish, and only the covariance, cell and
gluing pieces remain. With one pulse observed at `t` and `ϖ_k(t) = 1` the gluing term vanishes
(since `ϖ_k' = 0`) and the cell residual is `𝓡_phys`. For `p = 0`, `P_p = Q_p = I` and the
covariance truncation is `-(𝖩 - BI)∇Z`. For the cascade menu (anchor `0`, factor `1`)
`menuLiftedRep` is the cascade's `liftedRep` (`menuLiftedRep_cascade`), and for the terminal menu it
is `termLiftedRep` (`menuLiftedRep_terminal`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Analysis.Convolution
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The pulse-local lift `T_k g` at the menu `Mn`: the `k`th summand of `menuLiftedRep` before its
partition weight. -/
def pulseLiftRep (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)) (k : ℤ)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root :=
  fun t x => pulsePhysicalLift (D.cellScaleSq m) (Mn.lenFactor * liftLength D m) (D.eps m)
    (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / (Mn.lenFactor * liftLength D m)) N depth (CcT k)
    (fun s' y => D.flowOf (m - 1) s' y (D.slotAnchor m k))
    (fun s' y => D.flowOf (m - 1) (D.slotAnchor m k) y s') g t x

/-- The glued time-derivative representative `∑_k (ϖ_k' T_k P_pZ + ϖ_k dT_k)` of `û`, from
pulse-local representatives `dT k` of `T_k P_pZ`. -/
def gluedTimeDeriv (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (dT : ℤ → ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root :=
  fun t x => ∑ k ∈ ocObsPulses D.α D.q D.Λ m t t,
    (deriv (ocCutoff D.α D.q D.Λ m k) t • pulseLiftRep Mn G m N depth CcT k aRep t x +
      ocCutoff D.α D.q D.Λ m k t • dT k t x)

end AVRegularity.Construction.Residual.Presentation
end
end
end

section
section
/-! **The bounds of the residual presentation: forms generic over the stage and the menu, and the
generic assembly**.

The bill of a passage (`termBill`, `succBill`) prices the residual of the lifted field
`û = T P_p Z` in the fine equation in six groups (listed above). This module fixes the
*form* in which each group is bounded, with the price a real parameter, so that the terminal bill
and the cascade bill instantiate the same statements.

**Route.**
The groups 1 (cell residual), 5 (gluing) and 6 (collection of the lifted coarse flux) are ONE
instance of the interior physical reconstruction on a window, `ReconWindowAt.physical_lift`, at the
coarse field `W = P_p Z` and the coarse flux `F_c = F_mean`. Its conclusion is not a bound on the
named classical pieces (the cell residual, the gluing term and a lifted flux presentation): it is an
EXISTENTIAL residual pair `(R, q)` of the lifted field in the plain coupled system (no kernels,
descending slots), with the total bound. Both consumers (`TerminalResidualClauses`,
`ComparisonClauses`) are existential in the residual pair, so this is what they need. The form of
that conclusion is `IsStageRecon`.
The reconstruction's equation has NO kernel (`IsCoupledWeakSolutionTorus` with the edge
coefficients): the fine matrix tail `F_fine = ∑ 𝖠_{m,γ}(I - S_γ)û` (group 4) is added to the flux
when the plain system is rewritten as the kernel system. Its form is `FineTailBound`.

The groups 2 and 3 (the three flux pieces of `F_mean`) enter the reconstruction as its coarse flux
norm `B^{-1/2}‖F_c‖_{L²(I;H_{ρ,k_c;π})}`. Their forms are `CovTruncBound`, `FrontierBound`,
`FilterBound`.

**Menu.** Every piece is at a menu `Mn`, on the menu operators
(`CovarianceTransport.Local`): the cascade menu has the covariance anchor `0` and the
slow length `liftLength`; the terminal menu has the anchor `t_p` and the slow length
`c_r·liftLength` (`termMenu`, `termLiftedRep`, `termCovPrimitive`). The three flux pieces of `F_mean`
are defined here; the other pieces are those listed above (restated at a menu).

**Norms.** All bounds are in the mass form of the reconstruction's own conclusion: a family of
torus Sobolev trajectories, square integrable in time, with
`(ν⁻¹ ∫_I ‖F‖²_{ρ,K;π})^{1/2} ≤ Y` (`FluxMassLe`) or `∫_I ‖q‖_{ρ,K;π} ≤ Y` (`ScalarMassLe`). The
bound of the square root makes `Y ≥ 0` automatic. The word clause of the consumers
(`residualNorm` of the `r^j`-scaled jets of every word of order `j ≤ k`) follows from the mass form
by `ResidualWordsOfMassStatement`.

For an edge-free stage `F_fine = 0` and `Υ = 0`, so `FineTailBound`, `FilterBound` and
`FrontierBound` hold with `Y = 0`, and the reconstruction bound has only the cell, covariance and
gluing terms. For `p = 0` one has `P_p = Q_p = I`, the covariance truncation is `-(𝖩 - BI)∇Z`
and its price is `ω⁰ = 1` times the coarse energy. For `k = 0` the word clause is the residual
norm of the value jets (the cascade's clause). For zero fields every `FluxMassLe` and
`ScalarMassLe` holds with `Y = 0`.

The realizations asked by `HasFluxBound` need the classical fluxes of class `C^{k}`, hence the
order floors of the instances. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Analysis.Convolution
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-! ### The flux pieces of the mean flux at a menu -/

/-- **Covariance truncation at a menu**: `(I - P_pQ_p)G - (𝖩 - BI)∇(𝒞^p/p!)Z` with the
covariance primitive and the lift of the menu `Mn`. -/
def menuCovTruncFlux (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : Fin 2 → hr v.1.root :=
  (menuGFlux Mn G m N p depth CcT aZ v t x -
      covPolyP (menuCovPrimitive D Mn m t) p
        (covPolyQ (menuCovPrimitive D Mn m t) p
          (fun y => menuGFlux Mn G m N p depth CcT aZ v t y)) x) -
    fun j => ∑ l : Fin 2, (ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t - D.κ (m - 1) • 1) j l •
      gradE (fun y => ((p.factorial : ℝ)⁻¹) •
        (covOperator (menuCovPrimitive D Mn m t))^[p] (fun y' => aZ t y' v) y) x l

/-- **Coarse filter tails at a menu**: `P_p` of the readout of the root flux defects of
the successor `G'`. -/
def menuFilterFlux (Mn : SuccMenu) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (G G' : GenStage D hr Dm b j₀) (m p : ℕ) (E η₀ : ℝ)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : Fin 2 → hr v.1.root :=
  covPolyP (menuCovPrimitive D Mn m t) p (fun y => WithLp.ofLp (readoutFlux m E η₀ (fun _ => True)
    (fun v' s y' => rootFluxDefect P seedK freshK φ₀ G G' aZ v' s y') v t y)) x

/-- **Response boundary at a menu**: `P_p` of the readout of the omitted flux on the
omitted rows (`¬ IsRetained m H J`). -/
def menuFrontierFlux (Mn : SuccMenu) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (G G' Gr : GenStage D hr Dm b j₀) (m p H J : ℕ) (E η₀ : ℝ)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : Fin 2 → hr v.1.root :=
  covPolyP (menuCovPrimitive D Mn m t) p (fun y => WithLp.ofLp
    (readoutFlux (S := G.comps) m E η₀ (fun c => ¬ IsRetained m H J c)
      (fun v' s y' => omittedFluxClassical P seedK freshK φ₀ G' Gr aY v' s y') v t y)) x

/-- **The split of the mean flux at a menu** (with the smoothness that the split uses: `P_p` has
order `2p`, so `C^{2p}` readouts suffice; the fields of a passage have finite order). For readouts
of class `C^{2p}` at the time `t`, `F_mean = covTrunc - filter - frontier`.

Route: the definition of `menuMeanFluxF` with `Υ = upsilonFlux` (a sum of two readouts), and the
additivity of `covPolyP` on `C^{2p}` fields (`covOperator_add`).
For `p = 0` the identity is the definition. -/
def MenuMeanFluxSplitStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (Mn : SuccMenu) (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' Gr : GenStage D hr Dm b j₀) (m N p depth H J : ℕ) (E η₀ : ℝ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ),
    ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (fun y => WithLp.ofLp (readoutFlux m E η₀ (fun _ => True)
      (fun v' s y' => rootFluxDefect P seedK freshK φ₀ G G' aZ v' s y') v t y)) →
    ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (fun y => WithLp.ofLp (readoutFlux (S := G.comps) m E η₀
      (fun c => ¬ IsRetained m H J c)
      (fun v' s y' => omittedFluxClassical P seedK freshK φ₀ G' Gr aY v' s y') v t y)) →
    ∀ x : Vec 2,
      menuMeanFluxF Mn G m N p depth CcT aZ
          (upsilonFlux P seedK freshK φ₀ G G' Gr m H J E η₀ aZ aY) v t x =
        menuCovTruncFlux Mn G m N p depth CcT aZ v t x -
          menuFilterFlux Mn P seedK freshK φ₀ G G' m p E η₀ aZ v t x -
          menuFrontierFlux Mn P seedK freshK φ₀ G G' Gr m p H J E η₀ aY v t x

/-! ### Norms and realizations -/

section Norms

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- `(ν⁻¹ ∫_I ‖F‖²_{ρ,K;π})^{1/2} ≤ Y` for a family of flux trajectories, square integrable in
time (the mass form of the flux part of a residual norm, and of `B^{-1/2}‖F_c‖_{L²(I;H_{ρ,k;π})}`
with `ν = B`). -/
def FluxMassLe {K : ι → ℕ} (ν ρ : ℝ) (π : ι → ℝ) (I : Set ℝ)
    (F : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v))) (Y : ℝ) : Prop :=
  (∀ v, MemLp (F v) 2 (volume.restrict I)) ∧
    Real.sqrt (ν⁻¹ * ∫ s in I, massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
      (K := K) ρ π (fun v => (F v s).val)) ≤ Y

/-- `∫_I ‖q‖_{ρ,K;π} ≤ Y` for a family of scalar trajectories, integrable in time (the mass form
of the scalar part of a residual norm). -/
def ScalarMassLe {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (I : Set ℝ)
    (q : ∀ v, ℝ → TorusHk (K v) (h v)) (Y : ℝ) : Prop :=
  (∀ v, Integrable (q v) (volume.restrict I)) ∧
    ∫ s in I, Real.sqrt (massNormSq (E := h) (K := K) ρ π (fun v => (q v s).val)) ≤ Y

/-- The trajectory `Fk` of order `k` realizes the classical flux `F` on the window: at every time
of the window its value jet is `F` almost everywhere on the cell (the pattern of
`successor_frontier_bounds`). -/
def IsFluxRealization (k : ℕ) (I : Set ℝ)
    (F : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (Fk : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) : Prop :=
  ∀ v, ∀ t ∈ I,
    (Fk v t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube] F v t

/-- The classical flux `F` has a realization of order `k` on the window with
`(ν⁻¹ ∫_I ‖F‖²_{ρ,k;π})^{1/2} ≤ Y`. -/
def HasFluxBound (k : ℕ) (I : Set ℝ) (ν ρ : ℝ) (π : ι → ℝ)
    (F : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) (Y : ℝ) : Prop :=
  ∃ Fk : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)),
    IsFluxRealization k I F Fk ∧ FluxMassLe (K := fun _ => k) ν ρ π I Fk Y

end Norms

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- The negative of a measurable carrier trajectory (through the continuous linear map `-id`:
the algebraic lemmas time out on the instance path of `TorusHk`). -/
theorem torusHk_aestronglyMeasurable_neg {k : ℕ} {μ : Measure ℝ} {f : ℝ → TorusHk k E}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun s => -(f s)) μ :=
  (-ContinuousLinearMap.id ℝ (TorusHk k E)).continuous.comp_aestronglyMeasurable hf

/-- `-f - g` for measurable carrier trajectories. -/
theorem torusHk_aestronglyMeasurable_neg_sub {k : ℕ} {μ : Measure ℝ} {f g : ℝ → TorusHk k E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun s => -(f s) - g s) μ :=
  (torusHk_aestronglyMeasurable_neg hf).sub hg

end Carrier

/-- **The residual clause at a common order `k`** for the pair `(-R₁ - R₂, -q)`: both members are
measurable in time, and every word of order `j ≤ k` has residual norm of its
`r^j`-scaled jets at most `X`. With `R₂ = 0` and `k = 0` it is the clause of the cascade's
`ComparisonClauses` for the pair `(-R₁, -q)`. -/
def ResidualWordsClause {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (k : ℕ) (ν r : ℝ) (π : ι → ℝ) (I : Set ℝ)
    (R₁ R₂ : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (q : ∀ v, ℝ → TorusHk k (h v)) (X : ℝ) : Prop :=
  (∀ v, AEStronglyMeasurable (fun t => -(R₁ v t) - R₂ v t) (volume.restrict I)) ∧
  (∀ v, AEStronglyMeasurable (fun t => -(q v t)) (volume.restrict I)) ∧
  ∀ j, j ≤ k → ∀ β : DerivativeWord2 j,
    residualNorm (ι := ι) (h := h) ν π I
        (fun t x i v => r ^ j • (torusJetOrder (-(R₁ v t) - R₂ v t) j β x) i)
        (fun t x v => r ^ j • torusJetOrder (-(q v t)) j β x) ≤
      ENNReal.ofReal X

/-- **From the mass form to the word clause** (generic). For a flux family that is
the sum of two families and a scalar family at the common order `k`, with mass bounds `X₁`, `X₂`
at the radius `r`, the negated pair `(-R₁ - R₂, -q)` is measurable in time and every word of order
`j ≤ k` has residual norm of its `r^j`-scaled jets at most `3·k!·(X₁ + X₂)`.

Route: `r^{2j}‖∂^β U‖²_{L²} ≤ (j!)²|U|²_{r,k}` (the summand `j` of `factorialNormSq`,
`factorialWeight r j = r^{2j}/(j!)²`); the value case is `lintegral_value_jet_sq_le` and
`residualNorm_le_of_mass`, whose proofs go through for any jet index
(`torusHk_toFunction_jet_ae`); the sum of two fluxes by `sqrt_massNormSq_add_le` and
`(a + b)² ≤ 2a² + 2b²`; the negation by `massNormSq_zero_sub`; integrability of the mass
densities by `integrable_massNormSq`; measurability by
`torusHk_aestronglyMeasurable_neg_sub` and `torusHk_aestronglyMeasurable_neg` above.
With the exact Minkowski inequality the constant is `2·k!`; `3·k!` leaves room for the crude one.

For `k = 0` this is `residualNorm_le_of_mass` for a sum; for `ν ≤ 0` the flux part of
the residual norm is `0` and `X₁, X₂ ≥ 0`. The masses must be positive (with a negative mass the
left side drops a term that the mass norm subtracts). -/
def ResidualWordsOfMassStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (k : ℕ) (ν r : ℝ) (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (tp tf : ℝ)
    (R₁ R₂ : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (q : ∀ v, ℝ → TorusHk k (h v)) (X₁ X₂ : ℝ),
    FluxMassLe (ι := ι) (h := h) (K := fun _ => k) ν r π (Set.Icc tp tf) R₁ X₁ →
    FluxMassLe (ι := ι) (h := h) (K := fun _ => k) ν r π (Set.Icc tp tf) R₂ X₂ →
    ScalarMassLe (ι := ι) (h := h) (K := fun _ => k) r π (Set.Icc tp tf) q X₁ →
    ResidualWordsClause (ι := ι) (h := h) k ν r π (Set.Icc tp tf) R₁ R₂ q
      (3 * (k.factorial : ℝ) * (X₁ + X₂))

/-! ### The reconstruction (groups 1, 5, 6) -/

/-- **The conclusion of the reconstruction at a stage.** At descending slots `K ≥ k`, the
trajectories `(uK, wK)` are the lifted field `uh` (value jets) and solve the plain coupled system
of the stage (edge coefficients, no kernel) on `[t_p, t_f]` from their own initial value, with the
residual pair `(RK, qK)`, whose truncations to the common order `k` have mass bounds `Xr` at the
radius `r_s`. This is the conclusion of `ReconWindowAt.physical_lift` at the actual family of the
stage, with the bounds read at the common order. -/
structure IsStageRecon (G : GenStage D hr Dm b j₀) (m k : ℕ) (π : CompIn G.comps → ℝ)
    (tp tf rs : ℝ) (uh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (Xr : ℝ)
    (K : CompIn G.comps → ℕ) (hK : ∀ v, k ≤ K v)
    (uK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (wK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root))
    (RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (qK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root)) : Prop where
  /-- The slots are descending. -/
  desc : G.fam.IsDescending K
  /-- The value of the trajectory is the lifted field. -/
  value : ∀ t ∈ Set.Icc tp tf, ∀ v,
    (uK v t).toFunction.jet (valueIndex2 (K v)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => uh t x v
  /-- The plain coupled system of the stage with the residual pair. -/
  plain : IsCoupledWeakSolutionTorus (ι := CompIn G.comps) (h := fun v => hr v.1.root) (D.κ m)
    tp tf (streamVel (D.Φ m)) Dm K
    (edgeCoefficient G.fam (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) G.actual K)
    (fun v => uK v tp) RK qK uK wK
  /-- The flux of the residual at the common order. -/
  flux : FluxMassLe (ι := CompIn G.comps) (h := fun v => hr v.1.root) (K := fun _ => k) (D.κ m)
    rs π (Set.Icc tp tf) (fun v t => truncateTorusHk (hK v) (RK v t)) Xr
  /-- The scalar part of the residual at the common order. -/
  scalar : ScalarMassLe (ι := CompIn G.comps) (h := fun v => hr v.1.root) (K := fun _ => k) rs π
    (Set.Icc tp tf) (fun v t => truncateTorusHk (hK v) (qK v t)) Xr

/-- **Form of the reconstruction bound (groups 1, 5, 6)**: the lifted field `menuLiftedRep` of
`aRep` has a reconstruction at the common order `k` with the bound `Xr`. The bills instantiate
`Xr = C·[ε_c^N(1 + Z_cl) + (√(B/ν) + ε_c²(1 + Z_cl))·𝔱 + ℓ√(B_p/d_gap)e^{-c d_gap/ℓ²}]·M`. -/
def ReconBound (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth k : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
    (tp tf rs Xr : ℝ) : Prop :=
  ∃ (K : CompIn G.comps → ℕ) (hK : ∀ v, k ≤ K v)
    (uK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (wK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root))
    (RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (qK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root)),
    IsStageRecon G m k π tp tf rs (menuLiftedRep Mn G m N depth CcT aRep) Xr K hK uK wK RK qK

/-! ### The flux pieces (groups 2, 3) and the fine tail (group 4) -/

/-- **Form of the covariance truncation bound**: `B^{-1/2}‖(I - P_pQ_p)G - (𝖩 - BI)∇(𝒞^p/p!)Z‖ ≤ Y` in
`L²(I; H_{ρ,k_c;π})`. Prices: `ω^p + ω^{p+1}` (cascade), `E^{δp_T}` (terminal).
-/
def CovTruncBound (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p depth kc : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
    (tp tf ρ Y : ℝ) : Prop :=
  HasFluxBound (ι := CompIn G.comps) (h := fun v => hr v.1.root) kc (Set.Icc tp tf)
    (D.κ (m - 1)) ρ π (fun v t x => toFluxL (menuCovTruncFlux Mn G m N p depth CcT aZ v t x)) Y

/-- **Form of the response boundary bound**: `B^{-1/2}‖P_p𝖱F_om‖ ≤ Y` on the omitted rows. Prices:
`E^{ιΣ_H} + E^{θ₁+Jθ₂}` (cascade: `successor_frontier_bounds` after `P_p`),
`E^{δ(R_T+1)/2}` (terminal). -/
def FrontierBound (Mn : SuccMenu) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (G G' Gr : GenStage D hr Dm b j₀) (m p H J kc : ℕ) (E η₀ : ℝ)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
    (tp tf ρ Y : ℝ) : Prop :=
  HasFluxBound (ι := CompIn G.comps) (h := fun v => hr v.1.root) kc (Set.Icc tp tf)
    (D.κ (m - 1)) ρ π
    (fun v t x => toFluxL (menuFrontierFlux Mn P seedK freshK φ₀ G G' Gr m p H J E η₀ aY v t x)) Y

/-- **Form of the coarse filter tails bound**: `B^{-1/2}‖P_p𝖱[∑ 𝖮_γ(I - S_γ)Z + ∑ 𝖥_{𝔩,γ}(I - S_m)Z]‖ ≤ Y`.
Prices: `ε_o^{L_c}` (cascade), `E^{b_T + t_TL_c} + x^{χ_w}(r_w/ρ)^{L_o}` (terminal: fresh and old
filters). -/
def FilterBound (Mn : SuccMenu) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (G G' : GenStage D hr Dm b j₀) (m p kc : ℕ) (E η₀ : ℝ)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
    (tp tf ρ Y : ℝ) : Prop :=
  HasFluxBound (ι := CompIn G.comps) (h := fun v => hr v.1.root) kc (Set.Icc tp tf)
    (D.κ (m - 1)) ρ π
    (fun v t x => toFluxL (menuFilterFlux Mn P seedK freshK φ₀ G G' m p E η₀ aZ v t x)) Y

/-- **Form of the fine matrix tail bound**: `ν^{-1/2}‖∑ 𝖠_{m,γ}(I - S_γ)û‖ ≤ Y` in
`L²(I; H_{r_s,k;π})`, on the lifted field of the menu. Prices: `ε_f^{L_f}` (cascade),
`x^{χ_w + σ_wL_f}` (terminal, by the kernel bounds). -/
def FineTailBound (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth k : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
    (tp tf rs Y : ℝ) : Prop :=
  HasFluxBound (ι := CompIn G.comps) (h := fun v => hr v.1.root) k (Set.Icc tp tf) (D.κ m) rs π
    (fineFluxF P seedK freshK φ₀ G (menuLiftedRep Mn G m N depth CcT aRep)) Y

/-! ### The generic assembly -/

/-- **The residual clause of the error at the common order `k`**, for the pair `(-R - F_f, -q)`
built from a reconstruction pair `(RK, qK)` at the slots `K ≥ k` and a flux trajectory `Ff` of
order `k`: `ResidualWordsClause` for the truncations.

At `ScalarH`, `m = M`, `r_s = c_K x` this is the second clause of `TerminalResidualClauses` with
measurability of the forcing, for `Rres = -R - F_f` and `qres = -q`. The negative pair is the forcing of
the error `e = V - û` in the kernel system; `(R + F_f, q)` is the forcing of `û` itself. -/
def ErrorResidualClause (G : GenStage D hr Dm b j₀) (m k : ℕ) (π : CompIn G.comps → ℝ)
    (tp tf rs Xtot : ℝ) (K : CompIn G.comps → ℕ) (hK : ∀ v, k ≤ K v)
    (RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (qK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (Ff : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) : Prop :=
  ResidualWordsClause (ι := CompIn G.comps) (h := fun v => hr v.1.root) k (D.κ m) rs π
    (Set.Icc tp tf) (fun v t => truncateTorusHk (hK v) (RK v t)) Ff
    (fun v t => truncateTorusHk (hK v) (qK v t)) Xtot

/-- The residual clause depends on its bound only through its value. -/
theorem ErrorResidualClause.congr {G : GenStage D hr Dm b j₀} {m k : ℕ}
    {π : CompIn G.comps → ℝ} {tp tf rs Xtot Xtot' : ℝ} {K : CompIn G.comps → ℕ}
    {hK : ∀ v, k ≤ K v}
    {RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    {qK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root)}
    {Ff : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    (h : ErrorResidualClause G m k π tp tf rs Xtot K hK RK qK Ff) (hX : Xtot = Xtot') :
    ErrorResidualClause G m k π tp tf rs Xtot' K hK RK qK Ff := hX ▸ h

/-- **Assembly, generic over the stage.** A reconstruction of the lifted field with the bound `Xr`
and a trajectory `Ff` of the common order with the mass bound `Xf` (a realization of the fine
matrix tail) give the residual clause of the error with the bound `3·k!·(Xr + Xf)`. -/
theorem errorResidualClause_of_recon_fine (hW : ResidualWordsOfMassStatement)
    (G : GenStage D hr Dm b j₀) (m k : ℕ) (π : CompIn G.comps → ℝ) (hπ : ∀ v, 0 < π v)
    (tp tf rs : ℝ) (uh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (Xr Xf : ℝ)
    (K : CompIn G.comps → ℕ) (hK : ∀ v, k ≤ K v)
    (uK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (wK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root))
    (RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (qK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (hrec : IsStageRecon G m k π tp tf rs uh Xr K hK uK wK RK qK)
    (Ff : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (hF : FluxMassLe (ι := CompIn G.comps) (h := fun v => hr v.1.root) (K := fun _ => k)
      (D.κ m) rs π (Set.Icc tp tf) Ff Xf) :
    ErrorResidualClause G m k π tp tf rs (3 * (k.factorial : ℝ) * (Xr + Xf)) K hK RK qK Ff :=
  hW k (D.κ m) rs π hπ tp tf (fun v t => truncateTorusHk (hK v) (RK v t)) Ff
    (fun v t => truncateTorusHk (hK v) (qK v t)) Xr Xf hrec.flux hF hrec.scalar

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! # The split of the mean flux at a menu (proof of `menuMeanFluxSplit`)

`covPolyP` is additive on `C^{2p}` fields, for an arbitrary normed target (the fields are
`Fin 2 → hr`-valued, so no inner product is available). Then
`menuMeanFluxF = menuCovTruncFlux - menuFilterFlux - menuFrontierFlux` by `abel`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation

section Additivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem meanSplit_fderiv_apply_contDiff {n : ℕ} {f : Vec 2 → E}
    (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f) (e : Vec 2) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun y => fderiv ℝ f y e) :=
  (hf.fderiv_right (by exact_mod_cast le_rfl)).clm_apply contDiff_const

theorem meanSplit_covOperator_contDiff (Hc : Matrix (Fin 2) (Fin 2) ℝ) {r : ℕ} {f : Vec 2 → E}
    (hf : ContDiff ℝ ((r + 2 : ℕ) : WithTop ℕ∞) f) :
    ContDiff ℝ (r : WithTop ℕ∞) (AVRegularity.covOperator Hc f) := by
  unfold AVRegularity.covOperator
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.const_smul _ ?_
  exact meanSplit_fderiv_apply_contDiff (n := r)
    (f := fun y => fderiv ℝ f y (basisVec j)) (meanSplit_fderiv_apply_contDiff (n := r + 1) hf _) _

theorem meanSplit_covOperator_add (Hc : Matrix (Fin 2) (Fin 2) ℝ) {f g : Vec 2 → E}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    AVRegularity.covOperator Hc (fun y => f y + g y) =
      fun y => AVRegularity.covOperator Hc f y + AVRegularity.covOperator Hc g y := by
  have h1 : ∀ y, fderiv ℝ (fun y => f y + g y) y =
      fderiv ℝ f y + fderiv ℝ g y := fun y =>
    fderiv_add (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)
  funext x
  unfold AVRegularity.covOperator
  have hfe : ∀ j, ContDiff ℝ 1 (fun y => fderiv ℝ f y (basisVec j)) := fun j =>
    meanSplit_fderiv_apply_contDiff (n := 1) (by simpa using hf) _
  have hge : ∀ j, ContDiff ℝ 1 (fun y => fderiv ℝ g y (basisVec j)) := fun j =>
    meanSplit_fderiv_apply_contDiff (n := 1) (by simpa using hg) _
  simp only [h1, add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_fun_add ((hfe j).differentiable one_ne_zero x) ((hge j).differentiable one_ne_zero x)]
  simp [smul_add]

theorem meanSplit_covOperator_iterate_add (Hc : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ (l : ℕ) {f g : Vec 2 → E}, ContDiff ℝ ((2 * l : ℕ) : WithTop ℕ∞) f →
      ContDiff ℝ ((2 * l : ℕ) : WithTop ℕ∞) g →
      (AVRegularity.covOperator Hc)^[l] (fun y => f y + g y) =
        fun y => (AVRegularity.covOperator Hc)^[l] f y + (AVRegularity.covOperator Hc)^[l] g y := by
  intro l
  induction l with
  | zero => intro f g _ _; rfl
  | succ l ih =>
    intro f g hf hg
    have hf2 : ContDiff ℝ 2 f := hf.of_le (by exact_mod_cast (by omega : 2 ≤ 2 * (l + 1)))
    have hg2 : ContDiff ℝ 2 g := hg.of_le (by exact_mod_cast (by omega : 2 ≤ 2 * (l + 1)))
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      meanSplit_covOperator_add Hc hf2 hg2]
    exact ih (meanSplit_covOperator_contDiff Hc (r := 2 * l) (by
        convert hf using 2)) (meanSplit_covOperator_contDiff Hc (r := 2 * l) (by
        convert hg using 2))

theorem meanSplit_covPolyP_add (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {f g : Vec 2 → E}
    (hf : ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) f) (hg : ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) g) :
    AVRegularity.covPolyP Hc p (fun y => f y + g y) =
      fun y => AVRegularity.covPolyP Hc p f y + AVRegularity.covPolyP Hc p g y := by
  funext x
  unfold AVRegularity.covPolyP
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  have hle : (((2 * l : ℕ) : WithTop ℕ∞)) ≤ ((2 * p : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by omega : 2 * l ≤ 2 * p)
  rw [meanSplit_covOperator_iterate_add Hc l (hf.of_le hle) (hg.of_le hle), smul_add]

end Additivity

/-- The split of the mean flux at a menu. -/
theorem menuMeanFluxSplit : MenuMeanFluxSplitStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ Mn P seedK freshK φ₀ G G' Gr m N p depth H J E η₀ CcT aZ aY v t
    h1 h2 x
  unfold menuMeanFluxF menuCovTruncFlux menuFilterFlux menuFrontierFlux upsilonFlux
  have h := meanSplit_covPolyP_add (menuCovPrimitive D Mn m t) p h1 h2
  have e : (fun y => WithLp.ofLp (readoutFlux m E η₀ (fun _ => True)
        (fun v' s y' => rootFluxDefect P seedK freshK φ₀ G G' aZ v' s y') v t y +
      readoutFlux (S := G.comps) m E η₀ (fun c => ¬ IsRetained m H J c)
        (fun v' s y' => omittedFluxClassical P seedK freshK φ₀ G' Gr aY v' s y') v t y)) =
      fun y => WithLp.ofLp (readoutFlux m E η₀ (fun _ => True)
        (fun v' s y' => rootFluxDefect P seedK freshK φ₀ G G' aZ v' s y') v t y) +
      WithLp.ofLp (readoutFlux (S := G.comps) m E η₀ (fun c => ¬ IsRetained m H J c)
        (fun v' s y' => omittedFluxClassical P seedK freshK φ₀ G' Gr aY v' s y') v t y) := by
    funext y; simp
  rw [e, congrFun h x]
  abel

end AVRegularity.Construction.Residual.Presentation
end
end
end
