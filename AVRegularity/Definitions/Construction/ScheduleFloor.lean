-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Construction.Preparation
public import AVRegularity.Statements.Intermediate.Families.IsEnvelope
public import AVRegularity.Statements.Intermediate.Families.AtlasIsQuiet
public import AVRegularity.Statements.Intermediate.Families.AtlasCoversQuiet
public import AVRegularity.Statements.Intermediate.Families.AtlasIsConsecutiveClosed
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTransverseOnPulses
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsFastIndependentOn
public import AVRegularity.Statements.Intermediate.KernelEnergy.KernelSchurMatrix
public import AVRegularity.Statements.Intermediate.KernelEnergy.SchurBound
public import AVRegularity.Statements.Intermediate.KernelEnergy.SpatialRegularizerTorus
public import AVRegularity.Statements.Intermediate.CycleJoint.OcTrimmedQuietTimes
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity

/-! Definition: the stage invariant (Definition 10.1 of the paper).

At every incoming stage the hypotheses of production and preparation must hold through the
selected reserves on the full window. `IsStageInvariant` is their
conjunction for a stage `G` of level `i` on the window `W = [t_A, t_B]`, with the constants
`InvConsts`, the ledger bound `S` and the kernel-price bound `θ_K`:

1. **Generated membership with quantitative context certificates**: the
   pieces are the natural charts, the records are the provenance tags, every coefficient is a
   scheduled generated context function on the admissible scheduled chains of the carrier with the
   recorded construction fixed (`IsGenerated`), and it has a holomorphic extension to the actual
   graded carrier whose context size at the producer reserve `μ_{G₀ + #𝖡(v)}` and fast weight `L_*`
   is dominated by the positive witness: `(ε_i/R_γ)^{d-2} ∑_{α,k} q_{μ,L_*}(a♭_{γ,d,α,k}) ≤ θ̄_γ`
   (`IsContextCertified`). Domain coverage of the physical labels is the lemma
   `GenStage.innerDomain_native`.
   The fields obey the context-level torus law (`IsShiftInvariant`: integer translations of the
   base label leave them unchanged); with the natural
   pieces it gives the torus compatibility consumed by `cycle_joint` and `cycle_comparison`
   (`IsStageInvariant.isTorusCompatible`). The generated expressions have seed provenance (their
   two-dimensional inverses occur only inside the certified seed exports `G.exports`),
   and every field is slotwise structurally transverse on the output domain `J_𝗉` of its slot
   (`IsSlotTransverse`); the windowed physical clause `IsTransverseOnPulses` of
   clause 3 is kept.
2. **Both independent envelopes with the recorded witnesses**, in the ordinary and the marked norm
   (`IsEnvelope` of the family and of `markerConj d F` with the record matrix and its marker
   conjugate), on the inner domain at the reserve `𝗆_env`, the marked/inflated ledger `S^♯ ≤ S`,
   and the priced kernel, moment, derivative and width bounds of preparation: every
   kernel is an admissible moving paired kernel of bound `Γ` with moment cancellation through
   `L_ker` and regularizes at every radius, both kernel-priced Schur sums at `ρ_⋆` are at most
   `θ_K` in both weights, and the widths satisfy `r_γ ≤ C_w ρ_⋆ e^{σ_f}`, `r_γ ≤ C_w ρ E^{λ_c}`.
3. **Exact quiet-chart matching** (the flux relation is
   `IsQuiet` on an atlas containing the consecutive renewal transitions and covering the quiet
   times of the window). The matched pairs are exactly the pairs of actual
   (native) contexts of adjacent pieces, which represent the same retained history (the
   physical gluing consumer); no totality over the outer carrier is asserted. With
   transversality on the enlarged pulses and fast independence on the quiet times (off the carrier
   the coefficients are pinned to zero).
4. **The carried history invariant**: at two contexts of a slot with the same history
   geometry over its availability interval at the natural level `M`, the fluxes agree as germs in
   the slow offset (`StageHistoryInvariant G M`). -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The enlarged pulses `[(k - 3/4)τ, (k + 3/4)τ]` of level `m`, clipped to `W`. -/
def enlargedPulse (D : OCData) (m : ℕ) (W : Set ℝ) (k : {k : ℤ // Odd k}) : Set ℝ :=
  Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau D.α D.q D.Λ m) (((k.1 : ℝ) + 3 / 4) * ocTau D.α D.q D.Λ m) ∩ W

/-- The parallel direction of the pulse `k` (`e_1` for `k ∈ 4ℤ+3`, `e_2` otherwise). -/
def parallelIndex (k : {k : ℤ // Odd k}) : Fin 2 := if k.1 % 4 = 3 then 0 else 1

/-- The constants of the stage invariant. -/
structure InvConsts where
  /-- The molecular radius constant `c₀`. -/
  c₀ : ℝ
  /-- The enhanced radius constant `c_r`. -/
  cr : ℝ
  /-- The kernel bound `Γ`. -/
  Γk : ℝ
  /-- The width constant. -/
  Cwid : ℝ
  /-- The fine width exponent `σ_f`. -/
  σf : ℝ
  /-- The coarse width exponent `λ_c`. -/
  lamC : ℝ
  /-- The analytic envelope constant. -/
  Ca : ℝ
  /-- The inner reserve of the envelope domains. -/
  mEnv : ℝ
  /-- The molecular envelope constants. -/
  Cm : ℕ → ℝ
  /-- The kernel derivative constants `c_j`. -/
  cker : ℕ → ℝ
  /-- The analytic slow reserve. -/
  Kan : ℕ
  /-- The analytic fast reserve. -/
  Lan : ℕ
  /-- The molecular derivative reserve. -/
  Jm : ℕ
  /-- The allocated slot bound. -/
  Ks : ℕ
  /-- The moment-cancellation order of the kernels. -/
  Lker : ℕ
  /-- The fast weight `L_*` of the context sizes. -/
  Lstar : ℕ
  /-- The producer grade offset `G₀`. -/
  G0 : ℕ
  /-- The producer top grade `H_prod`. -/
  Hprod : ℕ

/-- The producer reserve `μ_{G₀ + #𝖡(v)} = 1 - (G₀ + #𝖡(v))/(H_prod + 1)` of a component. -/
def compReserve (k : InvConsts) (c : Comp) : ℝ :=
  1 - ((k.G0 + compGrade c : ℕ) : ℝ) / ((k.Hprod : ℝ) + 1)

namespace GenStage

/-- Slotwise structural transversality: on the scheduled output domain
`J_𝗉` of every slot, every field of every identity is invariant under parallel shifts of the fast
variable (the parallel direction `p_i` of the slot), at every context and slow offset. Weak
two-dimensional outputs enter only through the mean and export boundary (inside `G.exports`). -/
def IsSlotTransverse (G : GenStage D hr Dm b j₀) : Prop :=
  ∀ (p : OddSlot) (c : StageCtx D b j₀ G.level p) v u (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)), ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
    ∀ (X z : Vec 2) (s : ℝ),
      G.fam.flux p c v u γ d I t X (z + s • basisVec (slotParallel p.1)) =
        G.fam.flux p c v u γ d I t X z

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- Restriction to a subset of the components keeps slotwise transversality. -/
theorem IsSlotTransverse.restrict {G : GenStage D hr Dm b j₀} (hG : G.IsSlotTransverse)
    (S : Finset Comp) (hS : S ⊆ G.comps) : (G.restrict S hS).IsSlotTransverse :=
  fun p c v u γ d I t ht X z s => hG p c ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩ γ d I t ht X z s

open scoped Classical in
/-- Every coefficient of every identity has a holomorphic extension to the graded carrier whose
context size at the reserve of the target component is dominated by the positive witness. -/
def IsContextCertified (k : InvConsts) (G : GenStage D hr Dm b j₀) : Prop :=
  ∀ v u (γ : G.fam.Γ v u), ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
    (∀ d α c, 0 ≤ θ d α c) ∧
    (∀ d, 2 ≤ d → d ≤ (G.fam.identity v u γ).maxOrder →
      (D.eps G.level / (G.fam.identity v u γ).record.length) ^ (d - 2) *
          ∑ α, ∑ c, θ d α c ≤ (G.fam.identity v u γ).record.size) ∧
    ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
      ∃ (f : OddSlot → GenSort.Sem .ctx)
        (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ),
        (∀ p, IsGeneratedCtxFrom D b j₀ G.exports G.level p.1 (f p) ∧
          IsHolExtension D b j₀ G.level p.1 (f p) (F p) ∧
          ∀ (ctx : StageCtx D b j₀ G.level p) (t : ℝ), t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
            ∀ (X z : Vec 2),
            G.fam.flux p ctx v u γ d α t X z c =
              if IsAdmissibleChain D b j₀ G.level p.1 (ctx.1.recenter D (D.eps (G.level - 1) • X))
              then f p t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0) ∧
        ctxSize D b j₀ G.level F (compReserve k v.1) k.Lstar ≤ ENNReal.ofReal (θ d α c)

end GenStage

/-- The stage invariant of `G` (level `i`) on the window `[tA, tB]` with the ledger bound `S` and
the kernel-price bound `θK`. -/
def IsStageInvariant (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (k : InvConsts) (tA tB S θK : ℝ)
    (G : GenStage D hr Dm b j₀) : Prop :=
  -- 1. generated membership with quantitative context certificates
  G.IsNatural M ∧ G.HasTags P ∧ G.IsGenerated ∧ G.IsShiftInvariant ∧ G.IsSlotTransverse ∧
    G.IsContextCertified k ∧
  -- 2. envelopes (ordinary and marked), ledger, kernels, widths
  (∀ K : CompIn G.comps → ℕ, (∀ v, K v ≤ k.Ks) →
    IsEnvelope G.fam (G.mass law) K (G.innerDomain (Set.Icc tA tB) k.mEnv)
        (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) (rhoStar D k.c₀ G.level)
        (recordMajorant (G.mass law) G.fam) S k.Ca k.Kan k.Lan k.Cm k.Jm ∧
      IsEnvelope (markerConj (G.marker law) G.fam) (G.mass law) K
        (G.innerDomain (Set.Icc tA tB) k.mEnv)
        (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) (rhoStar D k.c₀ G.level)
        (fun v u => G.marker law v / G.marker law u * recordMajorant (G.mass law) G.fam v u)
        S k.Ca k.Kan k.Lan k.Cm k.Jm) ∧
  markedLedger (G.mass law) (G.marker law) G.fam ≤ S ∧
  (∀ v u (γ : G.fam.Γ v u), (G.kernelOf P seedK freshK v u γ).IsAdmissible k.Γk k.Lker ∧
    (G.kernelOf P seedK freshK v u γ).width = (G.fam.identity v u γ).record.width ∧
    (G.fam.identity v u γ).record.width ≤
      k.Cwid * rhoStar D k.c₀ G.level * D.eps G.level ^ k.σf ∧
    (G.fam.identity v u γ).record.width ≤
      k.Cwid * rhoEnh D k.cr G.level * D.eps (G.level - 1) ^ k.lamC ∧
    ∀ ϱ : ℝ, 0 < ϱ → ∀ kk ≤ k.Ks,
      IsSpatialRegularizerTorus ϱ kk Dm tA tB k.cker (G.kernelOf P seedK freshK v u γ).width
        (G.sysS P seedK freshK φ₀ hφ₀ v u γ)) ∧
  (∀ kk ≤ k.Ks, ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = G.marker law →
    SchurBound θK (kernelSchurMatrix (ι := CompIn G.comps) (h := fun v => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) (D.kap G.level) (rhoStar D k.c₀ G.level)
      (fun v => G.mass law v / w v ^ 2) kk Dm tA tB k.cker
      (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
      (fun v u γ d => G.physCoeff v u γ d.1))) ∧
  -- 3. exact quiet-chart matching, transversality, fast independence
  (∃ T : G.fam.Atlas,
    T.IsConsecutiveClosed (Set.Icc tA tB) ∧
    T.CoversQuiet (ocQuietTimes D.α D.q D.Λ D.ζ G.level) (Set.Icc tA tB) ∧
    T.IsQuiet (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ∧
    (∀ p q (hpq : T.adjacent p q),
      ((G.fam.piece p).output ∩ (G.fam.piece q).output ∩ Set.Icc tA tB).Nonempty →
      T.sameCtx p q hpq (G.actual p) (G.actual q)) ∧
    (∀ p q (hpq : T.adjacent p q) c c', T.sameCtx p q hpq c c' →
      c = G.actual p ∧ c' = G.actual q)) ∧
  G.fam.IsTransverseOnPulses (enlargedPulse D G.level (Set.Icc tA tB)) parallelIndex ∧
  G.fam.IsFastIndependentOn (ocTrimmedQuietTimes D.α D.q D.Λ D.ζ G.level ∩ Set.Icc tA tB) ∧
  -- 4. the carried history invariant
  StageHistoryInvariant G M

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! Definition: a generated seed and its finite-order requirements (E1)-(E3) and its
admissibility.

`IsGeneratedSeed` at the level `n`, on the window `[t_S, t_f]`:
* the seed is a stage of level `n` with natural pieces, records equal to its tags, generated
  coefficients (finite expressions in (K1)-(K6), the transverse primitive, the higher transfer and
  solved seed nodes, `IsGenerated`), seed identities only (`Prov.seed`), and components of grade
  zero with empty birth sets (marker `I`): its components have grade zero and marker `I`, while
  every constituent retains its original birth tags;
* (E1) mass `∑π ≤ C_e`, depth at most `r₀`, orders at most `D₀`, widths `r_γ ≤ ε_n`, original
  lengths `R_γ ≤ ε_n` of higher tagged constituents, kernels of bound `Γ_e` (moving paired
  kernels) with moment cancellation through `L_ker` (`2n - 1 ≥ L_ker`; the successor needs it
  through `max{L_pr, L_c, L_f}`);
* (E2) the marked/inflated ledger `S_n^♯ ≤ C_e ε_n^{τ_e}` (`markedLedger`);
* (E3) the sampled bound `𝒜_{ϱ,k}(B_{γ,d}) ≤ C_e θ_γ κ_n R_γ^{d-2}` for `0 < ϱ ≤ ε_n`, `k ≤ K_s`,
  `2 ≤ d ≤ D_γ`;
* the stage invariant at the seed with the seed-supplied constants (`IsStageInvariant`):
  generated membership with quantitative context certificates (including the solved
  nodes), both envelopes in the ordinary and the marked norm with the record matrix (the record
  also dominates the supplied independent molecular envelope at the seed radius),
  `S_n^♯ ≤ C_e ε_n^{τ_e}`, the admissible kernels of bound `Γ` with moment cancellation and
  their supplied price, and the **exact quiet-transition certificate** (the atlas with
  `IsQuiet`, including matched quiet representatives) with transversality and fast
  independence;
* the **certified context exports** `seed.exports`: the occurrence
  trees, the only places where two-dimensional inverses may occur in the subsequent production;
  each export is scheduled and slotwise structurally parallel invariant on the output domain `J_𝗉`
  of its slot: invariant under parallel shifts of the child phases and of the final phase
  (`IsSlotParInvCtx`), with a unique denotation on `J_𝗉` and the
  admissible chains (the seed's solved nodes are the original inverses); the
  export roots lie at or above the seed level
  (`SeedExports.Above`, well-formedness metadata). -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The seed at level `n` is a generated seed satisfying its finite-order requirements, with the
seed-supplied invariant constants `kS` on the window `[tS, tf]`; its ledger is
`S_n^♯ ≤ C_e ε_n^{τ_e}` and its kernel price is `≤ C_e ε_{n-1}^{qτ_e}` (the price from the
marked inflated ledger on the parent wavelength). -/
def IsGeneratedSeed (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (kS : InvConsts)
    (seed : GenStage D hr Dm b j₀) (n : ℕ) (tS tf Ce τe : ℝ) (r₀ D₀ : ℕ) : Prop :=
  seed.level = n ∧
    (∀ v : CompIn seed.comps, v.1.births = []) ∧
    (∀ v u (γ : seed.fam.Γ v u), ∃ k tag, seed.prov v u γ = .seed k tag) ∧
    ∑ v, seed.mass law v ≤ Ce ∧ seed.fam.HasDepthAtMost r₀ ∧
    (∀ v u (γ : seed.fam.Γ v u), (seed.fam.identity v u γ).maxOrder ≤ D₀ ∧
      (seed.fam.identity v u γ).record.width ≤ D.eps n ∧
      (1 ≤ (seed.fam.identity v u γ).record.birthExcess →
        (seed.fam.identity v u γ).record.length ≤ D.eps n)) ∧
    (∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ D.eps n → ∀ k ≤ kS.Ks, ∀ v u (γ : seed.fam.Γ v u) (d : ℕ), 2 ≤ d →
      d ≤ (seed.fam.identity v u γ).maxOrder →
      coefficientSeminorm ϱ k tS tf (seed.physCoeff v u γ d) ≤
        ENNReal.ofReal (Ce * (seed.fam.identity v u γ).record.size * D.κ n *
          (seed.fam.identity v u γ).record.length ^ (d - 2))) ∧
    IsStageInvariant law P seedK freshK φ₀ hφ₀ M kS tS tf (Ce * D.eps n ^ τe)
      (Ce * D.eps (n - 1) ^ (D.q * τe)) seed ∧
    (∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), seed.exports e →
      Gen.IsScheduled D e ∧ (∀ f : GenSort.Sem .ctx, Gen.Denotes D b j₀ e f →
        IsSlotParInvCtx D b j₀ i p f) ∧
      ∀ f f' : GenSort.Sem .ctx, Gen.Denotes D b j₀ e f → Gen.Denotes D b j₀ e f' →
        ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ ch : RealChain, IsAdmissibleChain D b j₀ i p ch →
          ∀ ζ : Vec 2, f t ch ζ = f' t ch ζ) ∧
    SeedExports.Above (fun {_ _} e => seed.exports e) n

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! Definition: the exponents, birth law, finite schedules and menus of the retained
successor.

* `ocMuS α q s = (q-1)(1-s) - qγ` (display (1.3) of the paper; equal to
  `(q-1)(1 - qβ/(q+1) - s)`).
* `succEta0 = min{δ/8, μ_s/4}`; `η_b = η₀/2`, `ι = η₀/8`. `IsSuccessorLaw`: the birth
  law has these exponents, `c_H = (1 - 128^{-η₀/2})/2` and `|𝔚| = T_w` (the number of nonempty
  words of length at most `J+1`).
* `succSchedR`, `succSchedD`: `r_g = (J+2)(r_{g-1}+1) - 1`, `D_g = D_{g-1} + 2N + 4p + 4` from the
  seed's `(r₀, D₀)`; `D_* = D_{H+1} - 2`.
* `succTheta1 = δ - σ₀D_* - η₀ - η_b/2 - ι`, `succTheta2 = δ - σ₀D_* - η₀`,
  `succSigmaH = ∑_{l≤H} q₀^l`, `q₀ = (1+q)/2`.
* `IsSuccessorSchedule`: the sufficient schedule by which the orders are chosen (displays
  (12.5) and (12.6) of the paper):
  `ιΣ_H, θ₁ + Jθ₂, 3δN, δp > Q + qγ + 4`, `(qγ + 3δ)A_cl ≥ 2 - β + 8δ`,
  `σ₀ = a + σ` with `0 < a ≤ σ`, `0 < σ₀ < λ_c`, `σ₀D_* ≤ δ/8`, `σ₀L_c > Q + qγ + 4`,
  `qσ_fL_f > Q + 4`, `qσ_fL_pr > Q + 3` (the preparation's approximation order with
  `κ_w = qσ_f`),
  `2n_k - 1 ≥ max{L_pr, L_c, L_f}`, `N_aux ≥ max{k_res + D_{H+1} + L_c + 6p, D_* + L_f + N + 2p + 1}`
  with `k_res = 4(N + D_{H+1}) + 2A_cl + 16`, and `N_out ≥ N_aux + 4p`.
* `succProvParams`, `succMenu`: the tag parameters (witness constant `C_w`, no further birth
  inflation, fresh lengths and widths) and the menus of the construction; the alphabet bounds are
  `n ≤ N + D_H`, `h ≤ r_H` (the padded producer menus). -/

/-- `μ_s = (q-1)(1-s) - qγ`. -/
def ocMuS (α q s : ℝ) : ℝ := (q - 1) * (1 - s) - q * ocGamma α q

/-- `η₀ = min{δ/8, μ_s/4}`. -/
def succEta0 (α q s : ℝ) : ℝ := min (ocDelta α q / 8) (ocMuS α q s / 4)

/-- The depth schedule `r_g = (J+2)(r_{g-1}+1) - 1`, `r_0 = r₀`. -/
def succSchedR (r₀ J : ℕ) : ℕ → ℕ
  | 0 => r₀
  | g + 1 => (J + 2) * (succSchedR r₀ J g + 1) - 1

/-- The order schedule `D_g = D_{g-1} + 2N + 4p + 4`, `D_0 = D₀`. -/
def succSchedD (D₀ N p : ℕ) : ℕ → ℕ
  | 0 => D₀
  | g + 1 => succSchedD D₀ N p g + 2 * N + 4 * p + 4

/-- `D_* = D_{H+1} - 2`. -/
def succDstar (D₀ N p H : ℕ) : ℕ := succSchedD D₀ N p (H + 1) - 2

/-- `θ₁ = δ - σ₀D_* - η₀ - η_b/2 - ι`. -/
def succTheta1 (α q s σ₀ : ℝ) (Dstar : ℕ) : ℝ :=
  ocDelta α q - σ₀ * Dstar - succEta0 α q s - succEta0 α q s / 4 - succEta0 α q s / 8

/-- `θ₂ = δ - σ₀D_* - η₀`. -/
def succTheta2 (α q s σ₀ : ℝ) (Dstar : ℕ) : ℝ :=
  ocDelta α q - σ₀ * Dstar - succEta0 α q s

/-- `Σ_H = ∑_{l=0}^H q₀^l`, `q₀ = (1+q)/2`. -/
def succSigmaH (q : ℝ) (H : ℕ) : ℝ := ∑ l ∈ Finset.range (H + 1), ((1 + q) / 2) ^ l

/-- The birth law of the successor. The mass constant `c_H` is fixed once, with the
construction. It is the largest value allowed by the constraint `c_H ≤ (1 - 128^{-η_b})/2`. The
ledger constant and the starting level of the cascade depend on it, so
the statements, which choose them before the law, are stated for this fixed `c_H`. -/
def IsSuccessorLaw (α q s : ℝ) (Tw : ℕ) (law : BirthLaw) : Prop :=
  law.eta0 = succEta0 α q s ∧ law.etaB = succEta0 α q s / 2 ∧ law.iota = succEta0 α q s / 8 ∧
    law.cH = (1 - (128 : ℝ) ^ (-(succEta0 α q s / 2))) / 2 ∧ law.wordCount = Tw

/-- The sufficient schedule of the finite orders. -/
def IsSuccessorSchedule (α q s Q σ₀ a σ σf lamC : ℝ)
    (D₀ H J N p nk Lc Lf Lpr Acl Naux Nout : ℕ) : Prop :=
  succEta0 α q s / 8 * succSigmaH q H > Q + q * ocGamma α q + 4 ∧
    succTheta1 α q s σ₀ (succDstar D₀ N p H) + J * succTheta2 α q s σ₀ (succDstar D₀ N p H) >
      Q + q * ocGamma α q + 4 ∧
    3 * ocDelta α q * N > Q + q * ocGamma α q + 4 ∧ ocDelta α q * p > Q + q * ocGamma α q + 4 ∧
    (q * ocGamma α q + 3 * ocDelta α q) * Acl ≥ 2 - (1 + α) + 8 * ocDelta α q ∧
    σ₀ = a + σ ∧ 0 < a ∧ a ≤ σ ∧ σ₀ < lamC ∧ σ₀ * succDstar D₀ N p H ≤ ocDelta α q / 8 ∧
    σ₀ * Lc > Q + q * ocGamma α q + 4 ∧ q * σf * Lf > Q + 4 ∧ q * σf * Lpr > Q + 3 ∧
    max Lpr (max Lc Lf) + 1 ≤ 2 * nk ∧
    max (4 * (N + succSchedD D₀ N p (H + 1)) + 2 * Acl + 16 + succSchedD D₀ N p (H + 1) + Lc + 6 * p)
      (succDstar D₀ N p H + Lf + N + 2 * p + 1) ≤ Naux ∧
    Naux + 4 * p ≤ Nout ∧ 1 ≤ H ∧ 2 ≤ N ∧ 1 ≤ p ∧ 1 ≤ nk

/-- The tag parameters of the construction. -/
def succProvParams (D : OCData) (Cw cr σ₀ η₀ : ℝ) (N p : ℕ) : ProvParams where
  C := Cw
  w := fun _ => 1
  eps := D.eps
  δ := ocDelta D.α D.q
  η0 := η₀
  N := N
  p := p
  Rb := freshLength D cr
  rb := freshWidth D cr σ₀

/-- The padded alphabet of the construction at the successor menus. -/
def succAlphabetOf (r₀ D₀ H J N p npad : ℕ) : Finset WordLetter :=
  succAlphabet (N + succSchedD D₀ N p H) (succSchedR r₀ J H) p npad

/-- The menus of the construction. -/
def succMenu (M r₀ D₀ H J N p npad sX sZ : ℕ) (η₀ : ℝ) : SuccMenu where
  M := M
  A := succAlphabetOf r₀ D₀ H J N p npad
  H := H
  J := J
  N := N
  p := p
  sX := sX
  sZ := sZ
  η0 := η₀
  anchor := 0
  lenFactor := 1

/-- The producer's fast weight `L_* = L_out + (r̄^prod_{H_prod} + 1)(N_prod + D^prod_{H_prod} + 2)
(D^prod_{H_prod} + 2)` with `N_prod = 2N + 4`, `H_prod = G₀ + H + 1` and the output order
`L_out = K_res`. -/
def succLstar (Kres G₀ H J N p : ℕ) : ℕ :=
  Kres + (succSchedR 0 J (G₀ + H + 1) + 1) * ((2 * N + 4) + succSchedD 2 N p (G₀ + H + 1) + 2) *
    (succSchedD 2 N p (G₀ + H + 1) + 2)

/-- The seed-supplied constants carry the producer allocation and the reserves required by the
schedule:
kernel moment cancellation through `max{L_pr, L_c, L_f}`, allocated slots and
analytic/molecular reserves through `K_res`, the fast weight `L_*`, the producer offset `G₀` of the
reserve adapter with `H_prod = G₀ + H + 1` (seed reserve `μ_{G₀}`), and an envelope inner reserve
below the smallest graded reserve. -/
def IsSeedAllocation (kS : InvConsts) (r₀ D₀ H J N p Kres Lpr Lc Lf : ℕ) : Prop :=
  max Lpr (max Lc Lf) ≤ kS.Lker ∧ Kres ≤ kS.Ks ∧ Kres ≤ kS.Kan ∧ Kres ≤ kS.Lan ∧ Kres ≤ kS.Jm ∧
    succLstar Kres kS.G0 H J N p ≤ kS.Lstar ∧
    (∀ g, succSchedR r₀ J g ≤ succSchedR 0 J (kS.G0 + g)) ∧
    (∀ g, succSchedD D₀ N p g ≤ succSchedD 2 N p (kS.G0 + g)) ∧ kS.Hprod = kS.G0 + H + 1 ∧
    0 ≤ kS.mEnv ∧ kS.mEnv < 1 / ((kS.Hprod : ℝ) + 1)

/-- The cascade invariant constants `kI` are admissible for the seed constants `kS` and the
thresholds `thr`:
* same radii; kernel bound `Γ ≥ max{Γ_S, Γ_*}` (`thr.Γk` is the fresh-kernel bound
  `Γ_* = max{2C_H, 3}`) and derivative constants above the seed's and the fresh
  kernels' (`thr.cker`); envelope and width constants above both;
* width exponents reduced as the successor allows and pinned to the exponents the schedule
  uses: `σ_f = min{σ_f^S, δ + σ₀}` (the exponent of `IsSuccessorSchedule`),
  `σ₀ < λ_c ≤ min{λ_c^S, (q-1)(1+c) + qσ₀}` (the coarse ratio pays `ε_o^{L_c}`);
* kernel moments `max{L_pr, L_c, L_f} ≤ L_ker ≤ min{L_ker^S, 2n_k - 1}` (fresh kernels have order
  `n_k`);
* reserves between the requirement `K_res` (resp. `L_*`) and the seed's; the same producer
  allocation `G₀, H_prod` as the seed (seed reserve `μ_{G₀}`); inner envelope reserve
  `0 ≤ 𝗆_env ≤ 𝗆_env^S`, below the smallest graded reserve `1/(H_prod + 1)`.
The ledger and witness constants are chosen **after** `kI` (`IsLedgerAdmissible`): the price
constant `C_price` depends on the kernel derivative constants `kI.cker`. -/
def IsInvariantAdmissible (kS thr kI : InvConsts)
    (H J N p nk Kres Lpr Lc Lf : ℕ) (σ₀ δ q c : ℝ) : Prop :=
  kI.c₀ = kS.c₀ ∧ kI.cr = kS.cr ∧ kS.Γk ≤ kI.Γk ∧ thr.Γk ≤ kI.Γk ∧
    kS.Cwid ≤ kI.Cwid ∧ thr.Cwid ≤ kI.Cwid ∧
    kI.σf = min kS.σf (δ + σ₀) ∧
    σ₀ < kI.lamC ∧ kI.lamC ≤ kS.lamC ∧ kI.lamC ≤ (q - 1) * (1 + c) + q * σ₀ ∧
    kS.Ca ≤ kI.Ca ∧ thr.Ca ≤ kI.Ca ∧ (∀ j, kS.Cm j ≤ kI.Cm j ∧ thr.Cm j ≤ kI.Cm j) ∧
    (∀ j, kS.cker j ≤ kI.cker j ∧ thr.cker j ≤ kI.cker j) ∧
    max Lpr (max Lc Lf) ≤ kI.Lker ∧ kI.Lker ≤ kS.Lker ∧ kI.Lker + 1 ≤ 2 * nk ∧
    Kres ≤ kI.Ks ∧ kI.Ks ≤ kS.Ks ∧ Kres ≤ kI.Kan ∧ kI.Kan ≤ kS.Kan ∧
    Kres ≤ kI.Lan ∧ kI.Lan ≤ kS.Lan ∧ Kres ≤ kI.Jm ∧ kI.Jm ≤ kS.Jm ∧
    succLstar Kres kI.G0 H J N p ≤ kI.Lstar ∧ kI.Lstar ≤ kS.Lstar ∧
    kI.G0 = kS.G0 ∧ kI.Hprod = kS.Hprod ∧ kI.Hprod = kI.G0 + H + 1 ∧
    0 ≤ kI.mEnv ∧ kI.mEnv ≤ kS.mEnv ∧ kI.mEnv < 1 / ((kI.Hprod : ℝ) + 1)

/-- The ledger constant `C_I ≥ max{C_e, C_I^thr}` (`C_I^thr ≥ 2^τ C_price(kI) C_S` is chosen
after `kI`) and the witness constant `C_w ≥ C_w^thr`, `C_w > 0`. -/
def IsLedgerAdmissible (Ce CI Cw CIthr Cwthr : ℝ) : Prop :=
  Ce ≤ CI ∧ CIthr ≤ CI ∧ Cwthr ≤ Cw ∧ 0 < Cw

end AVRegularity
end
end

section
@[expose] public section
namespace AVRegularity

/-! The reserve-allocation adapter.
The successor's schedules from the seed bounds `(r₀, D₀)`, `r_{g+1} = (J+2)(r_g+1) - 1`,
`D_{g+1} = D_g + 2N + 4p + 4`, are dominated by the auxiliary producer's schedules with the padded
menus `J_prod = J+1`, `N_prod = 2N+4` from `(0, 2)` (the identical recursions `succSchedR 0 J`,
`succSchedD 2 N p`), shifted by a finite producer grade `G₀`:
`r_g ≤ r^prod_{G₀+g}`, `D_g ≤ D^prod_{G₀+g}` for every `g`. The reserves are allocated through
`H_prod = G₀ + H + 1`, with the seed reserve `μ_{G₀} = 1 - G₀/(H_prod + 1)` (`compReserve` at a
component of grade zero).
The actual alphabet, cutoffs and words are unchanged (`succAlphabetOf`). The producer recursion
with the padded menus `J_prod = J+1`, `N_prod = 2N+4` is
literally `r ↦ (J+2)(r+1) - 1` and `D ↦ D + 2N + 4p + 4`, which is why `succSchedR 0 J` and
`succSchedD 2 N p` are the producer schedules. -/

theorem succSchedR_mono (J : ℕ) {r r' : ℕ} (h : r ≤ r') (g : ℕ) :
    succSchedR r J g ≤ succSchedR r' J g := by
  induction g with
  | zero => simpa [succSchedR] using h
  | succ g ih =>
      simp only [succSchedR]
      have := Nat.mul_le_mul_left (J + 2) (Nat.add_le_add_right ih 1)
      omega

theorem succSchedR_shift (r J G : ℕ) (g : ℕ) :
    succSchedR r J (G + g) = succSchedR (succSchedR r J G) J g := by
  induction g with
  | zero => rfl
  | succ g ih =>
      show succSchedR r J ((G + g) + 1) = _
      simp only [succSchedR, ih]

theorem le_succSchedR (r J g : ℕ) : g ≤ succSchedR r J g := by
  induction g with
  | zero => exact Nat.zero_le _
  | succ g ih =>
      simp only [succSchedR]
      have h1 : 2 * (succSchedR r J g + 1) ≤ (J + 2) * (succSchedR r J g + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega

theorem succSchedD_eq (D₀ N p g : ℕ) : succSchedD D₀ N p g = D₀ + g * (2 * N + 4 * p + 4) := by
  induction g with
  | zero => simp [succSchedD]
  | succ g ih => simp only [succSchedD, ih]; ring

end AVRegularity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity

/-! Definition: the floor of the auxiliary order `N_aux` asked by the physical
reconstruction of the cycle comparison at a cascade passage.

The schedule of the successor (`IsSuccessorSchedule`) has the floor
`N_aux ≥ max{k_res + D_{H+1} + L_c + 6p,
D_* + L_f + N + 2p + 1}` with `k_res = 4(N + D_{H+1}) + 2A_cl + 16`, with no term in the depth of
the incoming family (the first floor of display (12.6) of the paper; `succReconFloor` is the
second). The reconstruction
(`k = 4D_c + 2A' + 16 + K_* + Δ_*`, `M_out = k + (J' + H + 3)(D_c + 8p' + 10)`; the reserves
`compReserveK`, `compReserveMout`) needs descending slots up to the depth times the order, a
coarse order above the partition order, and the coarse field and the initial datum of the window
inside `H^{N_aux - 2p}`. The passage statements assume `succReconFloor … ≤ N_aux`; the order
choice `cascade_schedule_exists` supplies it.

The degenerate case `r₀ = 0`, `J = 0`, `H = 1` (`r_H = 1`) is included: the floor is
`4(N + D) + 2A_cl + 16 + 2D + max (D + L_c + N + 6p + 4) (4(N + D + 12) + 2p)`, above the first
member of the schedule's floor; the floor is monotone in every argument. -/

/-- The floor of the auxiliary order asked by the physical reconstruction at a cascade passage:
with `D = D_{H+1}` and `r = r_H` (the depth of the incoming family), descending
slots up to `2Dr`, the coarse order `k_c = 4(N + D) + 2A_cl + 16 + 2Dr`, the three flux bounds at
the order `k_c` (`D + L_c + N + 6p + 4` more), and the coarse field and the initial datum of the
window inside `H^{N_aux - 2p}` (`(r + 3)(N + D + 12)` more). -/
def succReconFloor (r₀ D₀ H J N p Acl Lc : ℕ) : ℕ :=
  4 * (N + succSchedD D₀ N p (H + 1)) + 2 * Acl + 16 +
      2 * succSchedD D₀ N p (H + 1) * succSchedR r₀ J H +
    max (succSchedD D₀ N p (H + 1) + Lc + N + 6 * p + 4)
      ((succSchedR r₀ J H + 3) * (N + succSchedD D₀ N p (H + 1) + 12) + 2 * p)

end AVRegularity
end
end
