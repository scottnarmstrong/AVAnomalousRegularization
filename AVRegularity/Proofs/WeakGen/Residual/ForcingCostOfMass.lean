-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.Orders
public import AVRegularity.EntryWeakAssembly.Assembly.KernelPriceTransport
public import AVRegularity.Finite.WeakPositive.Model
import AVRegularity.Proofs.WeakGen.WeakStageHistory
import AVRegularity.CycleComparison.Coarse.Energy.Zero
public import AVRegularity.Construction.Residual.Presentation.ProofMeanFluxSplit
import AVRegularity.CycleComparison.Error.Main
public import AVRegularity.Proofs.QuietAtlas.FirstSourceRenewal
public import AVRegularity.Statements.Intermediate.CycleOutput.PulseMeanField

section
section
/-! `IsLiftSetting` is monotone in the orders `(K, k, L)` (hence in the reserves `q_s, q_f`). A slot
lift stored at larger orders gives the setting at the exact orders a cycle statement asks for. Every
field that mentions `q_s` or `q_f` is a bound for all orders up to the reserve, and the reserves are
monotone in `K` and in `k, L`. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity.Providers.WeakGen.Residual

section Mono

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}
    {Q : LiftOperatorData ι h D} {π : ι → ℝ} {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ}
    {par : Fin 2} {V : ℝ → ℝ → ℝ} {H N K k L K' k' L' qs qf qs' qf' : ℕ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ}

/-- The jet envelope is monotone in the stored orders. -/
theorem weakIsScaledJetEnvelope_mono {edge : ConstituentEdges D h} {I : Set ℝ} {Ks Ls Ks' Ls' : ℕ}
    (hE : IsScaledJetEnvelope π edge I lam Cj Ks Ls b Θ) (hK : Ks' ≤ Ks) (hL : Ls' ≤ Ls) :
    IsScaledJetEnvelope π edge I lam Cj Ks' Ls' b Θ :=
  ⟨hE.nonneg, hE.row_sum, hE.col_sum,
    fun v u r hr q hq => hE.jets v u r (hr.trans hK) q (hq.trans hL)⟩

/-- `IsLiftSetting` is monotone in the orders `(K, k, L)`: a setting at `(K, k, L)` is a setting at
every `(K', k', L') ≤ (K, k, L)` (reserves recomputed, all other data unchanged). -/
theorem weakIsLiftSetting_mono
    (hS : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (hK : K' ≤ K) (hk : k' ≤ k) (hL : L' ≤ L)
    (hqs : qs' = K' + 4 * (H + 1) * (N + D) ^ 2)
    (hqf : qf' = max k' (L' + 2) + H * D + 2 * N + 2 * D) :
    IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K' k' L' qs' qf' CG Cw Cj b Θ := by
  have h1 : qs' ≤ qs := by rw [hqs, hS.qs_eq]; omega
  have h2 : qf' ≤ qf := by rw [hqf, hS.qf_eq]; omega
  exact
    { window := hS.window, e_pos := hS.e_pos, ν_pos := hS.ν_pos, B_pos := hS.B_pos
      ρ_pos := hS.ρ_pos, E_pos := hS.E_pos, ℓ_eq := hS.ℓ_eq, η_eq := hS.η_eq, η_le := hS.η_le
      dstar_eq := hS.dstar_eq, εc_eq := hS.εc_eq, εc_le := hS.εc_le, lam_eq := hS.lam_eq
      lam_le := hS.lam_le, N_ge := hS.N_ge, D_ge := hS.D_ge, qs_eq := hqs, qf_eq := hqf
      mass_pos := hS.mass_pos, G_symm := hS.G_symm, G_meas := hS.G_meas
      G_smooth := fun t ht i j => (hS.G_smooth t ht i j).of_le (by exact_mod_cast h1)
      G_ellip := hS.G_ellip
      G_jets := fun r hr => hS.G_jets r (hr.trans h1)
      v_shear := hS.v_shear
      V_smooth := fun t ht => (hS.V_smooth t ht).of_le (by exact_mod_cast h2)
      V_per := hS.V_per, V_mean := hS.V_mean, v_meas := hS.v_meas
      w_jets := fun q hq => hS.w_jets q (hq.trans h2)
      depth := hS.depth, transverse := hS.transverse, coeff_meas := hS.coeff_meas
      coeff_smooth := fun v u d γ hγ α t ht =>
        CycleComparison.Reconstruction.isBoxSmooth_mono (hS.coeff_smooth v u d γ hγ α t ht) h1 h2
      envelope := weakIsScaledJetEnvelope_mono hS.envelope h1 h2 }

end Mono

end AVRegularity.Providers.WeakGen.Residual
end
end

section
/-! **The four pieces of the weak residual** (definitions only).

At a weak passage of level `i`, the incoming stage `G` has level `i` and the coarse stage `G'` has
level `i − 1`. Take `g = 𝓡_i Ū`, with `Ū` the coarse family. The error `𝔢 = U − Λ_i g` solves
```
(L_i − 𝒮_i)𝔢 = Λ_i𝔇𝓡_{i,R_w}Ū − ∑_𝗉 ϖ_𝗉 Res_𝗉 g − ∑_𝗉 ϖ'_𝗉(T_𝗉 − I)g
                 − ∑_𝗉 ϖ_𝗉(T_𝗉 − I)(𝔐 − 𝔐_𝗉)g,          𝔢(t_*) = 0.
```
Everything here acts on classical fields `a : ℝ → Vec 2 → ∀ v : CompIn G.comps, ℝ` (`WeakField`).
Spatial derivatives are classical (`gradE`, `divE`, `orderedDerivative`). No time derivative of
the field appears in any piece.

The objects:
- **Slot `𝗉 = k`** (odd `k`, among `ocObsPulses i t t`, the set of `Λ_i`).
  - The cutoff is `ϖ_k = ocCutoff i k`.
  - The lift is `T_k = pulsePhysicalLift` with the parameters of `weakGluedLift`
    (`weakSlotLift`). `Λ_i a = ∑_k ϖ_k T_k a` is `weakGluedLift`.
  - The retained means of slot `k` are `𝔐_k a = −∑_{r ≤ depth} pulseMeanField − ν₀Δa`, for the lift
    data of the full fiber (`weakSlotMean`), and `𝔐 = ∑_k ϖ_k 𝔐_k` (`weakGluedMean`).
    - Sign: the lift identity is `(𝒫 − 𝒮)C^{[N]} − C^{[N]}(∂_t + ∑_n ε^n L_n) = ∑ ε^n R_n`,
      so `L_{i−1} − 𝔐_k` has the spatial part
      `b₀·∇ + ∑ ℓ⁻²ε^n L_n`. The stored fluxes `pathMeanFlux`, `weakEddyFlux` are
      `−ℓ⁻²ε^nρ⟨liftFluxX⟩`, whose divergence is `−ℓ⁻²ε^n L_n`.
    - Molecular term: `L_2` at grade zero is `div_X(⟨wT_1a⟩ − ηG∇_Xa)`. Its
      second part is the molecular `−ν₀Δ`, which stays in `L_{i−1}`; the `−ν₀Δa` in `𝔐_k` cancels it,
      and the eddy letters `𝔇_{i,n} = −M^e_n` remain.
    - Degrees `2 … N + D_m` at every grade: the diagonal means above `N + 1` vanish (`P_0𝓑_2C = 0`
      for centered `C`), and the inherited means above the identity orders have zero sources.
- **Operators.**
  - `L a = b·∇a − νΔa` is the spatial part of `∂_t + b·∇ − νΔ` (`weakHeatSpatial`).
  - `𝒮_G a = div ∑_{u,γ,d} a^phys_{γ,d} ∇^{d−1}a_u` is the width-zero coupling of a stage
    (`weakCouplingField`).
- **Slot residual** (`weakSlotResidual`). `Res_k a` is the defect of the slot identity
  `(L_i − 𝒮_i)T_k a − T_k(L_{i−1} − 𝔐_k)a`, with the time derivative of `T_k a` taken with `a`
  frozen at the current time. The time derivative of `a` occurs once on each side and cancels.
  The slot identity gives it the diagonal-remainder form; that is the content of the residual estimate, not of the
  definition.
- **Frontier** (`weakFrontierField`, `weakLetterFlux`).
  - `𝓡_{i,R_w}Ū` is the readout of the words of length exactly `R_w`.
  - `𝔇 = ∑_n 𝔇_{i,n}` is diagonal in the old component. Its coefficient on `v` is `λ_i` times the
    stored coefficient of the letter edge `(v, []) → (v, [n])` of `G'` (word independent:
    `WeakSource.fluxOp` of `.eddy` does not read the word). This needs `R_w ≥ 1`.
- **Pieces** (`weakResidualFrontier`, `weakResidualSlot`, `weakResidualGlueTime`,
  `weakResidualGlueMean`), indexed by `weakResidualPiece`; the residual source is their sum. The
  signs are those of the error equation. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Classical scalar fields on the components of a stage. -/
abbrev WeakField (G : GenStage D ScalarH Dm b j₀) : Type :=
  ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root

/-- The lift `T_k` of slot `k` at level `i` (the summand of `weakGluedLift`). -/
def weakSlotLift (i N depth : ℕ) (G : GenStage D ScalarH Dm b j₀)
    (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)) (k : ℤ)
    (a : WeakField G) : WeakField G :=
  fun t x => pulsePhysicalLift (D.cellScaleSq i) (D.eps (i - 1)) (D.eps i)
    (D.eps i / D.eps (i - 1)) N depth (CcR k) (fun s' y => D.flowOf (i - 1) s' y (D.slotAnchor i k))
    (fun s' y => D.flowOf (i - 1) (D.slotAnchor i k) y s') a t x

open scoped Classical in
/-- The sum of the lift means of slot `k`, `∑_{r ≤ depth} ℓ⁻² ∑_{n=2}^{N+D_m} ε^n L_n^{(r)}`, for the
lift data of the full fiber at the native chain (as in `IsWeakReadoutLifts`); zero off the odd
slots. With the coarse transport it is the spatial part of `L_{i−1} − 𝔐_k`. -/
def weakSlotLiftMean (i N depth : ℕ) (G : GenStage D ScalarH Dm b j₀)
    (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)) (k : ℤ)
    (a : WeakField G) : WeakField G :=
  fun t x => if hk : Odd k then
    ∑ r ∈ Finset.range (depth + 1), pulseMeanField (D.cellScaleSq i) (D.eps (i - 1))
      (D.eps i / D.eps (i - 1)) N r
      (familyLiftData D i k (nativeChain i k) (D.eps (i - 1)) (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      (CcR k) (fun s' y => D.flowOf (i - 1) s' y (D.slotAnchor i k))
      (fun s' y => D.flowOf (i - 1) (D.slotAnchor i k) y s') a t x
  else 0

/-- **The retained means `𝔐_k` of slot `k`**: `𝔐_k a = −∑_{r ≤ depth} pulseMeanField − ν₀Δa`, with
`ν₀` the coarse diffusivity (signs and the molecular term as in the module docstring). -/
def weakSlotMean (i N depth : ℕ) (G : GenStage D ScalarH Dm b j₀)
    (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)) (ν₀ : ℝ) (k : ℤ)
    (a : WeakField G) : WeakField G :=
  fun t x v => -weakSlotLiftMean i N depth G CcR k a t x v -
    ν₀ * divE (fun y => gradE (fun y' => a t y' v) y) x

/-- The glued means `𝔐 = ∑_k ϖ_k 𝔐_k` over the slots of `Λ_i`. -/
def weakGluedMean (i N depth : ℕ) (G : GenStage D ScalarH Dm b j₀)
    (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)) (ν₀ : ℝ)
    (a : WeakField G) : WeakField G :=
  fun t x => ∑ k ∈ ocObsPulses D.α D.q D.Λ i t t,
    ocCutoff D.α D.q D.Λ i k t • weakSlotMean i N depth G CcR ν₀ k a t x

/-- The spatial part `b·∇a − νΔa` of `∂_t + b·∇ − νΔ`, componentwise. -/
def weakHeatSpatial {G : GenStage D ScalarH Dm b j₀} (bv : ℝ → Vec 2 → Vec 2) (ν : ℝ)
    (a : WeakField G) : WeakField G :=
  fun t x v => (∑ j : Fin 2, bv t x j * gradE (fun y => a t y v) x j) -
    ν * divE (fun y => gradE (fun y' => a t y' v) y) x

/-- The width-zero coupling `𝒮_G a = div ∑_{u,γ,d} a^phys_{γ,d} ∇^{d−1}a_u` of a stage. -/
def weakCouplingField (G : GenStage D ScalarH Dm b j₀) (a : WeakField G) : WeakField G :=
  fun t x v => divE (fun y j => (∑ u : CompIn G.comps, ∑ γ : G.fam.Γ v u, ∑ d : Finset.Icc 2 Dm,
    G.physCoeff v u γ d.1 t y (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      orderedDerivative word (fun y' => a t y' u) y)) j) x

/-- **The slot residual** `Res_k a`: the defect of the slot identity
`(L_i − 𝒮_i)T_k a − T_k(L_{i−1} − 𝔐_k)a`, with the time derivative of `T_k a` taken at the frozen
field `a(t)`. `(bi, νi)` is the drift and
diffusivity of the incoming system, `(b₀, ν₀)` those of the coarse system. The spatial part of
`L_{i−1} − 𝔐_k` is `b₀·∇a + weakSlotLiftMean a`: the two `ν₀Δa` cancel. -/
def weakSlotResidual (i N depth : ℕ) (G : GenStage D ScalarH Dm b j₀)
    (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (bi b₀ : ℝ → Vec 2 → Vec 2) (νi ν₀ : ℝ) (k : ℤ) (a : WeakField G) : WeakField G :=
  fun t x v =>
    deriv (fun s => weakSlotLift i N depth G CcR k (fun _ => a t) s x v) t +
      weakHeatSpatial bi νi (weakSlotLift i N depth G CcR k a) t x v -
      weakCouplingField G (weakSlotLift i N depth G CcR k a) t x v -
      weakSlotLift i N depth G CcR k
        (fun s y w => weakHeatSpatial b₀ ν₀ a s y w - weakSlotMean i N depth G CcR ν₀ k a s y w)
        t x v

open scoped Classical in
/-- `𝓡_{i,R}`: the readout of the words of length exactly `R` (weights `λ_i^R = E^{η₀R}`), from
the components of `G'` (level `i − 1`) to those of `G` (level `i`). -/
def weakFrontierField (i Rw : ℕ) (η₀ : ℝ) (G G' : GenStage D ScalarH Dm b j₀)
    (g : CompIn G'.comps → Vec 2 → ℝ) : CompIn G.comps → Vec 2 → ℝ :=
  fun v x => ∑ v' : CompIn G'.comps,
    if compParent i v'.1 = v.1 ∧ (compWord i v'.1).length = Rw then
      (D.eps (i - 1) ^ η₀) ^ Rw * g v' x else 0

open scoped Classical in
/-- The flux of `𝔇 = ∑_{n=2}^{N+1} 𝔇_{i,n}` on a field of the old components: on the component `v`,
`λ_i` times the stored coefficient of the letter edges `(v, []) → (v, [n])` of `G'`, applied to
`∇^{d−1}a_v` (zero if the letter component is absent). -/
def weakLetterFlux (i N : ℕ) (η₀ : ℝ) (G G' : GenStage D ScalarH Dm b j₀) (a : WeakField G)
    (t : ℝ) (x : Vec 2) (v : CompIn G.comps) : Fin 2 → ℝ :=
  fun j => ∑ n ∈ Finset.Icc 2 (N + 1),
    if h : v.1 ∈ G'.comps ∧ succComp i v.1 [WordLetter.eddy n] ∈ G'.comps then
      ∑ γ : G'.fam.Γ ⟨succComp i v.1 [WordLetter.eddy n], h.2⟩ ⟨v.1, h.1⟩, ∑ d : Finset.Icc 2 Dm,
        D.eps (i - 1) ^ η₀ *
          G'.physCoeff ⟨succComp i v.1 [WordLetter.eddy n], h.2⟩ ⟨v.1, h.1⟩ γ d.1 t x
            (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              orderedDerivative word (fun y => a t y v) x) j
    else 0

/-- **The response frontier** `Λ_i𝔇𝓡_{i,R_w}Ū`: the glued lift of `div` of the letter flux of the
length-`R_w` readout `H`. -/
def weakResidualFrontier (i N depth Rw : ℕ) (η₀ : ℝ) (G G' : GenStage D ScalarH Dm b j₀)
    (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → CompIn G'.comps → Vec 2 → ℝ) : WeakField G :=
  fun t x v => ∑ k ∈ ocObsPulses D.α D.q D.Λ i t t, ocCutoff D.α D.q D.Λ i k t *
    weakSlotLift i N depth G CcR k
      (fun s y w => divE (fun y' => weakLetterFlux i N η₀ G G'
        (fun s' y'' w' => weakFrontierField i Rw η₀ G G' (aU s') w' y'') s y' w) y) t x v

/-- **The slot residuals** `−∑_k ϖ_k Res_k g`. -/
def weakResidualSlot (i N depth : ℕ) (G : GenStage D ScalarH Dm b j₀)
    (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (bi b₀ : ℝ → Vec 2 → Vec 2) (νi ν₀ : ℝ) (g : WeakField G) : WeakField G :=
  fun t x v => -∑ k ∈ ocObsPulses D.α D.q D.Λ i t t,
    ocCutoff D.α D.q D.Λ i k t * weakSlotResidual i N depth G CcR bi b₀ νi ν₀ k g t x v

/-- **The first gluing term** `−∑_k ϖ'_k(T_k − I)g`. -/
def weakResidualGlueTime (i N depth : ℕ) (G : GenStage D ScalarH Dm b j₀)
    (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (g : WeakField G) : WeakField G :=
  fun t x v => -∑ k ∈ ocObsPulses D.α D.q D.Λ i t t,
    deriv (ocCutoff D.α D.q D.Λ i k) t * (weakSlotLift i N depth G CcR k g t x v - g t x v)

/-- **The second gluing term** `−∑_k ϖ_k(T_k − I)(𝔐 − 𝔐_k)g`. -/
def weakResidualGlueMean (i N depth : ℕ) (G : GenStage D ScalarH Dm b j₀)
    (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)) (ν₀ : ℝ)
    (g : WeakField G) : WeakField G :=
  fun t x v => -∑ k ∈ ocObsPulses D.α D.q D.Λ i t t, ocCutoff D.α D.q D.Λ i k t *
    (weakSlotLift i N depth G CcR k
        (fun s y w => weakGluedMean i N depth G CcR ν₀ g s y w -
          weakSlotMean i N depth G CcR ν₀ k g s y w) t x v -
      (weakGluedMean i N depth G CcR ν₀ g t x v - weakSlotMean i N depth G CcR ν₀ k g t x v))

/-- The coarse readout `g = 𝓡_iŪ` of a classical representative `aU` of the coarse family. -/
def weakResidualReadout (i : ℕ) (η₀ : ℝ) (G G' : GenStage D ScalarH Dm b j₀)
    (aU : ℝ → CompIn G'.comps → Vec 2 → ℝ) : WeakField G :=
  fun t x v => weakReadoutStep i η₀ G G' (aU t) v x

/-- The pieces, indexed by `Fin 4`: `0` the frontier, `1` the slot residuals, `2` the first and `3`
the second gluing term. -/
def weakResidualPiece (i N depth Rw : ℕ) (η₀ : ℝ) (G G' : GenStage D ScalarH Dm b j₀)
    (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (bi b₀ : ℝ → Vec 2 → Vec 2) (νi ν₀ : ℝ) (aU : ℝ → CompIn G'.comps → Vec 2 → ℝ) :
    Fin 4 → WeakField G
  | 0 => weakResidualFrontier i N depth Rw η₀ G G' CcR aU
  | 1 => weakResidualSlot i N depth G CcR bi b₀ νi ν₀ (weakResidualReadout i η₀ G G' aU)
  | 2 => weakResidualGlueTime i N depth G CcR (weakResidualReadout i η₀ G G' aU)
  | 3 => weakResidualGlueMean i N depth G CcR ν₀ (weakResidualReadout i η₀ G G' aU)

end AVRegularity.Providers.WeakGen.Residual
end
end

section
/-! **The second menu inequality forces a response order `R_w ≥ 1`**.

The comparison of a weak passage is stated under the two menu inequalities; the second is
`P_w + 2q^{J_w} + 1 + q^{J_w} + 1 < 2a_*(R_w + 1)` with `a_* = (q + 2)(q - 1)(1 + α)/(q + 1)`.
For admissible `q < 17/16` and `α < 1/3` one has `a_* ≤ 1`, while the left side exceeds `5`. So
the inequality fails at `R_w = 0`: every passage of the comparison has `R_w ≥ 1`, and the stage
`i - 1` has its letter components. The degenerate menu `R_w = 0`, where no letter component
exists and the stored eddy letters vanish, is not a case of the comparison.

The degenerate cases are included: `R_w = 0` gives `2a_* ≤ 2 < 5`; the statement does not read
`N_w`. -/

@[expose] public section

namespace AVRegularity.Providers.WeakGen.Residual

open WeakEntryProofs.Assembly

/-- The abstract form: `P + 3q^J + 2 < 2(q + 2)(q - 1)(1 + α)/(q + 1)·(R + 1)` forces `R ≥ 1`. -/
theorem menu_response_pos {α q P : ℝ} {J Rw : ℕ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hq₁ : 1 < q)
    (hq₂ : q < 17 / 16) (hP : 0 < P)
    (hR : P + 2 * q ^ J + 1 + q ^ J + 1 <
      2 * ((q + 2) * ((q - 1) * (1 + α) / (q + 1))) * (Rw + 1)) : 1 ≤ Rw := by
  by_contra hne
  have h0 : Rw = 0 := by omega
  subst h0
  have hqJ : 1 ≤ q ^ J := one_le_pow₀ hq₁.le
  have h1 : (q - 1) * (1 + α) ≤ 1 / 16 * (4 / 3) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have h2 : (q - 1) * (1 + α) / (q + 1) ≤ 1 / 16 * (4 / 3) :=
    (div_le_self (mul_nonneg (by linarith) (by linarith)) (by linarith)).trans h1
  have h3 : 0 ≤ (q - 1) * (1 + α) / (q + 1) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h4 : (q + 2) * ((q - 1) * (1 + α) / (q + 1)) ≤ 49 / 16 * (1 / 16 * (4 / 3)) :=
    mul_le_mul (by linarith) h2 h3 (by norm_num)
  simp only [Nat.cast_zero, zero_add, mul_one] at hR
  linarith

/-- **Every passage of the comparison has `R_w ≥ 1`.** -/
theorem weakMenu_one_le_Rw {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (hR : A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 <
      2 * weakAStar B.α B.q * (A.Rw + 1)) : 1 ≤ A.Rw :=
  menu_response_pos B.hα₀ B.hα₁ B.hq.1 B.hq.2.1 A.Pw_pos (by
    unfold weakAStar ocGamma at hR
    exact hR)

end AVRegularity.Providers.WeakGen.Residual
end
end
end

section
section
/-! **The comparison residual over its four pieces: the residual equation and the residual
estimate**.

The pieces are those defined above (`weakResidualPiece`), at a weak passage of level `i`
(`weakComparisonPiece`):
- incoming stage `c.stage i`, diffusivity `κ_M`, drift `Φ_i`;
- coarse stage `c.stage (i − 1)`, with the diffusivity and drift of its level (those of the
  passage solution in `IsWeakPassageSolution`);
- lift coefficients `h.CcR i`, classical representative `h.aU`.

* A presentation `(F, g)` of a classical source `S`: at almost every time and for every smooth
  periodic test `φ`, `∫ Sφ = −∫ F·∇φ + ∫ gφ` on the unit cell, so `S = div F + g` in
  distributions.
* The exact residual equation: for every time-measurable presentation `(F, g)` of the residual
  source, the error `h.e` solves the zero-data regularized system of the stage with the forcing
  `(F, g)`. This includes `𝔢(t_*) = 0` and the old coupling in the equation.
* The estimate for the piece `p`: the piece has a time-measurable presentation at
  `plan.forcingOrder R` whose forcing cost is at most `forceC/8 · ε_M^{P_w + 2q^{J_w} + 1} Φ`.
  The residual estimate is the estimate for all four pieces.

The residual equation and the residual estimate give the residual, with the pieces of the sum
presented separately. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen.Residual

open WeakEntryProofs WeakEntryProofs.Assembly

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The piece `p` of the weak residual at a passage, from the comparison input. -/
abbrev weakComparisonPiece {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ} (h : WeakComparisonInput r i) (p : Fin 4) :
    WeakField (c.stage i) :=
  weakResidualPiece i A.Nw (A.Jw * A.Rw) A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.CcR i)
    (streamVel (c.D.Φ i)) (streamVel (c.D.Φ (c.stage (i - 1)).level)) (c.D.κ c.M)
    (c.D.kap (c.stage (i - 1)).level) h.aU p

end AVRegularity.Providers.WeakGen.Residual
end
end

section
/-! **Jets of sums of torus classes**, for the sum of the four presentations of the residual
pieces.

* `torusHk_jet_zero_ae`, `torusHk_jet_sum_ae`: the jets of the zero class vanish, and the jets of
  a finite sum of torus classes are the sums of the jets, almost everywhere on the unit cube. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen.Residual

open WeakEntryProofs WeakEntryProofs.Assembly

section Jets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- The jets of the zero class vanish almost everywhere on the unit cube. -/
theorem torusHk_jet_zero_ae {K : ℕ} :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ a : JetIndex2 K,
      (0 : TorusHk K E).toFunction.jet a x = 0 := by
  filter_upwards [CycleComparison.Coarse.jet_add_ae (0 : TorusHk K E) 0] with x hx a
  have h := hx a
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- The jets of a finite sum of torus classes are the sums of the jets, almost everywhere. -/
theorem torusHk_jet_sum_ae {K : ℕ} {ι : Type*} (s : Finset ι) (U : ι → TorusHk K E) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ a : JetIndex2 K,
      (∑ p ∈ s, U p).toFunction.jet a x = ∑ p ∈ s, (U p).toFunction.jet a x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [torusHk_jet_zero_ae (E := E) (K := K)] with x hx a
    simpa using hx a
  | insert p s hp ih =>
    filter_upwards [CycleComparison.Coarse.jet_add_ae (U p) (∑ q ∈ s, U q), ih] with x h1 h2 a
    rw [Finset.sum_insert hp, Finset.sum_insert hp, h1 a, h2 a]

end Jets

section Bridge

end Bridge

end AVRegularity.Providers.WeakGen.Residual
end
end

section
/-! **The residual estimate: its shared layers, as named statements**.

Every piece of the weak residual is a classical field. The residual estimate asks for a
`TorusHk`-valued presentation of each piece with a cost bound. The layers below are shared by the
four pieces.

* **Classical trajectories.** A family of classical periodic fields `f t` of class `C^k`, jointly
  measurable with its derivatives, is the classical representative of an almost everywhere
  strongly measurable trajectory in `TorusHk k`. With `classicalFactorialSq_eq_of_rep`, the
  factorial norms of the trajectory are the classical factorial densities of `f t`.
* **Classical presentations.** A classical flux `Ψ` and scalar `q` at the forcing order give
  `(F, g)` presenting `div Ψ + q`, measurable in time, with forcing cost at most the classical cost
  `weakClassicalForcingCost` (the same formula as `weakComparisonForcingCost`, on classical
  densities, at the radius `c·ε_i`).
* **The coarse readout energy** (`WeakCoarseReadoutEnergyStatement`). The classical representative
  `h.aU` of the coarse family is smooth to the order `kOf R + 1`, continuously in time. The
  classical strong energy at the coarse radius `c·ε_{i−1}` and order `kOf R`
  - of the readout `𝓡_iŪ` is at most `C Φ`;
  - of the length-`R_w` readout `𝓡_{i,R_w}Ū` is at most `C x^{2a_*R_w} Φ`.

  Here `Φ = h.Φ` bounds the incoming family on `[t_{i+1}, T]`. This is the only place where the
  coarse family enters the lift-side estimates. Its proof is the higher order of the reduction, the
  passage energy with data and the quiet trace, with the fresh gain `Pe²` per
  letter. The order function `kOf` depends on the request only, never on `D_m`.

* **The slot lifts** (`WeakSlotLiftStatement`). Above floors of the lift orders `sX`,
  `sZ`, of the carrier and of the level, every passage stage `c.stage i` has, at every odd slot,
  the slot lift `WeakPositiveSlot` of the finite case: an `IsLiftSetting` at a capped order, an
  `IsLiftSequence` for its coefficients, and the native source identities. With
  `weak_positive_support_identification`, the readout lifts `h.CcR i k` of `IsWeakReadoutLifts`
  are the coefficients of the slot lift on the slot window, at every `sX sZ`. With
  `weak_positive_graded_recurrence` they have the graded jets. This is the only input of the cycle
  statements (`cycle_lift_identity`, `cycle_residual_differentiated`,
  `cycle_residual_partition_differentiated`, `cycle_residual_coarse_flux_differentiated`) at a weak
  passage. It is `WeakPlateauParentSettingStatement` read on a passage instance.

The lift-side assemblies of the four pieces are in the residual estimate modules. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen.Residual

open WeakEntryProofs WeakEntryProofs.Assembly

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The classical forcing cost of a flux `Ψ` and a scalar `q` on the components of a stage: the
formula of `weakComparisonForcingCost` on the classical factorial densities through order `k`, at
the radius `ρ`, diffusivity `ν`, masses `π`, window `I`. -/
def weakClassicalForcingCost {G : GenStage D ScalarH Dm b j₀} (ν ρ : ℝ)
    (π : CompIn G.comps → ℝ) (I : Set ℝ) (k : ℕ)
    (Ψ : ℝ → Vec 2 → CompIn G.comps → Fin 2 → ℝ) (q : WeakField G) : ℝ≥0∞ :=
  (∑ v, (ENNReal.ofReal (π v))⁻¹ *
    ((ENNReal.ofReal ν)⁻¹ *
        (∫⁻ t in I, classicalFactorialSq ρ k
          (fun x => (WithLp.toLp 2 (Ψ t x v) : PiLp 2 (fun _ : Fin 2 => ℝ)))) +
      (∫⁻ t in I, (classicalFactorialSq ρ k (fun x => q t x v)) ^ (1 / 2 : ℝ)) ^ 2)) ^ (1 / 2 : ℝ)

/-- **(iv) The coarse readout energy**, at the classical order `kOf R`: the
representative `h.aU` is of class `C^{kOf R + 1}`, with derivatives continuous in time and space on
the window; the readout `𝓡_iŪ` has classical strong energy at most `C Φ` at the coarse radius
`c·ε_{i−1}`, and the length-`R_w` readout at most `C x^{2a_*R_w} Φ`. The constant is chosen before
the data. -/
def WeakCoarseReadoutEnergyStatement (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ) :
    Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1) →
    A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1) →
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
      c.M < i → i ≤ c.M + A.Jw → ∀ h : WeakComparisonInput r i,
      (∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ v',
        ContDiff ℝ ((kOf R + 1 : ℕ) : ℕ∞) (h.aU t v')) ∧
      (∀ v' n, n ≤ kOf R + 1 → ∀ w : DerivativeWord2 n,
        ContinuousOn (fun p : ℝ × Vec 2 => orderedDerivative w (h.aU p.1 v') p.2)
          (Set.Icc (r.tq i) (r.a + A.T₀) ×ˢ Set.univ)) ∧
      classicalStrongEnergy (plan.radius R * c.D.eps (i - 1)) (c.D.κ c.M)
          (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (Set.Icc (r.tq i) (r.a + A.T₀)) (kOf R)
          (weakResidualReadout i A.η₀ (c.stage i) (c.stage (i - 1)) h.aU) ≤
        ENNReal.ofReal (C * h.Φ) ∧
      classicalStrongEnergy (plan.radius R * c.D.eps (i - 1)) (c.D.κ c.M)
          (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (Set.Icc (r.tq i) (r.a + A.T₀)) (kOf R)
          (fun t x v => weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v x) ≤
        ENNReal.ofReal (C * c.D.eps c.M ^ (2 * weakAStar B.α B.q * A.Rw) * h.Φ)

/-- **(ii) The slot lifts of a passage instance**: for every readout order `Lr ≥ J_wN_w` there
are floors `SX`, `SZ` of the lift orders, chosen before the request, such that for every request
above them there are slot-lift parameters `P` at the order `Lr + 3`, carrier constants and a level
floor (a function of the carrier start), with: every passage stage `c.stage i`, `M < i ≤ M + J_w`,
of an instance above these floors has the positive geometry and a slot lift at every odd slot,
with the weak masses. -/
def WeakSlotLiftStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (Lr : ℕ), A.Jw * A.Nw ≤ Lr →
    ∃ SX SZ : ℕ, ∀ R : WeakPassageRequest A, SX ≤ R.sX → SZ ≤ R.sZ →
    ∃ (P : Finite.WeakLift.WeakPositiveParameters A.Nw (A.Jw * A.Rw) (Lr + 3)) (CH Υ : ℝ)
      (M₀ : ℕ → ℕ),
      ∀ c : WeakPassageInstance plan R,
        IsCarrierStart B.α B.q A.Λ A.bw CH Υ c.j₀ → M₀ c.j₀ ≤ c.M →
        ∀ i, c.M < i → i ≤ c.M + A.Jw →
          Finite.WeakLift.WeakPositiveGeometry P i (c.stage i) ∧
          Nonempty (∀ slot : OddSlot, Finite.WeakLift.WeakPositiveSlot P i (c.stage i)
            (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) slot)

end AVRegularity.Providers.WeakGen.Residual
end
end
end

section
section
/-! **The slot lifts with their choices exposed, and their quietness**.

**The exposed choices.** The factory of the slot lifts (`weak_parent_setting_on_of_ingredients`)
makes explicit choices that `WeakPlateauParentSettingStatement` hides behind existentials:
- the carrier constants are `(1, 400)`, those of a passage instance;
- the slot-lift parameters are `capMax = max 2 (1 + J_wN_w)`,
  `slowOrder = Lr + 3 + (N_w + capMax)`, `fastOrder = Lr + 3` (`weakParentParameters`);
- the floors of the lift orders are `0`.
This is `WeakSlotLiftStatement` with these exposed. It answers two needs of the assemblies of the
residual estimate.
- The cycle statements take the setting at exact orders, for example
  `K = A_cl + 2 + r + cap·(H + 1)·N` in `cycle_residual_partition_differentiated`. With the
  slot-lift orders explicit, the consumer chooses `Lr ≥ A_cl + r + capMax·(H + 1)·N + max k_l L_l`
  and lowers the orders with `weakIsLiftSetting_mono`. The reserve fields of
  `WeakPositiveParameters` alone do not give this (`N = 16, H = 100, U = 19, cap = 100,
  slowOrder = 135, fastOrder = 19`).
- `r = plan.forcingOrder R` depends on the request, so `Lr` does. This is possible only because
  the floors of `sX`, `sZ` do not depend on `Lr`.

**`WeakSlotNativeQuietStatement`.**
`cycle_residual_partition_differentiated` asks `IsQuietOn Q.edge` of the lift data `Q` of the
slot lift, on the cell-time transition interval. A slot lift `WeakPositiveSlot` identifies the
metric, the drift and the source operators of `Q` with the native data, not its edge list, so
quietness of `Q.edge` is not a consequence of the fields of the slot lift (a constituent with zero
map and a fast-dependent coefficient changes no source operator).

The binder splits in two.
* **The native data is quiet** (`WeakSlotNativeQuietStatement`, below): the lift data of the stage's
  own fibre at an odd slot has zero cell drift and fast-independent edge coefficients at the cell
  times of the slot window whose physical times are trimmed quiet times of the level. This is a
  statement about the stage, with no slot lift.
  - Drift: the native drift is the shear of the pulses of the level, zero at quiet times.
  - Edges: fast independence of the family of a weak stage on the trimmed quiet times (the clause
    of the weak stages, `weakStageIndependence` and `weakGen_stage_slot_laws` at the level `i`),
    passed to the lift edges of the fibre.
* **The slot lift inherits it**: the factory builds `Q.edge` from the native edges by clamping the
  time to the slot window (`windowEdges`) and restricting the degrees (`restrictLiftData`), or as
  the empty list. So fast independence passes from the native edges to `Q.edge` on subsets of the
  slot window. The slot lift does not record this; as a field of `WeakPositiveSlot` (finite case)
  it would read:
  `edge_fast : ∀ S ⊆ Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1),
    (∀ v u d, ∀ γ ∈ (weakPositiveNativeData i G slot ρ).edge v u d, ∀ α,
      IsFastIndependentOn S (γ.coeff α)) →
    ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α, IsFastIndependentOn S (γ.coeff α)`.
  With `drift_eq` this gives `IsQuietOn A.Q.edge (fun τ z => √A.Q.η • A.Q.v τ z) S` for every
  slot lift `A`.

The degenerate cases are included:
- `R_w = 0`: the native edge lists are empty and the edge clause of the quietness statement is
  vacuous.
- `S = ∅`: both clauses of the quietness statement are vacuous.
- A time in a pulse: it is not a trimmed quiet time, and nothing is asserted there.
- `J_w = N_w = 1`: `capMax = 2`, the minimal cap; `slowOrder = Lr + 6`.
- Constants: `capMax`, the orders and `Lr` depend on the menu and the request. `D_m` enters
  nowhere. -/

@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.WeakEntryProofs.Assembly
namespace AVRegularity.Providers.WeakGen.Residual

/-- The cap of the slot lifts of the menu: `max 2 (1 + J_wN_w)` (`weakParentCap`). -/
def weakSlotCap {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ :=
  max 2 (1 + A.Jw * A.Nw)

/-- **(ii-q) The native slot data of a passage stage is quiet on trimmed quiet times.** `S` is a set
of cell times of the slot window; `cellScaleSq i · t` is the physical time. -/
def WeakSlotNativeQuietStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ), c.M < i → i ≤ c.M + A.Jw →
  ∀ (slot : OddSlot) (S : Set ℝ),
    S ⊆ Set.Icc (Finite.WeakLift.weakSlotLeft c.D i slot.1)
      (Finite.WeakLift.weakSlotRight c.D i slot.1) →
    (∀ t ∈ S, c.D.cellScaleSq i * t ∈ ocTrimmedQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i) →
    IsQuietOn (Finite.WeakLift.weakPositiveNativeData i (c.stage i) slot).edge
      (fun τ z => Real.sqrt (Finite.WeakLift.weakPositiveNativeData i (c.stage i) slot).η •
        (Finite.WeakLift.weakPositiveNativeData i (c.stage i) slot).v τ z) S

end AVRegularity.Providers.WeakGen.Residual
end
end

section
/-! The classical forcing cost `weakClassicalForcingCost` is bounded by the sum, over the
derivative words of order at most `S`, of the residual norms `residualNorm` of `ρ^j ∂^w (Ψ, q)`.
This is the converse-free direction needed to convert the output of `cycle_residual_differentiated`
(a bound on `residualNorm (rs^j ∂^β ·)`) into a bound on the cost of the classical presentation.
The factorial weights `ρ^{2j}/(j!)²` are at most `ρ^{2j}`; the only non-formal step is the
Minkowski inequality `ℓ²_v(L¹_t) ≤ L¹_t(ℓ²_v)` (`weakResidualCost_minkowski`), which costs nothing
in the number of components. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen.Residual

theorem weakResidualCost_sum_lintegral_le {α κ : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset κ) (f : κ → α → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ t, f i t ∂μ ≤ ∫⁻ t, ∑ i ∈ s, f i t ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (add_le_add_right ih _).trans ?_
    refine (le_lintegral_add _ _).trans_eq ?_
    simp only [Finset.sum_insert ha]

/-- Minkowski for the integral against the Euclidean norm of a finite family, in `[0,∞]`. -/
theorem weakResidualCost_minkowski {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]
    (h : ι → α → ℝ≥0∞) :
    (∑ v, (∫⁻ t, h v t ∂μ) ^ 2) ^ (1 / 2 : ℝ) ≤
      ∫⁻ t, (∑ v, (h v t) ^ 2) ^ (1 / 2 : ℝ) ∂μ := by
  set I := ∫⁻ t, (∑ v, (h v t) ^ 2) ^ (1 / 2 : ℝ) ∂μ with hI
  by_cases hItop : I = ⊤
  · rw [hItop]; exact le_top
  have hA : ∀ v, ∫⁻ t, h v t ∂μ ≠ ⊤ := by
    intro v
    refine ne_top_of_le_ne_top hItop (lintegral_mono fun t => ?_)
    calc h v t = ((h v t) ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ ≤ _ := ENNReal.rpow_le_rpow
          (Finset.single_le_sum (f := fun v => (h v t) ^ 2) (fun _ _ => zero_le)
            (Finset.mem_univ v)) (by norm_num)
  set S := ∑ v, (∫⁻ t, h v t ∂μ) ^ 2 with hS
  have hStop : S ≠ ⊤ := by
    refine ENNReal.sum_ne_top.2 fun v _ => ?_
    exact ENNReal.pow_ne_top (hA v)
  by_cases hS0 : S = 0
  · rw [hS0]; simp
  have hr0 : S ^ (1 / 2 : ℝ) ≠ 0 := by
    simpa [ENNReal.rpow_eq_zero_iff] using hS0
  have hrtop : S ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hStop
  have hsq : S = S ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_add _ _ hS0 hStop]; norm_num
  have key : S ≤ S ^ (1 / 2 : ℝ) * I := by
    calc S = ∑ v, (∫⁻ t, h v t ∂μ) * ∫⁻ t, h v t ∂μ := by
          simp only [hS, sq]
      _ = ∑ v, ∫⁻ t, (∫⁻ t', h v t' ∂μ) * h v t ∂μ := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [lintegral_const_mul' _ _ (hA v)]
      _ ≤ ∫⁻ t, ∑ v, (∫⁻ t', h v t' ∂μ) * h v t ∂μ := weakResidualCost_sum_lintegral_le _ _
      _ ≤ ∫⁻ t, S ^ (1 / 2 : ℝ) * (∑ v, (h v t) ^ 2) ^ (1 / 2 : ℝ) ∂μ := by
          refine lintegral_mono fun t => ?_
          have := ENNReal.inner_le_Lp_mul_Lq (Finset.univ : Finset ι)
            (fun v => ∫⁻ t', h v t' ∂μ) (fun v => h v t) Real.HolderConjugate.two_two
          simpa [hS, one_div] using this
      _ = S ^ (1 / 2 : ℝ) * I := lintegral_const_mul' _ _ hrtop
  exact (ENNReal.mul_le_mul_iff_right hr0 hrtop).1 (hsq.symm.le.trans key)

section Parts

variable {ι : Type*}

/-- The `ρ^j ∂^w` scalar part of the residual norm integrand, on the unit cell. -/
def weakResidualCostScal (q : ℝ → Vec 2 → ι → ℝ) (ρ : ℝ) {j : ℕ}
    (w : DerivativeWord2 j) (t : ℝ) (v : ι) : ℝ≥0∞ :=
  ∫⁻ x in AVenhance.unitCube, ‖ρ ^ j * orderedDerivative w (fun x' => q t x' v) x‖ₑ ^ 2

theorem weakResidualCost_enorm_pow_sq (ρ : ℝ) (j : ℕ) :
    ‖ρ ^ j‖ₑ ^ 2 = ENNReal.ofReal (ρ ^ (2 * j)) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), norm_pow, Real.norm_eq_abs,
    ← pow_mul, mul_comm j 2, pow_mul, sq_abs, ← pow_mul]

theorem weakResidualCost_coeff_le (ρ : ℝ) (j : ℕ) (d : ℝ) :
    ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) * ‖d‖ₑ ^ 2 ≤ ‖ρ ^ j * d‖ₑ ^ 2 := by
  rw [enorm_mul, mul_pow, weakResidualCost_enorm_pow_sq]
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have h1 : (1 : ℝ) ≤ ((j.factorial : ℝ)) ^ 2 := by
    have : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
    nlinarith
  have h0 : 0 ≤ ρ ^ (2 * j) := by rw [pow_mul]; positivity
  exact div_le_self h0 h1

theorem weakResidualCost_cfs_scal_le (q : ℝ → Vec 2 → ι → ℝ) (S : ℕ) (t : ℝ) (ρ : ℝ) (v : ι) :
    classicalFactorialSq ρ S (fun x => q t x v) ≤
      ∑ j ∈ Finset.range (S + 1), ∑ w : DerivativeWord2 j, weakResidualCostScal q ρ w t v := by
  unfold classicalFactorialSq
  refine Finset.sum_le_sum fun j hj => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  unfold weakResidualCostScal
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun x => weakResidualCost_coeff_le ρ j _

end Parts

end AVRegularity.Providers.WeakGen.Residual
end
end

section
/-! **Every stage of a weak construction below the root is presented by transfers**
(native quietness). `weakConstruction_stage_presentation` presents the stage `M`; the
same argument presents the stage `i`, `M ≤ i < M + J`, as the output of the passage into `i + 1`,
with the carried finer invariant, and it is natural. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly

namespace AVRegularity.Providers.WeakGen

open QuietAtlas WeakEntryProofs

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The stage `i` of a weak construction is presented by transfers**, with the carried finer
invariant, for `M ≤ i < M + J`; it is natural up to the finest level. -/
theorem weakNativeQuietStagePresentation (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (hcell : ∀ m, 0 < D.cellScaleSq m) {P : ProvParams} {Mn : WeakMenu} {M J : ℕ} {rW : ℝ}
    {r : ℕ} {stage : ℕ → GenStage D ScalarH Dm b j₀}
    (hc : IsWeakConstruction D P Mn M J rW r stage) {i : ℕ} (hMi : M ≤ i) (hiJ : i < M + J) :
    ∃ Q : QuietPresentation (stage i), Q.AllTransfer ∧
      FinerHistoryInvariant (stage i) Q (M + J) ∧ (stage i).IsNatural (M + J) := by
  obtain ⟨ihinv, ihcov⟩ :=
    weakConstruction_history hΛ hζ hb hstart hcell hc (M + J - (i + 1)) (by omega)
  rw [show M + J - (M + J - (i + 1)) = i + 1 by omega] at ihinv ihcov
  have hpass := (hc.2.2 (i + 1) (by omega) (by omega)).1
  obtain ⟨w⟩ := IsWeakPassage.witness hpass
  have hlv := EntryWeakProofs.weakConstruction_level P Mn M J r rW stage hc
  have hlev : (stage (i + 1)).level = (stage (i + 1 - 1)).level + 1 := by
    rw [hlv _ (by omega) (by omega), hlv _ (by omega) (by omega)]
    omega
  have hnat : (stage (i + 1 - 1)).IsNatural (M + J) := by
    have h := hpass.2.2.2.2.1
    rwa [hc.1] at h
  exact ⟨weakPassagePresentation w hlev, weakPassagePresentation_allTransfer w hlev,
    weakPassage_finerHistory hζ hΛ w hlev (hcell _) ihcov ihinv, hnat⟩

end AVRegularity.Providers.WeakGen
end
end

section
/-! **The forcing cost from the mass bounds of a residual pair**.

The physical lift of a reconstruction window bounds its residual `(R_res, q_res)` in the mass
forms `FluxMassLe` (`(ν⁻¹ ∫ ‖R‖²_{ρ;π})^{1/2} ≤ X₁`) and `ScalarMassLe` (`∫ ‖q‖_{ρ;π} ≤ X₂`). The
forcing cost of a weak passage (`weakComparisonForcingCost`) sums over the components after the
time integrals: `(∑_v π_v⁻¹ (ν⁻¹ ∫ |F_v|² + (∫ |g_v|)²))^{1/2}`.

* `mixedCost_le_of_mass`: the mixed cost is at most `X₁ + X₂`. The flux part is an identity; the
  scalar part is Minkowski's inequality `ℓ²_v(L¹_t) ≤ L¹_t(ℓ²_v)` (`weakResidualCost_minkowski`).
* `weakComparisonForcingCost_le_of_mass`: the same for the forcing cost of a passage.

The degenerate cases are included: `F = 0`, `g = 0` give `0 ≤ X₁ + X₂`; one component is the
definition of the two mass forms; an empty family has cost `0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Residual.Presentation
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen.Residual

open WeakEntryProofs WeakEntryProofs.Assembly CycleComparison.Coarse

/-- **The mixed cost of a flux and a scalar family from their mass bounds.** -/
theorem mixedCost_le_of_mass {ι : Type} [Fintype ι] {h : ι → Type}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {k : ℕ} (ν ρ : ℝ) (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (a b : ℝ) (F : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (g : ∀ v, ℝ → TorusHk k (h v)) {X₁ X₂ : ℝ}
    (hF : FluxMassLe (ι := ι) (h := h) (K := fun _ => k) ν ρ π (Set.Icc a b) F X₁)
    (hg : ScalarMassLe (ι := ι) (h := h) (K := fun _ => k) ρ π (Set.Icc a b) g X₂) :
    (∑ v, (ENNReal.ofReal (π v))⁻¹ *
      ((ENNReal.ofReal ν)⁻¹ *
        (∫⁻ t in Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (F v t).val)) +
        (∫⁻ t in Set.Icc a b,
          ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g v t).val))) ^ 2)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (X₁ + X₂) := by
  classical
  obtain ⟨hFm, hFb⟩ := hF
  obtain ⟨hgi, hgb⟩ := hg
  have hX₁ : 0 ≤ X₁ := (Real.sqrt_nonneg _).trans hFb
  have hX₂ : 0 ≤ X₂ := (integral_nonneg fun _ => Real.sqrt_nonneg _).trans hgb
  -- the flux part is the mass form
  have hA : ∀ v, ∫⁻ t in Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (F v t).val) =
      ENNReal.ofReal (∫ t in Set.Icc a b, factorialNormSq ρ (F v t).val) := fun v =>
    (ofReal_integral_eq_lintegral_ofReal (integrable_factorialNormSq_torus (hFm v))
      (Filter.Eventually.of_forall fun t => factorialNormSq_nonneg _ _)).symm
  have hIn : ∀ v, 0 ≤ ∫ t in Set.Icc a b, factorialNormSq ρ (F v t).val := fun v =>
    integral_nonneg fun t => factorialNormSq_nonneg _ _
  have hflux : ∑ v, (ENNReal.ofReal (π v))⁻¹ * ((ENNReal.ofReal ν)⁻¹ *
        ∫⁻ t in Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (F v t).val)) =
      ENNReal.ofReal (ν⁻¹ * ∫ s in Set.Icc a b,
        massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π
          (fun v => (F v s).val)) := by
    unfold massNormSq
    rw [integral_finsetSum _ fun v _ =>
      (integrable_factorialNormSq_torus (hFm v)).const_mul _]
    simp only [integral_const_mul]
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun v _ =>
      mul_nonneg (inv_nonneg.2 hν.le) (mul_nonneg (inv_nonneg.2 (hπ v).le) (hIn v))]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hA v, ENNReal.ofReal_mul (inv_nonneg.2 hν.le),
      ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le), ENNReal.ofReal_inv_of_pos hν,
      ENNReal.ofReal_inv_of_pos (hπ v)]
    ring
  have hmnF : ∀ s, 0 ≤ massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => k) ρ π (fun v => (F v s).val) := fun s => by
    unfold massNormSq
    exact Finset.sum_nonneg fun v _ =>
      mul_nonneg (inv_nonneg.2 (hπ v).le) (factorialNormSq_nonneg _ _)
  have hmng : ∀ s, 0 ≤ massNormSq (E := h) (K := fun _ => k) ρ π (fun v => (g v s).val) :=
    fun s => by
      unfold massNormSq
      exact Finset.sum_nonneg fun v _ =>
        mul_nonneg (inv_nonneg.2 (hπ v).le) (factorialNormSq_nonneg _ _)
  have hfluxle : (∑ v, (ENNReal.ofReal (π v))⁻¹ * ((ENNReal.ofReal ν)⁻¹ *
        ∫⁻ t in Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (F v t).val))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal X₁ := by
    rw [hflux, ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg (inv_nonneg.2 hν.le) (integral_nonneg hmnF)) (by norm_num),
      ← Real.sqrt_eq_rpow]
    exact ENNReal.ofReal_le_ofReal hFb
  -- the scalar part: Minkowski
  have hscal : (∑ v, (ENNReal.ofReal (π v))⁻¹ * (∫⁻ t in Set.Icc a b,
        ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g v t).val))) ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal X₂ := by
    have h1 : ∀ v, (ENNReal.ofReal (π v))⁻¹ * (∫⁻ t in Set.Icc a b,
          ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g v t).val))) ^ 2 =
        (∫⁻ t in Set.Icc a b, ENNReal.ofReal (Real.sqrt (π v)⁻¹) *
          ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g v t).val))) ^ 2 := by
      intro v
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_pow,
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (inv_nonneg.2 (hπ v).le),
        ENNReal.ofReal_inv_of_pos (hπ v)]
    rw [Finset.sum_congr rfl fun v _ => h1 v]
    refine (weakResidualCost_minkowski (μ := volume.restrict (Set.Icc a b))
      (fun v t => ENNReal.ofReal (Real.sqrt (π v)⁻¹) *
        ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g v t).val)))).trans ?_
    have h2 : ∀ t, (∑ v, (ENNReal.ofReal (Real.sqrt (π v)⁻¹) *
          ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g v t).val))) ^ 2) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.sqrt (massNormSq (E := h) (K := fun _ => k) ρ π
          (fun v => (g v t).val))) := by
      intro t
      have h3 : ∑ v, (ENNReal.ofReal (Real.sqrt (π v)⁻¹) *
            ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g v t).val))) ^ 2 =
          ENNReal.ofReal (massNormSq (E := h) (K := fun _ => k) ρ π (fun v => (g v t).val)) := by
        unfold massNormSq
        rw [ENNReal.ofReal_sum_of_nonneg fun v _ =>
          mul_nonneg (inv_nonneg.2 (hπ v).le) (factorialNormSq_nonneg _ _)]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
          ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (inv_nonneg.2 (hπ v).le),
          Real.sq_sqrt (factorialNormSq_nonneg _ _),
          ← ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)]
      rw [h3, ENNReal.ofReal_rpow_of_nonneg (hmng t) (by norm_num), ← Real.sqrt_eq_rpow]
    rw [lintegral_congr h2, ← ofReal_integral_eq_lintegral_ofReal
      (CycleComparison.Error.integrable_sqrt_massNormSq (h := h) ρ π hπ (K := fun _ => k) g hgi)
      (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hgb
  calc (∑ v, (ENNReal.ofReal (π v))⁻¹ *
        ((ENNReal.ofReal ν)⁻¹ *
          (∫⁻ t in Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (F v t).val)) +
          (∫⁻ t in Set.Icc a b,
            ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g v t).val))) ^ 2)) ^ (1 / 2 : ℝ)
      = (∑ v, (ENNReal.ofReal (π v))⁻¹ * ((ENNReal.ofReal ν)⁻¹ *
            ∫⁻ t in Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (F v t).val)) +
          ∑ v, (ENNReal.ofReal (π v))⁻¹ * (∫⁻ t in Set.Icc a b,
            ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g v t).val))) ^ 2) ^ (1 / 2 : ℝ) := by
        simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ (∑ v, (ENNReal.ofReal (π v))⁻¹ * ((ENNReal.ofReal ν)⁻¹ *
            ∫⁻ t in Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (F v t).val))) ^ (1 / 2 : ℝ) +
          (∑ v, (ENNReal.ofReal (π v))⁻¹ * (∫⁻ t in Set.Icc a b,
            ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g v t).val))) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
    _ ≤ ENNReal.ofReal X₁ + ENNReal.ofReal X₂ := add_le_add hfluxle hscal
    _ = ENNReal.ofReal (X₁ + X₂) := (ENNReal.ofReal_add hX₁ hX₂).symm

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {c : WeakPassageInstance plan R}

/-- **The forcing cost of a passage from the mass bounds of the forcing.** -/
theorem weakComparisonForcingCost_le_of_mass (r : WeakPassageRun c) (i : ℕ)
    (hκ : 0 < c.D.κ c.M)
    (hπ : ∀ v : CompIn (c.stage i).comps, 0 < weakMass c.D A.Nw A.Jw A.η₀ v.1)
    (F : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (plan.forcingOrder R) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (ScalarH v.1.root))
    {X₁ X₂ : ℝ}
    (hF : FluxMassLe (ι := CompIn (c.stage i).comps) (h := fun v => ScalarH v.1.root)
      (K := fun _ => plan.forcingOrder R) (c.D.κ c.M) (plan.radius R * c.D.eps i)
      (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (Set.Icc (r.tq i) (r.a + A.T₀)) F X₁)
    (hg : ScalarMassLe (ι := CompIn (c.stage i).comps) (h := fun v => ScalarH v.1.root)
      (K := fun _ => plan.forcingOrder R) (plan.radius R * c.D.eps i)
      (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (Set.Icc (r.tq i) (r.a + A.T₀)) g X₂) :
    weakComparisonForcingCost r i F g ≤ ENNReal.ofReal (X₁ + X₂) :=
  mixedCost_le_of_mass (c.D.κ c.M) (plan.radius R * c.D.eps i) hκ
    (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1) hπ (r.tq i)
    (r.a + A.T₀) F g hF hg

end AVRegularity.Providers.WeakGen.Residual
end
end
end
