-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.ProofMeanFluxSplit
public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **The bounds of the terminal residual: the terminal instances and the assembly**

The data and premises of `entry_terminal_residual` from the construction data to the lifted field
are bundled in `TermResCtx` (the premises of `EnergyAtM`, `EntryTerminal/Assembly/Route/Bundled`).
`TermResAux` adds what the bounds use and the statement does not give:
- classical representatives `aZ`, `aY` of the readout `𝖱_T Z` and of the retained solution `Z`
  (they exist by the Sobolev embedding at the order `K̂ - 2`);
- `c_r = 1` (the interior reconstruction is proved at the slow length `√(Bτ'')`, the terminal lift
  has `c_r√(Bτ'')`; the plan `EntryTerminal.Route.plan` chooses `c_r = 1`);
- the quiet margin at `t_p` (the lift of a pulse open at `t_p` must coincide with the
  lift started at `t_p`);
- the reserve premise `k_W.G₀ ≤ k_W.H_prod + 1` that the statement needs, and the two further premises
  (`k_W.G₀ ≤ k_W.H_prod` and the weight floor
  `N_T + D_W + d_W(D_t + 1) ≤ k_W.L_*`), which the terminal successor certificate needs.

The statements, at one context (`…At`) and with the prefix of the statement
(`TermResPrefix`), are instances of the forms of the residual presentation at the terminal menu
`termMenu … t_p c_r`, the masses of the weak stage, the window `[t_p, a + T₀]`:

| Statement | Form | Radius | Price (group of `termBill`) |
|---|---|---|---|
| `TermCovTruncAt` | `CovTruncBound` | `ρ = c_r√(Bh)` | `E^{δp_T}` |
| `TermFrontierAt` | `FrontierBound` | `ρ` | `E^{δ(R_T+1)/2}` |
| `TermFilterAt` | `FilterBound` | `ρ` | `E^{b_T + t_TL_c} + x^{χ_w}(r_w/ρ)^{L_o}` |
| `TermFineTailAt` | `FineTailBound` | `r_* = c_K x` | `x^{χ_w + σ_wL_f}` |
| `TermReconAt` | `ReconBound` | `r_*` | `termBill` without the fine term |

`TermReconAt` takes the three flux bounds as premises: the collection of the coarse flux
`F_mean = covTrunc - filter - frontier` and its lift are inside the reconstruction.

**Assembly** (`termResidualBound_of_parts`): at one context, the five bounds and the word
conversion `ResidualWordsOfMassStatement` give `TermResidualBoundAt`: a reconstruction
`(uK, wK, RK, qK)` of the lifted field, a realization `Ff` of the fine tail, and the residual
clause of `TerminalResidualClauses` (with measurability) for
`Rres = -RK - Ff`, `qres = -qK`, with the constant `3·k₀!·C`.

By `bill_eq_recon_add_fine` the prices above are the groups of `termBill`. For a stage without
edges the fine tail is `0` and the filter and frontier fluxes vanish. For `t_p = a + T₀` the
window is a point and every time integral is `0`. -/

section
/-- **The data and premises of `entry_terminal_residual` at the level `M`**, from the construction
data to the lifted field (the premises of `EnergyAtM`, in the statement's order). -/
structure TermResCtx {X : TermConstruction} (A : TermArgs X) (Kout sXT sZT Kw Lt : ℕ) (nW : ℕ+)
    (hk₀w : A.k₀ ≤ Kw) (cr : ℝ) (kS : InvConsts) (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts)
    (cP CP cHP Cw Ce : ℝ) (cker : ℕ → ℝ) (j₀ M : ℕ) where
  /-- The construction data. -/
  D : OCData
  data : IsTermData X A.Λ M D
  /-- The start of the window of the weak stage. -/
  a : ℝ
  lawW : BirthLaw
  PW : ProvParams
  /-- The weak stage. -/
  Gw : GenStage D ScalarH A.Dt A.bw j₀
  aM : ℝ
  Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ
  weak : IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
    Gw aM
  /-- The quiet anchor. -/
  tp : ℝ
  Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
    (∀ v : CompIn Gw.comps, TorusHk (A.Khat Kout) (ScalarH v.1.root))
  lawT : BirthLaw
  /-- The terminal successor. -/
  Gt' : GenStage D ScalarH A.Dt A.bw j₀
  prep : IsTerminalPrepMap M Kw (A.Khat Kout) cP CP Gw aM tp Pterm
  law : IsTerminalLaw lawW lawT cHP A.η₀ A.nWords
  succ : IsActualSuccessor D (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) Gw Gt'
  seed : TerminalSeedCertificate (A.Pt D Cw cr M) lawT (A.Kw_ D M nW) (A.Kn_ D M cr) A.φ₀ A.hφ₀
    cker (M + A.Jw) (M - 1) M (A.Khat Kout) kS Ce A.τe A.r0 A.Dt A.Ds cr tp (tp + D.termH M)
    (a + A.T₀) (Gt'.retained M 1 A.RT)
  /-- The datum. -/
  f : Vec 2 → ℝ
  θ : ℝ → Vec 2 → ℝ
  U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)
  U : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root)
  /-- The paired solution. -/
  V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root)
  Uw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root)
  Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root)
  Uk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + A.Dt - 1) (ScalarH u.1.root)
  Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + A.Dt - 1) (ScalarH u.1.root)
  paired : IsWeakPaired PW A.φ₀ A.hφ₀ lawW M Kw Lt nW a A.T₀ A.σw A.χw cK CK f Gw aM U₀ U V Uw Vw
    Uk Vk
  readout : IsWeakReadout lawW M A.Jw A.Lw Kw (D.κ M) a A.τ A.T₀ X.s A.Pw cK Cread Cid f θ Gw Ww V
  prepB : IsTerminalPrepBounds lawW M Kw (A.Khat Kout) A.k₀ hk₀w
    (le_trans (by omega : A.k₀ ≤ 2 * A.k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kout _)))
    cr cK CP A.QT f Gw aM tp Pterm V
  Z₀ : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, TorusHk (A.Khat Kout) (ScalarH v.1.root)
  /-- The first coarse family. -/
  Z : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk (A.Khat Kout) (ScalarH v.1.root)
  Zw : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ →
    TorusHk (A.Khat Kout + 1) (ScalarH v.1.root)
  Zk : ∀ v u (_ : (Gt'.retained M 1 A.RT).fam.Γ v u), ℝ →
    TorusHk (A.Khat Kout + A.Dt - 1) (ScalarH u.1.root)
  trace : IsTerminalTrace Gw (Gt'.retained M 1 A.RT) (Pterm fun v => V v aM) Z₀
  sol : (Gt'.retained M 1 A.RT).IsRegSolution (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr)
    A.φ₀ A.hφ₀ (D.termB M) (streamVel (D.Φ (M - 1))) (A.Khat Kout) tp (a + A.T₀) Z₀
    (fun _ _ => 0) (fun _ _ => 0) Z Zw Zk
  /-- The lift coefficients. -/
  CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root)
  PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (A.Khat Kout - 2 * A.pT) (ScalarH v.1.root)
  /-- The classical representative of `P_pZ`. -/
  aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root
  /-- The lifted field. -/
  û : ∀ v : CompIn Gw.comps, ℝ → TorusHk A.k₀ (ScalarH v.1.root)
  ŵ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (A.k₀ + 1) (ScalarH v.1.root)
  lift : IsTerminalLiftedField Gw (Gt'.retained M 1 A.RT) M A.pT (A.Khat Kout) A.NT A.dW sXT sZT
    A.η₀ tp (a + A.T₀) cr Z CcT PZ aRep û
  trunc : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc tp (a + A.T₀))),
    truncateTorusHk (Nat.le_succ A.k₀) (ŵ v t) = û v t

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **What the bounds use beyond the premises**: classical representatives of the
readout and of the retained solution at the order `K̂ - 2`, the slow length factor `c_r = 1`, the
quiet margin and the reserve premise. -/
structure TermResAux
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) where
  /-- A classical representative of the readout `𝖱_T Z`. -/
  aZ : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root
  /-- A classical representative of the retained solution `Z`. -/
  aY : ℝ → Vec 2 → ∀ v : CompIn (c.Gt'.retained M 1 A.RT).comps, ScalarH v.1.root
  repZ : ∀ v : CompIn c.Gw.comps, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    IsClassicalRep (succReadout M (c.D.eps (M - 1)) A.η₀ (A.Khat Kout) (fun v' => c.Z v' t) v)
      (fun x => aZ t x v) (A.Khat Kout - 2)
  repY : ∀ v' : CompIn (c.Gt'.retained M 1 A.RT).comps, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    IsClassicalRep (c.Z v' t) (fun x => aY t x v') (A.Khat Kout - 2)
  one : cr = 1
  quietMargin : Set.Icc (c.tp - ocTauP c.D.α c.D.q c.D.Λ M) (c.tp + ocTauP c.D.α c.D.q c.D.Λ M) ⊆
    ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ M
  reserve : kW.G0 ≤ kW.Hprod + 1
  /-- The strict reserve (the grade-one components of `Gt'` have nonnegative reserve). -/
  reserve1 : kW.G0 ≤ kW.Hprod
  /-- The weight floor of the terminal successor certificate (`liftWt D_t d_W nMax`,
  `nMax ≤ N_T + D_W`). -/
  lstar : A.NT + A.DW + A.dW * (A.Dt + 1) ≤ kW.Lstar
  /-- The birth constant of the terminal law is at most `1`. -/
  cHle : cHP ≤ 1
  /-- The certificate of the terminal successor at the weak constants (by
  `termCertBlock_exists`, at `C_w` above its threshold). -/
  cert : c.Gt'.IsContextCertified kW
  /-- The weight constant is nonnegative (the threshold of the certificate is: `0 ≤ C_{w,0}`). -/
  cwNonneg : 0 ≤ Cw

namespace TermResCtx

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- `‖f‖₂`. -/
def normF : ℝ := Real.sqrt (l2NormSq c.f)

/-- The terminal bill at the context. -/
def bill (cgap Cg : ℝ) : ℝ :=
  termBill c.D M A.NT A.pT A.RT A.AT A.LcT A.LoT A.LfT A.alph cr A.σw A.χw A.η₀ A.tT cgap Cg c.tp
    (c.a + A.T₀)

/-- The price of the response boundary: `E^{δ(R_T+1)/2}`. -/
def frontPrice : ℝ := c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q * ((A.RT : ℝ) + 1) / 2)

/-- The price of the covariance truncation: `E^{δp_T}`. -/
def covPrice : ℝ := c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q * (A.pT : ℝ))

/-- The price of the coarse filter tails: `E^{b_T + t_TL_c} + x^{χ_w}(r_w/ρ)^{L_o}`. -/
def filterPrice : ℝ :=
  c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ - A.η₀ / 4 -
      A.tT * (termExcess A.NT A.pT A.alph : ℝ) + A.tT * (A.LcT : ℝ)) +
    c.D.eps M ^ A.χw * (c.D.termRW A.σw M / c.D.termRho cr M) ^ A.LoT

/-- The price of the fine matrix tail: `x^{χ_w + σ_wL_f}`. -/
def fineBill : ℝ := c.D.eps M ^ (A.χw + A.σw * (A.LfT : ℝ))

/-- The bill of the reconstruction: the cell residual, the lifted coarse flux and the gluing
(`termBill` without the fine matrix tail). -/
def reconBill (cgap Cg : ℝ) : ℝ :=
  c.D.termEpsCell cr M ^ A.NT *
      (1 + Real.sqrt (c.a + A.T₀ - c.tp) / Real.sqrt (c.D.termEllSq M) *
        (c.D.eps M / c.D.termRho cr M) ^ A.AT) +
    (Real.sqrt (c.D.termB M / c.D.termNu M) + c.D.termEpsCell cr M ^ 2 *
      (1 + Real.sqrt (c.a + A.T₀ - c.tp) / Real.sqrt (c.D.termEllSq M) *
        (c.D.eps M / c.D.termRho cr M) ^ A.AT)) *
      (c.frontPrice + c.covPrice + c.filterPrice) +
    Cg * c.D.eps (M - 1) ^ (-Cg) * Real.sqrt (c.D.termEllSq M) *
      Real.sqrt ((1 + (c.a + A.T₀ - c.tp) / ocTau c.D.α c.D.q c.D.Λ M) /
        (cgap * ocTau c.D.α c.D.q c.D.Λ M)) *
      Real.exp (-(cgap * ocTau c.D.α c.D.q c.D.Λ M / Real.sqrt (c.D.termEllSq M) ^ 2))

/-- **The groups of the terminal bill**: `termBill` is the bill of the reconstruction plus the
price of the fine matrix tail. -/
theorem bill_eq_recon_add_fine (cgap Cg : ℝ) :
    c.bill cgap Cg = c.reconBill cgap Cg + c.fineBill := by
  simp only [bill, reconBill, fineBill, frontPrice, covPrice, filterPrice, termBill]
  ring

end TermResCtx

section Statements

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **The covariance truncation bound at a context.** The flux
`(I - P_pQ_p)G - (𝖩_M - BI)∇(𝒞^{p_T}/p_T!)Z` of the terminal menu has a realization of order `k_c`
on `[t_p, a + T₀]` with `B^{-1/2}‖·‖_{L²(I;H_{ρ,k_c;π})} ≤ C E^{δp_T}‖f‖₂`.

`PQ - I` has no degrees `1,…,p_T` and its remaining terms cost `(‖H_M‖/ρ²)^{p_T+1}`, while
`T_cov` costs `(‖H_M‖/ρ²)^{p_T}·‖J_M - BI‖/B`; both are at most `CE^{δp_T}`. -/
def TermCovTruncAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  CovTruncBound (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW kc c.CcT x.aZ (c.Gw.mass c.lawW)
    c.tp (c.a + A.T₀) (c.D.termRho cr M) (C * c.covPrice * c.normF)

/-- **The response boundary bound at a context.** `P_p` of the readout of the omitted flux of the
terminal successor on the omitted rows has a realization of order `k_c` with
`B^{-1/2}‖·‖ ≤ C E^{δ(R_T+1)/2}‖f‖₂`.

`Bd` collects every omitted response of length `R_T + 1`; each has at least `R_T+1` fresh letters,
each of normalized gain at most `CE^{δ/2}`. The cascade analogue before `P_p` is
`successor_frontier_bounds`. -/
def TermFrontierAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  FrontierBound (A.Mt M sXT sZT c.tp cr) (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr)
    A.φ₀ c.Gw c.Gt' (c.Gt'.retained M 1 A.RT) M A.pT 1 A.RT kc (c.D.eps (M - 1)) A.η₀ x.aY
    (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRho cr M) (C * c.frontPrice * c.normF)

/-- **The coarse filter tails bound at a context.** `P_p` of the readout of the root flux defects
`∑ 𝖮(I - S_o)Z + ∑ 𝖥_α(I - S_α)Z` of the terminal successor has a realization of order `k_c` with
`B^{-1/2}‖·‖ ≤ C [E^{b_T + t_TL_c} + x^{χ_w}(r_w/ρ)^{L_o}]‖f‖₂`.

The two terms are the fresh coarse filter tails, with `L_c` moments at `r_new`, and the old
coarse filter tails, with `L_o` moments at `r_w`; each tail uses the original dimensional
coefficient bound of its constituent before summation. -/
def TermFilterAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  FilterBound (A.Mt M sXT sZT c.tp cr) (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
    c.Gw c.Gt' M A.pT kc (c.D.eps (M - 1)) A.η₀ x.aZ (c.Gw.mass c.lawW) c.tp (c.a + A.T₀)
    (c.D.termRho cr M) (C * c.filterPrice * c.normF)

/-- **The fine matrix tail bound at a context.** The flux `∑ 𝖠_{vu,α}D^α(I - S_w)û_u` of the weak
stage on the terminal lifted field has a realization of order `k₀` with
`ν^{-1/2}‖·‖_{L²(I;H_{r_*,k₀;π})} ≤ C x^{χ_w + σ_wL_f}‖f‖₂`.

The whole fine matrix tail of the fine identity is bounded by the kernel bounds with `L_f`
moments, the pair factor, the full ordered lift and the conversion, at the coarse reserve
`k₀ + s_* + L_f + N_T + 2p_T`. -/
def TermFineTailAt (_x : TermResAux c) (C : ℝ) : Prop :=
  FineTailBound c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) A.φ₀ (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT
    A.dW A.k₀ c.CcT c.aRep (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M)
    (C * c.fineBill * c.normF)

/-- **The reconstruction bound at a context.** If the three flux pieces of the mean flux are bounded
with the constant `C_fl` at the order `k_c`, the terminal lifted field has a reconstruction at the
common order `k₀ + ℓ` and the radius `r_* = c_K x` with the bound `C·𝔅_rec·‖f‖₂`, `𝔅_rec` the
terminal bill without the fine matrix tail. The bounds of the terminal residual use `ℓ = 0`. The lift step of the fine tail bound uses
`ℓ = L_f + D_t`: the plain system of the reconstruction with the coupled energy estimate gives the
energy of the lifted field at that order.
Route: `ReconWindowAt.physical_lift` at the actual family of the weak stage, `W = P_pZ`, with the
mean flux as `F_c`. -/
def TermReconAt (x : TermResAux c) (kc ℓ : ℕ) (Cfl C cgap Cg : ℝ) : Prop :=
  TermCovTruncAt c x kc Cfl → TermFrontierAt c x kc Cfl → TermFilterAt c x kc Cfl →
    ReconBound (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW (A.k₀ + ℓ) c.CcT c.aRep
      (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M) (C * c.reconBill cgap Cg * c.normF)

/-- **The bounds of the terminal residual at a context.** A reconstruction `(uK, wK, RK, qK)`
of the terminal lifted field at descending slots `K ≥ k₀`, a realization `Ff` of the fine matrix
tail with a mass bound (square-integrable in time: plain-to-kernel needs it; the fine tail bound
gives it), and
the residual clause of `TerminalResidualClauses` with measurability for
`Rres = -RK - Ff`, `qres = -qK` (truncated to the order `k₀`) with the bill `C·𝔅_T·‖f‖₂`.

The identification of the two systems completes it: the plain system of `uK` with `(RK, qK)` is the kernel system of `û` with
`(RK + Ff, qK)` (the coefficients above the maximal order of an identity vanish; the kernel
defect is `Ff`), and the difference with the paired solution `V` is the error. -/
def TermResidualBoundAt (C cgap Cg : ℝ) : Prop :=
  ∃ (K : CompIn c.Gw.comps → ℕ) (hK : ∀ v, A.k₀ ≤ K v)
    (uK : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (K v) (ScalarH v.1.root))
    (wK : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (K v + 1) (ScalarH v.1.root))
    (RK : ∀ v : CompIn c.Gw.comps, ℝ →
      TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (qK : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (K v) (ScalarH v.1.root))
    (Ff : ∀ v : CompIn c.Gw.comps, ℝ →
      TorusHk A.k₀ (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Xr : ℝ),
    IsStageRecon c.Gw M A.k₀ (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M)
      (menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep) Xr K hK uK wK RK qK ∧
    IsFluxRealization (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) A.k₀
      (Set.Icc c.tp (c.a + A.T₀))
      (fineFluxF c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) A.φ₀ c.Gw
        (menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep)) Ff ∧
    (∃ Yf : ℝ, FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root)
      (K := fun _ => A.k₀) (c.D.κ M) (c.D.termRStar cK M) (c.Gw.mass c.lawW)
      (Set.Icc c.tp (c.a + A.T₀)) Ff Yf) ∧
    ErrorResidualClause c.Gw M A.k₀ (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M)
      (C * c.bill cgap Cg * c.normF) K hK RK qK Ff

/-- **Assembly of the bounds of the terminal residual at a context.** The three flux bounds with a common constant, the
reconstruction and the fine matrix tail with a common constant `C`, and the word conversion give
the bounds of the terminal residual with the constant `3·k₀!·C`. The masses of the weak stage are
positive (`birth_compMass_pos`,
in the OC regime of the data). -/
theorem termResidualBound_of_parts (hW : ResidualWordsOfMassStatement) (x : TermResAux c)
    {kc : ℕ} {Cfl C cgap Cg : ℝ} (hπ : ∀ v, 0 < c.Gw.mass c.lawW v)
    (h2a : TermCovTruncAt c x kc Cfl) (h2b : TermFrontierAt c x kc Cfl)
    (h3 : TermFilterAt c x kc Cfl) (hrec : TermReconAt c x kc 0 Cfl C cgap Cg)
    (hfine : TermFineTailAt c x C) :
    TermResidualBoundAt c (3 * (A.k₀.factorial : ℝ) * C) cgap Cg := by
  obtain ⟨K, hK, uK, wK, RK, qK, hrecon⟩ := hrec h2a h2b h3
  obtain ⟨Ff, hFf, hFm⟩ := hfine
  refine ⟨K, hK, uK, wK, RK, qK, Ff, _, hrecon, hFf, ⟨_, hFm⟩, ?_⟩
  refine (errorResidualClause_of_recon_fine hW c.Gw M A.k₀ (c.Gw.mass c.lawW) hπ c.tp
    (c.a + A.T₀) (c.D.termRStar cK M) _ _ _ K hK uK wK RK qK hrecon Ff hFm).congr ?_
  rw [c.bill_eq_recon_add_fine cgap Cg]
  ring

end Statements

/-! ### The statements with the prefix of the statement -/

/-- **The quantifier prefix of `entry_terminal_residual`** around a predicate on the context, the
auxiliary data, the coarse order `k_c`, the flux constant `C_fl` and the constants `C, c_gap, C_g`.
Order: construction `→ Λ₀ → Λ`, the data `A`, `∃ k_c⁰`, `∀ k_c ≥ k_c⁰`, the lift and order floors,
the plan, the weak constants, the preparation and seed constants, `∀ C_fl`, `∃ C₀, c_gap, C_g` and
the carrier constants, `∀ C ≥ C₀` (the constant is reached from above), the carrier start, the
threshold, the context. The coarse order and the flux constant are internal: the
statement has neither. -/
def TermResPrefix
    (Q : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∃ kc₀ : ℕ, ∀ kc : ℕ, kc₀ ≤ kc →
  ∃ (SX SZ Kfloor : ℕ), ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT → ∀ Kout : ℕ, Kfloor ≤ Kout →
  ∃ Kneed : ℕ,
  ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (_ : A.Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
    Kneed ≤ Kw → A.L0w ≤ Lt → A.LpT ≤ Lt → Lt + 1 ≤ 2 * (nW : ℕ) →
    IsTerminalKernelOrders nW A.LoT A.LfT A.LpT A.Lpr A.Lc A.Lf →
    0 < cr → cr ≤ 1 → cr = 1 → kS.cr = cr → 0 < kS.c₀ →
    Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
  ∀ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
    IsWeakAllocation kW kS Lt →
  ∀ (cP CP cHP Cw Ce : ℝ) (cker : ℕ → ℝ), 0 < cP →
  ∀ Cfl : ℝ, ∃ (C₀ cgap Cg : ℝ), 0 < cgap ∧ ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
  ∀ C : ℝ, C₀ ≤ C → ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHt Υt j₀ →
  ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
  ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c), Q c x kc Cfl C cgap Cg

/-- **The covariance truncation bound at the terminal menu** -/
def TermCovTruncStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => TermCovTruncAt c x kc C

/-- **The response boundary bound at the terminal menu** -/
def TermFrontierStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => TermFrontierAt c x kc C

/-- **The coarse filter tails bound at the terminal menu** -/
def TermFilterStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => TermFilterAt c x kc C

/-- **The fine matrix tail bound at the terminal lifted field** -/
def TermFineTailStatement : Prop :=
  TermResPrefix fun c x _ _ C _ _ => TermFineTailAt c x C

/-- **The reconstruction bound, the reconstruction of the terminal lifted field** (groups 1, 5, 6).
The constant, the gap constant `c_gap` and `C_g` are chosen after the flux constant. The order
offset `ℓ` of the common order `k₀ + ℓ` comes first, so the coarse order and the floors are chosen
after it. -/
def TermReconStatement : Prop :=
  ∀ ℓ : ℕ, TermResPrefix fun c x kc Cfl C cgap Cg => TermReconAt c x kc ℓ Cfl C cgap Cg

/-- **The bounds of the terminal residual**, with the prefix of the statement. -/
def TermResidualBoundStatement : Prop :=
  TermResPrefix fun c _ _ _ C cgap Cg => TermResidualBoundAt c C cgap Cg
end

/-! **E8.I, the identification of the field**. On the window `[t_p, t_f]` the truncation
of the trajectory `uK` of the reconstruction (`IsStageRecon.value`: its value jet is the lifted
field `termLiftedRep`) to the order `k₀` is the lifted field `û` of the context
(`IsTerminalLiftedField`, third clause: the value jet of `û` is `termLiftedRep`), by uniqueness of
weak jets (`TorusHk.ext_value`).

The degenerate cases are included:
- `uK = û` with `K v = k₀`: the truncation is the identity.
- An empty weak family: the statement is about an empty product.
- `K v = k₀ + 1` (the order of `ŵ`): the truncation drops one order. -/

/-- Two torus elements whose value jets agree almost everywhere on the cell have equal values. -/
theorem value_eq_of_jet_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ} (Y : TorusHk K E)
    (Z : TorusHk L E)
    (h : Y.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      Z.toFunction.jet (valueIndex2 L)) : Y.val (valueIndex2 K) = Z.val (valueIndex2 L) :=
  Lp.ext ((periodicJetRepresentative_ae Y.val _).symm.trans
    (h.trans (periodicJetRepresentative_ae Z.val _)))

end AVRegularity.Construction.Residual.Presentation
end
