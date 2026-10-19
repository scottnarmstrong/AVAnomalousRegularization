-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
public import AVRegularity.Finite.Assembly.TerminalLiftProfileBoundsOfIngredients
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.EntryTerminal.Assembly.Route.EntryTerminalOfWeak
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The covariance image of the first coarse family, anchored at `t_p`**.

The terminal covariance primitive `H_M(t) = ∫_{t_p}^t (J_M - B I)` is symmetric entry by entry, as
the cascade's primitive is (the reference flux is symmetric). A family `Z` of order `K̂` that is
the truncation of a family `Zhi` of order `R ≥ K̂ - 2p + 2p + 2` on the window has, for every
component of the weak stage and every time of the window:
- a covariance image `PZ` of its readout, of order `K̂ - 2p`;
- a classical representative `aRep` at that full order.

This is the cascade's `higher_readout_covariance_input_exists` with the anchor `t_p` in place of
`0`.

Degenerate cases:
- `t = t_p`: `H_M(t_p) = 0`, and the image is the readout itself.
- `p = 0`: no covariance derivatives.
- `Z = 0`: `PZ = 0`, `aRep = 0`.
- `R = K̂ + 2`: the least internal order. -/

open AVRegularity.Construction.Preservation.FullLift

/-- The terminal covariance primitive is symmetric entry by entry. -/
theorem termCovPrimitive_entry_symm (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (M : ℕ) (tp t : ℝ) (i j : Fin 2) :
    termCovPrimitive D M tp t i j = termCovPrimitive D M tp t j i := by
  change (∫ r in tp..t, ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) r i j -
      D.κ (M - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) =
    ∫ r in tp..t, ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) r j i -
      D.κ (M - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) j i
  apply intervalIntegral.integral_congr
  intro r _
  change ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) r i j -
      D.κ (M - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j =
    ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) r j i -
      D.κ (M - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) j i
  rw [refFlux_entry_symm hΛ hζ]
  simp only [Matrix.one_apply, eq_comm]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]

/-- **The anchored covariance input from a higher family.** -/
theorem term_readout_covariance_input_exists {S S' : Finset Comp} (D : OCData) (M p Naux R : ℕ)
    (hNR : Naux ≤ R) (hreserve : Naux - 2 * p + 2 * p + 2 ≤ R) (η tp tf : ℝ) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ)
    (Y : ∀ c : CompIn S', ℝ → TorusHk Naux (hr c.1.root))
    (Yhi : ∀ c : CompIn S', ℝ → TorusHk R (hr c.1.root))
    (heq : ∀ c, ∀ t ∈ Set.Icc tp tf, Y c t = truncateTorusHk hNR (Yhi c t)) :
    ∃ (PZ : ∀ v : CompIn S, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (a : ℝ → Vec 2 → ∀ v : CompIn S, hr v.1.root),
      ∀ v, ∀ t ∈ Set.Icc tp tf,
        IsCovImage (covPolyP (termCovPrimitive D M tp t) p)
          (succReadout M (D.eps (M - 1)) η Naux (fun c => Y c t) v) (PZ v t) ∧
        IsClassicalRep (PZ v t) (fun x => a t x v) (Naux - 2 * p) := by
  classical
  have hex (v : CompIn S) (t : ℝ) :
      ∃ (W : TorusHk (Naux - 2 * p) (hr v.1.root)) (a : Vec 2 → hr v.1.root),
        IsCovImage (covPolyP (termCovPrimitive D M tp t) p)
          (succReadout M (D.eps (M - 1)) η R (fun c => Yhi c t) v) W ∧
        IsClassicalRep W a (Naux - 2 * p) := by
    obtain ⟨u, hu⟩ := hilbert_classicalRep_exists R (Naux - 2 * p + 2 * p) hreserve
      (succReadout M (D.eps (M - 1)) η R (fun c => Yhi c t) v)
    obtain ⟨W, hW, hw⟩ := covPolyP_carrier_exists (termCovPrimitive D M tp t)
      (termCovPrimitive_entry_symm D hΛ hζ M tp t) p (Naux - 2 * p) _ u hu
    exact ⟨W, _, hW, hw⟩
  choose W a ha using hex
  refine ⟨fun v t => W v t, fun t x v => a v t x, fun v t ht => ⟨?_, (ha v t).2⟩⟩
  have hc := covImage_truncate_input hNR _ _ _ (ha v t).1
  rw [truncate_succReadout] at hc
  have he : (fun c => truncateTorusHk hNR (Yhi c t)) = fun c => Y c t := by
    funext c
    exact (heq c t ht).symm
  rw [he] at hc
  exact hc

end AVRegularity.EntryTerminal.Ingredients
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Ingredients

/-! **A representation of the coarse family at one time**. The lift profile needs a
representation `r` of `Z(t)` at the order `L_r + N_T + 2p_T + 4` with `IsRepOf`.

If `Z(t)` is the truncation of a family of order `R ≥ n + 2`, its components have classical
representatives `a_v` of order `n ≤ K`. The representation with base `compField π a` and no
profiles is at order `n`. Its value, rescaled by `√π_v`, is `a_v`, which is the value of the
order-zero truncation of `Z_v(t)` almost everywhere.

Degenerate cases:
- An empty family: the base is the zero field of an empty product.
- `n = 0`: continuity and periodicity only.
- `Z = 0`: `a = 0`, base `0`. -/

section
open AVRegularity.Construction.Preservation.FullLift

/-- The normalized component field of smooth periodic components is smooth and periodic. -/
theorem compField_contDiff_periodic {S : Finset Comp} (π : CompIn S → ℝ) (n : ℕ)
    (a : ∀ v : CompIn S, Vec 2 → ScalarH v.1.root) (ha : ∀ v, ContDiff ℝ n (a v))
    (hp : ∀ v, IsZ2Periodic (a v)) :
    ContDiff ℝ n (compField π (fun x v => a v x)) ∧
      IsZ2Periodic (compField π (fun x v => a v x)) := by
  constructor
  · have hpi : ContDiff ℝ n (fun x => fun v : CompIn S => (Real.sqrt (π v))⁻¹ * a v x) :=
      contDiff_pi.mpr fun v => contDiff_const.mul (ha v)
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : CompIn S => ℝ)).symm.contDiff.comp hpi
  · intro q x
    show toCompSpace π (fun v => a v (x + latticeShift q)) = toCompSpace π (fun v => a v x)
    simp only [hp _ q x]

/-- **The representation of a truncated higher family.** -/
theorem representation_of_higher {S : Finset Comp} (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    {K R : ℕ} (n : ℕ) (hnK : n ≤ K) (hKR : K ≤ R) (hn : n + 2 ≤ R) (e : ℝ) (he0 : 0 < e)
    (he1 : e ≤ 1) (Z : ∀ v : CompIn S, TorusHk K (ScalarH v.1.root))
    (Zhi : ∀ v : CompIn S, TorusHk R (ScalarH v.1.root))
    (hZ : ∀ v, Z v = truncateTorusHk hKR (Zhi v)) :
    ∃ r : Representation (CompSpace S), IsRepresentationAt e n r ∧
      IsRepOf π (fun v => truncateTorusHk (Nat.zero_le K) (Z v)) r.value := by
  choose a ha using fun v => hilbert_classicalRep_exists R n hn (Zhi v)
  have hZa : ∀ v, IsClassicalRep (Z v) (a v) n := fun v => by
    rw [hZ v]
    exact classicalRep_truncate hKR hnK (Zhi v) (a v) (ha v)
  have h0 : ∀ v, IsClassicalRep (truncateTorusHk (Nat.zero_le K) (Z v)) (a v) 0 := fun v =>
    classicalRep_truncate (Nat.zero_le K) le_rfl (Z v) (a v)
      (classicalRep_order_mono (Z v) (a v) (hZa v) (Nat.zero_le n))
  obtain ⟨hcd, hper⟩ := compField_contDiff_periodic π n a (fun v => (ha v).2.1)
    (fun v => (ha v).2.2.1)
  refine ⟨⟨compField π (fun x v => a v x), []⟩, ⟨he0, he1, hcd, hper, by simp⟩, fun v => ?_⟩
  filter_upwards [classicalRep_value_ae _ _ (h0 v)] with x hx
  rw [hx]
  simp only [Representation.value, List.map_nil, List.sum_nil, add_zero]
  change a v x = Real.sqrt (π v) * ((Real.sqrt (π v))⁻¹ * a v x)
  rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hπ v)).ne', one_mul]
end

/-! **Components of normalized fields**. If the difference of two normalized component
fields `compField π f - compField π g` is `C^k` and periodic, and every component of `g` is, then
every component of `f` is (`π > 0`): `f_v = √π_v (compField π f - compField π g)_v + g_v`.

Degenerate cases:
- `f = g`: the difference is `0`.
- An empty family: vacuous.
- `k = 0`: continuity and periodicity. -/

/-- **The components of a field from a normalized difference.** -/
theorem component_of_compField_sub {S : Finset Comp} (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (f g : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) (k : ℕ)
    (hd : ContDiff ℝ k (compField π f - compField π g))
    (hdp : IsZ2Periodic (compField π f - compField π g))
    (hg : ∀ v, ContDiff ℝ k (fun x => g x v)) (hgp : ∀ v, IsZ2Periodic (fun x => g x v))
    (v : CompIn S) :
    ContDiff ℝ k (fun x => f x v) ∧ IsZ2Periodic (fun x => f x v) := by
  have hrep : (fun x => f x v) = fun x =>
      Real.sqrt (π v) * (PiLp.proj (𝕜 := ℝ) 2 (fun _ : CompIn S => ℝ) v
        ((compField π f - compField π g) x)) + g x v := by
    funext x
    change f x v = Real.sqrt (π v) * ((Real.sqrt (π v))⁻¹ * f x v -
      (Real.sqrt (π v))⁻¹ * g x v) + g x v
    rw [mul_sub, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hπ v)).ne',
      one_mul, one_mul, sub_add_cancel]
  rw [hrep]
  refine ⟨(contDiff_const.mul ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : CompIn S => ℝ) v).contDiff.comp hd)).add
    (hg v), fun q x => ?_⟩
  have h2 : g (x + latticeShift q) v = g x v := hgp v q x
  simp only
  rw [hdp q x, h2]

/-! **Realizations of classical fields**. A family of fields that are `C^{k+1}` and
periodic at every time of a window has realizations `û` of order `k` and `ŵ` of order `k+1`.
`ŵ` is the classical Hilbert carrier of order `k+1` and `û` is its truncation. Both have the
fields as classical representatives on the window, and `trunc ŵ = û` at every time.

Degenerate cases:
- A zero field: `û = 0`, `ŵ = 0`.
- Times outside the window: `ŵ = 0` there.
- `k = 0`: order-zero realizations of `C¹` fields. -/

section
open AVRegularity.Construction.Preservation.FullLift

/-- **Realizations on a window.** -/
theorem realization_exists {S : Finset Comp} (k : ℕ) (tp tf : ℝ)
    (F : ∀ v : CompIn S, ℝ → Vec 2 → ScalarH v.1.root)
    (hF : ∀ v, ∀ t ∈ Set.Icc tp tf, ContDiff ℝ (k + 1 : ℕ) (F v t) ∧ IsZ2Periodic (F v t)) :
    ∃ (û : ∀ v : CompIn S, ℝ → TorusHk k (ScalarH v.1.root))
      (ŵ : ∀ v : CompIn S, ℝ → TorusHk (k + 1) (ScalarH v.1.root)),
      (∀ v t, truncateTorusHk (Nat.le_succ k) (ŵ v t) = û v t) ∧
      ∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep (û v t) (F v t) k := by
  have hex (v : CompIn S) (t : ℝ) : ∃ W : TorusHk (k + 1) (ScalarH v.1.root),
      t ∈ Set.Icc tp tf → IsClassicalRep W (F v t) (k + 1) := by
    by_cases ht : t ∈ Set.Icc tp tf
    · have hcd : ContDiff ℝ ((k + 1 : ℕ) : ℕ∞) (F v t) := by exact_mod_cast (hF v t ht).1
      exact ⟨classicalHilbertHk (k + 1) (F v t) hcd (hF v t ht).2,
        fun _ => classicalHilbertHk_rep (k + 1) (F v t) hcd (hF v t ht).2⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose ŵ hŵ using hex
  exact ⟨fun v t => truncateTorusHk (Nat.le_succ k) (ŵ v t), ŵ, fun _ _ => rfl,
    fun v t ht => classicalRep_truncate (Nat.le_succ k) le_rfl (ŵ v t) (F v t)
      (classicalRep_order_mono _ _ (hŵ v t ht) (Nat.le_succ k))⟩
end

end AVRegularity.EntryTerminal.Ingredients
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The lifted field at one level.** The lifted field of the first coarse family from two named
inputs, both in the lifted field's frame:
- `TerminalLiftSeqAtM`: the lift sequences of the weak stage's fibers at the terminal slow length
  (`TerminalLevelLiftStatement` at `G.level = D.term = M`, `ρ = c_r liftLength D M`);
- `TerminalLiftRegAtM`: the regularity `termLiftedRep ∈ C^{k₀+1}` for every lift datum (from
  `TerminalDifferenceBoundsGeneralStatement`, `liftReg_of_diff`).

The rest is proved here:
- the covariance image anchored at `t_p` from the family `Zhi` of order `≥ K̂ + 3`
  (`term_readout_covariance_input_exists`);
- the realizations (`realization_exists`): order `0` for existence, order `k₀` with the gradient
  representative of order `k₀ + 1` for every lifted field.

For `Z = 0` the covariance image and the representative vanish. For an empty weak family every
clause is about an empty product. If `L_w + 3 = k₀`, the classical representative sits at the top
order. -/

/-- The lift sequences of the weak stage's fibers at level `M` and the terminal slow length. -/
def TerminalLiftSeqAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+)
    (kW : InvConsts) (CL Cχ cr : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ D : OCData, IsTermData X A.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw Gw aM →
  ∃ CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root),
    ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
          (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩)))
        sXT sZT (D.slotStart M k / D.cellScaleSq M)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) A.NT A.dW (CcT k)

/-- **The terminal lift sequences** (named input; the instance of
`TerminalLevelLiftStatement` at the terminal level). The reserve premise `G₀ ≤ H_prod + 1` is the
one `LiftFieldStatement` carries: `terminal_level_lift` needs `0 ≤ compReserve ≤ 2` on the root
components. -/
def TerminalLiftSeqStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
  ∀ (nW : ℕ+) (cr : ℝ), 0 < cr → cr ≤ 1 → ∀ (kW : InvConsts) (CL Cχ : ℝ),
    kW.G0 ≤ kW.Hprod + 1 →
  ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → TerminalLiftSeqAtM A sXT sZT nW kW CL Cχ cr j₀ M

/-- The regularity of the lifted representative for every lift datum of a family that is the
truncation of a higher family. -/
def TerminalLiftRegAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT Kout Kw : ℕ) (nW : ℕ+)
    (kW : InvConsts) (CL Cχ cr c C Cw cH : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ D : OCData, IsTermData X A.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw Gw aM →
  ∀ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (A.Khat Kout) (ScalarH v.1.root))),
    IsTerminalPrepMap M Kw (A.Khat Kout) c C Gw aM tp Pterm →
  ∀ (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀),
    IsTerminalLaw lawW lawT cH A.η₀ A.nWords →
    IsActualSuccessor D (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) Gw Gt' →
  ∀ (Z : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk (A.Khat Kout) (ScalarH v.1.root))
    (Khi : ℕ) (hKhi : A.Khat Kout + 3 ≤ Khi)
    (Zhi : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk Khi (ScalarH v.1.root)),
    (∀ v, ∀ t ∈ Set.Icc tp (a + A.T₀),
      Z v t = truncateTorusHk (le_trans (Nat.le_add_right _ 3) hKhi) (Zhi v t)) →
  ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (A.Khat Kout - 2 * A.pT) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root),
    Finite.TerminalLift.IsTerminalLiftData Gw (Gt'.retained M 1 A.RT) M A.pT (A.Khat Kout) A.NT A.dW
      sXT sZT A.η₀ tp (a + A.T₀) cr Z CcT PZ aRep →
  ∀ t ∈ Set.Icc tp (a + A.T₀), ∀ v,
    ContDiff ℝ (A.k₀ + 1 : ℕ) (fun x => termLiftedRep Gw M A.NT A.dW cr CcT aRep t x v) ∧
      IsZ2Periodic (fun x => termLiftedRep Gw M A.NT A.dW cr CcT aRep t x v)

/-- **The lifted field at one level** from the lift sequences and the regularity. -/
theorem liftAtM_of {X : TermConstruction} (A : TermArgs X) (sXT sZT Kout Kw : ℕ) (nW : ℕ+)
    (kW : InvConsts) (CL Cχ cr c C Cw cH : ℝ) (j₀ M : ℕ) (hΛ : 1 ≤ A.Λ)
    (hLk : A.Lw + 3 ≤ A.k₀)
    (hseq : TerminalLiftSeqAtM A sXT sZT nW kW CL Cχ cr j₀ M)
    (hreg : TerminalLiftRegAtM A sXT sZT Kout Kw nW kW CL Cχ cr c C Cw cH j₀ M) :
    LiftAtM A sXT sZT Kout Kw nW kW CL Cχ cr c C Cw cH j₀ M := by
  intro D hD a lawW PW Gw aM hW tp Pterm hmap lawT Gt' hlaw hsucc Z Khi hKhi Zhi hZ
  have hRK : ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (A.Khat Kout - 2 * A.pT) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root),
      Finite.TerminalLift.IsTerminalLiftData Gw (Gt'.retained M 1 A.RT) M A.pT (A.Khat Kout) A.NT
        A.dW sXT sZT A.η₀ tp (a + A.T₀) cr Z CcT PZ aRep →
      ∀ t ∈ Set.Icc tp (a + A.T₀), ∀ v,
        ContDiff ℝ (A.k₀ + 1 : ℕ) (fun x => termLiftedRep Gw M A.NT A.dW cr CcT aRep t x v) ∧
          IsZ2Periodic (fun x => termLiftedRep Gw M A.NT A.dW cr CcT aRep t x v) :=
    hreg D hD a lawW PW Gw aM hW tp Pterm hmap lawT Gt' hlaw hsucc Z Khi hKhi Zhi hZ
  refine ⟨?_, ?_⟩
  · -- existence: lift sequences, the covariance image, an order-zero realization
    obtain ⟨CcT, hCcT⟩ := hseq D hD a lawW PW Gw aM hW
    obtain ⟨hDα, -, hDΛ, hDζ, -, -, -⟩ := hD
    have hΛD : 1 ≤ D.Λ := hDΛ ▸ hΛ
    have hζD : IsFastProfile D.ζ := hDζ ▸ X.hζ
    have hreserve : A.Khat Kout - 2 * A.pT + 2 * A.pT + 2 ≤ Khi := by
      have : 2 * A.pT ≤ A.Khat Kout := by
        dsimp only [TermArgs.Khat]
        omega
      omega
    obtain ⟨PZ, aRep, hcov⟩ := term_readout_covariance_input_exists D M A.pT (A.Khat Kout) Khi
      (le_trans (Nat.le_add_right _ 3) hKhi) hreserve A.η₀ tp (a + A.T₀) hΛD hζD Z Zhi hZ
    have hdata : Finite.TerminalLift.IsTerminalLiftData Gw (Gt'.retained M 1 A.RT) M A.pT
        (A.Khat Kout) A.NT A.dW sXT sZT A.η₀ tp (a + A.T₀) cr Z CcT PZ aRep := ⟨hCcT, hcov⟩
    obtain ⟨û₀, -, -, hrep₀⟩ := realization_exists 0 tp (a + A.T₀)
      (fun v t x => termLiftedRep Gw M A.NT A.dW cr CcT aRep t x v)
      (fun v t ht => ⟨(hRK CcT PZ aRep hdata t ht v).1.of_le (by exact_mod_cast (by omega :
        0 + 1 ≤ A.k₀ + 1)), (hRK CcT PZ aRep hdata t ht v).2⟩)
    exact ⟨CcT, PZ, aRep, û₀, hCcT, hcov, fun v t ht =>
      Construction.Preservation.FullLift.classicalRep_value_ae _ _ (hrep₀ v t ht)⟩
  · -- every lifted field of order zero has a realization of order `k₀`
    intro CcT PZ aRep û₀ hl
    have hdata := Finite.TerminalLift.terminal_lift_data_of_lifted_field hl
    obtain ⟨û, ŵ, htr, hrep⟩ := realization_exists A.k₀ tp (a + A.T₀)
      (fun v t x => termLiftedRep Gw M A.NT A.dW cr CcT aRep t x v)
      (fun v t ht => hRK CcT PZ aRep hdata t ht v)
    refine ⟨û, ŵ, ⟨hl.1, hl.2.1, fun v t ht =>
      Construction.Preservation.FullLift.classicalRep_value_ae _ _ (hrep v t ht)⟩,
      fun v => Filter.Eventually.of_forall fun t => htr v t, fun v t ht =>
      Construction.Preservation.FullLift.classicalRep_order_mono _ _ (hrep v t ht) hLk⟩

/-! **The regularity of the lifted representative from the difference bounds.**

`TerminalDifferenceBoundsGeneralStatement` is taken at `L_r = k₀ - 2`. It gives the oscillatory
difference `compField π (termLiftedRep) - compField π aRep` in `C^{L_r+3} = C^{k₀+1}`, periodic, for every lift
datum and every representation `r` of `Z(t)` at order `L_r + N_T + 2p_T + 4`.
- `r` comes from the higher family (`representation_of_higher`).
- `aRep` is `C^{K̂-2p_T}` by its classical clause.
- The components of `termLiftedRep` follow (`component_of_compField_sub`).

`k₀ ≥ 5` by the schedule (`L_w + 5 ≤ k₀`); the lift uses `L_w + 3 ≤ k₀`.

For an empty retained family, or for `Z = 0`, the representation is the zero field. The least
order the schedule allows is `k₀ = 5`, where `L_r = 3`. -/

/-- The regularity of the lifted representative at every level above a threshold. -/
def TerminalLiftRegStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
  ∀ (Kout Kw : ℕ) (nW : ℕ+) (cr : ℝ), 0 < cr → cr ≤ 1 →
  ∀ (kW : InvConsts) (CL Cχ c C Cw cH : ℝ), 0 < c → 0 < cH → kW.G0 ≤ kW.Hprod + 1 →
  ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    TerminalLiftRegAtM A sXT sZT Kout Kw nW kW CL Cχ cr c C Cw cH j₀ M

/-- **The regularity from the difference bounds.** -/
theorem liftReg_of_diff (hdiff : Finite.TerminalLift.TerminalDifferenceBoundsGeneralStatement) :
    TerminalLiftRegStatement := by
  intro X
  obtain ⟨Λ₀, h128, h1⟩ := hdiff X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ
  refine ⟨Λ₀, h128, fun A hΛ hA => ?_⟩
  obtain ⟨-, ⟨hφs, hφn, hφm, hφsupp⟩, ⟨hbw0, hbw1⟩, ⟨hJw, hτ, hτT, -, hσ, hσ1, hχ, hη, hη1⟩, -,
    hsched, -, -⟩ := hA
  have hLk : A.Lw + 3 ≤ A.k₀ := by
    obtain ⟨h, -⟩ := hsched
    omega
  obtain ⟨SX, SZ, h2⟩ := h1 A.Λ hΛ A.φ₀ A.hφ₀ hφs hφn hφm hφsupp A.bw hbw0 hbw1 A.Jw A.Lw A.dW A.DW
    A.T₀ A.η₀ A.σw A.χw hJw (hτ.trans hτT) hη hη1 hσ hσ1 hχ A.PT A.QT A.NT A.pT A.RT A.AT A.k₀
    A.LcT A.LoT A.LfT A.LpT A.tT hsched (A.k₀ - 2)
  refine ⟨SX, SZ, fun sXT sZT hX hZ Kout Kw nW cr hcr hcr1 kW CL Cχ c C Cw cH hc hcH hkw => ?_⟩
  obtain ⟨Cb, -, h3⟩ := h2 sXT sZT hX hZ cr hcr hcr1 Kw (A.Khat Kout) nW kW CL Cχ c C Cw cH hc hcH
    hkw
  intro j₀
  obtain ⟨M₀, h4⟩ := h3 j₀
  refine ⟨M₀, fun M hM => ?_⟩
  intro D hD a lawW PW Gw aM hW tp Pterm hmap lawT Gt' hlaw hsucc Z Khi hKhi Zhi hZ CcT PZ aRep
    hdata t ht v
  obtain ⟨hDα, hDq, hDΛ, hDζ, hstream, hband, hterm⟩ := hD
  have hΛ128 : 128 ≤ A.Λ := h128.trans hΛ
  have hq1 : 1 < D.q := hDq ▸ X.hq.1
  have hΛD : 128 ≤ D.Λ := hDΛ ▸ hΛ128
  have hπT : ∀ w, 0 < (Gt'.retained M 1 A.RT).mass lawT w := fun w =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD lawT w.1
  have hπW : ∀ w, 0 < Gw.mass lawW w := fun w =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD lawW w.1
  obtain ⟨hε0, hε1, -⟩ := Scales.epsilon_basic (m := M - 1) hq1 hΛD
  have hKR : A.Khat Kout ≤ Khi := le_trans (Nat.le_add_right _ 3) hKhi
  have hnK : A.k₀ - 2 + (A.NT + 2 * A.pT) + 4 ≤ A.Khat Kout := by
    dsimp only [TermArgs.Khat]
    omega
  obtain ⟨r, hr, hrep⟩ := representation_of_higher ((Gt'.retained M 1 A.RT).mass lawT) hπT
    (A.k₀ - 2 + (A.NT + 2 * A.pT) + 4) hnK hKR (by omega) (D.eps (M - 1)) hε0 hε1
    (fun w => Z w t) (fun w => Zhi w t) (fun w => hZ w t ht)
  obtain ⟨-, -, hosc, hoscp, -⟩ := h4 M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hW
    tp Pterm hmap lawT Gt' hlaw hsucc (A.Khat Kout) Z CcT PZ aRep hdata t ht r hr hrep
  have hord : A.k₀ - 2 + 3 ≤ A.Khat Kout - 2 * A.pT := by
    dsimp only [TermArgs.Khat]
    omega
  have hc := component_of_compField_sub (Gw.mass lawW) hπW
    (termLiftedRep Gw M A.NT A.dW cr CcT aRep t) (aRep t) (A.k₀ - 2 + 3) hosc hoscp
    (fun w => (hdata.2 w t ht).2.2.1.of_le (by exact_mod_cast hord))
    (fun w => (hdata.2 w t ht).2.2.2.1) v
  have hk : A.k₀ - 2 + 3 = A.k₀ + 1 := by omega
  rw [hk] at hc
  exact hc

/-! **The lifted field**: `liftField_of : LiftFieldStatement` from two named inputs.
- `TerminalLiftSeqStatement`: the terminal lift sequences, the instance of
  `TerminalLevelLiftStatement`.
- `TerminalDifferenceBoundsGeneralStatement`, whose oscillatory `C^{L_r+3}` clause at
  `L_r = k₀ - 2` is the clause the lifted field uses (`liftReg_of_diff`).

The covariance image anchored at `t_p`, the representation and the realizations are proved here.

For `Z = 0` the lifted field and its realization vanish, and for an empty weak family all products
are empty. At `L_w + 5 = k₀`, the least order the schedule allows, the representative of order
`L_w + 3` lies two orders below the top; `Khi = K̂ + 3` is the least internal order. -/

/-- **The lifted field from the terminal lift sequences and the difference bounds.** -/
theorem liftField_of (hseq : TerminalLiftSeqStatement)
    (hdiff : Finite.TerminalLift.TerminalDifferenceBoundsGeneralStatement) : LiftFieldStatement := by
  intro X
  obtain ⟨ΛS, hΛS, hS⟩ := hseq X
  obtain ⟨ΛR, -, hR⟩ := liftReg_of_diff hdiff X
  refine ⟨max ΛS ΛR, le_trans hΛS (le_max_left _ _), fun A hΛ hA => ?_⟩
  have hLk : A.Lw + 3 ≤ A.k₀ := by
    obtain ⟨h, -⟩ := hA.2.2.2.2.2.1
    omega
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) (le_trans hΛS (m2l hΛ))
  obtain ⟨SX1, SZ1, hS1⟩ := hS A (m2l hΛ) hA
  obtain ⟨SX2, SZ2, hR1⟩ := hR A (m2r hΛ) hA
  refine ⟨max SX1 SX2, max SZ1 SZ2,
    fun sXT sZT hX hZ Kout Kw nW cr hcr hcr1 kW CL Cχ c C Cw cH hc hcH hkw j₀ => ?_⟩
  obtain ⟨M1, hS2⟩ := hS1 sXT sZT (m2l hX) (m2l hZ) nW cr hcr hcr1 kW CL Cχ hkw j₀
  obtain ⟨M2, hR2⟩ := hR1 sXT sZT (m2r hX) (m2r hZ) Kout Kw nW cr hcr hcr1 kW CL Cχ c C Cw cH hc
    hcH hkw j₀
  exact ⟨max M1 M2, fun M hM => liftAtM_of A sXT sZT Kout Kw nW kW CL Cχ cr c C Cw cH j₀ M hΛ1
    hLk (hS2 M (m2l hM)) (hR2 M (m2r hM))⟩

end AVRegularity.EntryTerminal.Ingredients
end
