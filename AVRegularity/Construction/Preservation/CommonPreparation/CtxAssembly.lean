-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.UniformOrderFunctions

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The selected requests of the joint preparation, scalar inputs and original envelopes
under ONE literal uniform prefix. The order functions of the joint preparation precede Ce and
kS; max/min joins of thresholds then produce the envelopes and scalar bounds
for the same context. The frequency floor of the joint preparation is carried as data, so its
continuation is available in the final callback.
The degenerate cases are included: empty, singleton and edgeless families, zero starting
orders, identity geometry and the seed itself keep the same numeric functions;
every actual positive request has the unchanged mass-uniform joint preparation. This
is an unconditional input prefix, not a completed preparation route. -/

/-- Chosen finite reserves, original envelopes and scalar inputs at the
same thresholds; the callback retains both common floors and both radii. -/
def preparationSelectedPrefixData (α s q : ℝ) (ζ : ℝ → ℝ) (Λg : ℕ) (g₀ : ℕ → ℝ)
    (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders) :
    PrepData (Unit × (ℕ × (ℝ × ℝ × ℕ))) :=
  fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres npad σ₀ a σ Hpr sX sZ Ce kS kI CI Cw j₀ x =>
    preparationGateFloorData Λg
      Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres npad σ₀ a σ Hpr sX sZ Ce kS kI CI Cw j₀ x.1 ∧
    preparationJoinedPrefixData α s q ζ (preparationKsFunction α q orders)
      (preparationKanFunction orders) (preparationLanFunction orders)
      (preparationJmFunction α q orders) g₀
      Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres npad σ₀ a σ Hpr sX sZ Ce kS kI CI Cw j₀ x.2

/-- One early selection for the joint preparation and common literal prefix for every actual
context; no order request grows with the seed's producer constants. -/
theorem preparation_uniform_request_prefix (α s : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λg : ℕ, 128 ≤ Λg ∧ ∃ g₀ : ℕ → ℝ, (∀ Λ, 0 < g₀ Λ) ∧
      ∃ orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders,
      (∀ E : PreparationEarlyOrderRequest, Λg ≤ E.Λ → 0 < E.Q →
        PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
          (E.depth α q) E.dimension (E.buffer α q)
          (orders E).Ks (orders E).Ls (orders E).Jm (orders E).qJ (orders E).Jchart) ∧
      PrepPrefix α s q (preparationDepthFunction α q)
        (preparationSelectedPrefixData α s q ζ Λg g₀ orders) := by
  obtain ⟨Λg, hΛg, g₀, hg₀, orders, horders⟩ :=
    preparation_uniform_gate_selection α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λg, hΛg, g₀, hg₀, orders, horders, ?_⟩
  have hjoined := preparation_scalar_and_envelope_prefix hα₀ hα₁ hs₀ hs₁ hq hζ
    (preparationDepthFunction α q) (preparationKsFunction α q orders)
    (preparationKanFunction orders) (preparationLanFunction orders)
    (preparationJmFunction α q orders) g₀ (fun Λ _ => hg₀ Λ)
  have hfloor := preparation_gate_frequency_prefix α s q (preparationDepthFunction α q) Λg
  exact hfloor.and hjoined

/-! One prefix for the early request, original envelopes, scalar inputs and
original-stage native tower. The original operator producer is discharged by the proved
instantiation of the native tower. The exact Kbuf request precedes the seed constants, while the
operator price and level floor are chosen at their allowed late positions.
The degenerate cases are included: empty and singleton families, an interior seed, zero initial
orders, identity geometry and an edgeless stage keep the original incoming G in every field.
No retained successor, stored-order floor or second evolution is substituted. -/

/-- The actual buffer request as one function of the early choices. -/
def preparationBufferFunction (α q : ℝ) : PrepHpr :=
  preparationOrderFunction (fun E => E.buffer α q)

/-- The literal data of the original-stage operator prefix, at the selected
buffer request and with its late uniform price and level floor retained. -/
def preparationOperatorPrefixData (α s q : ℝ) (ζ : ℝ → ℝ) : PrepData (ℝ × ℕ) :=
  fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres npad σ₀ a σ Hpr sX sZ Ce kS kI CI Cw j₀ x =>
    let Kbuf := preparationBufferFunction α q
      Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres npad σ₀ a σ
    0 ≤ x.1 ∧ 2 ≤ x.2 ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad
        sX sZ σ₀ kI CI Cw j₀ Hpr Q T₀ hr), x.2 ≤ c.m →
      Nonempty (PreparationNativeTower c.request Kbuf (fun j => max (kI.cker j) 0)
        (x.1 * (CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe)))

/-- All supplied facts of the actual callback share the same literal choices. -/
def preparationOperatorRequestData (α s q : ℝ) (ζ : ℝ → ℝ) (Λg : ℕ) (g₀ : ℕ → ℝ)
    (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders) :
    PrepData ((Unit × (ℕ × (ℝ × ℝ × ℕ))) × (ℝ × ℕ)) :=
  fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres npad σ₀ a σ Hpr sX sZ Ce kS kI CI Cw j₀ x =>
    preparationSelectedPrefixData α s q ζ Λg g₀ orders
      Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres npad σ₀ a σ Hpr sX sZ Ce kS kI CI Cw j₀ x.1 ∧
    preparationOperatorPrefixData α s q ζ
      Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres npad σ₀ a σ Hpr sX sZ Ce kS kI CI Cw j₀ x.2

/-- One prefix for all actual callback inputs, with the
original-stage operator discharged at the same early buffer order. -/
theorem preparation_uniform_operator_request_prefix (α s : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λg : ℕ, 128 ≤ Λg ∧ ∃ g₀ : ℕ → ℝ, (∀ Λ, 0 < g₀ Λ) ∧
      ∃ orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders,
      (∀ E : PreparationEarlyOrderRequest, Λg ≤ E.Λ → 0 < E.Q →
        PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
          (E.depth α q) E.dimension (E.buffer α q)
          (orders E).Ks (orders E).Ls (orders E).Jm (orders E).qJ (orders E).Jchart) ∧
      PrepPrefix α s q (preparationDepthFunction α q)
        (preparationOperatorRequestData α s q ζ Λg g₀ orders) := by
  obtain ⟨Λg, hΛg, g₀, hg₀, orders, horders, hselected⟩ :=
    preparation_uniform_request_prefix α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λg, hΛg, g₀, hg₀, orders, horders, ?_⟩
  have hop : PrepPrefix α s q (preparationDepthFunction α q)
      (preparationOperatorPrefixData α s q ζ) :=
    nativePreparationOperatorPrefix α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
      (preparationDepthFunction α q) (preparationBufferFunction α q)
  exact hselected.and hop

/-! The final actual same-route callback of the uniform preparation prefix.
All early scalar, envelope and native-operator requests are already produced;
this is the integration of their SAME physical frame, copied
solution, joint-preparation witness and moment/tail prices. Constants and one level floor
precede every root type, stage, window and datum.
The degenerate cases are included: empty and singleton families, identity geometry,
constants and the zero datum, an interior edgeless seed and the smallest scheduled orders retain
the scalar buffer endpoint and the mass-uniform joint-preparation witness. The early depth is
>=1. No new evolution, Cauchy, moment or ledger estimate is an input to this join. -/

/-- Fixed-choice integration of the existing producers into ONE actual
route/model witness, in exactly the callback form of the final prefix assembly. -/
def UniformActualPreparationContextStatement (α s q : ℝ) (ζ : ℝ → ℝ)
    (Λg : ℕ) (g₀ : ℕ → ℝ)
    (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders)
    (_horders : ∀ E : PreparationEarlyOrderRequest, Λg ≤ E.Λ → 0 < E.Q →
      PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
        (E.depth α q) E.dimension (E.buffer α q)
        (orders E).Ks (orders E).Ls (orders E).Jm (orders E).qJ (orders E).Jchart) : Prop :=
  ∀ (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
      (bw Q T₀ : ℝ) (r₀ D₀ : ℕ) (τe lamE σE : ℝ)
      (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ)
      (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ),
      PrepFacts α s q Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
        H J N p nk Lc Lf Lpr Acl Naux Nout Kres σ₀ a σ sX sZ Ce kS kI CI Cw j₀ →
      ∀ x : (Unit × (ℕ × (ℝ × ℝ × ℕ))) × (ℝ × ℕ),
      preparationOperatorRequestData α s q ζ Λg g₀ orders Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE
        H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
        ((preparationDepthFunction α q) Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
          H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ)
        sX sZ Ce kS kI CI Cw j₀ x →
      ∃ y : ℝ × ℝ × ℝ × ℕ,
        PrepWitnessCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
          r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀
          ((preparationDepthFunction α q) Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
            H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ) Q T₀ y

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The fixed-choice callback form of the actual preparation context** (the
actual-context callback `UniformActualPreparationContextStatement`).

`ActualCallback α s q ζ Λg g₀ orders Concl`: at all choices of the prefix with
their facts (`PrepFacts`) and every datum `x` of `preparationOperatorRequestData` at the
selected depth `H_pr = preparationDepthFunction`, constants `y : Y` with `Concl … (x, y)`. The
callback `UniformActualPreparationContextStatement` is this form with `Y = ℝ × ℝ × ℝ × ℕ` and the
route witnesses (`actualContext_of_callback`).

* `ActualCallback.and`: two callbacks give the callback of the conjunction (constants paired).
* `ActualCallback.imp`: a consequence at fixed choices.

For `Y = Unit` and the conclusion `True` the callback is trivial, and `.and` of a callback
with itself is again a callback. -/

/-- The data of the actual callback. -/
abbrev ActualX : Type := (Unit × (ℕ × (ℝ × ℝ × ℕ))) × (ℝ × ℕ)

/-- **The fixed-choice callback form**: constants `y` at every datum of the request data. -/
def ActualCallback (α s q : ℝ) (ζ : ℝ → ℝ) (Λg : ℕ) (g₀ : ℕ → ℝ)
    (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders) {Y : Type}
    (Concl : PrepData (ActualX × Y)) : Prop :=
  ∀ (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
      (bw Q T₀ : ℝ) (r₀ D₀ : ℕ) (τe lamE σE : ℝ)
      (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ)
      (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ),
      PrepFacts α s q Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
        H J N p nk Lc Lf Lpr Acl Naux Nout Kres σ₀ a σ sX sZ Ce kS kI CI Cw j₀ →
      ∀ x : ActualX,
      preparationOperatorRequestData α s q ζ Λg g₀ orders Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE
        H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
        ((preparationDepthFunction α q) Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
          H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ)
        sX sZ Ce kS kI CI Cw j₀ x →
      ∃ y : Y, Concl Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE
        H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
        ((preparationDepthFunction α q) Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
          H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ)
        sX sZ Ce kS kI CI Cw j₀ (x, y)

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λg : ℕ} {g₀ : ℕ → ℝ}
  {orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders} {Y₁ Y₂ : Type}

/-- **Two callbacks give the callback of the conjunction**, with paired constants. -/
theorem ActualCallback.and {C₁ : PrepData (ActualX × Y₁)}
    {C₂ : PrepData (ActualX × Y₂)}
    (h₁ : ActualCallback α s q ζ Λg g₀ orders C₁)
    (h₂ : ActualCallback α s q ζ Λg g₀ orders C₂) :
    ActualCallback α s q ζ Λg g₀ orders (Y := Y₁ × Y₂)
      (fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
        Hpr sX sZ Ce kS kI CI Cw j₀ z =>
        C₁ Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
          Hpr sX sZ Ce kS kI CI Cw j₀ (z.1, z.2.1) ∧
        C₂ Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
          Hpr sX sZ Ce kS kI CI Cw j₀ (z.1, z.2.2)) := by
  intro Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    sX sZ Ce kS kI CI Cw j₀ hf x hx
  obtain ⟨y₁, hy₁⟩ := h₁ Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres npad σ₀ a σ sX sZ Ce kS kI CI Cw j₀ hf x hx
  obtain ⟨y₂, hy₂⟩ := h₂ Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres npad σ₀ a σ sX sZ Ce kS kI CI Cw j₀ hf x hx
  exact ⟨(y₁, y₂), hy₁, hy₂⟩

/-- **A consequence at fixed choices**, with the facts of the prefix and the datum available. -/
theorem ActualCallback.imp {C₁ : PrepData (ActualX × Y₁)}
    {C₂ : PrepData (ActualX × Y₂)}
    (h : ActualCallback α s q ζ Λg g₀ orders C₁)
    (himp : ∀ (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Q T₀ : ℝ) (r₀ D₀ : ℕ)
      (τe lamE σE : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ)
      (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ),
      PrepFacts α s q Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres
        σ₀ a σ sX sZ Ce kS kI CI Cw j₀ →
      ∀ (x : ActualX),
      preparationOperatorRequestData α s q ζ Λg g₀ orders Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE
        H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
        ((preparationDepthFunction α q) Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
          H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ)
        sX sZ Ce kS kI CI Cw j₀ x →
      ∀ y₁ : Y₁, C₁ Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres
        npad σ₀ a σ ((preparationDepthFunction α q) Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
          H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ) sX sZ Ce kS kI CI Cw j₀ (x, y₁) →
      ∃ y₂ : Y₂, C₂ Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres
        npad σ₀ a σ ((preparationDepthFunction α q) Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
          H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ) sX sZ Ce kS kI CI Cw j₀ (x, y₂)) :
    ActualCallback α s q ζ Λg g₀ orders C₂ := by
  intro Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    sX sZ Ce kS kI CI Cw j₀ hf x hx
  obtain ⟨y₁, hy₁⟩ := h Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres npad σ₀ a σ sX sZ Ce kS kI CI Cw j₀ hf x hx
  exact himp Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a
    σ sX sZ Ce kS kI CI Cw j₀ hf x hx y₁ hy₁

/-- **The actual-context callback from its fixed-choice form** with the route witnesses. -/
theorem actualContext_of_callback {horders : ∀ E : PreparationEarlyOrderRequest,
      Λg ≤ E.Λ → 0 < E.Q →
      PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
        (E.depth α q) E.dimension (E.buffer α q)
        (orders E).Ks (orders E).Ls (orders E).Jm (orders E).qJ (orders E).Jchart}
    (h : ActualCallback α s q ζ Λg g₀ orders (Y := ℝ × ℝ × ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe _lamE _σE H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres
          npad σ₀ _a _σ Hpr sX sZ Ce kS kI CI Cw j₀ z =>
        PrepWitnessCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ Hpr Q T₀ z.2)) :
    UniformActualPreparationContextStatement α s q ζ Λg g₀ orders horders := h

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The two named pieces of the actual preparation context** (the actual-context
callback `UniformActualPreparationContextStatement`).

At a request `F` (the request of a context) with the descending slots `K`:

* `CopyFacts F R K B ρ_old C_buf`: of a route `R` and a buffered datum `B` (copy zero of the
  slots): the constant trace of `B`, its buffer bound at the radius `ρ_old` in the two weights, and
  ONE copied solution of the neutral chain of the actual family of `F.G` on `[t_buf, t_f]` with the
  initial datum `B f` in copy zero, whose plain readout is the plain trace of `R` at every time.
* `RoutePkg F K β C_full C_def L ρ_old C_buf`: ONE route with its scalar restart, its realized
  evolution, a weighted seminorm `p` with the four energy rows of the finite expansion (trace for
  every model, kernel source `β`, full `C_full`, plain defect `C_def ε_{m-1}^L`) and the copy facts.
* `ModelAt F R C_joint C_jet`: a model of `R` with the neutral-chain model clauses and the
  endpoint clauses.

The pieces, in the fixed-choice callback form (`ActualCallback`):

* `RoutePieceStatement`: at every context of level `≥ m_*` the route package at the slots
  `preparationNeutralSlots H_pr D (preparationPlainBaseOrder D N_out L_pr)`, the kernel price
  `β = 7|A·(C_I ε_m^θ)|` of the native tower of the datum, `C_full = 2`, a defect constant `C_def`
  (chosen) and `L = q σ_f L_pr`, the old radius `ρ_old = c_old ε_m^{1+γ/2+δ}` of the datum and
  `C_buf = √(bufferEnergyCost K_buf)`.
* `ModelPieceStatement`: above a frequency floor `Λ_m`, given the continuation
  `PreparationGateAfterOrders` of the joint preparation, constants
  `C_joint`, `C_jet ≥ 0` and a level `m_*` with a model of every route with these copy facts.

The selected depth satisfies `H_pr ≥ 1`; an empty component family and the zero datum are
allowed. -/

open CopyJoint

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The copy facts of a route and a buffered datum at the slots `K`. -/
def CopyFacts (F : Request hr D Dm bw j₀) {X : Type} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ)
    (B : (∀ i : CompIn F.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
      (∀ i : CompIn F.G.comps, TorusHk (K (i, 0)) (hr i.1.root))) (ρold Cbuf : ℝ) : Prop :=
  (∀ (cv : ∀ v : CompIn F.G.comps, hr v.1.root) (f : F.Data 0),
    (∀ v, (f v).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun _ => cv v) →
    ∀ i, (truncateTorusHk (Nat.zero_le _) (B f i)).toFunction.jet (valueIndex2 0)
      =ᵐ[volume.restrict unitCube] fun _ => cv i) ∧
  (∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law → ∀ f : F.Data 0,
    Real.sqrt (∑ i : CompIn F.G.comps, (F.G.mass F.law i / w i ^ 2)⁻¹ *
      torusHkNorm ρold (le_refl (K (i, 0))) (B f i) ^ 2) ≤ Cbuf * F.inputNorm w f) ∧
  ∀ f : F.Data 0,
    ∃ (u : ∀ v : CompIn F.G.comps × Fin (F.Hpr + 1), ℝ → TorusHk (K v) (hr v.1.1.root))
      (w : ∀ v : CompIn F.G.comps × Fin (F.Hpr + 1), ℝ → TorusHk (K v + 1) (hr v.1.1.root)),
      IsCoupledWeakSolutionTorus (h := fun v : CompIn F.G.comps × Fin (F.Hpr + 1) =>
          hr v.1.1.root)
        (D.κ F.G.level) F.bufferEnd F.tf (streamVel (D.Φ F.G.level)) Dm K
        (edgeCoefficient (preparationNeutralChain F.G.actualFamily F.Hpr) (D.κ F.G.level)
          (D.eps F.G.level) (D.eps (F.G.level - 1)) (fun _ => ()) K)
        (preparationNeutralInitial F.Hpr K (B f)) (fun _ _ => 0) (fun _ _ => 0) u w ∧
      ∀ t ∈ Set.Icc F.bufferEnd F.tf,
        R.plainTrace t f = plainReadout (h := fun i : CompIn F.G.comps => hr i.1.root) K u t

/-- **The route package of a request.** -/
structure RoutePkg (F : Request hr D Dm bw j₀) (K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ)
    (β Cfull Cdef L ρold Cbuf : ℝ) where
  X : Type
  [group : AddCommGroup X]
  [moduleSpace : Module ℝ X]
  route : F.InsertionRoute X
  p : (CompIn F.G.comps → ℝ) → Seminorm ℝ X
  B : (∀ i : CompIn F.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
    (∀ i : CompIn F.G.comps, TorusHk (K (i, 0)) (hr i.1.root))
  restart : F.ScalarRestartStatement route
  evolution : F.RealizedEvolutionStatement route
  trace : ∀ M : F.Model, F.TraceEnergyStatement route M p
  kernel : F.KernelSourceEnergyStatement route p β
  full : F.BufferedFullEnergyStatement route p Cfull
  defect : F.PlainSourceDefectStatement route p Cdef L
  copies : CopyFacts F route K B ρold Cbuf

attribute [instance] RoutePkg.group RoutePkg.moduleSpace

/-- A model of a route with the neutral-chain model clauses and the endpoint clauses. -/
def ModelAt (F : Request hr D Dm bw j₀) {X : Type} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (Cjoint Cjet : ℝ) : Prop :=
  ∃ M : F.Model, F.NeutralChainModelStatement R M Cjoint Cjet ∧ F.EndpointStatement M

/-- The descending slots of the selected copies. -/
abbrev Slots {ι : Type} (Hpr Dm Nout Lpr : ℕ) : ι × Fin (Hpr + 1) → ℕ :=
  preparationNeutralSlots Hpr Dm (preparationPlainBaseOrder Dm Nout Lpr)

/-- **The route part at fixed choices**: a defect constant `C_def` and a level `m_*` (the
constants `z.2`), with the route package at every context of level `≥ m_*`. -/
def RouteConcl (α s q : ℝ) (ζ : ℝ → ℝ) : PrepData (ActualX × (ℝ × ℕ)) :=
  fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
      Hpr sX sZ Ce kS kI CI Cw j₀ z =>
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
        kI CI Cw j₀ Hpr Q T₀ hr), z.2.2 ≤ c.m →
      Nonempty (RoutePkg c.request (Slots Hpr (succSchedD D₀ N p (H + 1)) Nout Lpr)
        (7 * |z.1.2.1 * (CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe)|) 2 z.2.1
        (q * kI.σf * Lpr) (z.1.1.2.2.1 * ocEpsilon q Λ c.m ^ (1 + ocGamma α q / 2 + ocDelta α q))
        (Real.sqrt (Buffer.bufferEnergyCost (preparationBufferFunction α q Λ φ₀ bw Q T₀ r₀ D₀ τe
          lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ))))

/-- **The model piece at fixed choices**: constants `C_joint`, `C_jet ≥ 0` and a level `m_*`
(the constants `z.2`), with a model of every route at every context of level `≥ m_*` whose copy
facts hold at the old radius and the buffer constant of the route part. -/
def ModelConcl (α s q : ℝ) (ζ : ℝ → ℝ) : PrepData (ActualX × (ℝ × ℝ × ℕ)) :=
  fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
      Hpr sX sZ Ce kS kI CI Cw j₀ z =>
    0 ≤ z.2.2.1 ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
        kI CI Cw j₀ Hpr Q T₀ hr), z.2.2.2 ≤ c.m →
      ∀ (X : Type) [AddCommGroup X] [Module ℝ X] (R : c.request.InsertionRoute X)
        (B : (∀ i : CompIn c.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
          (∀ i : CompIn c.G.comps, TorusHk
            (Slots Hpr (succSchedD D₀ N p (H + 1)) Nout Lpr (i, 0)) (hr i.1.root))),
        CopyFacts c.request R (Slots Hpr (succSchedD D₀ N p (H + 1)) Nout Lpr) B
          (z.1.1.2.2.1 * ocEpsilon q Λ c.m ^ (1 + ocGamma α q / 2 + ocDelta α q))
          (Real.sqrt (Buffer.bufferEnergyCost (preparationBufferFunction α q Λ φ₀ bw Q T₀ r₀ D₀
            τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ))) →
        ModelAt c.request R z.2.1 z.2.2.1

/-- **The route part.** -/
def RoutePieceStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∀ (Λg : ℕ) (g₀ : ℕ → ℝ) (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders),
    ActualCallback α s q ζ Λg g₀ orders (RouteConcl α s q ζ)

/-- **The model piece**, above a frequency floor and given the continuation
`PreparationGateAfterOrders` of the joint preparation. -/
def ModelPieceStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∃ Λm : ℕ, 128 ≤ Λm ∧ ∀ (Λg : ℕ) (g₀ : ℕ → ℝ)
    (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders),
    (∀ E : PreparationEarlyOrderRequest, Λg ≤ E.Λ → 0 < E.Q →
      PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
        (E.depth α q) E.dimension (E.buffer α q)
        (orders E).Ks (orders E).Ls (orders E).Jm (orders E).qJ (orders E).Jchart) →
    Λm ≤ Λg → ActualCallback α s q ζ Λg g₀ orders (ModelConcl α s q ζ)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Closing the uniform preparation prefix from its exact fixed-choice
callback. All early order functions, scalar/envelope inputs and native
operators are discharged by the input-prefix construction, which needs no hypotheses. The
only hypothesis is the fixed-choice callback.
Its own frequency floor is joined by a maximum before all later requests;
the selected order functions and every supplied data witness are retained.
The degenerate cases are included: empty and singleton components, zero datum, identity
geometry, the smallest scheduled orders and an edgeless interior seed preserve the SAME
callback witness. Its uniform level floor precedes every root space and
stage; no existential witness is chosen after the physical datum. -/

/-- The exact actual-context callback closes the already proved uniform
input prefix. -/
theorem preparation_uniform_route_of_actual_context (α s : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hctx : ∃ Λc : ℕ, 128 ≤ Λc ∧
      ∀ (Λg : ℕ) (g₀ : ℕ → ℝ)
        (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders)
        (horders : ∀ E : PreparationEarlyOrderRequest, Λg ≤ E.Λ → 0 < E.Q →
          PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
            (E.depth α q) E.dimension (E.buffer α q)
            (orders E).Ks (orders E).Ls (orders E).Jm (orders E).qJ (orders E).Jchart),
        Λc ≤ Λg →
        UniformActualPreparationContextStatement α s q ζ Λg g₀ orders horders) :
    UniformCommonPreparationRouteStatement α s q ζ := by
  obtain ⟨Λc, _hΛc, hctx⟩ := hctx
  obtain ⟨Λg, _hΛg, g₀, _hg₀, orders, horders, hpre⟩ :=
    preparation_uniform_operator_request_prefix α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let Λg' := max Λg Λc
  have horders' : ∀ E : PreparationEarlyOrderRequest, Λg' ≤ E.Λ → 0 < E.Q →
      PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
        (E.depth α q) E.dimension (E.buffer α q)
        (orders E).Ks (orders E).Ls (orders E).Jm (orders E).qJ (orders E).Jchart :=
    fun E hE hQ => horders E ((le_max_left Λg Λc).trans hE) hQ
  have hpre' : PrepPrefix α s q (preparationDepthFunction α q)
      (preparationOperatorRequestData α s q ζ Λg' g₀ orders) := by
    have hjoined := hpre.and
      (preparation_gate_frequency_prefix α s q (preparationDepthFunction α q) Λc)
    refine hjoined.imp ?_
    intro Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres npad σ₀ a σ sX sZ Ce kS kI CI Cw j₀ _hfacts x hx
    refine ⟨x.1, ?_⟩
    exact ⟨⟨max_le hx.1.1.1 hx.2, hx.1.1.2⟩, hx.1.2⟩
  exact uniformPreparationPrefixAssembly α s q ζ
    (preparationDepthFunction α q) (preparationOperatorRequestData α s q ζ Λg' g₀ orders)
    hpre' (hctx Λg' g₀ orders horders' (le_max_right Λg Λc))

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The route package of a request from its physical parts** (the route part of the actual
preparation context).

Small generic lemmas (the normed instances of the path spaces `H, V` and the group instances of
the route space are implicit arguments, determined by the given maps), at a request `F`:

* `routePkg_mk`: the route package from a route and its facts.
* `route_trace`, `route_kernel`, `route_full`, `route_defectStmt`: the energy
  rows of the route `preparationBufferedInsertionRoute F e hac hcb M E` from the rows of its maps.
* `route_copyFacts`: the copy facts of that route from the constant trace and the buffer bound
  of `B` and ONE copied solution whose readout is the post-buffer plain trace
  (`buffered_insertion_route`).
* `routePkg_all`: the route package from all of these; `routePkg_rows`: the same from the
  named rows (`NativeRow`, `TraceRow`, `KernelRow`, `FullRow`, `DefectRow` with a
  parent scale `ε = ε_{m-1}`, `ConstRow`, `BufRow`, `SolveRow`).
* `PiEquiv` (the data identity into the native path structure), `SeminormOn`, `pathSub`.

The case `H_pr = 0`, an empty component family and the zero datum are allowed. -/

open CopyJoint

local instance routeTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance routeTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance routeTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance
attribute [local instance] preparationNeutralSlotsMonoid preparationNeutralSlotsModule

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- **The route package from a route and its facts.** -/
theorem routePkg_mk (F : Request hr D Dm bw j₀)
    {K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ} {β Cfull Cdef L ρold Cbuf : ℝ}
    {X : Type} {gX : AddCommGroup X} {mX : Module ℝ X} (R : F.InsertionRoute X)
    (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ X)
    (B : (∀ i : CompIn F.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
      (∀ i : CompIn F.G.comps, TorusHk (K (i, 0)) (hr i.1.root)))
    (hrest : F.ScalarRestartStatement R) (hevol : F.RealizedEvolutionStatement R)
    (htr : ∀ M : F.Model, F.TraceEnergyStatement R M p) (hk : F.KernelSourceEnergyStatement R p β)
    (hf : F.BufferedFullEnergyStatement R p Cfull) (hd : F.PlainSourceDefectStatement R p Cdef L)
    (hc : CopyFacts F R K B ρold Cbuf) :
    Nonempty (RoutePkg F K β Cfull Cdef L ρold Cbuf) :=
  ⟨⟨X, R, p, B, hrest, hevol, htr, hk, hf, hd, hc⟩⟩

section Route

variable (F : Request hr D Dm bw j₀) {H V : Type} {iH : NormedAddCommGroup H}
  {sH : NormedSpace ℝ H} {iV : NormedAddCommGroup V} {sV : NormedSpace ℝ V}
  (e : F.Data 0 ≃ₗ[ℝ] H) (hac : F.s ≤ F.bufferEnd) (hcb : F.bufferEnd ≤ F.tf)
  (M : PreparationBufferedMaps H V F.s F.tf F.bufferEnd)
  (E : PreparationPostPlainMaps H V F.Hpr F.bufferEnd F.tf)
  (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ (PreparationEnergyPath H V F.s F.tf F.bufferEnd))

/-- The trace row of the route. -/
theorem route_trace
    (htrace : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∀ (x : PreparationEnergyPath H V F.s F.tf F.bufferEnd) (t : Set.Icc F.s F.tf),
        F.inputNorm w (e.symm (x.1 t)) ≤ p w x) (Mod : F.Model) :
    F.TraceEnergyStatement (preparationBufferedInsertionRoute F e hac hcb M E) Mod p :=
  fun w hw x => htrace w hw x _

/-- The kernel row of the route. -/
theorem route_kernel {β : ℝ}
    (hkernel : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∀ x, p w (preparationBufferedKernelMap hcb M.source x) ≤ β * p w x) :
    F.KernelSourceEnergyStatement (preparationBufferedInsertionRoute F e hac hcb M E) p β :=
  hkernel

/-- The full row of the route. -/
theorem route_full {Cfull : ℝ}
    (hfull : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∀ f, p w (M.full (e f)) ≤ Cfull * F.inputNorm w f) :
    F.BufferedFullEnergyStatement (preparationBufferedInsertionRoute F e hac hcb M E) p Cfull :=
  hfull

/-- The plain-defect row of the route. -/
theorem route_defectStmt {Cdef L : ℝ}
    (hdefect : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∀ f (l : ℕ), l < F.Hpr →
        p w (preparationBufferedPlainLayer hac hcb M E (l + 1) (e f) -
          preparationBufferedKernelMap hcb M.source
            (preparationBufferedPlainLayer hac hcb M E l (e f))) ≤
          Cdef * D.eps (F.G.level - 1) ^ L * F.inputNorm w f) :
    F.PlainSourceDefectStatement (preparationBufferedInsertionRoute F e hac hcb M E) p Cdef L :=
  hdefect

/-- The copy facts of the route. -/
theorem route_copyFacts {K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ} {ρold Cbuf : ℝ}
    (hfix : M.IsFixedPoint hac hcb) (hjoin : BufferedPlainLayerJoinStatement hac hcb M E)
    (B : (∀ i : CompIn F.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
      (∀ i : CompIn F.G.comps, TorusHk (K (i, 0)) (hr i.1.root)))
    (hconst : ∀ (cv : ∀ v : CompIn F.G.comps, hr v.1.root) (f : F.Data 0),
      (∀ v, (f v).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun _ => cv v) →
      ∀ i, (truncateTorusHk (Nat.zero_le _) (B f i)).toFunction.jet (valueIndex2 0)
        =ᵐ[volume.restrict unitCube] fun _ => cv i)
    (hbuf : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∀ f : F.Data 0, Real.sqrt (∑ i : CompIn F.G.comps, (F.G.mass F.law i / w i ^ 2)⁻¹ *
        torusHkNorm ρold (le_refl (K (i, 0))) (B f i) ^ 2) ≤ Cbuf * F.inputNorm w f)
    (hsolve : ∀ f : F.Data 0,
      ∃ (u : ∀ v : CompIn F.G.comps × Fin (F.Hpr + 1), ℝ → TorusHk (K v) (hr v.1.1.root))
        (w : ∀ v : CompIn F.G.comps × Fin (F.Hpr + 1), ℝ → TorusHk (K v + 1) (hr v.1.1.root)),
        IsCoupledWeakSolutionTorus (h := fun v : CompIn F.G.comps × Fin (F.Hpr + 1) =>
            hr v.1.1.root)
          (D.κ F.G.level) F.bufferEnd F.tf (streamVel (D.Φ F.G.level)) Dm K
          (edgeCoefficient (preparationNeutralChain F.G.actualFamily F.Hpr) (D.κ F.G.level)
            (D.eps F.G.level) (D.eps (F.G.level - 1)) (fun _ => ()) K)
          (preparationNeutralInitial F.Hpr K (B f)) (fun _ _ => 0) (fun _ _ => 0) u w ∧
        ∀ (t : ℝ) (ht : t ∈ Set.Icc F.bufferEnd F.tf),
          e.symm (∑ l : Fin (F.Hpr + 1), (E l (e f)).1 ⟨t, ht⟩) =
            plainReadout (h := fun i : CompIn F.G.comps => hr i.1.root) K u t) :
    CopyFacts F (preparationBufferedInsertionRoute F e hac hcb M E) K B ρold Cbuf := by
  have hRS := buffered_insertion_route F e hac hcb M E hfix hjoin
  exact ⟨hconst, hbuf, fun f => (hsolve f).elim fun u hu => hu.elim fun w hw =>
    ⟨u, w, hw.1, fun t ht => (hRS.2.1 f t ht).trans (hw.2 t ht)⟩⟩

end Route

/-- **The route package from its physical parts**, by the small lemmas above. -/
theorem routePkg_all (F : Request hr D Dm bw j₀)
    {K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ} {β Cfull Cdef L ρold Cbuf : ℝ}
    {Kbuf : ℕ} {CK : ℕ → ℝ} {Θ : ℝ} (T : PreparationNativeTower F Kbuf CK Θ)
    {H V : Type} {iH : NormedAddCommGroup H} {sH : NormedSpace ℝ H}
    {iV : NormedAddCommGroup V} {sV : NormedSpace ℝ V}
    (hac : F.s ≤ F.bufferEnd) (hcb : F.bufferEnd ≤ F.tf)
    (M : PreparationBufferedMaps H V F.s F.tf F.bufferEnd)
    (E : PreparationPostPlainMaps H V F.Hpr F.bufferEnd F.tf) (e : F.Data 0 ≃ₗ[ℝ] H)
    (hNative : ∀ f : F.Data 0,
      ∃ (W : ∀ v : CompIn F.G.comps, ℝ → TorusHk 1 (hr v.1.root))
        (Y : ∀ v u (_γ : F.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root)),
        let P := T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩
        IsKernelWeakSolutionTorus (D.κ F.G.level) F.s F.tf (streamVel (D.Φ F.G.level))
          0 Dm P.B P.C P.S f (fun _ _ => 0) (fun _ _ => 0)
          (fun v t => e.symm ((M.full (e f)).1 (Set.projIcc F.s F.tf (hac.trans hcb) t)) v) W Y)
    (hfix : M.IsFixedPoint hac hcb) (hjoin : BufferedPlainLayerJoinStatement hac hcb M E)
    (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ (PreparationEnergyPath H V F.s F.tf F.bufferEnd))
    (htrace : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∀ (x : PreparationEnergyPath H V F.s F.tf F.bufferEnd) (t : Set.Icc F.s F.tf),
        F.inputNorm w (e.symm (x.1 t)) ≤ p w x)
    (hkernel : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∀ x, p w (preparationBufferedKernelMap hcb M.source x) ≤ β * p w x)
    (hfull : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∀ f, p w (M.full (e f)) ≤ Cfull * F.inputNorm w f)
    (hdefect : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∀ f (l : ℕ), l < F.Hpr →
        p w (preparationBufferedPlainLayer hac hcb M E (l + 1) (e f) -
          preparationBufferedKernelMap hcb M.source
            (preparationBufferedPlainLayer hac hcb M E l (e f))) ≤
          Cdef * D.eps (F.G.level - 1) ^ L * F.inputNorm w f)
    (B : (∀ i : CompIn F.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
      (∀ i : CompIn F.G.comps, TorusHk (K (i, 0)) (hr i.1.root)))
    (hconst : ∀ (cv : ∀ v : CompIn F.G.comps, hr v.1.root) (f : F.Data 0),
      (∀ v, (f v).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun _ => cv v) →
      ∀ i, (truncateTorusHk (Nat.zero_le _) (B f i)).toFunction.jet (valueIndex2 0)
        =ᵐ[volume.restrict unitCube] fun _ => cv i)
    (hbuf : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∀ f : F.Data 0, Real.sqrt (∑ i : CompIn F.G.comps, (F.G.mass F.law i / w i ^ 2)⁻¹ *
        torusHkNorm ρold (le_refl (K (i, 0))) (B f i) ^ 2) ≤ Cbuf * F.inputNorm w f)
    (hsolve : ∀ f : F.Data 0,
      ∃ (u : ∀ v : CompIn F.G.comps × Fin (F.Hpr + 1), ℝ → TorusHk (K v) (hr v.1.1.root))
        (w : ∀ v : CompIn F.G.comps × Fin (F.Hpr + 1), ℝ → TorusHk (K v + 1) (hr v.1.1.root)),
        IsCoupledWeakSolutionTorus (h := fun v : CompIn F.G.comps × Fin (F.Hpr + 1) =>
            hr v.1.1.root)
          (D.κ F.G.level) F.bufferEnd F.tf (streamVel (D.Φ F.G.level)) Dm K
          (edgeCoefficient (preparationNeutralChain F.G.actualFamily F.Hpr) (D.κ F.G.level)
            (D.eps F.G.level) (D.eps (F.G.level - 1)) (fun _ => ()) K)
          (preparationNeutralInitial F.Hpr K (B f)) (fun _ _ => 0) (fun _ _ => 0) u w ∧
        ∀ (t : ℝ) (ht : t ∈ Set.Icc F.bufferEnd F.tf),
          e.symm (∑ l : Fin (F.Hpr + 1), (E l (e f)).1 ⟨t, ht⟩) =
            plainReadout (h := fun i : CompIn F.G.comps => hr i.1.root) K u t) :
    Nonempty (RoutePkg F K β Cfull Cdef L ρold Cbuf) :=
  routePkg_mk F (preparationBufferedInsertionRoute F e hac hcb M E) p B
    (preparation_physical_route_realized F T hac hcb e M E hNative hfix hjoin).2
    (preparation_physical_route_realized F T hac hcb e M E hNative hfix hjoin).1
    (route_trace F e hac hcb M E p htrace) (route_kernel F e hac hcb M E p hkernel)
    (route_full F e hac hcb M E p hfull) (route_defectStmt F e hac hcb M E p hdefect)
    (route_copyFacts F e hac hcb M E hfix hjoin B hconst hbuf hsolve)

/-- The identity of the native data space, from its direct structure to the structure of the
native path space (normed group of `preparationNativeFamilyNormed`, normed space of
`preparationWeightedLowSpace`). -/
noncomputable def PiEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {h : ι → Type}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] :
    @LinearEquiv ℝ ℝ _ _ (RingHom.id ℝ) (RingHom.id ℝ) _ _ (∀ i, TorusHk 0 (h i))
      (∀ i, TorusHk 0 (h i)) _
      (@AddCommGroup.toAddCommMonoid _
        (@NormedAddCommGroup.toAddCommGroup _ (preparationNativeFamilyNormed (h := h) 0))) _
      (@NormedSpace.toModule ℝ _ _ _ (preparationWeightedLowSpace (h := h))) :=
  LinearEquiv.refl ℝ _

section Generic

variable {H V : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {a b c : ℝ}

/-- A seminorm on a path space with its own structure, from a function and its seminorm laws. -/
noncomputable def SeminormOn (f : PreparationEnergyPath H V a b c → ℝ)
    (hadd : ∀ x y, f (x + y) ≤ f x + f y) (hsmul : ∀ (r : ℝ) x, f (r • x) = ‖r‖ * f x) :
    Seminorm ℝ (PreparationEnergyPath H V a b c) :=
  Seminorm.of f hadd hsmul

/-- The difference on a path space with its own structure. -/
noncomputable def pathSub (x y : PreparationEnergyPath H V a b c) :
    PreparationEnergyPath H V a b c :=
  x - y

end Generic

section Rows

variable (F : Request hr D Dm bw j₀) {H V : Type} {iH : NormedAddCommGroup H}
  {sH : NormedSpace ℝ H} {iV : NormedAddCommGroup V} {sV : NormedSpace ℝ V}

/-- The native row of buffered maps at a native tower. -/
def NativeRow {Kbuf : ℕ} {CK : ℕ → ℝ} {Θ : ℝ} (T : PreparationNativeTower F Kbuf CK Θ)
    (hac : F.s ≤ F.bufferEnd) (hcb : F.bufferEnd ≤ F.tf)
    (M : PreparationBufferedMaps H V F.s F.tf F.bufferEnd) (e : F.Data 0 ≃ₗ[ℝ] H) : Prop :=
  ∀ f : F.Data 0,
    ∃ (W : ∀ v : CompIn F.G.comps, ℝ → TorusHk 1 (hr v.1.root))
      (Y : ∀ v u (_γ : F.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root)),
      let P := T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩
      IsKernelWeakSolutionTorus (D.κ F.G.level) F.s F.tf (streamVel (D.Φ F.G.level))
        0 Dm P.B P.C P.S f (fun _ _ => 0) (fun _ _ => 0)
        (fun v t => e.symm ((M.full (e f)).1 (Set.projIcc F.s F.tf (hac.trans hcb) t)) v) W Y

/-- The trace row of a seminorm. -/
def TraceRow (e : F.Data 0 ≃ₗ[ℝ] H)
    (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ (PreparationEnergyPath H V F.s F.tf F.bufferEnd)) :
    Prop :=
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    ∀ (x : PreparationEnergyPath H V F.s F.tf F.bufferEnd) (t : Set.Icc F.s F.tf),
      F.inputNorm w (e.symm (x.1 t)) ≤ p w x

/-- The kernel row of a seminorm. -/
def KernelRow (hcb : F.bufferEnd ≤ F.tf)
    (M : PreparationBufferedMaps H V F.s F.tf F.bufferEnd)
    (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ (PreparationEnergyPath H V F.s F.tf F.bufferEnd))
    (β : ℝ) : Prop :=
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    ∀ x, p w (preparationBufferedKernelMap hcb M.source x) ≤ β * p w x

/-- The full row of a seminorm. -/
def FullRow (M : PreparationBufferedMaps H V F.s F.tf F.bufferEnd) (e : F.Data 0 ≃ₗ[ℝ] H)
    (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ (PreparationEnergyPath H V F.s F.tf F.bufferEnd))
    (Cfull : ℝ) : Prop :=
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    ∀ f, p w (M.full (e f)) ≤ Cfull * F.inputNorm w f

/-- The plain-defect row of a seminorm, with the parent scale `ε`. -/
def DefectRow (hac : F.s ≤ F.bufferEnd) (hcb : F.bufferEnd ≤ F.tf)
    (M : PreparationBufferedMaps H V F.s F.tf F.bufferEnd)
    (E : PreparationPostPlainMaps H V F.Hpr F.bufferEnd F.tf) (e : F.Data 0 ≃ₗ[ℝ] H)
    (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ (PreparationEnergyPath H V F.s F.tf F.bufferEnd))
    (Cdef ε L : ℝ) : Prop :=
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    ∀ f (l : ℕ), l < F.Hpr →
      p w (pathSub (preparationBufferedPlainLayer hac hcb M E (l + 1) (e f))
        (preparationBufferedKernelMap hcb M.source
          (preparationBufferedPlainLayer hac hcb M E l (e f)))) ≤
        Cdef * ε ^ L * F.inputNorm w f

/-- The constant-trace row of a buffered datum. -/
def ConstRow {K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ}
    (B : (∀ i : CompIn F.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
      (∀ i : CompIn F.G.comps, TorusHk (K (i, 0)) (hr i.1.root))) : Prop :=
  ∀ (cv : ∀ v : CompIn F.G.comps, hr v.1.root) (f : F.Data 0),
    (∀ v, (f v).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun _ => cv v) →
    ∀ i, (truncateTorusHk (Nat.zero_le _) (B f i)).toFunction.jet (valueIndex2 0)
      =ᵐ[volume.restrict unitCube] fun _ => cv i

/-- The buffer row of a buffered datum at an old radius. -/
def BufRow {K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ}
    (B : (∀ i : CompIn F.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
      (∀ i : CompIn F.G.comps, TorusHk (K (i, 0)) (hr i.1.root))) (ρold Cbuf : ℝ) : Prop :=
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    ∀ f : F.Data 0, Real.sqrt (∑ i : CompIn F.G.comps, (F.G.mass F.law i / w i ^ 2)⁻¹ *
      torusHkNorm ρold (le_refl (K (i, 0))) (B f i) ^ 2) ≤ Cbuf * F.inputNorm w f

/-- The copied-solution row of a buffered datum and post-buffer plain maps. -/
def SolveRow {K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ}
    (E : PreparationPostPlainMaps H V F.Hpr F.bufferEnd F.tf) (e : F.Data 0 ≃ₗ[ℝ] H)
    (B : (∀ i : CompIn F.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
      (∀ i : CompIn F.G.comps, TorusHk (K (i, 0)) (hr i.1.root))) : Prop :=
  ∀ f : F.Data 0,
    ∃ (u : ∀ v : CompIn F.G.comps × Fin (F.Hpr + 1), ℝ → TorusHk (K v) (hr v.1.1.root))
      (w : ∀ v : CompIn F.G.comps × Fin (F.Hpr + 1), ℝ → TorusHk (K v + 1) (hr v.1.1.root)),
      IsCoupledWeakSolutionTorus (h := fun v : CompIn F.G.comps × Fin (F.Hpr + 1) =>
          hr v.1.1.root)
        (D.κ F.G.level) F.bufferEnd F.tf (streamVel (D.Φ F.G.level)) Dm K
        (edgeCoefficient (preparationNeutralChain F.G.actualFamily F.Hpr) (D.κ F.G.level)
          (D.eps F.G.level) (D.eps (F.G.level - 1)) (fun _ => ()) K)
        (preparationNeutralInitial F.Hpr K (B f)) (fun _ _ => 0) (fun _ _ => 0) u w ∧
      ∀ (t : ℝ) (ht : t ∈ Set.Icc F.bufferEnd F.tf),
        e.symm (∑ l : Fin (F.Hpr + 1), (E l (e f)).1 ⟨t, ht⟩) =
          plainReadout (h := fun i : CompIn F.G.comps => hr i.1.root) K u t

end Rows

/-- **The route package from its named rows**, with the parent scale `ε = ε_{m-1}`. -/
theorem routePkg_rows (F : Request hr D Dm bw j₀)
    {K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ} {β Cfull Cdef ε L ρold Cbuf : ℝ}
    {Kbuf : ℕ} {CK : ℕ → ℝ} {Θ : ℝ} (T : PreparationNativeTower F Kbuf CK Θ)
    {H V : Type} {iH : NormedAddCommGroup H} {sH : NormedSpace ℝ H}
    {iV : NormedAddCommGroup V} {sV : NormedSpace ℝ V}
    (hac : F.s ≤ F.bufferEnd) (hcb : F.bufferEnd ≤ F.tf)
    (M : PreparationBufferedMaps H V F.s F.tf F.bufferEnd)
    (E : PreparationPostPlainMaps H V F.Hpr F.bufferEnd F.tf) (e : F.Data 0 ≃ₗ[ℝ] H)
    (hNative : NativeRow F T hac hcb M e)
    (hfix : M.IsFixedPoint hac hcb) (hjoin : BufferedPlainLayerJoinStatement hac hcb M E)
    (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ (PreparationEnergyPath H V F.s F.tf F.bufferEnd))
    (htrace : TraceRow F e p) (hkernel : KernelRow F hcb M p β)
    (hfull : FullRow F M e p Cfull) (hdefect : DefectRow F hac hcb M E e p Cdef ε L)
    (hε : D.eps (F.G.level - 1) = ε)
    (B : (∀ i : CompIn F.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
      (∀ i : CompIn F.G.comps, TorusHk (K (i, 0)) (hr i.1.root)))
    (hconst : ConstRow F B) (hbuf : BufRow F B ρold Cbuf) (hsolve : SolveRow F E e B) :
    Nonempty (RoutePkg F K β Cfull Cdef L ρold Cbuf) := by
  subst hε
  exact routePkg_all F T hac hcb M E e hNative hfix hjoin p htrace hkernel hfull hdefect B
    hconst hbuf hsolve

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Assembly of the model half from a shared certificate of the joint preparation for the
copied family (`CtxModelGate`).
The certificate selects the endpoint and blocks before either mass or
buffer datum. The supplied route's same copied solution is restricted to
that endpoint, then the existing literal copied-witness join is applied. -/

open CopyJoint
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule

section Model
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- One mass-uniform witness of the joint preparation, its actual normalized source budget
and its uniform copied-readout prices. No model or buffer map is selected. -/
structure CtxModelGate (F : Request hr D Dm bw j₀)
    (K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ)
    (ρold Cbuf Cjoint Cjet : ℝ) where
  tp : ℝ
  A : Matrix (CompIn F.G.comps × Fin (F.Hpr + 1))
    (CompIn F.G.comps × Fin (F.Hpr + 1)) ℝ
  Θ : ℝ
  S : ℝ
  C : ℝ
  CP : ℝ
  ρm : ℝ
  Pd : ∀ v : CompIn F.G.comps × Fin (F.Hpr + 1), TorusHk 0 (hr v.1.1.root) →ₗ[ℝ]
    TorusHk (max F.Nout (K v)) (hr v.1.1.root)
  Pg : ℕ → ∀ v u : CompIn F.G.comps × Fin (F.Hpr + 1), TorusHk 0 (hr u.1.1.root) →ₗ[ℝ]
    TorusHk (max F.Nout (K v)) (hr v.1.1.root)
  matrix_nonneg : ∀ v u, 0 ≤ A v u
  budget_nonneg : 0 ≤ S
  model_radius_pos : 0 < ρm
  error_scale_nonneg : 0 ≤ CP * D.eps (F.G.level - 1) ^ F.Q
  enhanced_radius_pos : 0 < rhoEnh D F.cr F.G.level
  delay : F.s ≤ F.bufferEnd ∧ F.bufferEnd ≤ F.s + 2 * ocTauPP D.α D.q D.Λ F.G.level
  window : tp ∈ Set.Icc F.bufferEnd
    (F.bufferEnd + 2 * ocTauPP D.α D.q D.Λ F.G.level)
  end_le : tp ≤ F.tf
  quiet : tp ∈ ocQuietTimes D.α D.q D.Λ D.ζ F.G.level
  quietMargin : Set.Icc (tp - ocTauP D.α D.q D.Λ F.G.level)
    (tp + ocTauP D.α D.q D.Λ F.G.level) ⊆ ocQuietTimes D.α D.q D.Λ D.ζ F.G.level
  weights : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    (∀ v, 0 < F.G.mass F.law v / w v ^ 2) ∧
    IsJointModel (h := fun v : CompIn F.G.comps × Fin (F.Hpr + 1) => hr v.1.1.root)
      (fun v => F.G.mass F.law v.1 / w v.1 ^ 2) K F.Nout F.Hpr
      (preparationNeutralChain F.G.actualFamily F.Hpr) A Θ (D.eps (F.G.level - 1)) F.Q
      ρm C CP Pd Pg ∧
    IsJointError (h := fun v : CompIn F.G.comps × Fin (F.Hpr + 1) => hr v.1.1.root)
      (fun v => F.G.mass F.law v.1 / w v.1 ^ 2) K F.Nout F.Hpr Dm (D.κ F.G.level)
      F.bufferEnd tp (rhoStar D F.c₀ F.G.level) ρold (D.eps (F.G.level - 1)) F.Q CP
      (streamVel (D.Φ F.G.level))
      (edgeCoefficient (preparationNeutralChain F.G.actualFamily F.Hpr) (D.κ F.G.level)
        (D.eps F.G.level) (D.eps (F.G.level - 1)) (fun _ => ()) K) Pd Pg ∧
    (∀ v, ∑ u, Real.sqrt ((F.G.mass F.law u.1 / w u.1 ^ 2) /
      (F.G.mass F.law v.1 / w v.1 ^ 2)) * A v u ≤ S) ∧
    (∀ u, ∑ v, Real.sqrt ((F.G.mass F.law u.1 / w u.1 ^ 2) /
      (F.G.mass F.law v.1 / w v.1 ^ 2)) * A v u ≤ S)
  joint_price : ((F.Hpr : ℝ) + 1) * (CP * Cbuf) ≤ Cjoint
  jet_price : ((F.Hpr : ℝ) + 1) *
    (CycleComparison.Reconstruction.jointModelConst C S F.Hpr F.Nout
      (rhoEnh D F.cr F.G.level / ρm) * Cbuf) ≤ Cjet

/-- The supplied copied solution and buffer give the neutral model of
the same route, using precisely the supplied endpoint and blocks of the joint preparation. -/
theorem model_at_of_gate (F : Request hr D Dm bw j₀)
    (K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ) (ρold Cbuf Cjoint Cjet : ℝ)
    (Z : CtxModelGate F K ρold Cbuf Cjoint Cjet)
    {X : Type} [AddCommGroup X] [Module ℝ X] (R : F.InsertionRoute X)
    (B : (∀ i : CompIn F.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
      (∀ i : CompIn F.G.comps, TorusHk (K (i, 0)) (hr i.1.root)))
    (hcopy : CopyFacts F R K B ρold Cbuf) : ModelAt F R Cjoint Cjet := by
  let I : ReadoutInput F F.Hpr := ⟨K, Z.Pd, Z.Pg, B.toFun⟩
  let P : GateParams F F.Hpr I :=
    { Part := OddSlot, Ctx := fun _ => Unit, Dord := Dm
      Fch := preparationNeutralChain F.G.actualFamily F.Hpr
      A' := Z.A, Θ := Z.Θ, E := D.eps (F.G.level - 1), ρm := Z.ρm, C := Z.C, CP := Z.CP
      ν := D.κ F.G.level, tS := F.bufferEnd, ρs := rhoStar D F.c₀ F.G.level
      ρold := ρold, S := Z.S, Cbuf := Cbuf, b := streamVel (D.Φ F.G.level)
      Ac := edgeCoefficient (preparationNeutralChain F.G.actualFamily F.Hpr) (D.κ F.G.level)
        (D.eps F.G.level) (D.eps (F.G.level - 1)) (fun _ => ()) K
      nonneg := Z.matrix_nonneg, S_nonneg := Z.budget_nonneg
      radius_model_pos := Z.model_radius_pos, error_scale_nonneg := Z.error_scale_nonneg
      scale_eq := rfl }
  have hgate : ∀ w, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      WeightGate F F.Hpr I P w Z.tp := by
    intro w hw
    obtain ⟨hpos, hmodel, herror, hr, hc⟩ := Z.weights w hw
    exact ⟨hpos, hmodel, herror, hr, hc, hcopy.2.1 w hw⟩
  have hconst : JointConstClause (h := fun i : CompIn F.G.comps => hr i.1.root)
      K F.Nout Z.Pd Z.Pg := (Z.weights (fun _ => 1) (Or.inl rfl)).2.1.2.2.2.2.2
  have hsolve : ∀ f : F.Data 0, ∃ u w,
      IsCoupledWeakSolutionTorus (h := fun v : CompIn F.G.comps × Fin (F.Hpr + 1) => hr v.1.1.root)
        P.ν P.tS Z.tp P.b P.Dord I.K P.Ac (preparationNeutralInitial F.Hpr I.K (I.B f))
        (fun _ _ => 0) (fun _ _ => 0) u w ∧
      R.plainTrace Z.tp f = plainReadout (h := fun i : CompIn F.G.comps => hr i.1.root)
        I.K u Z.tp := by
    intro f
    obtain ⟨u, w, hs, hre⟩ := hcopy.2.2 f
    have hsub : Set.Icc F.bufferEnd Z.tp ⊆ Set.Icc F.bufferEnd F.tf :=
      Set.Icc_subset_Icc le_rfl Z.end_le
    have hμ : volume.restrict (Set.Icc F.bufferEnd Z.tp) ≤
        volume.restrict (Set.Icc F.bufferEnd F.tf) := Measure.restrict_mono hsub le_rfl
    exact ⟨u, w, ⟨fun i => (hs.1 i).mono hsub, fun i => (hs.2.1 i).mono_measure hμ,
      fun i => (hs.2.2.1 i).filter_mono (ae_mono hμ), hs.2.2.2.1,
      fun i t ht => hs.2.2.2.2 i t (hsub ht)⟩, hre Z.tp ⟨Z.window.1, Z.end_le⟩⟩
  obtain ⟨M, _, _, hmodel, hend⟩ := copiedPreparationWitnessJoin F F.Hpr I P R Z.tp
    Cjoint Cjet B rfl Z.delay Z.window Z.quiet Z.quietMargin hgate Z.enhanced_radius_pos
    hconst hcopy.1 hsolve Z.joint_price Z.jet_price
  exact ⟨M, hmodel, hend⟩
end Model

/-- Shared joint-preparation data and uniform readout prices at fixed prefix choices.
The blocks precede R and B, as well as the weights and each datum. -/
def ModelGateConcl (α s q : ℝ) (ζ : ℝ → ℝ) : PrepData (ActualX × (ℝ × ℝ × ℕ)) :=
  fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
      Hpr sX sZ Ce kS kI CI Cw j₀ z =>
    0 ≤ z.2.2.1 ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
        kI CI Cw j₀ Hpr Q T₀ hr), z.2.2.2 ≤ c.m →
      Nonempty (CtxModelGate c.request
        (Slots Hpr (succSchedD D₀ N p (H + 1)) Nout Lpr)
        (z.1.1.2.2.1 * ocEpsilon q Λ c.m ^ (1 + ocGamma α q / 2 + ocDelta α q))
        (Real.sqrt (Buffer.bufferEnergyCost (preparationBufferFunction α q Λ φ₀ bw Q T₀ r₀ D₀
          τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ))) z.2.1 z.2.2.1)

/-- The join producing the joint-preparation data, with the literal prefix order. -/
def ModelGatePieceStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∃ Λm : ℕ, 128 ≤ Λm ∧ ∀ (Λg : ℕ) (g₀ : ℕ → ℝ)
    (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders),
    (∀ E : PreparationEarlyOrderRequest, Λg ≤ E.Λ → 0 < E.Q →
      PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
        (E.depth α q) E.dimension (E.buffer α q)
        (orders E).Ks (orders E).Ls (orders E).Jm (orders E).qJ (orders E).Jchart) →
    Λm ≤ Λg → ActualCallback α s q ζ Λg g₀ orders (ModelGateConcl α s q ζ)

/-- Assembly of the exact model piece from shared joint-preparation data. All model
and endpoint clauses are discharged by the existing same-witness join. -/
theorem model_piece_of_gate {α s q : ℝ} {ζ : ℝ → ℝ}
    (h : ModelGatePieceStatement α s q ζ) : ModelPieceStatement α s q ζ := by
  obtain ⟨Λm, hΛm, hgate⟩ := h
  refine ⟨Λm, hΛm, ?_⟩
  intro Λg g₀ orders horders hΛg
  apply (hgate Λg g₀ orders horders hΛg).imp
  intro Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    sX sZ Ce kS kI CI Cw j₀ hf x hx y hy
  refine ⟨y, hy.1, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm X _ _ R B hcopy
  obtain ⟨Z⟩ := hy.2 c hm
  exact model_at_of_gate c.request _ _ _ _ _ Z R B hcopy

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The actual preparation context from its two pieces** (the actual-context callback
`UniformActualPreparationContextStatement`; the form with a frequency floor `Λ_c ≤ Λ_g`).

* `witness_of_pieces`: at a request, the route witness (`PreparationRouteWitness F 1 C_joint
  C_jet`) from a route package, a native tower (the operators), a model of the route, the order
  `N_aux + 2p ≤ N_out`, the covariance smallness at every time and the finite expansion.
* `actualContext_of_pieces`: from the route part and the model piece, a floor `Λ_c` with the
  callback at every `Λ_g ≥ Λ_c`. At the fixed choices: the level is the maximum of the route,
  model and tower floors, the kernel-price floor (`preparation_native_price_threshold`), the
  expansion floor (`expansion_price_threshold`, `C_exp = 1`, kernel decay
  `β ≤ 7 A C_I 2^θ ε_{m-1}^{qθ}`) and the covariance floor (`covariance_small_eventually`).

For `A = 0` there is no kernel price, and an empty component family is allowed. -/

section Request

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- **The route witness of a request from its pieces.** -/
theorem witness_of_pieces (F : Request hr D Dm bw j₀)
    {K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ} {β Cdef L ρold Cbuf Cjoint Cjet : ℝ}
    {Kbuf : ℕ} {CK : ℕ → ℝ} {Θ : ℝ}
    (Pk : RoutePkg F K β 2 Cdef L ρold Cbuf) (T : PreparationNativeTower F Kbuf CK Θ)
    (hM : ModelAt F Pk.route Cjoint Cjet) (hCjet : 0 ≤ Cjet)
    (horder : F.Naux + 2 * F.p ≤ F.Nout)
    (hcov : ∀ t : ℝ, 0 < rhoEnh D F.cr F.G.level ∧
      CycleComparison.Coarse.fbCovConst (rhoEnh D F.cr F.G.level)
        (covPrimitive D F.G.level t) F.Nout ≤ 1)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hprice : (∑ h ∈ Finset.range (F.Hpr + 1), (h : ℝ)) * Cdef * D.eps (F.G.level - 1) ^ L +
      β ^ (F.Hpr + 1) * 2 ≤ 1 * D.eps (F.G.level - 1) ^ F.Q) :
    Nonempty (PreparationRouteWitness F 1 Cjoint Cjet) := by
  obtain ⟨M, hneutral, hend⟩ := hM
  exact ⟨{ X := Pk.X
           route := Pk.route
           model := M
           jet_constant_nonneg := hCjet
           covariance_order := horder
           radius_positive := (hcov M.tp).1
           covariance_small := (hcov M.tp).2
           operators := fun w hw => ⟨T.operators w hw ⟨0, Nat.succ_pos _⟩, T.coefficient w hw _,
             T.inclusion w hw _, T.kernel w hw _, T.mass w hw _⟩
           actual_evolution := Pk.evolution
           expansion := finite_expansion_approximation_of_operator_bounds F Pk.route M Pk.p β 2
             Cdef 1 L hβ hβ1 Pk.restart (Pk.trace M) Pk.kernel Pk.full Pk.defect hprice
           neutral_model := hneutral
           endpoint := hend }⟩

end Request

/-- **The actual preparation context from the route part and the model piece**, above a
frequency floor `Λ_c`. -/
theorem actualContext_of_pieces (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) (hroute : RoutePieceStatement α s q ζ)
    (hmodel : ModelPieceStatement α s q ζ) :
    ∃ Λc : ℕ, 128 ≤ Λc ∧ ∀ (Λg : ℕ) (g₀ : ℕ → ℝ)
      (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders)
      (horders : ∀ E : PreparationEarlyOrderRequest, Λg ≤ E.Λ → 0 < E.Q →
        PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
          (E.depth α q) E.dimension (E.buffer α q)
          (orders E).Ks (orders E).Ls (orders E).Jm (orders E).qJ (orders E).Jchart),
      Λc ≤ Λg → UniformActualPreparationContextStatement α s q ζ Λg g₀ orders horders := by
  obtain ⟨Λm, hΛm, hmodel⟩ := hmodel
  obtain ⟨Λv, hΛv, hcov⟩ := covariance_small_eventually hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λm Λv, hΛm.trans (le_max_left _ _), ?_⟩
  intro Λg g₀ orders horders hΛg
  apply actualContext_of_callback
  refine ((hroute Λg g₀ orders).and
    (hmodel Λg g₀ orders horders ((le_max_left _ _).trans hΛg))).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    sX sZ Ce kS kI CI Cw j₀ hf x hx y hy
  obtain ⟨⟨hfloor, -, -⟩, hA, -, htower⟩ := hx
  obtain ⟨hcI, hcr, hCI, -, -, hQL, horder, hθ, -, hQH⟩ :=
    preparation_context_numeric_orders hα₀ hα₁ hs₀ hs₁ hq hf
  have h128 : 128 ≤ Λ := hf.hΛ
  have hΛvΛ : Λv ≤ Λ := ((le_max_right _ _).trans hΛg).trans hfloor
  obtain ⟨mp, -, hprice⟩ := preparation_native_price_threshold hq.1 hq.2.1 h128 hθ x.2.1 CI hA
    (zero_le_one.trans hCI)
  obtain ⟨me, -, hexp⟩ := expansion_price_threshold
    (preparationDepthFunction α q Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux
      Nout Kres npad σ₀ a σ) hq.1 h128 hQL hQH
    (∑ h ∈ Finset.range (preparationDepthFunction α q Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk
      Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ + 1), (h : ℝ)) y.1.1
    (7 * x.2.1 * CI * (2 : ℝ) ^ min (ocDelta α q / 4) τe) 2
  obtain ⟨mc, -, hcovm⟩ := hcov Λ hΛvΛ kI.cr hcr Nout
  refine ⟨(1, y.2.1, y.2.2.1, max y.1.2 (max y.2.2.2 (max x.2.2 (max mp (max me mc))))), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm
  replace hm : max y.1.2 (max y.2.2.2 (max x.2.2 (max mp (max me mc)))) ≤ c.m := hm
  have h1 : y.1.2 ≤ c.m := by omega
  have h2 : y.2.2.2 ≤ c.m := by omega
  have h3 : x.2.2 ≤ c.m := by omega
  obtain ⟨Pk⟩ := hy.1 c h1
  let := Pk.group
  let := Pk.moduleSpace
  have hM := hy.2.2 c h2 Pk.X Pk.route Pk.B Pk.copies
  obtain ⟨T⟩ := htower c h3
  have heps (i : ℕ) : c.D.eps i = ocEpsilon q Λ i := by
    unfold OCData.eps
    rw [c.hq, c.hΛ]
  obtain ⟨-, hp1, hp2⟩ := hprice c.m (by omega)
  have hβ0 : 0 ≤ 7 * |x.2.1 * (CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe)| := by positivity
  rw [heps] at hβ0
  have hexpm := hexp c.m (by omega) _ hβ0 hp2
  refine witness_of_pieces c.request Pk T hM hy.2.1 horder ?_ ?_ ?_ ?_
  · intro t
    rw [c.request_level]
    exact hcovm c.D c.M c.hα c.hq c.hΛ c.hζ c.hband c.m (by omega) c.m_le_M t
  · rw [heps]
    exact hβ0
  · rw [heps]
    exact hp1
  · rw [c.request_level, heps, heps]
    exact hexpm

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
