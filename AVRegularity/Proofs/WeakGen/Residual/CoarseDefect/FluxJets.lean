-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Reduction.QuietTraceHighRestriction
import AVRegularity.Proofs.WeakGen.Reduction.CoeffAllOrder
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
public import AVRegularity.Proofs.WeakGen.Residual.Window.Bill
import Mathlib.CategoryTheory.Countable

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The weighted sum of weak identities** (generic linear algebra on `CoupledWeakIdentity`).

`coupledWeakIdentity_weighted_rows`: if each row `j ∈ S` satisfies the weak identity with its data,
then the data `u₀*, f*, du*, flux*` that agree with the weighted sums (values everywhere in space,
gradients and total flux at almost every time, forcings of the rows a.e. zero) satisfy it with zero
forcing, provided the new right side is integrable at every time. Proved from the congruence and
linear-combination lemmas of `CycleWords`. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The weighted sum of the row identities** with the target data (see the module docstring). -/
theorem coupledWeakIdentity_weighted_rows {J : Type*} (S : Finset J) (lam : J → ℝ)
    (μ : Measure (Vec 2)) (ν a t : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (u f : J → Vec 2 → H) (φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : J → ℝ → Fin 2 → Vec 2 → H)
    (A F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : J → ℝ → Vec 2 → H)
    (h : ∀ j ∈ S, CoupledWeakIdentity μ ν a t v (u j) (f j) φ dφ (du j) (A j) (F j) (g j))
    (u₀ f₀ : Vec 2 → H) (du₀ : ℝ → Fin 2 → Vec 2 → H)
    (flux F₀ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (hu : (∑ j ∈ S, lam j • u j) =ᵐ[μ] u₀) (hf : (∑ j ∈ S, lam j • f j) =ᵐ[μ] f₀)
    (hF : ∀ r, (∑ j ∈ S, lam j • F j) r =ᵐ[μ] 0) (hg : ∀ r, (∑ j ∈ S, lam j • g j) r =ᵐ[μ] 0)
    (hd : ∀ᵐ s ∂volume.restrict (Set.Ioc a t), ∀ k,
      (∑ j ∈ S, lam j • du j) s k =ᵐ[μ] du₀ s k)
    (he : ∀ᵐ s ∂volume.restrict (Set.Ioc a t),
      (fun x => (∑ j ∈ S, lam j • A j) s x) =ᵐ[μ] (fun x => flux s x + F₀ s x))
    (hi : ∀ s ∈ Set.Ioc a t, Integrable (fun x =>
      -(∑ k : Fin 2, v s x k * inner ℝ (du₀ s k x) (φ x)) -
        ν * ∑ k : Fin 2, inner ℝ (du₀ s k x) (dφ k x) -
        ∑ k : Fin 2, inner ℝ (flux s x k + F₀ s x k) (dφ k x) +
        inner ℝ ((0 : ℝ → Vec 2 → H) s x) (φ x)) μ) :
    CoupledWeakIdentity μ ν a t v u₀ f₀ φ dφ du₀ flux F₀ (fun _ _ => 0) := by
  have h1 : CoupledWeakIdentity μ ν a t v (∑ j ∈ S, lam j • u j) (∑ j ∈ S, lam j • f j) φ dφ
      (∑ j ∈ S, lam j • du j) (∑ j ∈ S, lam j • A j) (∑ j ∈ S, lam j • F j)
      (∑ j ∈ S, lam j • g j) :=
    CycleWords.coupledWeakIdentity_finset_sum S μ ν a t v (fun j => lam j • u j)
      (fun j => lam j • f j) φ dφ (fun j => lam j • du j) (fun j => lam j • A j)
      (fun j => lam j • F j) (fun j => lam j • g j) fun j hj =>
      CycleJointProofs.coupledWeakIdentity_smul μ (lam j) ν a t v (u j) (f j) φ dφ (du j) (A j)
        (F j) (g j) (h j hj)
  have h2 := CycleWords.coupledWeakIdentity_zero_forcings μ ν a t v _ _ φ dφ _ _ _ _ h1 hF hg
  have h3 := CycleWords.coupledWeakIdentity_value_congr μ ν a t v _ _ u₀ f₀ φ dφ _ _ _ _ h2 hu hf
  exact CycleWords.coupledWeakIdentity_gradient_flux_ae_time_congr μ ν a t v u₀ f₀ φ dφ _ du₀ _ 0
    flux F₀ 0 h3 hd (by simpa using he) hi

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The data of the coarse defect equation of the readout** (definitions only).

For a passage `M < i ≤ M + J_w` of an instance `c` the readout `g = 𝓡_iŪ` of the coarse family
`Uhi (i-1)` (the coupled solution of `WeakStagePassage`, at the reduction reserves) is a weak
solution of `(∂_t + 𝐛·∇ - κ_M Δ) g = div(F_A g + F_E g + Fc)` on `[t_i, a + T₀]`. The data of the
the `IsCoarseDefect t₀ t₁ B b D H k N AD CE Jm f W Fc` are:

* the index type `CompIn (c.stage i).comps`, the cap `D = Dc` (a parameter, `1 + J_wN_w ≤ Dc`), the grade bound
  `H = J_wR_w`;
* `W` (`cdW`): the weighted sum of the children, truncated to the common order `K' = k + 1 + D`
  (every reduction reserve is at least `K_w + m`; the hypothesis is `K' ≤ K_w + m`);
* `f` (`cdF`): the same readout of the trace of the family of stage `i` at `t_i`, at the order `N`;
* `AD` (`cdAD`): `ε_{i-1}^{η₀}` times the stored coefficients of the letter edges
  `(v₀, []) → (v₀, [n])`, `2 ≤ n ≤ N_w + 1`, at ONE reference component `v₀` (the statement is for
  every `v₀`; that the value does not depend on `v₀` is a lemma of the proof);
* `CE` (`cdCE`): the sum of the stored coefficients of the edges of the incoming family that the
  classification of `IsWeakPassage` makes inherited sources of path length `r` (the grade);
* `Fc`: not constructed here; `CdFcRealizes` says which class it is (minus the `AD`-flux of the
  frontier readout `cdFrontier`, the readout of the words of length exactly `R_w`).

The reserve index: `weakReductionReserve R m v = K_w + m + (J_wR_w - rank v)(J_wN_w - 1) ≥ K_w + m`
on every component, so the order `k + 1 + D` is available on every component exactly when
`k + 1 + D ≤ K_w + m`; the statement takes `m ≤ weakEntryMmax R` and that inequality.

Special cases: `R_w = 0` makes `cdAD = 0` (no letter component) and the frontier the whole
readout; a stage without edges has `cdCE = 0`; `cdF` vanishes with the trace. -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The readout weight `(ε_{i-1}^{η₀})^{|w|}` of a component of the stage `i - 1` (`|w|` its word
at the passage `i`). -/
def cdWeight (c : WeakPassageInstance plan R) (i : ℕ) (v' : Comp) : ℝ :=
  (c.D.eps (i - 1) ^ A.η₀) ^ (compWord i v').length

open scoped Classical in
/-- **The readout at the order `K'`** of a family of the stage `i - 1` at the reduction reserves,
restricted to the components `v'` with `p v'`: `v ↦ ∑_{parent v' = v, p v'} (ε^{η₀})^{|w|} U_{v'}`. -/
def cdReadout (c : WeakPassageInstance plan R) (m K' : ℕ)
    (hK : ∀ w, K' ≤ weakReductionReserve R m w) (i : ℕ) (p : Comp → Prop)
    (U : ∀ v' : CompIn (c.stage (i - 1)).comps,
      TorusHk (weakReductionReserve R m v'.1) (ScalarH v'.1.root))
    (v : CompIn (c.stage i).comps) : TorusHk K' (ScalarH v.1.root) :=
  ∑ v' : CompIn (c.stage (i - 1)).comps,
    if compParent i v'.1 = v.1 ∧ p v'.1 then cdWeight c i v'.1 • truncateTorusHk (hK v'.1) (U v')
    else 0

/-- **`W`**: the readout of the coarse family `Uhi (i-1)` at the order `K' = k + 1 + D`. -/
def cdW (c : WeakPassageInstance plan R) (m K' : ℕ)
    (hK : ∀ w, K' ≤ weakReductionReserve R m w) (i : ℕ)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (v : CompIn (c.stage i).comps) (t : ℝ) : TorusHk K' (ScalarH v.1.root) :=
  cdReadout c m K' hK i (fun _ => True) (fun v' => Uhi (i - 1) v' t) v

/-- **The frontier readout** `H = 𝓡_{i,R_w}Ū`: the words of length exactly `R_w`, at the order
`K'`. -/
def cdFrontier (c : WeakPassageInstance plan R) (m K' : ℕ)
    (hK : ∀ w, K' ≤ weakReductionReserve R m w) (i : ℕ)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (v : CompIn (c.stage i).comps) (t : ℝ) : TorusHk K' (ScalarH v.1.root) :=
  cdReadout c m K' hK i (fun w => (compWord i w).length = A.Rw) (fun v' => Uhi (i - 1) v' t) v

/-- **`f`**: the readout of the trace at `t_i` of the family of stage `i`, at the order `N`. For the
trace `f v = U_v(t_i)` (`weakStageTrace_new`: it vanishes on the new components). -/
def cdF (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (m N : ℕ)
    (hN : ∀ w, N ≤ weakReductionReserve R m w) (i : ℕ)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (v : CompIn (c.stage i).comps) : TorusHk N (ScalarH v.1.root) :=
  cdReadout c m N hN i (fun _ => True)
    (weakStageTrace (weakPassageRawSetting c) m i (Uhi i) (r.tq i)) v

/-- **`AD`**: `ε_{i-1}^{η₀}` times the stored coefficients of the letter edges
`(v₀, []) → (v₀, [𝔇_n])`, `2 ≤ n ≤ N_w + 1`, of the stage `i - 1`, at the reference component `v₀`
(zero if the letter component is absent). The flux of `weakLetterFlux` read as a scalar operator. -/
def cdAD (c : WeakPassageInstance plan R) (Dc i : ℕ) (v₀ : CompIn (c.stage i).comps)
    (d : Finset.Icc 2 Dc) (s : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ) :=
  ∑ n ∈ Finset.Icc 2 (A.Nw + 1),
    if h : v₀.1 ∈ (c.stage (i - 1)).comps ∧
        succComp i v₀.1 [WordLetter.eddy n] ∈ (c.stage (i - 1)).comps then
      ∑ γ : (c.stage (i - 1)).fam.Γ ⟨succComp i v₀.1 [WordLetter.eddy n], h.2⟩ ⟨v₀.1, h.1⟩,
        (c.D.eps (i - 1) ^ A.η₀) •
          (c.stage (i - 1)).physCoeff ⟨succComp i v₀.1 [WordLetter.eddy n], h.2⟩ ⟨v₀.1, h.1⟩ γ
            d.1 s x
    else 0

/-- The classification of the edges of the output stage of the passage `i`: the equivalence of
`IsWeakPassage` between the edges of `c.stage (i - 1)` and the valid sources (a fixed choice). -/
def cdEdgeSource (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (v' u' : CompIn (c.stage (i - 1)).comps) :
    (c.stage (i - 1)).fam.Γ v' u' ≃ {s : WeakSource (c.stage i) //
      s.Valid A.Nw A.Rw (1 + (c.M + A.Jw - i) * A.Nw) ∧ s.srcComp (c.stage i).level = u'.1 ∧ s.tgtComp (c.stage i).level = v'.1} :=
  Classical.choose (c.construction.2.2 i hi hit).1.2.2.2.2.2 v' u'

/-- A source is inherited of path length (grade) `r`. -/
def cdIsGrade {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {G : GenStage D ScalarH Dm b j₀} (r : ℕ) :
    WeakSource G → Prop
  | .inherited _ h _ _ => h = r
  | .eddy .. => False

open scoped Classical in
/-- **`CE r v u d`**: the sum of the stored coefficients of the edges `(u, []) → (v, [])` of the
stage `i - 1` that are inherited sources of path length `r`, at the order `d`. -/
def cdCE (c : WeakPassageInstance plan R) (Dc i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (r : ℕ) (v u : CompIn (c.stage i).comps) (d : Finset.Icc 2 Dc) (s : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root) :=
  if h : v.1 ∈ (c.stage (i - 1)).comps ∧ u.1 ∈ (c.stage (i - 1)).comps then
    ∑ γ : (c.stage (i - 1)).fam.Γ ⟨v.1, h.1⟩ ⟨u.1, h.2⟩,
      if cdIsGrade r (cdEdgeSource c i hi hit ⟨v.1, h.1⟩ ⟨u.1, h.2⟩ γ).1 then
        (c.stage (i - 1)).physCoeff ⟨v.1, h.1⟩ ⟨u.1, h.2⟩ γ d.1 s x
      else 0
  else 0

/-- **The class of `Fc`** (the realization): `Fc v t` is minus the `AD`-flux of the frontier
readout, `-∑_d ∑_α AD_d(e_α) ∂^α H_v`, as an a.e. identity of the value jets on the cell. -/
def CdFcRealizes (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (Dc m k : ℕ)
    (hK : ∀ w, k + 1 + Dc ≤ weakReductionReserve R m w) (i : ℕ)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (AD : ∀ d : Finset.Icc 2 Dc, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) : Prop :=
  ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
    (Fc v t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => -(WithLp.toLp 2 fun j : Fin 2 =>
        ∑ d : Finset.Icc 2 Dc, ∑ α : DerivativeWord2 (d.1 - 1),
          (AD d t x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) j) •
            torusJetOrder (cdFrontier c m (k + 1 + Dc) hK i Uhi v t) (d.1 - 1) α x)

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end

section
section
section
/-! **The readout of the weak window is continuous in time** (the
hypothesis `hWc` of the physical lift).

`cdW_continuousOn`: on the window `[t_i, a + T₀]` of a passage, the readout `W = cdW` of the high
family of the stage `i - 1` is continuous in time, because that family is the value of a coupled
weak solution on the window (`WeakStagePassage`) and the readout is a finite combination of
truncations.

Special cases: a parent without child has the zero readout; the order `K'` does not matter. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- A multiple of a truncation of a time-continuous family is continuous in time (for an abstract
value space, where the instance search is cheap). -/
theorem continuousOn_smul_truncate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ} (hKL : K ≤ L) (w : ℝ)
    (U : ℝ → TorusHk L E) {I : Set ℝ} (hU : ContinuousOn U I) :
    ContinuousOn (fun t => w • truncateTorusHk hKL (U t)) I :=
  ((truncateTorusHk hKL).continuous.comp_continuousOn hU).const_smul w

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The readout `W = cdW` is continuous in time on the window.** -/
theorem cdW_continuousOn (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (m K' : ℕ)
    (hK : ∀ w, K' ≤ weakReductionReserve R m w) (i : ℕ)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j)
    (hpass : WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi i)
    (v : CompIn (c.stage i).comps) :
    ContinuousOn (fun t => cdW c m K' hK i Uhi v t) (Set.Icc (r.tq i) (r.a + A.T₀)) := by
  classical
  unfold cdW cdReadout
  refine continuousOn_finsetSum _ fun v' _ => ?_
  by_cases hc : compParent i v'.1 = v.1 ∧ True
  · simp only [hc, and_self, ↓reduceIte]
    exact continuousOn_smul_truncate (hK v'.1) (cdWeight c i v'.1) (Uhi (i - 1) v') (hpass.1 v')
  · simp only [hc, ↓reduceIte]
    exact continuousOn_const

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The jets of the readout** are the weighted sums of the jets of the children
(`cdReadout_jet_ae`), at every order `m' ≤ K'`. Linearity of `torusJetOrder` a.e. on the cell, and
the jets of a truncation. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

section Linear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem cdJet_add_ae (U V : TorusHk K E) {m : ℕ} (hm : m ≤ K) (w : DerivativeWord2 m) :
    torusJetOrder (U + V) m w =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => torusJetOrder U m w x + torusJetOrder V m w x := by
  filter_upwards [CycleComparison.Coarse.jet_add_ae U V] with x hx
  simp only [torusJetOrder, hm, ↓reduceDIte]
  exact hx _

theorem cdJet_smul_ae (c : ℝ) (U : TorusHk K E) {m : ℕ} (hm : m ≤ K) (w : DerivativeWord2 m) :
    torusJetOrder (c • U) m w =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => c • torusJetOrder U m w x := by
  filter_upwards [CycleComparison.Coarse.jet_smul_ae c U] with x hx
  simp only [torusJetOrder, hm, ↓reduceDIte]
  exact hx _

theorem cdJet_zero_ae {m : ℕ} (hm : m ≤ K) (w : DerivativeWord2 m) :
    torusJetOrder (0 : TorusHk K E) m w =ᵐ[volume.restrict AVenhance.unitCube] fun _ => 0 := by
  filter_upwards [torusHk_zero_jet_ae (E := E) K ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩] with x hx
  simp only [torusJetOrder, hm, ↓reduceDIte]
  exact hx

theorem cdJet_sum_ae {J : Type*} (S : Finset J) (P : J → TorusHk K E) {m : ℕ} (hm : m ≤ K)
    (w : DerivativeWord2 m) :
    torusJetOrder (∑ j ∈ S, P j) m w =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ j ∈ S, torusJetOrder (P j) m w x := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using cdJet_zero_ae (E := E) (K := K) hm w
  | insert j S hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [cdJet_add_ae (P j) (∑ j ∈ S, P j) hm w, ih] with x h1 h2
    rw [h1, h2, Finset.sum_insert hj]

end Linear

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

open scoped Classical in
/-- **The jets of the readout** at every order `m' ≤ K'`: the weighted sum of the jets of the
selected children. -/
theorem cdReadout_jet_ae (c : WeakPassageInstance plan R) (m K' : ℕ)
    (hK : ∀ w, K' ≤ weakReductionReserve R m w) (i : ℕ) (p : Comp → Prop)
    (U : ∀ v' : CompIn (c.stage (i - 1)).comps,
      TorusHk (weakReductionReserve R m v'.1) (ScalarH v'.1.root))
    (v : CompIn (c.stage i).comps) {m' : ℕ} (hm' : m' ≤ K') (w : DerivativeWord2 m') :
    torusJetOrder (cdReadout c m K' hK i p U v) m' w =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ v' : CompIn (c.stage (i - 1)).comps,
        if compParent i v'.1 = v.1 ∧ p v'.1 then cdWeight c i v'.1 • torusJetOrder (U v') m' w x
        else 0 := by
  unfold cdReadout
  refine (cdJet_sum_ae Finset.univ _ hm' w).trans ?_
  have hall : ∀ v' ∈ (Finset.univ : Finset (CompIn (c.stage (i - 1)).comps)),
      torusJetOrder (if compParent i v'.1 = v.1 ∧ p v'.1 then
        cdWeight c i v'.1 • truncateTorusHk (hK v'.1) (U v') else 0) m' w =ᵐ[volume.restrict
        AVenhance.unitCube] fun x => if compParent i v'.1 = v.1 ∧ p v'.1 then
          cdWeight c i v'.1 • torusJetOrder (U v') m' w x else 0 := by
    intro v' _
    by_cases hv : compParent i v'.1 = v.1 ∧ p v'.1
    · simp only [hv, and_self, ↓reduceIte]
      refine (cdJet_smul_ae _ _ hm' w).trans ?_
      filter_upwards [Construction.Preservation.FullLift.torusJetOrder_truncate_ae (hK v'.1) (U v')
        hm' w] with x hx
      rw [hx]
    · simp only [hv, ↓reduceIte]
      exact cdJet_zero_ae hm' w
  have hae := ae_all_iff.2 fun v' : CompIn (c.stage (i - 1)).comps =>
    hall v' (Finset.mem_univ v')
  filter_upwards [hae] with x hx
  exact Finset.sum_congr rfl fun v' _ => hx v'

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The initial datum of the weak window** (the statement, and
the truncation of the readout).

The physical lift of the reconstruction window starts its family at the truncation of a datum
`X₀` whose truncation to the order of the coarse equation is `f₀ = cdF` (the readout of the trace
at `t_i` of the family of stage `i`). The comparison error of the passage starts at `U(t_i)`
(`weakIncomingInit`). Two facts connect them.

* `cdReadout_truncate` (proved): a readout at the order `K'` truncates to the readout at a lower
  order `K`. So `X₀ = cdF` at a high order has `f₀ = cdF` at the order of the coarse equation.
* `WeakCoarseInitialStatement` (statement): at order zero `cdF` is the incoming value,
  `trunc₀ (cdF … v) = trunc₀ (U_i(t_i))_v`. The trace of the family of stage `i` on the stage
  `i - 1` is the family on the old components and zero on the new ones (`weakStageTrace`); the
  only child of `v` among the old components is `v` itself, with the empty word and the weight
  `1` (`compWord_nil_of_old`, `compParent_eq_of_compWord_nil`); and the high family of stage `i`
  truncates to `r.Ur i` at `t_i` (the clauses `hvr` at the root, `hval` at `j = i + 1`
  otherwise, with `t_{i+1} ≤ t_i ≤ a + T₀`).

Special cases: at the root `i = M + J_w` the clause is `hvr`; a stage with one component and
`R_w ≥ 1` has the children `(v, w)`, of which only `(v, [])` is old; `N = 0` is no truncation. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual

/-- Truncation commutes with finite sums (stated for an abstract value space, where the
instance search is cheap). -/
theorem truncateTorusHk_finsetSum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ} (hKL : K ≤ L) {ι : Type*}
    (s : Finset ι) (f : ι → TorusHk L E) :
    truncateTorusHk hKL (∑ j ∈ s, f j) = ∑ j ∈ s, truncateTorusHk hKL (f j) :=
  map_sum (truncateTorusHk hKL) f s

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **A readout truncates to the readout at a lower order.** -/
theorem cdReadout_truncate (c : WeakPassageInstance plan R) (m K K' : ℕ) (hKK : K ≤ K')
    (hK' : ∀ w, K' ≤ weakReductionReserve R m w) (i : ℕ) (p : Comp → Prop)
    (U : ∀ v' : CompIn (c.stage (i - 1)).comps,
      TorusHk (weakReductionReserve R m v'.1) (ScalarH v'.1.root))
    (v : CompIn (c.stage i).comps) :
    truncateTorusHk hKK (cdReadout c m K' hK' i p U v) =
      cdReadout c m K (fun w => hKK.trans (hK' w)) i p U v := by
  classical
  unfold cdReadout
  rw [truncateTorusHk_finsetSum]
  refine Finset.sum_congr rfl fun v' _ => ?_
  split_ifs
  · rw [ContinuousLinearMap.map_smul]
    rfl
  · exact ContinuousLinearMap.map_zero _

/-- **At order zero the initial datum of the window is the incoming value `U(t_i)`.** -/
def WeakCoarseInitialStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (m N : ℕ) (hN : N ≤ R.Kw + m)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j),
    -- the clauses exported by `WeakCoarseHighEnergyAt`: the top family and the truncations
    (∀ v : CompIn (c.stage (c.M + A.Jw)).comps,
      ∀ t ∈ Set.Icc (r.tq (c.M + A.Jw + 1)) (r.a + A.T₀),
      truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (c.M + A.Jw) v t) =
        r.Ur (c.M + A.Jw) v t) →
    (∀ j, c.M < j → j ≤ c.M + A.Jw → ∀ v : CompIn (c.stage (j - 1)).comps,
      ∀ t ∈ Set.Icc (r.tq j) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (j - 1) v t) =
          r.Ur (j - 1) v t) →
    ∀ (i : ℕ) (_hi : c.M < i) (_hit : i ≤ c.M + A.Jw), r.tq i ≤ r.a + A.T₀ →
    ∀ v : CompIn (c.stage i).comps,
      truncateTorusHk (Nat.zero_le N)
          (cdF c r m N (fun w => hN.trans (weakReductionReserve_kw R m w)) i Uhi v) =
        weakIncomingInit r i v

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end

section
section
/-! **The two statements of the coarse defect.**

* `WeakCoarseDefectStatement`: for a passage `M < i ≤ M + J_w`, the coupled family `Uhi`
  solving the passages at the reduction reserves (`WeakStagePassage`, as `weakCoarse_high_energy_at`
  provides it), and any class `Fc` realizing minus the `AD`-flux of the frontier readout
  (`CdFcRealizes`), the readout `W = cdW` satisfies `IsCoarseDefect` on `[t_i, a + T₀]` with
  `B = κ_M`, `b = streamVel (Φ_{i-1})`, `D = Dc` (a parameter with `1 + J_wN_w ≤ Dc`), `H = J_wR_w`, `Jm = κ_M I`, `f = cdF`,
  at every reference component `v₀` of the letters.
* `WeakCoarseMeanStatement`: the literal `hmean` of the free-length
  reconstruction window, with the actual family re-capped at `Dw = 1 + J_w N_w`,
  lift length `ε_{i-1}`, and coefficient cap `N_w + Dw`.

Clock: the hypothesis uses `weakPassageRawClock r`, the one the high-reserve energy statement exports. Orders: with `m` (any; the high-reserve energy statement supplies `Uhi` for `m ≤ weakEntryMmax R`) and `k + 1 + D ≤ K_w + m` (resp. `N ≤ K_w + m`) every
component has the reserve `weakReductionReserve R m v ≥ K_w + m ≥ k + 1 + D`
(`weakReductionReserve_kw`), so `W` lives in `TorusHk (k + 1 + D)` on every component. The
constant orders `k`, `N`, `m` are arguments of the request, not existentials after the plan.

Premises beyond the family: none of smoothness of the readout (the realization `CdFcRealizes` and
the jets are those of the classes). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
open AVRegularity.Construction.Residual.Presentation

/-- **The coarse defect equation of the readout.** -/
def WeakCoarseDefectStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc m k N : ℕ) (_hDc : 1 + A.Jw * A.Nw ≤ Dc) (hk : k + 1 + Dc ≤ R.Kw + m)
    (hN : N ≤ R.Kw + m)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
        (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j),
    (∀ j, c.M < j → j ≤ c.M + A.Jw →
      WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi j) →
    ∀ (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps)
      (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))),
    CdFcRealizes c r Dc m k (fun w => hk.trans (weakReductionReserve_kw R m w)) i Uhi
      (cdAD c Dc i v₀) Fc →
    IsCoarseDefect (r.tq i) (r.a + A.T₀) (c.D.κ c.M) (streamVel (c.D.Φ (i - 1))) Dc
      (A.Jw * A.Rw) k N (cdAD c Dc i v₀) (cdCE c Dc i hi hit)
      (fun _ => (c.D.κ c.M) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (cdF c r m N (fun w => hN.trans (weakReductionReserve_kw R m w)) i Uhi)
      (fun v t => cdW c m (k + 1 + Dc) (fun w => hk.trans (weakReductionReserve_kw R m w))
        i Uhi v t) Fc

/-- **The letters present the window's glued means**, grade by grade.
The positive-response premise is discharged from the comparison menu. The
family, pulse data, fixed observation set, weights and charts are exactly those
of `ReconWindowAt.hmean`; the ambient cap is not a mean summation cap. -/
def WeakCoarseMeanStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (_hRw : 1 ≤ A.Rw)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i) (v₀ : CompIn (c.stage i).comps)
    (ρ : ℕ), ρ ≤ A.Jw * A.Rw →
    let Dw := 1 + A.Jw * A.Nw
    let F := Window.weakWindowFamily c i hi hit
    IsMeanPresentation (Set.Icc (r.tq i) (r.a + A.T₀)) (A.Nw + Dw) ρ
      (cdAD c (A.Nw + Dw) i v₀) (cdCE c (A.Nw + Dw) i hi hit)
      (fun _ => (c.D.κ c.M) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (gluedMean (ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.a + A.T₀))
        (fun k => F.weight (oddSlotOf k)) (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2)
        (c.D.eps (i - 1))
        (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / c.D.eps (i - 1)) A.Nw ρ
        (fun k => pulseLiftData c.D.α c.D.q c.D.Λ i c.D.ζ (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
          (c.D.κ c.M) (c.D.κ c.M) (c.D.eps (i - 1))
          (c.D.eps (i - 1) / c.D.eps (i - 1)) k (F.fiber (oddSlotOf k) ()))
        (h.CcR i)
        (fun k => ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
        (fun k => ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k)))

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The assembly** of the coarse defect equation of the readout.

For a parent `v` of the stage `i` the weighted sum (weights `λ_{v'} = (ε^{η₀})^{|w|}` for the
children `v'` of `v`, zero otherwise) of the row identities of the passage `i` is the identity of
`IsCoarseDefect` at `v` (`coupledWeakIdentity_weighted_rows`). The parts that are not linear algebra
are the named propositions of this file:

* `CdFluxIdentity`: the weighted sum of the row fluxes equals the target flux plus the jet
  of `Fc`, a.e. in time and space. Split in the lemmas for the jets of the lifts `Whi`, the
  classification of the edges and the reindexing of children by words;
* `CdIntegrable`: the right side of the target identity is integrable at every time.

The jets (`hu`, `hf`, `hd`, `hF`, `hg`) are proved from `cdReadout_jet_ae`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The flux of the row `v'`** of the passage `i` (stage `i - 1`), read from the jets of the
lifts `Whi`: the flux term of `IsCoupledWeakSolutionTorus`. -/
def cdRowFlux (c : WeakPassageInstance plan R) (m : ℕ)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j) (i : ℕ)
    (v' : CompIn (c.stage (i - 1)).comps) (s : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => ℝ) :=
  ∑ u' : CompIn (c.stage (i - 1)).comps,
    ∑ d : admissibleOrders
        (fun v : CompIn (c.stage (i - 1)).comps => weakReductionReserve R m v.1)
        (1 + A.Jw * A.Nw) v' u',
      weakStageCoeff (weakPassageRawSetting c) m (i - 1) v' u' d s x
        (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (Whi (i - 1) u' s).toFunction.jet
            ⟨⟨d.1 - 1, by
              have h := Finset.mem_filter.1 d.2
              have := Finset.mem_Icc.1 h.1
              have h2 := h.2
              dsimp only at h2
              omega⟩, word⟩ x)

open scoped Classical in
/-- The readout weight of the child `v'` for the parent `v`. -/
def cdLam (c : WeakPassageInstance plan R) (i : ℕ) (v : CompIn (c.stage i).comps)
    (v' : CompIn (c.stage (i - 1)).comps) : ℝ :=
  if compParent i v'.1 = v.1 then cdWeight c i v'.1 else 0

/-- **The target flux** `coarseDefectFlux` of the readout `cdW`, with the letters `cdAD`, `cdCE`. -/
def cdTargetFlux (c : WeakPassageInstance plan R) (Dc m k : ℕ)
    (hK : ∀ w, k + 1 + Dc ≤ weakReductionReserve R m w) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (v : CompIn (c.stage i).comps) (s : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => ℝ) :=
  coarseDefectFlux (c.D.κ c.M) Dc (A.Jw * A.Rw) (cdAD c Dc i v₀) (cdCE c Dc i hi hit)
    (fun _ => (c.D.κ c.M) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (fun v t => cdW c m (k + 1 + Dc) hK i Uhi v t) v s x

/-- **The flux identity**: the weighted sum of the row fluxes is, a.e. in time on the window
and a.e. in space, the target flux plus the jet of `Fc`. -/
def CdFluxIdentity (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (Dc m k : ℕ)
    (hK : ∀ w, k + 1 + Dc ≤ weakReductionReserve R m w) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j)
    (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (v : CompIn (c.stage i).comps) : Prop :=
  ∀ᵐ s ∂volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)),
    (fun x => ∑ v', cdLam c i v v' • cdRowFlux c m Whi i v' s x) =ᵐ[volume.restrict unitCube]
      fun x => cdTargetFlux c Dc m k hK i hi hit v₀ Uhi v s x +
        (Fc v s).toFunction.jet (valueIndex2 k) x

/-- **Integrability** of the right side of the target identity at every time of the window,
for every `H¹` test. -/
def CdIntegrable (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (Dc m k : ℕ)
    (hK : ∀ w, k + 1 + Dc ≤ weakReductionReserve R m w) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (v : CompIn (c.stage i).comps) : Prop :=
  ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ φ : TorusHk 1 (ScalarH v.1.root),
    ∀ s ∈ Set.Ioc (r.tq i) t, Integrable (fun x =>
      -(∑ k' : Fin 2, streamVel (c.D.Φ (i - 1)) s x k' *
          inner ℝ (torusJetOrder (cdW c m (k + 1 + Dc) hK i Uhi v s) 1 (fun _ => k') x)
            (φ.toFunction.jet (valueIndex2 1) x)) -
        c.D.κ c.M * ∑ k' : Fin 2,
          inner ℝ (torusJetOrder (cdW c m (k + 1 + Dc) hK i Uhi v s) 1 (fun _ => k') x)
            (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k'⟩ x) -
        ∑ k' : Fin 2, inner ℝ (cdTargetFlux c Dc m k hK i hi hit v₀ Uhi v s x k' +
            (Fc v s).toFunction.jet (valueIndex2 k) x k')
          (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k'⟩ x) +
        inner ℝ ((0 : ℝ → Vec 2 → ℝ) s x) (φ.toFunction.jet (valueIndex2 1) x))
      (volume.restrict unitCube)

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The weighted sum of the rows** for one parent `v`: `IsCoarseDefect` at `v` from the
row identities of the passage `i`, the flux identity `CdFluxIdentity` and the integrability
`CdIntegrable`, and the jet congruences `hu`, `hf`, `hd`, `hF`, `hg` of
`coupledWeakIdentity_weighted_rows`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The passage hypothesis with the diffusivity `κ_M` and the drift of level `i - 1`. -/
theorem cdPassage_rewrite (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (m : ℕ)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw)
    (hp : WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi i) :
    IsCoupledWeakSolutionTorus (c.D.κ c.M) (r.tq i) (r.a + A.T₀)
      (streamVel (c.D.Φ (i - 1))) (1 + A.Jw * A.Nw)
      (fun v : CompIn (c.stage (i - 1)).comps => weakReductionReserve R m v.1)
      (weakStageCoeff (weakPassageRawSetting c) m (i - 1))
      (weakStageTrace (weakPassageRawSetting c) m i (Uhi i) (r.tq i))
      (fun _ _ => 0) (fun _ _ => 0) (Uhi (i - 1)) (Whi (i - 1)) := by
  have hL : c.M ≤ i - 1 := by omega
  have hlev : ((weakPassageRawSetting c).stage (i - 1)).level = i - 1 :=
    (weakPassageRawSetting c).level_eq (i - 1) hL (by show i - 1 ≤ c.M + A.Jw; omega)
  have hkap : (weakPassageRawSetting c).D.kap ((weakPassageRawSetting c).stage (i - 1)).level =
      (weakPassageRawSetting c).D.κ (weakPassageRawSetting c).M := by
    rw [hlev]; exact (weakPassageRawSetting c).kap_eq _ hL
  have hs := hp
  unfold WeakStagePassage at hs
  rw [hkap, hlev] at hs
  exact hs

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The value jets of the readout** (`hu`, `hf` of `coupledWeakIdentity_weighted_rows`):
the jet of the readout at the value index is the weighted sum of the value jets of the children,
a.e. on the cell. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

theorem cdJetOrder_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} (U : TorusHk K E)
    (w : DerivativeWord2 0) : torusJetOrder U 0 w = U.toFunction.jet (valueIndex2 K) := by
  funext x
  have hw : w = Fin.elim0 := Subsingleton.elim _ _
  subst hw
  simp only [torusJetOrder, Nat.zero_le, dite_true]
  rfl

open scoped Classical in
/-- **The value jet of the readout** is the weighted sum of the value jets of the children. -/
theorem cdReadout_value_ae (c : WeakPassageInstance plan R) (m K' : ℕ)
    (hK : ∀ w, K' ≤ weakReductionReserve R m w) (i : ℕ) (p : Comp → Prop)
    (U : ∀ v' : CompIn (c.stage (i - 1)).comps,
      TorusHk (weakReductionReserve R m v'.1) (ScalarH v'.1.root))
    (v : CompIn (c.stage i).comps) :
    (cdReadout c m K' hK i p U v).toFunction.jet (valueIndex2 K')
      =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ v' : CompIn (c.stage (i - 1)).comps,
        if compParent i v'.1 = v.1 ∧ p v'.1 then
          cdWeight c i v'.1 • (U v').toFunction.jet (valueIndex2 (weakReductionReserve R m v'.1)) x
        else 0 := by
  have h := cdReadout_jet_ae c m K' hK i p U v (m' := 0) (Nat.zero_le _) Fin.elim0
  rw [cdJetOrder_zero] at h
  refine h.trans (Filter.Eventually.of_forall fun x => ?_)
  refine Finset.sum_congr rfl fun v' _ => ?_
  rw [cdJetOrder_zero]

/-- `hu`: the weighted sum of the value jets of the children is the value jet of `cdW`. -/
theorem cdW_value_ae (c : WeakPassageInstance plan R) (m K' : ℕ)
    (hK : ∀ w, K' ≤ weakReductionReserve R m w) (i : ℕ)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (v : CompIn (c.stage i).comps) (t : ℝ) :
    (∑ j : CompIn (c.stage (i - 1)).comps, cdLam c i v j •
        (Uhi (i - 1) j t).toFunction.jet (valueIndex2 (weakReductionReserve R m j.1)))
      =ᵐ[volume.restrict AVenhance.unitCube]
      (cdW c m K' hK i Uhi v t).toFunction.jet (valueIndex2 K') := by
  have h := cdReadout_value_ae c m K' hK i (fun _ => True) (fun v' => Uhi (i - 1) v' t) v
  refine Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => ?_) h.symm
  simp only [Finset.sum_apply, Pi.smul_apply, cdLam]
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases h : compParent i v'.1 = v.1 <;> simp [h]

/-- `hf`: the same for the readout of the trace at the order `N`. -/
theorem cdF_value_ae (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (m N : ℕ)
    (hN : ∀ w, N ≤ weakReductionReserve R m w) (i : ℕ)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (v : CompIn (c.stage i).comps) :
    (∑ j : CompIn (c.stage (i - 1)).comps, cdLam c i v j •
        (weakStageTrace (weakPassageRawSetting c) m i (Uhi i) (r.tq i) j).toFunction.jet
          (valueIndex2 (weakReductionReserve R m j.1)))
      =ᵐ[volume.restrict AVenhance.unitCube]
      (cdF c r m N hN i Uhi v).toFunction.jet (valueIndex2 N) := by
  have h := cdReadout_value_ae c m N hN i (fun _ => True)
    (weakStageTrace (weakPassageRawSetting c) m i (Uhi i) (r.tq i)) v
  refine Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => ?_) h.symm
  simp only [Finset.sum_apply, Pi.smul_apply, cdLam]
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases h : compParent i v'.1 = v.1 <;> simp [h]

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The gradient jets** (`hd` of `coupledWeakIdentity_weighted_rows`): for a.e. time the
order-one jets of the lifts `Whi` weighted by `cdLam` are the order-one jets of `cdW`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The order-one jet of the lift is the order-one jet of its truncation, a.e. on the cell. -/
theorem cdLift_grad_ae {K : ℕ} (hK : 1 ≤ K) (Wl : TorusHk (K + 1) ℝ) (Ul : TorusHk K ℝ)
    (h : truncateTorusHk (Nat.le_succ K) Wl = Ul) (k : Fin 2) :
    Wl.toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩
      =ᵐ[volume.restrict AVenhance.unitCube] torusJetOrder Ul 1 (fun _ => k) := by
  subst h
  filter_upwards [Construction.Preservation.FullLift.torusJetOrder_truncate_ae (Nat.le_succ K) Wl
    hK (fun _ => k)] with x hx
  rw [hx]
  simp only [torusJetOrder, Nat.le_succ_of_le hK, dite_true]

open scoped Classical in
/-- `hd`: for a.e. time the weighted order-one jets of the lifts are those of `cdW`. -/
theorem cdW_grad_ae (c : WeakPassageInstance plan R) (m K' : ℕ)
    (hK : ∀ w, K' ≤ weakReductionReserve R m w) (hK1 : 1 ≤ K') (i : ℕ)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j) (ν : Measure ℝ)
    (hw : ∀ j : CompIn (c.stage (i - 1)).comps, ∀ᵐ s ∂ν,
      truncateTorusHk (Nat.le_succ _) (Whi (i - 1) j s) = Uhi (i - 1) j s)
    (v : CompIn (c.stage i).comps) :
    ∀ᵐ s ∂ν, ∀ k : Fin 2,
      (fun x => ∑ j : CompIn (c.stage (i - 1)).comps, cdLam c i v j •
        (Whi (i - 1) j s).toFunction.jet
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos _)⟩, fun _ => k⟩ x)
        =ᵐ[volume.restrict AVenhance.unitCube]
      torusJetOrder (cdW c m K' hK i Uhi v s) 1 (fun _ => k) := by
  filter_upwards [ae_all_iff.2 hw] with s hs k
  have h1 := cdReadout_jet_ae c m K' hK i (fun _ => True) (fun v' => Uhi (i - 1) v' s) v
    (m' := 1) hK1 (fun _ => k)
  refine Filter.EventuallyEq.trans ?_ h1.symm
  have h2 := ae_all_iff.2 fun j : CompIn (c.stage (i - 1)).comps =>
    cdLift_grad_ae (le_trans hK1 (hK j.1)) (Whi (i - 1) j s) (Uhi (i - 1) j s) (hs j) k
  filter_upwards [h2] with x hx
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hx j]
  by_cases h : compParent i j.1 = v.1 <;> simp [cdLam, h]

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The row fluxes read the jets of `Uhi`.** For almost every time the jets of the
lifts `Whi` of order `d - 1` are, a.e. on the cell, the jets of the families `Uhi`; hence
`cdRowFlux` equals `cdRowFluxU`, the flux read from `torusJetOrder (Uhi (i-1) u' s)`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The jet of a lift of order `n ≤ K` is the jet of its truncation, a.e. on the cell. -/
theorem cdLift_jet_ae {K : ℕ} {n : ℕ} (hn : n ≤ K) (Wl : TorusHk (K + 1) ℝ) (Ul : TorusHk K ℝ)
    (h : truncateTorusHk (Nat.le_succ K) Wl = Ul) (w : DerivativeWord2 n) :
    Wl.toFunction.jet ⟨⟨n, Nat.lt_succ_of_le (Nat.le_succ_of_le hn)⟩, w⟩
      =ᵐ[volume.restrict AVenhance.unitCube] torusJetOrder Ul n w := by
  subst h
  filter_upwards [Construction.Preservation.FullLift.torusJetOrder_truncate_ae (Nat.le_succ K) Wl
    hn w] with x hx
  rw [hx]
  simp only [torusJetOrder, Nat.le_succ_of_le hn, dite_true]

/-- **The row flux read from `Uhi`.** -/
def cdRowFluxU (c : WeakPassageInstance plan R) (m : ℕ)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j) (i : ℕ)
    (v' : CompIn (c.stage (i - 1)).comps) (s : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => ℝ) :=
  ∑ u' : CompIn (c.stage (i - 1)).comps,
    ∑ d : admissibleOrders
        (fun v : CompIn (c.stage (i - 1)).comps => weakReductionReserve R m v.1)
        (1 + A.Jw * A.Nw) v' u',
      weakStageCoeff (weakPassageRawSetting c) m (i - 1) v' u' d s x
        (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          torusJetOrder (Uhi (i - 1) u' s) (d.1 - 1) word x)

/-- **Row flux**: for a.e. time, `cdRowFlux = cdRowFluxU` a.e. on the cell. -/
theorem cdRowFlux_ae (c : WeakPassageInstance plan R) (m : ℕ)
    (hK1 : ∀ w, 1 ≤ weakReductionReserve R m w)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j) (ν : Measure ℝ) (i : ℕ)
    (hw : ∀ j : CompIn (c.stage (i - 1)).comps, ∀ᵐ s ∂ν,
      truncateTorusHk (Nat.le_succ _) (Whi (i - 1) j s) = Uhi (i - 1) j s) :
    ∀ᵐ s ∂ν, ∀ v' : CompIn (c.stage (i - 1)).comps,
      (fun x => cdRowFlux c m Whi i v' s x) =ᵐ[volume.restrict unitCube]
        fun x => cdRowFluxU c m Uhi i v' s x := by
  filter_upwards [ae_all_iff.2 hw] with s hs v'
  have h : ∀ (u' : CompIn (c.stage (i - 1)).comps) (d : admissibleOrders
      (fun v : CompIn (c.stage (i - 1)).comps => weakReductionReserve R m v.1)
      (1 + A.Jw * A.Nw) v' u') (word : DerivativeWord2 (d.1 - 1)),
      ∀ᵐ x ∂(volume.restrict unitCube), (Whi (i - 1) u' s).toFunction.jet
        ⟨⟨d.1 - 1, by
          have h := Finset.mem_filter.1 d.2
          have := Finset.mem_Icc.1 h.1
          have h2 := h.2
          dsimp only at h2
          omega⟩, word⟩ x = torusJetOrder (Uhi (i - 1) u' s) (d.1 - 1) word x := by
    intro u' d word
    have h1 := hK1 v'.1
    have hd := Finset.mem_filter.1 d.2
    have hd2 := hd.2
    dsimp only at hd2
    exact cdLift_jet_ae (by omega) (Whi (i - 1) u' s) (Uhi (i - 1) u' s) (hs u') word
  have h' := ae_all_iff.2 fun u' => ae_all_iff.2 fun d => ae_all_iff.2 fun word => h u' d word
  filter_upwards [h'] with x hx
  unfold cdRowFlux cdRowFluxU
  refine Finset.sum_congr rfl fun u' _ => Finset.sum_congr rfl fun d _ => ?_
  congr 2
  funext word
  exact hx u' d word

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end
end
