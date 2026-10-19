-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.Transverse.Ops
public import AVRegularity.Definitions.Construction.ScheduleFloor
import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.FullX
import AVRegularity.Proofs.Results.Construction.SuccWindowData.Jacobian
import AVRegularity.CycleReference.ChartDerivativeBounded
import AVRegularity.Proofs.Results.Construction.SuccessorFluxUnique
public import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Algebra.Order.Star.Real

section
section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity
namespace AVRegularity.Providers.GenSem

/-! Structural transversality of generated expressions.

Every function denoted by an expression of `Gen` over the slot `p` is invariant under parallel
shifts of the phases of the children of its chain (each along the parallel direction of its own
pulse, `ParEq`); a context or cell function is also invariant under a parallel shift of its
internal phase `ζ`/`η` along `parIdx p`; a family function only has the chain invariance.
The invariances are stated on well-slotted chains whose last slot is `p`
(`ch.WellSlotted ∧ ch.slot = p`): the appended child of (K6) is built from the pulse
`ch.slot`, so the parallel direction of the phase is that of `ch.slot`, not of an arbitrary slot.

A `solved` node is pinned by an equation only, so its invariance is a hypothesis
(a predicate defined by recursion on the expression). No premise on the fast profile
and no scheduling is needed (`Gen.IsScheduled` is carried only to match the statement). -/

/-- Invariance of a context/cell function over the slot `p`: under parallel shifts of the child
phases of well-slotted chains with last slot `p`, and under `+ s • e_{parIdx p}` in the internal
variable. -/
def ParInv (p : ℤ) (f : ℝ → RealChain → Vec 2 → ℝ) : Prop :=
  (∀ t ch ch' ζ, ch.WellSlotted → ch.slot = p → ParEq ch ch' → f t ch' ζ = f t ch ζ) ∧
  ∀ t ch ζ (s : ℝ), ch.WellSlotted → ch.slot = p → f t ch (ζ + s • basisVec (parIdx p)) = f t ch ζ

/-- Invariance of a family function over the slot `p` under parallel shifts of child phases. -/
def FamInv (p : ℤ) (f : ℝ → RealChain → ℝ) : Prop :=
  ∀ t ch ch', ch.WellSlotted → ch.slot = p → ParEq ch ch' → f t ch' = f t ch

/-- Invariance of a context function over the slot `p`. -/
abbrev CtxInv (p : ℤ) (f : GenSort.Sem .ctx) : Prop := ParInv p f

/-- Invariance of a cell function over the slot `p`. -/
abbrev CellInv (p : ℤ) (f : GenSort.Sem .cell) : Prop := ParInv p f

/-- The invariance predicate of a sort. -/
def _root_.AVRegularity.GenSort.ParInv : (s : GenSort) → ℤ → s.Sem → Prop
  | .ctx, p, f => CtxInv p f
  | .fam, p, f => FamInv p f
  | .cell, p, f => CellInv p f

theorem ParInv.zipWith {p : ℤ} {fa fb : ℝ → RealChain → Vec 2 → ℝ} (op : ℝ → ℝ → ℝ)
    (ha : ParInv p fa) (hb : ParInv p fb) : ParInv p (fun t c z => op (fa t c z) (fb t c z)) :=
  ⟨fun t ch ch' ζ hl hs hp => by simp only [ha.1 t ch ch' ζ hl hs hp, hb.1 t ch ch' ζ hl hs hp],
    fun t ch ζ s hl hs => by simp only [ha.2 t ch ζ s hl hs, hb.2 t ch ζ s hl hs]⟩

theorem FamInv.zipWith {p : ℤ} {fa fb : ℝ → RealChain → ℝ} (op : ℝ → ℝ → ℝ)
    (ha : FamInv p fa) (hb : FamInv p fb) : FamInv p (fun t c => op (fa t c) (fb t c)) :=
  fun t ch ch' hl hs hp => by simp only [ha t ch ch' hl hs hp, hb t ch ch' hl hs hp]

theorem evalAt_parEq (D : OCData) {ch ch' : RealChain} (h : ParEq ch ch') (u : ℝ)
    (L : GeoLetter) : L.evalAt D ch' u = L.evalAt D ch u := by
  have hg := h.geom D
  have hll : ch'.lastLevel = ch.lastLevel := by
    simp only [RealChain.lastLevel, h.1, h.children_length]
  cases L <;> simp [GeoLetter.evalAt, RealChain.famJac, RealChain.famMetric, RealChain.famStrain,
    hg, hll]

theorem famMetric_parEq (D : OCData) {ch ch' : RealChain} (h : ParEq ch ch') (u : ℝ) :
    ch'.famMetric D u = ch.famMetric D u := by
  have hg := h.geom D
  simp [RealChain.famJac, RealChain.famMetric, hg]

theorem driftSem_phase (D : OCData) (i : ℕ) (p : ℤ) (c : Fin 2) (t : ℝ) (ch : RealChain)
    (η : Vec 2) (s : ℝ) :
    driftSem D i p c t ch (η + s • basisVec (parIdx p)) = driftSem D i p c t ch η := by
  have key : ocEpsilon D.q D.Λ i • (η + s • basisVec (parIdx p)) =
      ocEpsilon D.q D.Λ i • η + (ocEpsilon D.q D.Λ i * s) • basisVec (parIdx p) := by
    rw [smul_add, smul_smul]
  simp only [driftSem, ocPulseCellDrift, key, ocShearVel_add_parallel]

theorem transverseInverseSem_phase (D : OCData) (i : ℕ) (p : ℤ) (F : Fin 2 → GenSort.Sem .cell)
    (t₀ : ℝ) (ι : GenSort.Sem .cell) (t : ℝ) (ch : RealChain) (η : Vec 2) (s : ℝ) :
    transverseInverseSem D i p F t₀ ι t ch (η + s • basisVec (parIdx p)) =
      transverseInverseSem D i p F t₀ ι t ch η := by
  simp only [transverseInverseSem, par_shift_transverse]

theorem transversePrimitiveSem_phase (p : ℤ) (f : GenSort.Sem .cell) (t : ℝ) (ch : RealChain)
    (η : Vec 2) (s : ℝ) :
    transversePrimitiveSem p f t ch (η + s • basisVec (parIdx p)) =
      transversePrimitiveSem p f t ch η := by
  simp only [transversePrimitiveSem, par_shift_transverse]

/-- Invariance under the parallel shift of the phase of the `k`-th child alone. -/
theorem ParInv.shiftChild {p : ℤ} {f : ℝ → RealChain → Vec 2 → ℝ} (hf : ParInv p f) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (hl : ch.WellSlotted) (hs : ch.slot = p) (k : ℕ) (s : ℝ) :
    f t (ch.shiftChild k s) ζ = f t ch ζ :=
  hf.1 t ch _ ζ hl hs (parEq_shiftChild ch k s)

theorem FamInv.shiftChild {p : ℤ} {f : ℝ → RealChain → ℝ} (hf : FamInv p f) (t : ℝ)
    (ch : RealChain) (hl : ch.WellSlotted) (hs : ch.slot = p) (k : ℕ) (s : ℝ) :
    f t (ch.shiftChild k s) = f t ch :=
  hf t ch _ hl hs (parEq_shiftChild ch k s)

end AVRegularity.Providers.GenSem
end
end

section
/-! Facade for the denotability closure of coefficient arrays. -/
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The slow-offset torus law of the actual successor: on a context
without children, moving the slow offset by `ε_{m-1}⁻¹ n` is shifting the base label by `n`, because
the fields of `IsActualSuccessor` are pinned at the recentered context `c.recenter (ε X)`, and on a
base family recentering adds to the base label. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem RealChain.recenter_add_shiftBase (D : OCData) (ch : RealChain) (h0 : ch.children = [])
    (n : Fin 2 → ℤ) (h : Vec 2) :
    ch.recenter D (h + AVenhance.latticeShift n) = (ch.shiftBase n).recenter D h := by
  obtain ⟨bl, sl, bs, ch'⟩ := ch
  simp only at h0
  subst h0
  simp only [RealChain.recenter, RealChain.shiftBase, List.getLast?_nil, RealChain.mk.injEq,
    true_and, and_true]
  abel

/-- **The slow-offset torus law of the actual successor.** -/
theorem IsActualSuccessor.slowOffset {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (hs : IsActualSuccessor D P Mn G G') (hε : D.eps (G'.level - 1) ≠ 0) :
    ∀ (p : OddSlot) (c c' : StageCtx D b j₀ G'.level p) (n : Fin 2 → ℤ), c.1.children = [] →
      c'.1 = c.1.shiftBase n →
      ∀ v u (γ : G'.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2),
        G'.fam.flux p c v u γ d I t (X + (D.eps (G'.level - 1))⁻¹ • AVenhance.latticeShift n) z =
          G'.fam.flux p c' v u γ d I t X z := by
  intro p c c' n h0 hc v u γ d I t X z
  have hrec : c.1.recenter D (D.eps (G'.level - 1) •
      (X + (D.eps (G'.level - 1))⁻¹ • AVenhance.latticeShift n)) =
      c'.1.recenter D (D.eps (G'.level - 1) • X) := by
    rw [smul_add, smul_inv_smul₀ hε, hc, RealChain.recenter_add_shiftBase D c.1 h0]
  by_cases hd : 2 ≤ d
  · obtain ⟨-, -, -, -, -, -, e, Cc, Cc0, -, -, hmain⟩ := hs
    obtain ⟨-, -, hnd, hdg⟩ := hmain v u γ
    by_cases hD : (e v u γ).1.IsDiag
    · rw [hdg hD p c d I t _ z hd, hdg hD p c' d I t X z hd, hrec]
    · rw [hnd hD p c d I t _ z hd, hnd hD p c' d I t X z hd, hrec]
  · have h1 := G'.fam.flux_zero p c v u γ d I (fun h => hd h.1)
    have h2 := G'.fam.flux_zero p c' v u γ d I (fun h => hd h.1)
    rw [h1, h2]

/-- **The slow-offset torus law of the actual successor, without assuming `ε_{m-1} ≠ 0`**: when
`ε_{m-1} = 0` the offset does not move and the base-label clause of `G'` gives the law. -/
theorem IsActualSuccessor.slowOffset' {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D hr Dm b j₀} (hs : IsActualSuccessor D P Mn G G')
    (hbase : ∀ (p : OddSlot) (c c' : StageCtx D b j₀ G'.level p) (n : Fin 2 → ℤ),
      c'.1 = c.1.shiftBase n → ∀ v u (γ : G'.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)),
        G'.fam.flux p c' v u γ d I = G'.fam.flux p c v u γ d I) :
    ∀ (p : OddSlot) (c c' : StageCtx D b j₀ G'.level p) (n : Fin 2 → ℤ), c.1.children = [] →
      c'.1 = c.1.shiftBase n →
      ∀ v u (γ : G'.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2),
        G'.fam.flux p c v u γ d I t (X + (D.eps (G'.level - 1))⁻¹ • AVenhance.latticeShift n) z =
          G'.fam.flux p c' v u γ d I t X z := by
  by_cases hε : D.eps (G'.level - 1) = 0
  · intro p c c' n _ hc v u γ d I t X z
    rw [hε, inv_zero, zero_smul, add_zero, hbase p c c' n hc v u γ d I]
  · exact hs.slowOffset hε

end AVRegularity
end
end
end

section
section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.GenStage

/-! **The coefficient certificate of an incoming stage** (`GenStage.OldCert`). The generation
(`SuccessorGeneration`) and the cascade invariants (`CascadeInvariants`) read
the coefficients of the incoming stage through their certificate: generated functions with
holomorphic extensions, whose context sizes are at most ledger entries `θ`, the entries being
bounded by the records. `OldCert G 𝒮 μ L Cθ` is that certificate with a registry `𝒮`, a reserve
`μ c` of each component `c`, a fast weight `L` and a factor `Cθ` on the record bound. The context
certificate of the cascade is the case `𝒮 = G.exports`, `μ = compReserve k`, `L = k.Lstar`,
`Cθ = 1` (`GenStage.IsContextCertified.oldCert`). The weak certificate is the case of the empty
registry, a reserve above `1` and a factor `Cθ ≥ 1` (weak entry). -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- **The coefficient certificate** of `G` with the registry `𝒮`, the reserves `μ`, the fast
weight `L` and the record factor `Cθ`. -/
def OldCert (G : GenStage D hr Dm b j₀) (𝒮 : SeedExports) (μ : Comp → ℝ) (L : ℕ) (Cθ : ℝ) :
    Prop :=
  ∀ v u (γ : G.fam.Γ v u), ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
    (∀ d α c, 0 ≤ θ d α c) ∧
    (∀ d, 2 ≤ d → d ≤ (G.fam.identity v u γ).maxOrder →
      (D.eps G.level / (G.fam.identity v u γ).record.length) ^ (d - 2) *
          ∑ α, ∑ c, θ d α c ≤ Cθ * (G.fam.identity v u γ).record.size) ∧
    ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
      ∃ (f : OddSlot → GenSort.Sem .ctx)
        (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ),
        (∀ p, IsGeneratedCtxFrom D b j₀ 𝒮 G.level p.1 (f p) ∧
          IsHolExtension D b j₀ G.level p.1 (f p) (F p) ∧
          ∀ (ctx : StageCtx D b j₀ G.level p) (t : ℝ), t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
            ∀ (X z : Vec 2),
            G.fam.flux p ctx v u γ d α t X z c =
              if IsAdmissibleChain D b j₀ G.level p.1 (ctx.1.recenter D (D.eps (G.level - 1) • X))
              then f p t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0) ∧
        ctxSize D b j₀ G.level F (μ v.1) L ≤ ENNReal.ofReal (θ d α c)

/-- The context certificate of the cascade is a coefficient certificate. -/
theorem IsContextCertified.oldCert {k : InvConsts} {G : GenStage D hr Dm b j₀}
    (h : G.IsContextCertified k) : G.OldCert G.exports (compReserve k) k.Lstar 1 := by
  intro v u γ
  obtain ⟨θ, h0, hr, hc⟩ := h v u γ
  exact ⟨θ, h0, fun d hd hdn => by rw [one_mul]; exact hr d hd hdn, hc⟩

end AVRegularity.GenStage
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **The cell problem of each lift coefficient.** For a lift sequence with scalar fibres, the
coefficient `C^{(hh)}_{n,m,I}(·, X, ·)` of the entry `(v ← u)` is the finite-past cell inverse at the
slow point `X` of `(m!)⁻¹ · (liftCellSource)_v` for the monomial test field `mono X I` placed in the
component `u`: at its centre the monomial picks exactly the coefficient of the word `I`
(`sum_orderedDerivative_mono` and the symmetry of the words). -/

open AVRegularity.Providers.PathDecomp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The monomial test field `mono X I` in the component `u`. -/
def monoField (u : ι) (y : Vec 2) {m : ℕ} (I : DerivativeWord2 m) : Vec 2 → ∀ _ : ι, ℝ :=
  fun Y => Pi.single u (mono y I Y)

theorem contDiff_monoField (u : ι) (y : Vec 2) {m : ℕ} (I : DerivativeWord2 m) :
    ContDiff ℝ (⊤ : ℕ∞) (monoField u y I) := by
  have e : monoField u y I = (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) u) ∘ mono y I := by
    funext Y; simp [monoField]
  rw [e]
  exact (ContinuousLinearMap.contDiff _).comp ((contDiff_mono y I).of_le (by exact_mod_cast le_top))

/-- At its centre the monomial field picks the coefficient of its word (the coefficients of order
`m` symmetric at the time `t` and the slow point `y` only). -/
theorem liftApply_monoField_at {Cc : LiftCoeff ι (fun _ => ℝ)} {n m : ℕ} (hmn : m ≤ n)
    (u : ι) (y : Vec 2) (I : DerivativeWord2 m) (t : ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin m)) (α : DerivativeWord2 m), Cc m (α ∘ σ) t y = Cc m α t y)
    (z : Vec 2) (v : ι) :
    liftApply n Cc (fun _ => monoField u y I) t y z v =
      (m.factorial : ℝ) * Cc m I t y z v u 1 := by
  have hod : ∀ {m'} (α : DerivativeWord2 m'), orderedDerivative α (monoField u y I) =
      fun Y => Pi.single u (orderedDerivative α (mono y I) Y) := by
    intro m' α
    have e : monoField u y I = fun Y => (Pi.single u (mono y I Y • (1 : ℝ)) : ∀ _ : ι, ℝ) := by
      funext Y; simp [monoField]
    rw [e, orderedDerivative_single (hs := fun _ : ι => ℝ) (1 : ℝ)
      ((contDiff_mono y I).of_le (by exact_mod_cast le_top)) α]
    funext Y; simp
  simp only [liftApply, hod]
  have hsingle : ∀ {m'} (α : DerivativeWord2 m'),
      ∑ u' : ι, Cc m' α t y z v u'
          ((Pi.single u (orderedDerivative α (mono y I) y) : ∀ _ : ι, ℝ) u') =
        orderedDerivative α (mono y I) y • Cc m' α t y z v u 1 := by
    intro m' α
    rw [Finset.sum_eq_single u (fun u' _ hu' => by simp [hu'])
      (fun h => absurd (Finset.mem_univ u) h)]
    rw [Pi.single_eq_same, smul_eq_mul, mul_comm,
      show orderedDerivative α (mono y I) y = orderedDerivative α (mono y I) y • (1 : ℝ) by simp,
      map_smul, smul_eq_mul]
    simp [mul_comm]
  simp_rw [hsingle]
  rw [Finset.sum_eq_single m]
  · rw [sum_orderedDerivative_mono y I (fun α => Cc m α t y z v u 1)]
    have hc : ∀ σ : Equiv.Perm (Fin m), Cc m (I ∘ σ) t y z v u 1 = Cc m I t y z v u 1 :=
      fun σ => by rw [hsym σ I]
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul]
  · intro m' _ hm'
    exact sum_orderedDerivative_mono_of_ne y I (fun α => Cc m' α t y z v u 1) hm'
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hmn)) h

/-- At its centre the monomial field picks the coefficient of its word. -/
theorem liftApply_monoField {Cc : LiftCoeff ι (fun _ => ℝ)} {n m : ℕ} (hmn : m ≤ n)
    (hsym : ∀ (σ : Equiv.Perm (Fin m)) (α : DerivativeWord2 m), Cc m (α ∘ σ) = Cc m α)
    (u : ι) (y : Vec 2) (I : DerivativeWord2 m) (t : ℝ) (z : Vec 2) (v : ι) :
    liftApply n Cc (fun _ => monoField u y I) t y z v =
      (m.factorial : ℝ) * Cc m I t y z v u 1 :=
  liftApply_monoField_at hmn u y I t (fun σ α => by rw [hsym σ α]) z v

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public section
open Homogenization AVRegularity AVRegularity.Providers.SuccWindow
namespace AVRegularity.Providers.GenSem

/-! Regularity of the chain metric `famMetric = F⁻¹F⁻ᵀ` of a real chain.

The metric is symmetric; the Jacobian `F_u = D_x𝔛(u, x_𝒜, s)` of the offset flow is invertible
(inverse law of the flow group) and continuous in `u` (joint `C¹` regularity of the chain flows,
`geomC1_geom`). Hence the metric is continuous, measurable, and uniformly positive definite with
bounded entries on every compact time window. The corollaries are the hypotheses of
`AVRegularity.Providers.lift_sequence_unique_elliptic` for `familyLiftData`. -/

/-- The molecular metric of a chain is symmetric. -/
theorem famMetric_symm (D : OCData) (ch : RealChain) (u : ℝ) (i j : Fin 2) :
    ch.famMetric D u i j = ch.famMetric D u j i := by
  have h : (ch.famMetric D u).transpose = ch.famMetric D u := by
    unfold RealChain.famMetric
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  exact (congrFun (congrFun h i) j).symm

/-- The Jacobian of the last family of a chain is invertible. -/
theorem famJac_isUnit (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) (u : ℝ) :
    IsUnit (ch.famJac D u).det :=
  jac_isUnit_det (ChainGeometry.invLaw_geomAux D _ _ _ (ChainGeometry.invLaw_base D _ _ _))
    (geomC1_geom D hζ ch) u _ _

/-- The Jacobian of the last family of a chain is continuous in time. -/
theorem continuous_famJac (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) :
    Continuous fun u => ch.famJac D u :=
  jac_continuous (f := fun u y => (ch.geom D).1 u y (ch.geom D).2.2)
    (geomC1_geom D hζ ch (ch.geom D).2.2) _

/-- The inverse Jacobian of a chain is continuous in time. -/
theorem continuous_famJac_inv (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) :
    Continuous fun u => (ch.famJac D u)⁻¹ :=
  continuous_inv_of_det (continuous_famJac D hζ ch) (famJac_isUnit D hζ ch)

/-- The chain metric is continuous in time. -/
theorem continuous_famMetric (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) :
    Continuous fun u => ch.famMetric D u := by
  have h := continuous_famJac_inv D hζ ch
  exact h.matrix_mul h.matrix_transpose

/-- The chain metric is measurable in time. -/
theorem measurable_famMetric (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) :
    Measurable fun u => ch.famMetric D u :=
  (continuous_famMetric D hζ ch).measurable

/-- Each entry of the chain metric is measurable in time. -/
theorem measurable_famMetric_apply (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain)
    (i j : Fin 2) : Measurable fun u => ch.famMetric D u i j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_famMetric D hζ ch))

/-- Entry bounds on a compact interval for a continuous matrix family. -/
theorem exists_entry_bound' {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hF : Continuous F) (a b : ℝ) :
    ∃ M : ℝ, ∀ t ∈ Set.Icc a b, ∀ i j, |F t i j| ≤ M := by
  have he : ∀ i j : Fin 2, Continuous (fun t => F t i j) := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hF)
  have hc : Continuous (fun t => |F t 0 0| + |F t 0 1| + |F t 1 0| + |F t 1 1|) := by fun_prop
  obtain ⟨M, -, hM⟩ := exists_bound_Icc hc a b
  refine ⟨M, fun t ht i j => ?_⟩
  have := hM t ht
  rw [abs_of_nonneg (by positivity)] at this
  have h00 := abs_nonneg (F t 0 0)
  have h01 := abs_nonneg (F t 0 1)
  have h10 := abs_nonneg (F t 1 0)
  have h11 := abs_nonneg (F t 1 1)
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- Uniform ellipticity of the chain metric on a compact time window. -/
theorem famMetric_pos_window (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) (a b : ℝ) :
    ∃ lo hi : ℝ, 0 < lo ∧ ∀ u ∈ Set.Icc a b, ∀ ξ : Vec 2,
      lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ch.famMetric D u i j * ξ i * ξ j ∧
        ∑ i, ∑ j, ch.famMetric D u i j * ξ i * ξ j ≤ hi * ∑ i, ξ i ^ 2 := by
  obtain ⟨M, hM⟩ := exists_entry_bound' (continuous_famJac D hζ ch) a b
  obtain ⟨N, hN⟩ := exists_entry_bound' (continuous_famJac_inv D hζ ch) a b
  refine ⟨(4 * M ^ 2 + 1)⁻¹, 4 * N ^ 2, by positivity, fun u hu ξ => ⟨?_, ?_⟩⟩
  · exact metric_elliptic (Matrix.nonsing_inv_mul _ (famJac_isUnit D hζ ch u)) (hM u hu) ξ
  · have hE := metric_entry_le (hN u hu)
    have hN0 : 0 ≤ N := (abs_nonneg _).trans (hN u hu 0 0)
    have h : ∀ i j, |ch.famMetric D u i j * ξ i * ξ j| ≤
        2 * N ^ 2 * (|ξ i| * |ξ j|) := by
      intro i j
      rw [abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right (hE i j) (by positivity)
    have hs : ∑ i, ∑ j, ch.famMetric D u i j * ξ i * ξ j ≤
        ∑ i, ∑ j, 2 * N ^ 2 * (|ξ i| * |ξ j|) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        (le_abs_self _).trans (h i j)
    refine hs.trans ?_
    simp only [Fin.sum_univ_two]
    have a0 := sq_abs (ξ 0)
    have a1 := sq_abs (ξ 1)
    nlinarith [sq_nonneg (|ξ 0| - |ξ 1|), sq_nonneg N, mul_nonneg (sq_nonneg N)
      (sq_nonneg (|ξ 0| - |ξ 1|))]

/-! ### The uniqueness hypotheses for `familyLiftData` -/

section Lift

variable {ι : Type*} {hv : ι → Type*} [∀ i, NormedAddCommGroup (hv i)]
  [∀ i, NormedSpace ℝ (hv i)] {Dm : ℕ}

/-- Symmetry of the lift metric. -/
theorem familyLiftData_symm (D : OCData) (m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm hv) (t : ℝ) (X : Vec 2) (i j : Fin 2) :
    (familyLiftData D m k A ρ edge).G t X i j = (familyLiftData D m k A ρ edge).G t X j i :=
  famMetric_symm D _ _ i j

/-- Measurability of the lift metric in time. -/
theorem familyLiftData_G_measurable (D : OCData) (hζ : IsFastProfile D.ζ) (m : ℕ) (k : ℤ)
    (A : RealChain) (ρ : ℝ) (edge : ConstituentEdges Dm hv) (X : Vec 2) (i j : Fin 2) :
    Measurable fun t => (familyLiftData D m k A ρ edge).G t X i j :=
  (measurable_famMetric_apply D hζ (A.recenter D (ρ • X)) i j).comp
    (measurable_const.mul measurable_id)

/-- Window ellipticity of the lift metric. -/
theorem familyLiftData_pos_window (D : OCData) (hζ : IsFastProfile D.ζ) (m : ℕ) (k : ℤ)
    (A : RealChain) (ρ : ℝ) (edge : ConstituentEdges Dm hv) (t₀ t₁ : ℝ) (X : Vec 2) :
    ∃ lo hi : ℝ, 0 < lo ∧ ∀ t ∈ Set.Icc t₀ t₁, ∀ ξ : Vec 2,
      lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, (familyLiftData D m k A ρ edge).G t X i j * ξ i * ξ j ∧
        ∑ i, ∑ j, (familyLiftData D m k A ρ edge).G t X i j * ξ i * ξ j ≤
          hi * ∑ i, ξ i ^ 2 := by
  set c := D.cellScaleSq m
  obtain ⟨lo, hi, hlo, h⟩ := famMetric_pos_window D hζ (A.recenter D (ρ • X))
    (min (c * t₀) (c * t₁)) (max (c * t₀) (c * t₁))
  refine ⟨lo, hi, hlo, fun t ht ξ => h (c * t) ?_ ξ⟩
  obtain ⟨h0, h1⟩ := ht
  rcases le_total 0 c with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h0 hc),
      (mul_le_mul_of_nonneg_left h1 hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h1 hc),
      (mul_le_mul_of_nonpos_left h0 hc).trans (le_max_left _ _)⟩

/-- Measurability of the pulse drift in time. -/
theorem ocPulseCellDrift_measurable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (m : ℕ) (ν : ℝ) (k : ℤ) (z : Vec 2) :
    Measurable fun t => ocPulseCellDrift α q Λ ζ m ν k t z := by
  have hc : Continuous (ocPulse α q Λ ζ m k) := CycleReference.ocPulse_continuous hζ k
  unfold ocPulseCellDrift
  have h1 : Continuous fun t : ℝ => ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) :=
    hc.comp (continuous_const.mul continuous_id)
  have h2 : Continuous fun t : ℝ => ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) •
      ocShearVel α q Λ m k (ocEpsilon q Λ m • z) :=
    h1.smul (continuous_const : Continuous fun _ : ℝ => ocShearVel α q Λ m k (ocEpsilon q Λ m • z))
  exact (h2.const_smul (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m)).measurable

/-- Uniform sup-norm bound of the pulse drift of an odd pulse. -/
theorem ocPulseCellDrift_norm_bound {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (m : ℕ) (ν : ℝ) {k : ℤ} (hk : Odd k) :
    ∃ Mv : ℝ, ∀ t z, ‖ocPulseCellDrift α q Λ ζ m ν k t z‖ ≤ Mv := by
  obtain ⟨M, hM⟩ := ocPulseCellDrift_bound (α := α) (q := q) (Λ := Λ) hζ m ν hk
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 0)
  exact ⟨M, fun t z => (pi_norm_le_iff_of_nonneg hM0).2 fun j => by
    simpa [Real.norm_eq_abs] using hM t z j⟩

/-- Measurability of the lift drift in time. -/
theorem familyLiftData_v_measurable (D : OCData) (hζ : IsFastProfile D.ζ) (m : ℕ) (k : ℤ)
    (A : RealChain) (ρ : ℝ) (edge : ConstituentEdges Dm hv) (z : Vec 2) :
    Measurable fun t => (familyLiftData D m k A ρ edge).v t z :=
  ocPulseCellDrift_measurable hζ _ _ _ z

/-- Boundedness of the lift drift (odd pulse). -/
theorem familyLiftData_v_bounded (D : OCData) (hζ : IsFastProfile D.ζ) (m : ℕ) {k : ℤ}
    (hk : Odd k) (A : RealChain) (ρ : ℝ) (edge : ConstituentEdges Dm hv) :
    ∃ Mv : ℝ, ∀ t z, ‖(familyLiftData D m k A ρ edge).v t z‖ ≤ Mv :=
  ocPulseCellDrift_norm_bound hζ _ _ hk

end Lift

end AVRegularity.Providers.GenSem
end
end
end
