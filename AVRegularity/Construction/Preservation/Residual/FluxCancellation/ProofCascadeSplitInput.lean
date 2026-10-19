-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetPoly
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovarianceFluxRegLiftFlux
import AVRegularity.CycleWords.CellTransitionLipschitz
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetSteps
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.EntryWeakAssembly.FiniteStagePaths
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCenteredConstantsWindow
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep

section
section
/-! **The jet-locality step, `liftApply` at finite regularity**.

`liftApply n c a t X z` is the differential operator `∑_{m ≤ n} ∑_α c_{m,α}(t, X, z) ∂^α a(t, X)`
of order `≤ n` in `X`, with coefficients smooth in `X`. If two fields `a₁(t, ·)`, `a₂(t, ·)` of class
`C^{S+N}` have equal jets of the orders `≤ S + N` at `X₀`, then for every `z` the lifted fields have
equal jets of the orders `≤ S` in `X` at `X₀` (`liftApply_sameJet`).

For `n = 0` the term is the coefficient times the value, and for `n > N` both sides are zero. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- Equal jets of the lifted fields in `X`, at every `z`. -/
def SameJetX {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ) (X₀ : Vec 2)
    (Φ₁ Φ₂ : Vec 2 → Vec 2 → E) : Prop :=
  ∀ z, SameJetAt r X₀ (fun X => Φ₁ X z) (fun X => Φ₂ X z)

theorem sameJet_orderedDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m r : ℕ} (α : DerivativeWord2 m) {x : Vec 2} {f g : Vec 2 → E}
    (h : SameJetAt (r + m) x f g) :
    SameJetAt r x (orderedDerivative α f) (orderedDerivative α g) := fun j I hj => by
  rw [← AVRegularity.CycleWords.orderedDerivative_append,
    ← AVRegularity.CycleWords.orderedDerivative_append]
  exact h _ _ (by omega)

/-- The `X`-slice of a box smooth field is `C^S`. -/
theorem boxSmooth_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : ℕ}
    {f : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth S S f) (z : Vec 2) :
    ContDiff ℝ (↑S : ℕ∞) (fun X => f X z) :=
  (hf.contDiff_uncurry le_rfl le_rfl).comp (contDiff_id.prodMk contDiff_const)

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- Equal jets of the coarse fields give equal jets of the lifted fields, one component. -/
theorem liftApply_sameJet_comp (Cc : ℕ → ℕ → LiftCoeff ι h) (a₁ a₂ : ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (hh n' S N : ℕ) (hn : n' ≤ N) (X₀ : Vec 2)
    (hb : ∀ n' m α v u, IsBoxSmooth S S (fun X z => Cc hh n' m α t X z v u))
    (ha₁ : ContDiff ℝ (↑(S + N) : ℕ∞) (a₁ t)) (ha₂ : ContDiff ℝ (↑(S + N) : ℕ∞) (a₂ t))
    (hj : SameJetAt (S + N) X₀ (a₁ t) (a₂ t)) (z : Vec 2) (v : ι) :
    SameJetAt S X₀ (fun X => liftApply n' (Cc hh n') a₁ t X z v)
      (fun X => liftApply n' (Cc hh n') a₂ t X z v) := by
  have hd : ∀ {a : ℝ → Vec 2 → ∀ i, h i}, ContDiff ℝ (↑(S + N) : ℕ∞) (a t) → ∀ m ≤ N,
      ∀ (α : DerivativeWord2 m) (u : ι),
      ContDiff ℝ (↑S : ℕ∞) (fun X => orderedDerivative α (a t) X u) := by
    intro a ha m hm α u
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp
      (AVRegularity.Sampling.contDiff_orderedDerivative S α (a t) (cd_le (by omega) ha))
  have hleaf : ∀ {a : ℝ → Vec 2 → ∀ i, h i}, ContDiff ℝ (↑(S + N) : ℕ∞) (a t) → ∀ m ≤ N,
      ∀ (α : DerivativeWord2 m) (u : ι),
      ContDiff ℝ (↑S : ℕ∞) (fun X => Cc hh n' m α t X z v u (orderedDerivative α (a t) X u)) := by
    intro a ha m hm α u
    exact (boxSmooth_slice (hb n' m α v u) z).clm_apply (hd ha m hm α u)
  unfold liftApply
  have hsum : ∀ {a : ℝ → Vec 2 → ∀ i, h i}, ContDiff ℝ (↑(S + N) : ℕ∞) (a t) → ∀ m ∈ Finset.range (n' + 1),
      ContDiff ℝ (↑S : ℕ∞) (fun X => ∑ α : DerivativeWord2 m, ∑ u : ι,
        Cc hh n' m α t X z v u (orderedDerivative α (a t) X u)) := by
    intro a ha m hm
    have hm' : m ≤ N := by have := Finset.mem_range.1 hm; omega
    exact ContDiff.sum fun α _ => ContDiff.sum fun u _ => hleaf ha m hm' α u
  refine sameJet_sum _ (fun m hm => hsum ha₁ m hm) (fun m hm => hsum ha₂ m hm) fun m hm => ?_
  have hm' : m ≤ N := by have := Finset.mem_range.1 hm; omega
  refine sameJet_sum _ (fun α _ => ContDiff.sum fun u _ => hleaf ha₁ m hm' α u)
    (fun α _ => ContDiff.sum fun u _ => hleaf ha₂ m hm' α u) fun α _ => ?_
  refine sameJet_sum _ (fun u _ => hleaf ha₁ m hm' α u) (fun u _ => hleaf ha₂ m hm' α u)
    fun u _ => ?_
  have hjα : SameJetAt S X₀ (fun X => orderedDerivative α (a₁ t) X u)
      (fun X => orderedDerivative α (a₂ t) X u) :=
    sameJet_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)
      (AVRegularity.Sampling.contDiff_orderedDerivative S α (a₁ t) (cd_le (by omega) ha₁))
      (AVRegularity.Sampling.contDiff_orderedDerivative S α (a₂ t) (cd_le (by omega) ha₂))
      (sameJet_orderedDerivative α (sameJet_mono (by omega) hj))
  exact sameJet_bilin (ContinuousLinearMap.id ℝ (h u →L[ℝ] h v)) X₀ S _ _ _
    (boxSmooth_slice (hb n' m α v u) z) (hd ha₁ m hm' α u) (hd ha₂ m hm' α u) hjα

/-- Equal jets of a `Pi`-valued function from equal jets of its components. -/
theorem sameJet_pi {r : ℕ} {x : Vec 2} {f g : Vec 2 → ∀ i, h i}
    (hf : ∀ v, ContDiff ℝ (↑r : ℕ∞) (fun y => f y v)) (hg : ∀ v, ContDiff ℝ (↑r : ℕ∞) (fun y => g y v))
    (hj : ∀ v, SameJetAt r x (fun y => f y v) (fun y => g y v)) : SameJetAt r x f g := by
  intro j I hj'
  have hj'' : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((r : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hj'
  funext v
  have e1 := congrFun (AVRegularity.orderedDerivative_clm_comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) I (g := f) (contDiff_pi.2 hf |>.of_le hj'')) x
  have e2 := congrFun (AVRegularity.orderedDerivative_clm_comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) I (g := g) (contDiff_pi.2 hg |>.of_le hj'')) x
  simp only [ContinuousLinearMap.proj_apply] at e1 e2
  have := hj v j I hj'
  rw [e1, e2] at this
  exact this

/-- `liftApply` at finite regularity: equal jets in `X` at every `z`, all degrees. -/
theorem liftApply_sameJet (Cc : ℕ → ℕ → LiftCoeff ι h) (a₁ a₂ : ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (hh n' S N : ℕ) (X₀ : Vec 2)
    (hz : ∀ n', N < n' → ∀ m α t X z v u, Cc hh n' m α t X z v u = 0)
    (hb : ∀ n' m α v u, IsBoxSmooth S S (fun X z => Cc hh n' m α t X z v u))
    (ha₁ : ContDiff ℝ (↑(S + N) : ℕ∞) (a₁ t)) (ha₂ : ContDiff ℝ (↑(S + N) : ℕ∞) (a₂ t))
    (hj : SameJetAt (S + N) X₀ (a₁ t) (a₂ t)) :
    SameJetX S X₀ (fun X z => liftApply n' (Cc hh n') a₁ t X z)
      (fun X z => liftApply n' (Cc hh n') a₂ t X z) := by
  intro z
  by_cases hn : n' ≤ N
  · have hc : ∀ {a : ℝ → Vec 2 → ∀ i, h i}, ContDiff ℝ (↑(S + N) : ℕ∞) (a t) → ∀ v,
        ContDiff ℝ (↑S : ℕ∞) (fun X => liftApply n' (Cc hh n') a t X z v) := fun {a} ha v =>
      contDiff_pi.1 (boxSmooth_slice (CovFluxReg.liftApply_box Cc a t hh n' N S hz hb ha) z) v
    exact sameJet_pi (fun v => hc ha₁ v) (fun v => hc ha₂ v)
      (fun v => liftApply_sameJet_comp Cc a₁ a₂ t hh n' S N hn X₀ hb ha₁ ha₂ hj z v)
  · have hz' := hz n' (by omega)
    have e : ∀ a : ℝ → Vec 2 → ∀ i, h i, (fun X => liftApply n' (Cc hh n') a t X z) = fun _ => 0 := by
      intro a
      funext X
      funext v
      simp only [liftApply]
      refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun u _ => ?_
      simp [hz' m α t X z v u]
    rw [e a₁, e a₂]
    exact fun r I hr => rfl

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The flux-from-arrays step of the path-sum step: the objects of its statement.

The step takes the extra hypothesis `ActualFluxJointSmooth G` after `Input`. Its proof has five
parts, all about one ladder point `X` and one functional `ℓ`:

* the lifted edge coefficients of the fibre and of every `pathEdges` are `GoodField 1` at the
  cell times;
* the arrays scalarized on the ladder (applied operator and source);
* the pointwise (in `z`) flux identity, from the scalarized arrays and the edge coefficients
  (`hl_flux_pointwise_of_decomposed`, `hl_pointwise_core`);
* continuity in `z` of the path integrands (`hl_path_continuous_of_decomposed`,
  `hl_pathContinuous_core`);
* the cell mean splits over the finite path sum (`hl_cellMean_core`). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport CovFluxReg

/-- The window of cell times of the pulse `k`. -/
def HLWindow (D : OCData) {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)] {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (G : GenStage D hr Dm b j₀) (k : ℤ) : Set ℝ :=
  Set.Icc (D.slotStart G.level k / D.cellScaleSq G.level)
    ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)

/-- The Hilbert lift hypothesis of the path-sum step. -/
def HLHilbertLift {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (ρ : ℝ) (depth : ℕ) (k : ℤ) (hk : Odd k)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)) : Prop :=
  IsLiftSequence (familyLiftData D G.level k (nativeChain G.level k) ρ
      (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
    Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
    ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N depth
    (CcT k)

/-- The lifts of the scalar path families of all lengths `1 ≤ h' ≤ g + 1` on the ladder. -/
def HLPathLifts {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (ρ : ℝ) (k : ℤ) (hk : Odd k)
    (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k)) (g : ℕ)
    (Cπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)) : Prop :=
  ∀ h' : ℕ, 1 ≤ h' → h' ≤ g + 1 → ∀ π : StagePath G h',
    IsLiftSequenceOn (ladderOmega D b j₀ G.level k (nativeChain G.level k) ρ)
      (familyLiftData D G.level k (nativeChain G.level k) ρ
        (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩))
      Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
      Mn.N h' (Cπ h' π)

/-- The scalar input field of the path `π`: the functional `ℓ` of the composed map applied to the
Hilbert field at the source, in the entry `0`. -/
def hlIn {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (G : GenStage D hr Dm b j₀) {h : ℕ}
    (π : StagePath G h) {r : ℕ} (ℓ : hr r →L[ℝ] ℝ)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) : ℝ → Vec 2 → Fin (h + 1) → ℝ :=
  fun s' X' => by
    classical
    exact Pi.single (0 : Fin (h + 1))
      (if hπ : π.src ∈ G.comps then
        ℓ (rootPathMap hr π.src.root π.mapList r (a s' X' ⟨π.src, hπ⟩)) else 0)

/-- The slow flux of the scalar path family of `π`, at the last entry, for the input of `ℓ`. -/
def hlPathFlux {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (G : GenStage D hr Dm b j₀) (ρ : ℝ) (k : ℤ) (hk : Odd k)
    (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k)) (g : ℕ)
    (Cπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ))
    (π : StagePath G (g + 1)) {r : ℕ} (ℓ : hr r →L[ℝ] ℝ)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (n : ℕ) (τ : ℝ) (X z : Vec 2) (j : Fin 2) :
    ℝ :=
  liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
    (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩)) (Cπ (g + 1) π) (hlIn G π ℓ a)
    (g + 1) n τ X z j (Fin.last (g + 1))

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The jet-locality step, the partial derivatives of a lifted field**.

For lifted fields `Φ₁, Φ₂` with equal `X`-jets of order `r + 1` at `X₀` (for every `z`), the slow
partials `∂_{X_j}Φ_i` have equal `X`-jets of order `r` (`slowPartial_sameJetX`); for box smooth
`Φ_i` with equal `X`-jets of order `r` the fast partials `∂_{z_j}Φ_i` have equal `X`-jets of order
`r` (`fastPartial_sameJetX`: the slow word and the fast derivative interchange,
`orderedDerivative_slow_fast_jet`).

If `Φ` is independent of `z` the fast partial is `0`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slowPartial_sameJetX {r : ℕ} {X₀ : Vec 2} {Φ₁ Φ₂ : Vec 2 → Vec 2 → E}
    (h : SameJetX (r + 1) X₀ Φ₁ Φ₂) (j : Fin 2) :
    SameJetX r X₀ (slowPartial j Φ₁) (slowPartial j Φ₂) := fun z =>
  (sameJet_succ_iff.1 (h z)).2 j

theorem fastPartial_sameJetX {r : ℕ} {X₀ : Vec 2} {Φ₁ Φ₂ : Vec 2 → Vec 2 → E}
    (h₁ : IsBoxSmooth r 1 Φ₁) (h₂ : IsBoxSmooth r 1 Φ₂) (h : SameJetX r X₀ Φ₁ Φ₂) (j : Fin 2) :
    SameJetX r X₀ (fastPartial j Φ₁) (fastPartial j Φ₂) := by
  intro z ρ I hρ
  have key : ∀ {Φ : Vec 2 → Vec 2 → E}, IsBoxSmooth r 1 Φ →
      orderedDerivative I (fun Y => fastPartial j Φ Y z) X₀ =
        iteratedFDeriv ℝ 1 (fun y => orderedDerivative I (fun Y => Φ Y y) X₀) z
          (fun _ => basisVec j) := by
    intro Φ hΦ
    have hΦ' : IsBoxSmooth ρ 1 Φ := hΦ.mono hρ le_rfl
    have hc : ContDiff ℝ (↑ρ : ℕ∞) (fun Y => iteratedFDeriv ℝ 1 (Φ Y) z) :=
      (hΦ'.2.1 1 le_rfl z)
    have e : (fun Y => fastPartial j Φ Y z) = fun Y =>
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Vec 2) E (fun _ => basisVec j))
          (iteratedFDeriv ℝ 1 (Φ Y) z) := by
      funext Y
      simp [fastPartial, iteratedFDeriv_one_apply]
    rw [e, AVRegularity.orderedDerivative_clm_comp _ I hc]
    beta_reduce
    rw [← AVRegularity.CycleComparison.Lift.orderedDerivative_slow_fast_jet ρ 1 Φ I hΦ' X₀ z]
    rfl
  rw [key h₁, key h₂]
  have : (fun y => orderedDerivative I (fun Y => Φ₁ Y y) X₀) =
      fun y => orderedDerivative I (fun Y => Φ₂ Y y) X₀ := funext fun y => h y ρ I hρ
  rw [this]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! A sub-step of the Hilbert flux from arrays: the lifted edge coefficients of the fibre
and of every path family are good fields of order `1` at the cell times, from
`ActualFluxJointSmooth G`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLTools
open CovarianceTransport CovFluxReg

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLTools

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport CovFluxReg

/-- The cell time window maps into the pulse window. -/
theorem hl_window_mem {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ}
    {b : ℝ} {j₀ : ℕ} (G : GenStage D hr Dm b j₀) (k : ℤ) (hc : 0 < D.cellScaleSq G.level)
    {τ : ℝ} (hτ : τ ∈ HLWindow D G k) :
    D.cellScaleSq G.level * τ ∈ ocPulseWindow D.α D.q D.Λ G.level k := by
  obtain ⟨h1, h2⟩ := hτ
  rw [div_le_iff₀ hc] at h1
  rw [le_div_iff₀ hc] at h2
  exact ⟨by simpa [OCData.slotStart, mul_comm] using h1, by simpa [mul_comm] using h2⟩

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! A sub-step of the Hilbert flux from arrays: the cell mean splits over the finite
path sum, from the pointwise identity and the continuity of the path integrands. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport CovFluxReg

/-- The cell mean of a product-valued continuous field is read coordinatewise. -/
theorem hl_mean_eval {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] [∀ i, CompleteSpace (h i)] {f : Vec 2 → ∀ i, h i}
    (hf : Continuous f) (i : ι) :
    fieldCellMean f i = fieldCellMean (fun z => f z i) :=
  (fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) i) hf).symm

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! Sub-step (2) of the Hilbert flux from arrays: the arrays scalarized. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport CovFluxReg

section PathApply
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- A path of at least one edge has its source among the components. -/
theorem hl_src_mem {G : GenStage D hr Dm b j₀} {g : ℕ} (π : StagePath G (g + 1)) : π.src ∈ G.comps := by
  simp [StagePath.src]

end PathApply

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end

section
section
/-! The first-source-flux step: the named steps of the physical flux of the first source and the
assembly `firstSourceIdentity_of_steps` from them.

The identity of `G'` out of the root `v` with provenance `letter m diag []` is unique (the root-bookkeeping step).
Its physical coefficient is the glue over the pieces `p` of `G'` (weights `ϖ_p`) of the Piola
transport (`transportedCoeff`) of the arrays `fluxCoeff (firstSourceFlux …) d I 0` (the
normalization `lam` is cancelled by the readout weight, the root-bookkeeping step). Step 1 is that bookkeeping.
Step 2 says that one piece, at a time of nonzero weight, is `-Q_p 𝒟`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The label array of the first source of the piece `p` of `G'` at the time `t` and the point `x`:
`fluxCoeff (firstSourceFlux …) d I 0` at the recentred actual context of `p` (recentred at
`Y = Φ_p(t,·)⁻¹ x`) and the fast variable `ε_{m-1}⁻¹ Y`; zero when that context is not admissible
(the formula of the flux of the first-source identity, `IsActualSuccessor`). -/
def fsPieceArray (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (p : OddSlot) (t : ℝ)
    (x : Vec 2) : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 :=
  fun d I =>
    if IsAdmissibleChain D b j₀ G'.level p.1
        ((G'.actual p).1.recenter D (((G'.fam.piece p).material t).symm x))
    then fluxCoeff (firstSourceFlux D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level)
        Mn.N Mn.p Mn.anchor Cc0 t ((G'.actual p).1.recenter D (((G'.fam.piece p).material t).symm x))
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)) d I 0
    else 0

/-- The physical flux of the first source through the piece `p`: the Piola transport
(`transportedCoeff`, order `N + 1 + 4p`) of `fsPieceArray`, contracted with the ordered derivatives
of `g` at `x` (the shape of `constituentPhysical` for the identity map). -/
def fsPiecePhys (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (p : OddSlot)
    (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => hr v.1.root)).symm
    (fun k : Fin 2 => ∑ d ∈ Finset.Icc 2 Dm, ∑ A : DerivativeWord2 (d - 1),
      transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
        (Mn.N + 1 + 4 * Mn.p) (fsPieceArray Mn G G' Cc0 p t x) (d - 1) A x k •
        orderedDerivative A (fun y => g t y v) x)

/-- The hypotheses on the field of the first-source-flux step: class `C^K`, `K ≥ N + Dm + 4p`, periodic, on the
window. -/
def FSField (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (K : ℕ) (ta tb : ℝ)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) : Prop :=
  Mn.N + Dm + 4 * Mn.p ≤ K ∧ ∀ v, ∀ t ∈ Set.Icc ta tb,
    ContDiff ℝ (K : ℕ) (fun x => g t x v) ∧ IsZ2Periodic (fun x => g t x v)

/-- **Step 1 (bookkeeping, from the root-bookkeeping step).** The diagonal readout is the glue over the pieces of
`G'` of the physical flux of the first source: the only first-source identity out of the root `v`
into a child of `v` is `letterDiag [] v` (provenance `letter m diag []`, unit total weight
`E^{η₀·1}·lam = 1`), its flux is the formula of `IsActualSuccessor` (the factor
`lam (κ ε^{d-2})⁻¹` cancels the readout weight and `ν e^{d-2}` of `dimFlux`), and orders above its
`maxOrder = N + 1 + 4p ≤ Dm` carry the zero array. -/
def FirstSourceReadoutStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (v : CompIn G.comps) (t : ℝ) (x : Vec 2),
    diagReadout G G' G.level (D.eps (G.level - 1)) Mn.η0 g v t x =
      ∑ᶠ p : OddSlot, G'.fam.weight p t • fsPiecePhys Mn G G' W.Cc0 g v p t x

/-- **Step 2 (one piece is `-Q_p 𝒟`).** For a piece of nonzero weight at a time of the window
(so `t` is in its output window and every active finer slot is scheduled in it), the Piola
transport of the first-source arrays of the piece is `-Q_p 𝒟 g`: the Piola-transport step (`piecePiolaFiniteOrder`)
and `arrOp_eq_sum_fluxCoeff`/`firstSourceFlux_applyArr` turn it into the Eulerian operator
`K · firstSourceFlux`; the context strain at the actual context is `D𝐛_{m-1}`
(`context_strain_physical`, `m - 1 ≥ 1`); `diagFluxCtx = diagFluxPhys` at the actual context
(`hilbertLiftGradeZero` on each component, the appended children as in the transfer step); the `C^K` field is
handled as in the finer-output and transfer steps. -/
def FirstSourcePieceStatement : Prop :=
  RootSourceBookkeepingStatement → PiecePiolaFiniteOrderStatement →
    HilbertLiftGradeZeroStatement →
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (K : ℕ) (ta tb : ℝ)
      (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root), FSField Mn G K ta tb g →
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc ta tb, ∀ x : Vec 2, ∀ p : OddSlot,
      G'.fam.weight p t ≠ 0 →
      fsPiecePhys Mn G G' W.Cc0 g v p t x =
        -covTemporalAt Mn G G.level Mn.N Mn.p CcT g v t x

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The weights of a natural stage add to one at every time. -/
theorem fs_weight_finsum {M : ℕ} {G' : GenStage D hr Dm b j₀} (hnat : G'.IsNatural M) (t : ℝ) :
    ∑ᶠ p : OddSlot, G'.fam.weight p t = 1 := by
  have hτ := Uniqueness.ocTau_pos_of_natural hnat
  simp_rw [hnat.2.1]
  exact WeakEntryProofs.ocCutoff_finsum_one _ _ _ _ hτ t

/-- **The first-source-flux step, assembled from the two named steps.** -/
theorem firstSourceIdentity_of_steps (S1 : FirstSourceReadoutStatement)
    (S2 : FirstSourcePieceStatement) :
    RootSourceBookkeepingStatement → PiecePiolaFiniteOrderStatement →
      HilbertLiftGradeZeroStatement → FirstSourceIdentityStatement := by
  intro h1 h2 h5 hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin K hK ta tb g hg v t ht x
  obtain ⟨W⟩ := splitWitness_nonempty hin.successor
  rw [S1 P Mn G G' depth CcT hin W g v t x]
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  have key : ∀ p : OddSlot, G'.fam.weight p t • fsPiecePhys Mn G G' W.Cc0 g v p t x =
      G'.fam.weight p t • (-covTemporalAt Mn G G.level Mn.N Mn.p CcT g v t x) := by
    intro p
    by_cases hp : G'.fam.weight p t = 0
    · simp [hp]
    · rw [S2 h1 h2 h5 P Mn G G' depth CcT hin W K ta tb g ⟨hK, hg⟩ v t ht x p hp]
  rw [finsum_congr key, ← finsum_smul, fs_weight_finsum hnat, one_smul]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, step 1, part A: the first-source identity out of a root `v` is unique.
From the root-bookkeeping step (`rootSourceBookkeeping`): the identity of `G'` with provenance `letter m diag []`
from a component `u'` of `G` into a child of `v` is the identity `letterDiag [] v`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- A source with the provenance of the first source is `letterDiag t w`. -/
theorem fs_isDiag_cases {G : GenStage D hr Dm b j₀} (m : ℕ) (s : SuccSource G)
    (h : s.prov m = Prov.letter m WordLetter.diag []) :
    ∃ (t : List WordLetter) (w : CompIn G.comps), s = SuccSource.letterDiag t w := by
  cases s with
  | letterDiag t w => exact ⟨t, w, rfl⟩
  | copyDir t v u γ => simp [SuccSource.prov] at h
  | copyQuad t h' π => simp [SuccSource.prov] at h
  | letterMean t n h' π => simp [SuccSource.prov] at h
  | letterCov t n h' a a' π => simp [SuccSource.prov] at h

/-- The first-source identity out of `v`: existence, weight, and uniqueness. -/
theorem fs_diag_data {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀} {depth : ℕ}
    {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : SplitInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G') (v : CompIn G.comps) :
    ∃ (v1 u1 : CompIn G'.comps) (γ0 : G'.fam.Γ v1 u1), u1.1 = v.1 ∧
      compParent G.level v1.1 = v.1 ∧
      G'.prov v1 u1 γ0 = Prov.letter G.level WordLetter.diag [] ∧
      D.eps (G.level - 1) ^ (Mn.η0 * ((compWord G.level v1.1).length : ℝ)) *
        (W.e v1 u1 γ0).1.lam G.level Mn.η0 = 1 ∧
      ∀ (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'), u'.1 ∈ G.comps →
        compParent G.level v'.1 = v.1 →
        G'.prov v' u' γ' = Prov.letter G.level WordLetter.diag [] →
        v' = v1 ∧ u' = u1 ∧ (W.e v' u' γ').1 = (W.e v1 u1 γ0).1 := by
  have bk := rootSourceBookkeeping P Mn G G' hin.stage hin.successor W
  have hdiagA : WordLetter.diag ∈ Mn.A := by
    obtain ⟨Dord, nMax, hMax, npad, hA, -⟩ := hin.range
    rw [hA]; simp [succAlphabet]
  have hval : (SuccSource.letterDiag ([] : List WordLetter) v).Valid Mn.A Mn.J := by
    refine ⟨by simp [SuccSource.word], ?_, trivial⟩
    intro l hl
    simp only [SuccSource.letter?, Option.some.injEq] at hl
    subst hl
    exact ⟨by simp [SuccSource.word], hdiagA⟩
  obtain ⟨v1, u1, γ0, he0, hu1⟩ := bk.2.2 _ hval rfl
  obtain ⟨hw0, hos0, hot0, hpar0, hcw0, hwt0, hdiag0⟩ := bk.2.1 v1 u1 γ0 hu1
  have hsrc0 : (W.e v1 u1 γ0).1.oldSrc = v.1 := by rw [he0]; rfl
  have hprov0 : G'.prov v1 u1 γ0 = Prov.letter G.level WordLetter.diag [] :=
    hdiag0.1 (by rw [he0]; trivial)
  refine ⟨v1, u1, γ0, ?_, ?_, hprov0, hwt0, ?_⟩
  · rw [← hos0, hsrc0]
  · rw [hpar0, he0]; rfl
  · intro v' u' γ' hu' hpar hprov
    obtain ⟨hw, hos, hot, hpar', hcw, hwt, hdiag⟩ := bk.2.1 v' u' γ' hu'
    have hD : (W.e v' u' γ').1.IsDiag := hdiag.2 hprov
    have hprovS := (rsb_isDiag_iff G.level _).1 hD
    obtain ⟨t, w, hs⟩ := fs_isDiag_cases G.level _ hprovS
    have hold : (W.e v' u' γ').1.oldTgt = v.1 := by rw [← hpar', hpar]
    have hwv : w = v := by
      apply Subtype.ext
      have : (W.e v' u' γ').1.oldTgt = w.1 := by rw [hs]; rfl
      rw [← this, hold]
    have ht : t = [] := by rw [← hw, hs]; rfl
    have hs' : (W.e v' u' γ').1 = (W.e v1 u1 γ0).1 := by rw [hs, he0, ht, hwv]
    refine ⟨?_, ?_, hs'⟩
    · apply Subtype.ext
      rw [← (W.e v' u' γ').2.2.2, ← (W.e v1 u1 γ0).2.2.2, hs']
    · apply Subtype.ext
      rw [← (W.e v' u' γ').2.2.1, ← (W.e v1 u1 γ0).2.2.1, hs']

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The inner sum of `rootDiagFlux` at one identity. -/
def fsDiagInner (G G' : GenStage D hr Dm b j₀)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v1 u1 : CompIn G'.comps)
    (γ0 : G'.fam.Γ v1 u1) (hu : u1.1 ∈ G.comps) (t : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => hr v1.1.root) :=
  ∑ d : Finset.Icc 2 Dm,
    G'.physCoeff v1 u1 γ0 d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      orderedDerivative word (fun y => g t y ⟨u1.1, hu⟩) x)

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem fs_rootDiag_collapse {G G' : GenStage D hr Dm b j₀}
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v1 u1 : CompIn G'.comps) (γ0 : G'.fam.Γ v1 u1) (hu : u1.1 ∈ G.comps)
    (hprov0 : G'.prov v1 u1 γ0 = Prov.letter G.level WordLetter.diag [])
    (huniq : ∀ (u' : CompIn G'.comps) (γ' : G'.fam.Γ v1 u'), u'.1 ∈ G.comps →
        G'.prov v1 u' γ' = Prov.letter G.level WordLetter.diag [] →
        ∃ h : u' = u1, h ▸ γ' = γ0)
    (t : ℝ) (x : Vec 2) :
    rootDiagFlux G G' g v1 t x = fsDiagInner G G' g v1 u1 γ0 hu t x := by
  classical
  unfold rootDiagFlux
  rw [Finset.sum_eq_single u1]
  · simp only [hu, ↓reduceDIte]
    rw [Finset.sum_eq_single γ0]
    · simp only [hprov0, ↓reduceIte]; rfl
    · intro γ _ hne
      simp only [ite_eq_right_iff]
      intro hp
      obtain ⟨_, h⟩ := huniq u1 γ hu hp
      exact absurd h hne
    · simp
  · intro u' _ hne
    by_cases hu' : u'.1 ∈ G.comps
    · simp only [hu', ↓reduceDIte]
      apply Finset.sum_eq_zero
      intro γ _
      simp only [ite_eq_right_iff]
      intro hp
      obtain ⟨h, _⟩ := huniq u' γ hu' hp
      exact absurd h hne
    · simp only [hu', ↓reduceDIte]
  · simp

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem fs_rootDiag_zero {G G' : GenStage D hr Dm b j₀}
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v' : CompIn G'.comps)
    (hno : ∀ (u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'), u'.1 ∈ G.comps →
        G'.prov v' u' γ' ≠ Prov.letter G.level WordLetter.diag []) (t : ℝ) (x : Vec 2) :
    rootDiagFlux G G' g v' t x = 0 := by
  classical
  unfold rootDiagFlux
  apply Finset.sum_eq_zero
  intro u' _
  by_cases hu' : u'.1 ∈ G.comps
  · simp only [hu', ↓reduceDIte]
    apply Finset.sum_eq_zero
    intro γ _
    simp only [hno u' γ hu', ↓reduceIte]
  · simp only [hu', ↓reduceDIte]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The path-sum step at positive grades: the pointwise flux identity from the path decomposition.

For a stage with the setting `HLDecomp.Setting` and the decomposition `HLDecomp.Decomposed`:

* a coarse field is the sum of its coordinates in bases of the fibres (`HLIdx`, `hlCoord`, `hlVec`,
  `hl_field_decomp`), and the scalar input of a path is the corresponding sum in the entry `0`
  (`hlPathConst`, `hl_hlIn_decomp`);
* `hl_stage_flux_formula`: the slow flux of the lift of the fibre is the sum over the coordinates
  and the walks of the scalar `formX`; `hl_path_flux_last`: the slow flux of a path lift at its
  last entry is the sum over the coordinates of `formX` along the path;
* `hl_flux_pointwise_of_decomposed`: after a functional `ℓ`, the slow flux of the lift of the fibre
  at grade `g + 1` is the sum over the paths of `g + 1` edges of the path fluxes (the walks of the
  stage are its paths, `sum_stageWalk_eq`);
* `hl_path_continuous_of_decomposed`: the path fluxes are continuous in the fast variable. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

open CovarianceTransport CovFluxReg
open AVRegularity.Providers.PathDecomp

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The slow flux reads the coarse field at its own time only. -/
theorem hl_liftFluxX_field_congr {ι : Type*} [Fintype ι] {hs : ι → Type*}
    [∀ i, NormedAddCommGroup (hs i)] [∀ i, NormedSpace ℝ (hs i)] {Dm : ℕ}
    (Q : LiftOperatorData ι hs Dm) (Cc : ℕ → ℕ → LiftCoeff ι hs) {a a' : ℝ → Vec 2 → ∀ i, hs i}
    (hh n : ℕ) (t : ℝ) (ha : a t = a' t) :
    liftFluxX Q Cc a hh n t = liftFluxX Q Cc a' hh n t := by
  have e : ∀ k hh', liftApply k (Cc hh' k) a t = liftApply k (Cc hh' k) a' t := fun k hh' =>
    Uniqueness.liftApply_congr (fun _ _ _ => rfl) ha
  unfold liftFluxX
  simp only [e]

/-- The coordinates of a coarse field of a stage: a component and a basis index of its fibre. -/
abbrev HLIdx (G : GenStage D hr Dm b j₀) : Type :=
  Σ w : CompIn G.comps, Fin (Module.finrank ℝ (hr w.1.root))

/-- The coordinate functional of an index. -/
def hlCoordL (G : GenStage D hr Dm b j₀) (s : HLIdx G) : hr s.1.1.root →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (hr s.1.1.root)).coord s.2)

/-- The coordinate profile of a coarse field. -/
def hlCoord (G : GenStage D hr Dm b j₀) (a₀ : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (s : HLIdx G) : Vec 2 → ℝ :=
  fun Y => hlCoordL G s (a₀ Y s.1)

/-- The basis vector of an index. -/
def hlVec (G : GenStage D hr Dm b j₀) (s : HLIdx G) : hr s.1.1.root :=
  Module.finBasis ℝ (hr s.1.1.root) s.2

/-- A coarse field is the sum of its coordinates. -/
theorem hl_field_decomp (G : GenStage D hr Dm b j₀)
    (a₀ : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (Y : Vec 2) :
    a₀ Y = ∑ s : HLIdx G,
      (Pi.single s.1 (hlCoord G a₀ s Y • hlVec G s) : ∀ v : CompIn G.comps, hr v.1.root) := by
  funext w
  rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single w]
  · simp only [Pi.single_eq_same, hlCoord, hlCoordL, hlVec,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    exact ((Module.finBasis ℝ (hr w.1.root)).sum_repr (a₀ Y w)).symm
  · intro w' _ hw'
    exact Finset.sum_eq_zero fun i _ => Pi.single_eq_of_ne (Ne.symm hw') _
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem hl_coord_contDiff (G : GenStage D hr Dm b j₀)
    {a₀ : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀)
    (s : HLIdx G) : ContDiff ℝ (⊤ : ℕ∞) (hlCoord G a₀ s) :=
  (hlCoordL G s).contDiff.comp ((ContinuousLinearMap.proj (R := ℝ)
    (φ := fun v : CompIn G.comps => hr v.1.root) s.1).contDiff.comp ha)

/-- The constant of the coordinate `s` in the scalar input of the path `π`: the functional `ℓ` of
the composed map of `π` on the basis vector of `s` (zero unless `s` sits on the source of `π`). -/
def hlPathConst (G : GenStage D hr Dm b j₀) {h : ℕ} (π : StagePath G h) {r : ℕ}
    (ℓ : hr r →L[ℝ] ℝ) (s : HLIdx G) : ℝ := by
  classical
  exact if hπ : π.src ∈ G.comps then
    ℓ (rootPathMap hr π.src.root π.mapList r
      ((Pi.single s.1 (hlVec G s) : ∀ v : CompIn G.comps, hr v.1.root) ⟨π.src, hπ⟩)) else 0

/-- The scalar input of a path is the sum over the coordinates, in the entry `0`. -/
theorem hl_hlIn_decomp (G : GenStage D hr Dm b j₀) {h : ℕ} (π : StagePath G h) {r : ℕ}
    (ℓ : hr r →L[ℝ] ℝ) (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) :
    hlIn G π ℓ a t = fun Y => ∑ s : HLIdx G,
      (Pi.single (0 : Fin (h + 1)) (hlCoord G (a t) s Y • hlPathConst G π ℓ s) :
        Fin (h + 1) → ℝ) := by
  classical
  funext Y i
  rw [Finset.sum_apply]
  by_cases hπ : π.src ∈ G.comps
  · by_cases hi : i = 0
    · subst hi
      simp only [hlIn, hlPathConst, dite_eq_left hπ, Pi.single_eq_same]
      conv_lhs => rw [hl_field_decomp G (a t) Y]
      rw [Finset.sum_apply, map_sum, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Pi.single_smul, Pi.smul_apply, map_smul, map_smul]
    · simp [hlIn, Pi.single_eq_of_ne hi]
  · by_cases hi : i = 0
    · subst hi
      simp [hlIn, hlPathConst, hπ]
    · simp [hlIn, Pi.single_eq_of_ne hi]

/-- The constant of a coordinate on the source of the path, and off it. -/
theorem hl_pathConst_eq (G : GenStage D hr Dm b j₀) {h : ℕ} (π : StagePath G h) {r : ℕ}
    (ℓ : hr r →L[ℝ] ℝ) (s : HLIdx G) (hπ : π.src ∈ G.comps) :
    hlPathConst G π ℓ s = if π.src = s.1.1 then
      ℓ (rootPathMap hr s.1.1.root π.mapList r (hlVec G s)) else 0 := by
  classical
  obtain ⟨w, i⟩ := s
  by_cases hw : π.src = w.1
  · have hw' : (⟨π.src, hπ⟩ : CompIn G.comps) = w := Subtype.ext hw
    subst hw'
    simp [hlPathConst, hπ]
  · have hw' : (⟨π.src, hπ⟩ : CompIn G.comps) ≠ w := fun h => hw (congrArg Subtype.val h)
    simp [hlPathConst, hπ, hw, Pi.single_eq_of_ne hw']

omit [∀ r, FiniteDimensional ℝ (hr r)] in
open scoped Classical in
/-- A sum over the joined step sequences is a sum over the paths. -/
theorem hl_sum_stagePath {M : Type*} [AddCommMonoid M] (G : GenStage D hr Dm b j₀) (h : ℕ)
    [Fintype (StagePath G h)] (f : StagePath G h → M) :
    ∑ st : Fin h → (Σ (v' u' : CompIn G.comps), G.fam.Γ v' u'),
        (if hj : ∀ (i : ℕ) (hi : i + 1 < h), (st ⟨i + 1, hi⟩).2.1 = (st ⟨i, by omega⟩).1 then
          f ⟨st, hj⟩ else 0) = ∑ π : StagePath G h, f π := by
  symm
  refine Fintype.sum_of_injective (fun π : StagePath G h => π.step)
    (WeakEntryProofs.stagePath_step_injective G h) _ _ ?_ ?_
  · intro st hst
    split_ifs with hj
    · exact absurd ⟨⟨st, hj⟩, rfl⟩ hst
    · rfl
  · intro π
    rw [dite_eq_left π.joined]

omit [∀ r, FiniteDimensional ℝ (hr r)] in
open scoped Classical in
/-- A functional of a walk sum of the stage is a sum over the paths. -/
theorem hl_dual_walk_sum {G : GenStage D hr Dm b j₀} {c₀ lam : ℝ} {p : OddSlot}
    {c : StageCtx D b j₀ G.level p} {g : ℕ} [Fintype (StagePath G (g + 1))]
    (u v : CompIn G.comps) (ev : hr u.1.root) (ℓ : hr v.1.root →L[ℝ] ℝ)
    (Φ : (Fin (g + 1) → StepDat) → ℝ) :
    ℓ (∑ q : (stageFam G c₀ lam p c).Walk (g + 1) u v,
        Φ ((stageFam G c₀ lam p c).walkDat q) • (stageFam G c₀ lam p c).compMap q ev) =
      ∑ π : StagePath G (g + 1), if π.src = u.1 ∧ π.tgt = v.1 then
        Φ (pathDat G c₀ lam p c π) * ℓ (rootPathMap hr u.1.root π.mapList v.1.root ev) else 0 := by
  rw [sum_stageWalk_eq (by omega) u v ev Φ, ← hl_sum_stagePath, map_sum]
  refine Finset.sum_congr rfl fun st _ => ?_
  split_ifs with hj hc
  · rw [map_smul, smul_eq_mul]
  · exact map_zero _
  · exact map_zero _

section Formulas

variable {G : GenStage D hr Dm b j₀} {m : ℕ} {k : ℤ} {A : RealChain} {ρ : ℝ} {p : OddSlot}
  {c : StageCtx D b j₀ G.level p} {t₀ t₁ : ℝ} {h N sX sZ : ℕ}
  {CcT : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
  {Ccπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)}

/-- The context of the explicit formulas of the stage for the coordinate `s` of the coarse field
`a₀`, at the time `t`. -/
def hlStageCtx (G : GenStage D hr Dm b j₀) (m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) (h : ℕ)
    (Ccπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)) (t : ℝ)
    (a₀ : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (s : HLIdx G) : Ctx :=
  HLDecomp.hlCtx (familyLiftData (ι := CompIn G.comps) D m k A ρ (G.fam.fiber p c))
    (HLDecomp.hlTop G m ρ p c h Ccπ) t (hlCoord G a₀ s)

/-- **The slow flux of the lift of the fibre**: the sum over the coordinates of the coarse field
and over the walks of the stage of the scalar `formX`. -/
theorem hl_stage_flux_formula (H : HLDecomp.Setting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ)
    (Hd : HLDecomp.Decomposed G m ρ p c t₀ t₁ h CcT Ccπ) {g' : ℕ} (hg : g' ≤ h) {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a t)) (n : ℕ) (X z : Vec 2) (κ : Fin 2) :
    liftFluxX (familyLiftData D m k A ρ (G.fam.fiber p c)) CcT a g' n t X z κ =
      ∑ s : HLIdx G,
        ∑ q : WalkFrom (stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c) g' s.1,
          (hlStageCtx G m k A ρ p c h Ccπ t (a t) s).formX n g'
            ((stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c).walkDat q.2) κ X z •
          walkVec (stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c) (hlVec G s) q := by
  rw [Uniqueness.liftFluxX_congr _ CcT
    (cand (stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c) (HLDecomp.hlTop G m ρ p c h Ccπ))
    a g' n t fun hh'' hle n' m' α => Hd.stage hh'' (hle.trans hg) n' t ht m' α,
    hl_liftFluxX_field_congr _ _ (a' := fun _ Y => ∑ s : HLIdx G,
      (Pi.single s.1 (hlCoord G (a t) s Y • hlVec G s) : ∀ v : CompIn G.comps, hr v.1.root))
      g' n t (funext fun Y => hl_field_decomp G (a t) Y)]
  exact HLDecomp.hl_liftFluxX_cand_sum _ _ (hasFamFlux_fiber G m k A ρ p c) _ t
    (fun g cd k' m' α => H.goodT ht g cd k' m' α) (fun v u γ => H.goodDat v u γ t ht)
    Finset.univ (w := fun s : HLIdx G => s.1) (fun s => hlCoord G (a t) s)
    (fun s => hl_coord_contDiff G ha s) (e := fun s => hlVec G s) g' n X z κ

/-- The lift of a path family is, in the slow flux, the path-candidate array of its chain family,
and the scalar input is the sum over the coordinates. -/
theorem hl_path_flux_cand (Hd : HLDecomp.Decomposed G m ρ p c t₀ t₁ h CcT Ccπ) {L : ℕ}
    (hL : L ≤ h) (π : StagePath G L) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) {r : ℕ} (ℓ : hr r →L[ℝ] ℝ) (n : ℕ) :
    liftFluxX (familyLiftData D m k A ρ (pathEdges G π p c)) (Ccπ L π) (hlIn G π ℓ a) L n t =
      liftFluxX (familyLiftData D m k A ρ (pathEdges G π p c))
        (cand (chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c π))
          (HLDecomp.hlTop G m ρ p c h Ccπ))
        (fun _ Y => ∑ s : HLIdx G, (Pi.single (0 : Fin (L + 1))
          (hlCoord G (a t) s Y • hlPathConst G π ℓ s) : Fin (L + 1) → ℝ)) L n t := by
  rw [Uniqueness.liftFluxX_congr _ (Ccπ L π)
    (cand (chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c π))
      (HLDecomp.hlTop G m ρ p c h Ccπ))
    (hlIn G π ℓ a) L n t fun hh'' hle n' m' α => Hd.path L hL π hh'' hle n' t ht m' α]
  exact hl_liftFluxX_field_congr _ _ L n t (hl_hlIn_decomp G π ℓ a t)

/-- **The slow flux of a path lift at its last entry**: the sum over the coordinates of the scalar
`formX` along the path, times the constants of the path. -/
theorem hl_path_flux_last (H : HLDecomp.Setting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ)
    (Hd : HLDecomp.Decomposed G m ρ p c t₀ t₁ h CcT Ccπ) {L : ℕ} (hL : L ≤ h)
    (π : StagePath G L) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (ha : ContDiff ℝ (⊤ : ℕ∞) (a t))
    {r : ℕ} (ℓ : hr r →L[ℝ] ℝ) (n : ℕ) (X z : Vec 2) (κ : Fin 2) :
    liftFluxX (familyLiftData D m k A ρ (pathEdges G π p c)) (Ccπ L π) (hlIn G π ℓ a) L n t X z κ
        (Fin.last L) =
      ∑ s : HLIdx G, (hlStageCtx G m k A ρ p c h Ccπ t (a t) s).formX n L
        (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c π) κ X z * hlPathConst G π ℓ s := by
  rw [hl_path_flux_cand Hd hL π ht a ℓ n]
  exact HLDecomp.hl_chain_liftFluxX_last_sum _ _ (hasFamFlux_pathEdges G m k A ρ p c π) _ t
    (fun g cd k' m' α => H.goodT ht g cd k' m' α) (fun i => H.goodDat_path π i t ht)
    Finset.univ (fun s => hlCoord G (a t) s) (fun s => hl_coord_contDiff G ha s)
    (fun s => hlPathConst G π ℓ s) n X z κ

/-- **Continuity of the path fluxes in the fast variable.** -/
theorem hl_path_continuous_of_decomposed
    (H : HLDecomp.Setting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ)
    (Hd : HLDecomp.Decomposed G m ρ p c t₀ t₁ h CcT Ccπ) {L : ℕ} (hL : L ≤ h)
    (π : StagePath G L) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (ha : ContDiff ℝ (⊤ : ℕ∞) (a t))
    {r : ℕ} (ℓ : hr r →L[ℝ] ℝ) (n : ℕ) (X : Vec 2) (κ : Fin 2) :
    Continuous fun z => liftFluxX (familyLiftData D m k A ρ (pathEdges G π p c)) (Ccπ L π)
      (hlIn G π ℓ a) L n t X z κ := by
  have hT := fun g (cd : Fin g → StepDat) k' m' (α : DerivativeWord2 m') =>
    H.goodT ht g cd k' m' α
  have hdat : ∀ v u (γ : (chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c π)).Γ v u),
      GoodDat (N + 1 + Dm) t
        ((chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c π)).dat v u γ) :=
    fun v u γ => H.goodDat_path π _ t ht
  have e : (fun z => liftFluxX (familyLiftData D m k A ρ (pathEdges G π p c)) (Ccπ L π)
      (hlIn G π ℓ a) L n t X z κ) = fun z => ∑ s : HLIdx G,
        ∑ q : WalkFrom (chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c π)) L
            (0 : Fin (L + 1)),
          (HLDecomp.hlCtx (familyLiftData D m k A ρ (pathEdges G π p c))
            (HLDecomp.hlTop G m ρ p c h Ccπ) t (hlCoord G (a t) s)).formX n L
            ((chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c π)).walkDat q.2)
              κ X z •
          walkVec (chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c π))
            (hlPathConst G π ℓ s) q := by
    funext z
    rw [hl_path_flux_cand Hd hL π ht a ℓ n]
    exact HLDecomp.hl_liftFluxX_cand_sum _ _ (hasFamFlux_pathEdges G m k A ρ p c π) _ t hT hdat
      Finset.univ (w := fun _ : HLIdx G => (0 : Fin (L + 1))) (fun s => hlCoord G (a t) s)
      (fun s => hl_coord_contDiff G ha s) (e := fun s => hlPathConst G π ℓ s) L n X z κ
  rw [e]
  exact HLDecomp.hl_continuous_cand_sum _ _ _ t hT hdat (H.metric t ht) (H.drift t ht)
    Finset.univ (fun _ : HLIdx G => (0 : Fin (L + 1))) (fun s => hlCoord G (a t) s)
    (fun s => hl_coord_contDiff G ha s) (fun s => hlPathConst G π ℓ s) L n X κ

open scoped Classical in
/-- **The pointwise flux identity from the decomposition.** After a functional `ℓ` on the fibre of
`v`, the slow flux of the lift of the fibre at the grade `g + 1` is the sum over the paths of
`g + 1` edges into `v` of the slow fluxes of the path lifts at their last entries. -/
theorem hl_flux_pointwise_of_decomposed
    (H : HLDecomp.Setting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ)
    (Hd : HLDecomp.Decomposed G m ρ p c t₀ t₁ h CcT Ccπ) {g : ℕ} (hg : g + 1 ≤ h) {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a t)) (n : ℕ) (X z : Vec 2) (κ : Fin 2) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) :
    ℓ (liftFluxX (familyLiftData D m k A ρ (G.fam.fiber p c)) CcT a (g + 1) n t X z κ v) =
      ∑ᶠ π : StagePath G (g + 1), if π.tgt = v.1 ∧ π.src ∈ G.comps then
        liftFluxX (familyLiftData D m k A ρ (pathEdges G π p c)) (Ccπ (g + 1) π) (hlIn G π ℓ a)
          (g + 1) n t X z κ (Fin.last (g + 1))
      else 0 := by
  have : Fintype (StagePath G (g + 1)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, hl_stage_flux_formula H Hd hg ht a ha n X z κ]
  have h1 := HLDecomp.hl_dual_sum_walkVec
    (stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c) Finset.univ
    (fun s : HLIdx G => s.1) (fun s => hlVec G s)
    (fun s q => (hlStageCtx G m k A ρ p c h Ccπ t (a t) s).formX n (g + 1)
      ((stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c).walkDat q.2) κ X z) v ℓ
  refine h1.trans ?_
  have h2 : ∀ s : HLIdx G, ℓ (∑ q : (stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c).Walk
        (g + 1) s.1 v,
        (hlStageCtx G m k A ρ p c h Ccπ t (a t) s).formX n (g + 1)
          ((stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c).walkDat q) κ X z •
          (stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c).compMap q (hlVec G s)) =
      ∑ π : StagePath G (g + 1), if π.src = s.1.1 ∧ π.tgt = v.1 then
        (hlStageCtx G m k A ρ p c h Ccπ t (a t) s).formX n (g + 1)
          (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c π) κ X z *
          ℓ (rootPathMap hr s.1.1.root π.mapList v.1.root (hlVec G s)) else 0 := fun s =>
    hl_dual_walk_sum s.1 v (hlVec G s) ℓ
      (fun cd => (hlStageCtx G m k A ρ p c h Ccπ t (a t) s).formX n (g + 1) cd κ X z)
  refine (Finset.sum_congr rfl fun s _ => h2 s).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  have hπ : π.src ∈ G.comps := hl_src_mem π
  by_cases htg : π.tgt = v.1
  · rw [ite_eq_left ⟨htg, hπ⟩, hl_path_flux_last H Hd hg π ht a ha ℓ n X z κ]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hl_pathConst_eq G π ℓ s hπ]
    by_cases hs : π.src = s.1.1
    · rw [ite_eq_left ⟨hs, htg⟩, ite_eq_left hs]
    · rw [ite_eq_right (fun hc => hs hc.1), ite_eq_right hs, mul_zero]
  · rw [ite_eq_right (fun hc => htg hc.1)]
    exact Finset.sum_eq_zero fun s _ => ite_eq_right (fun hc => htg hc.2)

end Formulas

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **Source mean, Right: the pointwise reading of `ℓ (𝐄^flux P_p g)_j`.**

The active pulses `rightPulses` (odd, nonzero cutoff), the terms `rightTerm` of the dressed
expansion and their sum `rightU`. `rightU_eq`: `ℓ` of the `j`-th component of the mean flux of
`P_p g` is `rightU` (pulse-reading and linearity steps, and `ℓ ∘ C_π` commuting with `P_p`). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The active pulses at time `t`: odd with nonzero cutoff. -/
def rightPulses (D : OCData) (m : ℕ) (t : ℝ) : Finset ℤ :=
  (ocObsPulses D.α D.q D.Λ m t t).filter fun k => Odd k ∧ ocCutoff D.α D.q D.Λ m k t ≠ 0

open scoped Classical in
/-- The term of the expansion for the pulse `k`, grade `r`, path `π` and power `a'` of the
inner covariance operator, at the Eulerian point `y` and component `j`. -/
def rightTerm (Mn : SuccMenu) {P : ProvParams} {G G' : GenStage D hr Dm b j₀}
    (W : SplitWitness P Mn G G') (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (j : Fin 2) (k : ℤ) (r n : ℕ)
    (π : StagePath G r) (a' : ℕ) (y : Vec 2) : ℝ :=
  if hπ : π.tgt = v.1 ∧ π.src ∈ G.comps then
    pathJ Mn G π (W.Cc (SuccSource.copyQuad [] r π)) n k t
      ((SuccSource.covAt D G.level Mn.anchor t)^[a'] (rightField g v ℓ π hπ.2)) y j
  else 0

open scoped Classical in
/-- `ℓ` of the `j`-th component of the mean flux of `P_p g`, as a sum over the active pulses. -/
def rightU (Mn : SuccMenu) {P : ProvParams} {G G' : GenStage D hr Dm b j₀}
    (W : SplitWitness P Mn G G') (depth : ℕ)
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (j : Fin 2) (y : Vec 2) : ℝ :=
  ∑ k ∈ rightPulses D G.level t, ocCutoff D.α D.q D.Λ G.level k t *
    ∑ r ∈ Finset.Icc 1 depth, ∑ n ∈ Finset.Icc 2 (Mn.N + Dm),
      ∑ᶠ π : StagePath G r, ∑ a' ∈ Finset.range (Mn.p + 1),
        ((a'.factorial : ℝ)⁻¹) * rightTerm Mn W g v ℓ t j k r n π a' y

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **Source mean, Right: the pointwise identity `rightU_eq`.** -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The field of a path in the menu is `P_p` of the field of the path. -/
theorem right_field_covPolyP (Mn : SuccMenu) {G : GenStage D hr Dm b j₀}
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (hg : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => g y v))
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) {r : ℕ} (π : StagePath G r)
    (hπ : π.src ∈ G.comps) :
    (fun z => ℓ (rootPathMap hr π.src.root π.mapList v.1.root
      (menuCovPRep Mn D G.level Mn.p (fun _ => g) t z ⟨π.src, hπ⟩))) =
    covPolyP (menuCovPrimitive D Mn G.level t) Mn.p (rightField g v ℓ π hπ) := by
  funext z
  have := covProj_covPolyP (menuCovPrimitive D Mn G.level t)
    (ℓ.comp (rootPathMap hr π.src.root π.mapList v.1.root)) Mn.p
    (f := fun y' => g y' ⟨π.src, hπ⟩)
    ((hg _).of_le (by exact_mod_cast le_top)) z
  exact this

open scoped Classical in
/-- **Pointwise reading**: `ℓ` of the `j`-th component of the mean flux of `P_p g` is `rightU`. -/
theorem rightU_eq (h1 : RightPulseReadStatement) (h3 : RightPathLinearStatement)
    (H5 : HilbertLiftPathSumStatement) (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hin : SplitInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G')
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hg : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => g y v))
    (v : CompIn G.comps) (t : ℝ) (ℓ : hr v.1.root →L[ℝ] ℝ) (j : Fin 2) (y : Vec 2) :
    ℓ (menuMeanFluxE Mn G G.level Mn.N depth CcT (menuCovPRep Mn D G.level Mn.p (fun _ => g))
      t y v j) = rightU Mn W depth g v ℓ t j y := by
  unfold menuMeanFluxE menuGluedMeanFlux rightU rightPulses
  rw [Finset.sum_filter]
  simp only [Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hc : Odd k ∧ ocCutoff D.α D.q D.Λ G.level k t ≠ 0
  · obtain ⟨hk, hcut⟩ := hc
    rw [ite_eq_left (show Odd k ∧ ocCutoff D.α D.q D.Λ G.level k t ≠ 0 from ⟨hk, hcut⟩), Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr' => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hk, dite_true, Pi.smul_apply, map_smul, smul_eq_mul]
    congr 1
    rw [h1 H5 P Mn G G' depth CcT hin W g hg v t ℓ j k hk hcut r hr' n hn y]
    refine finsum_congr fun π => ?_
    by_cases hπ : π.tgt = v.1 ∧ π.src ∈ G.comps
    · simp only [hπ, and_self, dite_true, rightTerm]
      rw [right_field_covPolyP Mn g hg v ℓ t π hπ.2,
        h3 P Mn G G' depth CcT hin W t k hk hcut r hr' n hn π (rightField g v ℓ π hπ.2)
          ((ℓ.comp (rootPathMap hr π.src.root π.mapList v.1.root)).contDiff.comp
            (hg ⟨π.src, hπ.2⟩)) y]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    · simp [hπ, rightTerm]
  · rw [ite_eq_right hc]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun n _ => ?_
    by_cases hk : Odd k
    · have hcut : ocCutoff D.α D.q D.Λ G.level k t = 0 := by
        by_contra h; exact hc ⟨hk, h⟩
      simp [hk, hcut]
    · simp [hk]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The cascade supplies the hypotheses of the generic flux cancellation core (piece
`CascadeSplitInputStatement`). The stage certificates are `StageSuccessor.cascade_successor_inputs`;
the successor and the lift are binders of the quantifier prefix; the alphabet is `succAlphabet` by
definition of `succMenu`; the path bound is `cascade_path_length_le_of_generatedSeed`; the two
floors are the prefix floors; the only new input is the cascade flux order bound
(`cascadeFluxOrderBoundWeak`). The fields
`stream`, `history`, `start` are the stream-sequence binder of the
prefix, the last clause of `IsStageInvariant`, and the carrier start of the prefix with its second
constant raised to at least `1` (`cascadeSplitInput_carrierStart`). The fields `alpha_pos`, `q_gt`
 are the hypotheses `0 < α`, `1 < q`; the conjunct `2 ≤ Dord` of `range`
is `2 ≤ D_H` (`1 ≤ H`, `2 ≤ N` of the schedule). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual
open FluxCancellation CovarianceTransport

/-- The order schedule is monotone in the grade. -/
theorem cascadeSplitInput_succSchedD_mono (D₀ N p : ℕ) {g H : ℕ} (h : g ≤ H) :
    succSchedD D₀ N p g ≤ succSchedD D₀ N p H := by
  rw [succSchedD_eq, succSchedD_eq]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- The carrier start with its second constant raised to at least `1` gives the carrier start of
the prefix and the one at the constants `1, 1` (field `start` of `SplitInput`). -/
theorem cascadeSplitInput_carrierStart {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {bw CH Υ : ℝ} {j₀ : ℕ}
    (hCH : 1 ≤ CH) (hΥ : 0 < Υ) (h : IsCarrierStart α q Λ bw CH (max Υ 1) j₀) :
    IsCarrierStart α q Λ bw CH Υ j₀ ∧ IsCarrierStart α q Λ bw 1 1 j₀ := by
  have hA : ∀ k, 0 ≤ ocA α q Λ k := fun k => by
    unfold ocA
    exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  have hT : ∀ k, 0 ≤ ocTauPP α q Λ k := fun k => (Construction.Stream.ocTauPP_pos hΛ).le
  exact ⟨IsCarrierStart.mono hA hT le_rfl (le_max_left _ _) (zero_le_one.trans hCH) hΥ.le h,
    IsCarrierStart.mono hA hT hCH (le_max_right _ _) zero_le_one zero_le_one h⟩

end AVRegularity.Construction.Preservation.Residual
end
end
end
