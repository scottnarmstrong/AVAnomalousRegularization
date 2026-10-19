-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetSteps
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.FullX
import AVRegularity.CycleWords.CellTransitionLipschitz
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber

section
section
/-! The data of the reindexing, one term of the reindexing, and the comparison of an identity of the extended successor
with the identity of the root source with the same path: provenance, kernel, flux fields and
physical coefficient (up to the casts of the fibres) do not depend on the word of the source. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The ordered product of maps commutes with casts along equalities of roots. -/
theorem reindex_rootPathMap_cast {ru ru' rv rv' : ℕ} (hu : ru = ru') (hv : rv = rv')
    (maps : List (Σ (a c : ℕ), hr a →L[ℝ] hr c)) (z : hr ru) :
    cast (congrArg hr hv) (rootPathMap hr ru maps rv z) =
      rootPathMap hr ru' maps rv' (cast (congrArg hr hu) z) := by
  subst hu hv
  rfl

/-- The data used to compare an identity of the extended successor with the identity of the
root source with the same path: the source bijection of `IsActualSuccessor`, the births, and the
facts that make the lift coefficients unique on the windows where they are used. -/
structure ReindexInput (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) where
  act : IsActualSuccessor D P Mn G G'
  W : SplitWitness P Mn G G'
  hold : ∀ c ∈ G.comps, ∀ e ∈ c.births, G.level ≤ e.scale
  hE : 0 < D.eps (G.level - 1)
  hcs : 0 ≤ D.cellScaleSq G.level
  hτ : 0 < ocTau D.α D.q D.Λ G.level
  hWin : Uniqueness.SuccWindowData D b j₀ Mn G
  hΩ : ∀ k A, IsAdmissibleChain D b j₀ G.level k A →
    IsOpen (ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level)) ∧
      (0 : Vec 2) ∈ ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level)
  hΦ : ∀ (A : RealChain) (t : ℝ), ContinuousAt (A.famMapInv D t) 0 ∧ A.famMapInv D t 0 = 0

variable {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}

namespace ReindexInput

/-- Two identities whose sources differ only in the word have the same provenance. -/
theorem prov_eq (R : ReindexInput P Mn G G') {v' u' v'' u'' : CompIn G'.comps}
    {γ : G'.fam.Γ v' u'} {γ'' : G'.fam.Γ v'' u''} {w : List WordLetter}
    (hs : (R.W.e v' u' γ).1 = reindexWithWord w (R.W.e v'' u'' γ'').1) :
    G'.prov v' u' γ = G'.prov v'' u'' γ'' := by
  rw [(R.W.spec v' u' γ).1, (R.W.spec v'' u'' γ'').1, hs, reindexWithWord_prov]

/-- Two identities whose sources differ only in the word have the same kernel. -/
theorem kernelOf_eq (R : ReindexInput P Mn G G') (seedK freshK : ℕ → KernelSpec)
    {v' u' v'' u'' : CompIn G'.comps}
    {γ : G'.fam.Γ v' u'} {γ'' : G'.fam.Γ v'' u''} {w : List WordLetter}
    (hs : (R.W.e v' u' γ).1 = reindexWithWord w (R.W.e v'' u'' γ'').1) :
    G'.kernelOf P seedK freshK v' u' γ = G'.kernelOf P seedK freshK v'' u'' γ'' := by
  unfold GenStage.kernelOf
  rw [R.prov_eq hs]

/-- Two identities whose sources differ only in the word have the same flux fields. -/
theorem flux_eq (R : ReindexInput P Mn G G') {v' u' v'' u'' : CompIn G'.comps}
    {γ : G'.fam.Γ v' u'} {γ'' : G'.fam.Γ v'' u''} {w : List WordLetter}
    (hs : (R.W.e v' u' γ).1 = reindexWithWord w (R.W.e v'' u'' γ'').1) (p : OddSlot)
    (c : StageCtx D b j₀ G'.level p) (d : ℕ) (I : DerivativeWord2 (d - 1)) :
    G'.fam.flux p c v' u' γ d I = G'.fam.flux p c v'' u'' γ'' d I := by
  funext t X z
  exact reindex_flux_withWord P Mn R.hcs R.hτ R.hWin R.hΩ R.hΦ R.W v' u' v'' u'' γ γ'' w hs p c
    d I t X z

/-- **A copy has the same physical coefficient in every word**, up to the casts of the fibres. -/
theorem physCoeff_cast (R : ReindexInput P Mn G G') {v' u' v'' u'' : CompIn G'.comps}
    {γ : G'.fam.Γ v' u'} {γ'' : G'.fam.Γ v'' u''} {w : List WordLetter}
    (hs : (R.W.e v' u' γ).1 = reindexWithWord w (R.W.e v'' u'' γ'').1)
    (hu : u'.1.root = u''.1.root) (hv : v'.1.root = v''.1.root) (d : ℕ) (t : ℝ) (x : Vec 2)
    (z : PiLp 2 (fun _ : DerivativeWord2 (d - 1) => hr u'.1.root))
    (z'' : PiLp 2 (fun _ : DerivativeWord2 (d - 1) => hr u''.1.root))
    (hz : ∀ word, z'' word = cast (congrArg hr hu) (z word)) :
    cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) hv) (G'.physCoeff v' u' γ d t x z) =
      G'.physCoeff v'' u'' γ'' d t x z'' := by
  rw [reindex_physCoeff_eq, reindex_physCoeff_eq]
  refine reindexPhi_cast hu hv _ _ _ ?_ ?_ _ _ ?_ d t x z z'' hz
  · rw [R.act.2.2.2.2.1 v' u' γ |>.2, R.act.2.2.2.2.1 v'' u'' γ'' |>.2, R.prov_eq hs]
  · funext p d' I
    unfold ChartedFamily.dimFlux ChartedFamily.slowFlux
    rw [R.flux_eq hs p (G'.actual p) d' I]
  · intro y
    rw [(R.W.spec v' u' γ).2.1, (R.W.spec v'' u'' γ'').2.1, hs, reindexWithWord_maps]
    exact reindex_rootPathMap_cast hu hv _ y

end ReindexInput

open CovarianceTransport

omit [∀ r, InnerProductSpace ℝ (hr r)] in
theorem reindex_cast_sum {ι : Type*} {r r' : ℕ} (e : r = r') (s : Finset ι)
    (f : ι → PiLp 2 (fun _ : Fin 2 => hr r)) :
    cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) (∑ i ∈ s, f i) =
      ∑ i ∈ s, cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) (f i) := by
  subst e
  rfl

theorem reindex_cast_smul {r r' : ℕ} (e : r = r') (a : ℝ)
    (f : PiLp 2 (fun _ : Fin 2 => hr r)) :
    cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) (a • f) =
      a • cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) f := by
  subst e
  rfl

omit [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)] in
theorem reindex_cast_cast {r r' r'' : ℕ} (e : r = r') (e' : r' = r'')
    (f : PiLp 2 (fun _ : Fin 2 => hr r)) :
    cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e')
        (cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) f) =
      cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) (e.trans e')) f := by
  subst e e'
  rfl

open scoped Classical in
/-- **One term of the reindexing.** The term of the readout of the omitted flux for the identity `γ`
of `c → v'` and the term of the readout of the root flux for the identity `γ''` of `u' → v''`
with the same path (the sources differ in the word only) are the same element of the target
fibre. -/
theorem reindex_term_eq (R : ReindexInput P Mn G G') (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (t : ℝ) (x : Vec 2) (E η : ℝ) {v : Comp}
    {v' v'' c u' : CompIn G'.comps} {γ : G'.fam.Γ v' c} {γ'' : G'.fam.Γ v'' u'}
    (hs : (R.W.e v' c γ).1 = reindexWithWord (compWord G.level c.1) (R.W.e v'' u' γ'').1)
    (hE : 0 < E) (hlen : (compWord G.level v'.1).length =
      (compWord G.level c.1).length + (compWord G.level v''.1).length)
    (hu : c.1.root = u'.1.root) (hv' : v'.1.root = v.root) (hv'' : v''.1.root = v.root)
    (Yc : Vec 2 → hr c.1.root) :
    (E ^ (η * ((compWord G.level v'.1).length : ℝ))) •
      cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) hv')
        (∑ d : Finset.Icc 2 Dm, G'.physCoeff v' c γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          orderedDerivative word ((G'.kernelOf P seedK freshK v' c γ).applyClassical φ₀ t Yc) x)) =
    (E ^ (η * ((compWord G.level v''.1).length : ℝ))) •
      cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) hv'')
        (∑ d : Finset.Icc 2 Dm, (E ^ (η * ((compWord G.level c.1).length : ℝ))) •
          G'.physCoeff v'' u' γ'' d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            cast (congrArg hr hu)
              (orderedDerivative word ((G'.kernelOf P seedK freshK v'' u' γ'').applyClassical φ₀ t Yc) x))) := by
  have hv : v'.1.root = v''.1.root := hv'.trans hv''.symm
  rw [reindex_cast_sum hv', reindex_cast_sum hv'', Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [reindex_cast_smul hv'', smul_smul]
  have hw : E ^ (η * ((compWord G.level v'.1).length : ℝ)) =
      E ^ (η * ((compWord G.level v''.1).length : ℝ)) *
        E ^ (η * ((compWord G.level c.1).length : ℝ)) := by
    rw [hlen, Nat.cast_add, mul_add, Real.rpow_add hE, mul_comm]
  rw [hw]
  have hpc := R.physCoeff_cast hs hu hv d.1 t x
    (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      orderedDerivative word ((G'.kernelOf P seedK freshK v' c γ).applyClassical φ₀ t Yc) x)
    (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      cast (congrArg hr hu)
        (orderedDerivative word ((G'.kernelOf P seedK freshK v'' u' γ'').applyClassical φ₀ t Yc) x))
    (by intro word; simp [R.kernelOf_eq seedK freshK hs])
  have h2 : cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) hv')
      (G'.physCoeff v' c γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word ((G'.kernelOf P seedK freshK v' c γ).applyClassical φ₀ t Yc) x)) =
      cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) hv'')
        (G'.physCoeff v'' u' γ'' d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          cast (congrArg hr hu)
            (orderedDerivative word
              ((G'.kernelOf P seedK freshK v'' u' γ'').applyClassical φ₀ t Yc) x))) := by
    rw [← hpc]
    exact (reindex_cast_cast hv hv'' _).symm
  rw [h2]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The jet-locality step: calculus of equal jets**.

`SameJetAt r x f g` (equal ordered derivatives of the orders `≤ r` at `x`) is stable under
continuous linear maps, sums, bilinear products with a common `C^r` factor, and composition on the
right with a common `C^r` map. The basic step is `sameJet_succ_iff`: equal jets of order `r + 1`
are equal values and equal jets of order `r` of the `r`-fold directional derivatives
`y ↦ fderiv f y (basisVec i)`.

For `r = 0` this is equality of values. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem sameJet_zero_iff {x : Vec 2} {f g : Vec 2 → E} :
    SameJetAt 0 x f g ↔ f x = g x := by
  constructor
  · intro h
    have := h 0 (fun i => i.elim0) le_rfl
    simpa [orderedDerivative_zero] using this
  · intro h r I hr
    obtain rfl : r = 0 := by omega
    simpa [orderedDerivative_zero] using h

theorem orderedDerivative_cons' {r : ℕ} (i : Fin 2) (I : DerivativeWord2 r) (f : Vec 2 → E) :
    orderedDerivative (Fin.cons i I : DerivativeWord2 (r + 1)) f =
      orderedDerivative I (fun y => fderiv ℝ f y (basisVec i)) := by
  simp [orderedDerivative, List.ofFn_succ]

/-- The basic step: jets of order `r + 1` are values and jets of order `r` of the partials. -/
theorem sameJet_succ_iff {r : ℕ} {x : Vec 2} {f g : Vec 2 → E} :
    SameJetAt (r + 1) x f g ↔ f x = g x ∧ ∀ i : Fin 2,
      SameJetAt r x (fun y => fderiv ℝ f y (basisVec i)) (fun y => fderiv ℝ g y (basisVec i)) := by
  constructor
  · intro h
    refine ⟨sameJet_zero_iff.1 (fun r' I hr' => h r' I (by omega)), fun i ρ I hρ => ?_⟩
    have := h (ρ + 1) (Fin.cons i I) (by omega)
    rwa [orderedDerivative_cons', orderedDerivative_cons'] at this
  · rintro ⟨hv, hd⟩ r' I hr'
    cases r' with
    | zero => exact sameJet_zero_iff.2 hv 0 I le_rfl
    | succ ρ =>
      obtain ⟨i, J, rfl⟩ : ∃ i J, I = (Fin.cons i J : DerivativeWord2 (ρ + 1)) :=
        ⟨I 0, Fin.tail I, (Fin.cons_self_tail I).symm⟩
      rw [orderedDerivative_cons', orderedDerivative_cons']
      exact hd i ρ J (by omega)

theorem sameJet_mono {s s' : ℕ} (hs : s ≤ s') {x : Vec 2} {f g : Vec 2 → E}
    (h : SameJetAt s' x f g) : SameJetAt s x f g := fun r I hr => h r I (hr.trans hs)

/-- Continuous linear maps preserve equal jets. -/
theorem sameJet_clm (L : E →L[ℝ] F) {r : ℕ} {x : Vec 2} {f g : Vec 2 → E}
    (hf : ContDiff ℝ (↑r : ℕ∞) f) (hg : ContDiff ℝ (↑r : ℕ∞) g) (h : SameJetAt r x f g) :
    SameJetAt r x (fun y => L (f y)) (fun y => L (g y)) := by
  intro j I hj
  have hj' : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((r : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hj
  rw [AVRegularity.orderedDerivative_clm_comp L I (hf.of_le hj'),
    AVRegularity.orderedDerivative_clm_comp L I (hg.of_le hj')]
  beta_reduce
  rw [h j I hj]

/-- Finite sums preserve equal jets. -/
theorem sameJet_sum {κ : Type*} (S : Finset κ) {r : ℕ} {x : Vec 2} {f g : κ → Vec 2 → E}
    (hf : ∀ i ∈ S, ContDiff ℝ (↑r : ℕ∞) (f i)) (hg : ∀ i ∈ S, ContDiff ℝ (↑r : ℕ∞) (g i))
    (h : ∀ i ∈ S, SameJetAt r x (f i) (g i)) :
    SameJetAt r x (fun y => ∑ i ∈ S, f i y) (fun y => ∑ i ∈ S, g i y) := by
  intro j I hj
  have hj' : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((r : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hj
  have e1 := congrFun (AVRegularity.Providers.PathDecomp.orderedDerivative_clm_sum S
    (fun _ => ContinuousLinearMap.id ℝ E) I (β := f) fun i hi => (hf i hi).of_le hj') x
  have e2 := congrFun (AVRegularity.Providers.PathDecomp.orderedDerivative_clm_sum S
    (fun _ => ContinuousLinearMap.id ℝ E) I (β := g) fun i hi => (hg i hi).of_le hj') x
  simp only [ContinuousLinearMap.id_apply] at e1 e2
  rw [e1, e2]
  exact Finset.sum_congr rfl fun i hi => h i hi j I hj

theorem sameJet_add {r : ℕ} {x : Vec 2} {f₁ f₂ g₁ g₂ : Vec 2 → E}
    (hf₁ : ContDiff ℝ (↑r : ℕ∞) f₁) (hf₂ : ContDiff ℝ (↑r : ℕ∞) f₂)
    (hg₁ : ContDiff ℝ (↑r : ℕ∞) g₁) (hg₂ : ContDiff ℝ (↑r : ℕ∞) g₂)
    (hf : SameJetAt r x f₁ f₂) (hg : SameJetAt r x g₁ g₂) :
    SameJetAt r x (fun y => f₁ y + g₁ y) (fun y => f₂ y + g₂ y) := by
  intro j I hj
  have hj' : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((r : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hj
  rw [AVRegularity.orderedDerivative_add I (hf₁.of_le hj') (hg₁.of_le hj'),
    AVRegularity.orderedDerivative_add I (hf₂.of_le hj') (hg₂.of_le hj')]
  beta_reduce
  rw [hf j I hj, hg j I hj]

/-- Derivative of a bilinear expression. -/
theorem fderiv_bilin (B : E →L[ℝ] F →L[ℝ] G) {c : Vec 2 → E} {f : Vec 2 → F} {y : Vec 2}
    (hc : DifferentiableAt ℝ c y) (hf : DifferentiableAt ℝ f y) (v : Vec 2) :
    fderiv ℝ (fun y => B (c y) (f y)) y v =
      B (fderiv ℝ c y v) (f y) + B (c y) (fderiv ℝ f y v) := by
  have h1 : HasFDerivAt (fun y => B (c y)) (B.comp (fderiv ℝ c y)) y :=
    B.hasFDerivAt.comp y hc.hasFDerivAt
  have h2 := h1.clm_apply hf.hasFDerivAt
  rw [h2.fderiv]
  simp [add_comm]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end

section
section
/-! The source bijection of the reindexing: the identities of the extended successor into a
column `c = (u, 𝔰)` and the identities into its parent `u` correspond bijectively through the
sources, which differ in the word only; the word lengths add up. Then the readout of the omitted
flux of the extended family is the readout of the kernel flux out of the roots
(`reindex_readout_eq`), column by column. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Two finite sums are equal when the index sets correspond bijectively through a relation that
identifies the summands. -/
theorem reindex_sum_of_rel {ι κ M : Type*} [AddCommMonoid M] (s : Finset ι) (t : Finset κ)
    (f : ι → M) (g : κ → M) (rel : ι → κ → Prop)
    (hL : ∀ x ∈ s, ∃ y ∈ t, rel x y) (hR : ∀ y ∈ t, ∃ x ∈ s, rel x y)
    (hy : ∀ x ∈ s, ∀ y ∈ t, ∀ y' ∈ t, rel x y → rel x y' → y = y')
    (hx : ∀ x ∈ s, ∀ x' ∈ s, ∀ y ∈ t, rel x y → rel x' y → x = x')
    (hf : ∀ x ∈ s, ∀ y ∈ t, rel x y → f x = g y) : ∑ x ∈ s, f x = ∑ y ∈ t, g y := by
  classical
  choose i hi hrel using hL
  refine Finset.sum_bij i hi ?_ ?_ ?_
  · intro x hx' x' hx'' h
    exact hx x hx' x' hx'' (i x hx') (hi x hx') (hrel x hx') (h ▸ hrel x' hx'')
  · intro y hy'
    obtain ⟨x, hxs, hxy⟩ := hR y hy'
    exact ⟨x, hxs, hy x hxs _ (hi x hxs) y hy' (hrel x hxs) hxy⟩
  · intro x hx'
    exact hf x hx' _ (hi x hx') (hrel x hx')

variable {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}

namespace ReindexInput

theorem reindexWithWord_reindexWithWord {G : GenStage D hr Dm b j₀} (w w' : List WordLetter)
    (s : SuccSource G) : reindexWithWord w (reindexWithWord w' s) = reindexWithWord w s := by
  cases s <;> rfl

/-- The target of a valid source is a component of the extended stage. -/
theorem tgtComp_mem (R : ReindexInput P Mn G G') {s : SuccSource G} (hs : s.Valid Mn.A Mn.J) :
    s.tgtComp G.level ∈ G'.comps := by
  rw [R.act.2.2.1]
  have hT := rsb_oldTgt_mem s hs
  unfold SuccSource.tgtComp succExtComps
  by_cases hn : s.newWord = []
  · rw [Finset.mem_union]
    left
    simpa [succComp, hn] using hT
  · rw [Finset.mem_union]
    right
    rw [Finset.mem_image]
    refine ⟨(s.oldTgt, s.newWord), Finset.mem_product.2 ⟨hT, ?_⟩, rfl⟩
    rw [reindex_newWord_eq] at hn ⊢
    cases hl : s.letter? with
    | none =>
      simp only [hl, Option.toList_none, List.append_nil] at hn ⊢
      rcases Finset.mem_insert.1 hs.1 with h | h
      · exact absurd h hn
      · exact h
    | some l =>
      obtain ⟨hlen, hlA⟩ := hs.2.1 l hl
      simpa using reindex_word_snoc_mem hs.1 hlen hlA

/-- The old source of a source of the extended stage is the parent of its source component, and
its word is the word of that component. -/
theorem src_facts (R : ReindexInput P Mn G G') (v' u' : CompIn G'.comps) (γ : G'.fam.Γ v' u') :
    (R.W.e v' u' γ).1.oldSrc = compParent G.level u'.1 ∧
      (R.W.e v' u' γ).1.word = compWord G.level u'.1 := by
  have hsrc := (R.W.e v' u' γ).2.2.1
  have hS := rsb_oldSrc_mem _ (R.W.e v' u' γ).2.1
  have h := Preservation.FullLift.parent_word_succComp R.act.1 _ (R.hold _ hS)
    (R.W.e v' u' γ).1.word
  have h' : succComp G.level (R.W.e v' u' γ).1.oldSrc (R.W.e v' u' γ).1.word = u'.1 := hsrc
  rw [h'] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- The old target of a source of the extended stage is the parent of its target component, and
the word of that component is the new word of the source. -/
theorem tgt_facts (R : ReindexInput P Mn G G') (v' u' : CompIn G'.comps) (γ : G'.fam.Γ v' u') :
    (R.W.e v' u' γ).1.oldTgt = compParent G.level v'.1 ∧
      (R.W.e v' u' γ).1.newWord = compWord G.level v'.1 := by
  have htgt := (R.W.e v' u' γ).2.2.2
  have hT := rsb_oldTgt_mem _ (R.W.e v' u' γ).2.1
  have h := Preservation.FullLift.parent_word_succComp R.act.1 _ (R.hold _ hT)
    (R.W.e v' u' γ).1.newWord
  have h' : succComp G.level (R.W.e v' u' γ).1.oldTgt (R.W.e v' u' γ).1.newWord = v'.1 := htgt
  rw [h'] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- Two identities into the same column with the same source are the same element of the sigma
type. -/
theorem sigma_ext (R : ReindexInput P Mn G G') {u : CompIn G'.comps} {v' w' : CompIn G'.comps}
    (γ : G'.fam.Γ v' u) (δ : G'.fam.Γ w' u) (h : (R.W.e v' u γ).1 = (R.W.e w' u δ).1) :
    (⟨v', γ⟩ : Σ v', G'.fam.Γ v' u) = ⟨w', δ⟩ := by
  have hv : v' = w' := Subtype.ext (by
    rw [← (R.W.e v' u γ).2.2.2, ← (R.W.e w' u δ).2.2.2, h])
  subst hv
  have : γ = δ := (R.W.e v' u).injective (Subtype.ext h)
  subst this
  rfl

/-- The relation between the identities into a column `c` and the identities into its parent `u'`:
the sources differ in the word only. -/
def rel (R : ReindexInput P Mn G G') (c u' : CompIn G'.comps)
    (x : Σ v', G'.fam.Γ v' c) (y : Σ v'', G'.fam.Γ v'' u') : Prop :=
  (R.W.e x.1 c x.2).1 = reindexWithWord (compWord G.level c.1) (R.W.e y.1 u' y.2).1

/-- The parent and the word of a component of the extended stage. -/
theorem col_facts (R : ReindexInput P Mn G G') (c : CompIn G'.comps) :
    compParent G.level c.1 ∈ G.comps ∧
      compWord G.level c.1 ∈ insert [] (wordsUpTo Mn.A (Mn.J + 1)) := by
  have hc : c.1 ∈ succExtComps G.level Mn.A Mn.J G.comps := R.act.2.2.1 ▸ c.2
  refine ⟨?_, Preservation.FullLift.readout_word_mem R.act.1 R.hold hc⟩
  rcases InitialValue.mem_succExtComps hc with h | ⟨v, hv, t, hvt⟩
  · rw [(InitialValue.compParent_eq_self R.act.1 (R.hold _ h)).1]
    exact h
  · rw [hvt, (Preservation.FullLift.parent_word_succComp R.act.1 v (R.hold _ hv) t).1]
    exact hv

theorem rel_forward (R : ReindexInput P Mn G G') (c u' : CompIn G'.comps)
    (hcu : u'.1 = compParent G.level c.1) (x : Σ v', G'.fam.Γ v' c) :
    ∃ y : Σ v'', G'.fam.Γ v'' u', R.rel c u' x y ∧
      compParent G.level y.1.1 = compParent G.level x.1.1 := by
  obtain ⟨v', γ⟩ := x
  set s := (R.W.e v' c γ).1 with hsdef
  have hsv : s.Valid Mn.A Mn.J := (R.W.e v' c γ).2.1
  obtain ⟨hsrc1, hsrc2⟩ := R.src_facts v' c γ
  obtain ⟨htgt1, htgt2⟩ := R.tgt_facts v' c γ
  have hs0 : (reindexWithWord [] s).Valid Mn.A Mn.J :=
    reindexWithWord_valid hsv (Finset.mem_insert_self _ _) (fun _ => by simp)
  have hsrc0 : (reindexWithWord [] s).srcComp G.level = u'.1 := by
    unfold SuccSource.srcComp
    rw [reindexWithWord_word, reindexWithWord_oldSrc, hsrc1, hcu]
    simp [succComp]
  have hmem := R.tgtComp_mem hs0
  refine ⟨⟨⟨_, hmem⟩, (R.W.e ⟨_, hmem⟩ u').symm ⟨reindexWithWord [] s, hs0, hsrc0, rfl⟩⟩, ?_, ?_⟩
  · show s = reindexWithWord (compWord G.level c.1) (((R.W.e _ u') ((R.W.e _ u').symm _)).1)
    rw [Equiv.apply_symm_apply]
    show s = reindexWithWord (compWord G.level c.1) (reindexWithWord [] s)
    rw [reindexWithWord_reindexWithWord, ← hsrc2, reindexWithWord_self]
  · have h0 := Preservation.FullLift.parent_word_succComp R.act.1 s.oldTgt
      (R.hold _ (rsb_oldTgt_mem s hsv)) (reindexWithWord [] s).newWord
    show compParent G.level ((reindexWithWord [] s).tgtComp G.level) = _
    unfold SuccSource.tgtComp
    rw [reindexWithWord_oldTgt] at *
    rw [h0.1, ← htgt1]

theorem rel_backward (R : ReindexInput P Mn G G') (c u' : CompIn G'.comps)
    (hcu : u'.1 = compParent G.level c.1) (hu : u'.1 ∈ G.comps)
    (hJ : (compWord G.level c.1).length ≤ Mn.J) (y : Σ v'', G'.fam.Γ v'' u') :
    ∃ x : Σ v', G'.fam.Γ v' c, R.rel c u' x y ∧
      compParent G.level x.1.1 = compParent G.level y.1.1 := by
  obtain ⟨v'', γ''⟩ := y
  set s0 := (R.W.e v'' u' γ'').1 with hs0def
  have hs0v : s0.Valid Mn.A Mn.J := (R.W.e v'' u' γ'').2.1
  have hs0src : s0.srcComp G.level = u'.1 := (R.W.e v'' u' γ'').2.2.1
  have hold0 : s0.word = [] := rsb_word_nil R.act.1 s0 (R.hold _ hu) hs0src
  have hold1 : s0.oldSrc = u'.1 := by
    have h : succComp G.level s0.oldSrc s0.word = u'.1 := hs0src
    rw [hold0] at h
    simpa [succComp] using h
  have hsv : (reindexWithWord (compWord G.level c.1) s0).Valid Mn.A Mn.J :=
    reindexWithWord_valid hs0v (R.col_facts c).2 (fun _ => hJ)
  have hsrc : (reindexWithWord (compWord G.level c.1) s0).srcComp G.level = c.1 := by
    unfold SuccSource.srcComp
    rw [reindexWithWord_word, reindexWithWord_oldSrc, hold1, hcu]
    exact Preservation.FullLift.succComp_parent_word G.level c.1
  have hmem := R.tgtComp_mem hsv
  refine ⟨⟨⟨_, hmem⟩, (R.W.e ⟨_, hmem⟩ c).symm ⟨reindexWithWord (compWord G.level c.1) s0, hsv, hsrc, rfl⟩⟩, ?_, ?_⟩
  · show ((R.W.e _ c) ((R.W.e _ c).symm _)).1 = _
    rw [Equiv.apply_symm_apply]
  · obtain ⟨htgt1, -⟩ := R.tgt_facts v'' u' γ''
    have h0 := Preservation.FullLift.parent_word_succComp R.act.1 s0.oldTgt
      (R.hold _ (rsb_oldTgt_mem s0 hs0v))
      (reindexWithWord (compWord G.level c.1) s0).newWord
    show compParent G.level ((reindexWithWord (compWord G.level c.1) s0).tgtComp G.level) = _
    unfold SuccSource.tgtComp
    rw [reindexWithWord_oldTgt]
    rw [h0.1, htgt1]

theorem rel_unique_y (R : ReindexInput P Mn G G') (c u' : CompIn G'.comps)
    (hu : u'.1 ∈ G.comps) (x : Σ v', G'.fam.Γ v' c) (y y' : Σ v'', G'.fam.Γ v'' u')
    (h : R.rel c u' x y) (h' : R.rel c u' x y') : y = y' := by
  have key : ∀ z : Σ v'', G'.fam.Γ v'' u', R.rel c u' x z →
      (R.W.e z.1 u' z.2).1 = reindexWithWord [] (R.W.e x.1 c x.2).1 := by
    intro z hz
    have hw : (R.W.e z.1 u' z.2).1.word = [] :=
      rsb_word_nil R.act.1 _ (R.hold _ hu) (R.W.e z.1 u' z.2).2.2.1
    have : reindexWithWord [] (R.W.e x.1 c x.2).1 = (R.W.e z.1 u' z.2).1 := by
      rw [hz, reindexWithWord_reindexWithWord, ← hw, reindexWithWord_self]
    exact this.symm
  exact R.sigma_ext y.2 y'.2 ((key y h).trans (key y' h').symm)

theorem rel_unique_x (R : ReindexInput P Mn G G') (c u' : CompIn G'.comps)
    (x x' : Σ v', G'.fam.Γ v' c) (y : Σ v'', G'.fam.Γ v'' u')
    (h : R.rel c u' x y) (h' : R.rel c u' x' y) : x = x' :=
  R.sigma_ext x.2 x'.2 (h.trans h'.symm)

theorem rel_weight (R : ReindexInput P Mn G G') (c u' : CompIn G'.comps)
    (hu : u'.1 ∈ G.comps) (x : Σ v', G'.fam.Γ v' c) (y : Σ v'', G'.fam.Γ v'' u')
    (h : R.rel c u' x y) :
    (compWord G.level x.1.1).length =
      (compWord G.level c.1).length + (compWord G.level y.1.1).length := by
  obtain ⟨-, hx2⟩ := R.tgt_facts x.1 c x.2
  obtain ⟨-, hy2⟩ := R.tgt_facts y.1 u' y.2
  have hw : (R.W.e y.1 u' y.2).1.word = [] :=
    rsb_word_nil R.act.1 _ (R.hold _ hu) (R.W.e y.1 u' y.2).2.2.1
  have e1 : (R.W.e x.1 c x.2).1.newWord = compWord G.level c.1 ++ (R.W.e y.1 u' y.2).1.letter?.toList := by
    rw [h, reindexWithWord_newWord]
  have e2 : (R.W.e y.1 u' y.2).1.newWord = (R.W.e y.1 u' y.2).1.letter?.toList := by
    rw [reindex_newWord_eq, hw, List.nil_append]
  rw [← hx2, ← hy2, e1, e2, List.length_append]

end ReindexInput

open scoped Classical in
/-- The readout of a finite sum of fluxes. -/
theorem reindex_readout_sum {S S' : Finset Comp} (m : ℕ) (E η : ℝ) {κ : Type*} (K : Finset κ)
    (f : κ → ∀ v' : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v'.1.root))
    (v : CompIn S) (t : ℝ) (x : Vec 2) :
    readoutFlux m E η (fun _ => True) (fun v' s y => ∑ k ∈ K, f k v' s y) v t x =
      ∑ k ∈ K, readoutFlux m E η (fun _ => True) (f k) v t x := by
  unfold readoutFlux
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases h : compParent m v'.1 = v.1
  · simp only [h, and_self, ↓reduceDIte]
    rw [reindex_cast_sum ((compParent_root m v'.1).symm.trans (congrArg Comp.root h)), Finset.smul_sum]
  · simp [h]

open scoped Classical in
/-- The readout of a flux that is a sum over the identities into a fixed column is a sum over the
sigma type of the rows and their identities. -/
theorem reindex_readout_sigma {S S' : Finset Comp} (m : ℕ) (E η : ℝ)
    (Γ : CompIn S' → Type) [∀ v', Fintype (Γ v')]
    (g : ∀ v' : CompIn S', Γ v' → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v'.1.root))
    (v : CompIn S) (t : ℝ) (x : Vec 2) :
    readoutFlux m E η (fun _ => True) (fun v' s y => ∑ γ : Γ v', g v' γ s y) v t x =
      ∑ z : Σ v', Γ v', if h : compParent m z.1.1 = v.1 then
        (E ^ (η * ((compWord m z.1.1).length : ℝ))) •
          cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r))
            ((compParent_root m z.1.1).symm.trans (congrArg Comp.root h))) (g z.1 z.2 t x)
        else 0 := by
  unfold readoutFlux
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases h : compParent m v'.1 = v.1
  · simp only [h, and_self, ↓reduceDIte]
    rw [reindex_cast_sum ((compParent_root m v'.1).symm.trans (congrArg Comp.root h)), Finset.smul_sum]
  · simp [h]

/-- Collapsing a sum over the parent index when each column has exactly one parent. -/
theorem reindex_sum_collapse {U C ι M : Type*} [Fintype U] [Fintype C] [Fintype ι]
    [AddCommMonoid M] (Γ : U → Type) [∀ u, Fintype (Γ u)] (Rel : C → U → Prop) [∀ c u, Decidable (Rel c u)] (u0 : C → U)
    (h0 : ∀ c, Rel c (u0 c)) (huniq : ∀ c u, Rel c u → u = u0 c)
    (X : ∀ (u : U) (_ : Γ u) (_ : ι) (c : C), Rel c u → M) :
    ∑ u : U, ∑ γ : Γ u, ∑ d : ι, ∑ c : C, (if h : Rel c u then X u γ d c h else 0) =
      ∑ c : C, ∑ γ : Γ (u0 c), ∑ d : ι, X (u0 c) γ d c (h0 c) := by
  have e : ∀ u : U, ∑ γ : Γ u, ∑ d : ι, ∑ c : C, (if h : Rel c u then X u γ d c h else 0) =
      ∑ c : C, ∑ γ : Γ u, ∑ d : ι, (if h : Rel c u then X u γ d c h else 0) := by
    intro u
    rw [Finset.sum_congr rfl (fun γ _ => Finset.sum_comm)]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun u _ => e u, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single (u0 c)]
  · refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [h0 c, ↓reduceDIte]
  · intro u _ hu
    refine Finset.sum_eq_zero fun γ _ => Finset.sum_eq_zero fun d _ => ?_
    have hn : ¬ Rel c u := fun h => hu (huniq c u h)
    simp only [hn, ↓reduceDIte]
  · intro h
    exact absurd (Finset.mem_univ _) h

open scoped Classical in
/-- The omitted flux of the extended family, split over the retained columns. -/
theorem reindex_omitted_expand (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G' : GenStage D hr Dm b j₀) (m H J : ℕ)
    (aY : ℝ → Vec 2 → ∀ v : CompIn (G'.retained m H J).comps, hr v.1.root)
    (v' : CompIn G'.comps) (t : ℝ) (x : Vec 2) :
    omittedFluxClassical P seedK freshK φ₀ G' (G'.retained m H J) aY v' t x =
      ∑ c : CompIn (G'.retained m H J).comps,
        ∑ γ : G'.fam.Γ v' ⟨c.1, (Finset.mem_filter.1 c.2).1⟩, ∑ d : Finset.Icc 2 Dm,
          G'.physCoeff v' ⟨c.1, (Finset.mem_filter.1 c.2).1⟩ γ d.1 t x
            (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              orderedDerivative word ((G'.kernelOf P seedK freshK v'
                ⟨c.1, (Finset.mem_filter.1 c.2).1⟩ γ).applyClassical φ₀ t (fun y => aY t y c)) x) := by
  unfold omittedFluxClassical
  exact reindex_sum_dite (S := G'.comps) (S₂ := (G'.retained m H J).comps)
    (Finset.filter_subset _ _) (fun c => ∑ γ : G'.fam.Γ v' ⟨c.1, (Finset.mem_filter.1 c.2).1⟩,
      ∑ d : Finset.Icc 2 Dm, G'.physCoeff v' ⟨c.1, (Finset.mem_filter.1 c.2).1⟩ γ d.1 t x
        (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          orderedDerivative word ((G'.kernelOf P seedK freshK v'
            ⟨c.1, (Finset.mem_filter.1 c.2).1⟩ γ).applyClassical φ₀ t (fun y => aY t y c)) x))

open scoped Classical in
/-- The readout of the omitted flux as a sum over the retained columns and the identities into
them. -/
theorem reindex_lhs_expand (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G' : GenStage D hr Dm b j₀) (m H J : ℕ) (E η : ℝ)
    (aY : ℝ → Vec 2 → ∀ v : CompIn (G'.retained m H J).comps, hr v.1.root)
    (v : CompIn G.comps) (t : ℝ) (x : Vec 2) :
    readoutFlux m E η (fun _ => True)
        (omittedFluxClassical P seedK freshK φ₀ G' (G'.retained m H J) aY) v t x =
      ∑ c : CompIn (G'.retained m H J).comps,
        ∑ z : Σ v', G'.fam.Γ v' ⟨c.1, (Finset.mem_filter.1 c.2).1⟩,
          if h : compParent m z.1.1 = v.1 then
            (E ^ (η * ((compWord m z.1.1).length : ℝ))) •
              cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r))
                ((compParent_root m z.1.1).symm.trans (congrArg Comp.root h)))
                (∑ d : Finset.Icc 2 Dm, G'.physCoeff z.1 ⟨c.1, (Finset.mem_filter.1 c.2).1⟩ z.2 d.1 t x
                  (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
                    orderedDerivative word ((G'.kernelOf P seedK freshK z.1
                      ⟨c.1, (Finset.mem_filter.1 c.2).1⟩ z.2).applyClassical φ₀ t
                        (fun y => aY t y c)) x))
          else 0 := by
  have hfun : (omittedFluxClassical P seedK freshK φ₀ G' (G'.retained m H J) aY) =
      fun v' s y => ∑ c : CompIn (G'.retained m H J).comps,
        ∑ γ : G'.fam.Γ v' ⟨c.1, (Finset.mem_filter.1 c.2).1⟩, ∑ d : Finset.Icc 2 Dm,
          G'.physCoeff v' ⟨c.1, (Finset.mem_filter.1 c.2).1⟩ γ d.1 s y
            (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              orderedDerivative word ((G'.kernelOf P seedK freshK v'
                ⟨c.1, (Finset.mem_filter.1 c.2).1⟩ γ).applyClassical φ₀ s (fun y' => aY s y' c)) y) :=
    funext fun v' => funext fun s => funext fun y => reindex_omitted_expand seedK freshK φ₀ G' m H J aY v' s y
  rw [hfun, reindex_readout_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact reindex_readout_sigma m E η (fun v' => G'.fam.Γ v' ⟨c.1, (Finset.mem_filter.1 c.2).1⟩)
    (fun v' γ s y => ∑ d : Finset.Icc 2 Dm, G'.physCoeff v' ⟨c.1, (Finset.mem_filter.1 c.2).1⟩ γ d.1 s y
      (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word ((G'.kernelOf P seedK freshK v'
          ⟨c.1, (Finset.mem_filter.1 c.2).1⟩ γ).applyClassical φ₀ s (fun y' => aY s y' c)) y)) v t x

namespace ReindexInput

theorem mem_iff (R : ReindexInput P Mn G G') (a : Comp) :
    a ∈ G'.comps ↔ a ∈ succExtComps G.level Mn.A Mn.J G.comps := by rw [R.act.2.2.1]

/-- The parent of a component of the extended stage, as a component of the extended stage. -/
abbrev parentComp (R : ReindexInput P Mn G G') (c : CompIn G'.comps) : CompIn G'.comps :=
  ⟨compParent G.level c.1, (R.mem_iff _).2 (Finset.mem_union_left _ (R.col_facts c).1)⟩

theorem parentComp_mem (R : ReindexInput P Mn G G') (c : CompIn G'.comps) :
    (R.parentComp c).1 ∈ G.comps := (R.col_facts c).1

end ReindexInput

variable [∀ r, CompleteSpace (hr r)]

open scoped Classical in
/-- **The root flux of the kernel average, split over the retained columns**: the kernel flux out
of the roots on the readout `aZ` is the sum over the retained columns `c` of the same expression
for the identities into the parent of `c` on the retained field `aY c`, weighted by `E^{η|𝔱|}`. -/
theorem reindex_rootFlux_expand (R : ReindexInput P Mn G G') (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    {S₁ : Finset Comp} (hS₁ : S₁ ⊆ G'.comps) (E η : ℝ) (t : ℝ)
    (aY : ℝ → Vec 2 → ∀ c : CompIn S₁, hr c.1.root) (hcont : ∀ c, Continuous fun x => aY t x c)
    (hper : ∀ c, IsZ2Periodic fun x => aY t x c)
    (hdiff : ∀ (c : CompIn S₁) (S : KernelSpec),
      ContDiff ℝ (Dm : ℕ∞) (S.applyClassical φ₀ t fun x => aY t x c))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hZ : ∀ u : CompIn G.comps, (fun x => aZ t x u) = fun x => ∑ c : CompIn S₁,
      if h : compParent G.level c.1 = u.1 then
        (E ^ (η * ((compWord G.level c.1).length : ℝ))) •
          cast (congrArg hr ((compParent_root G.level c.1).symm.trans (congrArg Comp.root h)))
            (aY t x c)
      else 0)
    (v'' : CompIn G'.comps) (x : Vec 2) :
    rootFluxOn P seedK freshK φ₀ G G' .kernel aZ v'' t x =
      ∑ c : CompIn S₁, ∑ γ : G'.fam.Γ v'' (R.parentComp ⟨c.1, hS₁ c.2⟩), ∑ d : Finset.Icc 2 Dm,
        (E ^ (η * ((compWord G.level c.1).length : ℝ))) •
          G'.physCoeff v'' (R.parentComp ⟨c.1, hS₁ c.2⟩) γ d.1 t x
            (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              cast (congrArg hr (compParent_root G.level c.1).symm)
                (orderedDerivative word ((G'.kernelOf P seedK freshK v''
                  (R.parentComp ⟨c.1, hS₁ c.2⟩) γ).applyClassical φ₀ t (fun y => aY t y c)) x)) := by
  unfold rootFluxOn
  rw [reindex_sum_dite (S := G'.comps) (S₂ := G.comps)
    (fun c hc => (R.mem_iff c).2 (Finset.mem_union_left _ hc))
    (fun u'' => ∑ γ : G'.fam.Γ v'' ⟨u''.1, (R.mem_iff _).2 (Finset.mem_union_left _ u''.2)⟩,
      ∑ d : Finset.Icc 2 Dm, G'.physCoeff v'' _ γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word (fun y => (G'.kernelOf P seedK freshK v'' _ γ).applyClassical φ₀ t
          (fun y' => aZ t y' u'') y) x))]
  have hstep : ∀ (u'' : CompIn G.comps) (γ : G'.fam.Γ v'' ⟨u''.1, (R.mem_iff _).2 (Finset.mem_union_left _ u''.2)⟩)
      (d : Finset.Icc 2 Dm),
      G'.physCoeff v'' _ γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word (fun y => (G'.kernelOf P seedK freshK v'' _ γ).applyClassical φ₀ t
          (fun y' => aZ t y' u'') y) x) =
      ∑ c : CompIn S₁, if h : compParent G.level c.1 = u''.1 then
        (E ^ (η * ((compWord G.level c.1).length : ℝ))) •
          G'.physCoeff v'' _ γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            cast (congrArg hr ((compParent_root G.level c.1).symm.trans (congrArg Comp.root h)))
              (orderedDerivative word ((G'.kernelOf P seedK freshK v'' _ γ).applyClassical φ₀ t
                (fun y => aY t y c)) x))
      else 0 := by
    intro u'' γ d
    have key := reindex_kernel_readout_term hφs hφsupp (G'.kernelOf P seedK freshK v'' _ γ) t
      G.level E η (aY t) hcont hper (j := d.1 - 1)
      (fun c => (hdiff c _).of_le (by
        have := (Finset.mem_Icc.1 d.2).2
        exact_mod_cast (Nat.sub_le _ _).trans this))
      u''.1 (fun x => aZ t x u'') (hZ u'') (G'.physCoeff v'' _ γ d.1 t x) x
    exact key
  refine (Finset.sum_congr rfl fun u'' _ => Finset.sum_congr rfl fun γ _ =>
    Finset.sum_congr rfl fun d _ => hstep u'' γ d).trans ?_
  have hcol := reindex_sum_collapse (ι := ↥(Finset.Icc 2 Dm)) (M := PiLp 2 (fun _ : Fin 2 => hr v''.1.root)) (Γ := fun u'' : CompIn G.comps =>
      G'.fam.Γ v'' ⟨u''.1, (R.mem_iff _).2 (Finset.mem_union_left _ u''.2)⟩)
    (fun c u => compParent G.level c.1 = u.1)
    (fun c => ⟨compParent G.level c.1, (R.col_facts ⟨c.1, hS₁ c.2⟩).1⟩) (fun c => rfl)
    (fun c u h => Subtype.ext h.symm)
    (fun u'' γ d c h => (E ^ (η * ((compWord G.level c.1).length : ℝ))) •
      G'.physCoeff v'' _ γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        cast (congrArg hr ((compParent_root G.level c.1).symm.trans (congrArg Comp.root h)))
          (orderedDerivative word ((G'.kernelOf P seedK freshK v'' _ γ).applyClassical φ₀ t
            (fun y => aY t y c)) x)))

  rw [hcol]

omit [∀ r, CompleteSpace (hr r)] in
/-- The readout at `(t, x)` only depends on the fluxes at `(t, x)`. -/
theorem reindex_readout_congr {S S' : Finset Comp} (m : ℕ) (E η : ℝ) (sel : Comp → Prop)
    (F F' : ∀ v' : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v'.1.root))
    (v : CompIn S) (t : ℝ) (x : Vec 2) (h : ∀ v', F v' t x = F' v' t x) :
    readoutFlux m E η sel F v t x = readoutFlux m E η sel F' v t x := by
  unfold readoutFlux
  refine Finset.sum_congr rfl fun v' _ => ?_
  simp only [h]

open scoped Classical in
/-- **The readout of the root flux, split over the retained columns.** -/
theorem reindex_rhs_expand (R : ReindexInput P Mn G G') (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    {S₁ : Finset Comp} (hS₁ : S₁ ⊆ G'.comps) (E η : ℝ) (t : ℝ)
    (aY : ℝ → Vec 2 → ∀ c : CompIn S₁, hr c.1.root) (hcont : ∀ c, Continuous fun x => aY t x c)
    (hper : ∀ c, IsZ2Periodic fun x => aY t x c)
    (hdiff : ∀ (c : CompIn S₁) (S : KernelSpec),
      ContDiff ℝ (Dm : ℕ∞) (S.applyClassical φ₀ t fun x => aY t x c))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hZ : ∀ u : CompIn G.comps, (fun x => aZ t x u) = fun x => ∑ c : CompIn S₁,
      if h : compParent G.level c.1 = u.1 then
        (E ^ (η * ((compWord G.level c.1).length : ℝ))) •
          cast (congrArg hr ((compParent_root G.level c.1).symm.trans (congrArg Comp.root h)))
            (aY t x c)
      else 0)
    (v : CompIn G.comps) (x : Vec 2) :
    rootReadout P seedK freshK φ₀ G G' .kernel G.level E η aZ v t x =
      ∑ c : CompIn S₁, ∑ z : Σ v'', G'.fam.Γ v'' (R.parentComp ⟨c.1, hS₁ c.2⟩),
        if h : compParent G.level z.1.1 = v.1 then
          (E ^ (η * ((compWord G.level z.1.1).length : ℝ))) •
            cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r))
              ((compParent_root G.level z.1.1).symm.trans (congrArg Comp.root h)))
              (∑ d : Finset.Icc 2 Dm, (E ^ (η * ((compWord G.level c.1).length : ℝ))) •
                G'.physCoeff z.1 (R.parentComp ⟨c.1, hS₁ c.2⟩) z.2 d.1 t x
                  (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
                    cast (congrArg hr (compParent_root G.level c.1).symm)
                      (orderedDerivative word ((G'.kernelOf P seedK freshK z.1
                        (R.parentComp ⟨c.1, hS₁ c.2⟩) z.2).applyClassical φ₀ t
                          (fun y => aY t y c)) x)))
        else 0 := by
  unfold rootReadout
  rw [reindex_readout_congr G.level E η (fun _ => True) _
    (fun v' s y => ∑ c : CompIn S₁, ∑ γ : G'.fam.Γ v' (R.parentComp ⟨c.1, hS₁ c.2⟩),
      ∑ d : Finset.Icc 2 Dm, (E ^ (η * ((compWord G.level c.1).length : ℝ))) •
        G'.physCoeff v' (R.parentComp ⟨c.1, hS₁ c.2⟩) γ d.1 s y
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            cast (congrArg hr (compParent_root G.level c.1).symm)
              (orderedDerivative word ((G'.kernelOf P seedK freshK v'
                (R.parentComp ⟨c.1, hS₁ c.2⟩) γ).applyClassical φ₀ s (fun y' => aY s y' c)) y)))
    v t x (fun v' => reindex_rootFlux_expand R seedK freshK φ₀ hφs hφsupp hS₁ E η t aY hcont hper
      hdiff aZ hZ v' x), reindex_readout_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := reindex_readout_sigma G.level E η
    (fun v' => G'.fam.Γ v' (R.parentComp ⟨c.1, hS₁ c.2⟩))
    (fun v' γ s y => ∑ d : Finset.Icc 2 Dm, (E ^ (η * ((compWord G.level c.1).length : ℝ))) •
        G'.physCoeff v' (R.parentComp ⟨c.1, hS₁ c.2⟩) γ d.1 s y
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            cast (congrArg hr (compParent_root G.level c.1).symm)
              (orderedDerivative word ((G'.kernelOf P seedK freshK v'
                (R.parentComp ⟨c.1, hS₁ c.2⟩) γ).applyClassical φ₀ s (fun y' => aY s y' c)) y))) v t x
  exact this

namespace ReindexInput

omit [∀ r, CompleteSpace (hr r)] in
theorem rel_parent (R : ReindexInput P Mn G G') (c u' : CompIn G'.comps)
    (x : Σ v', G'.fam.Γ v' c) (y : Σ v'', G'.fam.Γ v'' u') (h : R.rel c u' x y) :
    compParent G.level x.1.1 = compParent G.level y.1.1 := by
  rw [← (R.tgt_facts x.1 c x.2).1, ← (R.tgt_facts y.1 u' y.2).1]
  have : (R.W.e x.1 c x.2).1.oldTgt = (reindexWithWord (compWord G.level c.1)
      (R.W.e y.1 u' y.2).1).oldTgt := by rw [h]
  rw [this, reindexWithWord_oldTgt]

end ReindexInput

open scoped Classical in
/-- **The reindexing.** The readout of the omitted flux of the extended family, over all rows, is
the readout of the kernel flux of the successor out of the roots: a copy has the same coefficient
and kernel in every word, a letter carries `E^{-η}`, and the readout weights add up. -/
theorem reindex_readout_eq (R : ReindexInput P Mn G G') (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    {H J : ℕ} (hJ : J ≤ Mn.J) (E η : ℝ) (hE : 0 < E) (t : ℝ)
    (aY : ℝ → Vec 2 → ∀ c : CompIn (G'.retained G.level H J).comps, hr c.1.root)
    (hcont : ∀ c, Continuous fun x => aY t x c)
    (hper : ∀ c, IsZ2Periodic fun x => aY t x c)
    (hdiff : ∀ (c : CompIn (G'.retained G.level H J).comps) (S : KernelSpec),
      ContDiff ℝ (Dm : ℕ∞) (S.applyClassical φ₀ t fun x => aY t x c))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hZ : ∀ u : CompIn G.comps, (fun x => aZ t x u) = fun x => ∑ c : CompIn (G'.retained G.level H J).comps,
      if h : compParent G.level c.1 = u.1 then
        (E ^ (η * ((compWord G.level c.1).length : ℝ))) •
          cast (congrArg hr ((compParent_root G.level c.1).symm.trans (congrArg Comp.root h)))
            (aY t x c)
      else 0)
    (v : CompIn G.comps) (x : Vec 2) :
    readoutFlux G.level E η (fun _ => True)
        (omittedFluxClassical P seedK freshK φ₀ G' (G'.retained G.level H J) aY) v t x =
      rootReadout P seedK freshK φ₀ G G' .kernel G.level E η aZ v t x := by
  have hS₁ : (G'.retained G.level H J).comps ⊆ G'.comps := Finset.filter_subset _ _
  rw [reindex_lhs_expand seedK freshK φ₀ G' G.level H J E η aY v t x,
    reindex_rhs_expand R seedK freshK φ₀ hφs hφsupp hS₁ E η t aY hcont hper hdiff aZ hZ v x]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine reindex_sum_of_rel _ _ _ _ (R.rel ⟨c.1, hS₁ c.2⟩ (R.parentComp ⟨c.1, hS₁ c.2⟩))
    (fun p _ => ?_) (fun q _ => ?_) (fun p _ q _ q' _ h h' => ?_) (fun p _ p' _ q _ h h' => ?_)
    (fun p _ q _ h => ?_)
  · obtain ⟨q, hq, -⟩ := R.rel_forward ⟨c.1, hS₁ c.2⟩ (R.parentComp ⟨c.1, hS₁ c.2⟩) rfl p
    exact ⟨q, Finset.mem_univ _, hq⟩
  · obtain ⟨p, hp, -⟩ := R.rel_backward ⟨c.1, hS₁ c.2⟩ (R.parentComp ⟨c.1, hS₁ c.2⟩) rfl
      (R.parentComp_mem _) ((Finset.mem_filter.1 c.2).2.2.trans hJ) q
    exact ⟨p, Finset.mem_univ _, hp⟩
  · exact R.rel_unique_y _ _ (R.parentComp_mem _) p q q' h h'
  · exact R.rel_unique_x _ _ p p' q h h'
  · by_cases hp : compParent G.level p.1.1 = v.1
    · have hq : compParent G.level q.1.1 = v.1 := (R.rel_parent _ _ p q h).symm.trans hp
      simp only [hp, hq, ↓reduceDIte]
      exact reindex_term_eq R seedK freshK φ₀ t x E η h hE
        (R.rel_weight _ _ (R.parentComp_mem _) p q h) (compParent_root G.level c.1).symm
        ((compParent_root G.level p.1.1).symm.trans (congrArg Comp.root hp))
        ((compParent_root G.level q.1.1).symm.trans (congrArg Comp.root hq)) (fun y => aY t y c)
    · have hq : ¬ compParent G.level q.1.1 = v.1 := fun h' => hp ((R.rel_parent _ _ p q h).trans h')
      simp only [hp, hq, ↓reduceDIte]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The jet-locality step: equal jets under products and composition**.

`sameJet_bilin`: a bilinear expression `B (c y) (f y)` with a common `C^r` factor `c` has equal
jets of order `r` when the `C^r` factors `f` have equal jets of order `r`. `sameJet_comp`:
`f ∘ φ` has equal jets of order `r` at `x` when `f` has equal jets of order `r` at `φ x`, for a
common `C^r` map `φ`. Both by induction on `r` with `sameJet_succ_iff` and the product and chain
rules. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem cd_le {a b : ℕ} (h : a ≤ b) {f : Vec 2 → E} (hf : ContDiff ℝ (↑b : ℕ∞) f) :
    ContDiff ℝ (↑a : ℕ∞) f := hf.of_le (by exact_mod_cast h)

/-- The partial derivative of a `C^{r+1}` function is `C^r`. -/
theorem cd_partial {r : ℕ} {f : Vec 2 → E} (hf : ContDiff ℝ (↑(r + 1) : ℕ∞) f) (i : Fin 2) :
    ContDiff ℝ (↑r : ℕ∞) (fun y => fderiv ℝ f y (basisVec i)) :=
  (hf.fderiv_right (by exact_mod_cast le_refl _)).clm_apply contDiff_const

theorem sameJet_bilin (B : E →L[ℝ] F →L[ℝ] G) (x : Vec 2) : ∀ (r : ℕ) (c : Vec 2 → E)
    (f₁ f₂ : Vec 2 → F), ContDiff ℝ (↑r : ℕ∞) c → ContDiff ℝ (↑r : ℕ∞) f₁ →
      ContDiff ℝ (↑r : ℕ∞) f₂ → SameJetAt r x f₁ f₂ →
      SameJetAt r x (fun y => B (c y) (f₁ y)) (fun y => B (c y) (f₂ y)) := by
  intro r
  induction r with
  | zero =>
    intro c f₁ f₂ _ _ _ h
    rw [sameJet_zero_iff] at h ⊢
    simp only [h]
  | succ r ih =>
    intro c f₁ f₂ hc hf₁ hf₂ h
    have hh := sameJet_succ_iff.1 h
    rw [sameJet_succ_iff]
    refine ⟨by simp only [hh.1], fun i => ?_⟩
    have hd : ∀ {f : Vec 2 → F}, ContDiff ℝ (↑(r + 1) : ℕ∞) f →
        (fun y => fderiv ℝ (fun y => B (c y) (f y)) y (basisVec i)) =
          fun y => B (fderiv ℝ c y (basisVec i)) (f y) + B (c y) (fderiv ℝ f y (basisVec i)) := by
      intro f hf
      funext y
      exact fderiv_bilin B ((hc.differentiable (by exact_mod_cast Nat.succ_ne_zero r)) y)
        ((hf.differentiable (by exact_mod_cast Nat.succ_ne_zero r)) y) _
    rw [hd hf₁, hd hf₂]
    have hdc := cd_partial hc i
    have hcr := cd_le (Nat.le_succ r) hc
    have t1 : ∀ {f : Vec 2 → F}, ContDiff ℝ (↑(r + 1) : ℕ∞) f →
        ContDiff ℝ (↑r : ℕ∞) (fun y => B (fderiv ℝ c y (basisVec i)) (f y)) := fun hf =>
      (B.contDiff.comp hdc).clm_apply (cd_le (Nat.le_succ r) hf)
    have t2 : ∀ {f : Vec 2 → F}, ContDiff ℝ (↑(r + 1) : ℕ∞) f →
        ContDiff ℝ (↑r : ℕ∞) (fun y => B (c y) (fderiv ℝ f y (basisVec i))) := fun hf =>
      (B.contDiff.comp hcr).clm_apply (cd_partial hf i)
    exact sameJet_add (t1 hf₁) (t1 hf₂) (t2 hf₁) (t2 hf₂)
      (ih _ _ _ hdc (cd_le (Nat.le_succ r) hf₁) (cd_le (Nat.le_succ r) hf₂)
        (sameJet_mono (Nat.le_succ r) h))
      (ih _ _ _ hcr (cd_partial hf₁ i) (cd_partial hf₂ i) (hh.2 i))

theorem sameJet_comp (x : Vec 2) : ∀ (r : ℕ) (φ : Vec 2 → Vec 2) (f₁ f₂ : Vec 2 → F),
    ContDiff ℝ (↑r : ℕ∞) φ → ContDiff ℝ (↑r : ℕ∞) f₁ → ContDiff ℝ (↑r : ℕ∞) f₂ →
      SameJetAt r (φ x) f₁ f₂ → SameJetAt r x (fun y => f₁ (φ y)) (fun y => f₂ (φ y)) := by
  intro r
  induction r with
  | zero =>
    intro φ f₁ f₂ _ _ _ h
    rw [sameJet_zero_iff] at h ⊢
    exact h
  | succ r ih =>
    intro φ f₁ f₂ hφ hf₁ hf₂ h
    have hh := sameJet_succ_iff.1 h
    rw [sameJet_succ_iff]
    refine ⟨hh.1, fun i => ?_⟩
    have hd : ∀ {f : Vec 2 → F}, ContDiff ℝ (↑(r + 1) : ℕ∞) f →
        (fun y => fderiv ℝ (fun y => f (φ y)) y (basisVec i)) =
          fun y => ∑ k : Fin 2, (fderiv ℝ φ y (basisVec i) k) • fderiv ℝ f (φ y) (basisVec k) := by
      intro f hf
      funext y
      have hfd : DifferentiableAt ℝ f (φ y) :=
        (hf.differentiable (by exact_mod_cast Nat.succ_ne_zero r)) _
      have hφd : DifferentiableAt ℝ φ y :=
        (hφ.differentiable (by exact_mod_cast Nat.succ_ne_zero r)) _
      have hc : fderiv ℝ (fun y => f (φ y)) y = (fderiv ℝ f (φ y)).comp (fderiv ℝ φ y) :=
        fderiv_comp y hfd hφd
      rw [hc]
      conv_lhs => rw [ContinuousLinearMap.comp_apply, AVRegularity.vec2_eq_sum_basisVec
        (fderiv ℝ φ y (basisVec i))]
      simp only [map_sum, map_smul]
    rw [hd hf₁, hd hf₂]
    have hφr := cd_le (Nat.le_succ r) hφ
    refine sameJet_sum Finset.univ (fun k _ => ?_) (fun k _ => ?_) fun k _ => ?_
    · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).contDiff.comp
        (cd_partial hφ i)).smul ((cd_partial hf₁ k).comp hφr)
    · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).contDiff.comp
        (cd_partial hφ i)).smul ((cd_partial hf₂ k).comp hφr)
    · have := sameJet_bilin (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F) x r
        (fun y => fderiv ℝ φ y (basisVec i) k)
        (fun y => fderiv ℝ f₁ (φ y) (basisVec k)) (fun y => fderiv ℝ f₂ (φ y) (basisVec k))
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).contDiff.comp
          (cd_partial hφ i))
        ((cd_partial hf₁ k).comp hφr) ((cd_partial hf₂ k).comp hφr)
        (ih φ _ _ hφr (cd_partial hf₁ k) (cd_partial hf₂ k) (hh.2 k))
      simpa using this

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The jet-locality step: the covariance polynomials at finite regularity**.

`covOperator Hc` is the second order operator `∑ Hc i j ∂_i ∂_j`; as a sum of ordered derivatives of
the words `(j, i)` it loses two derivatives and reads the jets of its argument of the orders
`≤ r + 2` to give those of order `r` (`covOperator_jet`). Iterating (`covOperator_iter_jet`)
gives `CovPolyPJetStatement` and `CovPolyQJetStatement`.

For `p = 0` the operator is the identity. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `covOperator` as a sum of ordered derivatives of the words `(j, i)`. -/
theorem covOperator_eq' (Hc : Matrix (Fin 2) (Fin 2) ℝ) (f : Vec 2 → E) :
    covOperator Hc f = fun y => ∑ q : Fin 2 × Fin 2,
      (Hc q.1 q.2 • ContinuousLinearMap.id ℝ E) (orderedDerivative ![q.2, q.1] f y) := by
  funext y
  simp [covOperator, orderedDerivative, List.ofFn_succ, Fintype.sum_prod_type]

/-- One application of `covOperator` loses two derivatives and the jets of order `r`. -/
theorem covOperator_jet (Hc : Matrix (Fin 2) (Fin 2) ℝ) (s : ℕ) (x : Vec 2)
    {f g : Vec 2 → E} (hf : ContDiff ℝ (↑(s + 2) : ℕ∞) f) (hg : ContDiff ℝ (↑(s + 2) : ℕ∞) g)
    (h : SameJetAt (s + 2) x f g) :
    ContDiff ℝ (↑s : ℕ∞) (covOperator Hc f) ∧ ContDiff ℝ (↑s : ℕ∞) (covOperator Hc g) ∧
      SameJetAt s x (covOperator Hc f) (covOperator Hc g) := by
  have hc : ∀ {k : Vec 2 → E}, ContDiff ℝ (↑(s + 2) : ℕ∞) k → ∀ q : Fin 2 × Fin 2,
      ContDiff ℝ (↑s : ℕ∞) (orderedDerivative ![q.2, q.1] k) := fun {k} hk q =>
    AVRegularity.Sampling.contDiff_orderedDerivative s _ k (by simpa [add_comm] using hk)
  refine ⟨?_, ?_, ?_⟩
  · rw [covOperator_eq']
    exact ContDiff.sum fun q _ => ((Hc q.1 q.2 • ContinuousLinearMap.id ℝ E).contDiff).comp (hc hf q)
  · rw [covOperator_eq']
    exact ContDiff.sum fun q _ => ((Hc q.1 q.2 • ContinuousLinearMap.id ℝ E).contDiff).comp (hc hg q)
  · intro r I hr
    rw [covOperator_eq', covOperator_eq']
    have hr' : ∀ {k : Vec 2 → E}, ContDiff ℝ (↑(s + 2) : ℕ∞) k → ∀ q : Fin 2 × Fin 2,
        ContDiff ℝ (↑r : ℕ∞) (orderedDerivative ![q.2, q.1] k) := fun hk q =>
      (hc hk q).of_le (by exact_mod_cast hr)
    have e1 := congrFun (AVRegularity.Providers.PathDecomp.orderedDerivative_clm_sum
      (Finset.univ : Finset (Fin 2 × Fin 2)) (fun q => Hc q.1 q.2 • ContinuousLinearMap.id ℝ E) I
      (β := fun q => orderedDerivative ![q.2, q.1] f) fun q _ => hr' hf q) x
    have e2 := congrFun (AVRegularity.Providers.PathDecomp.orderedDerivative_clm_sum
      (Finset.univ : Finset (Fin 2 × Fin 2)) (fun q => Hc q.1 q.2 • ContinuousLinearMap.id ℝ E) I
      (β := fun q => orderedDerivative ![q.2, q.1] g) fun q _ => hr' hg q) x
    rw [e1, e2]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    rw [← AVRegularity.CycleWords.orderedDerivative_append, ← AVRegularity.CycleWords.orderedDerivative_append]
    exact h _ _ (by omega)

/-- The iterates of `covOperator` lose `2l` derivatives. -/
theorem covOperator_iter_jet (Hc : Matrix (Fin 2) (Fin 2) ℝ) (x : Vec 2) (n : ℕ) :
    ∀ (l : ℕ) {f g : Vec 2 → E}, ContDiff ℝ (↑(n + 2 * l) : ℕ∞) f →
      ContDiff ℝ (↑(n + 2 * l) : ℕ∞) g → SameJetAt (n + 2 * l) x f g →
      ContDiff ℝ (↑n : ℕ∞) ((covOperator Hc)^[l] f) ∧ ContDiff ℝ (↑n : ℕ∞) ((covOperator Hc)^[l] g) ∧
        SameJetAt n x ((covOperator Hc)^[l] f) ((covOperator Hc)^[l] g) := by
  intro l
  induction l with
  | zero => intro f g hf hg h; exact ⟨hf, hg, h⟩
  | succ l ih =>
    intro f g hf hg h
    have e : n + 2 * (l + 1) = (n + 2 * l) + 2 := by ring
    rw [e] at hf hg h
    obtain ⟨h1, h2, h3⟩ := covOperator_jet Hc (n + 2 * l) x hf hg h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih h1 h2 h3

/-- `SameJetAt` is monotone in the order. -/
theorem sameJetAt_mono {s s' : ℕ} (hs : s ≤ s') {x : Vec 2} {f g : Vec 2 → E}
    (h : SameJetAt s' x f g) : SameJetAt s x f g := fun r I hr => h r I (hr.trans hs)

/-- **Inner step (`P_p`).** -/
theorem covPolyPJet : CovPolyPJetStatement := by
  intro E _ _ Hc p s x f g hf hg h
  have key : ∀ l ∈ Finset.range (p + 1),
      ContDiff ℝ (↑s : ℕ∞) ((covOperator Hc)^[l] f) ∧ ContDiff ℝ (↑s : ℕ∞) ((covOperator Hc)^[l] g) ∧
        SameJetAt s x ((covOperator Hc)^[l] f) ((covOperator Hc)^[l] g) := by
    intro l hl
    have hl' : l ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have hle : s + 2 * l ≤ s + 2 * p := by omega
    exact covOperator_iter_jet Hc x s l (hf.of_le (by exact_mod_cast hle))
      (hg.of_le (by exact_mod_cast hle)) (sameJetAt_mono hle h)
  have sm : ∀ k : Vec 2 → E, (∀ l ∈ Finset.range (p + 1), ContDiff ℝ (↑s : ℕ∞) ((covOperator Hc)^[l] k)) →
      covPolyP Hc p k = fun y => ∑ l ∈ Finset.range (p + 1),
        (((l.factorial : ℝ)⁻¹) • ContinuousLinearMap.id ℝ E) (((covOperator Hc)^[l] k) y) := by
    intro k _; funext y; simp [covPolyP, Finset.sum_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [sm f fun l hl => (key l hl).1]
    exact ContDiff.sum fun l hl => (_ : E →L[ℝ] E).contDiff.comp (key l hl).1
  · rw [sm g fun l hl => (key l hl).2.1]
    exact ContDiff.sum fun l hl => (_ : E →L[ℝ] E).contDiff.comp (key l hl).2.1
  · intro r I hr
    rw [sm f fun l hl => (key l hl).1, sm g fun l hl => (key l hl).2.1]
    have e1 := congrFun (AVRegularity.Providers.PathDecomp.orderedDerivative_clm_sum
      (Finset.range (p + 1)) (fun l => ((l.factorial : ℝ)⁻¹) • ContinuousLinearMap.id ℝ E) I
      (β := fun l => (covOperator Hc)^[l] f)
      fun l hl => (key l hl).1.of_le (by exact_mod_cast hr)) x
    have e2 := congrFun (AVRegularity.Providers.PathDecomp.orderedDerivative_clm_sum
      (Finset.range (p + 1)) (fun l => ((l.factorial : ℝ)⁻¹) • ContinuousLinearMap.id ℝ E) I
      (β := fun l => (covOperator Hc)^[l] g)
      fun l hl => (key l hl).2.1.of_le (by exact_mod_cast hr)) x
    rw [e1, e2]
    exact Finset.sum_congr rfl fun l hl => by rw [(key l hl).2.2 r I hr]

/-- **Outer step (`Q_p`).** -/
theorem covPolyQJet : CovPolyQJetStatement := by
  intro E _ _ Hc p x f g hf hg h
  unfold covPolyQ
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  have hle : 0 + 2 * l ≤ 2 * p := by omega
  have := (covOperator_iter_jet Hc x 0 l (hf.of_le (by exact_mod_cast hle))
    (hg.of_le (by exact_mod_cast hle)) (sameJetAt_mono hle h)).2.2 0 (Fin.elim0 : DerivativeWord2 0) le_rfl
  simp only [orderedDerivative_zero] at this
  rw [this]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end
