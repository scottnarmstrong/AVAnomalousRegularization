-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.TrimmedQuietMargin
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.CycleComparison.Residual.FastJets.Sampling
import AVRegularity.CycleComparison.Residual.TailJets
import AVRegularity.CycleComparison.Residual.Jets.Lift
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.FastJets

/-! Fast derivatives of the cell antidivergence: if `V = ∇_z φ`, `div_z V = f`, then
`∂_z^δ V = ∇_z ∂_z^δ φ` and `div_z ∂_z^δ V = ∂_z^δ f`, so the fibrewise `L²` bound with slow
derivatives holds for fast derivatives as well. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_fderiv_symm {g : Vec 2 → E} (hg : ContDiff ℝ 2 g) (y u w : Vec 2) :
    fderiv ℝ (fun y' => fderiv ℝ g y' u) y w = fderiv ℝ (fun y' => fderiv ℝ g y' w) y u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) y :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) y
  have h1 : ∀ v w, fderiv ℝ (fun y' => fderiv ℝ g y' v) y w = fderiv ℝ (fderiv ℝ g) y w v := by
    intro v w
    have := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp y hd.hasFDerivAt
    have h2 : (fun y' => fderiv ℝ g y' v) = (ContinuousLinearMap.apply ℝ E v) ∘ fderiv ℝ g := rfl
    rw [h2, this.fderiv]; rfl
  rw [h1, h1]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp)).eq w u

/-- Periodicity of a fast derivative. -/
theorem isZ2Periodic_fderiv {g : Vec 2 → E} (hg : AVenhance.IsZ2Periodic g) (v : Vec 2) :
    AVenhance.IsZ2Periodic (fun y => fderiv ℝ g y v) := by
  intro n x
  have e : (fun y => g (y + AVenhance.latticeShift n)) = g := funext (hg n)
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := x) (AVenhance.latticeShift n)
  rw [e] at h
  simp only
  rw [← h]

theorem fastPartial_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {G : Vec 2 → Vec 2 → E} (hG : ∀ X, Differentiable ℝ (G X)) (i : Fin 2) (X z : Vec 2) :
    fastPartial i (fun X' z' => L (G X' z')) X z = L (fastPartial i G X z) := by
  have := L.hasFDerivAt.comp z (hG X z).hasFDerivAt
  simp only [fastPartial]
  have h2 : (fun z' => L (G X z')) = L ∘ G X := rfl
  rw [h2, this.fderiv]; rfl

theorem two_le_cast {n : ℕ} (h : 2 ≤ n) : (2 : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) := by
  have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.2 (by exact_mod_cast h)
  simpa using h1

section Inner
variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- One fast derivative of a cell antidivergence is a cell antidivergence of the fast derivative. -/
theorem isCellAntidivergence_fastPartial {sX s : ℕ} {f : Vec 2 → Vec 2 → E}
    {V : Vec 2 → Vec 2 → Fin 2 → E} (h : IsCellAntidivergence sX (s + 2) f V) (i : Fin 2) :
    IsCellAntidivergence sX (s + 1) (fastPartial i f)
      (fun X z k => fastPartial i (fun X' z' => V X' z' k) X z) := by
  obtain ⟨hVbox, hVper, φ, hφbox, hφper, hφmean, hVφ, hdiv⟩ := h
  have hVd : ∀ X, Differentiable ℝ (V X) := fun X =>
    (hVbox.1 X).differentiable (by exact_mod_cast (by omega : s + 2 ≠ 0))
  have hVk : ∀ X k, ContDiff ℝ 2 (fun z => V X z k) := fun X k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k).contDiff.comp
      (hVbox.1 X)).of_le (two_le_cast (by omega))
  have hφC : ∀ X, ContDiff ℝ 2 (φ X) := fun X =>
    (hφbox.1 X).of_le (two_le_cast (by omega))
  have hk : ∀ X z k, fastPartial i (fun X' z' => V X' z' k) X z = fastPartial i V X z k :=
    fun X z k => fastPartial_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k)
      hVd i X z
  have hVeq : (fun X z k => fastPartial i (fun X' z' => V X' z' k) X z) = fastPartial i V :=
    funext fun X => funext fun z => funext fun k => hk X z k
  rw [hVeq]
  refine ⟨hVbox.fastPartial i, fun X n x => ?_, fastPartial i φ, hφbox.fastPartial i,
    fun X n x => ?_, fun X => ?_, fun X z k => ?_, fun X z => ?_⟩
  · exact isZ2Periodic_fderiv (hVper X) (basisVec i) n x
  · exact isZ2Periodic_fderiv (hφper X) (basisVec i) n x
  · exact fieldCellMean_fastPartial_eq_zero (φ X)
      ((hφC X).of_le (by norm_num)) (hφper X) i
  · have e1 : (fun z' => V X z' k) = fun z' => fderiv ℝ (φ X) z' (basisVec k) :=
      funext fun z' => hVφ X z' k
    have e2 : fastPartial i V X z k = fderiv ℝ (fun z' => V X z' k) z (basisVec i) := by
      rw [← hk]; rfl
    rw [e2, e1]
    exact fderiv_fderiv_symm (hφC X) z (basisVec k) (basisVec i)
  · have hdk : ∀ k : Fin 2, DifferentiableAt ℝ (fun z' => fderiv ℝ (fun z => V X z k) z' (basisVec k)) z :=
      fun k => ((((hVk X k).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
        one_ne_zero) z
    have e3 : f X = fun z' => ∑ k : Fin 2, fderiv ℝ (fun z => V X z k) z' (basisVec k) :=
      funext fun z' => (hdiv X z').symm
    have e4 : fastPartial i f X z = ∑ k : Fin 2,
        fderiv ℝ (fun z' => fderiv ℝ (fun z => V X z k) z' (basisVec k)) z (basisVec i) := by
      simp only [fastPartial]
      rw [e3, fderiv_fun_sum fun k _ => hdk k]
      simp
    rw [e4]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e5 : (fun z' => fastPartial i V X z' k) =
        fun z' => fderiv ℝ (fun z => V X z k) z' (basisVec i) := funext fun z' => by
      rw [← hk]; rfl
    rw [e5]
    exact (fderiv_fderiv_symm (hVk X k) z (basisVec k) (basisVec i)).symm

/-- A fast word of a cell antidivergence is a cell antidivergence of the fast word. -/
theorem isCellAntidivergence_fastWord {sX : ℕ} : ∀ {b : ℕ} (δ : DerivativeWord2 b) {sZ : ℕ}
    {f : Vec 2 → Vec 2 → E} {V : Vec 2 → Vec 2 → Fin 2 → E},
    IsCellAntidivergence sX sZ f V → b + 1 ≤ sZ →
      IsCellAntidivergence sX (sZ - b) (fun X z => orderedDerivative δ (f X) z)
        (fun X z k => orderedDerivative δ (fun z' => V X z' k) z) := by
  intro b
  induction b with
  | zero =>
    intro δ sZ f V h _
    simpa [orderedDerivative_zero] using h
  | succ b ih =>
    intro δ sZ f V h hb
    obtain ⟨k, δ', rfl⟩ : ∃ k δ', δ = Fin.cons k δ' := ⟨δ 0, Fin.tail δ, (Fin.cons_self_tail δ).symm⟩
    obtain ⟨s, rfl⟩ : ∃ s, sZ = s + 2 := ⟨sZ - 2, by omega⟩
    have h1 := isCellAntidivergence_fastPartial h k
    have key := ih δ' h1 (by omega)
    simp only [orderedDerivative_cons]
    rw [show s + 2 - (b + 1) = s + 1 - b by omega]
    exact key

end Inner

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- The scalar source of a cell antidivergence is box smooth of fast order one less. -/
theorem isBoxSmooth_of_isCellAntidivergence {sX s : ℕ} {f : Vec 2 → Vec 2 → F}
    {V : Vec 2 → Vec 2 → Fin 2 → F} (h : IsCellAntidivergence sX (s + 1) f V) :
    IsBoxSmooth sX s f := by
  obtain ⟨hVbox, -, φ, -, -, -, -, hdiv⟩ := h
  have hk : ∀ k : Fin 2, IsBoxSmooth sX s (fastPartial k (fun X z => V X z k)) := fun k =>
    (hVbox.map_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => F) k)).fastPartial k
  have := IsBoxSmooth.sum (Finset.univ : Finset (Fin 2)) fun k _ => hk k
  have e : f = fun X z => ∑ k : Fin 2, fastPartial k (fun X z => V X z k) X z :=
    funext fun X => funext fun z => (hdiv X z).symm
  rw [e]
  exact this

end InnerProduct
end

/-! Fast jets along a cleanup chain: a fast word `δ` of a cleanup chain is again a cleanup chain
(of one fast order less per letter), because the slow divergence commutes with fast derivatives
and a fast derivative of a cell antidivergence is a cell antidivergence. The fast jet estimates
are then the slow jet estimates along a cleanup chain (for `scalJet` and `vecJet`) applied to the
differentiated chain. -/

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The fast word `δ` of every member of a family of vector fields. -/
def fastFam {b : ℕ} (δ : DerivativeWord2 b) (V : ℕ → Vec 2 → Vec 2 → Fin 2 → F) :
    ℕ → Vec 2 → Vec 2 → Fin 2 → F :=
  fun n X z k => orderedDerivative δ (fun z' => V n X z' k) z

omit [FiniteDimensional ℝ F] in
/-- The slow divergence commutes with a fast word. -/
theorem fast_cleanupSource {b : ℕ} (δ : DerivativeWord2 b) {V : ℕ → Vec 2 → Vec 2 → Fin 2 → F}
    {j : ℕ} (hV : IsBoxSmooth 1 b (V (j - 1))) :
    (fun X z => orderedDerivative δ (fun z' => cleanupSource V j X z') z) =
      cleanupSource (fastFam δ V) j := by
  have hk : ∀ k : Fin 2, IsBoxSmooth 1 b (fun X z => V (j - 1) X z k) := fun k =>
    hV.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => F) k)
  have hlen : (List.ofFn δ).length = b := List.length_ofFn
  have hsw : ∀ k : Fin 2, IsBoxSmooth 0 b (slowPartial k (fun X z => V (j - 1) X z k)) := fun k =>
    (hk k).slowPartial (sX := 0) k
  funext X z
  simp only [cleanupSource]
  have hg : ∀ k : Fin 2, ContDiff ℝ (b : ℕ∞)
      (fun z' => slowPartial k (fun X z => V (j - 1) X z k) X z') := fun k => (hsw k).1 X
  rw [orderedDerivative_neg_sum δ (g := fun k z' => slowPartial k (fun X z => V (j - 1) X z k) X z') hg z]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have := slowPartial_fastL k (List.ofFn δ) (F := fun X z => V (j - 1) X z k)
    (by rw [hlen]; exact hk k)
  have h2 := congrFun (congrFun this X) z
  exact h2.symm

/-- A fast word of a cleanup chain is a cleanup chain of one fast order less per letter. -/
theorem isCleanupChain_fastWord {sX sZ A b : ℕ} (δ : DerivativeWord2 b) (hb : b + 1 ≤ sZ)
    {f₀ : Vec 2 → Vec 2 → F} {F₀ : Vec 2 → Vec 2 → Fin 2 → F}
    {V : ℕ → Vec 2 → Vec 2 → Fin 2 → F} (hF : IsBoxSmooth sX sZ F₀)
    (hV : IsCleanupChain sX sZ A f₀ F₀ V) (hX : 1 ≤ sX ∨ A ≤ 1) :
    IsCleanupChain sX (sZ - b) A (fun X z => orderedDerivative δ (f₀ X) z)
      (fun X z k => orderedDerivative δ (fun z' => F₀ X z' k) z) (fastFam δ V) := by
  have hbox := IsCleanupChain.isBoxSmooth hF hV
  obtain ⟨⟨W₀, hW₀, hV0⟩, hVj⟩ := hV
  refine ⟨⟨fun X z k => orderedDerivative δ (fun z' => W₀ X z' k) z,
    isCellAntidivergence_fastWord δ hW₀ hb, ?_⟩, fun j hj1 hjA => ?_⟩
  · funext X z k
    have hF1 : ContDiff ℝ (b : ℕ∞) (fun z' => F₀ X z' k) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => F) k).contDiff.comp
        (hF.1 X)).of_le (by exact_mod_cast (by omega : b ≤ sZ))
    have hW1 : ContDiff ℝ (b : ℕ∞) (fun z' => W₀ X z' k) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => F) k).contDiff.comp
        (hW₀.1.1 X)).of_le (by exact_mod_cast (by omega : b ≤ sZ))
    have := congrFun (orderedDerivative_add δ hF1 hW1) z
    simp only [fastFam, hV0]
    exact this
  · have hX1 : 1 ≤ sX := by rcases hX with h | h <;> omega
    have hV' : IsBoxSmooth 1 b (V (j - 1)) :=
      (hbox (j - 1) (by omega)).mono hX1 (by omega)
    have h' := isCellAntidivergence_fastWord δ (hVj j hj1 hjA) hb
    rw [← fast_cleanupSource δ hV']
    exact h'

omit [FiniteDimensional ℝ F] in
/-- The componentwise fast word of a box-smooth vector field is the fast word of the field. -/
theorem fastFam_eq {b s n : ℕ} (δ : DerivativeWord2 b) {V : ℕ → Vec 2 → Vec 2 → Fin 2 → F}
    (hV : IsBoxSmooth s b (V n)) : fastFam δ V n = fastL (List.ofFn δ) (V n) := by
  funext X z k
  have h := congrFun (orderedDerivative_clm_comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => F) k) δ (g := V n X)
    (by exact_mod_cast (hV.1 X))) z
  exact h

omit [FiniteDimensional ℝ F] in
theorem isSlowSmooth_fastFam {b s n : ℕ} (δ : DerivativeWord2 b)
    {V : ℕ → Vec 2 → Vec 2 → Fin 2 → F} (hV : IsBoxSmooth s b (V n)) :
    IsSlowSmooth s (fastFam δ V n) := by
  rw [fastFam_eq δ hV]
  exact (isBoxSmooth_fastL (sZ := 0) (List.ofFn δ) (by simpa using hV)).isSlowSmooth

section Chain

variable {sX sZ A b : ℕ} {f₀ : Vec 2 → Vec 2 → F} {F₀ : Vec 2 → Vec 2 → Fin 2 → F}
  {V : ℕ → Vec 2 → Vec 2 → Fin 2 → F}

/-- Iterated cleanup with a fast word: the `m`-th jet of `V_j` is controlled by the `(m+j)`-th jet
of `V_0`. -/
theorem vecJetF_cleanupChain_le (δ : DerivativeWord2 b) (hb : b + 1 ≤ sZ)
    (hF : IsBoxSmooth sX sZ F₀) (hV : IsCleanupChain sX sZ A f₀ F₀ V) :
    ∀ j, j < A → ∀ m, m + j ≤ sX → ∀ X,
      vecJetF (V j) m δ X ≤ (2 * antidivConst) ^ j * vecJetF (V 0) (m + j) δ X := by
  intro j hj m hm X
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simp
  · have hX : 1 ≤ sX := by omega
    have hch := isCleanupChain_fastWord δ hb hF hV (Or.inl hX)
    have hFs : IsSlowSmooth sX (fun X z k => orderedDerivative δ (fun z' => F₀ X z' k) z) := by
      have := isSlowSmooth_fastFam δ (V := fun _ => F₀) (n := 0) (hF.mono le_rfl (by omega))
      exact this
    exact vecJet_cleanupChain_le (sZ := sZ - b) (by omega) hFs hch j hj m hm X

/-- The first member of the chain, with a fast word. -/
theorem vecJetF_cleanupChain_zero_le (δ : DerivativeWord2 b) (hb : b + 1 ≤ sZ)
    (hF : IsBoxSmooth sX sZ F₀) (hV : IsCleanupChain sX sZ A f₀ F₀ V) {m : ℕ} (hm : m ≤ sX)
    (X : Vec 2) :
    vecJetF (V 0) m δ X ≤ 2 * vecJetF F₀ m δ X + 2 * (antidivConst * scalJetF f₀ m δ X) := by
  have hV1 : IsCleanupChain sX sZ 1 f₀ F₀ V :=
    ⟨hV.1, fun j h1 h2 => absurd h2 (by omega)⟩
  have hch := isCleanupChain_fastWord δ hb hF hV1 (Or.inr le_rfl)
  have hFs : IsSlowSmooth sX (fun X z k => orderedDerivative δ (fun z' => F₀ X z' k) z) := by
    have := isSlowSmooth_fastFam δ (V := fun _ => F₀) (n := 0) (hF.mono le_rfl (by omega))
    exact this
  obtain ⟨⟨W₀, hW₀, -⟩, -⟩ := hV
  obtain ⟨s, rfl⟩ : ∃ s, sZ = s + 1 := ⟨sZ - 1, by omega⟩
  have hf : IsBoxSmooth sX s f₀ := isBoxSmooth_of_isCellAntidivergence hW₀
  have hfs : IsSlowSmooth m (fun X z => orderedDerivative δ (f₀ X) z) :=
    ((isBoxSmooth_fastL (sZ := s - b) (List.ofFn δ)
      (hf.mono le_rfl (by simp; omega))).isSlowSmooth).mono hm
  exact vecJet_cleanupChain_zero_le (sZ := s + 1 - b) (by omega) hFs hch hm hfs X

/-- The scalar remainder of the chain, with a fast word. -/
theorem scalJetF_cleanupChain_remainder_le (δ : DerivativeWord2 b) (hb : b + 1 ≤ sZ)
    (hA : 1 ≤ A) (hF : IsBoxSmooth sX sZ F₀) (hV : IsCleanupChain sX sZ A f₀ F₀ V) {m : ℕ}
    (hm : m + A ≤ sX) (X : Vec 2) :
    scalJetF (cleanupSource V A) m δ X ≤
      2 * ((2 * antidivConst) ^ (A - 1) * vecJetF (V 0) (m + A) δ X) := by
  have hX : 1 ≤ sX := by omega
  have hbox := IsCleanupChain.isBoxSmooth hF hV
  have hch := isCleanupChain_fastWord δ hb hF hV (Or.inl hX)
  have hFs : IsSlowSmooth sX (fun X z k => orderedDerivative δ (fun z' => F₀ X z' k) z) := by
    have := isSlowSmooth_fastFam δ (V := fun _ => F₀) (n := 0) (hF.mono le_rfl (by omega))
    exact this
  have hV' : IsBoxSmooth 1 b (V (A - 1)) := (hbox (A - 1) (by omega)).mono hX (by omega)
  have e : scalJetF (cleanupSource V A) m δ X = scalJet (cleanupSource (fastFam δ V) A) m X := by
    rw [← fast_cleanupSource δ hV']; rfl
  rw [e]
  exact scalJet_cleanupChain_remainder_le (sZ := sZ - b) (by omega) hA hFs hch hm X

end Chain
end

end AVRegularity.FastJets
end
