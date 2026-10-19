-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.External.FourierCarrierParseval
public import AVRegularity.CycleWords.Assembly.MixedWordsB1Statements
import AVRegularity.CycleWords.CellTransverseStrongSourceMemLp
import AVRegularity.CycleJoint.PlaneScalarDiffusionDeviationReadout
import AVRegularity.KernelEnergyPlane.PlaneDerivativeTensorCLM
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.CategoryTheory.Countable

section
section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords.Assembly

/-! # the swap of the slow and fast derivatives of a box-smooth field

For a box-smooth field `g(X, z)` of orders `(s, j)` the `j`-th fast jet of the `s`-th slow derivative
equals, as an element of the space of `j`-linear maps, the `s`-th slow derivative of the `j`-th fast
jet, evaluated at the same arguments (`fast_jet_slow_jet`).  Hence its norm is at most
`∏ ‖m_i‖` times the mixed jet `‖D_X^s D_z^j g‖` that the analytic envelope bounds
(`norm_fast_jet_slow_jet_le`). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Peeling the last slow derivative. -/
theorem iteratedFDeriv_peel_last {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : Vec 2 → G} {x : Vec 2} {b : ℕ} (hf : ContDiffAt ℝ ((b + 1 : ℕ) : WithTop ℕ∞) f x)
    (m : Fin (b + 1) → Vec 2) :
    iteratedFDeriv ℝ (b + 1) f x m =
      iteratedFDeriv ℝ b (fun y => fderiv ℝ f y (m (Fin.last b))) x (Fin.init m) := by
  have hfd : ContDiffAt ℝ (b : WithTop ℕ∞) (fderiv ℝ f) x :=
    hf.fderiv_right (m := (b : WithTop ℕ∞)) (by push_cast; exact le_rfl)
  rw [iteratedFDeriv_succ_apply_right]
  have h1 := ContinuousLinearMap.iteratedFDeriv_comp_left
    (ContinuousLinearMap.apply ℝ G (m (Fin.last b))) hfd (i := b) le_rfl
  have h3 : (fun y => fderiv ℝ f y (m (Fin.last b))) =
      ⇑(ContinuousLinearMap.apply ℝ G (m (Fin.last b))) ∘ fderiv ℝ f := rfl
  rw [h3, h1]
  rfl

theorem tbBoxSlow_contDiff {s j : ℕ} {g : Vec 2 → Vec 2 → E} (hg : IsBoxSmooth s j g)
    (z : Vec 2) : ContDiff ℝ (s : ℕ∞) (fun X => g X z) := by
  have h := (continuousMultilinearCurryFin0 ℝ (Vec 2) E).contDiff.comp
    ((hg.2.1 0 (Nat.zero_le _) z))
  simpa [Function.comp_def, iteratedFDeriv_zero_eq_comp] using h

/-- **Swap of the slow and fast derivatives** (equality of `j`-linear maps). -/
theorem fast_jet_slow_jet (j : ℕ) : ∀ (s : ℕ) (g : Vec 2 → Vec 2 → E), IsBoxSmooth s j g →
    ∀ (m : Fin s → Vec 2) (X₀ z : Vec 2),
      iteratedFDeriv ℝ j (fun z' => iteratedFDeriv ℝ s (fun X => g X z') X₀ m) z =
        iteratedFDeriv ℝ s (fun X' => iteratedFDeriv ℝ j (g X') z) X₀ m := by
  intro s
  induction s with
  | zero =>
    intro g hg m X₀ z
    simp [iteratedFDeriv_zero_apply]
  | succ s ih =>
    intro g hg m X₀ z
    set v := m (Fin.last s) with hv
    set gv : Vec 2 → Vec 2 → E := fun X z' => fderiv ℝ (fun X' => g X' z') X v with hgv
    have hbs : IsBoxSmooth s j gv := hg.slowDir v
    have hpeel : ∀ z', iteratedFDeriv ℝ (s + 1) (fun X => g X z') X₀ m =
        iteratedFDeriv ℝ s (fun X => gv X z') X₀ (Fin.init m) := by
      intro z'
      exact iteratedFDeriv_peel_last
        ((tbBoxSlow_contDiff hg z').contDiffAt) m
    have hfun : (fun z' => iteratedFDeriv ℝ (s + 1) (fun X => g X z') X₀ m) =
        fun z' => iteratedFDeriv ℝ s (fun X => gv X z') X₀ (Fin.init m) := funext hpeel
    rw [hfun, ih gv hbs (Fin.init m) X₀ z]
    have hcomm : ∀ X', iteratedFDeriv ℝ j (gv X') z =
        fderiv ℝ (fun X'' => iteratedFDeriv ℝ j (g X'') z) X' v := fun X' =>
      (slowDir_aux j E g (hg.mono (by omega) le_rfl) v X').2 z
    have hfun2 : (fun X' => iteratedFDeriv ℝ j (gv X') z) =
        fun X' => fderiv ℝ (fun X'' => iteratedFDeriv ℝ j (g X'') z) X' v := funext hcomm
    rw [hfun2]
    have hH : ContDiffAt ℝ ((s + 1 : ℕ) : WithTop ℕ∞)
        (fun X'' => iteratedFDeriv ℝ j (g X'') z) X₀ :=
      ((hg.2.1 j le_rfl z).of_le (by exact_mod_cast le_rfl)).contDiffAt
    exact (iteratedFDeriv_peel_last hH m).symm

theorem norm_fast_jet_slow_jet_le (j s : ℕ) (g : Vec 2 → Vec 2 → E) (hg : IsBoxSmooth s j g)
    (m : Fin s → Vec 2) (X₀ z : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun z' => iteratedFDeriv ℝ s (fun X => g X z') X₀ m) z‖ ≤
      (∏ i, ‖m i‖) * ‖iteratedFDeriv ℝ s (fun X' => iteratedFDeriv ℝ j (g X') z) X₀‖ := by
  rw [fast_jet_slow_jet j s g hg m X₀ z, mul_comm]
  exact ContinuousMultilinearMap.le_opNorm _ m

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # the envelope jets of a letter as real bounds on the term coefficients

For a constituent coefficient `g(X, z) = γ.coeff α r X z` that is box-smooth of orders
`(slow, J)` and jointly `C^{slow+J}`, the scalar term coefficient
`c(z) = D_X^s g(·, z)_k (X₀) [e_{ω₁}, …, e_{ω_s}]` is `C^J` and periodic in `z`, and its `l`-th jet
is bounded by the mixed jet `‖D_X^s D_z^l g‖` of the envelope (`tbTermCoef_jet_le`, through the
swap of the slow and fast derivatives, `norm_fast_jet_slow_jet_le`).

`LetterGood` collects the almost-every-time bounds of all constituent jets of a letter; the finite
intersection (letters, edges, orders, constituents, words, `s ≤ slow`, `q ≤ J`) is
`letterGood_ae`.  `envelope_real_sum_le` turns `IsAnalyticEnvelope` into the real inequality
`√(π_{x'}/π_x) ∑_γ ‖γ.map‖ ∑_{α,s,q} jet ≤ majorant`. -/

section Slice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slice_jet_eq {G : Vec 2 → Vec 2 → E} {s J : ℕ}
    (hG : ContDiff ℝ ((s + J : ℕ) : ℕ∞) (Function.uncurry G))
    (m : Fin s → Vec 2) (X₀ z' : Vec 2) :
    iteratedFDeriv ℝ s (fun X => G X z') X₀ m =
      iteratedFDeriv ℝ s (Function.uncurry G) (X₀, z') (fun i => (m i, 0)) := by
  have hc : ContDiff ℝ ((s + J : ℕ) : ℕ∞)
      (fun p : Vec 2 × Vec 2 => Function.uncurry G (p + (0, z'))) :=
    hG.comp (contDiff_id.add contDiff_const)
  have h1 : (fun X => G X z') = (fun p : Vec 2 × Vec 2 => Function.uncurry G (p + (0, z'))) ∘
      (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) := by
    funext X; simp [Function.uncurry]
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc _
    (by exact_mod_cast Nat.le_add_right _ _)]
  rw [iteratedFDeriv_comp_add_right]
  simp

theorem slice_jet_contDiff {G : Vec 2 → Vec 2 → E} {s J : ℕ}
    (hG : ContDiff ℝ ((s + J : ℕ) : ℕ∞) (Function.uncurry G))
    (m : Fin s → Vec 2) (X₀ : Vec 2) :
    ContDiff ℝ (J : ℕ∞) (fun z' => iteratedFDeriv ℝ s (fun X => G X z') X₀ m) := by
  have e : (fun z' => iteratedFDeriv ℝ s (fun X => G X z') X₀ m) = fun z' =>
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => Vec 2 × Vec 2) E (fun i => (m i, 0)))
        (iteratedFDeriv ℝ s (Function.uncurry G) (X₀, z')) := by
    funext z'; rw [slice_jet_eq hG]; rfl
  rw [e]
  refine (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => Vec 2 × Vec 2) E _).contDiff.comp ?_
  exact (hG.iteratedFDeriv_right (by exact_mod_cast le_of_eq (Nat.add_comm J s))).comp
    (contDiff_const.prodMk contDiff_id)

end Slice

section Term

/-- The scalar coefficient of a term: the `k`-th component of the `s`-th slow derivative in the
directions of the word `ω`, at `X₀`, as a function of `z`. -/
def tbTermCoef (coeff : Vec 2 → Vec 2 → Vec 2) (s : ℕ) (ω : DerivativeWord2 s) (X₀ : Vec 2)
    (k : Fin 2) : Vec 2 → ℝ :=
  fun z' => iteratedFDeriv ℝ s (fun X => coeff X z' k) X₀ (fun n => basisVec (ω n))

variable {coeff : Vec 2 → Vec 2 → Vec 2} {s J : ℕ}

theorem tbTermCoef_eq (hG : ContDiff ℝ ((s + J : ℕ) : ℕ∞) (Function.uncurry coeff))
    (ω : DerivativeWord2 s) (X₀ : Vec 2) (k : Fin 2) (z' : Vec 2) :
    tbTermCoef coeff s ω X₀ k z' =
      iteratedFDeriv ℝ s (fun X => coeff X z') X₀ (fun n => basisVec (ω n)) k := by
  unfold tbTermCoef
  have hX : ContDiff ℝ (s : ℕ∞) (fun X => coeff X z') := by
    have : ContDiff ℝ ((s + J : ℕ) : ℕ∞) (fun X => coeff X z') :=
      hG.comp (contDiff_id.prodMk contDiff_const)
    exact this.of_le (by exact_mod_cast Nat.le_add_right _ _)
  have := ContinuousLinearMap.iteratedFDeriv_comp_left (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 2 => ℝ) k) hX.contDiffAt (x := X₀) (i := s) le_rfl
  have h2 : (fun X => coeff X z' k) = ⇑(ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 2 => ℝ) k) ∘ (fun X => coeff X z') := rfl
  rw [h2, this]
  rfl

theorem tbTermCoef_contDiff (hG : ContDiff ℝ ((s + J : ℕ) : ℕ∞) (Function.uncurry coeff))
    (ω : DerivativeWord2 s) (X₀ : Vec 2) (k : Fin 2) :
    ContDiff ℝ (J : ℕ∞) (tbTermCoef coeff s ω X₀ k) := by
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).contDiff.comp
    (slice_jet_contDiff hG (fun n => basisVec (ω n)) X₀)
  have e : tbTermCoef coeff s ω X₀ k = ⇑(ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 2 => ℝ) k) ∘ (fun z' => iteratedFDeriv ℝ s (fun X => coeff X z') X₀
        (fun n => basisVec (ω n))) := by
    funext z'; rw [tbTermCoef_eq hG]; rfl
  rw [e]; exact h

theorem tbTermCoef_periodic (hper : ∀ X, AVenhance.IsZ2Periodic (coeff X)) (ω : DerivativeWord2 s)
    (X₀ : Vec 2) (k : Fin 2) : AVenhance.IsZ2Periodic (tbTermCoef coeff s ω X₀ k) := by
  intro n z
  unfold tbTermCoef
  have : (fun X => coeff X (z + AVenhance.latticeShift n) k) = fun X => coeff X z k := by
    funext X; rw [hper X n z]
  rw [this]

theorem tbTermCoef_jet_le (hG : ContDiff ℝ ((s + J : ℕ) : ℕ∞) (Function.uncurry coeff))
    (hB : IsBoxSmooth s J coeff) (ω : DerivativeWord2 s) (X₀ : Vec 2) (k : Fin 2) (l : ℕ)
    (hl : l ≤ J) (z : Vec 2) :
    ‖iteratedFDeriv ℝ l (tbTermCoef coeff s ω X₀ k) z‖ ≤
      ‖iteratedFDeriv ℝ s (fun X' => iteratedFDeriv ℝ l (coeff X') z) X₀‖ := by
  set C : Vec 2 → Vec 2 := fun z' => iteratedFDeriv ℝ s (fun X => coeff X z') X₀
    (fun n => basisVec (ω n)) with hC
  have hCd : ContDiff ℝ (J : ℕ∞) C := slice_jet_contDiff hG _ X₀
  have e : tbTermCoef coeff s ω X₀ k = ⇑(ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 2 => ℝ) k) ∘ C := by
    funext z'; rw [tbTermCoef_eq hG]; rfl
  have hproj : ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => by
      simpa using norm_le_pi_norm y k)
  rw [e]
  have h1 := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k)
    (hCd.contDiffAt) (x := z) (n := l) (by exact_mod_cast hl)
  have h2 := norm_fast_jet_slow_jet_le l s coeff (hB.mono le_rfl hl) (fun n => basisVec (ω n)) X₀ z
  have hprod : ∏ i : Fin s, ‖(basisVec (ω i) : Vec 2)‖ = 1 := by
    simp [AVRegularity.norm_basisVec]
  rw [hprod, one_mul] at h2
  calc _ ≤ ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k)‖ *
        ‖iteratedFDeriv ℝ l C z‖ := h1
    _ ≤ 1 * ‖iteratedFDeriv ℝ l C z‖ := mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h2

end Term

section Env
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem envelope_real_sum_le (π : ι → ℝ) (L : CycleLetter ι h D) (dom : Set (ℝ × Vec 2)) (J H : ℕ)
    (hL : IsCycleLetter π L dom J H) (x x' : ι) :
    Real.sqrt (π x' / π x) * ∑ o : Finset.Icc 2 D, ∑ k : Fin (L.edge x x' o).length,
      ‖((L.edge x x' o).get k).map‖ *
        ∑ w : DerivativeWord2 (o.1 - 1), ∑ s ∈ Finset.range (L.slow + 1),
          ∑ q ∈ Finset.range (J + 1),
            (jetSupOn dom s q (((L.edge x x' o).get k).coeff w)).toReal ≤ L.majorant x x' := by
  have hE := hL.analytic.2 x x'
  have hm := hL.nonneg x x'
  rw [← ENNReal.ofReal_le_ofReal_iff (by simpa using hm)]
  refine le_trans ?_ (by simpa using hE)
  have hs0 : 0 ≤ Real.sqrt (π x' / π x) := Real.sqrt_nonneg _
  have hj0 : ∀ (o : Finset.Icc 2 D) (k : Fin (L.edge x x' o).length) (w : DerivativeWord2 (o.1 - 1))
      (s q : ℕ), 0 ≤ (jetSupOn dom s q (((L.edge x x' o).get k).coeff w)).toReal :=
    fun _ _ _ _ _ => ENNReal.toReal_nonneg
  have e1 : ENNReal.ofReal (Real.sqrt (π x' / π x) * ∑ o : Finset.Icc 2 D,
      ∑ k : Fin (L.edge x x' o).length, ‖((L.edge x x' o).get k).map‖ *
        ∑ w : DerivativeWord2 (o.1 - 1), ∑ s ∈ Finset.range (L.slow + 1),
          ∑ q ∈ Finset.range (J + 1),
            (jetSupOn dom s q (((L.edge x x' o).get k).coeff w)).toReal) =
      ENNReal.ofReal (Real.sqrt (π x' / π x)) * ∑ o : Finset.Icc 2 D,
      ∑ k : Fin (L.edge x x' o).length, ENNReal.ofReal ‖((L.edge x x' o).get k).map‖ *
        ∑ w : DerivativeWord2 (o.1 - 1), ∑ s ∈ Finset.range (L.slow + 1),
          ∑ q ∈ Finset.range (J + 1),
            ENNReal.ofReal (jetSupOn dom s q (((L.edge x x' o).get k).coeff w)).toReal := by
    rw [ENNReal.ofReal_mul hs0, ENNReal.ofReal_sum_of_nonneg (fun o _ =>
      Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun w _ =>
        Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun q _ => hj0 o k w s q))]
    congr 1
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (norm_nonneg _)
      (Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun q _ => hj0 o k w s q))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_sum_of_nonneg (fun w _ =>
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun q _ => hj0 o k w s q)]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => Finset.sum_nonneg fun q _ => hj0 o k w s q)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => hj0 o k w s q)]
  rw [e1]
  gcongr
  have hs : ∀ f : (ChartedFamily.ofFiber L.edge).Γ x x' → ℝ≥0∞, ∑ γ, f γ =
      ∑ o : Finset.Icc 2 D, ∑ k : Fin (L.edge x x' o).length, f ⟨o, k⟩ := fun f => by
    exact Fintype.sum_sigma f
  rw [hs]
  refine Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun k _ => ?_
  refine mul_le_mul' (ofReal_norm _).le ?_
  have hmem : o.1 ∈ Finset.Icc 2 ((ChartedFamily.ofFiber L.edge).identity x x' ⟨o, k⟩).maxOrder :=
    Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 o.2).1, le_rfl⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun d => ∑ I : DerivativeWord2 (d - 1),
    ∑ r ∈ Finset.range (L.slow + 1), ∑ q ∈ Finset.range (J + 1),
      jetSupFam (fun _ : (ChartedFamily.ofFiber L.edge).Index => dom) r q
        (fun x_6 => (ChartedFamily.ofFiber L.edge).slowFlux 1 x_6.fst x_6.snd x x' ⟨o, k⟩ d I))
    (fun _ _ => bot_le) hmem)
  refine Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun q _ => ?_
  exact ENNReal.ofReal_toReal_le.trans
    (Weighted.ofFiber_jetSupOn_le_jetSupFam L.edge dom x x' o k w r q)

/-- The almost-every-time bounds of all the reserved jets of the constituents of a letter. -/
def LetterGood (L : CycleLetter ι h D) (I : Set ℝ) (J : ℕ) (r : ℝ) : Prop :=
  ∀ (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length),
    ((L.edge v u o).get k).map ≠ 0 → ∀ (w : DerivativeWord2 (o.1 - 1)) (s q : ℕ),
      s ≤ L.slow → q ≤ J → ∀ X z : Vec 2,
        ‖iteratedFDeriv ℝ s (fun X' => iteratedFDeriv ℝ q
          (((L.edge v u o).get k).coeff w r X') z) X‖ ≤
          (jetSupOn (I ×ˢ Set.univ) s q (((L.edge v u o).get k).coeff w)).toReal

theorem letterGood_ae (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (L : CycleLetter ι h D) (I : Set ℝ)
    (J H : ℕ) (hL : IsCycleLetter π L (I ×ˢ Set.univ) J H) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ I → LetterGood L I J r := by
  have per : ∀ (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length)
      (w : DerivativeWord2 (o.1 - 1)) (s q : ℕ), ∀ᵐ r ∂(volume : Measure ℝ), r ∈ I →
        ((L.edge v u o).get k).map ≠ 0 → s ≤ L.slow → q ≤ J → ∀ X z : Vec 2,
          ‖iteratedFDeriv ℝ s (fun X' => iteratedFDeriv ℝ q
            (((L.edge v u o).get k).coeff w r X') z) X‖ ≤
            (jetSupOn (I ×ˢ Set.univ) s q (((L.edge v u o).get k).coeff w)).toReal := by
    intro v u o k w s q
    by_cases hc : ((L.edge v u o).get k).map ≠ 0 ∧ s ≤ L.slow ∧ q ≤ J
    · have hne := Weighted.letter_coefficient_jetSupOn_ne_top π hπ L (I ×ˢ Set.univ) J H hL v u o k
        hc.1 w s q hc.2.1 hc.2.2
      filter_upwards [Weighted.jetSupOn_ae_norm_bound (I ×ˢ Set.univ) s q _ hne] with r hr hrI _ _ _ X z
      exact hr X ⟨hrI, Set.mem_univ X⟩ z
    · exact Filter.Eventually.of_forall fun r _ h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc
  have all := ae_all_iff.2 fun v => ae_all_iff.2 fun u => ae_all_iff.2 fun o =>
    ae_all_iff.2 fun k => ae_all_iff.2 fun w => ae_all_iff.2 fun s => ae_all_iff.2 fun q =>
      per v u o k w s q
  filter_upwards [all] with r hr hrI v u o k hk w s q hs hq
  exact hr v u o k w s q hrI hk hs hq

end Env

section Facts

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- **The term coefficient of a constituent** at a good time: smooth of class `C^J`, periodic, with
jets bounded by the essential mixed jets of the envelope. -/
theorem letter_term_facts (π : ι → ℝ) (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H) (r : ℝ) (hr : r ∈ Set.Icc a b)
    (hg : LetterGood L (Set.Icc a b) J r) (v u : ι) (o : Finset.Icc 2 D)
    (k : Fin (L.edge v u o).length) (hk : ((L.edge v u o).get k).map ≠ 0)
    (w : DerivativeWord2 (o.1 - 1)) (s : ℕ) (hs : s ≤ L.slow) (ω : DerivativeWord2 s)
    (X₀ : Vec 2) (c : Fin 2) :
    ContDiff ℝ (J : ℕ∞) (tbTermCoef (((L.edge v u o).get k).coeff w r) s ω X₀ c) ∧
    AVenhance.IsZ2Periodic (tbTermCoef (((L.edge v u o).get k).coeff w r) s ω X₀ c) ∧
    ∀ l ≤ J, ∀ z, ‖iteratedFDeriv ℝ l (tbTermCoef (((L.edge v u o).get k).coeff w r) s ω X₀ c) z‖ ≤
      (jetSupOn (Set.Icc a b ×ˢ Set.univ) s l (((L.edge v u o).get k).coeff w)).toReal := by
  have hG0 := Weighted.letter_coefficient_joint_contDiff π L a b J H hL v u o k w r hr
  have hG : ContDiff ℝ ((s + J : ℕ) : ℕ∞) (Function.uncurry (((L.edge v u o).get k).coeff w r)) :=
    hG0.of_le (by exact_mod_cast Nat.add_le_add_right hs J)
  have hB : IsBoxSmooth s J (((L.edge v u o).get k).coeff w r) :=
    (Weighted.letter_coefficient_boxSmooth π L a b J H hL v u o k w r hr).mono hs le_rfl
  refine ⟨tbTermCoef_contDiff hG ω X₀ c, tbTermCoef_periodic (((L.edge v u o).get k).periodic w r) ω X₀ c,
    fun l hl z => ?_⟩
  exact (tbTermCoef_jet_le hG hB ω X₀ c l hl z).trans (hg v u o k hk w s l hs hl X₀ z)

end Facts

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! Fourier modes as elements of `TorusHk s ℂ` for every order `s`. -/

local instance quietHsModeMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

/-- The product of the derivative multipliers `2πi n_{w_l}` of an ordered word. -/
def quietHsSymbol {s : ℕ} (n : Fin 2 → ℤ) (a : JetIndex2 s) : ℂ :=
  ∏ l : Fin a.1.val, (2 * (Real.pi : ℂ) * Complex.I) * (n (a.2 l) : ℂ)

theorem quietHsSymbol_value (s : ℕ) (n : Fin 2 → ℤ) :
    quietHsSymbol n (valueIndex2 s) = 1 := by
  unfold quietHsSymbol
  exact Fin.prod_univ_zero _

theorem quietHsSymbol_next {s : ℕ} (n : Fin 2 → ℤ) (j : Fin s) (w : DerivativeWord2 j.val)
    (i : Fin 2) :
    quietHsSymbol n (nextIndex2 j w i) =
      quietHsSymbol n (lowerIndex2 j w) * ((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) := by
  simp only [quietHsSymbol, nextIndex2, nextIndex, lowerIndex2, lowerIndex]
  change ∏ l : Fin (j.val + 1), (2 * (Real.pi : ℂ) * Complex.I) * (n (Fin.snoc (α := fun _ => Fin 2) w i l) : ℂ) = _
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rfl

/-- The raw jet of the smooth periodic function `c e_n`. -/
def quietHsModeJet (s : ℕ) (n : Fin 2 → ℤ) (c : ℂ) : RawJet2 s ℂ := fun a x =>
  c * quietHsSymbol n a * cellComplexFourierMode n x

theorem quietHsModeJet_hasPeriodicWeakJet (s : ℕ) (n : Fin 2 → ℤ) (c : ℂ) :
    HasPeriodicOrderedWeakJet (quietHsModeJet s n c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a k x
    simp only [quietHsModeJet]
    rw [cellComplexFourierMode_periodic n k x]
  · intro a
    exact (cellComplexFourierMode_memLp n).const_mul (c * quietHsSymbol n a)
  · intro j w i e
    have hf : ContDiff ℝ 1 (fun x => (c * quietHsSymbol n (lowerIndex2 j w)) *
        cellComplexFourierMode n x) :=
      contDiff_const.mul ((cellComplexFourierMode_contDiff n).of_le
        (show (1 : WithTop ℕ∞) ≤ ⊤ from le_top))
    have h := smoothVector_weak_coordinate hf i e
    have hd (x : Vec 2) : fderiv ℝ (fun x => (c * quietHsSymbol n (lowerIndex2 j w)) *
        cellComplexFourierMode n x) x (basisVec i) =
        (c * quietHsSymbol n (nextIndex2 j w i)) * cellComplexFourierMode n x := by
      rw [fderiv_const_mul
        (((cellComplexFourierMode_contDiff n).differentiable (by simp)) x),
        smul_apply, cellComplexFourierMode_directional_derivative,
        quietHsSymbol_next]
      simp only [smul_eq_mul]
      ring
    simp_rw [hd] at h
    exact h

/-- The mode `c e_n` as an element of `TorusHk s ℂ`. -/
def quietHsMode (s : ℕ) (n : Fin 2 → ℤ) (c : ℂ) : TorusHk s ℂ :=
  TorusHkFunction.toHk
    { jet := quietHsModeJet s n c
      hasPeriodicWeakJet := quietHsModeJet_hasPeriodicWeakJet s n c }

/-- Every jet coordinate of a mode is a scalar multiple of the Fourier basis vector. -/
theorem quietHsMode_coordinate (s : ℕ) (n : Fin 2 → ℤ) (c : ℂ) (a : JetIndex2 s) :
    (quietHsMode s n c).val a = (c * quietHsSymbol n a) • scalarTorusToCell (mFourierLp 2 n) := by
  have hjet := torusJetToL2_ae (quietHsModeJet s n c)
    (quietHsModeJet_hasPeriodicWeakJet s n c).2.1 a
  change (quietHsMode s n c).val a =ᵐ[volume.restrict AVenhance.unitCube]
    quietHsModeJet s n c a at hjet
  have hval : scalarTorusToCell (mFourierLp 2 n) =ᵐ[volume.restrict AVenhance.unitCube]
      cellComplexFourierMode n := by
    rw [scalarTorusToCell_mode]
    exact (cellComplexFourierMode_memLp n).coeFn_toLp
  apply Lp.ext
  filter_upwards [hjet, hval, Lp.coeFn_smul (c * quietHsSymbol n a)
    (scalarTorusToCell (mFourierLp 2 n))] with x hx hv hsx
  rw [hx, hsx, Pi.smul_apply, hv, smul_eq_mul]
  rfl

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CycleWords AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! Fourier coefficients of the jet coordinates of `TorusHk s ℂ`. -/

section
local instance quietHsCoeffMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

/-- The `H¹` element carrying the pair (derivative word `w`, its first derivatives) of a jet. -/
def quietHsStep {s : ℕ} (f : TorusHk s ℂ) (j : Fin s) (w : DerivativeWord2 j.val) :
    TorusHk 1 ℂ :=
  derivativeTorusHk (K := 1) (r := j.val) w
    (truncateTorusHk (show 1 + j.val ≤ s by have := j.isLt; omega) f)

theorem quietHsStep_index_value {s : ℕ} (j : Fin s) (h : 1 + j.val ≤ s)
    (w : DerivativeWord2 j.val) :
    truncateJetIndex h (prefixJetIndex w (valueIndex2 1)) = lowerIndex2 j w := by
  refine Sigma.ext (Fin.ext (by simp [prefixJetIndex, truncateJetIndex, valueIndex2, valueIndex,
    lowerIndex2, lowerIndex])) (heq_of_eq ?_)
  funext l
  simp [prefixJetIndex, truncateJetIndex, valueIndex2, valueIndex, lowerIndex2, lowerIndex]

theorem quietHsStep_index_next {s : ℕ} (j : Fin s) (h : 1 + j.val ≤ s)
    (w : DerivativeWord2 j.val) (i : Fin 2) :
    truncateJetIndex h (prefixJetIndex w ⟨⟨1, by decide⟩, fun _ => i⟩) = nextIndex2 j w i := by
  refine Sigma.ext (Fin.ext (by simp [prefixJetIndex, truncateJetIndex, nextIndex2, nextIndex])) (heq_of_eq ?_)
  funext l
  simp only [prefixJetIndex, truncateJetIndex, nextIndex2, nextIndex]
  induction l using Fin.lastCases with
  | last =>
      rw [Fin.snoc_last]
      exact Fin.append_right w (fun _ => i) (0 : Fin 1)
  | cast c =>
      rw [Fin.snoc_castSucc]
      exact Fin.append_left w (fun _ => i) c

theorem quietHsStep_value {s : ℕ} (f : TorusHk s ℂ) (j : Fin s) (w : DerivativeWord2 j.val) :
    torusHkValueCLM (quietHsStep f j w) = f.val (lowerIndex2 j w) := by
  change f.val (truncateJetIndex _ (prefixJetIndex w (valueIndex2 1))) = _
  rw [quietHsStep_index_value]

theorem quietHsStep_derivative {s : ℕ} (f : TorusHk s ℂ) (j : Fin s) (w : DerivativeWord2 j.val)
    (i : Fin 2) : cellDerivativeCLM i (quietHsStep f j w) = f.val (nextIndex2 j w i) := by
  change f.val (truncateJetIndex _ (prefixJetIndex w ⟨⟨1, by decide⟩, fun _ => i⟩)) = _
  rw [quietHsStep_index_next]

/-- One derivative multiplies the Fourier coefficient by `2πi n_i`. -/
theorem quietHs_step_coeff {s : ℕ} (f : TorusHk s ℂ) (j : Fin s) (w : DerivativeWord2 j.val)
    (i : Fin 2) (n : Fin 2 → ℤ) :
    mFourierCoeff (scalarCellToTorus (f.val (nextIndex2 j w i))) n =
      ((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) *
        mFourierCoeff (scalarCellToTorus (f.val (lowerIndex2 j w))) n := by
  have h := cellH1_fourierDerivative (quietHsStep f j w) i n
  rwa [quietHsStep_value, quietHsStep_derivative] at h

/-- Every jet coordinate has Fourier coefficient symbol times value coefficient. -/
theorem quietHs_jet_coeff {s : ℕ} (f : TorusHk s ℂ) (n : Fin 2 → ℤ) (a : JetIndex2 s) :
    mFourierCoeff (scalarCellToTorus (f.val a)) n =
      quietHsSymbol n a * mFourierCoeff (scalarCellToTorus (f.val (valueIndex2 s))) n := by
  obtain ⟨⟨j, hj⟩, w⟩ := a
  induction j with
  | zero =>
      have hw : w = Fin.elim0 := Subsingleton.elim _ _
      subst hw
      have : (⟨⟨0, hj⟩, (Fin.elim0 : DerivativeWord2 0)⟩ : JetIndex2 s) = valueIndex2 s := rfl
      rw [this, quietHsSymbol_value, one_mul]
  | succ j ih =>
      have hjs : j < s := by omega
      have hw : w = Fin.snoc (Fin.init w) (w (Fin.last j)) := (Fin.snoc_init_self w).symm
      have hidx : (⟨⟨j + 1, hj⟩, w⟩ : JetIndex2 s) =
          nextIndex2 ⟨j, hjs⟩ (Fin.init w) (w (Fin.last j)) := by
        simp only [nextIndex2, nextIndex, Fin.snoc_init_self]
      have ih' := ih (by omega) (Fin.init w)
      rw [hidx, quietHs_step_coeff]
      change _ = quietHsSymbol n (nextIndex2 ⟨j, hjs⟩ (Fin.init w) (w (Fin.last j))) * _
      rw [quietHsSymbol_next]
      change _ * mFourierCoeff (scalarCellToTorus (f.val ⟨⟨j, _⟩, Fin.init w⟩)) n = _
      rw [ih']
      change _ = (quietHsSymbol n ⟨⟨j, _⟩, Fin.init w⟩ * _) * _
      ring
end

/-! A bounded Fourier multiplier acts on `TorusHk s ℂ` with the same bound. -/

section
local instance quietHsMultiplierMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem quietHs_cellToTorus_toCell (h : ScalarTorusL2) :
    scalarCellToTorus (scalarTorusToCell h) = h :=
  scalarTorusToCell.injective (scalarTorusToCell_scalarCellToTorus _)

theorem quietHs_cellToTorus_norm (f : ComplexCellL2) : ‖scalarCellToTorus f‖ = ‖f‖ := by
  conv_rhs => rw [← scalarTorusToCell_scalarCellToTorus f]
  exact (scalarTorusToCell.norm_map _).symm

/-- A jet whose Fourier coefficients obey the derivative symbols lies in the Sobolev graph. -/
theorem quietHs_mem_graph {s : ℕ} (g : JetIndex2 s → ScalarTorusL2)
    (hg : ∀ a n, mFourierCoeff (g a) n =
      quietHsSymbol n a * mFourierCoeff (g (valueIndex2 s)) n) :
    (WithLp.toLp 2 (fun a => scalarTorusToCell (g a)) :
      JetL2 (volume.restrict AVenhance.unitCube) s ℂ) ∈ torusHkGraph (E := ℂ) s := by
  let c : (Fin 2 → ℤ) → ℂ := fun n => mFourierCoeff (g (valueIndex2 s)) n
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : JetIndex2 s => ComplexCellL2)
  have hpi : HasSum (fun n : Fin 2 → ℤ => fun a : JetIndex2 s =>
      ((quietHsMode s n (c n)).val a)) (fun a => scalarTorusToCell (g a)) := by
    apply Pi.hasSum.mpr
    intro a
    have hs := scalarTorusToCell_fourier_series (g a)
    apply hs.congr_fun
    intro n
    rw [quietHsMode_coordinate, hg a n, mul_comm]
  have h := hpi.mapL e.symm.toContinuousLinearMap
  have hsum : HasSum (fun n : Fin 2 → ℤ => ((quietHsMode s n (c n)).val :
      JetL2 (volume.restrict AVenhance.unitCube) s ℂ))
      (WithLp.toLp 2 (fun a => scalarTorusToCell (g a))) := by
    convert h using 1
    · funext n
      apply PiLp.ext
      intro a
      rfl
    · apply PiLp.ext
      intro a
      rfl
  refine (torusHkGraph (E := ℂ) s).isClosed.mem_of_tendsto hsum
    (Filter.Eventually.of_forall fun F => ?_)
  exact (torusHkGraph (E := ℂ) s).toSubmodule.sum_mem fun n _ =>
    (quietHsMode s n (c n)).property

/-- The Sobolev element with the given coefficient-compatible `L²` jet. -/
def quietHsOfCoeff {s : ℕ} (g : JetIndex2 s → ScalarTorusL2)
    (hg : ∀ a n, mFourierCoeff (g a) n =
      quietHsSymbol n a * mFourierCoeff (g (valueIndex2 s)) n) : TorusHk s ℂ :=
  ⟨WithLp.toLp 2 (fun a => scalarTorusToCell (g a)), quietHs_mem_graph g hg⟩

/-- A bounded Fourier multiplier acts on `H^s` with the same bound. -/
theorem quietHs_multiplier (s : ℕ) (m : (Fin 2 → ℤ) → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ n, ‖m n‖ ≤ M) (w₀ : TorusHk s ℂ) :
    ∃ w : TorusHk s ℂ, (∀ n, mFourierCoeff (scalarCellToTorus (torusHkValueCLM w)) n =
      m n * mFourierCoeff (scalarCellToTorus (torusHkValueCLM w₀)) n) ∧ ‖w‖ ≤ M * ‖w₀‖ := by
  have hex : ∀ a : JetIndex2 s, ∃ h : ScalarTorusL2,
      (∀ n, mFourierCoeff h n = m n * mFourierCoeff (scalarCellToTorus (w₀.val a)) n) ∧
        ‖h‖ ≤ M * ‖scalarCellToTorus (w₀.val a)‖ :=
    fun a => External.exists_torusL2FourierMultiplier m _ M hM hm
  choose g hgc hgn using hex
  have hrel : ∀ a n, mFourierCoeff (g a) n =
      quietHsSymbol n a * mFourierCoeff (g (valueIndex2 s)) n := by
    intro a n
    rw [hgc a n, hgc (valueIndex2 s) n, quietHs_jet_coeff w₀ n a]
    ring
  refine ⟨quietHsOfCoeff g hrel, ?_, ?_⟩
  · intro n
    change mFourierCoeff (scalarCellToTorus (scalarTorusToCell (g (valueIndex2 s)))) n = _
    rw [quietHs_cellToTorus_toCell, hgc]
    rfl
  · have hsq : ‖quietHsOfCoeff g hrel‖ ^ 2 ≤ (M * ‖w₀‖) ^ 2 := by
      have h1 : ‖quietHsOfCoeff g hrel‖ ^ 2 = ∑ a : JetIndex2 s, ‖g a‖ ^ 2 := by
        change ‖(WithLp.toLp 2 (fun a => scalarTorusToCell (g a)) :
          JetL2 (volume.restrict AVenhance.unitCube) s ℂ)‖ ^ 2 = _
        rw [PiLp.norm_sq_eq_of_L2]
        simp only [scalarTorusToCell.norm_map]
      have h0 : ‖w₀‖ ^ 2 = ∑ a : JetIndex2 s, ‖w₀.val a‖ ^ 2 := by
        change ‖w₀.val‖ ^ 2 = _
        rw [PiLp.norm_sq_eq_of_L2]
      rw [h1, mul_pow, h0, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (hgn a).trans_eq (by rw [quietHs_cellToTorus_norm])
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))
      (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
end

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # T1, the `L²` layer: the sharp energy of a real Bloch shift

For a real shift `θ` (`star θ_j = θ_j`) and a divergence-free drift, the drift does no work and the
metric is coercive with constant `1/2`, so the weak dual derivative of the homogeneous cell
equation has `⟪u', u⟫ ≤ -(1/2) ∑_j ‖(∂_j + iθ_j) u‖²` (`cellDualDerivative_real_energy`). With
`‖(∂_j + iθ_j)u‖² ≥ ‖∂_j u‖²/2 - |θ_j|²‖u‖²` (`shiftedDerivative_sq_lower`) and the Poincaré
inequality of a state of small mean, `|⟨u⟩| ≤ δ‖u‖`, the energy decays at the rate
`2π²(1-δ)² - |θ|²` (`cellWeak_small_mean_decay`). No smallness of the drift is used. -/

/-- **The sharp energy of a real shift.** -/
theorem cellDualDerivative_real_energy {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Fin 2 → ℂ) (hθ : ∀ j, star (θ j) = θ j)
    (t : ℝ) (u : TorusHk 1 ℂ) :
    inner ℝ (cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv.1 hb t u 0 0) u ≤
      -((1 / 2) * ∑ j, ‖cellShiftedDerivativeCLM θ j u‖ ^ 2) := by
  have he := cellDualComplexPair_derivative ⟨G, v, θ, 0⟩ hG V hv.1 hb t u u 0 (fun _ => 0)
  rw [cellComplexSource_zero, add_zero] at he
  have hr := congrArg Complex.re he
  rw [cellDualComplexPair_re, cellComplexGenerator_real_diagonal hG hv V hb θ hθ] at hr
  have hc := cellMetricVectorEnergy_coercive hG t (fun j => cellShiftedDerivativeCLM θ j u)
  have hr' : inner ℝ (cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv.1 hb t u 0 0) u =
      -cellMetricVectorEnergy hG t (fun j => cellShiftedDerivativeCLM θ j u) := by
    simpa only [show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using hr
  rw [hr']
  linarith

/-- `‖a + b‖² ≥ ‖a‖²/2 - ‖b‖²`. -/
theorem norm_add_sq_ge_half {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a‖ ^ 2 / 2 - ‖b‖ ^ 2 ≤ ‖a + b‖ ^ 2 := by
  have h1 : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
    calc ‖a‖ = ‖(a + b) + -b‖ := by rw [add_neg_cancel_right]
      _ ≤ ‖a + b‖ + ‖-b‖ := norm_add_le _ _
      _ = ‖a + b‖ + ‖b‖ := by rw [norm_neg]
  have h0 := norm_nonneg a
  have h2 : ‖a‖ ^ 2 ≤ (‖a + b‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
  nlinarith [sq_nonneg (‖a + b‖ - ‖b‖)]

/-- `‖(∂_j + iθ_j)u‖² ≥ ‖∂_j u‖²/2 - |θ_j|²‖u‖²`, summed over `j`. -/
theorem shiftedDerivative_sq_lower (θ : Fin 2 → ℂ) (u : TorusHk 1 ℂ) :
    (1 / 2) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 - (∑ j, ‖θ j‖ ^ 2) * ‖torusHkValueCLM u‖ ^ 2 ≤
      ∑ j, ‖cellShiftedDerivativeCLM θ j u‖ ^ 2 := by
  have hj : ∀ j, ‖cellDerivativeCLM j u‖ ^ 2 / 2 - ‖θ j‖ ^ 2 * ‖torusHkValueCLM u‖ ^ 2 ≤
      ‖cellShiftedDerivativeCLM θ j u‖ ^ 2 := by
    intro j
    have h := norm_add_sq_ge_half (cellDerivativeCLM j u)
      (cellScalarCLM (Complex.I * θ j) (torusHkValueCLM u))
    have hs : ‖cellScalarCLM (Complex.I * θ j) (torusHkValueCLM u)‖ =
        ‖θ j‖ * ‖torusHkValueCLM u‖ := by
      simp [cellScalarCLM, norm_smul]
    rw [hs, mul_pow] at h
    simpa [cellShiftedDerivativeCLM] using h
  calc (1 / 2) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 -
        (∑ j, ‖θ j‖ ^ 2) * ‖torusHkValueCLM u‖ ^ 2
      = ∑ j, (‖cellDerivativeCLM j u‖ ^ 2 / 2 - ‖θ j‖ ^ 2 * ‖torusHkValueCLM u‖ ^ 2) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ _ := Finset.sum_le_sum fun j _ => hj j

/-- **The small-mean gap of a shifted gradient.** -/
theorem shiftedDerivative_small_mean_gap (θ : Fin 2 → ℂ) (u : TorusHk 1 ℂ) (δ : ℝ) (hδ : δ ≤ 1)
    (hm : ‖cellMeanCLM (torusHkValueCLM u)‖ ≤ δ * ‖torusHkValueCLM u‖) :
    (2 * Real.pi ^ 2 * (1 - δ) ^ 2 - ∑ j, ‖θ j‖ ^ 2) * ‖torusHkValueCLM u‖ ^ 2 ≤
      ∑ j, ‖cellShiftedDerivativeCLM θ j u‖ ^ 2 := by
  have hg := cellSmallMean_gradient_gap u δ hδ hm
  have hl := shiftedDerivative_sq_lower θ u
  nlinarith

/-- **Exponential decay of a weak curve of small mean.** If the homogeneous solution of a real
shift keeps `|⟨u⟩| ≤ δ‖u‖`, its energy decays at the rate `2π²(1-δ)² - |θ|²`. -/
theorem cellWeak_small_mean_decay {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (hθ : ∀ j, star (θ j) = θ j) (δ : ℝ) (hδ : δ ≤ 1)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv.1 hb t (slice t) 0 0))
    (hm : ∀ t ∈ Icc a b, ‖cellMeanCLM (u t)‖ ≤ δ * ‖u t‖) :
    Real.exp ((2 * Real.pi ^ 2 * (1 - δ) ^ 2 - ∑ j, ‖θ j‖ ^ 2) * (b - a)) * ‖u b‖ ^ 2 ≤
      ‖u a‖ ^ 2 := by
  set c := 2 * Real.pi ^ 2 * (1 - δ) ^ 2 - ∑ j, ‖θ j‖ ^ 2 with hc
  have hw := (h.energy_strongTime hab).scalar_weighted_bound hab c (fun _ => 0) (fun _ => 0)
    intervalIntegrable_const intervalIntegrable_const (by
      filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
      have hmt := hm t hti
      rw [ht] at hmt ⊢
      have he := cellDualDerivative_real_energy hG hv V hb θ hθ t (slice t)
      have hgap := shiftedDerivative_small_mean_gap θ (slice t) δ hδ hmt
      linarith)
  simpa using hw

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
open MeasureTheory Homogenization
namespace AVRegularity.CycleWords.Assembly

/-! # Powers and dilations of the low cutoff

The retained amplitudes are cut off at the end, while the datum norms carry a cutoff inside the
frequency derivatives. These are compatible only when the amplitude cutoff is a power
`χ_r^{n+1} χ₃` of the norm cutoff `χ_r`, `n` the number of frequency derivatives that reach the
datum (`χ^{j+1} ∂^j g = ∑_{i ≤ j} c_{ij} ∂^i(χ g)`). Two instances are used:

* `χ_lo = χ_lo(·/2)^{N} χ_lo` (`IsLowCutoff.eq_dilate_pow_mul`): the dilated cutoff is one on the
  support of `χ_lo`, for the statements that only integrate the datum norms;
* `χ_lo^{N+1}` is again a low cutoff (`IsLowCutoff.pow`), for the Gaussian amplitude bound with
  `χ_lo` itself inside the datum norm. -/

/-- The cutoff `χ_lo` has compact support. -/
theorem IsLowCutoff.hasCompactSupport {K : ScalarConstants} {χlo : Vec 2 → ℝ}
    (hχ : IsLowCutoff K χlo) : HasCompactSupport χlo := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec 2) (2 * K.ξlo)) fun ξ hξ => ?_
  refine hχ.supp ξ ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hξ
  refine hξ.le.trans ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => ξ j * ξ j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

theorem sqrt_vecDot_smul (s : ℝ) (θ : Vec 2) :
    Real.sqrt (vecDot (s • θ) (s • θ)) = |s| * Real.sqrt (vecDot θ θ) := by
  have h : vecDot (s • θ) (s • θ) = s ^ 2 * vecDot θ θ := by
    simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]

/-- A compactly supported smooth function has bounded derivatives. -/
theorem exists_bound_iteratedFDeriv_of_hasCompactSupport {χ : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (k : ℕ) :
    ∃ B : ℝ, ∀ θ, ‖iteratedFDeriv ℝ k χ θ‖ ≤ B :=
  (hχ.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)
    ).bounded_above_of_compact_support (hc.iteratedFDeriv k)

/-- A compactly supported smooth function composed with a dilation has bounded derivatives. -/
theorem exists_bound_iteratedFDeriv_comp_smul {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (κ : ℝ) (k : ℕ) :
    ∃ B : ℝ, ∀ θ, ‖iteratedFDeriv ℝ k (fun θ => χ (κ • θ)) θ‖ ≤ B := by
  obtain ⟨B0, hB0⟩ := exists_bound_iteratedFDeriv_of_hasCompactSupport hχ hc k
  refine ⟨B0 * ‖κ • ContinuousLinearMap.id ℝ (Vec 2)‖ ^ k, fun θ => ?_⟩
  have h : (fun θ : Vec 2 => χ (κ • θ)) = χ ∘ (κ • ContinuousLinearMap.id ℝ (Vec 2)) := by
    funext θ
    simp
  rw [h, (κ • ContinuousLinearMap.id ℝ (Vec 2)).iteratedFDeriv_comp_right hχ θ
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (hB0 _) (by positivity)

/-- The constant `1` has bounded derivatives. -/
theorem exists_bound_iteratedFDeriv_const_one (k : ℕ) :
    ∃ B : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k (fun _ : Vec 2 => (1 : ℝ)) ξ‖ ≤ B := by
  refine ⟨1, fun ξ => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne hk.ne']
    simp

/-- A positive power of a low cutoff is a low cutoff. -/
theorem IsLowCutoff.pow {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (N : ℕ) : IsLowCutoff K (fun ξ => χlo ξ ^ (N + 1)) where
  smooth := hχ.smooth.pow _
  even ξ := by simp only [hχ.even]
  one ξ hξ := by simp only [hχ.one ξ hξ, one_pow]
  supp ξ hξ := by simp only [hχ.supp ξ hξ, ne_eq, Nat.add_one_ne_zero, not_false_eq_true,
    zero_pow]

/-- The dilated low cutoff. -/
theorem IsLowCutoff.dilate_smooth {K : ScalarConstants} {χlo : Vec 2 → ℝ}
    (hχ : IsLowCutoff K χlo) : ContDiff ℝ (⊤ : ℕ∞) (fun ξ => χlo ((2 : ℝ)⁻¹ • ξ)) :=
  hχ.smooth.comp (contDiff_const_smul _)

theorem IsLowCutoff.dilate_hasCompactSupport {K : ScalarConstants} {χlo : Vec 2 → ℝ}
    (hχ : IsLowCutoff K χlo) : HasCompactSupport (fun ξ => χlo ((2 : ℝ)⁻¹ • ξ)) :=
  hχ.hasCompactSupport.comp_smul (inv_ne_zero two_ne_zero)

/-- The dilated cutoff `χ_lo(ξ/2)` is one on the support of `χ_lo`. -/
theorem IsLowCutoff.eq_dilate_pow_mul {K : ScalarConstants} {χlo : Vec 2 → ℝ}
    (hχ : IsLowCutoff K χlo) (N : ℕ) (ξ : Vec 2) :
    χlo ξ = χlo ((2 : ℝ)⁻¹ • ξ) ^ N * χlo ξ := by
  by_cases h : 2 * K.ξlo ≤ Real.sqrt (vecDot ξ ξ)
  · rw [hχ.supp ξ h, mul_zero]
  · rw [hχ.one ((2 : ℝ)⁻¹ • ξ) ?_, one_pow, one_mul]
    rw [sqrt_vecDot_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    linarith [not_le.mp h]

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # Linear combinations of word chains

A linear combination of two solutions of the coupled plane system with the same coefficients is a
solution with the combined data (`isCoupledWeakSolutionPlane_combination`); word chains at two
descending slot assignments truncate to their minimum (`wordChainFrom_truncate`) and combine there
(`chainCombination`). -/

universe u v

section Combination

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The jets of a combination of carrier elements are a.e. the combination of the jets. -/
theorem planeJet_combination_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} (a b : ℝ)
    (U U' : PlaneHk Set.univ K E) (j : JetIndex2 K) :
    (a • U + b • U').toFunction.jet j =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
      fun x => a • U.toFunction.jet j x + b • U'.toFunction.jet j x := by
  filter_upwards [KernelEnergyPlane.planeJet_add_ae (a • U) (b • U') j,
    KernelEnergyPlane.planeJet_smul_ae a U j, KernelEnergyPlane.planeJet_smul_ae b U' j]
    with x hx ha hb
  rw [hx, ha, hb]

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
/-- The coupling flux of a combination of jets is the combination of the coupling fluxes. -/
theorem flux_sum_combination_of_jets {D : ℕ} {K : ι → ℕ} (i : ι)
    (A : ∀ (i' : ι) (d : admissibleOrders K D i i'),
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (a b : ℝ)
    (J J₁ J₂ : ∀ (i' : ι) (d : admissibleOrders K D i i'), DerivativeWord2 (d.1 - 1) → h i')
    (hJ : ∀ i' d word, J i' d word = a • J₁ i' d word + b • J₂ i' d word) :
    ∑ i' : ι, ∑ d : admissibleOrders K D i i', A i' d (WithLp.toLp 2 (J i' d)) =
      a • (∑ i' : ι, ∑ d : admissibleOrders K D i i', A i' d (WithLp.toLp 2 (J₁ i' d))) +
        b • ∑ i' : ι, ∑ d : admissibleOrders K D i i', A i' d (WithLp.toLp 2 (J₂ i' d)) := by
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hfun : J i' d = a • J₁ i' d + b • J₂ i' d := funext (hJ i' d)
  rw [hfun, WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul, map_add, map_smul, map_smul]

/-- **Linear combinations of plane solutions.** -/
theorem isCoupledWeakSolutionPlane_combination {ν t₀ t₁ : ℝ} {v : ℝ → Vec 2 → Vec 2} {D : ℕ}
    {K : ι → ℕ}
    {A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {f f' : ∀ i, PlaneHk Set.univ (K i) (h i)}
    {F F' : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g g' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)} {u u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
    {w w' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}
    (hsol : IsCoupledWeakSolutionPlane ν t₀ t₁ v D K A f F g u w)
    (hsol' : IsCoupledWeakSolutionPlane ν t₀ t₁ v D K A f' F' g' u' w') (a b : ℝ) :
    IsCoupledWeakSolutionPlane ν t₀ t₁ v D K A (fun i => a • f i + b • f' i)
      (fun i s => a • F i s + b • F' i s) (fun i s => a • g i s + b • g' i s)
      (fun i s => a • u i s + b • u' i s) (fun i s => a • w i s + b • w' i s) := by
  refine ⟨fun i => ((hsol.1 i).const_smul a).add ((hsol'.1 i).const_smul b),
    fun i => ((hsol.2.1 i).const_smul a).add ((hsol'.2.1 i).const_smul b), ?_, ?_, ?_⟩
  · intro i
    filter_upwards [hsol.2.2.1 i, hsol'.2.2.1 i] with s hs hs'
    show truncatePlaneHk (Nat.le_succ (K i)) (a • w i s + b • w' i s) = a • u i s + b • u' i s
    rw [map_add, map_smul, map_smul, hs, hs']
  · intro i
    show a • u i t₀ + b • u' i t₀ = a • f i + b • f' i
    rw [hsol.2.2.2.1 i, hsol'.2.2.2.1 i]
  · intro i t ht φ
    have hd := CycleJointProofs.coupledWeakIdentity_add _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (CycleJointProofs.coupledWeakIdentity_smul _ a _ _ _ _ _ _ _ _ _ _ _ _
        (hsol.2.2.2.2 i t ht φ))
      (CycleJointProofs.coupledWeakIdentity_smul _ b _ _ _ _ _ _ _ _ _ _ _ _
        (hsol'.2.2.2.2 i t ht φ))
    refine CycleJointProofs.coupledWeakIdentity_integrands_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ ?_ ?_ ?_ hd
    · filter_upwards [planeJet_combination_ae a b (u i t) (u' i t) (valueIndex2 (K i))]
        with x hx
      simp only [Pi.add_apply, Pi.smul_apply, hx]
    · filter_upwards [planeJet_combination_ae a b (f i) (f' i) (valueIndex2 (K i))] with x hx
      simp only [Pi.add_apply, Pi.smul_apply, hx]
    · intro s _
      refine CycleJointProofs.weakIdentityRhs_congr_ae _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
        ?_ ?_ ?_ ?_
      · intro k
        filter_upwards [planeJet_combination_ae a b (w i s) (w' i s)
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩] with x hx
        simp only [Pi.add_apply, Pi.smul_apply, hx]
      · have hall : ∀ᵐ x ∂(volume.restrict (Set.univ : Set (Vec 2))), ∀ i' : ι, ∀ j,
            (a • w i' s + b • w' i' s).toFunction.jet j x =
              a • (w i' s).toFunction.jet j x + b • (w' i' s).toFunction.jet j x :=
          ae_all_iff.mpr fun i' => ae_all_iff.mpr fun j =>
            planeJet_combination_ae a b (w i' s) (w' i' s) j
        filter_upwards [hall] with x hx
        simp only [Pi.add_apply, Pi.smul_apply]
        symm
        apply flux_sum_combination_of_jets i (fun i' d => A i i' d s x) a b
        intro i' d word
        exact hx i' _
      · filter_upwards [planeJet_combination_ae a b (F i s) (F' i s) (valueIndex2 (K i))]
          with x hx
        simp only [Pi.add_apply, Pi.smul_apply, hx]
      · filter_upwards [planeJet_combination_ae a b (g i s) (g' i s) (valueIndex2 (K i))]
          with x hx
        simp only [Pi.add_apply, Pi.smul_apply, hx]

end Combination

section Chain

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {N : ℕ}

/-- The level data of a chain started from `f`: `f` at level `0`, `0` above. -/
noncomputable def chainDatum (κ : Fin (N + 1) → ι → ℕ) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)) :
    ∀ j x, PlaneHk Set.univ (κ j x) (h x) :=
  fun j x => if hj : j = 0 then (by subst hj; exact f x) else 0

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem chainDatum_zero (κ : Fin (N + 1) → ι → ℕ) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (x : ι) : chainDatum κ f 0 x = f x := by
  simp only [chainDatum, ↓reduceDIte]

theorem isPlaneChain_iff_from {D : ℕ} (cd : PlaneChainData ι h D N) (κ : Fin (N + 1) → ι → ℕ)
    (t₀ t₁ : ℝ) (v : ℝ → Vec 2 → Vec 2) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (F : ∀ (j : Fin (N + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (u : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)) :
    IsPlaneChain cd κ t₀ t₁ v f F u w ↔ IsPlaneChainFrom cd κ t₀ t₁ v (chainDatum κ f) F u w :=
  Iff.rfl

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The combined truncated datum is the datum of the combined truncated initial value. -/
theorem chainDatum_combination (κ κ'' : Fin (N + 1) → ι → ℕ) (κ' : Fin (N + 1) → ι → ℕ)
    (hle : ∀ j x, κ'' j x ≤ κ j x) (hle' : ∀ j x, κ'' j x ≤ κ' j x)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)) (f' : ∀ x, PlaneHk Set.univ (κ' 0 x) (h x))
    (a b : ℝ) :
    (fun j x => a • truncatePlaneHk (hle j x) (chainDatum κ f j x) +
        b • truncatePlaneHk (hle' j x) (chainDatum κ' f' j x)) =
      chainDatum κ'' (fun x => a • truncatePlaneHk (hle 0 x) (f x) +
        b • truncatePlaneHk (hle' 0 x) (f' x)) := by
  funext j x
  by_cases hj : j = 0
  · subst hj
    simp only [chainDatum, ↓reduceDIte]
  · simp only [chainDatum, hj, ↓reduceDIte, ContinuousLinearMap.map_zero, smul_zero,
      add_zero]

/-- Linear combinations of plane solutions, with the combined data given explicitly. -/
theorem isCoupledWeakSolutionPlane_combination_of_eq {ν t₀ t₁ : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {D : ℕ} {K : ι → ℕ}
    {A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {f f' f'' : ∀ i, PlaneHk Set.univ (K i) (h i)}
    {F F' F'' : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g g' g'' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
    {u u' u'' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
    {w w' w'' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}
    (hsol : IsCoupledWeakSolutionPlane ν t₀ t₁ v D K A f F g u w)
    (hsol' : IsCoupledWeakSolutionPlane ν t₀ t₁ v D K A f' F' g' u' w') (a b : ℝ)
    (hf'' : f'' = fun i => a • f i + b • f' i)
    (hF'' : F'' = fun i s => a • F i s + b • F' i s)
    (hg'' : g'' = fun i s => a • g i s + b • g' i s)
    (hu'' : u'' = fun i s => a • u i s + b • u' i s)
    (hw'' : w'' = fun i s => a • w i s + b • w' i s) :
    IsCoupledWeakSolutionPlane ν t₀ t₁ v D K A f'' F'' g'' u'' w'' := by
  rw [hf'', hF'', hg'', hu'', hw'']
  exact isCoupledWeakSolutionPlane_combination hsol hsol' a b

/-- Linear combinations of chains with all level data at the same slots. -/
theorem planeChainFrom_combination {D : ℕ} {cd : PlaneChainData ι h D N}
    {κ : Fin (N + 1) → ι → ℕ} {t₀ t₁ : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {f₁ f₂ : ∀ j x, PlaneHk Set.univ (κ j x) (h x)}
    {F₁ F₂ : ∀ (j : Fin (N + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x))}
    {u₁ u₂ : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x)}
    {w₁ w₂ : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)}
    (hs : IsPlaneChainFrom cd κ t₀ t₁ v f₁ F₁ u₁ w₁)
    (hs' : IsPlaneChainFrom cd κ t₀ t₁ v f₂ F₂ u₂ w₂) (a b : ℝ) :
    IsPlaneChainFrom cd κ t₀ t₁ v (fun j x => a • f₁ j x + b • f₂ j x)
      (fun j x s => a • F₁ j x s + b • F₂ j x s) (fun j x s => a • u₁ j x s + b • u₂ j x s)
      (fun j x s => a • w₁ j x s + b • w₂ j x s) :=
  isCoupledWeakSolutionPlane_combination_of_eq hs hs' a b rfl rfl
    (funext fun _ => funext fun _ => by simp) rfl rfl

/-- Chains transfer along equal data. -/
theorem IsPlaneChainFrom.congr_data {D : ℕ} {cd : PlaneChainData ι h D N}
    {κ : Fin (N + 1) → ι → ℕ} {t₀ t₁ : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {f f' : ∀ j x, PlaneHk Set.univ (κ j x) (h x)}
    {F F' : ∀ (j : Fin (N + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x))}
    {u : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x)}
    {w : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)}
    (hs : IsPlaneChainFrom cd κ t₀ t₁ v f F u w) (hf : f = f') (hF : F = F') :
    IsPlaneChainFrom cd κ t₀ t₁ v f' F' u w := hf ▸ hF ▸ hs

/-- The value of a combination of truncations is a.e. the combination of the values. -/
theorem planeValue_truncate_combination_ae {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L L' : ℕ}
    (hL : K ≤ L) (hL' : K ≤ L') (a b : ℝ) (U : PlaneHk Set.univ L E)
    (U' : PlaneHk Set.univ L' E) :
    planeValue (a • truncatePlaneHk hL U + b • truncatePlaneHk hL' U') =ᵐ[volume]
      fun z => a • planeValue U z + b • planeValue U' z := by
  have hT : planeValue (truncatePlaneHk hL U) = planeValue U :=
    planeJetOrder_truncate hL (Nat.zero_le K) U _
  have hT' : planeValue (truncatePlaneHk hL' U') = planeValue U' :=
    planeJetOrder_truncate hL' (Nat.zero_le K) U' _
  filter_upwards [planeValue_add_ae (a • truncatePlaneHk hL U) (b • truncatePlaneHk hL' U'),
    planeValue_smul_ae a (truncatePlaneHk hL U), planeValue_smul_ae b (truncatePlaneHk hL' U')]
    with z h1 h2 h3
  rw [h1, h2, h3, hT, hT']

/-- **Linear combinations of word chains** (`ChainCombinationStatement`). -/
theorem chainCombination : ChainCombinationStatement.{u, v} := by
  intro ι _ h _ _ _ _ _ _ D N letters G v X₀ δ t₀ t₁ κ κ' hD hκ hκ' f u w f' u' w' hs hs' a b
  have hle : ∀ j x, min (κ j x) (κ' j x) ≤ κ j x := fun j x => min_le_left _ _
  have hle' : ∀ j x, min (κ j x) (κ' j x) ≤ κ' j x := fun j x => min_le_right _ _
  have hκ'' : IsWordSlots letters fun j x => min (κ j x) (κ' j x) := by
    intro j x y o hne
    have h1 := hκ j x y o hne
    have h2 := hκ' j x y o hne
    show min (κ j.succ x) (κ' j.succ x) + o.1 ≤ min (κ j.castSucc y) (κ' j.castSucc y) + 2
    omega
  have hT := wordChainFrom_truncate hD G letters κ (fun j x => min (κ j x) (κ' j x)) hle hκ hκ''
    X₀ δ t₀ t₁ v (chainDatum κ f) (fun _ _ _ => 0) u w hs
  have hT' := wordChainFrom_truncate hD G letters κ' (fun j x => min (κ j x) (κ' j x)) hle' hκ'
    hκ'' X₀ δ t₀ t₁ v (chainDatum κ' f') (fun _ _ _ => 0) u' w' hs'
  have hC := planeChainFrom_combination hT hT' a b
  refine ⟨fun x => a • truncatePlaneHk (hle 0 x) (f x) + b • truncatePlaneHk (hle' 0 x) (f' x),
    fun j x t => a • truncatePlaneHk (hle j x) (u j x t) +
      b • truncatePlaneHk (hle' j x) (u' j x t),
    fun j x t => a • truncatePlaneHk (Nat.succ_le_succ (hle j x)) (w j x t) +
      b • truncatePlaneHk (Nat.succ_le_succ (hle' j x)) (w' j x t), ?_, fun x => ?_, fun x => ?_⟩
  · refine (isPlaneChain_iff_from _ _ _ _ _ _ _ _ _).2 (IsPlaneChainFrom.congr_data hC
      (chainDatum_combination κ _ κ' hle hle' f f' a b) ?_)
    funext j x s
    simp only [ContinuousLinearMap.map_zero, smul_zero, add_zero]
  · exact planeValue_truncate_combination_ae (hle 0 x) (hle' 0 x) a b (f x) (f' x)
  · exact planeValue_truncate_combination_ae (hle (Fin.last N) x) (hle' (Fin.last N) x) a b
      (u (Fin.last N) x t₁) (u' (Fin.last N) x t₁)

end Chain

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Homogenization
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Periodized sources in `L²` from iterated bounds (generic part)

On a product measure the lower integral is at most the iterated one (`lintegral_prod_le`, no
measurability). So an a.e.-strongly measurable periodic part of a time-dependent field is in
`L²([a,b] × cell)` as soon as each time slice is measurable and the iterated weighted integral is
finite. The joint measurability is a hypothesis: for the literal sources of the amplitude
identification it is not available (plane values are chosen time by time), so it is applied to
measurable representatives.

The weighted integrals are handled by the Cauchy–Schwarz bound for finite sums
(`sq_sum_le_card_mul`) and the comparison of the lattice weight times a moment weight with the
chart weight `(1 + ϖ²|y|²)^N`. -/

/-- Cauchy–Schwarz for a finite sum: `(∑ a_i)² ≤ n ∑ a_i²`. -/
theorem sq_sum_le_card_mul {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ s, a i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, a i ^ 2 :=
  sq_sum_le_card_mul_sum_sq

end AVRegularity.CycleWords.Assembly
end
end
end
