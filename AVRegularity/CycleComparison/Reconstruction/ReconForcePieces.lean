-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.ReconSplitBill
import AVRegularity.CycleComparison.Reconstruction.ReconChains
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Jets of the classical representative and of its Galerkin errors**. The jets
of order `i ≤ r` of a classical representative `aRep(t)` of `W(t) ∈ H^K`, `r + 2 ≤ K`, are bounded
by a fixed multiple of a bound of the norms of `W(t)` (`classicalRep_family_iteratedFDeriv_le`),
and those of `a_n(t) - aRep(t)` by the Galerkin errors `‖S_n W(t) - W(t)‖`
(`coarseTraj_sub_rep_iteratedFDeriv_le`). -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

omit [DecidableEq ι] in
/-- **The jets of a classical representative of a family** are bounded by the norms. -/
theorem classicalRep_family_iteratedFDeriv_le {K r : ℕ} (hr : r + 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ∀ v, TorusHk K (h v)) (a : Vec 2 → ∀ i, h i),
      (∀ v, IsClassicalRep (V v) (fun x => a x v) r) → ∀ {B : ℝ}, 0 ≤ B →
      (∀ v, ‖V v‖ ≤ B) → ∀ i ≤ r, ∀ x, ‖iteratedFDeriv ℝ i a x‖ ≤ C * B := by
  choose C hC hb using fun v : ι => classicalRep_iteratedFDeriv_le (E := h v) K r hr
  refine ⟨∑ v, C v, Finset.sum_nonneg fun v _ => hC v, fun V a ha B hB hV i hi x => ?_⟩
  have hac : ContDiff ℝ (i : ℕ∞) a := contDiff_pi.2 fun v => isClassicalRep_contDiff_of_le (ha v) hi
  refine norm_iteratedFDeriv_le_of_apply_le hac x
    (mul_nonneg (Finset.sum_nonneg fun v _ => hC v) hB) fun v => ?_
  refine (hb v (V v) _ (ha v) i hi x).trans ?_
  refine (mul_le_mul_of_nonneg_left (hV v) (hC v)).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := C) (fun v _ => hC v)
    (Finset.mem_univ v)) hB

/-- **The jets of the Galerkin errors of a classical representative** are bounded by the norms of
the Galerkin errors of the field. -/
theorem coarseTraj_sub_rep_iteratedFDeriv_le {K r : ℕ} (hr : r + 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (W : ∀ v, ℝ → TorusHk K (h v)) (aRep : ℝ → Vec 2 → ∀ i, h i)
      (t : ℝ), (∀ v, IsClassicalRep (W v t) (fun x => aRep t x v) r) → ∀ {B : ℝ}, 0 ≤ B →
      (∀ v, ‖galerkinProj n (W v t) - W v t‖ ≤ B) → ∀ i ≤ r, ∀ x,
        ‖iteratedFDeriv ℝ i (fun y => coarseTraj n W t y - aRep t y) x‖ ≤ C * B := by
  choose C hC hb using fun v : ι => classicalRep_iteratedFDeriv_sub_le (E := h v) K r hr
  refine ⟨∑ v, C v, Finset.sum_nonneg fun v _ => hC v,
    fun n W aRep t ha B hB hW i hi x => ?_⟩
  have hac : ContDiff ℝ (i : ℕ∞) (aRep t) :=
    contDiff_pi.2 fun v => isClassicalRep_contDiff_of_le (ha v) hi
  refine norm_iteratedFDeriv_le_of_apply_le (((coarseTraj_contDiff n W t).of_le
    (by exact_mod_cast le_top)).sub hac) x
    (mul_nonneg (Finset.sum_nonneg fun v _ => hC v) hB) fun v => ?_
  have hrep : IsClassicalRep (galerkinProj n (W v t))
      (fun y => coarseApprox n (fun u => W u t) y v) r :=
    coarseApprox_isClassicalRep n (fun u => W u t) v (by omega)
  have he : (fun y => (coarseTraj n W t y - aRep t y) v) = fun y =>
      coarseApprox n (fun u => W u t) y v - aRep t y v := by
    rw [coarseTraj_eq]
    rfl
  rw [he]
  refine (hb v _ _ _ _ hrep (ha v) i hi x).trans ?_
  refine (mul_le_mul_of_nonneg_left (hW v) (hC v)).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := C) (fun v _ => hC v)
    (Finset.mem_univ v)) hB

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open scoped Topology
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The commutator remainder of the Galerkin approximants tends to zero**.
At a fixed time `s`, the commutator remainder `e_n = S_n g₁(aRep) - g₁(a_n)` (`defectRemainder`) of the approximants `a_n = S_n W(s)`
(`coarseTraj`) splits as `(S_n G - G) + g₁(aRep - a_n)`, `G = g₁(aRep)`, by linearity of the
classical defect field `g₁` (`classicalDefectField_sub`, `defectRemainder_apply_eq`).

* The Galerkin projection of the field `G` is the approximant of its carrier in `H^{M+2}`
  (`coarseProjField_eq_coarseApprox`), hence a classical representative of the Galerkin cutoff
  of that carrier (`coarseProjField_isClassicalRep`); with `H^{M+2}(𝕋²) ⊂ C^M` the jets of order
  `≤ M` of `S_n G - G` tend to zero.
* The jets of order `≤ M` of `g₁(aRep - a_n)` are bounded by those of order `≤ M + D` of
  `aRep - a_n` (`classicalDefectField_jetBounded`), which tend to zero by `H^K ⊂ C^{M+D}`.

Hence the jets of order `≤ M` of `e_n` tend to zero uniformly in space
(`defectRemainder_jet_tendsto`), and they are bounded uniformly in `n` by a constant times the
coefficient bound and the norm of `W(s)` (`defectRemainder_jet_le`). The embedding
`H^{M+2} ⊂ C^M` needs `G ∈ C^{M+2}`: the drift is taken of class `C^{M+2}` and the coefficients
`A_d`, `C^{[r]}` of class `C^{M+3}`. -/

/-- A periodic field of class `C^K` is a classical representative of its carrier at every
order `r ≤ K`. -/
theorem periodicHk_isClassicalRep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] (K : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) {r : ℕ} (hr : r ≤ K) :
    IsClassicalRep (periodicHk K f hf hp) f r := by
  refine ⟨hr, hf.of_le (by exact_mod_cast hr), hp, fun m hm w => ?_⟩
  exact (AVRegularity.CycleComparison.Assembly.torusJetOrder_ae (periodicHk K f hf hp)
    (hm.trans hr) w).trans
    (periodicHk_jet_ae K f hf hp ⟨⟨m, Nat.lt_succ_of_le (hm.trans hr)⟩, w⟩)

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

omit [DecidableEq ι] in
/-- **Jets of a classical representative**, uniformly: a field whose components are classical
representatives at order `r` of fields of `H^K` of norm `≤ B`, `r + 2 ≤ K`, has jets of order
`≤ r` bounded by `C B`. -/
theorem classicalRep_pi_jetBounded {K r : ℕ} (hr : r + 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ∀ v, TorusHk K (h v)) (a : Vec 2 → ∀ i, h i) (B : ℝ), 0 ≤ B →
      (∀ v, IsClassicalRep (V v) (fun x => a x v) r) → (∀ v, ‖V v‖ ≤ B) →
        JetBoundedBy r a (C * B) := by
  choose C hC hb using fun v : ι => classicalRep_iteratedFDeriv_le (E := h v) K r hr
  have hC0 : 0 ≤ ∑ v, C v := Finset.sum_nonneg fun v _ => hC v
  refine ⟨∑ v, C v, hC0, fun V a B hB ha hV => ?_⟩
  refine JetBoundedBy.of_components (mul_nonneg hC0 hB) fun v =>
    ⟨(ha v).2.1, fun i hi x => (hb v _ _ (ha v) i hi x).trans ?_⟩
  exact mul_le_mul (Finset.single_le_sum (f := C) (fun v _ => hC v) (Finset.mem_univ v)) (hV v)
    (norm_nonneg _) hC0

omit [DecidableEq ι] in
/-- **Jets of a difference of classical representatives**, uniformly. -/
theorem classicalRep_pi_sub_jetBounded {K r : ℕ} (hr : r + 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V V' : ∀ v, TorusHk K (h v)) (a a' : Vec 2 → ∀ i, h i) (B : ℝ),
      0 ≤ B → (∀ v, IsClassicalRep (V v) (fun x => a x v) r) →
      (∀ v, IsClassicalRep (V' v) (fun x => a' x v) r) → (∀ v, ‖V v - V' v‖ ≤ B) →
        JetBoundedBy r (fun x => a x - a' x) (C * B) := by
  choose C hC hb using fun v : ι => classicalRep_iteratedFDeriv_sub_le (E := h v) K r hr
  have hC0 : 0 ≤ ∑ v, C v := Finset.sum_nonneg fun v _ => hC v
  refine ⟨∑ v, C v, hC0, fun V V' a a' B hB ha ha' hV => ?_⟩
  have hc : ContDiff ℝ (r : ℕ∞) (fun x => a x - a' x) :=
    (contDiff_pi.2 fun v => (ha v).2.1).sub (contDiff_pi.2 fun v => (ha' v).2.1)
  refine JetBoundedBy.of_components (mul_nonneg hC0 hB) fun v =>
    ⟨contDiff_pi.1 hc v, fun i hi x => (hb v _ _ _ _ (ha v) (ha' v) i hi x).trans ?_⟩
  exact mul_le_mul (Finset.single_le_sum (f := C) (fun v _ => hC v) (Finset.mem_univ v)) (hV v)
    (norm_nonneg _) hC0

/-- The Galerkin projection of a periodic family of class `C^K` is the approximant of its
carrier. -/
theorem coarseProjField_eq_coarseApprox (n K : ℕ) (g : ∀ v, Vec 2 → h v)
    (hg : ∀ v, ContDiff ℝ (K : ℕ∞) (g v)) (hgp : ∀ v, AVenhance.IsZ2Periodic (g v))
    (x : Vec 2) :
    coarseProjField n g x = coarseApprox n (fun v => periodicHk K (g v) (hg v) (hgp v)) x := by
  unfold coarseProjField coarseApprox
  refine Finset.sum_congr rfl fun r _ => congrArg (· • coarseMode n r x) ?_
  unfold coarseModeCoeff
  refine integral_congr_ae ?_
  filter_upwards [periodicHk_value_ae K (g r.1) (hg r.1) (hgp r.1)] with y hy
  exact congrArg (fun z => inner ℝ z (coupledModeJet n r r.1 0 Fin.elim0 y)) hy.symm

/-- The Galerkin projection of a periodic family of class `C^K` is a classical representative of
the Galerkin cutoff of its carrier at every order `r ≤ K`. -/
theorem coarseProjField_isClassicalRep (n K : ℕ) (g : ∀ v, Vec 2 → h v)
    (hg : ∀ v, ContDiff ℝ (K : ℕ∞) (g v)) (hgp : ∀ v, AVenhance.IsZ2Periodic (g v)) {r : ℕ}
    (hr : r ≤ K) (v : ι) :
    IsClassicalRep (galerkinProj n (periodicHk K (g v) (hg v) (hgp v)))
      (fun x => coarseProjField n g x v) r := by
  have he : (fun x => coarseProjField n g x v) =
      fun x => coarseApprox n (fun v => periodicHk K (g v) (hg v) (hgp v)) x v :=
    funext fun x => by rw [coarseProjField_eq_coarseApprox n K g hg hgp x]
  rw [he]
  exact coarseApprox_isClassicalRep n (fun v => periodicHk K (g v) (hg v) (hgp v)) v hr

/-- **The commutator remainder splits**: `e_n = (S_n G - G) + g₁(aRep - a_n)`, `G = g₁(aRep)`. -/
theorem defectRemainder_apply_eq (n : ℕ) {b : ℝ → Vec 2 → Vec 2} {D H K : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {s : ℝ} (ha : ContDiff ℝ (D : ℕ∞) (aRep s)) (hD : 1 ≤ D)
    (hF : ∀ v j, Differentiable ℝ (fun y => classicalTotalFlux D H AD CE Jm aRep s v y j))
    (hF' : ∀ v j,
      Differentiable ℝ (fun y => classicalTotalFlux D H AD CE Jm (coarseTraj n W) s v y j))
    (v : ι) :
    (fun x => defectRemainder n b D H AD CE Jm W aRep s x v) = fun x =>
      (coarseProjField n (classicalDefectField b D H AD CE Jm aRep s) x v -
        classicalDefectField b D H AD CE Jm aRep s v x) +
      classicalDefectField b D H AD CE Jm (fun t y => aRep t y - coarseTraj n W t y) s v x := by
  funext x
  show coarseProjField n (classicalDefectField b D H AD CE Jm aRep s) x v -
      classicalDefectField b D H AD CE Jm (coarseTraj n W) s v x =
    (coarseProjField n (classicalDefectField b D H AD CE Jm aRep s) x v -
        classicalDefectField b D H AD CE Jm aRep s v x) +
      classicalDefectField b D H AD CE Jm (fun t y => aRep t y - coarseTraj n W t y) s v x
  rw [← classicalDefectField_sub (b := b) (a := aRep) (a' := coarseTraj n W) (s := s) ha
    ((coarseTraj_contDiff n W s).of_le (by exact_mod_cast le_top)) hD hF hF' v x]
  exact (sub_add_sub_cancel _ _ _).symm

/-- **Uniform bound of the jets of the commutator remainder.** There is a constant `Ce`,
depending only on `D, H, K, r₀, M` and the fibers, such that if at the time `s` the jets of order
`≤ M + 2` of the drift and of order `≤ M + 3` of the coefficients `A_d`, `C^{[r]}` are bounded by
`Cco`, `|𝖩(s)| ≤ Cco`, and `‖W_v(s)‖ ≤ B`, then the jets of order `≤ M` of every commutator
remainder `e_n(s)` are bounded by `Ce Cco B`. -/
theorem defectRemainder_jet_le {D H K r₀ M : ℕ} (hD : 2 ≤ D) (hord : M + D + 3 ≤ r₀)
    (hrK : r₀ + 2 ≤ K) :
    ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ (b : ℝ → Vec 2 → Vec 2)
      (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
        PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
      (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
        (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
          (PiLp 2 (fun _ : Fin 2 => h v)))
      (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (W : ∀ v, ℝ → TorusHk K (h v))
      (aRep : ℝ → Vec 2 → ∀ i, h i) (s Cco B : ℝ), 0 ≤ Cco → 0 ≤ B →
      (∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀) →
      ContDiff ℝ ((M + 2 : ℕ) : ℕ∞) (b s) → AVenhance.IsZ2Periodic (b s) →
      (∀ d, ContDiff ℝ ((M + 3 : ℕ) : ℕ∞) (AD d s)) → (∀ d, AVenhance.IsZ2Periodic (AD d s)) →
      (∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ ((M + 3 : ℕ) : ℕ∞) (CE r v u d s)) →
      (∀ r ∈ Finset.Icc 1 H, ∀ v u d, AVenhance.IsZ2Periodic (CE r v u d s)) →
      (∀ i ≤ M + 2, ∀ x, ‖iteratedFDeriv ℝ i (b s) x‖ ≤ Cco) →
      (∀ d, ∀ i ≤ M + 3, ∀ x, ‖iteratedFDeriv ℝ i (AD d s) x‖ ≤ Cco) →
      (∀ r ∈ Finset.Icc 1 H, ∀ v u d, ∀ i ≤ M + 3, ∀ x,
        ‖iteratedFDeriv ℝ i (CE r v u d s) x‖ ≤ Cco) →
      (∀ k l, |Jm s k l| ≤ Cco) → (∀ v, ‖W v s‖ ≤ B) →
      ∀ n, ∀ j ≤ M, ∀ x,
        ‖iteratedFDeriv ℝ j (defectRemainder n b D H AD CE Jm W aRep s) x‖ ≤ Ce * Cco * B := by
  obtain ⟨Crep, hCrep, hrepB⟩ := classicalRep_pi_jetBounded (h := h) hrK
  obtain ⟨Ct, hCt, htraj⟩ := coarseTraj_iteratedFDeriv_le (h := h) (K := K) (r := M + D)
    (by omega)
  choose Cp hCp hproj using fun v : ι =>
    classicalRep_iteratedFDeriv_le (E := h v) (M + 2) M le_rfl
  have hCp0 : 0 ≤ ∑ v, Cp v := Finset.sum_nonneg fun v _ => hCp v
  refine ⟨(∑ v, Cp v) * (Fintype.card (JetIndex2 (M + 2)) : ℝ) *
      defectJetConst (h := h) (M + 2) D H * Crep + defectJetConst (h := h) M D H * Ct,
    add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCp0 (Nat.cast_nonneg _))
      (defectJetConst_nonneg (h := h) (M + 2) D H)) hCrep)
      (mul_nonneg (defectJetConst_nonneg (h := h) M D H) hCt), ?_⟩
  intro b AD CE Jm W aRep s Cco B hCco hB hrep hb hbp hAD hADp hCE hCEp hbB hADB hCEB hJ hW n
    j hj x
  -- jet bounds of the data
  have hbJ : JetBoundedBy (M + 2) (b s) Cco := ⟨hb, hbB⟩
  have hADJ : ∀ d, JetBoundedBy (M + 3) (AD d s) Cco := fun d => ⟨hAD d, hADB d⟩
  have hCEJ : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, JetBoundedBy (M + 3) (CE r v u d s) Cco :=
    fun r hr v u d => ⟨hCE r hr v u d, hCEB r hr v u d⟩
  have hA : JetBoundedBy r₀ (aRep s) (Crep * B) :=
    hrepB (fun v => W v s) (aRep s) B hB hrep hW
  -- the classical defect field of the representative and its carrier
  have hGjet : ∀ v, JetBoundedBy (M + 2)
      (fun x => classicalDefectField b D H AD CE Jm aRep s v x)
      (defectJetConst (h := h) (M + 2) D H * (Cco * (Crep * B))) := fun v =>
    classicalDefectField_jetBounded (s := s) hD hCco (hA.mono (by omega) le_rfl) hbJ
      (fun d => (hADJ d).mono (by omega) le_rfl)
      (fun r hr v u d => (hCEJ r hr v u d).mono (by omega) le_rfl) hJ v
  have hGc : ∀ v, ContDiff ℝ ((M + 2 : ℕ) : ℕ∞)
      (classicalDefectField b D H AD CE Jm aRep s v) := fun v => (hGjet v).1
  have hGp : ∀ v, AVenhance.IsZ2Periodic (classicalDefectField b D H AD CE Jm aRep s v) :=
    classicalDefectField_periodic hrep hADp hCEp hbp
  have hAG : 0 ≤ defectJetConst (h := h) (M + 2) D H * (Cco * (Crep * B)) :=
    mul_nonneg (defectJetConst_nonneg (h := h) (M + 2) D H) (mul_nonneg hCco (mul_nonneg hCrep hB))
  -- the Galerkin projection of the field
  have hX1 : JetBoundedBy M (coarseProjField n (classicalDefectField b D H AD CE Jm aRep s))
      ((∑ v, Cp v) * ((Fintype.card (JetIndex2 (M + 2)) : ℝ) *
        (defectJetConst (h := h) (M + 2) D H * (Cco * (Crep * B))))) := by
    refine JetBoundedBy.of_components (mul_nonneg hCp0 (mul_nonneg (Nat.cast_nonneg _) hAG))
      fun v => ⟨contDiff_pi.1 ((coarseProjField_contDiff n
        (classicalDefectField b D H AD CE Jm aRep s)).of_le (by exact_mod_cast le_top)) v,
        fun i hi y => ?_⟩
    refine (hproj v _ _ (coarseProjField_isClassicalRep n (M + 2) _ hGc hGp (by omega) v) i hi
      y).trans ?_
    exact mul_le_mul (Finset.single_le_sum (f := Cp) (fun v _ => hCp v) (Finset.mem_univ v))
      ((galerkinProj_norm_le n _).trans
        (periodicHk_norm_le_of_jet (M + 2) (hGc v) (hGp v) hAG (hGjet v).2))
      (norm_nonneg _) hCp0
  -- the defect field of the approximant
  have hT : JetBoundedBy (M + D) (coarseTraj n W s) (Ct * B) :=
    ⟨(coarseTraj_contDiff n W s).of_le (by exact_mod_cast le_top), htraj n W s hB hW⟩
  have hX2 : JetBoundedBy M (fun x v => classicalDefectField b D H AD CE Jm (coarseTraj n W) s v x)
      (defectJetConst (h := h) M D H * (Cco * (Ct * B))) :=
    JetBoundedBy.of_components (mul_nonneg (defectJetConst_nonneg (h := h) M D H)
      (mul_nonneg hCco (mul_nonneg hCt hB))) fun v =>
      classicalDefectField_jetBounded (s := s) hD hCco hT (hbJ.mono (by omega) le_rfl)
        (fun d => (hADJ d).mono (by omega) le_rfl)
        (fun r hr v u d => (hCEJ r hr v u d).mono (by omega) le_rfl) hJ v
  exact ((hX1.sub hX2).2 j hj x).trans (le_of_eq (by ring))

/-- **The commutator remainder tends to zero in `C^M`.** At a fixed time `s`, if the drift is of
class `C^{M+2}`, the coefficients `A_d`, `C^{[r]}` of class `C^{M+3}`, all periodic, and `aRep(s)`
is a classical representative of `W(s)` at an order `r₀ ≥ M + D + 3` with `r₀ + 2 ≤ K`, then the
jets of order `≤ M` of the commutator remainders `e_n(s)` tend to zero uniformly in space. -/
theorem defectRemainder_jet_tendsto {D H K r₀ M : ℕ} (hD : 2 ≤ D) (hord : M + D + 3 ≤ r₀)
    (hrK : r₀ + 2 ≤ K) (b : ℝ → Vec 2 → Vec 2)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (W : ∀ v, ℝ → TorusHk K (h v))
    (aRep : ℝ → Vec 2 → ∀ i, h i) (s : ℝ)
    (hrep : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hb : ContDiff ℝ ((M + 2 : ℕ) : ℕ∞) (b s)) (hbp : AVenhance.IsZ2Periodic (b s))
    (hAD : ∀ d, ContDiff ℝ ((M + 3 : ℕ) : ℕ∞) (AD d s))
    (hADp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ ((M + 3 : ℕ) : ℕ∞) (CE r v u d s))
    (hCEp : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, AVenhance.IsZ2Periodic (CE r v u d s)) :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop, ∀ j ≤ M, ∀ x,
      ‖iteratedFDeriv ℝ j (defectRemainder n b D H AD CE Jm W aRep s) x‖ ≤ ε := by
  intro ε hε
  -- bounds of the coefficients, the representative and the approximants
  obtain ⟨Cco, hCco, hbJ, hADJ, hCEJ, hJ⟩ :=
    exists_coeff_jetBounded b AD CE Jm s hb hbp hAD hADp hCE hCEp
  obtain ⟨Crep, -, hrepB⟩ := classicalRep_pi_jetBounded (h := h) hrK
  obtain ⟨Cs, hCs, hsubB⟩ := classicalRep_pi_sub_jetBounded (h := h) hrK
  obtain ⟨Ct, -, htraj⟩ := coarseTraj_iteratedFDeriv_le (h := h) (K := K) (r := M + D)
    (by omega)
  choose Cp hCp hpsub using fun v : ι =>
    classicalRep_iteratedFDeriv_sub_le (E := h v) (M + 2) M le_rfl
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, B₀ = ∑ v, ‖W v s‖ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B₀ := by rw [hB₀]; exact Finset.sum_nonneg fun v _ => norm_nonneg _
  have hWB : ∀ v, ‖W v s‖ ≤ B₀ := fun v => by
    rw [hB₀]
    exact Finset.single_le_sum (f := fun v => ‖W v s‖) (fun v _ => norm_nonneg _)
      (Finset.mem_univ v)
  have hA : JetBoundedBy r₀ (aRep s) (Crep * B₀) :=
    hrepB (fun v => W v s) (aRep s) B₀ hB0 hrep hWB
  -- the classical defect field of the representative
  have hGjet : ∀ v, JetBoundedBy (M + 2)
      (fun x => classicalDefectField b D H AD CE Jm aRep s v x)
      (defectJetConst (h := h) (M + 2) D H * (Cco * (Crep * B₀))) := fun v =>
    classicalDefectField_jetBounded (s := s) hD hCco (hA.mono (by omega) le_rfl) hbJ
      (fun d => (hADJ d).mono (by omega) le_rfl)
      (fun r hr v u d => (hCEJ r hr v u d).mono (by omega) le_rfl) hJ v
  have hGc : ∀ v, ContDiff ℝ ((M + 2 : ℕ) : ℕ∞)
      (classicalDefectField b D H AD CE Jm aRep s v) := fun v => (hGjet v).1
  have hGp : ∀ v, AVenhance.IsZ2Periodic (classicalDefectField b D H AD CE Jm aRep s v) :=
    classicalDefectField_periodic hrep hADp hCEp hbp
  have hFa : ∀ v j, Differentiable ℝ (fun y => classicalTotalFlux D H AD CE Jm aRep s v y j) :=
    fun v j => (classicalTotalFlux_jetBounded (P := M) (s := s) hD hCco
      (hA.mono (by omega) le_rfl) (fun d => (hADJ d).mono (by omega) le_rfl)
      (fun r hr v u d => (hCEJ r hr v u d).mono (by omega) le_rfl) hJ v j).1.differentiable
      (by exact_mod_cast Nat.succ_ne_zero M)
  -- the threshold
  obtain ⟨Kt, hKt⟩ : ∃ Kt : ℝ, Kt = ∑ v, Cp v + defectJetConst (h := h) M D H * (Cco * Cs) :=
    ⟨_, rfl⟩
  have hKt0 : 0 ≤ Kt := by
    rw [hKt]
    exact add_nonneg (Finset.sum_nonneg fun v _ => hCp v)
      (mul_nonneg (defectJetConst_nonneg (h := h) M D H) (mul_nonneg hCco hCs))
  have hK1 : 0 < Kt + 1 := add_pos_of_nonneg_of_pos hKt0 one_pos
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / (Kt + 1) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact div_pos hε hK1
  have hKη : Kt * η ≤ ε := by
    rw [hη, mul_div_assoc', div_le_iff₀ hK1]
    calc Kt * ε ≤ Kt * ε + ε := le_add_of_nonneg_right hε.le
      _ = ε * (Kt + 1) := by ring
  -- the Galerkin cutoffs converge
  have hev : ∀ᶠ n in Filter.atTop, ∀ v,
      ‖galerkinProj n (periodicHk (M + 2) _ (hGc v) (hGp v)) -
          periodicHk (M + 2) _ (hGc v) (hGp v)‖ < η ∧
        ‖W v s - galerkinProj n (W v s)‖ < η := by
    refine Filter.eventually_all.2 fun v => ?_
    filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.1
        (galerkinProj_tendsto (periodicHk (M + 2) _ (hGc v) (hGp v)))).eventually
        (gt_mem_nhds hη0),
      (tendsto_iff_norm_sub_tendsto_zero.1 (galerkinProj_tendsto (W v s))).eventually
        (gt_mem_nhds hη0)] with n h1 h2
    exact ⟨h1, by rw [norm_sub_rev]; exact h2⟩
  filter_upwards [hev] with n hn j hj x
  -- the approximant and the difference with the representative
  have hrepn : ∀ v, IsClassicalRep (galerkinProj n (W v s)) (fun x => coarseTraj n W s x v) r₀ :=
    fun v => by
      rw [coarseTraj_eq]
      exact coarseApprox_isClassicalRep n (fun u => W u s) v (by omega)
  have hT : JetBoundedBy (M + D) (coarseTraj n W s) (Ct * B₀) :=
    ⟨(coarseTraj_contDiff n W s).of_le (by exact_mod_cast le_top), htraj n W s hB0 hWB⟩
  have hFt : ∀ v j, Differentiable ℝ
      (fun y => classicalTotalFlux D H AD CE Jm (coarseTraj n W) s v y j) := fun v j =>
    (classicalTotalFlux_jetBounded (P := M) (s := s) hD hCco hT
      (fun d => (hADJ d).mono (by omega) le_rfl)
      (fun r hr v u d => (hCEJ r hr v u d).mono (by omega) le_rfl) hJ v j).1.differentiable
      (by exact_mod_cast Nat.succ_ne_zero M)
  have hdiff : JetBoundedBy r₀ (fun x => aRep s x - coarseTraj n W s x) (Cs * η) :=
    hsubB (fun v => W v s) (fun v => galerkinProj n (W v s)) (aRep s) (coarseTraj n W s) η
      hη0.le hrep hrepn fun v => (hn v).2.le
  -- the two parts of the remainder
  have hdef : ∀ v, JetBoundedBy M (fun x => classicalDefectField b D H AD CE Jm
      (fun t y => aRep t y - coarseTraj n W t y) s v x)
      (defectJetConst (h := h) M D H * (Cco * (Cs * η))) := fun v =>
    classicalDefectField_jetBounded (a := fun t y => aRep t y - coarseTraj n W t y) (s := s) hD
      hCco (hdiff.mono (by omega) le_rfl) (hbJ.mono (by omega) le_rfl)
      (fun d => (hADJ d).mono (by omega) le_rfl)
      (fun r hr v u d => (hCEJ r hr v u d).mono (by omega) le_rfl) hJ v
  have hproj : ∀ v, JetBoundedBy M (fun x =>
      coarseProjField n (classicalDefectField b D H AD CE Jm aRep s) x v -
        classicalDefectField b D H AD CE Jm aRep s v x) (Cp v * η) := fun v => by
    refine ⟨(contDiff_pi.1 ((coarseProjField_contDiff n
      (classicalDefectField b D H AD CE Jm aRep s)).of_le (by exact_mod_cast le_top)) v).sub
      ((hGc v).of_le (by exact_mod_cast (by omega : M ≤ M + 2))), fun i hi y => ?_⟩
    exact (hpsub v _ _ _ _ (coarseProjField_isClassicalRep n (M + 2) _ hGc hGp (by omega) v)
      (periodicHk_isClassicalRep (M + 2) (hGc v) (hGp v) (by omega)) i hi y).trans
      (mul_le_mul_of_nonneg_left (hn v).1.le (hCp v))
  have hcomp : ∀ v, JetBoundedBy M (fun x => defectRemainder n b D H AD CE Jm W aRep s x v)
      (Cp v * η + defectJetConst (h := h) M D H * (Cco * (Cs * η))) := fun v => by
    rw [defectRemainder_apply_eq n (b := b)
      (hA.1.of_le (by exact_mod_cast (by omega : D ≤ r₀))) (by omega) hFa hFt v]
    exact (hproj v).add (hdef v)
  have hall : JetBoundedBy M (defectRemainder n b D H AD CE Jm W aRep s) (Kt * η) :=
    JetBoundedBy.of_components (mul_nonneg hKt0 hη0.le) fun v => (hcomp v).mono le_rfl (by
      rw [hKt]
      calc Cp v * η + defectJetConst (h := h) M D H * (Cco * (Cs * η))
          ≤ (∑ v, Cp v) * η + defectJetConst (h := h) M D H * (Cco * (Cs * η)) :=
            add_le_add (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := Cp)
              (fun v _ => hCp v) (Finset.mem_univ v)) hη0.le) le_rfl
        _ = (∑ v, Cp v + defectJetConst (h := h) M D H * (Cco * Cs)) * η := by ring)
  exact (hall.2 j hj x).trans hKη

end Pi

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Time regularity facts of the retained field on the window**. The Galerkin
coefficients of `W` are continuous on the window, hence measurable in the clamped time
(`ReconWindowAt.coarseCoeff_measurable`). A trajectory `W` continuous on a compact window is bounded
(`exists_bound_of_continuousOn_family`), its Galerkin cutoffs converge uniformly at a rate
(`exists_galerkin_uniform`), and a classical representative of it is jointly continuous, hence
jointly measurable on the window (`classicalRep_joint_continuous`,
`classicalRep_joint_measurable`). -/

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- **A family of trajectories continuous on a compact interval is bounded.** -/
theorem exists_bound_of_continuousOn_family {K : ℕ} {a b : ℝ} (W : ∀ v, ℝ → TorusHk K (h v))
    (hWc : ∀ v, ContinuousOn (W v) (Set.Icc a b)) :
    ∃ CW : ℝ, 0 ≤ CW ∧ ∀ s ∈ Set.Icc a b, ∀ u, ‖W u s‖ ≤ CW := by
  choose C hC using fun v => isCompact_Icc.exists_bound_of_continuousOn (hWc v)
  refine ⟨∑ v, |C v|, Finset.sum_nonneg fun v _ => abs_nonneg _, fun s hs u => ?_⟩
  exact (hC u s hs).trans ((le_abs_self _).trans (Finset.single_le_sum
    (f := fun v => |C v|) (fun v _ => abs_nonneg _) (Finset.mem_univ u)))

omit [DecidableEq ι] in
/-- **The Galerkin cutoffs of a family of trajectories continuous on a compact interval converge
uniformly**, at a rate `δ n → 0`. -/
theorem exists_galerkin_uniform {K : ℕ} {a b : ℝ} (hab : a ≤ b) (W : ∀ v, ℝ → TorusHk K (h v))
    (hWc : ∀ v, ContinuousOn (W v) (Set.Icc a b)) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ n, ∀ s ∈ Set.Icc a b, ∀ u, ‖galerkinProj n (W u s) - W u s‖ ≤ δ n := by
  obtain ⟨CW, hCW, hWb⟩ := exists_bound_of_continuousOn_family W hWc
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ → ℝ, ∀ n s, S n s = ∑ u, ‖galerkinProj n (W u s) - W u s‖ :=
    ⟨_, fun _ _ => rfl⟩
  have hS0 : ∀ n s, 0 ≤ S n s := fun n s => (hS n s).symm ▸
    Finset.sum_nonneg fun u _ => norm_nonneg _
  have hSb : ∀ n, ∀ s ∈ Set.Icc a b, S n s ≤ ∑ _u : ι, 2 * CW := fun n s hs => by
    rw [hS]
    refine Finset.sum_le_sum fun u _ => ?_
    calc ‖galerkinProj n (W u s) - W u s‖ ≤ ‖galerkinProj n (W u s)‖ + ‖W u s‖ := norm_sub_le _ _
      _ ≤ ‖W u s‖ + ‖W u s‖ := add_le_add (galerkinProj_norm_le n (W u s)) le_rfl
      _ ≤ 2 * CW := by linarith [hWb s hs u]
  have hne : ((fun s => S 0 s) '' Set.Icc a b).Nonempty := ⟨_, Set.mem_image_of_mem _
    (Set.left_mem_Icc.2 hab)⟩
  have hbdd : ∀ n, BddAbove ((fun s => S n s) '' Set.Icc a b) := fun n =>
    ⟨∑ _u : ι, 2 * CW, fun y ⟨s, hs, hy⟩ => hy ▸ hSb n s hs⟩
  have hle : ∀ n, ∀ s ∈ Set.Icc a b, S n s ≤ sSup ((fun s => S n s) '' Set.Icc a b) :=
    fun n s hs => le_csSup (hbdd n) (Set.mem_image_of_mem _ hs)
  refine ⟨fun n => sSup ((fun s => S n s) '' Set.Icc a b), fun n => (hS0 n a).trans
    (hle n a (Set.left_mem_Icc.2 hab)), ?_, fun n s hs u => ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have hc : (0 : ℝ) < Fintype.card ι + 1 := by positivity
    have hev : ∀ u, ∀ᶠ n in atTop, ∀ s ∈ Set.Icc a b,
        ‖galerkinProj n (W u s) - W u s‖ < ε / (2 * (Fintype.card ι + 1)) := fun u =>
      galerkinProj_eventually_uniform isCompact_Icc (hWc u) (by positivity)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 hev)
    refine ⟨N, fun n hn => ?_⟩
    have hsup : sSup ((fun s => S n s) '' Set.Icc a b) ≤
        Fintype.card ι * (ε / (2 * (Fintype.card ι + 1))) := by
      refine csSup_le ⟨_, Set.mem_image_of_mem _ (Set.left_mem_Icc.2 hab)⟩ ?_
      rintro y ⟨s, hs, rfl⟩
      show S n s ≤ _
      rw [hS]
      calc ∑ u, ‖galerkinProj n (W u s) - W u s‖
          ≤ ∑ _u : ι, ε / (2 * (Fintype.card ι + 1)) :=
            Finset.sum_le_sum fun u _ => (hN n hn u s hs).le
        _ = Fintype.card ι * (ε / (2 * (Fintype.card ι + 1))) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h0 : 0 ≤ sSup ((fun s => S n s) '' Set.Icc a b) :=
      (hS0 n a).trans (hle n a (Set.left_mem_Icc.2 hab))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    refine hsup.trans_lt ?_
    have h1 : (Fintype.card ι : ℝ) * (ε / (2 * (Fintype.card ι + 1))) =
        ε * ((Fintype.card ι) / (2 * (Fintype.card ι + 1))) := by ring
    rw [h1]
    refine mul_lt_of_lt_one_right hε ?_
    rw [div_lt_one (by positivity)]
    linarith [(Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ Fintype.card ι)]
  · refine le_trans ?_ (hle n s hs)
    rw [hS]
    exact Finset.single_le_sum (f := fun u => ‖galerkinProj n (W u s) - W u s‖)
      (fun u _ => norm_nonneg _) (Finset.mem_univ u)

omit [Fintype ι] [DecidableEq ι] in
/-- **A classical representative of a trajectory continuous on a compact interval is jointly
continuous on the interval.** -/
theorem classicalRep_joint_continuous {K r : ℕ} (hr : r + 2 ≤ K) {a b : ℝ}
    (W : ∀ v, ℝ → TorusHk K (h v)) (hWc : ∀ v, ContinuousOn (W v) (Set.Icc a b))
    (aRep : ℝ → Vec 2 → ∀ i, h i)
    (hrep : ∀ s ∈ Set.Icc a b, ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r) :
    Continuous fun q : Set.Icc a b × Vec 2 => aRep q.1 q.2 := by
  refine continuous_pi fun v => ?_
  obtain ⟨C, hC, hb⟩ := classicalRep_iteratedFDeriv_sub_le (E := h v) K r hr
  have hWv : Continuous (fun s : Set.Icc a b => W v s) := (hWc v).domRestrict
  rw [Metric.continuous_iff]
  rintro ⟨s₀, x₀⟩ ε hε
  have hx : Continuous (fun x => aRep s₀ x v) := (hrep s₀ s₀.2 v).2.1.continuous
  obtain ⟨δ₁, hδ₁, hx'⟩ := Metric.continuous_iff.1 hx x₀ (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, hs'⟩ := Metric.continuous_iff.1 hWv s₀ (ε / (2 * (C + 1)))
    (by have := hC; positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  rintro ⟨s, x⟩ hq
  have hq1 : dist s s₀ < δ₂ := (le_max_left _ _).trans_lt (hq.trans_le (min_le_right _ _))
  have hq2 : dist x x₀ < δ₁ := (le_max_right _ _).trans_lt (hq.trans_le (min_le_left _ _))
  have h1 : ‖aRep s x v - aRep s₀ x v‖ ≤ C * ‖W v s - W v s₀‖ := by
    have := hb (W v s) (W v s₀) _ _ (hrep s s.2 v) (hrep s₀ s₀.2 v) 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have h2 : C * ‖W v s - W v s₀‖ < ε / 2 := by
    have hd : ‖W v s - W v s₀‖ < ε / (2 * (C + 1)) := by
      rw [← dist_eq_norm]
      exact hs' s hq1
    calc C * ‖W v s - W v s₀‖ ≤ (C + 1) * ‖W v s - W v s₀‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C + 1) * (ε / (2 * (C + 1))) := mul_lt_mul_of_pos_left hd (by linarith)
      _ = ε / 2 := by field_simp
  have h3 : dist (aRep s₀ x v) (aRep s₀ x₀ v) < ε / 2 := hx' x hq2
  calc dist (aRep s x v) (aRep s₀ x₀ v)
      ≤ dist (aRep s x v) (aRep s₀ x v) + dist (aRep s₀ x v) (aRep s₀ x₀ v) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (by rw [dist_eq_norm]; exact h1.trans h2.le) h3
    _ = ε := by ring

omit [DecidableEq ι] in
/-- **A classical representative of a continuous trajectory is jointly measurable.** -/
theorem classicalRep_joint_measurable {K r : ℕ} (hr : r + 2 ≤ K) {a b : ℝ}
    (W : ∀ v, ℝ → TorusHk K (h v)) (hWc : ∀ v, ContinuousOn (W v) (Set.Icc a b))
    (aRep : ℝ → Vec 2 → ∀ i, h i)
    (hrep : ∀ s ∈ Set.Icc a b, ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r) :
    Measurable fun q : Set.Icc a b × Vec 2 => aRep q.1 q.2 :=
  (classicalRep_joint_continuous hr W hWc aRep hrep).measurable

end Family

section Window

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The Galerkin coefficients of the retained field are measurable in the clamped time** (the
hypothesis `hcm` of the measurability of the residuals). -/
theorem ReconWindowAt.coarseCoeff_measurable
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (n : ℕ) (r : CoupledFourierModeIndex (h := h) n) :
    Measurable fun s => coarseCoeff n W r
      (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s) := by
  have htAZ : tp ≤ tp + Tobs := by linarith [w.hTobs]
  have hc := (coarseCoeff_prim w.hcd htAZ n r).continuousOn htAZ
  exact (hc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    fun s => (Set.projIcc tp (tp + Tobs) htAZ s).2).measurable

end Window

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The commutator remainders on a reconstruction window**. In the coarse
setting of the window the jets of the drift, of the coefficients `A_d`, `C^{[r]}` and the entries
of `𝖩` are bounded uniformly in time (`coarse_coeff_jets_bounded`): the drift by
`Coarse.drift_bound`, the coefficients by their finite seminorms `𝒜_{ρ,N}`
(`coeff_jet_bound_of_seminorm`), and `𝖩` by `‖𝖩 - B·1‖_∞ < ∞`. Hence the jets of order
`≤ N_c + r` of the commutator remainders `e_n(s)` of the approximants tend to zero at every
window time (`ReconWindowAt.defect_jets_tendsto`) and are bounded uniformly in `n` and `s` by a
constant times the bound of `W` (`ReconWindowAt.defect_jets_bound`), as the residual force
(`ReconWindowAt.force_limit`) requires. -/

/-- A bound for each member of a finite family, monotone in the bound, gives a common bound. -/
theorem exists_uniform_of_finset {κ : Type*} (S : Finset κ) (Q : κ → ℝ → Prop)
    (hmono : ∀ k A A', A ≤ A' → Q k A → Q k A') (hQ : ∀ k ∈ S, ∃ A, Q k A) :
    ∃ A, 0 ≤ A ∧ ∀ k ∈ S, Q k A := by
  classical
  choose! A hA using hQ
  refine ⟨∑ k ∈ S, max (A k) 0, Finset.sum_nonneg fun _ _ => le_max_right _ _,
    fun k hk => hmono k _ _ ((le_max_left (A k) 0).trans ?_) (hA k hk)⟩
  exact Finset.single_le_sum (f := fun k => max (A k) 0) (fun _ _ => le_max_right _ _) hk

/-- An order bound in `ℕ` as an order bound of smoothness classes. -/
theorem withTop_enat_cast_le {a b : ℕ} (hab : a ≤ b) :
    (((a : ℕ∞)) : WithTop ℕ∞) ≤ ((b : ℕ) : WithTop ℕ∞) := by
  exact_mod_cast hab

/-- The jets of a coefficient field are bounded by its derivative array. -/
theorem norm_iteratedFDeriv_coeff_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {C : Vec 2 → E →L[ℝ] F} {l : ℕ}
    (hC : ContDiff ℝ (l : ℕ) C) (x : Vec 2) :
    ‖iteratedFDeriv ℝ l C x‖ ≤ 2 ^ l * ‖coefficientDerivativeArray C l x‖ := by
  refine (norm_le_sum_basisVec _).trans ?_
  have hterm : ∀ w : DerivativeWord2 l,
      ‖iteratedFDeriv ℝ l C x (fun i => basisVec (w i))‖ ≤
        ‖coefficientDerivativeArray C l x‖ := by
    intro w
    have e1 : iteratedFDeriv ℝ l C x (fun i => basisVec (w i)) =
        orderedCoefficientDerivative C l (fun i => w i.rev) x := by
      rw [AVRegularity.Weighted.orderedCoefficientDerivative_eq_iterated _ l hC]
      simp
    rw [e1]
    exact Coarse.norm_orderedCoeff_le_array _ l _ x
  calc ∑ w : DerivativeWord2 l, ‖iteratedFDeriv ℝ l C x (fun i => basisVec (w i))‖
      ≤ ∑ _w : DerivativeWord2 l, ‖coefficientDerivativeArray C l x‖ :=
        Finset.sum_le_sum fun w _ => hterm w
    _ = 2 ^ l * ‖coefficientDerivativeArray C l x‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp [DerivativeWord2]

/-- **Uniform jets of a coefficient of finite seminorm**: a coefficient of class `C^N` on the
window with `𝒜_{ρ,N} < ∞` has jets of order `≤ P ≤ N` bounded uniformly in time and space. -/
theorem coeff_jet_bound_of_seminorm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} {t₀ t₁ : ℝ}
    {A : ℝ → Vec 2 → E →L[ℝ] F} (hA : coefficientSeminorm ρ N t₀ t₁ A ≠ ⊤)
    (hs : ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (N : ℕ) (A t)) {P : ℕ} (hP : P ≤ N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i ≤ P, ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ‖iteratedFDeriv ℝ i (A t) x‖ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_uniform_of_finset (Finset.range (P + 1))
    (fun i M => ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ‖iteratedFDeriv ℝ i (A t) x‖ ≤ M)
    (fun i A A' hle hQ t ht x => (hQ t ht x).trans hle) (fun i hi => by
      have hi' : i < P + 1 := Finset.mem_range.1 hi
      have hiN : i ≤ N := by omega
      obtain ⟨M, -, hM⟩ := Coarse.coeffArray_bound_of_seminorm hρ hA hiN
      refine ⟨2 ^ i * M, fun t ht x => ?_⟩
      have hiN' : ((i : ℕ) : WithTop ℕ∞) ≤ ((N : ℕ) : WithTop ℕ∞) := by exact_mod_cast hiN
      exact (norm_iteratedFDeriv_coeff_le ((hs t ht).of_le hiN') x).trans
        (mul_le_mul_of_nonneg_left (hM t ht x) (by positivity)))
  exact ⟨M, hM0, fun i hi t ht x => hM i (Finset.mem_range.2 (by omega)) t ht x⟩

section Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

/-- **Uniform bounds of the coarse coefficients.** In the coarse setting, the jets of order
`≤ P + 2` of the drift and of order `≤ P + 3` of the coefficients `A_d`, `C^{[r]}`, and the
entries of `𝖩`, are bounded on the window by a common constant, if `P + 3 ≤ N`. -/
theorem coarse_coeff_jets_bounded
    (S : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {P : ℕ} (hP : P + 3 ≤ N) :
    ∃ Cco : ℝ, 0 ≤ Cco ∧
      (∀ s ∈ Set.Icc t₀ t₁, ∀ i ≤ P + 2, ∀ x, ‖iteratedFDeriv ℝ i (b s) x‖ ≤ Cco) ∧
      (∀ s ∈ Set.Icc t₀ t₁, ∀ d, ∀ i ≤ P + 3, ∀ x, ‖iteratedFDeriv ℝ i (AD d s) x‖ ≤ Cco) ∧
      (∀ s ∈ Set.Icc t₀ t₁, ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ∀ i ≤ P + 3, ∀ x,
        ‖iteratedFDeriv ℝ i (CE r v u d s) x‖ ≤ Cco) ∧
      (∀ s ∈ Set.Icc t₀ t₁, ∀ k l, |Jm s k l| ≤ Cco) := by
  classical
  -- the drift
  obtain ⟨Cb, hCb, hb⟩ := exists_uniform_of_finset (Finset.range (P + 3))
    (fun i M => ∀ s ∈ Set.Icc t₀ t₁, ∀ x, ‖iteratedFDeriv ℝ i (b s) x‖ ≤ M)
    (fun i A A' hle hQ s hs x => (hQ s hs x).trans hle) (fun i hi => by
      have hi' : i < P + 3 := Finset.mem_range.1 hi
      obtain ⟨M, -, hM⟩ := Coarse.drift_bound S (l := i) (by omega)
      exact ⟨M, hM⟩)
  -- the diagonal coefficients
  obtain ⟨Ca, hCa, ha⟩ := exists_uniform_of_finset Finset.univ
    (fun d M => ∀ i ≤ P + 3, ∀ s ∈ Set.Icc t₀ t₁, ∀ x, ‖iteratedFDeriv ℝ i (AD d s) x‖ ≤ M)
    (fun d A A' hle hQ i hi s hs x => (hQ i hi s hs x).trans hle) (fun d _ => by
      obtain ⟨M, -, hM⟩ := coeff_jet_bound_of_seminorm S.rho_pos (S.AD_fin d)
        (S.AD_smooth d) hP
      exact ⟨M, hM⟩)
  -- the edge coefficients
  obtain ⟨Ce, hCe, he⟩ := exists_uniform_of_finset
    (Finset.Icc 1 H ×ˢ (Finset.univ : Finset (ι × ι × Finset.Icc 2 D)))
    (fun c M => ∀ i ≤ P + 3, ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖iteratedFDeriv ℝ i (CE c.1 c.2.1 c.2.2.1 c.2.2.2 s) x‖ ≤ M)
    (fun c A A' hle hQ i hi s hs x => (hQ i hi s hs x).trans hle) (fun c hc => by
      have hr : c.1 ∈ Finset.Icc 1 H := (Finset.mem_product.1 hc).1
      obtain ⟨M, -, hM⟩ := coeff_jet_bound_of_seminorm S.rho_pos
        (S.CE_fin c.1 hr c.2.1 c.2.2.1 c.2.2.2) (S.CE_smooth c.1 hr c.2.1 c.2.2.1 c.2.2.2) hP
      exact ⟨M, hM⟩)
  -- the flux matrix
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (matrixSupNorm
      (fun t => Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁).toReal := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; exact ENNReal.toReal_nonneg
  have hle : matrixSupNorm (fun t => Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁ ≤
      ENNReal.ofReal c := by
    rw [hc, ENNReal.ofReal_toReal S.J_bdd]
  have hJ : ∀ s ∈ Set.Icc t₀ t₁, ∀ k l, |Jm s k l| ≤ c + B := fun s hs k l => by
    have h1 : |(Jm s - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) k l| ≤ c :=
      Coarse.abs_entry_le_of_matrixSupNorm
        (M := fun t => Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) hc0 hle hs k l
    have h2 : |(B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) k l| ≤ B := by
      by_cases hkl : k = l
      · simp [hkl, abs_of_pos S.B_pos]
      · simp [hkl, S.B_pos.le]
    calc |Jm s k l| = |(Jm s - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) k l +
          (B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) k l| := by
          rw [Matrix.sub_apply, sub_add_cancel]
      _ ≤ |(Jm s - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) k l| +
          |(B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) k l| := abs_add_le _ _
      _ ≤ c + B := add_le_add h1 h2
  -- the common bound
  have hcB : 0 ≤ c + B := add_nonneg hc0 S.B_pos.le
  refine ⟨Cb + Ca + Ce + (c + B), by positivity, fun s hs i hi x => ?_,
    fun s hs d i hi x => ?_, fun s hs r hr v u d i hi x => ?_, fun s hs k l => ?_⟩
  · exact (hb i (Finset.mem_range.2 (by omega)) s hs x).trans (by linarith)
  · exact (ha d (Finset.mem_univ d) i hi s hs x).trans (by linarith)
  · exact (he (r, v, u, d) (Finset.mem_product.2 ⟨hr, Finset.mem_univ _⟩) i hi s hs x).trans
      (by linarith)
  · exact (hJ s hs k l).trans (by linarith)

/-- The entries of the flux matrix of a coarse setting are interval integrable on the window. -/
theorem IsCoarseSetting.J_intervalIntegrable
    (S : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    (hN3 : 3 ≤ N) (i j : Fin 2) : IntervalIntegrable (fun s => Jm s i j) volume t₀ t₁ := by
  obtain ⟨Cco, -, -, -, -, hJ⟩ := coarse_coeff_jets_bounded S (P := 0) (by omega)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le S.window]
  exact Measure.integrableOn_of_bounded (M := Cco) measure_Ioc_lt_top.ne
    (S.J_meas i j).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs]
      exact hJ t (Set.Ioc_subset_Icc_self ht) i j))

end Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The commutator remainders tend to zero on the window**: at every window time, the jets
of order `≤ N_c + r` of the commutator remainders of the approximants tend to zero uniformly in
space. -/
theorem ReconWindowAt.defect_jets_tendsto
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {r : ℕ} (hord : Nc + r + (Nc + D) + 3 ≤ r₀) (hrK : r₀ + 2 ≤ kc + 1 + (Nc + D))
    (hN : Nc + r + 3 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) :
    ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ ε > 0, ∀ᶠ n in atTop, ∀ j ≤ Nc + r, ∀ x,
      ‖iteratedFDeriv ℝ j ((defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE
          Jm W aRep) s) x‖ ≤ ε := by
  intro t ht
  have hN' : (((Nc + r + 3 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
      ((kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) : ℕ) : WithTop ℕ∞) :=
    withTop_enat_cast_le hN
  exact defectRemainder_jet_tendsto (M := Nc + r) w.hcs.D_ge hord hrK (streamVel (Φ (m - 1)))
    AD CE Jm W aRep t (w.hrep t ht)
    ((w.hcs.drift_smooth t ht).of_le (WithTop.coe_le_coe.2 le_top)) (w.hcs.drift_per t ht)
    (fun d => (w.hcs.AD_smooth d t ht).of_le hN') (fun d => w.hcs.AD_per d t ht)
    (fun r hr v u d => (w.hcs.CE_smooth r hr v u d t ht).of_le hN')
    (fun r hr v u d => w.hcs.CE_per r hr v u d t ht)

/-- **Uniform bound of the commutator remainders on the window**: if `‖W_u(s)‖ ≤ C_W` on the
window, the jets of order `≤ N_c + r` of all the commutator remainders are bounded by a constant
`C_E'`. -/
theorem ReconWindowAt.defect_jets_bound
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {r : ℕ} (hord : Nc + r + (Nc + D) + 3 ≤ r₀) (hrK : r₀ + 2 ≤ kc + 1 + (Nc + D))
    (hN : Nc + r + 3 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
    {CW : ℝ} (hCW : 0 ≤ CW) (hWB : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ u, ‖W u s‖ ≤ CW) :
    ∃ CE' : ℝ, 0 ≤ CE' ∧ ∀ n, ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ j ≤ Nc + r, ∀ x,
      ‖iteratedFDeriv ℝ j ((defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE
          Jm W aRep) s) x‖ ≤ CE' := by
  obtain ⟨Ce, hCe, hle⟩ := defectRemainder_jet_le (ι := ι) (h := h) (M := Nc + r) w.hcs.D_ge
    hord hrK
  obtain ⟨Cco, hCco, hb, hAD, hCE, hJ⟩ := coarse_coeff_jets_bounded w.hcs (P := Nc + r) hN
  have hN' : (((Nc + r + 3 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
      ((kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) : ℕ) : WithTop ℕ∞) :=
    withTop_enat_cast_le hN
  refine ⟨Ce * Cco * CW, mul_nonneg (mul_nonneg hCe hCco) hCW, fun n t ht j hj x => ?_⟩
  exact hle (streamVel (Φ (m - 1))) AD CE Jm W aRep t Cco CW hCco hCW
    (w.hrep t ht)
    ((w.hcs.drift_smooth t ht).of_le (WithTop.coe_le_coe.2 le_top)) (w.hcs.drift_per t ht)
    (fun d => (w.hcs.AD_smooth d t ht).of_le hN') (fun d => w.hcs.AD_per d t ht)
    (fun r hr v u d => (w.hcs.CE_smooth r hr v u d t ht).of_le hN')
    (fun r hr v u d => w.hcs.CE_per r hr v u d t ht) (hb t ht) (hAD t ht) (hCE t ht) (hJ t ht)
    (hWB t ht) n j hj x

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The lifted pieces of the residual force of the approximants**. Carriers are
additive (`periodicHk_add`, `carrierOf_add`); the commutator remainder `e_n` is periodic
(`defectRemainder_periodic`). At a time of the window, the components of a glued lift with
weights supported in the pulse windows (the glued lift of `e_n` and the partition term
`∑_k ϖ_k' 𝒯_k a_n`) are of class `C^{K_v}` and periodic (`ReconWindowAt.gluedPiece_smooth`), and
their carriers are bounded by the jets of the lifted field (`ReconWindowAt.gluedPiece_carrier_le`). -/

section Single

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The carrier of a sum is the sum of the carriers.** -/
theorem periodicHk_add (K : ℕ) {f g : Vec 2 → E} (hf : ContDiff ℝ (K : ℕ∞) f)
    (hg : ContDiff ℝ (K : ℕ∞) g) (hfp : AVenhance.IsZ2Periodic f)
    (hgp : AVenhance.IsZ2Periodic g) :
    periodicHk K f hf hfp + periodicHk K g hg hgp =
      periodicHk K (fun x => f x + g x) (hf.add hg) (fun n x => by
        show f (x + AVenhance.latticeShift n) + g (x + AVenhance.latticeShift n) = f x + g x
        rw [hfp n x, hgp n x]) := by
  apply Subtype.ext
  ext a : 1
  have hcoe : (periodicHk K f hf hfp + periodicHk K g hg hgp).val a =
      (periodicHk K f hf hfp).val a + (periodicHk K g hg hgp).val a := rfl
  rw [hcoe]
  have hle : a.1.val ≤ K := Nat.lt_succ_iff.1 a.1.isLt
  have hadd := orderedDerivative_add a.2 (hf.of_le (by exact_mod_cast hle))
    (hg.of_le (by exact_mod_cast hle))
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add ((periodicHk K f hf hfp).val a) ((periodicHk K g hg hgp).val a),
    periodicHk_jet_ae K f hf hfp a, periodicHk_jet_ae K g hg hgp a,
    periodicHk_jet_ae K (fun x => f x + g x) (hf.add hg) (fun n x => by
      show f (x + AVenhance.latticeShift n) + g (x + AVenhance.latticeShift n) = f x + g x
      rw [hfp n x, hgp n x]) a] with x hx hfx hgx hdx
  rw [hx, Pi.add_apply, hfx, hgx, hdx, hadd]

/-- **The carrier of a sum of smooth periodic fields.** -/
theorem carrierOf_add (K : ℕ) {f g : Vec 2 → E} (hf : ContDiff ℝ (K : ℕ∞) f)
    (hg : ContDiff ℝ (K : ℕ∞) g) (hfp : AVenhance.IsZ2Periodic f)
    (hgp : AVenhance.IsZ2Periodic g) :
    carrierOf K (fun x => f x + g x) = carrierOf K f + carrierOf K g := by
  rw [carrierOf_eq K hf hfp, carrierOf_eq K hg hgp, periodicHk_add K hf hg hfp hgp,
    carrierOf_eq K (hf.add hg) (fun n x => by
      show f (x + AVenhance.latticeShift n) + g (x + AVenhance.latticeShift n) = f x + g x
      rw [hfp n x, hgp n x])]

end Single

section Defect

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The commutator remainder is periodic** at a time at which the coefficients are periodic and
the classical representative is one. -/
theorem defectRemainder_periodic (n : ℕ) {b : ℝ → Vec 2 → Vec 2} {D H K r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (W : ∀ v, ℝ → TorusHk K (h v))
    (aRep : ℝ → Vec 2 → ∀ i, h i) {s : ℝ}
    (hrep : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hADp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hCEp : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, AVenhance.IsZ2Periodic (CE r v u d s))
    (hbp : AVenhance.IsZ2Periodic (b s)) :
    AVenhance.IsZ2Periodic (defectRemainder n b D H AD CE Jm W aRep s) := by
  have hrn : ∀ u, IsClassicalRep (galerkinProj n (W u s)) (fun x => coarseTraj n W s x u) r₀ :=
    fun u => by
      rw [coarseTraj_eq]
      exact coarseApprox_isClassicalRep n (fun u => W u s) u (hrep u).1
  intro z x
  have h1 := classicalDefectField_periodic (W := fun u _ => galerkinProj n (W u s))
    (aRep := coarseTraj n W) (s := s) (Jm := Jm) hrn hADp hCEp hbp
  have h2 := classicalDefectField_periodic (Jm := Jm) hrep hADp hCEp hbp
  funext v
  simp only [defectRemainder, coarseProjField, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
    coarseMode_periodic n _ z x, h1 v z x]

end Defect

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The components of a glued lift with weights supported in the pulse windows are smooth and
periodic** at a time of the window, for a field of class `C^{N+r}` periodic at that time. -/
theorem ReconWindowAt.gluedPiece_smooth
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {r : ℕ} (hrK : r ≤ Klift) (hrL : r ≤ Llift) (ω : ℤ → ℝ → ℝ)
    (hω : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ t ∈ Set.Icc tp (tp + Tobs), ω k t ≠ 0 →
      t ∈ ocPulseWindow α q Λ m k)
    (u : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs))
    (hu : ContDiff ℝ ((Nc + r : ℕ) : ℕ∞) (u t)) (hup : IsZ2Periodic (u t)) (Kc : ι → ℕ)
    (hKr : ∀ v, Kc v ≤ r) :
    (∀ v, ContDiff ℝ (Kc v : ℕ∞) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) ω (ocEll q
        Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u t x v)) ∧
    (∀ v, IsZ2Periodic (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) ω (ocEll q Λ m ν ^
        2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u t x v)) := by
  have hc := w.gluedLift_weights_contDiff ω hω (J := r) (by omega) (by omega) u ht hu
  have hp := w.gluedLift_weights_periodic ω hω u ht
    (hu.of_le (by exact_mod_cast Nat.le_add_right Nc r)) hup
  exact ⟨fun v => (contDiff_pi.1 hc v).of_le (by exact_mod_cast hKr v),
    fun v l x => congrFun (hp l x) v⟩

/-- **The carriers of the components of a glued lift with bounded weights supported in the pulse
windows are bounded by the jets of the lifted field.** -/
theorem ReconWindowAt.gluedPiece_carrier_le
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {r : ℕ} (hrK : r ≤ Klift) (hrL : r ≤ Llift) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ω : ℤ → ℝ → ℝ) (Cω : ℝ), 0 ≤ Cω →
      (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ t ∈ Set.Icc tp (tp + Tobs), ω k t ≠ 0 →
        t ∈ ocPulseWindow α q Λ m k) →
      ∀ (u : ℝ → Vec 2 → ∀ i, h i) (t : ℝ), t ∈ Set.Icc tp (tp + Tobs) →
      (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), |ω k t| ≤ Cω) →
      ContDiff ℝ ((Nc + r : ℕ) : ℕ∞) (u t) → IsZ2Periodic (u t) → ∀ A : ℝ, 0 ≤ A →
      (∀ i ≤ Nc + r, ∀ y, ‖iteratedFDeriv ℝ i (u t) y‖ ≤ A) → ∀ v,
        ‖carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) ω (ocEll q Λ m ν
            ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) u t x v)‖ ≤
          (Fintype.card (JetIndex2 (Kc v)) : ℝ) * (Cω * M * A) := by
  obtain ⟨M, hM0, hM⟩ := w.gluedLift_weights_jet_le (J := r) (by omega) (by omega)
  refine ⟨M, hM0, fun ω Cω hCω hω u t ht hωb hu hup A hA hjet v => ?_⟩
  obtain ⟨hs, hp⟩ := w.gluedPiece_smooth hrK hrL ω hω u ht hu hup Kc hKr
  have hc := w.gluedLift_weights_contDiff ω hω (J := r) (by omega) (by omega) u ht hu
  refine carrierOf_norm_le_of_jet (Kc v) (hs v) (hp v) (by positivity) fun j hj x => ?_
  have hjr : j ≤ r := hj.trans (hKr v)
  exact (norm_iteratedFDeriv_component_le (hc.of_le (by exact_mod_cast hjr)) v x).trans
    (hM ω Cω hCω hω u t ht hωb hu A hjet j hjr x)

end AVRegularity.CycleComparison.Reconstruction
end
