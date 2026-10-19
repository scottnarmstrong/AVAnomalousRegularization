-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Parts.EdgeD
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.QuietDecay.Lift.Recentre

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal NNReal ContDiff
namespace AVRegularity.QuietDecay

/-! **The source term built from the quiet means (the "E" part of the quiet source).** The quiet
mean of the grade `1` is `-𝒮_{n-j}` of the slow-only test field, a combination of edge coefficients
and slow derivatives of the test field, so its slow jets at `X` are bounded by the edge envelope;
the outer lift action contributes the block jets of the coefficient blocks, a right product. -/

section SlowOnly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem edge_volume_unitCube : volume (AVenhance.unitCube : Set (Vec 2)) = 1 := by
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp

/-- The cell `L²` mixed jet of a slow-only field with no fast derivatives is the norm of the slow
jet. -/
theorem edge_ptJet_slowOnly_zero (g : Vec 2 → E) (X : Vec 2) (a : ℕ) :
    ptJet (fun X' (_ : Vec 2) => g X') X a 0 = ‖iteratedFDeriv ℝ a g X‖ₑ := by
  have e : (fun z : Vec 2 => ‖iteratedFDeriv ℝ a (fun X' =>
      iteratedFDeriv ℝ 0 (fun _ : Vec 2 => g X') z) X‖) = fun _ => ‖iteratedFDeriv ℝ a g X‖ := by
    funext z
    have : (fun X' => iteratedFDeriv ℝ 0 (fun _ : Vec 2 => g X') z) =
        (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm ∘ g := by
      funext X'; rw [iteratedFDeriv_zero_eq_comp]; rfl
    rw [this]
    exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left _ _ _ _
  unfold ptJet
  rw [e, eLpNorm_const _ (by norm_num) (by simp [edge_volume_unitCube]),
    Measure.restrict_apply_univ, edge_volume_unitCube]
  simp

theorem edge_ptJet_slowOnly_le (g : Vec 2 → E) (X : Vec 2) (a b' : ℕ) :
    ptJet (fun X' (_ : Vec 2) => g X') X a b' ≤ ‖iteratedFDeriv ℝ a g X‖ₑ := by
  rcases Nat.eq_zero_or_pos b' with rfl | hb
  · exact (edge_ptJet_slowOnly_zero g X a).le
  · have e : (fun z : Vec 2 => ‖iteratedFDeriv ℝ a (fun X' =>
        iteratedFDeriv ℝ b' (fun _ : Vec 2 => g X') z) X‖) = fun _ => 0 := by
      funext z
      have : (fun X' => iteratedFDeriv ℝ b' (fun _ : Vec 2 => g X') z) = fun _ => 0 := by
        funext X'; rw [iteratedFDeriv_const_of_ne hb.ne']; rfl
      rw [this, iteratedFDeriv_fun_zero]; simp
    unfold ptJet
    rw [e]
    simp

end SlowOnly

section Words

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem edge_norm_derivList_le (L : List (Fin 2)) {g : Vec 2 → V}
    (hg : ContDiff ℝ (L.length : ℕ∞) g) (X : Vec 2) :
    ‖derivList L g X‖ ≤ ‖iteratedFDeriv ℝ L.length g X‖ := by
  have := norm_orderedDerivative_le hg L.get X
  rwa [orderedDerivative_eq_derivList, List.ofFn_get] at this

theorem edge_norm_iteratedFDeriv_le_words {q : ℕ} {g : Vec 2 → V} (hg : ContDiff ℝ (q : ℕ∞) g)
    (X : Vec 2) :
    ‖iteratedFDeriv ℝ q g X‖ ≤ ∑ w : DerivativeWord2 q, ‖orderedDerivative w g X‖ := by
  have h1 := norm_le_sum_basisVec (iteratedFDeriv ℝ q g X)
  have h2 : ∑ w : DerivativeWord2 q, ‖iteratedFDeriv ℝ q g X (fun i => basisVec (w i))‖ =
      ∑ w : DerivativeWord2 q, ‖orderedDerivative w g X‖ := by
    rw [← Equiv.sum_comp (wordRev q)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [orderedDerivative_eq_iteratedFDeriv w hg]
    rfl
  rwa [h2] at h1

end Words

section Test

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The full jets of the test field at its centre. -/
theorem edge_testField_iter_le (X : Vec 2) (β : List (Fin 2)) (y : E) (a : ℕ) :
    ‖iteratedFDeriv ℝ a (fun Y => monoF X β Y • y) X‖ ≤
      2 ^ a * ((β.length.factorial : ℝ) * ‖y‖) := by
  have hg : ContDiff ℝ (a : ℕ∞) (fun Y => monoF X β Y • y) :=
    ((contDiff_monoF X (a : WithTop ℕ∞) β).smul contDiff_const)
  refine (edge_norm_iteratedFDeriv_le_words hg X).trans ?_
  have : ∀ w : DerivativeWord2 a, ‖orderedDerivative w (fun Y => monoF X β Y • y) X‖ ≤
      (β.length.factorial : ℝ) * ‖y‖ := by
    intro w
    rw [orderedDerivative_eq_derivList, derivList_smul_const y _ _ (contDiff_monoF X ∞ β),
      norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (derivList_monoF_abs_le X X (by simp) _ β) (norm_nonneg _)
  refine (Finset.sum_le_sum fun w _ => this w).trans (le_of_eq ?_)
  rw [Finset.sum_const, card_derivativeWord2]
  simp

end Test

section Xi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

omit [Fintype ι] in
/-- The jets of the components of the test field, summed as in `srcBoundE`. -/
theorem edge_Phi0_B_le (D : ℕ) (X : Vec 2) (β : List (Fin 2)) (u : ι) (x : h u) (hx : ‖x‖ ≤ 1)
    (u'' : ι) (R n' r : ℕ) (hr : r ≤ R) :
    ∑ a ∈ Finset.range (r + n' + 1), ∑ b' ∈ Finset.range (0 + D + 1),
      srcPtJet (fun X' (_ : Vec 2) =>
        (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) X' u'') X a b' ≤
      (((R + n' + 1) * (D + 1) : ℕ) : ℝ≥0∞) *
        (((2 ^ (R + n') * β.length.factorial : ℕ) : ℝ≥0∞) * if u'' = u then 1 else 0) := by
  have hterm : ∀ a ∈ Finset.range (r + n' + 1), ∀ b' : ℕ,
      srcPtJet (fun X' (_ : Vec 2) =>
        (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) X' u'') X a b' ≤
      (((2 ^ (R + n') * β.length.factorial : ℕ) : ℝ≥0∞)) * if u'' = u then 1 else 0 := by
    intro a ha b'
    have ha' := Finset.mem_range.1 ha
    refine le_trans (edge_ptJet_slowOnly_le (fun Y => monoF X β Y •
      (Pi.single u x : ∀ i, h i) u'') X a b') ?_
    have h1 := edge_testField_iter_le X β ((Pi.single u x : ∀ i, h i) u'') a
    have h2 := enorm_le_ofReal_of_norm_le h1
    refine h2.trans ?_
    rcases eq_or_ne u'' u with rfl | hu
    · simp only [Pi.single_eq_same, ite_true, mul_one]
      rw [← ENNReal.ofReal_natCast]
      refine ENNReal.ofReal_le_ofReal ?_
      push_cast
      have : (2 : ℝ) ^ a ≤ 2 ^ (R + n') := pow_le_pow_right₀ (by norm_num) (by omega)
      have hK : (0 : ℝ) ≤ β.length.factorial := by positivity
      calc (2 : ℝ) ^ a * ((β.length.factorial : ℝ) * ‖x‖) ≤ 2 ^ a * ((β.length.factorial : ℝ) * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx hK) (by positivity)
        _ ≤ 2 ^ (R + n') * (β.length.factorial : ℝ) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_right this hK
    · simp [hu]
  calc _ ≤ ∑ a ∈ Finset.range (r + n' + 1), ∑ b' ∈ Finset.range (0 + D + 1),
        (((2 ^ (R + n') * β.length.factorial : ℕ) : ℝ≥0∞) * if u'' = u then 1 else 0) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b' _ => hterm a ha b'
    _ = (((r + n' + 1) * (0 + D + 1) : ℕ) : ℝ≥0∞) *
        (((2 ^ (R + n') * β.length.factorial : ℕ) : ℝ≥0∞) * if u'' = u then 1 else 0) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring
    _ ≤ _ := mul_le_mul' (by exact_mod_cast Nat.mul_le_mul (by omega) (by omega)) le_rfl

variable {D : ℕ}

/-- **The slow jets of the quiet mean of grade `1`**: the norm at `X` of the `r`-th slow jet of
`X' ↦ 𝒮_{n'}(slow-only test field)(X', 0)_{u'}` is bounded by the edge envelope. -/
theorem edge_E_xi_le (Q : LiftOperatorData ι h D) (σ : ℝ) (hη : Q.η ≤ 1)
    (hquiet : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α X z z', γ.coeff α σ X z = γ.coeff α σ X z')
    (X : Vec 2) (β : List (Fin 2)) (u : ι) (x : h u) (hx : ‖x‖ ≤ 1) {R n' r : ℕ} (hr : r ≤ R)
    (hedge : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α z,
      ContDiff ℝ ((R + 1 : ℕ) : ℕ∞) (fun Y => γ.coeff α σ Y z)) (u' : ι) :
    ‖iteratedFDeriv ℝ r (fun X' => sourceCoeff Q.edge Q.η n' σ (fun X'' _ =>
        (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) X'') X' 0 u') X‖ₑ ≤
      ((6 * 2 ^ (R + D) : ℕ) : ℝ≥0∞) * (edgeEnv Q σ X u' u (R + 1) *
        ((((R + n' + 1) * (D + 1) : ℕ) : ℝ≥0∞) *
          ((2 ^ (R + n') * β.length.factorial : ℕ) : ℝ≥0∞))) := by
  set b : Vec 2 → ∀ i, h i := fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i) with hb
  set Φ0 : Vec 2 → Vec 2 → ∀ i, h i := fun X'' _ => b X'' with hΦ0def
  have hΦ0 : IsBoxSmooth (R + D) D Φ0 :=
    edge_isBoxSmooth_slowOnly (g := b) (edge_contDiff_testField X β u x _)
  have hfast : FastIndep (sourceCoeff Q.edge Q.η n' σ Φ0) :=
    sourceCoeff_fastIndep Q.edge Q.η σ n' hquiet (fun _ _ _ => rfl)
  have hedge0 : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α z,
      ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun X => γ.coeff α σ X z) := fun v w d γ hγ α z =>
    (hedge v w d γ hγ α z).of_le (by exact_mod_cast (by omega : r + 1 ≤ R + 1))
  have hsq : Real.sqrt Q.η ≤ 1 := (Real.sqrt_le_sqrt hη).trans_eq Real.sqrt_one
  have e1 : (fun X' (_ : Vec 2) => sourceCoeff Q.edge Q.η n' σ Φ0 X' 0 u') =
      fun X' z => sourceCoeff Q.edge Q.η n' σ Φ0 X' z u' :=
    funext fun X' => funext fun z => by rw [hfast X' 0 z]
  have e2 := edge_ptJet_slowOnly_zero (fun X' => sourceCoeff Q.edge Q.η n' σ Φ0 X' 0 u') X r
  rw [← e2, e1]
  have h2 := srcPtJet_sourceCoeff_le_box Q.edge Q.η σ hsq hquiet hΦ0 r 0 n'
    (by omega) (by omega) hedge0 X u'
  rw [edge_srcBoundE_eq] at h2
  have hc6 : ((6 * 2 ^ (r + D) : ℕ) : ℝ≥0∞) ≤ ((6 * 2 ^ (R + D) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine h2.trans (mul_le_mul' hc6 ?_)
  calc _ ≤ ∑ u'' : ι, edgeEnv Q σ X u' u'' (R + 1) *
        ((((R + n' + 1) * (D + 1) : ℕ) : ℝ≥0∞) *
          (((2 ^ (R + n') * β.length.factorial : ℕ) : ℝ≥0∞) * if u'' = u then 1 else 0)) :=
        Finset.sum_le_sum fun u'' _ => mul_le_mul' (edgeEnv_mono Q σ X u' u'' (by omega))
          (edge_Phi0_B_le D X β u x hx u'' R n' r hr)
    _ = _ := by
        rw [Finset.sum_eq_single u]
        · simp
        · intro u'' _ hu''
          simp [hu'']
        · intro hu; exact absurd (Finset.mem_univ u) hu

omit [DecidableEq ι] in
theorem edge_liftApply_congr_at (n : ℕ) (c : LiftCoeff ι h) {a a' : ℝ → Vec 2 → ∀ i, h i}
    {t : ℝ} (ha : a t = a' t) : liftApply n c a t = liftApply n c a' t := by
  unfold liftApply
  rw [ha]

omit [DecidableEq ι] in
theorem edge_quietMeanOp_one (Q : LiftOperatorData ι h D) (a₀ : Vec 2 → ∀ i, h i) (n' : ℕ)
    (s : ℝ) (X' : Vec 2) :
    quietMeanOp Q a₀ 1 n' s X' = -sourceCoeff Q.edge Q.η n' s (fun X'' _ => a₀ X'') X' 0 := by
  simp [quietMeanOp]

/-- The constant bounding the slow jets of the quiet mean. -/
def edgeCm (D p n j : ℕ) (β : List (Fin 2)) : ℕ :=
  6 * 2 ^ (p + j + D) * (((p + j + (n - j) + 1) * (D + 1)) * (2 ^ (p + j + (n - j)) *
    β.length.factorial))

/-- The explicit constant of `edge_E_bound`. -/
def edgeCE (D p q n j : ℕ) (β : List (Fin 2)) : ℕ :=
  2 ^ (p + q) * ((j + 1) * 2 ^ j * 2 ^ p) * edgeCm D p n j β

/-- The fixed vectors of the outer lift action: the slow jets of the quiet mean. -/
theorem edge_E_hM (Q : LiftOperatorData ι h D) (σ : ℝ) (hη : Q.η ≤ 1)
    (hquiet : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α X z z', γ.coeff α σ X z = γ.coeff α σ X z')
    (X : Vec 2) (β : List (Fin 2)) (u : ι) (x : h u) (hx : ‖x‖ ≤ 1) {p n j p0 : ℕ}
    (hp0 : p0 ≤ p) (hjn : j < n)
    (hedge : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α z,
      ContDiff ℝ ((p + n : ℕ) : ℕ∞) (fun Y => γ.coeff α σ Y z))
    (A : Vec 2 → ∀ i, h i)
    (hAeq : A = fun X' => -sourceCoeff Q.edge Q.η (n - j) σ (fun X'' _ =>
      (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) X'') X' 0)
    (hAs : ContDiff ℝ ((p0 + j : ℕ) : ℕ∞) A) :
    ∀ m' ≤ j, ∀ α : DerivativeWord2 m', ∀ u' : ι, ∀ l2 : List (Fin 2),
      l2.length + m' ≤ p0 + j →
      ‖derivList l2 (fun X' => orderedDerivative α A X' u') X‖ₑ ≤
        (edgeCm D p n j β : ℝ≥0∞) * edgeEnv Q σ X u' u (p + n) := by
  intro m' hm' α u' l2 hlen
  have hAm : ContDiff ℝ (m' : ℕ∞) A := hAs.of_le (by exact_mod_cast (by omega : m' ≤ p0 + j))
  have e1 : (fun X' => orderedDerivative α A X' u') =
      derivList (List.ofFn α) (fun X' => A X' u') := by
    funext X'
    exact (congrFun (orderedDerivative_clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) u')
      α hAm) X').symm
  rw [e1, derivList_append']
  have hLlen : (List.ofFn α ++ l2).length ≤ p0 + j := by
    rw [List.length_append, List.length_ofFn]; omega
  have hg : ContDiff ℝ ((List.ofFn α ++ l2).length : ℕ∞) (fun X' => A X' u') :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := h) u').contDiff.comp hAs).of_le
      (by exact_mod_cast hLlen)
  have h2 := edge_norm_derivList_le (List.ofFn α ++ l2) hg X
  have h3 : ‖derivList (List.ofFn α ++ l2) (fun X' => A X' u') X‖ₑ ≤
      ‖iteratedFDeriv ℝ (List.ofFn α ++ l2).length (fun X' => sourceCoeff Q.edge Q.η (n - j) σ
        (fun X'' _ => (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) X'') X' 0 u') X‖ₑ := by
    rw [enorm_le_iff_norm_le]
    refine h2.trans (le_of_eq ?_)
    have : (fun X' => A X' u') = -(fun X' => sourceCoeff Q.edge Q.η (n - j) σ
        (fun X'' _ => (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) X'') X' 0 u') := by
      funext X'; rw [hAeq]; rfl
    rw [this, iteratedFDeriv_neg_apply, norm_neg]
  refine h3.trans ?_
  refine (edge_E_xi_le Q σ hη hquiet X β u x hx (R := p + j) (n' := n - j)
    (r := (List.ofFn α ++ l2).length) (by omega) (fun v w d γ hγ α z => (hedge v w d γ hγ α z).of_le
      (by exact_mod_cast (by omega : p + j + 1 ≤ p + n))) u').trans ?_
  have hE := edgeEnv_mono Q σ X u' u (r := p + j + 1) (r' := p + n) (by omega)
  calc _ ≤ ((6 * 2 ^ (p + j + D) : ℕ) : ℝ≥0∞) * (edgeEnv Q σ X u' u (p + n) *
        ((((p + j + (n - j) + 1) * (D + 1) : ℕ) : ℝ≥0∞) *
          ((2 ^ (p + j + (n - j)) * β.length.factorial : ℕ) : ℝ≥0∞))) :=
        mul_le_mul' le_rfl (mul_le_mul' hE le_rfl)
    _ = (edgeCm D p n j β : ℝ≥0∞) * edgeEnv Q σ X u' u (p + n) := by
        simp only [edgeCm]; push_cast; ring

/-- The quiet mean of the grade `1` of the test field is smooth. -/
theorem edge_E_smooth (Q : LiftOperatorData ι h D) (σ : ℝ)
    (hquiet : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α X z z', γ.coeff α σ X z = γ.coeff α σ X z')
    (X : Vec 2) (β : List (Fin 2)) (u : ι) (x : h u) {p n j p0 : ℕ} (hp0 : p0 ≤ p) (hjn : j < n)
    (hedge : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α z,
      ContDiff ℝ ((p + n : ℕ) : ℕ∞) (fun Y => γ.coeff α σ Y z)) :
    ContDiff ℝ ((p0 + j : ℕ) : ℕ∞) (fun X' => -sourceCoeff Q.edge Q.η (n - j) σ (fun X'' _ =>
      (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) X'') X' 0) := by
  have hedge1 : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α z,
      ContDiff ℝ ((p0 + j + 1 : ℕ) : ℕ∞) (fun X => γ.coeff α σ X z) := fun v w d γ hγ α z =>
    (hedge v w d γ hγ α z).of_le (by exact_mod_cast (by omega : p0 + j + 1 ≤ p + n))
  have hΦ0 : IsBoxSmooth (p0 + j + D) D (fun X'' (_ : Vec 2) =>
      (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) X'') :=
    edge_isBoxSmooth_slowOnly (edge_contDiff_testField X β u x _)
  have hS := edge_isBoxSmooth_sourceCoeff Q.edge Q.η σ hquiet hΦ0 (n - j) (p := p0 + j) (q := 0)
    (by omega) (by omega) (by omega) (by omega) hedge1
  exact (hS.contDiff_slow 0).neg

omit [DecidableEq ι] in
/-- The assembly of the `E` part for an abstract input field `A`. -/
theorem edge_E_assemble (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (σ : ℝ)
    {p q n j hh : ℕ}
    (hc : ∀ m α w u', IsBoxSmooth p q (fun X z => Cc (hh - 1) j m α σ X z w u'))
    (X : Vec 2) (β : List (Fin 2)) (u : ι) {l m : List (Fin 2)} (hl : l.length ≤ p)
    (hm : m.length ≤ q) (v : ι) (A : Vec 2 → ∀ i, h i)
    (hAs : ContDiff ℝ ((l.length + j : ℕ) : ℕ∞) A)
    (hM : ∀ m' ≤ j, ∀ α : DerivativeWord2 m', ∀ u' : ι, ∀ l2 : List (Fin 2),
      l2.length + m' ≤ l.length + j →
      ‖derivList l2 (fun X' => orderedDerivative α A X' u') X‖ₑ ≤
        (edgeCm D p n j β : ℝ≥0∞) * edgeEnv Q σ X u' u (p + n)) :
    vecJ (fun X' z => liftApply j (Cc (hh - 1) j) (fun _ => A) σ X' z v) X l m ≤
      ENNReal.ofReal (edgeCE D p q n j β : ℝ) * ∑ w : ι,
        blkJ Cc (hh - 1) j σ v w p q * edgeEnv Q σ X w u (p + n) := by
  have hGbox := edge_isBoxSmooth_liftApply (Cc (hh - 1) j) j A σ v
    (fun m α u' => (hc m α v u').mono hl hm) hAs
  have h1 := edge_vecJ_le_ptJet hGbox l m le_rfl le_rfl X
  have key := edge_ptJet_liftApply_le Cc (hh - 1) j σ v (a := l.length) (b' := m.length)
    (sX := p) (sZ := q) hl hm (fun m α u' => hc m α v u') A hAs X
    (fun u' => (edgeCm D p n j β : ℝ≥0∞) * edgeEnv Q σ X u' u (p + n)) hM
  have hmono : ∀ u' : ι, blkJ Cc (hh - 1) j σ v u' l.length m.length ≤
      blkJ Cc (hh - 1) j σ v u' p q := fun u' => edge_blkJ_mono _ _ _ _ _ _ hl hm
  refine h1.trans (key.trans ?_)
  have hp1 : (2 : ℝ≥0∞) ^ (l.length + m.length) ≤ 2 ^ (p + q) :=
    pow_right_mono₀ one_le_two (by omega)
  have hp2 : (2 : ℝ≥0∞) ^ l.length ≤ 2 ^ p := pow_right_mono₀ one_le_two hl
  calc _ ≤ 2 ^ (p + q) * (((j + 1 : ℕ) : ℝ≥0∞) * 2 ^ j * 2 ^ p *
        ∑ u' : ι, (edgeCm D p n j β : ℝ≥0∞) * edgeEnv Q σ X u' u (p + n) *
          blkJ Cc (hh - 1) j σ v u' p q) :=
        mul_le_mul' hp1 (mul_le_mul' (mul_le_mul' le_rfl hp2)
          (Finset.sum_le_sum fun u' _ => mul_le_mul' le_rfl (hmono u')))
    _ = _ := by
        rw [ENNReal.ofReal_natCast, edgeCE]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u' _ => ?_
        push_cast; ring

/-- **The `E` part of the quiet source.** `S_E = p`, `F_E = q`, and the constant is
`edgeCE D p q n j β` (a right product: the lift action acts on the quiet mean, which carries the
edge). -/
theorem edge_E_bound (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (σ : ℝ)
    (hη : Q.η ≤ 1)
    (hquiet : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α X z z', γ.coeff α σ X z = γ.coeff α σ X z')
    {p q n j hh : ℕ} (hjn : j < n)
    (hedge : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α z,
      ContDiff ℝ ((p + n : ℕ) : ℕ∞) (fun Y => γ.coeff α σ Y z))
    (hc : ∀ m α w u', IsBoxSmooth p q (fun X z => Cc (hh - 1) j m α σ X z w u'))
    (X : Vec 2) (β : List (Fin 2)) (u : ι) (x : h u) (hx : ‖x‖ ≤ 1)
    {l m : List (Fin 2)} (hl : l.length ≤ p) (hm : m.length ≤ q) (v : ι) :
    vecJ (fun X' z => liftApply j (Cc (hh - 1) j) (fun s X' => quietMeanOp Q
        (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) 1 (n - j) s X') σ X' z v) X l m ≤
      ENNReal.ofReal (edgeCE D p q n j β : ℝ) * ∑ w : ι,
        blkJ Cc (hh - 1) j σ v w p q * edgeEnv Q σ X w u (p + n) := by
  have hAeq : (fun X' => quietMeanOp Q (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) 1
      (n - j) σ X') = fun X' => -sourceCoeff Q.edge Q.η (n - j) σ (fun X'' _ =>
      (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) X'') X' 0 :=
    funext fun X' => edge_quietMeanOp_one Q _ (n - j) σ X'
  have hAs := edge_E_smooth Q σ hquiet X β u x (p0 := l.length) hl hjn hedge (j := j)
  rw [← hAeq] at hAs
  have hM := edge_E_hM Q σ hη hquiet X β u x hx hl hjn hedge _ hAeq hAs
  have e : liftApply j (Cc (hh - 1) j) (fun s X' => quietMeanOp Q
      (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) 1 (n - j) s X') σ =
      liftApply j (Cc (hh - 1) j) (fun _ X' => quietMeanOp Q
        (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) 1 (n - j) σ X') σ :=
    edge_liftApply_congr_at j (Cc (hh - 1) j) rfl
  rw [e]
  exact edge_E_assemble Q Cc σ hc X β u hl hm v (fun X' => quietMeanOp Q
    (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) 1 (n - j) σ X') hAs hM

end Xi

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The lift layer of the metric parts: the Leibniz terms of the `L²` mixed jets of one component
of a lift action on a field concentrated in one component are bounded by the block jets of the
coefficients, with vector factors of bounded norm (`metric_term_le`, `metric_word_le`,
`metric_ptJet_lift_le`). -/

section
section Smul

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem metric_deriv_smul_const {m : ℕ} (α : DerivativeWord2 m) (s2 : List (Fin 2))
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ ((m + s2.length : ℕ) : ℕ∞) f) (w0 : ∀ i, h i) (u : ι)
    (X : Vec 2) :
    derivList s2 (fun X' => orderedDerivative α (fun Y => f Y • w0) X' u) X =
      derivList (List.ofFn α ++ s2) f X • w0 u := by
  have hfm : ContDiff ℝ (m : ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_add_right _ _)
  have hb : ContDiff ℝ (m : ℕ∞) (fun Y => f Y • w0) := hfm.smul contDiff_const
  have h1 : ∀ X', orderedDerivative α (fun Y => f Y • w0) X' u =
      derivList (List.ofFn α) f X' • w0 u := by
    intro X'
    have h2 := congrFun (orderedDerivative_clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)
      α hb) X'
    have h4 := congrFun (orderedDerivative_clm_comp
      (ContinuousLinearMap.toSpanSingleton ℝ (w0 u)) α hfm) X'
    exact h2.symm.trans h4
  have hg : ContDiff ℝ (s2.length : ℕ∞) (derivList (List.ofFn α) f) := by
    refine contDiff_derivList (List.ofFn α) f s2.length ?_
    simpa using hf
  simp only [h1]
  have := congrFun (metric_derivList_clm (ContinuousLinearMap.toSpanSingleton ℝ (w0 u)) s2 hg) X
  rw [metric_derivList_append] at this
  exact this

/-- Derivative data of a field `f • w0` concentrated in the component `u`: the components other
than `u` vanish and the `u` component is bounded by the derivative bound of `f`. -/
theorem metric_smul_bounds {N i : ℕ} {f : Vec 2 → ℝ} (hf : ContDiff ℝ ((i + N : ℕ) : ℕ∞) f)
    (w0 : ∀ i, h i) (u : ι) (hw0 : ∀ u' ≠ u, w0 u' = 0) (X : Vec 2) {B : ℝ}
    (hB : ∀ L : List (Fin 2), L.length ≤ i + N → |derivList L f X| ≤ B) (hw : ‖w0 u‖ ≤ 1) :
    (∀ u' ≠ u, ∀ m (α : DerivativeWord2 m), m ≤ N → ∀ s2 : List (Fin 2), s2.length ≤ i →
      derivList s2 (fun X' => orderedDerivative α (fun Y => f Y • w0) X' u') X = 0) ∧
    (∀ m (α : DerivativeWord2 m), m ≤ N → ∀ s2 : List (Fin 2), s2.length ≤ i →
      ‖derivList s2 (fun X' => orderedDerivative α (fun Y => f Y • w0) X' u) X‖ ≤ B) := by
  have hf' : ∀ m (α : DerivativeWord2 m), m ≤ N → ∀ s2 : List (Fin 2), s2.length ≤ i →
      ContDiff ℝ ((m + s2.length : ℕ) : ℕ∞) f := fun m α hm s2 hs =>
    hf.of_le (by exact_mod_cast (by omega : m + s2.length ≤ i + N))
  refine ⟨fun u' hu' m α hm s2 hs => ?_, fun m α hm s2 hs => ?_⟩
  · rw [metric_deriv_smul_const α s2 (hf' m α hm s2 hs) w0 u' X, hw0 u' hu', smul_zero]
  · rw [metric_deriv_smul_const α s2 (hf' m α hm s2 hs) w0 u X, norm_smul, Real.norm_eq_abs]
    have h1 := hB (List.ofFn α ++ s2) (by simp; omega)
    calc |derivList (List.ofFn α ++ s2) f X| * ‖w0 u‖ ≤ B * 1 :=
          mul_le_mul h1 hw (norm_nonneg _) ((abs_nonneg _).trans h1)
      _ = B := mul_one B

end Smul


section Term

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- Scaling a vector: a vector of norm at most `R` is `R` times a vector of norm at most one. -/
theorem metric_exists_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ξ : E) {R : ℝ}
    (hR : 0 ≤ R) (hξ : ‖ξ‖ ≤ R) : ∃ η : E, ‖η‖ ≤ 1 ∧ ξ = R • η := by
  rcases hR.eq_or_lt with rfl | hpos
  · have : ξ = 0 := norm_le_zero_iff.1 hξ
    exact ⟨0, by simp, by simp [this]⟩
  · refine ⟨R⁻¹ • ξ, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Real.norm_of_nonneg hR]
      calc R⁻¹ * ‖ξ‖ ≤ R⁻¹ * R := by gcongr
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

omit [Fintype ι] in
/-- A Leibniz term of a lift action: the slow word `s1` of the fast word `β` of the coefficient
block, applied to a vector of norm at most `R`, is controlled by the block jet. -/
theorem metric_term_le {N sX sZ : ℕ} (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (σ : ℝ) (v u : ι)
    {m : ℕ} (α : DerivativeWord2 m) (hm : m ≤ N)
    (hcb : IsBoxSmooth sX sZ (fun X z => Cc hh N m α σ X z v u))
    (s1 : List (Fin 2)) {q : ℕ} (β : DerivativeWord2 q) (hs1 : s1.length + 1 ≤ sX) (hq : q ≤ sZ)
    (S F : ℕ) (hS : s1.length ≤ S) (hF : q ≤ F) (X : Vec 2) (ξ : h u) {R : ℝ} (hR : 0 ≤ R)
    (hξ : ‖ξ‖ ≤ R) :
    eLpNorm (fun z => derivList s1
      (fun X' => orderedDerivative β (fun z' => Cc hh N m α σ X' z' v u) z) X ξ) 2
      (volume.restrict AVenhance.unitCube) ≤ ENNReal.ofReal R * blkJ Cc hh N σ v u S F := by
  obtain ⟨η, hη, hξη⟩ := metric_exists_unit ξ hR hξ
  set Cop : Vec 2 → Vec 2 → (h u →L[ℝ] h v) := fun X z => Cc hh N m α σ X z v u with hCop
  set Lη : (h u →L[ℝ] h v) →L[ℝ] h v := ContinuousLinearMap.apply ℝ (h v) η with hLη
  have hlen : (List.ofFn β).length = q := List.length_ofFn
  have hsl : IsSlowSmooth (s1.length + 1) Cop := hcb.isSlowSmooth.mono hs1
  have hbox : IsBoxSmooth s1.length (List.ofFn β).length Cop :=
    hcb.mono (by omega) (by omega)
  have hbox' : IsBoxSmooth (0 + s1.length) (List.ofFn β).length Cop := by
    simpa using hbox
  have hcd : ContDiff ℝ ((List.ofFn β).length : ℕ∞) (slowDerivs s1 Cop X) := by
    have := (isBoxSmooth_slowIter s1 0 Cop hbox').1 X
    rwa [slowIter_eq_slowDerivs] at this
  have key : ∀ z, derivList s1
      (fun X' => orderedDerivative β (fun z' => Cc hh N m α σ X' z' v u) z) X ξ =
      R • fastDerivs (List.ofFn β) (slowDerivs s1 (fun X z => Lη (Cop X z)) X) z := by
    intro z
    rw [slowDerivs_clm Lη s1 hsl, fastDerivs_clm Lη (List.ofFn β) hcd]
    have e : derivList s1 (fun X' => orderedDerivative β
        (fun z' => Cc hh N m α σ X' z' v u) z) X =
        fastDerivs (List.ofFn β) (slowDerivs s1 Cop X) z :=
      (metric_fastDerivs_slowDerivs_eq s1 (List.ofFn β) hbox X z).symm
    rw [e, hξη, map_smul]
    rfl
  have e2 : (fun z => derivList s1
      (fun X' => orderedDerivative β (fun z' => Cc hh N m α σ X' z' v u) z) X ξ) =
      R • fun z => fastDerivs (List.ofFn β) (slowDerivs s1
        (fun X z => Cc hh N m α σ X z v u η) X) z := by
    funext z
    exact key z
  rw [e2, eLpNorm_const_smul, Real.enorm_eq_ofReal hR]
  refine mul_le_mul' le_rfl ?_
  exact vecJ_le_blkJ Cc hh N σ v u S F hm α s1 (List.ofFn β) hS (by omega) X η hη

end Term

section Word

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem metric_sum_two_pow_le (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), (2 : ℝ≥0∞) ^ m ≤ 2 ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ _ (N + 1)]
    calc _ ≤ 2 ^ (N + 1) + 2 ^ (N + 1) := add_le_add ih le_rfl
      _ = 2 ^ (N + 1) * 2 := by ring

/-- The word layer: the mixed word derivative of one component of a lift action on a field `b`
concentrated in the component `u`, in terms of the block jet of the coefficients. -/
theorem metric_word_le {N i q sX sZ : ℕ} (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (σ : ℝ)
    (v u : ι) (hi : i + 1 ≤ sX) (hq : q ≤ sZ)
    (hc : ∀ m (α : DerivativeWord2 m) u', IsBoxSmooth sX sZ (fun X z => Cc hh N m α σ X z v u'))
    (b : Vec 2 → ∀ i, h i) (hb : ContDiff ℝ ((i + N : ℕ) : ℕ∞) b) {R : ℝ} (hR : 0 ≤ R)
    (X : Vec 2)
    (hbu : ∀ u' ≠ u, ∀ m (α : DerivativeWord2 m), m ≤ N → ∀ s2 : List (Fin 2), s2.length ≤ i →
      derivList s2 (fun X' => orderedDerivative α b X' u') X = 0)
    (hξ : ∀ m (α : DerivativeWord2 m), m ≤ N → ∀ s2 : List (Fin 2), s2.length ≤ i →
      ‖derivList s2 (fun X' => orderedDerivative α b X' u) X‖ ≤ R)
    (w : DerivativeWord2 i) (β : DerivativeWord2 q) (S F : ℕ) (hS : i ≤ S) (hF : q ≤ F) :
    eLpNorm (fun z => orderedDerivative w (fun X' => orderedDerivative β
        (fun z' => liftApply N (Cc hh N) (fun _ => b) σ X' z' v) z) X) 2
      (volume.restrict AVenhance.unitCube) ≤
      2 ^ (N + 1) * (2 ^ i * (ENNReal.ofReal R * blkJ Cc hh N σ v u S F)) := by
  classical
  refine (eLpNorm_liftApply_word_le (p := i) (q := q) (n := N) (by omega) hq (Cc hh N) b σ v hc hb w
    β X).trans ?_
  set K : ℝ≥0∞ := ENNReal.ofReal R * blkJ Cc hh N σ v u S F with hK
  have hterm : ∀ m ∈ Finset.range (N + 1), ∀ (α : DerivativeWord2 m) (u' : ι)
      (s : Fin i → Bool), eLpNorm (fun z =>
        derivList (splitWord i w s).1
          (fun X' => orderedDerivative β (fun z' => Cc hh N m α σ X' z' v u') z) X
          (derivList (splitWord i w s).2 (fun X' => orderedDerivative α b X' u') X)) 2
        (volume.restrict AVenhance.unitCube) ≤ if u' = u then K else 0 := by
    intro m hm α u' s
    have hmN : m ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have hlen := splitWord_length i w s
    by_cases hu : u' = u
    · subst hu
      simp only [↓reduceIte]
      exact metric_term_le Cc hh σ v u' α hmN (hc m α u') (splitWord i w s).1 β (by omega) hq S F
        (by omega) hF X _ hR (hξ m α hmN _ (by omega))
    · rw [hbu u' hu m α hmN _ (by omega)]
      simp [hu]
  refine (Finset.sum_le_sum fun m hm => (Finset.sum_le_sum fun α _ =>
    (Finset.sum_le_sum fun u' _ => Finset.sum_le_sum fun s _ => hterm m hm α u' s))).trans ?_
  have hsum : ∀ m : ℕ, ∑ α : DerivativeWord2 m, ∑ u' : ι, ∑ s : Fin i → Bool,
      (if u' = u then K else 0) = 2 ^ m * (2 ^ i * K) := by
    intro m
    simp [Finset.sum_ite_eq']
  simp only [hsum]
  rw [← Finset.sum_mul]
  exact mul_le_mul' (metric_sum_two_pow_le N) le_rfl

theorem metric_isBoxSmooth_liftApply {N sX sZ : ℕ} (c : LiftCoeff ι h) (b : Vec 2 → ∀ i, h i)
    (t : ℝ) (v : ι) (hc : ∀ m (α : DerivativeWord2 m) u,
      IsBoxSmooth sX sZ (fun X z => c m α t X z v u))
    (hb : ContDiff ℝ ((sX + N : ℕ) : ℕ∞) b) :
    IsBoxSmooth sX sZ (fun X z => liftApply N c (fun _ => b) t X z v) := by
  have hξ : ∀ m ∈ Finset.range (N + 1), ∀ (α : DerivativeWord2 m) (u : ι),
      ContDiff ℝ (sX : ℕ∞) (fun X' => orderedDerivative α b X' u) := fun m hm α u =>
    contDiff_orderedDerivative_comp (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) α hb u
  have hterm : ∀ m ∈ Finset.range (N + 1), ∀ (α : DerivativeWord2 m) (u : ι),
      IsBoxSmooth sX sZ (fun X z => c m α t X z v u (orderedDerivative α b X u)) :=
    fun m hm α u => (hc m α u).apply_slow (hξ m hm α u)
  have hα : ∀ m ∈ Finset.range (N + 1), ∀ (α : DerivativeWord2 m),
      IsBoxSmooth sX sZ (fun X z => ∑ u : ι, c m α t X z v u (orderedDerivative α b X u)) :=
    fun m hm α => IsBoxSmooth.sum _ fun u _ => hterm m hm α u
  have hm' : ∀ m ∈ Finset.range (N + 1),
      IsBoxSmooth sX sZ (fun X z => ∑ α : DerivativeWord2 m, ∑ u : ι,
        c m α t X z v u (orderedDerivative α b X u)) :=
    fun m hm => IsBoxSmooth.sum _ fun α _ => hα m hm α
  exact IsBoxSmooth.sum _ hm'

/-- The pointwise jet layer: `ptJet` of one component of a lift action on a field `b`
concentrated in the component `u`, in terms of the block jet of the coefficients. -/
theorem metric_ptJet_lift_le {N i q sX sZ : ℕ} (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (σ : ℝ)
    (v u : ι) (hi : i + 1 ≤ sX) (hq : q ≤ sZ)
    (hc : ∀ m (α : DerivativeWord2 m) u', IsBoxSmooth sX sZ (fun X z => Cc hh N m α σ X z v u'))
    (b : Vec 2 → ∀ i, h i) (hb : ContDiff ℝ ((sX + N : ℕ) : ℕ∞) b) {R : ℝ} (hR : 0 ≤ R)
    (X : Vec 2)
    (hbu : ∀ u' ≠ u, ∀ m (α : DerivativeWord2 m), m ≤ N → ∀ s2 : List (Fin 2), s2.length ≤ i →
      derivList s2 (fun X' => orderedDerivative α b X' u') X = 0)
    (hξ : ∀ m (α : DerivativeWord2 m), m ≤ N → ∀ s2 : List (Fin 2), s2.length ≤ i →
      ‖derivList s2 (fun X' => orderedDerivative α b X' u) X‖ ≤ R)
    (S F : ℕ) (hS : i ≤ S) (hF : q ≤ F) :
    ptJet (fun X z => liftApply N (Cc hh N) (fun _ => b) σ X z v) X i q ≤
      2 ^ (i + q) * (2 ^ (N + 1) * (2 ^ i * (ENNReal.ofReal R * blkJ Cc hh N σ v u S F))) := by
  have hΦ := metric_isBoxSmooth_liftApply (Cc hh N) b σ v hc hb
  refine (ptJet_le_two_pow_mul_iSup hΦ (by omega) hq X).trans (mul_le_mul' le_rfl ?_)
  refine iSup₂_le fun w β => ?_
  exact metric_word_le Cc hh σ v u hi hq hc b (hb.of_le (by exact_mod_cast (by omega :
    i + N ≤ sX + N))) hR X hbu hξ w β S F hS hF

end Word
end

/-! The metric parts `ℬ₁`, `ℬ₂` of the quiet source on the lift action of a centred monomial test
field `b = monoF X β • Pi.single u x`: the vector mixed jets at the slow point `X` are bounded by
the block jets of the lower level coefficients (`metric_cellB1_le`, `metric_cellB2_le`). -/

section
section Cross

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem metric_isBoxSmooth_pi {sX sZ : ℕ} {Φ : Vec 2 → Vec 2 → ∀ i, h i}
    (hΦ : ∀ i, IsBoxSmooth sX sZ (fun X z => Φ X z i)) : IsBoxSmooth sX sZ Φ := by
  have e : Φ = fun X z => ∑ i, ContinuousLinearMap.single ℝ h i (Φ X z i) := by
    funext X z
    ext w
    simp [Finset.sum_apply]
  rw [e]
  exact IsBoxSmooth.sum _ fun i _ => (hΦ i).clm_comp (ContinuousLinearMap.single ℝ h i)

theorem metric_two_le_cast {n : ℕ} (h : 2 ≤ n) : (2 : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) := by
  have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.2 (by exact_mod_cast h)
  simpa using h1

/-- The constant of the first cross operator. -/
def metricCA (p q N : ℕ) (Γ : ℝ) (k : ℕ) : ℝ :=
  12 * Γ * (((p + 2 : ℕ) : ℝ) * 2 ^ (3 * p + q + N + 4)) * (k.factorial : ℝ)

/-- The constant of the second cross operator. -/
def metricCB (p q N : ℕ) (Γ : ℝ) (k : ℕ) : ℝ :=
  8 * Γ * (((p + 3 : ℕ) : ℝ) * 2 ^ (3 * p + q + N + 5)) * (k.factorial : ℝ)

/-- `ptJet` of one component of the lift action on a centred monomial test field, in terms of the
block jet. -/
theorem metric_ptJet_mono_le {N i q sX sZ : ℕ} (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (σ : ℝ)
    (v u : ι) (hi : i + 1 ≤ sX) (hq : q ≤ sZ)
    (hc : ∀ m (α : DerivativeWord2 m) u', IsBoxSmooth sX sZ (fun X z => Cc hh N m α σ X z v u'))
    (X : Vec 2) (β : List (Fin 2)) (x : h u) (hx : ‖x‖ ≤ 1) (S F : ℕ) (hS : i ≤ S) (hF : q ≤ F) :
    ptJet (fun X' z => liftApply N (Cc hh N)
        (fun _ => fun Y => monoF X β Y • Pi.single u x) σ X' z v) X i q ≤
      2 ^ (i + q) * (2 ^ (N + 1) * (2 ^ i * (ENNReal.ofReal (β.length.factorial : ℝ) *
        blkJ Cc hh N σ v u S F))) := by
  have hf : ContDiff ℝ ((i + N : ℕ) : ℕ∞) (monoF X β) := contDiff_monoF X _ β
  obtain ⟨hbu, hξ⟩ := metric_smul_bounds hf (Pi.single u x : ∀ i, h i) u
    (fun u' hu' => Pi.single_eq_of_ne hu' x) X
    (fun L _ => derivList_monoF_abs_le X X (by simp) L β) (by simpa using hx)
  exact metric_ptJet_lift_le Cc hh σ v u hi hq hc _ ((contDiff_monoF X _ β).smul contDiff_const)
    (Nat.cast_nonneg _) X hbu hξ S F hS hF

theorem metric_ofReal_CA (p q N : ℕ) {Γ : ℝ} (hΓ : 0 ≤ Γ) (k : ℕ) :
    ENNReal.ofReal (metricCA p q N Γ k) = 12 * ENNReal.ofReal Γ *
      (((p + 2 : ℕ) : ℝ≥0∞) * 2 ^ (3 * p + q + N + 4)) * (k.factorial : ℝ≥0∞) := by
  unfold metricCA
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  simp

/-- The first cross operator on the lift action of a centred monomial test field, at exact orders:
the `v` component of `ℬ₁(liftApply N …)`. -/
theorem metric_cellB1_exact (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh N : ℕ)
    (σ : ℝ) {sX sZ : ℕ} (v u : ι) (l m : List (Fin 2)) (hsX : l.length + 2 ≤ sX)
    (hsZ : m.length + 1 ≤ sZ) (hη1 : Q.η ≤ 1) (hv : ∀ z, Real.sqrt Q.η • Q.v σ z = 0)
    (hGs : ∀ i j, ContDiff ℝ ((l.length + 1 : ℕ) : ℕ∞) (fun X => Q.G σ X i j)) {Γ : ℝ}
    (X : Vec 2)
    (hΓ : ∀ i j r, r ≤ l.length + 1 → ‖iteratedFDeriv ℝ r (fun X' => Q.G σ X' i j) X‖ ≤ Γ)
    (hc : ∀ w m (α : DerivativeWord2 m) u',
      IsBoxSmooth sX sZ (fun X z => Cc hh N m α σ X z w u'))
    (β : List (Fin 2)) (x : h u) (hx : ‖x‖ ≤ 1) (S F : ℕ) (hS : l.length + 1 ≤ S)
    (hF : m.length + 1 ≤ F) :
    vecJ (fun X' z => cellB1 Q.η Q.G Q.v σ (liftApply N (Cc hh N)
        (fun _ => fun Y => monoF X β Y • Pi.single u x) σ) X' z v) X l m ≤
      ENNReal.ofReal (metricCA l.length m.length N Γ β.length) * blkJ Cc hh N σ v u S F := by
  set p := l.length with hp
  set q := m.length with hq
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hΓ 0 0 0 (Nat.zero_le _))
  set b : Vec 2 → ∀ i, h i := fun Y => monoF X β Y • Pi.single u x with hb
  have hbd : ContDiff ℝ ((sX + N : ℕ) : ℕ∞) b := (contDiff_monoF X _ β).smul contDiff_const
  set Φ := liftApply N (Cc hh N) (fun _ => b) σ with hΦdef
  have hΦw : ∀ w, IsBoxSmooth sX sZ (fun X z => Φ X z w) := fun w =>
    metric_isBoxSmooth_liftApply (Cc hh N) b σ w (fun m α u' => hc w m α u') hbd
  have hΦ : IsBoxSmooth sX sZ Φ := metric_isBoxSmooth_pi hΦw
  have hΦ11 : IsBoxSmooth 1 1 Φ := hΦ.mono (by omega) (by omega)
  have hGd : ∀ i j, Differentiable ℝ (fun X => Q.G σ X i j) := fun i j =>
    (hGs i j).differentiable (by simp)
  have e : (fun X' z => cellB1 Q.η Q.G Q.v σ Φ X' z v) =
      cellB1 Q.η Q.G Q.v σ (fun X z => Φ X z v) :=
    (metric_cellB1_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) hΦ11 hGd).symm
  rw [e]
  have hΦv : IsBoxSmooth (p + 1) (q + 1) (fun X z => Φ X z v) :=
    (hΦw v).mono (by omega) (by omega)
  have hbox : IsBoxSmooth p q (cellB1 Q.η Q.G Q.v σ (fun X z => Φ X z v)) :=
    metric_isBoxSmooth_cellB1 hΦv hv hGs
  refine (metric_vecJ_le_ptJet l m hbox X).trans ?_
  refine (ptJet_cellB1_le hΦv hv hGs X hΓ).trans ?_
  set blk := blkJ Cc hh N σ v u S F with hblk
  set Rn : ℝ≥0∞ := ENNReal.ofReal (β.length.factorial : ℝ) with hRn
  set T : ℝ≥0∞ := 2 ^ (p + 1 + (q + 1)) * (2 ^ (N + 1) * (2 ^ (p + 1) * (Rn * blk))) with hT
  have hi : ∀ i ∈ Finset.range (p + 2), ptJet (fun X' z => Φ X' z v) X i (q + 1) ≤ T := by
    intro i hi
    have hip : i ≤ p + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    refine (metric_ptJet_mono_le Cc hh σ v u (by omega) (by omega) (hc v) X β x hx S F
      (by omega) (by omega)).trans ?_
    rw [hT]
    gcongr <;> norm_num
  have hsum : ∑ i ∈ Finset.range (p + 2), ptJet (fun X' z => Φ X' z v) X i (q + 1) ≤
      ((p + 2 : ℕ) : ℝ≥0∞) * T := by
    refine (Finset.sum_le_card_nsmul _ _ _ hi).trans ?_
    simp [nsmul_eq_mul]
  have hsq : ENNReal.ofReal (Real.sqrt Q.η) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_one.mpr hη1)
  calc (12 * 2 ^ p) * ENNReal.ofReal (Real.sqrt Q.η) * ENNReal.ofReal Γ *
        ∑ i ∈ Finset.range (p + 2), ptJet (fun X' z => Φ X' z v) X i (q + 1)
      ≤ (12 * 2 ^ p) * 1 * ENNReal.ofReal Γ * (((p + 2 : ℕ) : ℝ≥0∞) * T) :=
        mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hsq) le_rfl) hsum
    _ = ENNReal.ofReal (metricCA p q N Γ β.length) * blk := by
        rw [metric_ofReal_CA p q N hΓ0, hT, hRn, ENNReal.ofReal_natCast]
        ring

theorem metricCA_mono {p p' q q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') (N : ℕ) {Γ : ℝ} (hΓ : 0 ≤ Γ)
    (k : ℕ) : metricCA p q N Γ k ≤ metricCA p' q' N Γ k := by
  unfold metricCA
  have h1 : ((p + 2 : ℕ) : ℝ) ≤ ((p' + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : p + 2 ≤ p' + 2)
  have h2 : (2 : ℝ) ^ (3 * p + q + N + 4) ≤ 2 ^ (3 * p' + q' + N + 4) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  gcongr

/-- **(A)** The first cross operator on the lift action of a centred monomial test field. -/
theorem metric_cellB1_le (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh N : ℕ)
    (σ : ℝ) {sX sZ p q : ℕ} (v u : ι) (l m : List (Fin 2)) (hl : l.length ≤ p) (hm : m.length ≤ q)
    (hsX : p + 2 ≤ sX) (hsZ : q + 1 ≤ sZ) (hη1 : Q.η ≤ 1)
    (hv : ∀ z, Real.sqrt Q.η • Q.v σ z = 0)
    (hGs : ∀ i j, ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun X => Q.G σ X i j)) {Γ : ℝ}
    (X : Vec 2) (hΓ : ∀ i j r, r ≤ p + 1 → ‖iteratedFDeriv ℝ r (fun X' => Q.G σ X' i j) X‖ ≤ Γ)
    (hc : ∀ w m (α : DerivativeWord2 m) u',
      IsBoxSmooth sX sZ (fun X z => Cc hh N m α σ X z w u'))
    (β : List (Fin 2)) (x : h u) (hx : ‖x‖ ≤ 1) :
    vecJ (fun X' z => cellB1 Q.η Q.G Q.v σ (liftApply N (Cc hh N)
        (fun _ => fun Y => monoF X β Y • Pi.single u x) σ) X' z v) X l m ≤
      ENNReal.ofReal (metricCA p q N Γ β.length) * blkJ Cc hh N σ v u (p + 1) (q + 1) := by
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hΓ 0 0 0 (Nat.zero_le _))
  refine (metric_cellB1_exact Q Cc hh N σ v u l m (by omega) (by omega) hη1 hv
    (fun i j => (hGs i j).of_le (by exact_mod_cast (by omega : l.length + 1 ≤ p + 1))) X
    (fun i j r hr => hΓ i j r (by omega)) hc β x hx (p + 1) (q + 1) (by omega) (by omega)).trans ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (metricCA_mono hl hm N hΓ0 _)) le_rfl

theorem metric_ofReal_CB (p q N : ℕ) {Γ : ℝ} (hΓ : 0 ≤ Γ) (k : ℕ) :
    ENNReal.ofReal (metricCB p q N Γ k) = 8 * ENNReal.ofReal Γ *
      (((p + 3 : ℕ) : ℝ≥0∞) * 2 ^ (3 * p + q + N + 5)) * (k.factorial : ℝ≥0∞) := by
  unfold metricCB
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  simp

theorem metricCB_mono {p p' q q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') (N : ℕ) {Γ : ℝ} (hΓ : 0 ≤ Γ)
    (k : ℕ) : metricCB p q N Γ k ≤ metricCB p' q' N Γ k := by
  unfold metricCB
  have h1 : ((p + 3 : ℕ) : ℝ) ≤ ((p' + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : p + 3 ≤ p' + 3)
  have h2 : (2 : ℝ) ^ (3 * p + q + N + 5) ≤ 2 ^ (3 * p' + q' + N + 5) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  gcongr

/-- The second cross operator on the lift action of a centred monomial test field, at exact
orders. -/
theorem metric_cellB2_exact (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh N : ℕ)
    (σ : ℝ) {sX sZ : ℕ} (v u : ι) (l m : List (Fin 2)) (hsX : l.length + 3 ≤ sX)
    (hsZ : m.length ≤ sZ) (hη0 : 0 ≤ Q.η) (hη1 : Q.η ≤ 1)
    (hGs : ∀ i j, ContDiff ℝ ((l.length + 1 : ℕ) : ℕ∞) (fun X => Q.G σ X i j)) {Γ : ℝ}
    (X : Vec 2)
    (hΓ : ∀ i j r, r ≤ l.length + 1 → ‖iteratedFDeriv ℝ r (fun X' => Q.G σ X' i j) X‖ ≤ Γ)
    (hc : ∀ w m (α : DerivativeWord2 m) u',
      IsBoxSmooth sX sZ (fun X z => Cc hh N m α σ X z w u'))
    (β : List (Fin 2)) (x : h u) (hx : ‖x‖ ≤ 1) (S F : ℕ) (hS : l.length + 2 ≤ S)
    (hF : m.length ≤ F) :
    vecJ (fun X' z => cellB2 Q.η Q.G σ (liftApply N (Cc hh N)
        (fun _ => fun Y => monoF X β Y • Pi.single u x) σ) X' z v) X l m ≤
      ENNReal.ofReal (metricCB l.length m.length N Γ β.length) * blkJ Cc hh N σ v u S F := by
  set p := l.length with hp
  set q := m.length with hq
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hΓ 0 0 0 (Nat.zero_le _))
  set b : Vec 2 → ∀ i, h i := fun Y => monoF X β Y • Pi.single u x with hb
  have hbd : ContDiff ℝ ((sX + N : ℕ) : ℕ∞) b := (contDiff_monoF X _ β).smul contDiff_const
  set Φ := liftApply N (Cc hh N) (fun _ => b) σ with hΦdef
  have hΦw : ∀ w, IsBoxSmooth sX sZ (fun X z => Φ X z w) := fun w =>
    metric_isBoxSmooth_liftApply (Cc hh N) b σ w (fun m α u' => hc w m α u') hbd
  have hΦ : IsBoxSmooth sX sZ Φ := metric_isBoxSmooth_pi hΦw
  have hΦ2 : ∀ z, ContDiff ℝ 2 (fun X => Φ X z) := fun z =>
    (hΦ.contDiff_slow z).of_le (metric_two_le_cast (by omega))
  have hGd : ∀ i j, Differentiable ℝ (fun X => Q.G σ X i j) := fun i j =>
    (hGs i j).differentiable (by simp)
  have e : (fun X' z => cellB2 Q.η Q.G σ Φ X' z v) =
      cellB2 Q.η Q.G σ (fun X z => Φ X z v) :=
    (metric_cellB2_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) hΦ2 hGd).symm
  rw [e]
  have hΦv : IsBoxSmooth (p + 2) q (fun X z => Φ X z v) :=
    (hΦw v).mono (by omega) (by omega)
  have hbox : IsBoxSmooth p q (cellB2 Q.η Q.G σ (fun X z => Φ X z v)) :=
    metric_isBoxSmooth_cellB2 hΦv hGs
  refine (metric_vecJ_le_ptJet l m hbox X).trans ?_
  refine (ptJet_cellB2_le hΦv hGs X hΓ).trans ?_
  set blk := blkJ Cc hh N σ v u S F with hblk
  set Rn : ℝ≥0∞ := ENNReal.ofReal (β.length.factorial : ℝ) with hRn
  set T : ℝ≥0∞ := 2 ^ (p + 2 + q) * (2 ^ (N + 1) * (2 ^ (p + 2) * (Rn * blk))) with hT
  have hi : ∀ i ∈ Finset.range (p + 3), ptJet (fun X' z => Φ X' z v) X i q ≤ T := by
    intro i hi
    have hip : i ≤ p + 2 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    refine (metric_ptJet_mono_le Cc hh σ v u (by omega) (by omega) (hc v) X β x hx S F
      (by omega) (by omega)).trans ?_
    rw [hT]
    gcongr <;> norm_num
  have hsum : ∑ i ∈ Finset.range (p + 3), ptJet (fun X' z => Φ X' z v) X i q ≤
      ((p + 3 : ℕ) : ℝ≥0∞) * T := by
    refine (Finset.sum_le_card_nsmul _ _ _ hi).trans ?_
    simp [nsmul_eq_mul]
  have hη : ‖Q.η‖ₑ ≤ 1 := by
    rw [Real.enorm_eq_ofReal hη0, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hη1
  calc (8 * 2 ^ p) * ‖Q.η‖ₑ * ENNReal.ofReal Γ *
        ∑ i ∈ Finset.range (p + 3), ptJet (fun X' z => Φ X' z v) X i q
      ≤ (8 * 2 ^ p) * 1 * ENNReal.ofReal Γ * (((p + 3 : ℕ) : ℝ≥0∞) * T) :=
        mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hη) le_rfl) hsum
    _ = ENNReal.ofReal (metricCB p q N Γ β.length) * blk := by
        rw [metric_ofReal_CB p q N hΓ0, hT, hRn, ENNReal.ofReal_natCast]
        ring

/-- **(B)** The second cross operator on the lift action of a centred monomial test field. -/
theorem metric_cellB2_le (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh N : ℕ)
    (σ : ℝ) {sX sZ p q : ℕ} (v u : ι) (l m : List (Fin 2)) (hl : l.length ≤ p) (hm : m.length ≤ q)
    (hsX : p + 3 ≤ sX) (hsZ : q ≤ sZ) (hη0 : 0 ≤ Q.η) (hη1 : Q.η ≤ 1)
    (hGs : ∀ i j, ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun X => Q.G σ X i j)) {Γ : ℝ}
    (X : Vec 2) (hΓ : ∀ i j r, r ≤ p + 1 → ‖iteratedFDeriv ℝ r (fun X' => Q.G σ X' i j) X‖ ≤ Γ)
    (hc : ∀ w m (α : DerivativeWord2 m) u',
      IsBoxSmooth sX sZ (fun X z => Cc hh N m α σ X z w u'))
    (β : List (Fin 2)) (x : h u) (hx : ‖x‖ ≤ 1) :
    vecJ (fun X' z => cellB2 Q.η Q.G σ (liftApply N (Cc hh N)
        (fun _ => fun Y => monoF X β Y • Pi.single u x) σ) X' z v) X l m ≤
      ENNReal.ofReal (metricCB p q N Γ β.length) * blkJ Cc hh N σ v u (p + 2) q := by
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hΓ 0 0 0 (Nat.zero_le _))
  refine (metric_cellB2_exact Q Cc hh N σ v u l m (by omega) (by omega) hη0 hη1
    (fun i j => (hGs i j).of_le (by exact_mod_cast (by omega : l.length + 1 ≤ p + 1))) X
    (fun i j r hr => hΓ i j r (by omega)) hc β x hx (p + 2) q (by omega) hm).trans ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (metricCB_mono hl hm N hΓ0 _)) le_rfl

end Cross
end

/-! The `ℬ₂` mean term of the quiet source: the lift action of order `j` on the quiet mean operator
`quietMeanOp Q b 0 (n - j)` of the centred monomial test field `b = monoF X β • Pi.single u x`. The
quiet mean operator is `-η ∑ ∂_i(G_ij ∂_j monoF) • Pi.single u x` (for `n - j = 2`, else zero); its
derivatives at `X` are bounded through the pointwise jet calculus of `ℬ₂`, and the vector Leibniz
bound of the lift layer gives the block jet bound `metric_mean_le`. -/

section
section Mean

theorem metric_norm_iteratedFDeriv_monoF_le (X : Vec 2) (β : List (Fin 2)) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (monoF X β) X‖ ≤ 2 ^ i * (β.length.factorial : ℝ) := by
  have hg : ContDiff ℝ (i : ℕ∞) (monoF X β) := contDiff_monoF X _ β
  have h1 := norm_iteratedFDeriv_sq_le_words hg X
  have h2 : ∑ w : DerivativeWord2 i, ‖orderedDerivative w (monoF X β) X‖ ^ 2 ≤
      ∑ _w : DerivativeWord2 i, ((β.length.factorial : ℝ)) ^ 2 :=
    Finset.sum_le_sum fun w _ => pow_le_pow_left₀ (norm_nonneg _)
      (norm_orderedDerivative_monoF_le X X (by simp) w β) 2
  rw [Finset.sum_const, card_derivativeWord2, nsmul_eq_mul] at h2
  have h3 : ‖iteratedFDeriv ℝ i (monoF X β) X‖ ^ 2 ≤ (2 ^ i * (β.length.factorial : ℝ)) ^ 2 := by
    calc _ ≤ _ := h1
      _ ≤ 2 ^ i * (((2 ^ i : ℕ) : ℝ) * (β.length.factorial : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by push_cast; ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h3

/-- The slow-only field `-η ∑ ∂_i(G_ij ∂_j monoF)` is the value of `ℬ₂` at `z = 0`. -/
def metricF2 {D : ℕ} {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (Q : LiftOperatorData ι h D) (σ : ℝ) (X : Vec 2)
    (β : List (Fin 2)) : Vec 2 → ℝ :=
  fun X' => cellB2 Q.η Q.G σ (fun X'' _ => monoF X β X'') X' 0

theorem metric_ofReal_Rc (r : ℕ) {Γ : ℝ} (hΓ : 0 ≤ Γ) (k : ℕ) :
    ENNReal.ofReal (64 * 4 ^ r * Γ * (k.factorial : ℝ)) =
      8 * 2 ^ r * ENNReal.ofReal Γ * 2 ^ (r + 3) * (k.factorial : ℝ≥0∞) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast]
  have h4 : (4 : ℝ≥0∞) ^ r = 2 ^ r * 2 ^ r := by rw [← mul_pow]; norm_num
  simp only [ENNReal.ofReal_ofNat, h4]
  ring

/-- The derivatives of the slow field `f₂ = -η ∑ ∂_i(G_ij ∂_j monoF)` at `X`. -/
theorem metric_f2_norm_le {D : ℕ} {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (Q : LiftOperatorData ι h D) (σ : ℝ) (hη0 : 0 ≤ Q.η)
    (hη1 : Q.η ≤ 1) {r : ℕ}
    (hGs : ∀ i j, ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun X => Q.G σ X i j)) {Γ : ℝ} (X : Vec 2)
    (hΓ : ∀ i j l, l ≤ r + 1 → ‖iteratedFDeriv ℝ l (fun X' => Q.G σ X' i j) X‖ ≤ Γ)
    (β : List (Fin 2)) :
    ‖iteratedFDeriv ℝ r (metricF2 Q σ X β) X‖ ≤ 64 * 4 ^ r * Γ * (β.length.factorial : ℝ) := by
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hΓ 0 0 0 (Nat.zero_le _))
  have hΦ : IsBoxSmooth (r + 2) 0 (fun X'' (_ : Vec 2) => monoF X β X'') :=
    metric_isBoxSmooth_slowOnly (contDiff_monoF X _ β)
  have h1 := ptJet_cellB2_le (η := Q.η) (G := Q.G) (t := σ) hΦ hGs X hΓ
  have e : (fun X' (_ : Vec 2) => metricF2 Q σ X β X') = cellB2 Q.η Q.G σ (fun X'' _ => monoF X β X'') := by
    funext X' z; rfl
  rw [← e, metric_ptJet_slowOnly] at h1
  simp only [metric_ptJet_slowOnly] at h1
  have hη : ‖Q.η‖ₑ ≤ 1 := by
    rw [Real.enorm_eq_ofReal hη0, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hη1
  have h2 : ∑ i ∈ Finset.range (r + 3), ‖iteratedFDeriv ℝ i (monoF X β) X‖ₑ ≤
      2 ^ (r + 3) * (β.length.factorial : ℝ≥0∞) := by
    calc _ ≤ ∑ i ∈ Finset.range (r + 3), 2 ^ i * (β.length.factorial : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := ENNReal.ofReal_le_ofReal (metric_norm_iteratedFDeriv_monoF_le X β i)
          rw [ofReal_norm] at this
          refine this.trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
            ENNReal.ofReal_natCast]
          simp
      _ = (∑ i ∈ Finset.range (r + 3), (2 : ℝ≥0∞) ^ i) * (β.length.factorial : ℝ≥0∞) := by
          rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul' (metric_sum_two_pow_le (r + 2)) le_rfl
  have h3 : ‖iteratedFDeriv ℝ r (metricF2 Q σ X β) X‖ₑ ≤
      ENNReal.ofReal (64 * 4 ^ r * Γ * (β.length.factorial : ℝ)) := by
    rw [metric_ofReal_Rc r hΓ0]
    refine h1.trans ?_
    calc (8 * 2 ^ r) * ‖Q.η‖ₑ * ENNReal.ofReal Γ * ∑ i ∈ Finset.range (r + 3),
          ‖iteratedFDeriv ℝ i (monoF X β) X‖ₑ
        ≤ (8 * 2 ^ r) * 1 * ENNReal.ofReal Γ * (2 ^ (r + 3) * (β.length.factorial : ℝ≥0∞)) :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hη) le_rfl) h2
      _ = _ := by ring
  rw [← ofReal_norm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

theorem metric_liftApply_congr {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {n : ℕ} {c : LiftCoeff ι h}
    {a a' : ℝ → Vec 2 → ∀ i, h i} {t : ℝ} (hh : a t = a' t) :
    liftApply n c a t = liftApply n c a' t := by
  unfold liftApply
  rw [hh]

/-- The constant of the mean term. -/
def metricCC (p j : ℕ) (Γ : ℝ) (k : ℕ) : ℝ :=
  2 ^ (j + 1) * 2 ^ p * (64 * 4 ^ (p + j) * Γ * (k.factorial : ℝ))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The quiet mean operator of the monomial test field is `f₂ • Pi.single u x` (or zero). -/
theorem metric_quietMeanOp_mono (Q : LiftOperatorData ι h D) (σ : ℝ) (X : Vec 2)
    (β : List (Fin 2)) (u : ι) (x : h u) (n' : ℕ)
    (hGd : ∀ i j, Differentiable ℝ (fun X => Q.G σ X i j)) (X' : Vec 2) :
    quietMeanOp Q (fun Y => monoF X β Y • Pi.single u x) 0 n' σ X' =
      (if n' = 2 then metricF2 Q σ X β X' else 0) • (Pi.single u x : ∀ i, h i) := by
  by_cases h2 : n' = 2
  · simp only [quietMeanOp, h2, ↓reduceIte]
    have := congrFun (congrFun (metric_cellB2_clm
      (ContinuousLinearMap.toSpanSingleton ℝ (Pi.single u x : ∀ i, h i)) (η := Q.η) (G := Q.G)
      (t := σ) (Φ := fun X'' (_ : Vec 2) => monoF X β X'') (fun z => contDiff_monoF X _ β)
      hGd) X') 0
    exact this
  · simp [quietMeanOp, h2]

/-- **(C)** The `ℬ₂` mean term of the quiet source: the lift action of order `j` on the quiet mean
operator of the monomial test field (nonzero only for `n - j = 2`). -/
theorem metric_mean_le (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh j n : ℕ)
    (σ : ℝ) {sX sZ p q : ℕ} (v u : ι) (l m : List (Fin 2)) (hl : l.length ≤ p) (hm : m.length ≤ q)
    (hsX : p + 1 ≤ sX) (hsZ : q ≤ sZ) (hη0 : 0 ≤ Q.η) (hη1 : Q.η ≤ 1)
    (hGs : ∀ i k, ContDiff ℝ ((p + j + 1 : ℕ) : ℕ∞) (fun X => Q.G σ X i k)) {Γ : ℝ}
    (X : Vec 2)
    (hΓ : ∀ i k r, r ≤ p + j + 1 → ‖iteratedFDeriv ℝ r (fun X' => Q.G σ X' i k) X‖ ≤ Γ)
    (hc : ∀ m (α : DerivativeWord2 m) u',
      IsBoxSmooth sX sZ (fun X z => Cc hh j m α σ X z v u'))
    (β : List (Fin 2)) (x : h u) (hx : ‖x‖ ≤ 1) :
    vecJ (fun X' z => liftApply j (Cc hh j) (fun s X' => quietMeanOp Q
        (fun Y => monoF X β Y • Pi.single u x) 0 (n - j) s X') σ X' z v) X l m ≤
      ENNReal.ofReal (metricCC p j Γ β.length) * blkJ Cc hh j σ v u p q := by
  classical
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hΓ 0 0 0 (Nat.zero_le _))
  set w0 : ∀ i, h i := Pi.single u x with hw0
  set fq : Vec 2 → ℝ := fun X' => if n - j = 2 then metricF2 Q σ X β X' else 0 with hfq
  set Rc : ℝ := 64 * 4 ^ (p + j) * Γ * (β.length.factorial : ℝ) with hRc
  have hRc0 : 0 ≤ Rc := by positivity
  have hGd : ∀ i k, Differentiable ℝ (fun X => Q.G σ X i k) := fun i k =>
    (hGs i k).differentiable (by simp)
  have hqm : ∀ X', quietMeanOp Q (fun Y => monoF X β Y • Pi.single u x) 0 (n - j) σ X' =
      fq X' • w0 := fun X' => metric_quietMeanOp_mono Q σ X β u x (n - j) hGd X'
  -- smoothness of the scalar field
  have hfqd : ContDiff ℝ ((p + j : ℕ) : ℕ∞) fq := by
    by_cases h2 : n - j = 2
    · simp only [hfq, h2, ↓reduceIte]
      have hΦ : IsBoxSmooth (p + j + 2) 0 (fun X'' (_ : Vec 2) => monoF X β X'') :=
        metric_isBoxSmooth_slowOnly (contDiff_monoF X _ β)
      have := (metric_isBoxSmooth_cellB2 (η := Q.η) (G := Q.G) (t := σ) hΦ hGs).contDiff_slow 0
      exact this
    · simp only [hfq, h2, ↓reduceIte]
      exact contDiff_const
  -- derivative bound of the scalar field
  have hB : ∀ L : List (Fin 2), L.length ≤ l.length + j → |derivList L fq X| ≤ Rc := by
    intro L hL
    by_cases h2 : n - j = 2
    · have hfd : ContDiff ℝ (L.length : ℕ∞) fq := hfqd.of_le (by exact_mod_cast (by omega :
        L.length ≤ p + j))
      have h1 : |derivList L fq X| ≤ ‖iteratedFDeriv ℝ L.length fq X‖ := by
        rw [metric_derivList_eq_orderedDerivative, ← Real.norm_eq_abs]
        exact norm_orderedDerivative_le hfd L.get X
      refine h1.trans ?_
      have h3 : fq = metricF2 Q σ X β := by funext X'; simp [hfq, h2]
      rw [h3]
      refine (metric_f2_norm_le Q σ hη0 hη1 (r := L.length)
        (fun i k => (hGs i k).of_le (by exact_mod_cast (by omega : L.length + 1 ≤ p + j + 1))) X
        (fun i k r hr => hΓ i k r (by omega)) β).trans ?_
      rw [hRc]
      have : (4 : ℝ) ^ L.length ≤ 4 ^ (p + j) := pow_le_pow_right₀ (by norm_num) (by omega)
      gcongr
    · have h3 : fq = fun _ => 0 := by funext X'; simp [hfq, h2]
      rw [h3, metric_derivList_zero]
      simpa using hRc0
  obtain ⟨hbu, hξ⟩ := metric_smul_bounds (N := j) (i := l.length) (f := fq)
    (hfqd.of_le (by exact_mod_cast (by omega : l.length + j ≤ p + j))) w0 u
    (fun u' hu' => Pi.single_eq_of_ne hu' x) X hB (by simpa [hw0] using hx)
  -- the field and its box smoothness
  set b₂ : Vec 2 → ∀ i, h i := fun Y => fq Y • w0 with hb₂
  have hb₂d : ContDiff ℝ ((p + j : ℕ) : ℕ∞) b₂ := hfqd.smul contDiff_const
  have hΨ : IsBoxSmooth l.length m.length (fun X' z => liftApply j (Cc hh j) (fun _ => b₂) σ X' z v) :=
    (metric_isBoxSmooth_liftApply (sX := p) (sZ := sZ) (Cc hh j) b₂ σ v
      (fun m α u' => (hc m α u').mono (by omega) le_rfl) hb₂d).mono hl (by omega)
  have hq' : (fun s X' => quietMeanOp Q (fun Y => monoF X β Y • Pi.single u x) 0 (n - j) s X') σ
      = b₂ := funext hqm
  have e : (fun X' z => liftApply j (Cc hh j) (fun s X' => quietMeanOp Q
        (fun Y => monoF X β Y • Pi.single u x) 0 (n - j) s X') σ X' z v) =
      fun X' z => liftApply j (Cc hh j) (fun _ => b₂) σ X' z v := by
    funext X' z
    rw [metric_liftApply_congr (a' := fun _ => b₂) hq']
  rw [e, metric_vecJ_eq l m hΨ X]
  have e2 : (fun z => derivList l (fun X' => derivList m
      (liftApply j (Cc hh j) (fun _ => b₂) σ X' · v) z) X) = fun z => orderedDerivative
      (m := l.length) l.get (fun X' => orderedDerivative (m := m.length) m.get
        (fun z' => liftApply j (Cc hh j) (fun _ => b₂) σ X' z' v) z) X := by
    funext z
    rw [metric_derivList_eq_orderedDerivative]
    congr 1
    funext X'
    rw [metric_derivList_eq_orderedDerivative]
  rw [e2]
  refine (metric_word_le (N := j) (i := l.length) (q := m.length) Cc hh σ v u (by omega)
    (by omega) (fun m α u' => hc m α u') b₂
    (hb₂d.of_le (by exact_mod_cast (by omega : l.length + j ≤ p + j))) hRc0 X hbu hξ l.get m.get p q
    hl hm).trans ?_
  have hC : ENNReal.ofReal (metricCC p j Γ β.length) =
      2 ^ (j + 1) * 2 ^ p * ENNReal.ofReal Rc := by
    unfold metricCC
    rw [← hRc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_pow (by norm_num)]
    simp
  rw [hC]
  calc 2 ^ (j + 1) * (2 ^ l.length * (ENNReal.ofReal Rc * blkJ Cc hh j σ v u p q))
      ≤ 2 ^ (j + 1) * (2 ^ p * (ENNReal.ofReal Rc * blkJ Cc hh j σ v u p q)) := by
        gcongr
        norm_num
    _ = _ := by ring

end Mean
end

end AVRegularity.QuietDecay
end
