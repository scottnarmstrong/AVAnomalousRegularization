-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open ContinuousLinearMap
namespace AVRegularity.CycleWords.Discard

/-! # a dual criterion for membership in a Hilbert subspace

If `ι : V → H` is a bounded map of real Hilbert spaces and `X ∈ H` satisfies
`⟨X, g⟩ ≤ M N` whenever `⟨ι w, g⟩ ≤ N ‖w‖` for all `w`, then `X = ι x` with `‖x‖ ≤ M`.
Proof: the functional `ι† g ↦ ⟨X, g⟩` is well defined and `M`-bounded on the range of the adjoint;
extend it (Hahn-Banach), represent it (Riesz). -/

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Dual criterion.** -/
theorem mem_of_dual_bound (ι : V →L[ℝ] H) (X : H) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ (g : H) (N : ℝ), 0 ≤ N → (∀ w : V, inner ℝ (ι w) g ≤ N * ‖w‖) →
      inner ℝ X g ≤ M * N) :
    ∃ x : V, ι x = X ∧ ‖x‖ ≤ M := by
  set A : H →L[ℝ] V := ContinuousLinearMap.adjoint ι with hA
  have hAi : ∀ (g : H) (w : V), inner ℝ (ι w) g = inner ℝ w (A g) := fun g w => by
    rw [hA, ContinuousLinearMap.adjoint_inner_right]
  -- the bound for the functional on the range of `A`
  have hbd : ∀ g : H, inner ℝ X g ≤ M * ‖A g‖ := fun g => by
    refine h g ‖A g‖ (norm_nonneg _) fun w => ?_
    rw [hAi]
    exact (real_inner_le_norm _ _).trans (by rw [mul_comm])
  have hbd' : ∀ g : H, |inner ℝ X g| ≤ M * ‖A g‖ := fun g => by
    rw [abs_le]
    refine ⟨?_, hbd g⟩
    have := hbd (-g)
    rw [inner_neg_right, map_neg, norm_neg] at this
    linarith
  have hker : LinearMap.ker (A : H →ₗ[ℝ] V) ≤ LinearMap.ker (innerSL ℝ X : H →ₗ[ℝ] ℝ) := by
    intro g hg
    have h0 : A g = 0 := hg
    have := hbd' g
    rw [h0, norm_zero, mul_zero] at this
    simpa using abs_nonpos_iff.mp this
  let φ : LinearMap.range (A : H →ₗ[ℝ] V) →ₗ[ℝ] ℝ :=
    ((LinearMap.ker (A : H →ₗ[ℝ] V)).liftQ (innerSL ℝ X : H →ₗ[ℝ] ℝ) hker).comp
      (LinearMap.quotKerEquivRange (A : H →ₗ[ℝ] V)).symm.toLinearMap
  have hφ : ∀ g : H, φ ⟨A g, ⟨g, rfl⟩⟩ = inner ℝ X g := fun g => by
    have : (LinearMap.quotKerEquivRange (A : H →ₗ[ℝ] V)).symm ⟨A g, ⟨g, rfl⟩⟩ =
        Submodule.Quotient.mk g := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
    rfl
  have hφb : ∀ r : LinearMap.range (A : H →ₗ[ℝ] V), ‖φ r‖ ≤ M * ‖r‖ := fun r => by
    obtain ⟨g, hg⟩ := r.2
    have hr : r = ⟨A g, ⟨g, rfl⟩⟩ := Subtype.ext hg.symm
    rw [hr, hφ, Real.norm_eq_abs]
    exact hbd' g
  let φc : LinearMap.range (A : H →ₗ[ℝ] V) →L[ℝ] ℝ := φ.mkContinuous M hφb
  obtain ⟨Φ, hΦ, hΦn⟩ := exists_extension_norm_eq (LinearMap.range (A : H →ₗ[ℝ] V)) φc
  have hΦM : ‖Φ‖ ≤ M := by
    rw [hΦn]
    exact LinearMap.mkContinuous_norm_le _ hM _
  refine ⟨(InnerProductSpace.toDual ℝ V).symm Φ, ?_, ?_⟩
  · refine ext_inner_right ℝ fun g => ?_
    rw [hAi, InnerProductSpace.toDual_symm_apply, hΦ ⟨A g, ⟨g, rfl⟩⟩]
    exact hφ g
  · rw [LinearIsometryEquiv.norm_map]
    exact hΦM

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords.Discard

/-! # counting separated marks, and the geometric kernel

For a finite set `M` of mark starting times, separated by `θs`, the number of complete marks in
`[r, s]` is `Count M θs r s`, and the kernel `(1/2)^count` has the kernel axioms of
`IsFibreKernel` that do not involve the equation. -/

/-- The number of marks of `M` of length `θs` contained in `[r, s]`. -/
noncomputable def Count (M : Finset ℝ) (θs r s : ℝ) : ℕ :=
  (M.filter (fun m => r ≤ m ∧ m + θs ≤ s)).card

/-- The geometric kernel. -/
noncomputable def geometricMarkKernel (M : Finset ℝ) (θs r s : ℝ) : ℝ := (1 / 2 : ℝ) ^ Count M θs r s

/-- The constant `N` of the shrink loss. -/
noncomputable def shrinkLossConst (θs : ℝ) : ℕ := ⌊1 / θs⌋₊ + 1

theorem count_self (M : Finset ℝ) {θs : ℝ} (hθ : 0 < θs) (r : ℝ) :
    Count M θs r r = 0 := by
  unfold Count
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m _ h
  linarith [h.1, h.2]

theorem count_mono (M : Finset ℝ) (θs : ℝ) {r r' s s' : ℝ} (h1 : r' ≤ r) (h2 : s ≤ s') :
    Count M θs r s ≤ Count M θs r' s' := by
  unfold Count
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, by linarith [hm.2.1], by linarith [hm.2.2]⟩

/-- A separated set of starting times in a window of length `ℓ` has at most `⌊ℓ/θs⌋ + 1`
elements. -/
theorem card_window (T : Finset ℝ) {θs : ℝ} (hθ : 0 < θs)
    (hsep : ∀ m ∈ T, ∀ m' ∈ T, m ≠ m' → m + θs ≤ m' ∨ m' + θs ≤ m) {x ℓ : ℝ}
    (hT : ∀ m ∈ T, x ≤ m ∧ m ≤ x + ℓ) : T.card ≤ ⌊ℓ / θs⌋₊ + 1 := by
  have hmap : ∀ m ∈ T, ⌊(m - x) / θs⌋₊ ∈ Finset.range (⌊ℓ / θs⌋₊ + 1) := by
    intro m hm
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.floor_le_floor
    exact div_le_div_of_nonneg_right (by linarith [(hT m hm).2]) hθ.le
  have := Finset.card_le_card_of_injOn (fun m => ⌊(m - x) / θs⌋₊) hmap (by
    intro m hm m' hm' he
    by_contra hne
    have key : ∀ p ∈ T, ∀ q ∈ T, p + θs ≤ q → ⌊(p - x) / θs⌋₊ < ⌊(q - x) / θs⌋₊ := by
      intro p hp q hq hpq
      have h0 : 0 ≤ (p - x) / θs := div_nonneg (by linarith [(hT p hp).1]) hθ.le
      have : (p - x) / θs + 1 ≤ (q - x) / θs := by
        have h1 : 1 ≤ (q - p) / θs := by rw [le_div_iff₀ hθ]; linarith
        have e : (q - x) / θs = (p - x) / θs + (q - p) / θs := by ring
        rw [e]; linarith
      calc ⌊(p - x) / θs⌋₊ < ⌊(p - x) / θs⌋₊ + 1 := Nat.lt_succ_self _
        _ = ⌊(p - x) / θs + 1⌋₊ := (Nat.floor_add_one h0).symm
        _ ≤ _ := Nat.floor_le_floor this
    rcases hsep m hm m' hm' hne with h | h
    · exact (key m hm m' hm' h).ne he
    · exact (key m' hm' m hm h).ne he.symm)
  simpa using this


/-- At most one mark contains a given time in its interior. -/
theorem count_le_add (M : Finset ℝ) {θs : ℝ}
    (hsep : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → m + θs ≤ m' ∨ m' + θs ≤ m) {r s t : ℝ} :
    Count M θs r t ≤ Count M θs r s + Count M θs s t + 1 := by
  set Str : Finset ℝ := M.filter (fun m => m < s ∧ s < m + θs) with hStr
  have hS : Str.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [hStr, Finset.mem_filter] at ha hb
    by_contra hne
    rcases hsep a ha.1 b hb.1 hne with h | h <;> linarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2]
  have hsub : M.filter (fun m => r ≤ m ∧ m + θs ≤ t) ⊆
      (M.filter (fun m => r ≤ m ∧ m + θs ≤ s) ∪ M.filter (fun m => s ≤ m ∧ m + θs ≤ t)) ∪
        Str := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_union, hStr] at hm ⊢
    by_cases h1 : m + θs ≤ s
    · exact Or.inl (Or.inl ⟨hm.1, hm.2.1, h1⟩)
    · by_cases h2 : s ≤ m
      · exact Or.inl (Or.inr ⟨hm.1, h2, hm.2.2⟩)
      · exact Or.inr ⟨hm.1, by linarith, by linarith⟩
  unfold Count
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (M.filter (fun m => r ≤ m ∧ m + θs ≤ s) ∪ M.filter (fun m => s ≤ m ∧ m + θs ≤ t)).card
        + Str.card := Finset.card_union_le _ _
    _ ≤ _ := by
      have := Finset.card_union_le (M.filter (fun m => r ≤ m ∧ m + θs ≤ s))
        (M.filter (fun m => s ≤ m ∧ m + θs ≤ t))
      omega

theorem count_shrink (M : Finset ℝ) {θs : ℝ} (hθ : 0 < θs)
    (hsep : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → m + θs ≤ m' ∨ m' + θs ≤ m) {r r' t' t : ℝ}
    (h2 : r' ≤ r + 1) (h5 : t ≤ t' + 1) :
    Count M θs r t ≤ Count M θs r' t' + 2 * shrinkLossConst θs := by
  set B1 : Finset ℝ := M.filter (fun m => r ≤ m ∧ m ≤ r + 1) with hB1
  set B2 : Finset ℝ := M.filter (fun m => t' - θs ≤ m ∧ m ≤ t - θs) with hB2
  have hsep' : ∀ (P : ℝ → Prop) [DecidablePred P], ∀ m ∈ M.filter P, ∀ m' ∈ M.filter P,
      m ≠ m' → m + θs ≤ m' ∨ m' + θs ≤ m := fun P _ m hm m' hm' =>
    hsep m (Finset.mem_filter.mp hm).1 m' (Finset.mem_filter.mp hm').1
  have c1 : B1.card ≤ shrinkLossConst θs := by
    unfold shrinkLossConst
    exact card_window B1 hθ (hsep' _) (x := r) (ℓ := 1) (fun m hm => by
      have := (Finset.mem_filter.mp hm).2
      exact ⟨this.1, by linarith [this.2]⟩)
  have c2 : B2.card ≤ shrinkLossConst θs := by
    unfold shrinkLossConst
    exact card_window B2 hθ (hsep' _) (x := t' - θs) (ℓ := 1) (fun m hm => by
      have := (Finset.mem_filter.mp hm).2
      exact ⟨this.1, by linarith [this.2]⟩)
  have hsub : M.filter (fun m => r ≤ m ∧ m + θs ≤ t) ⊆
      (M.filter (fun m => r' ≤ m ∧ m + θs ≤ t') ∪ B1) ∪ B2 := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_union, hB1, hB2] at hm ⊢
    by_cases a1 : r' ≤ m
    · by_cases a2 : m + θs ≤ t'
      · exact Or.inl (Or.inl ⟨hm.1, a1, a2⟩)
      · exact Or.inr ⟨hm.1, by linarith, by linarith [hm.2.2]⟩
    · exact Or.inl (Or.inr ⟨hm.1, hm.2.1, by linarith⟩)
  unfold Count
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (M.filter (fun m => r' ≤ m ∧ m + θs ≤ t') ∪ B1).card + B2.card :=
        Finset.card_union_le _ _
    _ ≤ _ := by
      have := Finset.card_union_le (M.filter (fun m => r' ≤ m ∧ m + θs ≤ t')) B1
      omega

theorem Ker_pos (M : Finset ℝ) (θs r s : ℝ) : 0 < geometricMarkKernel M θs r s := by
  unfold geometricMarkKernel; positivity

theorem Ker_le_one (M : Finset ℝ) (θs r s : ℝ) : geometricMarkKernel M θs r s ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem Ker_self (M : Finset ℝ) {θs : ℝ} (hθ : 0 < θs) (r : ℝ) : geometricMarkKernel M θs r r = 1 := by
  unfold geometricMarkKernel; rw [count_self M hθ]; simp

theorem Ker_anti (M : Finset ℝ) (θs : ℝ) {r s t : ℝ} (hst : s ≤ t) :
    geometricMarkKernel M θs r t ≤ geometricMarkKernel M θs r s := by
  unfold geometricMarkKernel
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (count_mono M θs le_rfl hst)

theorem Ker_mul_le (M : Finset ℝ) {θs : ℝ}
    (hsep : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → m + θs ≤ m' ∨ m' + θs ≤ m) {r s t : ℝ} :
    geometricMarkKernel M θs r s * geometricMarkKernel M θs s t ≤ 2 * geometricMarkKernel M θs r t := by
  unfold geometricMarkKernel
  have h := count_le_add M hsep (r := r) (s := s) (t := t)
  rw [← pow_add]
  have h2 : (1 / 2 : ℝ) ^ (Count M θs r t) ≥ (1 / 2 : ℝ) ^ (Count M θs r s +
      Count M θs s t + 1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  rw [pow_succ] at h2
  linarith

theorem Ker_shrink (M : Finset ℝ) {θs : ℝ} (hθ : 0 < θs)
    (hsep : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → m + θs ≤ m' ∨ m' + θs ≤ m) {r r' t' t : ℝ}
    (h2 : r' ≤ r + 1) (h5 : t ≤ t' + 1) :
    geometricMarkKernel M θs r' t' ≤ 2 ^ (2 * shrinkLossConst θs) * geometricMarkKernel M θs r t := by
  unfold geometricMarkKernel
  have h := count_shrink M hθ hsep h2 h5
  have h2 : (1 / 2 : ℝ) ^ (Count M θs r t) ≥ (1 / 2 : ℝ) ^ (Count M θs r' t' +
      2 * shrinkLossConst θs) := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  rw [pow_add] at h2
  have e : (2 : ℝ) ^ (2 * shrinkLossConst θs) * (1 / 2 : ℝ) ^ (2 * shrinkLossConst θs) = 1 := by
    rw [← mul_pow]; norm_num
  have hp : 0 < (1 / 2 : ℝ) ^ (Count M θs r' t') := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 ^ (2 * shrinkLossConst θs))]

/-- **Decay of the norm along the marks**, for any nonnegative function `n` of time that does not
increase on `[r₀, s₀]` and halves across every mark of `M` inside `[r₀, s₀]`. -/
theorem decay_marks (M : Finset ℝ) {θs : ℝ} (hθ : 0 < θs)
    (hsep : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → m + θs ≤ m' ∨ m' + θs ≤ m) {r₀ s₀ : ℝ}
    (n : ℝ → ℝ)
    (hmono : ∀ s t, r₀ ≤ s → s ≤ t → t ≤ s₀ → n t ≤ n s)
    (hmark : ∀ m ∈ M, r₀ ≤ m → m + θs ≤ s₀ → n (m + θs) ≤ 1 / 2 * n m)
    {r s : ℝ} (hr : r₀ ≤ r) (hrs : r ≤ s) (hs : s ≤ s₀) :
    n s ≤ geometricMarkKernel M θs r s * n r := by
  unfold geometricMarkKernel Count
  have key : ∀ F : Finset ℝ, F ⊆ M → ∀ s : ℝ, r ≤ s → s ≤ s₀ →
      (∀ m ∈ F, r ≤ m ∧ m + θs ≤ s) → n s ≤ (1 / 2 : ℝ) ^ F.card * n r := by
    intro F
    induction F using Finset.induction_on_max with
    | empty =>
      intro _ s hrs hs _
      simpa using hmono r s hr hrs hs
    | insert a F ha ih =>
      intro hFM s hrs hs hall
      have haM : a ∈ M := hFM (Finset.mem_insert_self _ _)
      have hFM' : F ⊆ M := fun x hx => hFM (Finset.mem_insert_of_mem hx)
      have haF : a ∉ F := fun h => lt_irrefl _ (ha a h)
      have ha1 := hall a (Finset.mem_insert_self _ _)
      have hF : ∀ m ∈ F, r ≤ m ∧ m + θs ≤ a := by
        intro m hm
        refine ⟨(hall m (Finset.mem_insert_of_mem hm)).1, ?_⟩
        rcases hsep m (hFM' hm) a haM (ha m hm).ne with h | h
        · exact h
        · linarith [ha m hm]
      have ih' := ih hFM' a ha1.1 (by linarith [ha1.2]) hF
      have hm1 := hmark a haM (by linarith [ha1.1]) (by linarith [ha1.2])
      have hm2 := hmono (a + θs) s (by linarith [ha1.1]) ha1.2 hs
      rw [Finset.card_insert_of_notMem haF, pow_succ]
      calc n s ≤ n (a + θs) := hm2
        _ ≤ 1 / 2 * n a := hm1
        _ ≤ 1 / 2 * ((1 / 2 : ℝ) ^ F.card * n r) := by linarith
        _ = _ := by ring
  exact key _ (Finset.filter_subset _ _) s hrs hs (fun m hm => (Finset.mem_filter.mp hm).2)

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.CycleWords.Discard

/-! # from the forced Duhamel equation to the coupled one

If `c_i(t) = e(t₁,t) c_i(t₁) + ∫ e(r,t) f_i(r) dr` with integrable forcings `f_i` and, for almost
every `r`, `f_i(r) = ∑_{i'} τ_{i,i'}(r) c_{i'}(r)`, then the integrands with `τ` are interval
integrable and the Duhamel equation holds with `τ`. -/

theorem quietDuhamel_glue {I : Type*} {t₁ t₂ : ℝ} (hlt : t₁ ≤ t₂) (lam : ℝ → ℂ)
    (hlam : IntervalIntegrable lam volume t₁ t₂) (c f : I → ℝ → ℂ) (τ : I → I → ℝ → ℂ)
    [Fintype I]
    (hf : ∀ i, IntervalIntegrable (f i) volume t₁ t₂)
    (hD0 : ∀ i, ∀ t ∈ Icc t₁ t₂, c i t = Complex.exp (∫ r in t₁..t, lam r) * c i t₁ +
      ∫ r in t₁..t, Complex.exp (∫ s in r..t, lam s) * f i r)
    (hae : ∀ᵐ r ∂volume, r ∈ Icc t₁ t₂ → ∀ i, f i r = ∑ i', τ i i' r * c i' r) :
    (∀ t ∈ Icc t₁ t₂, ∀ i, IntervalIntegrable (fun r =>
      Complex.exp (∫ s in r..t, lam s) * ∑ i', τ i i' r * c i' r) volume t₁ t) ∧
    ∀ i, ∀ t ∈ Icc t₁ t₂, c i t = Complex.exp (∫ r in t₁..t, lam r) * c i t₁ +
      ∫ r in t₁..t, Complex.exp (∫ s in r..t, lam s) * ∑ i', τ i i' r * c i' r := by
  have hprim : ContinuousOn (fun x => ∫ s in t₁..x, lam s) (uIcc t₁ t₂) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le hlt]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hlt).1 hlam)
  have hsub : ∀ t ∈ Icc t₁ t₂, ∀ r ∈ Icc t₁ t,
      ∫ s in r..t, lam s = (∫ s in t₁..t, lam s) - ∫ s in t₁..r, lam s := by
    intro t ht r hr
    have h1 : IntervalIntegrable lam volume t₁ t := hlam.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hlt]; exact Icc_subset_Icc le_rfl ht.2)
    have h2 : IntervalIntegrable lam volume t₁ r := hlam.mono_set (by
      rw [uIcc_of_le hr.1, uIcc_of_le hlt]; exact Icc_subset_Icc le_rfl (hr.2.trans ht.2))
    rw [eq_sub_iff_add_eq, add_comm, intervalIntegral.integral_add_adjacent_intervals h2
      (h1.mono_set (by rw [uIcc_of_le hr.2, uIcc_of_le ht.1]; exact Icc_subset_Icc hr.1 le_rfl))]
  have hcont : ∀ t ∈ Icc t₁ t₂, ContinuousOn (fun r => Complex.exp (∫ s in r..t, lam s))
      (uIcc t₁ t) := by
    intro t ht
    rw [uIcc_of_le ht.1]
    have : ContinuousOn (fun r => Complex.exp ((∫ s in t₁..t, lam s) - ∫ s in t₁..r, lam s))
        (Icc t₁ t) := by
      refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.sub ?_)
      refine hprim.mono ?_
      rw [uIcc_of_le hlt]; exact Icc_subset_Icc le_rfl ht.2
    exact this.congr fun r hr => by rw [hsub t ht r hr]
  have hint1 : ∀ t ∈ Icc t₁ t₂, ∀ i, IntervalIntegrable (fun r =>
      Complex.exp (∫ s in r..t, lam s) * f i r) volume t₁ t := by
    intro t ht i
    exact ((hf i).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hlt]; exact Icc_subset_Icc le_rfl ht.2)).continuousOn_mul
        (hcont t ht)
  have hae' : ∀ t ∈ Icc t₁ t₂, ∀ᵐ r ∂volume, r ∈ Set.uIoc t₁ t → ∀ i,
      Complex.exp (∫ s in r..t, lam s) * f i r =
        Complex.exp (∫ s in r..t, lam s) * ∑ i', τ i i' r * c i' r := by
    intro t ht
    filter_upwards [hae] with r hr hrI i
    rw [uIoc_of_le ht.1] at hrI
    rw [hr ⟨hrI.1.le, hrI.2.trans ht.2⟩ i]
  refine ⟨fun t ht i => ?_, fun i t ht => ?_⟩
  · rw [intervalIntegrable_iff]
    refine (intervalIntegrable_iff.1 (hint1 t ht i)).congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact (hae' t ht).mono fun r hr hrI => hr hrI i
  · rw [hD0 i t ht]
    congr 1
    exact intervalIntegral.integral_congr_ae ((hae' t ht).mono fun r hr hrI => hr hrI i)

/-! # the `ℓ²` helpers for the vector Duhamel bound

`sqrt_sum_norm_add_le'`: Minkowski in `ℓ²`. `norm_sq_integral_le`: the `ℓ²` norm of a vector of
interval integrals is at most the length times a uniform bound on the `ℓ²` norm of the
integrands (the integrands being interval integrable). -/

theorem sqrt_sum_norm_add_le' {I : Type*} (s : Finset I) (x y : I → ℂ) :
    Real.sqrt (∑ i ∈ s, ‖x i + y i‖ ^ 2) ≤
      Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) + Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) := by
  classical
  have h := norm_add_le (WithLp.toLp 2 (fun i : s => x i)) (WithLp.toLp 2 (fun i : s => y i))
  simp only [PiLp.norm_eq_of_L2, PiLp.add_apply, Finset.univ_eq_attach] at h
  rw [Finset.sum_attach s (fun i => ‖x i + y i‖ ^ 2), Finset.sum_attach s (fun i => ‖x i‖ ^ 2),
    Finset.sum_attach s (fun i => ‖y i‖ ^ 2)] at h
  exact h

theorem norm_sq_integral_le {I : Type*} (s : Finset I) (F : I → ℝ → ℂ) {a b G : ℝ}
    (hab : a ≤ b) (hF : ∀ i ∈ s, IntervalIntegrable (F i) volume a b) (hG : 0 ≤ G)
    (hb : ∀ r ∈ Ioc a b, ∑ i ∈ s, ‖F i r‖ ^ 2 ≤ G ^ 2) :
    ∑ i ∈ s, ‖∫ r in a..b, F i r‖ ^ 2 ≤ ((b - a) * G) ^ 2 := by
  set J : I → ℂ := fun i => ∫ r in a..b, F i r with hJ
  set N2 : ℝ := ∑ i ∈ s, ‖J i‖ ^ 2 with hN2
  have hN0 : 0 ≤ N2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hZ : (N2 : ℂ) = ∫ r in a..b, ∑ i ∈ s, (starRingEnd ℂ) (J i) * F i r := by
    rw [intervalIntegral.integral_finsetSum (fun i hi => (hF i hi).const_mul _)]
    rw [hN2]; push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul]
    have e : ∫ x in a..b, F i x = J i := rfl
    rw [e, Complex.conj_mul']
  have hpt : ∀ r ∈ Ioc a b, ‖∑ i ∈ s, (starRingEnd ℂ) (J i) * F i r‖ ≤ Real.sqrt N2 * G := by
    intro r hr
    calc ‖∑ i ∈ s, (starRingEnd ℂ) (J i) * F i r‖ ≤ ∑ i ∈ s, ‖J i‖ * ‖F i r‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul, Complex.norm_conj]
      _ ≤ Real.sqrt (∑ i ∈ s, ‖J i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖F i r‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt N2 * G := by
          gcongr
          exact Real.sqrt_le_iff.2 ⟨hG, hb r hr⟩
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun r => ∑ i ∈ s, (starRingEnd ℂ) (J i) * F i r)
    (fun r hr => hpt r (by rwa [Set.uIoc_of_le hab] at hr))
  rw [← hZ, Complex.norm_real, Real.norm_of_nonneg hN0, abs_of_nonneg (sub_nonneg.2 hab)] at hint
  by_cases h0 : N2 = 0
  · rw [h0]; positivity
  · have hp : 0 < Real.sqrt N2 := Real.sqrt_pos.2 (lt_of_le_of_ne hN0 (Ne.symm h0))
    have h1 : Real.sqrt N2 ≤ (b - a) * G := by
      have : Real.sqrt N2 * Real.sqrt N2 ≤ Real.sqrt N2 * ((b - a) * G) := by
        rw [Real.mul_self_sqrt hN0]; nlinarith
      exact le_of_mul_le_mul_left this hp
    calc N2 = Real.sqrt N2 ^ 2 := (Real.sq_sqrt hN0).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords.Discard

/-! # Derivative bounds for the symbol factor `(iξ)^w (1 - μ)`

`indexWordSymbol w` is the radian symbol of a word of length `a`; its iterated derivatives of
order `n` are bounded by `c (1 + ‖ξ‖)^a`. With `μ` smooth and its derivatives of order `≤ m` bounded,
the derivatives of `symbolCutoffFactor μ w = (iξ)^w (1 - μ)` of order `≤ m` are bounded by `B (1 + ‖ξ‖)^{Kf}`,
uniformly in the words of length `a ≤ Kf` (Leibniz: `norm_iteratedFDeriv_mul_le`). -/

/-- The symbol `∏_j (i ξ_{w j})`. -/
def indexWordSymbol {a : ℕ} (w : Fin a → Fin 2) (ξ : Vec 2) : ℂ :=
  ∏ j : Fin a, (Complex.I * (ξ (w j) : ℂ))

/-- The coordinate multiplier `ξ ↦ i ξ_k` as a continuous linear map. -/
def coordMultiplierCLM (k : Fin 2) : Vec 2 →L[ℝ] ℂ :=
  (Complex.I • Complex.ofRealCLM).comp (ContinuousLinearMap.proj k)

theorem Lin_apply (k : Fin 2) (ξ : Vec 2) : coordMultiplierCLM k ξ = Complex.I * (ξ k : ℂ) := by
  simp [coordMultiplierCLM]

theorem Lin_norm_le (k : Fin 2) : ‖coordMultiplierCLM k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [Lin_apply, norm_mul, Complex.norm_I, one_mul, one_mul, Complex.norm_real]
  exact norm_le_pi_norm x k

theorem Lin_iter_le (k : Fin 2) (i : ℕ) (ξ : Vec 2) :
    ‖iteratedFDeriv ℝ i (coordMultiplierCLM k) ξ‖ ≤ 1 + ‖ξ‖ := by
  rcases i with _ | j
  · rw [norm_iteratedFDeriv_zero]
    calc ‖coordMultiplierCLM k ξ‖ ≤ ‖coordMultiplierCLM k‖ * ‖ξ‖ := (coordMultiplierCLM k).le_opNorm ξ
      _ ≤ 1 * ‖ξ‖ := by gcongr; exact Lin_norm_le k
      _ ≤ _ := by linarith [norm_nonneg ξ]
  · rw [← norm_iteratedFDeriv_fderiv]
    have : fderiv ℝ (coordMultiplierCLM k) = fun _ => coordMultiplierCLM k := by
      funext x; exact (coordMultiplierCLM k).fderiv
    rw [this]
    rcases j with _ | j
    · rw [norm_iteratedFDeriv_zero]
      linarith [Lin_norm_le k, norm_nonneg ξ]
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      simp; positivity

theorem Sym_contDiff {a : ℕ} (w : Fin a → Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (indexWordSymbol w) := by
  unfold indexWordSymbol
  refine contDiff_prod fun j _ => ?_
  have h : (fun ξ : Vec 2 => Complex.I * (ξ (w j) : ℂ)) = ⇑(coordMultiplierCLM (w j)) := by
    funext ξ; rw [Lin_apply]
  rw [h]
  exact (coordMultiplierCLM (w j)).contDiff

theorem Sym_succ {a : ℕ} (w : Fin (a + 1) → Fin 2) :
    indexWordSymbol w = fun ξ => coordMultiplierCLM (w 0) ξ * indexWordSymbol (fun j : Fin a => w j.succ) ξ := by
  funext ξ
  simp only [indexWordSymbol, Fin.prod_univ_succ, Lin_apply]

theorem Sym_bound (a : ℕ) : ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (w : Fin a → Fin 2) (ξ : Vec 2),
    ‖iteratedFDeriv ℝ n (indexWordSymbol w) ξ‖ ≤ c * (1 + ‖ξ‖) ^ a := by
  induction a with
  | zero =>
    intro n
    refine ⟨1, zero_le_one, fun w ξ => ?_⟩
    have : indexWordSymbol w = fun _ => (1 : ℂ) := by funext ξ; simp [indexWordSymbol]
    rw [this]
    rcases n with _ | n
    · simp
    · rw [iteratedFDeriv_const_of_ne (by omega)]; simp
  | succ a ih =>
    intro n
    choose c hc0 hc using ih
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * c (n - i), ?_, fun w ξ => ?_⟩
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hc0 _)
    · rw [Sym_succ]
      have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun ξ => coordMultiplierCLM (w 0) ξ) := (coordMultiplierCLM (w 0)).contDiff
      have h2 := Sym_contDiff (fun j : Fin a => w j.succ)
      refine (norm_iteratedFDeriv_mul_le (N := (⊤ : ℕ∞)) h1 h2 ξ (by exact_mod_cast le_top)).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hA := Lin_iter_le (w 0) i ξ
      have hB := hc (n - i) (fun j : Fin a => w j.succ) ξ
      have hpos : 0 ≤ (1 + ‖ξ‖) := by positivity
      calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (coordMultiplierCLM (w 0)) ξ‖ *
            ‖iteratedFDeriv ℝ (n - i) (indexWordSymbol fun j : Fin a => w j.succ) ξ‖
          ≤ (n.choose i : ℝ) * (1 + ‖ξ‖) * (c (n - i) * (1 + ‖ξ‖) ^ a) := by
            gcongr
        _ = _ := by ring

/-- The factor `(iξ)^w (1 - μ(ξ))`. -/
def symbolCutoffFactor {a : ℕ} (μ : Vec 2 → ℝ) (w : Fin a → Fin 2) : Vec 2 → ℂ :=
  fun ξ => indexWordSymbol w ξ * ((1 - μ ξ : ℝ) : ℂ)

theorem Nu_contDiff {μ : Vec 2 → ℝ} (hμ : ContDiff ℝ (⊤ : ℕ∞) μ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Vec 2 => ((1 - μ ξ : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hμ)

theorem Nu_bound {μ : Vec 2 → ℝ} (hμ : ContDiff ℝ (⊤ : ℕ∞) μ) {Bμ : ℝ} {m : ℕ}
    (hB : ∀ l ≤ m, ∀ θ, ‖iteratedFDeriv ℝ l μ θ‖ ≤ Bμ) {k : ℕ} (hk : k ≤ m) (ξ : Vec 2) :
    ‖iteratedFDeriv ℝ k (fun ξ : Vec 2 => ((1 - μ ξ : ℝ) : ℂ)) ξ‖ ≤ 1 + Bμ := by
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Vec 2 => 1 - μ ξ) := contDiff_const.sub hμ
  have e : (fun ξ : Vec 2 => ((1 - μ ξ : ℝ) : ℂ)) =
      (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ (fun ξ : Vec 2 => 1 - μ ξ) := rfl
  rw [e, LinearIsometry.norm_iteratedFDeriv_comp_left _ hsub.contDiffAt (by exact_mod_cast le_top)]
  have hB0 := hB k hk ξ
  rcases k with _ | k
  · rw [norm_iteratedFDeriv_zero] at hB0 ⊢
    calc ‖1 - μ ξ‖ ≤ ‖(1 : ℝ)‖ + ‖μ ξ‖ := norm_sub_le _ _
      _ ≤ _ := by simpa using hB0
  · have e2 : iteratedFDeriv ℝ (k + 1) (fun ξ : Vec 2 => 1 - μ ξ) ξ =
        - iteratedFDeriv ℝ (k + 1) μ ξ := by
      have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := k + 1) (x := ξ) (f := fun _ : Vec 2 => (1 : ℝ))
        (g := μ) (contDiff_const.contDiffAt.of_le (by exact_mod_cast le_top)) (hμ.contDiffAt.of_le (by exact_mod_cast le_top))
      simpa [Pi.sub_def, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)] using this
    rw [e2, norm_neg]
    linarith [hB0]

theorem H_contDiff {a : ℕ} {μ : Vec 2 → ℝ} (hμ : ContDiff ℝ (⊤ : ℕ∞) μ) (w : Fin a → Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (symbolCutoffFactor μ w) := (Sym_contDiff w).mul (Nu_contDiff hμ)

theorem H_bound (Kf m : ℕ) (Bμ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (μ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) μ →
      (∀ l ≤ m, ∀ θ, ‖iteratedFDeriv ℝ l μ θ‖ ≤ Bμ) → 0 ≤ Bμ →
      ∀ a ≤ Kf, ∀ (w : Fin a → Fin 2), ∀ n ≤ m, ∀ ξ : Vec 2,
        ‖iteratedFDeriv ℝ n (symbolCutoffFactor μ w) ξ‖ ≤ B * (1 + ‖ξ‖) ^ Kf := by
  have hs := fun a n => Sym_bound a n
  choose c hc0 hc using hs
  set c' : ℕ → ℕ → ℝ := fun a n =>
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * c a i * (1 + Bμ) ^ 1 with hc'
  refine ⟨∑ a ∈ Finset.range (Kf + 1), ∑ n ∈ Finset.range (m + 1), |c' a n|, ?_, ?_⟩
  · exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun n _ => abs_nonneg _
  intro μ hμ hB hB0 a ha w n hn ξ
  have h1 := Sym_contDiff w
  have h2 := Nu_contDiff hμ
  have hx : (1 : ℝ) ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  have step : ‖iteratedFDeriv ℝ n (symbolCutoffFactor μ w) ξ‖ ≤ c' a n * (1 + ‖ξ‖) ^ a := by
    refine (norm_iteratedFDeriv_mul_le (N := (⊤ : ℕ∞)) h1 h2 ξ (by exact_mod_cast le_top)).trans ?_
    simp only [hc', Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
    have hA := hc a i w ξ
    have hN := Nu_bound hμ hB (k := n - i) (by omega) ξ
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (indexWordSymbol w) ξ‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun ξ : Vec 2 => ((1 - μ ξ : ℝ) : ℂ)) ξ‖
        ≤ (n.choose i : ℝ) * (c a i * (1 + ‖ξ‖) ^ a) * (1 + Bμ) := by
          gcongr
          exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hc0 _ _) (by positivity))
      _ = _ := by ring
  have hle : c' a n ≤ ∑ a ∈ Finset.range (Kf + 1), ∑ n ∈ Finset.range (m + 1), |c' a n| := by
    refine (le_abs_self _).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ n ∈ Finset.range (m + 1), |c' a n|)
      (fun a _ => Finset.sum_nonneg fun n _ => abs_nonneg _) (Finset.mem_range.2 (by omega : a < Kf + 1)))
    exact Finset.single_le_sum (f := fun n => |c' a n|) (fun n _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega : n < m + 1))
  calc _ ≤ c' a n * (1 + ‖ξ‖) ^ a := step
    _ ≤ _ * (1 + ‖ξ‖) ^ Kf := by
        have hc'0 : 0 ≤ c' a n := by
          refine Finset.sum_nonneg fun i _ => ?_
          have := hc0 a i
          positivity
        calc c' a n * (1 + ‖ξ‖) ^ a ≤ c' a n * (1 + ‖ξ‖) ^ Kf := by
              gcongr
          _ ≤ _ := by gcongr

/-! # iterated directional derivatives on the plane

`dirDerivAlong v f = ∂_v f`, `iterDirDeriv vs f` the iterate along a list of directions. For `C^∞` functions the
partials commute, the iterate is `iteratedFDeriv` applied to the list, and it vanishes where `f` does
on an open set. Used for the Leibniz expansion of `∂^γ [(iξ)^w (1 - μ) ĝ]`. -/

/-- The directional derivative `∂_v f`. -/
def dirDerivAlong (v : Vec 2) (f : Vec 2 → ℂ) : Vec 2 → ℂ := fun ξ => fderiv ℝ f ξ v

/-- The iterated directional derivative along a list of directions. -/
def iterDirDeriv : List (Vec 2) → (Vec 2 → ℂ) → (Vec 2 → ℂ)
  | [], f => f
  | v :: vs, f => dirDerivAlong v (iterDirDeriv vs f)

theorem P_contDiff {f : Vec 2 → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (dirDerivAlong v f) :=
  (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem PL_contDiff {f : Vec 2 → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (vs : List (Vec 2)) :
    ContDiff ℝ (⊤ : ℕ∞) (iterDirDeriv vs f) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact P_contDiff ih v

theorem P_hasFDerivAt {f : Vec 2 → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (u : Vec 2) (ξ : Vec 2) :
    HasFDerivAt (dirDerivAlong u f) ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ f) ξ)) ξ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) ξ :=
    ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)) ξ
  exact (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp ξ hd.hasFDerivAt

theorem P_comm {f : Vec 2 → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (u v : Vec 2) :
    dirDerivAlong v (dirDerivAlong u f) = dirDerivAlong u (dirDerivAlong v f) := by
  funext ξ
  have h1 := (P_hasFDerivAt hf u ξ).fderiv
  have h2 := (P_hasFDerivAt hf v ξ).fderiv
  have hs : IsSymmSndFDerivAt ℝ f ξ :=
    (hf.contDiffAt).isSymmSndFDerivAt (by simp)
  show fderiv ℝ (dirDerivAlong u f) ξ v = fderiv ℝ (dirDerivAlong v f) ξ u
  rw [h1, h2]
  simp [hs.eq]

theorem PL_P_comm {f : Vec 2 → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Vec 2)
    (l : List (Vec 2)) : dirDerivAlong v (iterDirDeriv l f) = iterDirDeriv l (dirDerivAlong v f) := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    show dirDerivAlong v (dirDerivAlong u (iterDirDeriv l f)) = dirDerivAlong u (iterDirDeriv l (dirDerivAlong v f))
    rw [P_comm (PL_contDiff hf l), ih]

theorem PL_append (l1 l2 : List (Vec 2)) (f : Vec 2 → ℂ) :
    iterDirDeriv (l1 ++ l2) f = iterDirDeriv l1 (iterDirDeriv l2 f) := by
  induction l1 with
  | nil => rfl
  | cons u l ih => show dirDerivAlong u (iterDirDeriv (l ++ l2) f) = _; rw [ih]; rfl

theorem PL_zero_on {f : Vec 2 → ℂ} {U : Set (Vec 2)} (hU : IsOpen U) (hf : ∀ ξ ∈ U, f ξ = 0)
    (l : List (Vec 2)) : ∀ ξ ∈ U, iterDirDeriv l f ξ = 0 := by
  induction l with
  | nil => exact hf
  | cons u l ih =>
    intro ξ hξ
    have : iterDirDeriv l f =ᶠ[nhds ξ] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (hU.mem_nhds hξ) ih
    show fderiv ℝ (iterDirDeriv l f) ξ u = 0
    rw [this.fderiv_eq]
    simp

theorem PL_eq_iterated {f : Vec 2 → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (vs : List (Vec 2)) (ξ : Vec 2) :
    iterDirDeriv vs f ξ = iteratedFDeriv ℝ vs.length f ξ vs.get := by
  induction vs generalizing ξ with
  | nil => show f ξ = iteratedFDeriv ℝ 0 f ξ _; rw [iteratedFDeriv_zero_apply]
  | cons v vs ih =>
    have hfun : iterDirDeriv vs f = fun x => iteratedFDeriv ℝ vs.length f x vs.get := funext ih
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ vs.length f) ξ :=
      (hf.differentiable_iteratedFDeriv (m := vs.length) (by exact_mod_cast ENat.natCast_lt_top vs.length)) ξ
    show fderiv ℝ (iterDirDeriv vs f) ξ v = _
    rw [hfun]
    have h1 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin vs.length => Vec 2) ℂ vs.get).hasFDerivAt.comp ξ hd.hasFDerivAt).fderiv
    have h2 : (fun x => iteratedFDeriv ℝ vs.length f x vs.get) =
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin vs.length => Vec 2) ℂ vs.get) ∘ iteratedFDeriv ℝ vs.length f := rfl
    rw [h2, h1]
    exact (iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := f) (x := ξ) (v :: vs).get).symm

theorem PL_norm_le {f : Vec 2 → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (vs : List (Vec 2))
    (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (ξ : Vec 2) :
    ‖iterDirDeriv vs f ξ‖ ≤ ‖iteratedFDeriv ℝ vs.length f ξ‖ := by
  rw [PL_eq_iterated hf]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have : ∏ i, ‖vs.get i‖ ≤ 1 := by
    refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hv _ (List.get_mem _ _))
  calc _ ≤ ‖iteratedFDeriv ℝ vs.length f ξ‖ * 1 := by gcongr
    _ = _ := mul_one _

theorem line_hasDerivAt {F : Vec 2 → ℂ} {ξ : Vec 2} (hF : DifferentiableAt ℝ F ξ) (v : Vec 2) :
    HasDerivAt (fun t : ℝ => F (ξ + t • v)) (fderiv ℝ F ξ v) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => ξ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add ξ
  have h2 : HasFDerivAt F (fderiv ℝ F ξ) (ξ + (0:ℝ) • v) := by simpa using hF.hasFDerivAt
  exact h2.comp_hasDerivAt (0:ℝ) h1

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open ContinuousLinearMap
namespace AVRegularity.CycleWords.Discard

/-! # the family dual criterion

A family `X_i ∈ H_i` of elements is the image `ι_i x_i` of a family `x_i` with
`(∑ ‖x_i‖²)^{1/2} ≤ M` as soon as `∑ ⟨X_i, g_i⟩ ≤ M (∑ N_i²)^{1/2}` whenever
`⟨ι_i w, g_i⟩ ≤ N_i ‖w‖` for all `w` and all `i`. One-line instance of the scalar criterion on
the `ℓ²` sums (`PiLp 2`). -/

variable {I : Type*} [Fintype I] {V H : I → Type*}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)] [∀ i, CompleteSpace (V i)]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)] [∀ i, CompleteSpace (H i)]

/-- The diagonal map on `ℓ²` sums. -/
def DiagMap (ι : ∀ i, V i →L[ℝ] H i) : PiLp 2 V →L[ℝ] PiLp 2 H :=
  ((PiLp.continuousLinearEquiv 2 ℝ H).symm : (∀ i, H i) →L[ℝ] PiLp 2 H) ∘L
    (ContinuousLinearMap.pi fun i => ι i ∘L ContinuousLinearMap.proj i) ∘L
    ((PiLp.continuousLinearEquiv 2 ℝ V : PiLp 2 V →L[ℝ] ∀ i, V i))

/-- **Family dual criterion.** -/
theorem mem_of_family_dual_bound (ι : ∀ i, V i →L[ℝ] H i) (X : ∀ i, H i) (M : ℝ)
    (hM : 0 ≤ M)
    (h : ∀ (g : ∀ i, H i) (N : I → ℝ), (∀ i, 0 ≤ N i) →
      (∀ i (w : V i), inner ℝ (ι i w) (g i) ≤ N i * ‖w‖) →
      ∑ i, inner ℝ (X i) (g i) ≤ M * Real.sqrt (∑ i, N i ^ 2)) :
    ∃ x : ∀ i, V i, (∀ i, ι i (x i) = X i) ∧ Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ M := by
  obtain ⟨x, hx, hxn⟩ := mem_of_dual_bound (DiagMap ι) (WithLp.toLp 2 X) M hM (by
    intro g N hN hg
    set Nf : I → ℝ := fun i => ‖ContinuousLinearMap.adjoint (ι i) (g i)‖ with hNf
    have hadj : ∀ i (w : V i), inner ℝ (ι i w) (g i) ≤ Nf i * ‖w‖ := fun i w => by
      rw [← ContinuousLinearMap.adjoint_inner_right]
      exact (real_inner_le_norm _ _).trans (by rw [mul_comm])
    have hS : Real.sqrt (∑ i, Nf i ^ 2) ≤ N := by
      set S : ℝ := ∑ i, Nf i ^ 2 with hSdef
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
      let w : PiLp 2 V := WithLp.toLp 2 fun i => ContinuousLinearMap.adjoint (ι i) (g i)
      have hw := hg w
      have hwn : ‖w‖ = Real.sqrt S := by
        rw [PiLp.norm_eq_of_L2]
      have hin : inner ℝ (DiagMap ι w) g = S := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        show inner ℝ (ι i (ContinuousLinearMap.adjoint (ι i) (g i))) (g i) = _
        rw [← ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
      rw [hin, hwn] at hw
      rcases hS0.eq_or_lt with h0 | hpos
      · rw [← h0]; simpa using hN
      · have hsq := Real.sqrt_pos.2 hpos
        have : Real.sqrt S * Real.sqrt S ≤ N * Real.sqrt S := by
          rwa [Real.mul_self_sqrt hS0]
        exact le_of_mul_le_mul_right this hsq
    have := h (fun i => g i) Nf (fun i => norm_nonneg _) hadj
    rw [PiLp.inner_apply]
    exact this.trans (mul_le_mul_of_nonneg_left hS hM))
  refine ⟨fun i => x i, fun i => ?_, ?_⟩
  · have := congrArg (fun y : PiLp 2 H => y i) hx
    exact this
  · rw [PiLp.norm_eq_of_L2] at hxn
    exact hxn

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords.Discard

/-! # the Leibniz family `D γ = ∂_0^{γ₁} ∂_1^{γ₂} (h · Ê)` as a sum of terms

A term `(δ, γ')` stands for `(∂^δ h) · E γ'`; `Step j` differentiates a multiset of terms
(Leibniz), `leibnizTerms a b` is `∂_0^a ∂_1^b` of the single term `h · E 0`. Because multiset addition
commutes, `Step 0` and `Step 1` commute, which makes the family `D (a,b)` consistent:
`D (a+1,b) = ∂_0 D (a,b)` and `D (a,b+1) = ∂_1 D (a,b)`. -/

/-- The unit multi-index `e_j`. -/
def unitIndexPair (j : Fin 2) : ℕ × ℕ := if j = 0 then (1, 0) else (0, 1)

/-- The partial derivative `∂_0^{δ₁} ∂_1^{δ₂} h`. -/
def multiPartialDeriv (h : Vec 2 → ℂ) (δ : ℕ × ℕ) : Vec 2 → ℂ :=
  iterDirDeriv (List.replicate δ.1 (basisVec 0) ++ List.replicate δ.2 (basisVec 1)) h

theorem Hd_contDiff {h : Vec 2 → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (δ : ℕ × ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (multiPartialDeriv h δ) := PL_contDiff hh _

theorem Hd_step {h : Vec 2 → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (j : Fin 2) (δ : ℕ × ℕ) :
    multiPartialDeriv h (δ + unitIndexPair j) = dirDerivAlong (basisVec j) (multiPartialDeriv h δ) := by
  fin_cases j
  · simp only [unitIndexPair, multiPartialDeriv]
    simp [List.replicate_succ, iterDirDeriv]
  · simp only [unitIndexPair, multiPartialDeriv]
    simp only [Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte,
      PL_append]
    rw [PL_P_comm (PL_contDiff hh _)]
    rfl


/-- A term `(δ, γ')` stands for `∂^δ h · E γ'`. -/
abbrev Term := (ℕ × ℕ) × (ℕ × ℕ)

/-- Differentiating a sum of terms: Leibniz on each term. -/
def Step (j : Fin 2) (M : Multiset Term) : Multiset Term :=
  M.map (fun p => (p.1 + unitIndexPair j, p.2)) + M.map (fun p => (p.1, p.2 + unitIndexPair j))

/-- The function represented by a multiset of terms. -/
def Dfun (h : Vec 2 → ℂ) (E : ℕ × ℕ → Vec 2 → ℂ) (M : Multiset Term) : Vec 2 → ℂ :=
  fun ξ => (M.map fun p => multiPartialDeriv h p.1 ξ * E p.2 ξ).sum

theorem Step_comm (i j : Fin 2) (M : Multiset Term) :
    Step i (Step j M) = Step j (Step i M) := by
  unfold Step
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def]
  have e1 : (fun p : Term => (p.1 + unitIndexPair j + unitIndexPair i, p.2)) =
      fun p => (p.1 + unitIndexPair i + unitIndexPair j, p.2) := by
    funext p; rw [add_right_comm]
  have e2 : (fun p : Term => (p.1, p.2 + unitIndexPair j + unitIndexPair i)) =
      fun p => (p.1, p.2 + unitIndexPair i + unitIndexPair j) := by
    funext p; rw [add_right_comm]
  simp only [e1, e2]
  abel


theorem Hd_hasDerivAt {h : Vec 2 → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (j : Fin 2) (δ : ℕ × ℕ)
    (ξ : Vec 2) :
    HasDerivAt (fun t : ℝ => multiPartialDeriv h δ (ξ + t • basisVec j)) (multiPartialDeriv h (δ + unitIndexPair j) ξ) 0 := by
  rw [Hd_step hh j δ]
  exact line_hasDerivAt
    (((Hd_contDiff hh δ).differentiable (by simp)) ξ) (basisVec j)

theorem Dfun_hasDerivAt {h : Vec 2 → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (E : ℕ × ℕ → Vec 2 → ℂ) (j : Fin 2) (ξ : Vec 2) (M : Multiset Term)
    (hE : ∀ p ∈ M, HasDerivAt (fun t : ℝ => E p.2 (ξ + t • basisVec j))
      (E (p.2 + unitIndexPair j) ξ) 0) :
    HasDerivAt (fun t : ℝ => Dfun h E M (ξ + t • basisVec j))
      (Dfun h E (Step j M) ξ) 0 := by
  induction M using Multiset.induction_on with
  | empty =>
    simp only [Dfun, Step, Multiset.map_zero, Multiset.sum_zero, add_zero]
    exact hasDerivAt_const _ _
  | cons p M ih =>
    have ih' := ih fun q hq => hE q (Multiset.mem_cons_of_mem hq)
    have hp := hE p (Multiset.mem_cons_self p M)
    have hT := (Hd_hasDerivAt hh j p.1 ξ).mul hp
    have hsum := hT.add ih'
    simp only [zero_smul, add_zero] at hsum
    have e1 : Dfun h E (Step j (p ::ₘ M)) ξ =
        (multiPartialDeriv h (p.1 + unitIndexPair j) ξ * E p.2 ξ + multiPartialDeriv h p.1 ξ * E (p.2 + unitIndexPair j) ξ) +
          Dfun h E (Step j M) ξ := by
      simp only [Dfun, Step, Multiset.map_cons, Multiset.cons_add, Multiset.add_cons,
        Multiset.sum_cons, Multiset.map_add, Multiset.sum_add]
      ring
    rw [e1]
    convert hsum using 1
    funext t
    simp [Dfun]


/-- The terms of `∂_0^a ∂_1^b (h · Ê)`: start from `h · E 0` and differentiate. -/
def leibnizTerms (a b : ℕ) : Multiset Term :=
  (Step 0)^[a] ((Step 1)^[b] {((0, 0), (0, 0))})

theorem Step_card (j : Fin 2) (M : Multiset Term) :
    Multiset.card (Step j M) = 2 * Multiset.card M := by
  simp [Step, two_mul]

theorem Step_sum (j : Fin 2) (γ : ℕ × ℕ) (M : Multiset Term)
    (hM : ∀ p ∈ M, p.1 + p.2 = γ) : ∀ p ∈ Step j M, p.1 + p.2 = γ + unitIndexPair j := by
  intro p hp
  simp only [Step, Multiset.mem_add, Multiset.mem_map] at hp
  rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · simp only [← hM q hq]; abel
  · simp only [← hM q hq]; abel

theorem Mab_sum (a b : ℕ) : ∀ p ∈ leibnizTerms a b, p.1 + p.2 = (a, b) := by
  have h1 : ∀ b : ℕ, ∀ p : Term, p ∈ (Step 1)^[b] ({((0, 0), (0, 0))} : Multiset Term) →
      p.1 + p.2 = (0, b) := by
    intro b
    induction b with
    | zero => intro p hp; simp at hp; subst hp; simp
    | succ b ih =>
      intro p hp
      rw [Function.iterate_succ_apply'] at hp
      have := Step_sum 1 _ _ ih p hp
      simpa [unitIndexPair] using this
  have h0 : ∀ a : ℕ, ∀ p : Term, p ∈ leibnizTerms a b → p.1 + p.2 = (a, b) := by
    intro a
    induction a with
    | zero => intro p hp; exact h1 b p hp
    | succ a ih =>
      intro p hp
      unfold leibnizTerms at hp
      rw [Function.iterate_succ_apply'] at hp
      have := Step_sum 0 _ _ ih p hp
      simpa [unitIndexPair] using this
  exact h0 a

theorem Mab_card (a b : ℕ) : Multiset.card (leibnizTerms a b) = 2 ^ (a + b) := by
  have h1 : ∀ b : ℕ, Multiset.card ((Step 1)^[b] ({((0, 0), (0, 0))} : Multiset Term)) =
      2 ^ b := by
    intro b
    induction b with
    | zero => simp
    | succ b ih => rw [Function.iterate_succ_apply', Step_card, ih]; ring
  unfold leibnizTerms
  have : ∀ a : ℕ, Multiset.card ((Step 0)^[a] ((Step 1)^[b]
      ({((0, 0), (0, 0))} : Multiset Term))) = 2 ^ (a + b) := by
    intro a
    induction a with
    | zero => simpa using h1 b
    | succ a ih => rw [Function.iterate_succ_apply', Step_card, ih]; ring
  exact this a

theorem Mab_succ_left (a b : ℕ) : leibnizTerms (a + 1) b = Step 0 (leibnizTerms a b) := by
  unfold leibnizTerms; rw [Function.iterate_succ_apply']

theorem Mab_succ_right (a b : ℕ) : leibnizTerms a (b + 1) = Step 1 (leibnizTerms a b) := by
  have key : ∀ a : ℕ, ∀ N : Multiset Term,
      (Step 0)^[a] (Step 1 N) = Step 1 ((Step 0)^[a] N) := by
    intro a
    induction a with
    | zero => intro N; rfl
    | succ a ih =>
      intro N
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Step_comm]
  unfold leibnizTerms
  rw [Function.iterate_succ_apply', key]


theorem Dfun_continuous {h : Vec 2 → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (E : ℕ × ℕ → Vec 2 → ℂ) (M : Multiset Term)
    (hE : ∀ p : Term, p ∈ M → Continuous (E p.2)) : Continuous (Dfun h E M) := by
  induction M using Multiset.induction_on with
  | empty => unfold Dfun; simpa using continuous_const
  | cons p M ih =>
    have hp : Continuous fun ξ => multiPartialDeriv h p.1 ξ * E p.2 ξ :=
      (Hd_contDiff hh p.1).continuous.mul (hE p (Multiset.mem_cons_self p M))
    have := hp.add (ih fun q hq => hE q (Multiset.mem_cons_of_mem hq))
    convert this using 1
    funext ξ
    simp [Dfun]

theorem Mab_hasDerivAt {h : Vec 2 → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (E : ℕ × ℕ → Vec 2 → ℂ) (β : ℕ × ℕ)
    (hEd : ∀ (j : Fin 2) (γ' : ℕ × ℕ), (γ' + unitIndexPair j).1 ≤ β.1 → (γ' + unitIndexPair j).2 ≤ β.2 →
      ∀ ξ : Vec 2, HasDerivAt (fun t : ℝ => E γ' (ξ + t • basisVec j)) (E (γ' + unitIndexPair j) ξ) 0)
    (j : Fin 2) (γ : ℕ × ℕ) (h1 : (γ + unitIndexPair j).1 ≤ β.1) (h2 : (γ + unitIndexPair j).2 ≤ β.2)
    (ξ : Vec 2) :
    HasDerivAt (fun t : ℝ => Dfun h E (leibnizTerms γ.1 γ.2) (ξ + t • basisVec j))
      (Dfun h E (leibnizTerms (γ + unitIndexPair j).1 (γ + unitIndexPair j).2) ξ) 0 := by
  have hE : ∀ p : Term, p ∈ leibnizTerms γ.1 γ.2 → HasDerivAt
      (fun t : ℝ => E p.2 (ξ + t • basisVec j)) (E (p.2 + unitIndexPair j) ξ) 0 := by
    intro p hp
    have hs := Mab_sum γ.1 γ.2 p hp
    have e1 : p.1.1 + p.2.1 = γ.1 := congrArg Prod.fst hs
    have e2 : p.1.2 + p.2.2 = γ.2 := congrArg Prod.snd hs
    refine hEd j p.2 ?_ ?_ ξ
    · simp only [Prod.fst_add] at h1 ⊢; omega
    · simp only [Prod.snd_add] at h2 ⊢; omega
  have := Dfun_hasDerivAt hh E j ξ (leibnizTerms γ.1 γ.2) hE
  convert this using 2
  fin_cases j
  · simp only [unitIndexPair, Fin.zero_eta, Fin.isValue, ↓reduceIte, Prod.fst_add, Prod.snd_add, add_zero]
    exact (Mab_succ_left γ.1 γ.2) ▸ rfl
  · simp only [unitIndexPair, Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte, Prod.fst_add,
      Prod.snd_add, add_zero]
    exact (Mab_succ_right γ.1 γ.2) ▸ rfl

end AVRegularity.CycleWords.Discard
end
end
