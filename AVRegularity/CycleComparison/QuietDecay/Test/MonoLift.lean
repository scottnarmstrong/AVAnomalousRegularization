-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Jet.Product
import Mathlib.Data.Int.Star
import Mathlib.Data.Fin.Tuple.Sort

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.QuietDecay

/-! Monomial test fields `Y ↦ Π_k (Y - X₀)_{α_k}`: smoothness, the first derivative in a coordinate
direction (a sum over the removal of one occurrence of the letter), linearity of the ordered
list derivative over finite sums, and commutation with a constant vector factor. -/

section
/-- `Π_{k} (Y - X₀)_{α_k}` for a word given as a list. -/
def monoF (X₀ : Vec 2) (α : List (Fin 2)) : Vec 2 → ℝ :=
  fun Y => (α.map fun i => Y i - X₀ i).prod

theorem monoF_nil (X₀ : Vec 2) : monoF X₀ [] = fun _ => 1 := by
  funext Y; simp [monoF]

theorem monoF_cons (X₀ : Vec 2) (i : Fin 2) (α : List (Fin 2)) (Y : Vec 2) :
    monoF X₀ (i :: α) Y = (Y i - X₀ i) * monoF X₀ α Y := by
  simp [monoF]

theorem contDiff_monoF (X₀ : Vec 2) (n : WithTop ℕ∞) :
    ∀ α : List (Fin 2), ContDiff ℝ n (monoF X₀ α)
  | [] => by rw [monoF_nil]; exact contDiff_const
  | i :: α => by
    have h : monoF X₀ (i :: α) = fun Y => (Y i - X₀ i) * monoF X₀ α Y := funext (monoF_cons X₀ i α)
    rw [h]
    exact ((contDiff_apply ℝ ℝ i).sub contDiff_const).mul (contDiff_monoF X₀ n α)

/-- All ways of deleting one occurrence of the letter `j` from a word. -/
def remLetter (j : Fin 2) : List (Fin 2) → List (List (Fin 2))
  | [] => []
  | a :: α => (if a = j then [α] else []) ++ (remLetter j α).map (a :: ·)

theorem fderiv_monoF_basis (X₀ : Vec 2) (j : Fin 2) :
    ∀ (α : List (Fin 2)) (Y : Vec 2), fderiv ℝ (monoF X₀ α) Y (basisVec j) =
      ((remLetter j α).map fun β => monoF X₀ β Y).sum
  | [], Y => by simp [monoF_nil, remLetter]
  | i :: α, Y => by
    have h1 : HasFDerivAt (fun Y : Vec 2 => Y i - X₀ i)
        (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ) Y :=
      (hasFDerivAt_apply i Y).sub_const _
    have h2 := ((contDiff_monoF X₀ 1 α).differentiable (by simp) Y).hasFDerivAt
    have h : monoF X₀ (i :: α) = fun Y => (Y i - X₀ i) * monoF X₀ α Y :=
      funext (monoF_cons X₀ i α)
    rw [h, (h1.fun_mul h2).fderiv]
    by_cases hij : i = j
    · subst hij
      simp [remLetter, fderiv_monoF_basis X₀ i α Y, monoF_cons, List.sum_map_mul_left,
        List.map_map, Function.comp_def, add_comm]
    · simp [remLetter, hij, fderiv_monoF_basis X₀ j α Y, monoF_cons, List.sum_map_mul_left,
        List.map_map, Function.comp_def]

section Smooth

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contDiff_fderiv_apply_infty {f : Vec 2 → V} (hf : ContDiff ℝ ∞ f) (v : Vec 2) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_derivList_infty : ∀ (l : List (Fin 2)) (g : Vec 2 → V),
    ContDiff ℝ ∞ g → ContDiff ℝ ∞ (derivList l g)
  | [], _, hg => hg
  | j :: l, _, hg => contDiff_derivList_infty l _ (contDiff_fderiv_apply_infty hg (basisVec j))

theorem contDiff_listSum {ι : Type*} {n : WithTop ℕ∞} (g : ι → Vec 2 → V) :
    ∀ L : List ι, (∀ β ∈ L, ContDiff ℝ n (g β)) → ContDiff ℝ n (fun Y => (L.map (g · Y)).sum)
  | [], _ => by simpa using contDiff_const
  | β :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h β (by simp)).add (contDiff_listSum g L fun γ hγ => h γ (by simp [hγ]))

theorem fderiv_listSum {ι : Type*} (g : ι → Vec 2 → V) (x v : Vec 2) :
    ∀ L : List ι, (∀ β ∈ L, ContDiff ℝ ∞ (g β)) →
      fderiv ℝ (fun Y => (L.map (g · Y)).sum) x v = (L.map fun β => fderiv ℝ (g β) x v).sum
  | [], _ => by simp
  | β :: L, h => by
    have hβ : ContDiff ℝ ∞ (g β) := h β (by simp)
    have hL := contDiff_listSum g L fun γ hγ => h γ (by simp [hγ])
    simp only [List.map_cons, List.sum_cons]
    have hd : fderiv ℝ (fun Y => g β Y + (L.map (g · Y)).sum) x =
        fderiv ℝ (g β) x + fderiv ℝ (fun Y => (L.map (g · Y)).sum) x :=
      fderiv_add (hβ.differentiable (by simp) x) (hL.differentiable (by simp) x)
    rw [hd, add_apply, fderiv_listSum g x v L fun γ hγ => h γ (by simp [hγ])]

/-- Linearity of the ordered list derivative over finite sums of smooth fields. -/
theorem derivList_listSum {ι : Type*} (g : ι → Vec 2 → V) :
    ∀ (l : List (Fin 2)) (L : List ι), (∀ β ∈ L, ContDiff ℝ ∞ (g β)) →
      derivList l (fun Y => (L.map (g · Y)).sum) =
        fun Y => (L.map fun β => derivList l (g β) Y).sum
  | [], L, _ => by simp
  | j :: l, L, h => by
    have h1 : (fun x => fderiv ℝ (fun Y => (L.map (g · Y)).sum) x (basisVec j)) =
        fun x => (L.map fun β => fderiv ℝ (g β) x (basisVec j)).sum :=
      funext fun x => fderiv_listSum g x _ L h
    show derivList l (fun x => fderiv ℝ (fun Y => (L.map (g · Y)).sum) x (basisVec j)) = _
    rw [h1]
    exact derivList_listSum (fun β x => fderiv ℝ (g β) x (basisVec j)) l L
      fun β hβ => contDiff_fderiv_apply_infty (h β hβ) _

/-- A constant vector factor commutes with the ordered list derivative. -/
theorem derivList_smul_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (w : E) :
    ∀ (l : List (Fin 2)) (f : Vec 2 → ℝ), ContDiff ℝ ∞ f →
      derivList l (fun Y => f Y • w) = fun Y => derivList l f Y • w
  | [], f, _ => rfl
  | j :: l, f, hf => by
    have h1 : (fun x => fderiv ℝ (fun Y => f Y • w) x (basisVec j)) =
        fun x => fderiv ℝ f x (basisVec j) • w := by
      funext x
      rw [fderiv_smul_const (hf.differentiable (by simp) x)]
      simp
    show derivList l (fun x => fderiv ℝ (fun Y => f Y • w) x (basisVec j)) = _
    rw [h1]
    exact derivList_smul_const w l _ (contDiff_fderiv_apply_infty hf _)

end Smooth

/-- The list derivative of a monomial, as a closed recursion over removals. -/
def monoDeriv (X₀ : Vec 2) : List (Fin 2) → List (Fin 2) → Vec 2 → ℝ
  | [], α => monoF X₀ α
  | j :: l, α => fun Y => ((remLetter j α).map fun β => monoDeriv X₀ l β Y).sum

theorem derivList_monoF (X₀ : Vec 2) :
    ∀ (l α : List (Fin 2)), derivList l (monoF X₀ α) = monoDeriv X₀ l α
  | [], α => rfl
  | j :: l, α => by
    have h1 : (fun x => fderiv ℝ (monoF X₀ α) x (basisVec j)) =
        fun x => ((remLetter j α).map fun β => monoF X₀ β x).sum :=
      funext fun x => fderiv_monoF_basis X₀ j α x
    show derivList l (fun x => fderiv ℝ (monoF X₀ α) x (basisVec j)) = _
    rw [h1, derivList_listSum (monoF X₀) l _ fun β _ => contDiff_monoF X₀ ∞ β]
    funext Y
    simp only [monoDeriv, derivList_monoF X₀ l]
end

/-! The ordered derivatives of a monomial at its centre: the integer `cnt l α`, its support
(`l` is a rearrangement of `α`), `cnt α α ≥ 1`, and the bound on derivatives near the centre. -/

/-- `cnt [] α = [α = []]`, `cnt (j :: l) α = Σ_{k, α_k = j} cnt l (α.eraseIdx k)`. -/
def cnt : List (Fin 2) → List (Fin 2) → ℕ
  | [], α => if α = [] then 1 else 0
  | j :: l, α => ((remLetter j α).map fun β => cnt l β).sum

theorem monoF_center (X₀ : Vec 2) (α : List (Fin 2)) :
    monoF X₀ α X₀ = if α = [] then 1 else 0 := by
  cases α with
  | nil => simp [monoF]
  | cons a α => simp [monoF_cons]

theorem monoDeriv_center (X₀ : Vec 2) :
    ∀ (l α : List (Fin 2)), monoDeriv X₀ l α X₀ = (cnt l α : ℝ)
  | [], α => by simp [monoDeriv, cnt, monoF_center]
  | j :: l, α => by
    simp only [monoDeriv, cnt, Nat.cast_list_sum, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left fun β _ => monoDeriv_center X₀ l β

/-- The ordered derivative of a monomial at its centre. -/
theorem derivList_monoF_center (X₀ : Vec 2) (l α : List (Fin 2)) :
    derivList l (monoF X₀ α) X₀ = (cnt l α : ℝ) := by
  rw [derivList_monoF, monoDeriv_center]

theorem mem_remLetter (j : Fin 2) : ∀ (α β : List (Fin 2)), β ∈ remLetter j α →
    β.length + 1 = α.length ∧ ∀ c, α.count c = β.count c + (if j = c then 1 else 0)
  | [], β, h => by simp [remLetter] at h
  | a :: α, β, h => by
    simp only [remLetter, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨γ, hγ, rfl⟩
    · split_ifs at h with ha
      · simp at h; subst h; subst ha
        simp [List.count_cons]
      · simp at h
    · obtain ⟨h1, h2⟩ := mem_remLetter j α γ hγ
      refine ⟨by simp [h1], fun c => ?_⟩
      have := h2 c
      simp only [List.count_cons]
      split_ifs <;> simp_all

theorem length_remLetter_le (j : Fin 2) : ∀ α : List (Fin 2), (remLetter j α).length ≤ α.length
  | [] => by simp [remLetter]
  | a :: α => by
    have := length_remLetter_le j α
    simp only [remLetter, List.length_append, List.length_map, List.length_cons]
    split_ifs <;> simp <;> omega

/-- The support of `cnt`: `l` is a rearrangement of `α`. -/
theorem cnt_ne_zero : ∀ (l α : List (Fin 2)), cnt l α ≠ 0 →
    l.length = α.length ∧ ∀ c, l.count c = α.count c
  | [], α, h => by
    simp only [cnt] at h
    split_ifs at h with hα
    · subst hα; simp
    · exact absurd rfl h
  | j :: l, α, h => by
    simp only [cnt] at h
    have : ∃ β ∈ remLetter j α, cnt l β ≠ 0 := by
      by_contra hn
      push Not at hn
      apply h
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      exact hn β hβ
    obtain ⟨β, hβ, hne⟩ := this
    obtain ⟨hl, hc⟩ := cnt_ne_zero l β hne
    obtain ⟨h1, h2⟩ := mem_remLetter j α β hβ
    refine ⟨by simp; omega, fun c => ?_⟩
    have := h2 c
    have := hc c
    simp only [List.count_cons]
    split_ifs <;> simp_all

theorem cnt_self_pos : ∀ α : List (Fin 2), 1 ≤ cnt α α
  | [] => by simp [cnt]
  | j :: l => by
    have := cnt_self_pos l
    simp [cnt, remLetter]
    omega

theorem descFactorial_le_factorial' (n k : ℕ) : n.descFactorial k ≤ n.factorial := by
  by_cases h : k ≤ n
  · have := Nat.factorial_mul_descFactorial h
    nlinarith [Nat.factorial_pos (n - k)]
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]; exact Nat.zero_le _

/-- Number of terms in the expansion of the `l`-derivative of a monomial of word `α`. -/
def nterms : List (Fin 2) → List (Fin 2) → ℕ
  | [], _ => 1
  | j :: l, α => ((remLetter j α).map fun β => nterms l β).sum

theorem nterms_le : ∀ (l α : List (Fin 2)), nterms l α ≤ α.length.descFactorial l.length
  | [], α => by simp [nterms]
  | j :: l, α => by
    simp only [nterms, List.length_cons]
    have hb : ∀ β ∈ remLetter j α, nterms l β ≤ (α.length - 1).descFactorial l.length := by
      intro β hβ
      have h1 := (mem_remLetter j α β hβ).1
      have := nterms_le l β
      have e : β.length = α.length - 1 := by omega
      rwa [e] at this
    have h2 : ((remLetter j α).map fun β => nterms l β).sum ≤
        (remLetter j α).length * (α.length - 1).descFactorial l.length := by
      have := List.sum_le_length_nsmul ((remLetter j α).map fun β => nterms l β)
        ((α.length - 1).descFactorial l.length)
        (by intro x hx; obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx; exact hb β hβ)
      simpa using this
    refine h2.trans ?_
    cases α with
    | nil => simp [remLetter]
    | cons a α =>
      rw [List.length_cons, Nat.add_sub_cancel, Nat.succ_descFactorial_succ]
      exact Nat.mul_le_mul_right _ (by simpa using length_remLetter_le j (a :: α))

theorem monoF_abs_le (X₀ Y : Vec 2) (hY : ∀ i, |Y i - X₀ i| ≤ 1) :
    ∀ α : List (Fin 2), |monoF X₀ α Y| ≤ 1
  | [] => by simp [monoF]
  | a :: α => by
    rw [monoF_cons, abs_mul]
    have := mul_le_mul (hY a) (monoF_abs_le X₀ Y hY α) (abs_nonneg _) zero_le_one
    simpa using this

theorem monoDeriv_abs_le (X₀ Y : Vec 2) (hY : ∀ i, |Y i - X₀ i| ≤ 1) :
    ∀ (l α : List (Fin 2)), |monoDeriv X₀ l α Y| ≤ (nterms l α : ℝ)
  | [], α => by simpa [monoDeriv, nterms] using monoF_abs_le X₀ Y hY α
  | j :: l, α => by
    simp only [monoDeriv, nterms, Nat.cast_list_sum, List.map_map, Function.comp_def]
    have key : ∀ L : List (List (Fin 2)),
        |(L.map fun β => monoDeriv X₀ l β Y).sum| ≤ (L.map fun β => (nterms l β : ℝ)).sum := by
      intro L
      induction L with
      | nil => simp
      | cons β L ih =>
        simp only [List.map_cons, List.sum_cons]
        exact (abs_add_le _ _).trans (add_le_add (monoDeriv_abs_le X₀ Y hY l β) ih)
    exact key _

/-- Derivative bounds near the centre: for `‖Y - X₀‖ ≤ 1` and any list `l` of derivative letters,
`|∂^l (monoF X₀ α) Y| ≤ (α.length)!`. -/
theorem derivList_monoF_abs_le (X₀ Y : Vec 2) (hY : ‖Y - X₀‖ ≤ 1) (l α : List (Fin 2)) :
    |derivList l (monoF X₀ α) Y| ≤ (α.length.factorial : ℝ) := by
  have hY' : ∀ i, |Y i - X₀ i| ≤ 1 := fun i => by
    have := norm_le_pi_norm (Y - X₀) i
    simpa using this.trans hY
  rw [derivList_monoF]
  refine (monoDeriv_abs_le X₀ Y hY' l α).trans ?_
  exact_mod_cast (nterms_le l α).trans (descFactorial_le_factorial' _ _)

/-- Derivative bounds near the centre, for words `w`: `‖∂^w (monoF X₀ α) Y‖ ≤ (α.length)!`. -/
theorem norm_orderedDerivative_monoF_le (X₀ Y : Vec 2) (hY : ‖Y - X₀‖ ≤ 1) {r : ℕ}
    (w : DerivativeWord2 r) (α : List (Fin 2)) :
    ‖orderedDerivative w (monoF X₀ α) Y‖ ≤ (α.length.factorial : ℝ) := by
  rw [Real.norm_eq_abs]
  exact derivList_monoF_abs_le X₀ Y hY _ α

/-! Re-centring a monomial: `monoF X' α Y = Σ_S monoF X (α|_S) Y · c_S(X')` with
`c_S(X') = Π_{k ∉ S} (X - X')_{α_k}`, and the ordered-derivative bound for `c_S` in `X'`. -/

/-- The sub-list of `α` on the positions in `S` (in the order of `α`). -/
def subWord (α : List (Fin 2)) (S : Finset (Fin α.length)) : List (Fin 2) :=
  ((List.finRange α.length).filter (· ∈ S)).map α.get

/-- `c_S(X') = Π_{k ∉ S} (X - X')_{α_k}`. -/
def cS (X : Vec 2) (α : List (Fin 2)) (S : Finset (Fin α.length)) (X' : Vec 2) : ℝ :=
  ∏ k ∈ Sᶜ, (X (α.get k) - X' (α.get k))

theorem length_subWord_le (α : List (Fin 2)) (S : Finset (Fin α.length)) :
    (subWord α S).length ≤ α.length := by
  simp only [subWord, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem monoF_eq_prod_get (X : Vec 2) (α : List (Fin 2)) (Y : Vec 2) :
    monoF X α Y = ∏ k : Fin α.length, (Y (α.get k) - X (α.get k)) := by
  rw [monoF, ← List.prod_ofFn]
  simp only [List.get_eq_getElem]
  rw [List.ofFn_getElem_eq_map α (fun i => Y i - X i)]

theorem prod_filter_map_finRange {n : ℕ} (S : Finset (Fin n)) (g : Fin n → ℝ) :
    ∀ L : List (Fin n), (((L.filter (· ∈ S)).map g)).prod =
      (L.map fun k => if k ∈ S then g k else 1).prod
  | [] => by simp
  | k :: L => by
    by_cases hk : k ∈ S <;> simp [hk, prod_filter_map_finRange S g L]

theorem monoF_subWord (X : Vec 2) (α : List (Fin 2)) (S : Finset (Fin α.length)) (Y : Vec 2) :
    monoF X (subWord α S) Y = ∏ k ∈ S, (Y (α.get k) - X (α.get k)) := by
  have h1 : monoF X (subWord α S) Y =
      ((((List.finRange α.length).filter (· ∈ S)).map fun k => Y (α.get k) - X (α.get k))).prod := by
    simp [monoF, subWord, List.map_map, Function.comp_def]
  rw [h1, prod_filter_map_finRange, ← Fin.prod_univ_def,
    Finset.prod_ite_mem Finset.univ S (fun k => Y (α.get k) - X (α.get k))]
  simp

/-- Re-centring: `monoF X' α Y = Σ_S monoF X (α|_S) Y * c_S(X')`. -/
theorem monoF_expand (X X' Y : Vec 2) (α : List (Fin 2)) :
    monoF X' α Y =
      ∑ S : Finset (Fin α.length), monoF X (subWord α S) Y * cS X α S X' := by
  have h := Finset.prod_add (fun k : Fin α.length => Y (α.get k) - X (α.get k))
    (fun k => X (α.get k) - X' (α.get k)) Finset.univ
  have e : ∀ k : Fin α.length, (Y (α.get k) - X (α.get k)) + (X (α.get k) - X' (α.get k)) =
      Y (α.get k) - X' (α.get k) := fun k => by ring
  simp only [e] at h
  rw [monoF_eq_prod_get, h, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [monoF_subWord, cS, Finset.compl_eq_univ_sdiff]

theorem cS_eq_smul (X : Vec 2) (α : List (Fin 2)) (S : Finset (Fin α.length)) :
    cS X α S = fun X' => monoF X (subWord α Sᶜ) X' • ((-1 : ℝ) ^ (Sᶜ).card) := by
  funext X'
  rw [monoF_subWord, smul_eq_mul, mul_comm, ← Finset.prod_neg, cS]
  exact Finset.prod_congr rfl fun k _ => by ring

theorem contDiff_cS (X : Vec 2) (α : List (Fin 2)) (S : Finset (Fin α.length)) (n : WithTop ℕ∞) :
    ContDiff ℝ n (cS X α S) := by
  rw [cS_eq_smul]
  exact (contDiff_monoF X n _).smul contDiff_const

/-- Ordered derivatives of `c_S` in `X'` are bounded by `(α.length)!` for `‖X' - X‖ ≤ 1`. -/
theorem norm_orderedDerivative_cS_le (X X' : Vec 2) (hX : ‖X' - X‖ ≤ 1) {r : ℕ}
    (w : DerivativeWord2 r) (α : List (Fin 2)) (S : Finset (Fin α.length)) :
    ‖orderedDerivative w (cS X α S) X'‖ ≤ (α.length.factorial : ℝ) := by
  rw [orderedDerivative_eq_derivList, cS_eq_smul,
    derivList_smul_const _ _ _ (contDiff_monoF X ∞ _)]
  simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
  exact (norm_orderedDerivative_monoF_le X X' hX w _).trans
    (by exact_mod_cast Nat.factorial_le (length_subWord_le α _))

/-! Reading off a single lift coefficient from a monomial test field: for a symmetric coefficient
array `c` and a monomial `Y ↦ Π_k (Y - X)_{α_k} • w`, `liftApply` returns `K α • Σ_u c_{m,α} w_u`. -/

section
/-- Symmetry of a coefficient array in the word. -/
def LiftSymm {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (c : LiftCoeff ι h) : Prop :=
  ∀ (m : ℕ) (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), c m (α ∘ σ) = c m α

/-- The multiplicity `K α = Σ_{α'} cnt α' α` (in fact `m!`). -/
def liftK {m : ℕ} (α : DerivativeWord2 m) : ℕ :=
  ∑ α' : DerivativeWord2 m, cnt (List.ofFn α') (List.ofFn α)

theorem one_le_liftK {m : ℕ} (α : DerivativeWord2 m) : 1 ≤ liftK α :=
  (cnt_self_pos (List.ofFn α)).trans
    (Finset.single_le_sum (f := fun α' : DerivativeWord2 m => cnt (List.ofFn α') (List.ofFn α))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ α))

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- A symmetric coefficient depends only on the letter counts of the word. -/
theorem coeff_eq_of_perm {c : LiftCoeff ι h} (hc : LiftSymm c) {m : ℕ}
    {α α' : DerivativeWord2 m} (hp : (List.ofFn α').Perm (List.ofFn α)) : c m α' = c m α := by
  have e : α' ∘ Tuple.sort α' = α ∘ Tuple.sort α :=
    List.ofFn_injective <|
      (((Tuple.sort α').ofFn_comp_perm α').trans (hp.trans ((Tuple.sort α).ofFn_comp_perm α).symm)
        ).eq_of_pairwise' (Tuple.monotone_sort α').sortedLE_ofFn.pairwise
          (Tuple.monotone_sort α).sortedLE_ofFn.pairwise
  rw [← hc m α' (Tuple.sort α'), e, hc m α (Tuple.sort α)]

theorem coeff_eq_of_cnt_ne_zero {c : LiftCoeff ι h} (hc : LiftSymm c) {m : ℕ}
    {α α' : DerivativeWord2 m} (hne : cnt (List.ofFn α') (List.ofFn α) ≠ 0) :
    c m α' = c m α :=
  coeff_eq_of_perm hc (List.perm_iff_count.2 (cnt_ne_zero _ _ hne).2)

variable [Fintype ι]

theorem orderedDerivative_monoF_smul (X : Vec 2) {r : ℕ} (α' : DerivativeWord2 r)
    (β : List (Fin 2)) (w : ∀ i, h i) (u : ι) :
    orderedDerivative α' (fun Y => monoF X β Y • w) X u =
      (cnt (List.ofFn α') β : ℝ) • w u := by
  rw [orderedDerivative_eq_derivList, derivList_smul_const w _ _ (contDiff_monoF X ∞ β)]
  simp [derivList_monoF_center]


theorem liftApply_monoF {c : LiftCoeff ι h} (hc : LiftSymm c) (n : ℕ) {m : ℕ} (hm : m ≤ n)
    (α : DerivativeWord2 m) (w : ∀ i, h i) (t : ℝ) (X z : Vec 2) :
    liftApply n c (fun _ Y => monoF X (List.ofFn α) Y • w) t X z =
      (liftK α : ℝ) • (fun v => ∑ u, c m α t X z v u (w u)) := by
  funext v
  simp only [liftApply, orderedDerivative_monoF_smul, map_smul, Pi.smul_apply]
  rw [Finset.sum_eq_single m]
  · have : ∀ α' : DerivativeWord2 m, ∑ u, (cnt (List.ofFn α') (List.ofFn α) : ℝ) •
        c m α' t X z v u (w u) =
        (cnt (List.ofFn α') (List.ofFn α) : ℝ) • ∑ u, c m α t X z v u (w u) := by
      intro α'
      by_cases h0 : cnt (List.ofFn α') (List.ofFn α) = 0
      · simp [h0]
      · rw [coeff_eq_of_cnt_ne_zero hc h0, Finset.smul_sum]
    rw [Finset.sum_congr rfl fun α' _ => this α', ← Finset.sum_smul]
    simp [liftK]
  · intro m' _ hm'
    refine Finset.sum_eq_zero fun α' _ => Finset.sum_eq_zero fun u _ => ?_
    have : cnt (List.ofFn α') (List.ofFn α) = 0 := by
      by_contra hne
      have := (cnt_ne_zero _ _ hne).1
      simp at this
      exact hm' this
    simp [this]
  · intro hn
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hm)) hn

end
end

end AVRegularity.QuietDecay
end
