/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.DoldKan.Decomposition
import Mathlib.Tactic.FinCases

/-!

# Behaviour of P_infty with respect to degeneracies

For any `X : SimplicialObject C` where `C` is an abelian category,
the projector `PInfty : K[X] ⟶ K[X]` is supposed to be the projection
on the normalized subcomplex, parallel to the degenerate subcomplex, i.e.
the subcomplex generated by the images of all `X.σ i`.

In this file, we obtain `degeneracy_comp_P_infty` which states that
if `X : SimplicialObject C` with `C` a preadditive category,
`θ : [n] ⟶ Δ'` is a non injective map in `SimplexCategory`, then
`X.map θ.op ≫ P_infty.f n = 0`. It follows from the more precise
statement vanishing statement `σ_comp_P_eq_zero` for the `P q`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Preadditive Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category C] [Preadditive C]

theorem HigherFacesVanish.comp_σ {Y : C} {X : SimplicialObject C} {n b q : ℕ} {φ : Y ⟶ X _[n + 1]}
    (v : HigherFacesVanish q φ) (hnbq : n + 1 = b + q) :
    HigherFacesVanish q
      (φ ≫
        X.σ ⟨b, by
          simp only [hnbq, Nat.lt_add_one_iff, le_add_iff_nonneg_right, zero_le]⟩) :=
  fun j hj => by
  rw [assoc, SimplicialObject.δ_comp_σ_of_gt', Fin.pred_succ, v.comp_δ_eq_zero_assoc _ _ hj,
    zero_comp]
  · dsimp
    rw [Fin.lt_iff_val_lt_val, Fin.val_succ]
    linarith
  · intro hj'
    simp only [hnbq, add_comm b, add_assoc, hj', Fin.val_zero, zero_add, add_le_iff_nonpos_right,
      nonpos_iff_eq_zero, add_eq_zero, false_and] at hj

theorem σ_comp_P_eq_zero (X : SimplicialObject C) {n q : ℕ} (i : Fin (n + 1)) (hi : n + 1 ≤ i + q) :
    X.σ i ≫ (P q).f (n + 1) = 0 := by
  revert i hi
  induction' q with q hq
  · intro i (hi : n + 1 ≤ i)
    exfalso
    linarith [Fin.is_lt i]
  · intro i (hi : n + 1 ≤ i + q + 1)
    by_cases h : n + 1 ≤ (i : ℕ) + q
    · rw [P_succ, HomologicalComplex.comp_f, ← assoc, hq i h, zero_comp]
    · replace hi : n = i + q := by
        obtain ⟨j, hj⟩ := le_iff_exists_add.mp hi
        rw [← Nat.lt_succ_iff, Nat.succ_eq_add_one, hj, not_lt, add_le_iff_nonpos_right,
          nonpos_iff_eq_zero] at h
        rw [← add_left_inj 1, hj, self_eq_add_right, h]
      rcases n with _|n
      · fin_cases i
        dsimp at h hi
        rw [show q = 0 by omega]
        change X.σ 0 ≫ (P 1).f 1 = 0
        simp only [P_succ, HomologicalComplex.add_f_apply, comp_add,
          HomologicalComplex.id_f, AlternatingFaceMapComplex.obj_d_eq, Hσ,
          HomologicalComplex.comp_f, Homotopy.nullHomotopicMap'_f (c_mk 2 1 rfl) (c_mk 1 0 rfl),
          comp_id]
        erw [hσ'_eq' (zero_add 0).symm, hσ'_eq' (add_zero 1).symm, comp_id, Fin.sum_univ_two,
          Fin.sum_univ_succ, Fin.sum_univ_two]
        simp only [Fin.val_zero, pow_zero, pow_one, pow_add, one_smul, neg_smul, Fin.mk_one,
          Fin.val_succ, Fin.val_one, Fin.succ_one_eq_two, P_zero, HomologicalComplex.id_f,
          Fin.val_two, pow_two, mul_neg, one_mul, neg_mul, neg_neg, id_comp, add_comp,
          comp_add, Fin.mk_zero, neg_comp, comp_neg, Fin.succ_zero_eq_one]
        erw [SimplicialObject.δ_comp_σ_self, SimplicialObject.δ_comp_σ_self_assoc,
          SimplicialObject.δ_comp_σ_succ, comp_id,
          SimplicialObject.δ_comp_σ_of_le X
            (show (0 : Fin 2) ≤ Fin.castSucc 0 by rw [Fin.castSucc_zero]),
          SimplicialObject.δ_comp_σ_self_assoc, SimplicialObject.δ_comp_σ_succ_assoc]
        simp only [add_neg_cancel, add_zero, zero_add]
      · rw [← id_comp (X.σ i), ← (P_add_Q_f q n.succ : _ = 𝟙 (X.obj _)), add_comp, add_comp,
          P_succ]
        have v : HigherFacesVanish q ((P q).f n.succ ≫ X.σ i) :=
          (HigherFacesVanish.of_P q n).comp_σ hi
        erw [← assoc, v.comp_P_eq_self, HomologicalComplex.add_f_apply, Preadditive.comp_add,
          comp_id, v.comp_Hσ_eq hi, assoc, SimplicialObject.δ_comp_σ_succ_assoc, Fin.eta,
          decomposition_Q n q, sum_comp, sum_comp, Finset.sum_eq_zero, add_zero, add_neg_eq_zero]
        intro j hj
        simp only [true_and_iff, Finset.mem_univ, Finset.mem_filter] at hj
        obtain ⟨k, hk⟩ := Nat.le.dest (Nat.lt_succ_iff.mp (Fin.is_lt j))
        rw [add_comm] at hk
        have hi' : i = Fin.castSucc ⟨i, by omega⟩ := by
          ext
          simp only [Fin.castSucc_mk, Fin.eta]
        have eq := hq j.rev.succ (by
          simp only [← hk, Fin.rev_eq j hk.symm, Nat.succ_eq_add_one, Fin.succ_mk, Fin.val_mk]
          omega)
        rw [HomologicalComplex.comp_f, assoc, assoc, assoc, hi',
          SimplicialObject.σ_comp_σ_assoc, reassoc_of% eq, zero_comp, comp_zero, comp_zero,
          comp_zero]
        simp only [Fin.rev_eq j hk.symm, Fin.le_iff_val_le_val, Fin.val_mk]
        omega

@[reassoc (attr := simp)]
theorem σ_comp_PInfty (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ PInfty.f (n + 1) = 0 := by
  rw [PInfty_f, σ_comp_P_eq_zero X i]
  simp only [le_add_iff_nonneg_left, zero_le]

@[reassoc]
theorem degeneracy_comp_PInfty (X : SimplicialObject C) (n : ℕ) {Δ' : SimplexCategory}
    (θ : ([n] : SimplexCategory) ⟶ Δ') (hθ : ¬Mono θ) : X.map θ.op ≫ PInfty.f n = 0 := by
  rw [SimplexCategory.mono_iff_injective] at hθ
  cases n
  · exfalso
    apply hθ
    intro x y h
    fin_cases x
    fin_cases y
    rfl
  · obtain ⟨i, α, h⟩ := SimplexCategory.eq_σ_comp_of_not_injective θ hθ
    rw [h, op_comp, X.map_comp, assoc, show X.map (SimplexCategory.σ i).op = X.σ i by rfl,
      σ_comp_PInfty, comp_zero]

end DoldKan

end AlgebraicTopology
