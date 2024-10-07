/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin

/-!
# Fin-indexed tuples of finsets
-/

open Fin Fintype

namespace Fin
variable {n : ℕ} {α : Fin (n + 1) → Type*} {f : ∀ i, α i} {s : ∀ i, Finset (α i)} {p : Fin (n + 1)}

open Fintype

lemma mem_piFinset_iff_zero_tail :
    f ∈ Fintype.piFinset s ↔ f 0 ∈ s 0 ∧ tail f ∈ piFinset (tail s) := by
  simp only [Fintype.mem_piFinset, forall_fin_succ, tail]

lemma mem_piFinset_iff_last_init :
    f ∈ piFinset s ↔ f (last n) ∈ s (last n) ∧ init f ∈ piFinset (init s) := by
  simp only [Fintype.mem_piFinset, forall_fin_succ', init, and_comm]

lemma mem_piFinset_iff_pivot_removeNth (p : Fin (n + 1)) :
    f ∈ piFinset s ↔ f p ∈ s p ∧ removeNth p f ∈ piFinset (removeNth p s) := by
  simp only [Fintype.mem_piFinset, forall_iff_succAbove p, removeNth]

@[deprecated (since := "2024-09-20")] alias mem_piFinset_succ := mem_piFinset_iff_zero_tail
@[deprecated (since := "2024-09-20")] alias mem_piFinset_succ' := mem_piFinset_iff_last_init

lemma cons_mem_piFinset_cons {x_zero : α 0} {x_tail : (i : Fin n) → α i.succ}
    {s_zero : Finset (α 0)} {s_tail : (i : Fin n) → Finset (α i.succ)} :
    cons x_zero x_tail ∈ piFinset (cons s_zero s_tail) ↔
      x_zero ∈ s_zero ∧ x_tail ∈ piFinset s_tail := by
  simp_rw [mem_piFinset_iff_zero_tail, cons_zero, tail_cons]

lemma snoc_mem_piFinset_snoc {x_last : α (last n)} {x_init : (i : Fin n) → α i.castSucc}
    {s_last : Finset (α (last n))} {s_init : (i : Fin n) → Finset (α i.castSucc)} :
    snoc x_init x_last ∈ piFinset (snoc s_init s_last) ↔
      x_last ∈ s_last ∧ x_init ∈ piFinset s_init := by
  simp_rw [mem_piFinset_iff_last_init, init_snoc, snoc_last]

lemma insertNth_mem_piFinset_insertNth {x_pivot : α p} {x_remove : ∀ i, α (succAbove p i)}
    {s_pivot : Finset (α p)} {s_remove : ∀ i, Finset (α (succAbove p i))} :
    insertNth p x_pivot x_remove ∈ piFinset (insertNth p s_pivot s_remove) ↔
      x_pivot ∈ s_pivot ∧ x_remove ∈ piFinset s_remove := by
  simp [mem_piFinset_iff_pivot_removeNth p]

end Fin

namespace Finset
variable {n : ℕ} {α : Fin (n + 1) → Type*} {p : Fin (n + 1)} (S : ∀ i, Finset (α i))

lemma map_consEquiv_filter_piFinset (P : (∀ i, α (succ i)) → Prop) [DecidablePred P] :
    ((piFinset S).filter fun r ↦ P <| tail r).map (consEquiv α).symm.toEmbedding =
      S 0 ×ˢ (piFinset fun x ↦ S <| succ x).filter P := by
  unfold tail; ext; simp [Fin.forall_iff_succ, and_assoc]

lemma map_snocEquiv_filter_piFinset (P : (∀ i, α (castSucc i)) → Prop) [DecidablePred P] :
    ((piFinset S).filter fun r ↦ P <| init r).map (snocEquiv α).symm.toEmbedding =
      S (last _) ×ˢ (piFinset <| init S).filter P := by
  unfold init; ext; simp [Fin.forall_iff_castSucc, and_assoc]

lemma map_insertNthEquiv_filter_piFinset (P : (∀ i, α (p.succAbove i)) → Prop) [DecidablePred P] :
    ((piFinset S).filter fun r ↦ P <| p.removeNth r).map (p.insertNthEquiv α).symm.toEmbedding =
      S p ×ˢ (piFinset <| p.removeNth S).filter P := by
  unfold removeNth; ext; simp [Fin.forall_iff_succAbove p, and_assoc]

lemma card_consEquiv_filter_piFinset (P : (∀ i, α (succ i)) → Prop) [DecidablePred P] :
    ((piFinset S).filter fun r ↦ P <| tail r).card =
      (S 0).card * ((piFinset fun x ↦ S <| succ x).filter P).card := by
  rw [← card_product, ← map_consEquiv_filter_piFinset, card_map]

lemma card_snocEquiv_filter_piFinset (P : (∀ i, α (castSucc i)) → Prop) [DecidablePred P] :
    ((piFinset S).filter fun r ↦ P <| init r).card =
      (S (last _)).card * ((piFinset <| init S).filter P).card := by
  rw [← card_product, ← map_snocEquiv_filter_piFinset, card_map]

lemma card_insertNthEquiv_filter_piFinset (P : (∀ i, α (p.succAbove i)) → Prop) [DecidablePred P] :
    ((piFinset S).filter fun r ↦ P <| p.removeNth r).card =
      (S p).card * ((piFinset <| p.removeNth S).filter P).card := by
  rw [← card_product, ← map_insertNthEquiv_filter_piFinset, card_map]

end Finset
