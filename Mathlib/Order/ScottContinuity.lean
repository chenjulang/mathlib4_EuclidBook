/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.Bounds.Basic

/-!
# Scott continuity
-/

open Set

variable {α β : Type*}

section ScottContinuous
variable [Preorder α] [Preorder β] {D D₁ D₂ : Set (Set α)} {E : Set (Set β)}
  {f : α → β} {a : α}

/-- A function between preorders is said to be Scott continuous on a set `D` of directed sets if it
preserves `IsLUB` on elements of `D`.

The dual notion

```lean
∀ ⦃d : Set α⦄, d ∈ D →  d.Nonempty → DirectedOn (· ≥ ·) d → ∀ ⦃a⦄, IsGLB d a → IsGLB (f '' d) (f a)
```

does not appear to play a significant role in the literature, so is omitted here.
-/
def ScottContinuousOn (D : Set (Set α)) (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)

lemma ScottContinuousOn.mono (hD : D₁ ⊆ D₂) (hf : ScottContinuousOn D₂ f) :
    ScottContinuousOn D₁ f := fun _  hdD₁ hd₁ hd₂ _ hda => hf (hD hdD₁) hd₁ hd₂ hda

protected theorem ScottContinuousOn.monotone (D : Set (Set α)) (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
    (h : ScottContinuousOn D f) : Monotone f := by
  refine' fun a b hab =>
    (h (hD a b hab) (insert_nonempty _ _) (directedOn_pair le_refl hab) _).1
      (mem_image_of_mem _ <| mem_insert _ _)
  rw [IsLUB, upperBounds_insert, upperBounds_singleton,
    inter_eq_self_of_subset_right (Ici_subset_Ici.2 hab)]
  exact isLeast_Ici

@[simp] lemma ScottContinuousOn.id : ScottContinuousOn D (id : α → α) := by simp [ScottContinuousOn]

/-- A function between preorders is said to be Scott continuous if it preserves `IsLUB` on directed
sets. It can be shown that a function is Scott continuous if and only if it is continuous wrt the
Scott topology.
-/
def ScottContinuous (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)

@[simp] lemma scottContinuousOn_univ : ScottContinuousOn univ f ↔ ScottContinuous f := by
  simp [ScottContinuousOn, ScottContinuous]

lemma ScottContinuous.scottContinuousOn {D : Set (Set α)} :
    ScottContinuous f → ScottContinuousOn D f := fun h _ _ d₂ d₃ _ hda => h d₂ d₃ hda

protected theorem ScottContinuous.monotone (h : ScottContinuous f) : Monotone f :=
  h.scottContinuousOn.monotone univ (fun _ _ _ ↦ trivial)

@[simp] lemma ScottContinuous.id : ScottContinuous (id : α → α) := by simp [ScottContinuous]

variable {g : α → β}

lemma ScottContinuous.prodMk (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous fun x => (f x, g x) := fun d hd₁ hd₂ a hda => by
  rw [IsLUB, IsLeast, upperBounds]
  constructor
  · simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_setOf_eq,
    Prod.mk_le_mk]
    intro b hb
    exact ⟨hf.monotone (hda.1 hb), hg.monotone (hda.1 hb)⟩
  · intro ⟨p₁, p₂⟩ hp
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_setOf_eq,
      Prod.mk_le_mk] at hp
    constructor
    · rw [isLUB_le_iff (hf hd₁ hd₂ hda), upperBounds]
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_setOf_eq]
      intro _ hb
      exact (hp _ hb).1
    · rw [isLUB_le_iff (hg hd₁ hd₂ hda), upperBounds]
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_setOf_eq]
      intro _ hb
      exact (hp _ hb).2

end ScottContinuous
