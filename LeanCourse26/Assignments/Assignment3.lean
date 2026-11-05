-- Name: Lars Lewerenz

module

public import Mathlib.Analysis.Complex.Exponential

open Real Function Set Nat

#click_suggestions

/-

* Hand in the solutions to the exercises below. Deadline: 4.11.2025 before class.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

section calculations

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by
  calc t ^ 2 - 3 * t - 17 = t * t - 3 * t - 17 := by rw [pow_two]
    _ = t * (t - 3) - 17 := by ring
    _ ≥ 10 * (10 - 3) - 17 := by gcongr
    -- _ = 10 * 7 - 17 := by ring
    -- _ = 53 := by ring
    _ ≥ 5 := by norm_num

/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by
  have ht4 : t ^ 2 = 4 := by
    calc t ^ 2 = t ^ 2 - 4 + 4 := by ring
      _ = 0 + 4 := by rw [ht]
      _ = 4 := by rw[zero_add]
  calc t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = (t ^ 2) * (t ^ 2) + 3 * t * (t ^ 2) - 3 * t * t - 2 * t - 2 := by ring
    _ = (t ^ 2) * (t ^ 2) + 3 * (t * (t ^ 2) - t ^ 2) - 2 * t - 2 := by ring
    _ = 4 * 4 + 3 * (t * 4 - 4) - 2 * t - 2 := by rw [ht4]
    -- _ = 14 + 12 * (t - 1) - 2 * t := by ring
    -- _ = 14 + 12 * t - 12 - 2 * t := by ring
    _ = 10 * t + 2 := by ring

end calculations

section Min
open LE
variable (a b c d : ℝ)

/- Recall the following properties of the `≤` relation -/
#check (le : ℝ → ℝ → Prop)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_antisymm : a ≤ b → b ≤ a → a = b)

/- The following theorems characterize `min`.
Let's use this characterization of it to prove that `min` is commutative and associative.
Don't use other lemmas about `min` from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

-- Note: the tactic `order` proves both of these immediately
-- For practice, prove them "by hand"
lemma exercise_min_comm : min a b = min b a := by
  apply le_antisymm
  · apply le_min
    · apply min_le_right
    · apply min_le_left
  · apply le_min
    · apply min_le_right
    · apply min_le_left

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by
  apply le_antisymm
  · apply le_min
    · apply le_min
      · apply min_le_left
      · apply le_trans
        · apply min_le_right
        · apply min_le_left
    · apply le_trans
      · apply min_le_right
      · apply min_le_right
  · apply le_min
    · apply le_trans
      · apply min_le_left
      · apply min_le_left
    · apply le_min
      · apply le_trans
        · apply min_le_left
        · apply min_le_right
      · apply le_trans
        · apply min_le_right
        · apply le_rfl

-- Prove the following exercise. You can use mathlib tactics now.
lemma exercise_min : min (min a (min (min b c) c)) d = min (min a (min d b)) c := by
  -- apply le_antisymm
  -- · apply le_min
  --   · apply le_min
  --     · apply le_trans
  --       · apply min_le_left
  --       · apply min_le_left
  --     · apply le_min
  --       · apply min_le_right
  --       · apply le_trans
  --         · apply min_le_left
  --         · order
  --   · order
  · order

end Min

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by
  constructor
  · intro h x
    rw [h]
    trivial
  · intro h
    ext x
    constructor
    · intro hx
      apply mem_univ
    · intro hu
      apply h


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
example (p : Prop) : p ∨ ¬ p := by
  by_contra h
  apply h
  right
  intro hp
  apply h
  left
  exact hp

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (132 + 32 * 3, (x + y) ^ 2) = (228, x ^ 2 + 2 * x * y + y ^ 2) := by
  ext
  · simp
  · ring
  -- The type is ℕ × ℝ, as 132 + 32 * 3 : ℕ

/- Prove a version of the axiom of choice Lean's `Classical.choose`.

Note: this might be a bit harder; you will probably find `Classical.choose` and
`Classical.choose_spec` useful. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by
  sorry

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by
  sorry

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by
  sorry

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by
  sorry

/- Prove this without using lemmas from Mathlib -/
example {f : α → β} (h : Injective f) : Injective (image f) := by
  sorry

end Set


/-! # Exercises to hand-in. -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
  ext y
  constructor
  · intro h
    obtain ⟨⟨x, hxs, rfl⟩, hyt⟩ := h
    use x
    constructor
    · constructor
      · apply hxs
      · exact hyt
    · rfl
  · intro hx
    obtain ⟨x, ⟨hs, hfs⟩, rfl⟩ := hx
    constructor
    · use x
    · exact hfs

/- Prove this without using lemmas from Mathlib. -/
-- Note: we still use the `simp` tactic... which is using mathlib, but only in a mild way.
-- That's a reasonable compromise for now.
example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := h
    simp at hx
    obtain ⟨s, hs⟩ := hx
    simp
    use s
    use x
  · intro h
    simp at h
    obtain ⟨i, x, hx, rfl⟩ := h
    simp
    use x
    constructor
    · use i
    · rfl

/- Prove this without using lemmas from Mathlib. -/
example {a b c d : ℝ} (hab : a < b) : Icc a b ⊆ Ioo c d ↔ c < a ∧ b < d := by
  constructor
  · intro h
    have ha : a ∈ Icc a b := by
      constructor
      · rfl
      · linarith
    have hb : b ∈ Ioo c d := by
      apply h
      constructor -- this is actually 'trivial', but I don't want to rely on that :D
      · linarith
      · rfl
    constructor
    · apply h at ha
      obtain ⟨hca, had⟩ := ha
      exact hca
    · obtain ⟨hcb, hbd⟩ := hb
      exact hbd
  · intro h x hx
    -- simp
    obtain ⟨hax, hxb⟩ := hx
    obtain ⟨hca, hbd⟩ := h
    constructor
    · linarith
    · linarith

#check sq_le_sq

#loogle _ ≤ |_| ↔ _

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by
  simp
  ext x
  simp
  have sqr16 : (16 : ℝ) = 4 ^ 2 := by ring
  rw [sqr16]
  rw [sq_le_sq]
  rw [le_abs']
  simp

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  unfold SurjectiveFunction
  constructor
  · intro hgf y
    obtain ⟨x, hx⟩ := hgf y
    use f x
    apply hx
  · intro hg y
    obtain ⟨x, hx⟩ := hg y
    obtain ⟨a, ha⟩ := hf x
    use a
    simp
    rw [ha]
    apply hx

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  unfold SurjectiveFunction
  intro y
  simp
  obtain ⟨z, hz⟩ := hf ((y - 1) / 2)
  use (z / 3) - 4
  ring_nf
  rw [hz]
  ring

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by
  sorry

end Surjectivity
